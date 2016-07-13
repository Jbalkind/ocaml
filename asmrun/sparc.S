/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* Asm part of the runtime system for the Sparc processor.  */
/* Must be preprocessed by cpp */

#ifndef SYS_solaris
#define INDIRECT_LIMIT
#endif

#define Exn_ptr %l5
#define Alloc_ptr %l6
#define Alloc_limit %l7

# define SAVE_FREGS_V8                      \
        std     %f0,  [%g1]         ;       \
        std     %f2,  [%g1 + 0x8]   ;       \
        std     %f4,  [%g1 + 0x10]  ;       \
        std     %f6,  [%g1 + 0x18]  ;       \
        std     %f8,  [%g1 + 0x20]  ;       \
        std     %f10, [%g1 + 0x28]  ;       \
        std     %f12, [%g1 + 0x30]  ;       \
        std     %f14, [%g1 + 0x38]  ;       \
        std     %f16, [%g1 + 0x40]  ;       \
        std     %f18, [%g1 + 0x48]  ;       \
        std     %f20, [%g1 + 0x50]  ;       \
        std     %f22, [%g1 + 0x58]  ;       \
        std     %f24, [%g1 + 0x60]  ;       \
        std     %f26, [%g1 + 0x68]  ;       \
        std     %f28, [%g1 + 0x70]

# define RESTORE_FREGS_V8                   \
       ldd     [%g1], %f0          ;       \
        ldd     [%g1 + 0x8], %f2    ;       \
        ldd     [%g1 + 0x10], %f4   ;       \
        ldd     [%g1 + 0x18], %f6   ;       \
        ldd     [%g1 + 0x20], %f8   ;       \
        ldd     [%g1 + 0x28], %f10  ;       \
        ldd     [%g1 + 0x30], %f12  ;       \
        ldd     [%g1 + 0x38], %f14  ;       \
        ldd     [%g1 + 0x40], %f16  ;       \
        ldd     [%g1 + 0x48], %f18  ;       \
        ldd     [%g1 + 0x50], %f20  ;       \
        ldd     [%g1 + 0x58], %f22  ;       \
        ldd     [%g1 + 0x60], %f24  ;       \
        ldd     [%g1 + 0x68], %f26  ;       \
        ldd     [%g1 + 0x70], %f28

#if defined(__arch64__)

# define Load(symb,reg)    setx symb,%g3,reg; ldx [reg], reg
# define Store(reg,symb)   setx symb,%g1,%g3; stx reg, [%g3]
# define Address(symb,reg) setx symb,%g3,reg
# define BIAS 2047
# define FRAME_SIZE 176
# define PTR_SIZE 8
# define STADDR stx
# define LDADDR ldx

# define Bi(op,target) b##op %xcc,target

# define IREGS_SIZE 20*8
# define FREGS_SIZE 15*8 + 1*8/*%f30,unused*/ + 16*8
# define REGS_PAD   8

       .common caml_required_size, 8, 8

# define SAVE_IREGS                         \
        stx     %o0, [%g1 + 0x00]   ;       \
        stx     %o1, [%g1 + 0x08]   ;       \
        stx     %o2, [%g1 + 0x10]   ;       \
        stx     %o3, [%g1 + 0x18]   ;       \
        stx     %o4, [%g1 + 0x20]   ;       \
        stx     %o5, [%g1 + 0x28]   ;       \
        stx     %i0, [%g1 + 0x30]   ;       \
        stx     %i1, [%g1 + 0x38]   ;       \
        stx     %i2, [%g1 + 0x40]   ;       \
        stx     %i3, [%g1 + 0x48]   ;       \
        stx     %i4, [%g1 + 0x50]   ;       \
        stx     %i5, [%g1 + 0x58]   ;       \
        stx     %l0, [%g1 + 0x60]   ;       \
        stx     %l1, [%g1 + 0x68]   ;       \
        stx     %l2, [%g1 + 0x70]   ;       \
        stx     %l3, [%g1 + 0x78]   ;       \
        stx     %l4, [%g1 + 0x80]   ;       \
        stx     %g4, [%g1 + 0x88]   ;       \
        stx     %g5, [%g1 + 0x90]   ;       \
        stx     %g2, [%g1 + 0x98]   /* Save required size */

# define RESTORE_IREGS                      \
       ldx     [%g1], %o0          ;       \
        ldx     [%g1 + 0x08], %o1   ;       \
        ldx     [%g1 + 0x10], %o2   ;       \
        ldx     [%g1 + 0x18], %o3   ;       \
        ldx     [%g1 + 0x20], %o4   ;       \
        ldx     [%g1 + 0x28], %o5   ;       \
        ldx     [%g1 + 0x30], %i0   ;       \
        ldx     [%g1 + 0x38], %i1   ;       \
        ldx     [%g1 + 0x40], %i2   ;       \
        ldx     [%g1 + 0x48], %i3   ;       \
        ldx     [%g1 + 0x50], %i4   ;       \
        ldx     [%g1 + 0x58], %i5   ;       \
        ldx     [%g1 + 0x60], %l0   ;       \
        ldx     [%g1 + 0x68], %l1   ;       \
        ldx     [%g1 + 0x70], %l2   ;       \
        ldx     [%g1 + 0x78], %l3   ;       \
        ldx     [%g1 + 0x80], %l4   ;       \
        ldx     [%g1 + 0x88], %g4   ;       \
        ldx     [%g1 + 0x90], %g5   ;       \
        ldx     [%g1 + 0x98], %g2     /* Recover desired size */

# define SAVE_FREGS                         \
       SAVE_FREGS_V8               ;       \
       /* %f30 would go here */            \
       std     %f32, [%g1 + 0x80]  ;       \
       std     %f34, [%g1 + 0x88]  ;       \
       std     %f36, [%g1 + 0x90]  ;       \
       std     %f38, [%g1 + 0x98]  ;       \
       std     %f40, [%g1 + 0xA0]  ;       \
       std     %f42, [%g1 + 0xA8]  ;       \
       std     %f44, [%g1 + 0xB0]  ;       \
       std     %f46, [%g1 + 0xB8]  ;       \
       std     %f48, [%g1 + 0xC0]  ;       \
       std     %f50, [%g1 + 0xC8]  ;       \
       std     %f52, [%g1 + 0xD0]  ;       \
       std     %f54, [%g1 + 0xD8]  ;       \
       std     %f56, [%g1 + 0xE0]  ;       \
       std     %f58, [%g1 + 0xE8]  ;       \
       std     %f60, [%g1 + 0xF0]  ;       \
       std     %f62, [%g1 + 0xF8]

# define RESTORE_FREGS                      \
       RESTORE_FREGS_V8            ;       \
       /* %f30 would go here */            \
        ldd     [%g1 + 0x80], %f32  ;       \
        ldd     [%g1 + 0x88], %f34  ;       \
        ldd     [%g1 + 0x90], %f36  ;       \
        ldd     [%g1 + 0x98], %f38  ;       \
        ldd     [%g1 + 0xA0], %f40  ;       \
        ldd     [%g1 + 0xA8], %f42  ;       \
        ldd     [%g1 + 0xB0], %f46  ;       \
        ldd     [%g1 + 0xB8], %f48  ;       \
        ldd     [%g1 + 0xC0], %f50  ;       \
        ldd     [%g1 + 0xC8], %f52  ;       \
        ldd     [%g1 + 0xD0], %f54  ;       \
        ldd     [%g1 + 0xD8], %f56  ;       \
        ldd     [%g1 + 0xE0], %f58  ;       \
        ldd     [%g1 + 0xE8], %f60  ;       \
        ldd     [%g1 + 0xF0], %f62  ;       \
       ldd     [%g1 + 0xF8], %f32

/* glibc/sparc64 is missing .rem, which is used by asmcomp in all
   flavors of sparc.  r = a - qd  where q = a/d */

       .text
       .global .rem
.rem:
       sdivx           %o0, %o1, %o2
       mulx            %o2, %o1, %o3
       retl
         sub           %o0, %o3, %o0
       
#else

# define Load(symb,reg)    sethi %hi(symb), %g1; ld [%g1 + %lo(symb)], reg
# define Store(reg,symb)   sethi %hi(symb), %g1; st reg, [%g1 + %lo(symb)]
# define Address(symb,reg) sethi %hi(symb), reg; or reg, %lo(symb), reg
# define BIAS 0
# define FRAME_SIZE 96
# define PTR_SIZE 4
# define STADDR st
# define LDADDR ld

# define Bi(op, target) b##op target

# define IREGS_SIZE 20*4
# define FREGS_SIZE 15*8
/* In sparc32 the stack frame must be aligned to double-word.  */
# define REGS_PAD   4
       
# define SAVE_IREGS                         \
        st      %o0, [%g1]          ;       \
        st      %o1, [%g1 + 0x4]    ;       \
        st      %o2, [%g1 + 0x8]    ;       \
        st      %o3, [%g1 + 0xc]    ;       \
        st      %o4, [%g1 + 0x10]   ;       \
        st      %o5, [%g1 + 0x14]   ;       \
        st      %i0, [%g1 + 0x18]   ;       \
        st      %i1, [%g1 + 0x1c]   ;       \
        st      %i2, [%g1 + 0x20]   ;       \
        st      %i3, [%g1 + 0x24]   ;       \
        st      %i4, [%g1 + 0x28]   ;       \
        st      %i5, [%g1 + 0x2c]   ;       \
        st      %l0, [%g1 + 0x30]   ;       \
        st      %l1, [%g1 + 0x34]   ;       \
        st      %l2, [%g1 + 0x38]   ;       \
        st      %l3, [%g1 + 0x3c]   ;       \
        st      %l4, [%g1 + 0x40]   ;       \
        st      %g3, [%g1 + 0x44]   ;       \
        st      %g4, [%g1 + 0x48]   ;       \
        st      %g2, [%g1 + 0x4C]      /* Save required size */

# define RESTORE_IREGS                      \
        ld      [%g1], %o0          ;       \
        ld      [%g1 + 0x4], %o1    ;       \
        ld      [%g1 + 0x8], %o2    ;       \
        ld      [%g1 + 0xc], %o3    ;       \
        ld      [%g1 + 0x10], %o4   ;       \
        ld      [%g1 + 0x14], %o5   ;       \
        ld      [%g1 + 0x18], %i0   ;       \
        ld      [%g1 + 0x1c], %i1   ;       \
        ld      [%g1 + 0x20], %i2   ;       \
        ld      [%g1 + 0x24], %i3   ;       \
        ld      [%g1 + 0x28], %i4   ;       \
        ld      [%g1 + 0x2c], %i5   ;       \
        ld      [%g1 + 0x30], %l0   ;       \
        ld      [%g1 + 0x34], %l1   ;       \
        ld      [%g1 + 0x38], %l2   ;       \
        ld      [%g1 + 0x3c], %l3   ;       \
        ld      [%g1 + 0x40], %l4   ;       \
        ld      [%g1 + 0x44], %g3   ;       \
        ld      [%g1 + 0x48], %g4   ;
        ld      [%g1 + 0x4C], %g2     /* Recover desired size */
       
# define SAVE_FREGS SAVE_FREGS_V8
# define RESTORE_FREGS RESTORE_FREGS_V8

#endif /* __arch64__ */

/* Allocation functions */

        .text

        .global  caml_system__code_begin
caml_system__code_begin:

        .global caml_allocN
        .global caml_call_gc

#if defined(__arch64__)
       .register %g2,#scratch
       .register %g3,#scratch
#endif

/* Required size in %g2 */
caml_allocN:
#ifdef INDIRECT_LIMIT
        LDADDR  [Alloc_limit], %g1
        sub     Alloc_ptr, %g2, Alloc_ptr
        cmp     Alloc_ptr, %g1
#else
        sub     Alloc_ptr, %g2, Alloc_ptr
        cmp     Alloc_ptr, Alloc_limit
#endif
        Bi(lu, caml_call_gc)
        nop
        retl
        nop

/* Required size in %g2 */
caml_call_gc:
#if defined(__arch64__)
       /* Save the required size from %g2 to the global so we
          can use the register below.  */
       Store(%g2, caml_required_size)
#endif
    /* Save exception pointer if GC raises */
        Store(Exn_ptr, caml_exception_pointer)
    /* Save current allocation pointer for debugging purposes */
        Store(Alloc_ptr, caml_young_ptr)
    /* Record lowest stack address, but mind the bias in sparc64 */
#if defined(__arch64__)
       add %sp, BIAS, %g2
       Store(%g2, caml_bottom_of_stack)
#else
        Store(%sp, caml_bottom_of_stack)
#endif
    /* Record last return address */
        Store(%o7, caml_last_return_address)
    /* Allocate space on stack for caml_context structure and float regs */
        sub     %sp, IREGS_SIZE + FREGS_SIZE + REGS_PAD, %sp
    /* Save int regs on stack and save it into caml_gc_regs */
L100:   add     %sp, BIAS + FRAME_SIZE + FREGS_SIZE, %g1
       SAVE_IREGS
       mov     %g1, %g2
       Store(%g2, caml_gc_regs)
    /* Save the floating-point registers */
        add     %sp, BIAS + FRAME_SIZE, %g1
       SAVE_FREGS
    /* Call the garbage collector */
        call    caml_garbage_collection
        nop
    /* Restore all regs used by the code generator */
        add     %sp, BIAS + FRAME_SIZE + FREGS_SIZE, %g1
        RESTORE_IREGS
        add     %sp, BIAS + FRAME_SIZE, %g1
        RESTORE_FREGS        
    /* Reload alloc ptr */
        Load(caml_young_ptr, Alloc_ptr)
    /* Allocate space for block */
#if defined(__arch64__)
       Load(caml_required_size, %g2)
#endif
#ifdef INDIRECT_LIMIT
        LDADDR  [Alloc_limit], %g1
        sub     Alloc_ptr, %g2, Alloc_ptr
        cmp     Alloc_ptr, %g1      /* Check that we have enough free space */
#else
        Load(caml_young_limit,Alloc_limit)
        sub     Alloc_ptr, %g2, Alloc_ptr
        cmp     Alloc_ptr, Alloc_limit
#endif
        Bi(lu, L100)                /* If not, call GC again */
        nop
    /* Return to caller */
        Load(caml_last_return_address, %o7)
        retl
        add     %sp, IREGS_SIZE + FREGS_SIZE + REGS_PAD, %sp       /* in delay slot */

/* Call a C function from Ocaml */

        .global caml_c_call
/* Function to call is in %g2 */
caml_c_call:
    /* Record lowest stack address and return address */
#if defined(__arch64__)
    /* We need another temporary to store %sp + BIAS, so we
       allocate a new window and use %l0.  */
       save %sp, -FRAME_SIZE, %sp
       add  %fp, BIAS, %l0
       Store (%l0, caml_bottom_of_stack)
       Store (%i7, caml_last_return_address)
       restore
#else  
        Store(%sp, caml_bottom_of_stack)
        Store(%o7, caml_last_return_address)
#endif
    /* Save the exception handler and alloc pointer */
        Store(Exn_ptr, caml_exception_pointer)
       Store(Alloc_ptr, caml_young_ptr)
    /* Call the C function */
        call    %g2
        nop                                              /* in delay slot */
    /* Reload return address */
        Load(caml_last_return_address, %o7)
    /* Reload alloc pointer */
       Load(caml_young_ptr, Alloc_ptr)
    /* Return to caller */
        retl
        nop                                              /* in delay slot */

/* Start the Ocaml program */

        .global caml_start_program
caml_start_program:
    /* Save all callee-save registers and also reserve space for a
       callback link on the stack.  Note that (PTR_SIZE*4) will always
       include the proper padding for the stack frame.  The exception
       handler is allocated below.  */
        save    %sp, -(FRAME_SIZE + (PTR_SIZE*4)), %sp
    /* Address of code to call */
        Address(caml_program, %l2)

    /* Code shared with caml_callback* */
L108:
    /* Set up a callback link on the stack. */
        Load(caml_bottom_of_stack, %l0)
        Load(caml_last_return_address, %l1)
        Load(caml_gc_regs, %l3)
        STADDR  %l0, [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 0)]
        STADDR  %l1, [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 1)]
        STADDR  %l3, [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 2)]
    /* Set up a trap frame to catch exceptions escaping the Ocaml code */
        call    L111
        sub     %sp, PTR_SIZE * 2, %sp
        b       L110
        nop
L111:   Load(caml_exception_pointer, Exn_ptr)
        STADDR  %o7,     [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 0)]
        STADDR  Exn_ptr, [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 1)]
        mov     %sp, Exn_ptr
    /* Reload allocation pointers */
        Load(caml_young_ptr, Alloc_ptr)
#ifdef INDIRECT_LIMIT
        Address(caml_young_limit, Alloc_limit)
#else
        Load(caml_young_limit, Alloc_limit)
#endif
    /* Call the Ocaml code */
L109:   call    %l2
        nop
    /* Pop trap frame and restore caml_exception_pointer */
        LDADDR  [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 1)], Exn_ptr
        add     %sp, PTR_SIZE * 2, %sp
        Store(Exn_ptr, caml_exception_pointer)
    /* Pop callback link, restoring the global variables */
L112:   LDADDR  [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 0)], %l0
        LDADDR  [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 1)], %l1
        LDADDR  [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 2)], %l2
        Store(%l0, caml_bottom_of_stack)
        Store(%l1, caml_last_return_address)
        Store(%l2, caml_gc_regs)
    /* Save allocation pointer */
        Store(Alloc_ptr, caml_young_ptr)
    /* Reload callee-save registers and return */
        ret
        restore %o0, 0, %o0     /* copy %o0 in this window to caller's %o0 */
L110:
    /* The trap handler */
        Store(Exn_ptr, caml_exception_pointer)
    /* Encode exception bucket as an exception result */
        b       L112
        or      %o0, 2, %o0

/* Raise an exception from C */

        .global caml_raise_exception
caml_raise_exception:
    /* Save exception bucket in a register outside the reg windows */
        mov     %o0, %g2
    /* Load exception pointer in a register outside the reg windows */
        Load(caml_exception_pointer, %g1)
    /* Pop some frames until the trap pointer is in the current frame. */
        cmp     %g1, %fp
        Bi(lt, L107)                    /* if Exn_ptr < %fp, over */
        nop
L106:   restore
        cmp     %fp, %g1                /* if %fp <= Exn_ptr, loop */
        Bi(le, L106)
        nop
L107:
    /* Reload allocation registers */
        Load(caml_young_ptr, Alloc_ptr)
#ifdef INDIRECT_LIMIT
        Address(caml_young_limit, Alloc_limit)
#else
        Load(caml_young_limit, Alloc_limit)
#endif
    /* Branch to exception handler */
        mov     %g1, %sp
        LDADDR  [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 0)], %g1
        LDADDR  [%sp + BIAS + FRAME_SIZE + (PTR_SIZE * 1)], Exn_ptr
        add     %sp, PTR_SIZE * 2, %sp
        jmp     %g1 + 8
    /* Restore bucket, in delay slot */
        mov     %g2, %o0

/* Callbacks C -> ML */

        .global caml_callback_exn
caml_callback_exn:
    /* Save callee-save registers and return address */
        save    %sp, -FRAME_SIZE-(PTR_SIZE * 4), %sp
    /* Initial shuffling of arguments */
        mov     %i0, %g1
        mov     %i1, %i0        /* first arg */
        mov     %g1, %i1        /* environment */
        b       L108
        LDADDR  [%g1], %l2      /* code pointer */

        .global caml_callback2_exn
caml_callback2_exn:
    /* Save callee-save registers and return address */
        save    %sp, -FRAME_SIZE-(PTR_SIZE * 4), %sp
    /* Initial shuffling of arguments */
        mov     %i0, %g1
        mov     %i1, %i0        /* first arg */
        mov     %i2, %i1        /* second arg */
        mov     %g1, %i2        /* environment */
        sethi   %hi(caml_apply2), %l2
        b       L108
	nop

        .global caml_callback3_exn
caml_callback3_exn:
    /* Save callee-save registers and return address */
        save    %sp, -FRAME_SIZE-(PTR_SIZE * 4), %sp
    /* Initial shuffling of arguments */
        mov     %i0, %g1
        mov     %i1, %i0        /* first arg */
        mov     %i2, %i1        /* second arg */
        mov     %i3, %i2        /* third arg */
        mov     %g1, %i3        /* environment */
        Address(caml_apply3, %l2)
        b       L108
	nop

#ifndef SYS_solaris
/* Glue code to call [caml_array_bound_error] */

        .global caml_ml_array_bound_error
caml_ml_array_bound_error:
        Address(caml_array_bound_error, %g2)
        b       caml_c_call
        nop
#endif

        .global caml_system__code_end
caml_system__code_end:

#ifdef SYS_solaris
        .section ".rodata"
#else
        .data
#endif
        .global caml_system__frametable
#if defined(__arch64__)
       .align  8

caml_system__frametable:
       .xword  1               /* one descriptor */
       .xword  L109            /* return address into callback */
#else

        .align  4               /* required for gas? */

caml_system__frametable:
        .word   1               /* one descriptor */
        .word   L109            /* return address into callback */

#endif /* __arch64__ */

        .half   -1              /* negative frame size => use callback link */
        .half   0               /* no roots */

#ifdef SYS_solaris
        .type caml_allocN, #function
        .type caml_call_gc, #function
        .type caml_c_call, #function
        .type caml_start_program, #function
        .type caml_raise_exception, #function
        .type caml_system__frametable, #object
#endif
