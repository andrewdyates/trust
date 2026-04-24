// tRust: regression test for rust-lang#129347
// `#[inline(never)]` on async fn should be respected by the coroutine body,
// not just the outer wrapper that constructs the future.
//
// Before the fix, the desugared coroutine had `InlineAttr::None` (default),
// so LLVM was free to inline the actual async fn body even when the user
// explicitly asked it not to be inlined.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ compile-flags: -Copt-level=3
//@ edition: 2021

#![crate_type = "lib"]

// CHECK-LABEL: @call_inline_never_async
// The function body should contain a call to the coroutine poll, not have
// it inlined. We check that there is a `call` instruction and that the
// `noinline` attribute appears on the coroutine function.
// CHECK: call
#[no_mangle]
pub async fn call_inline_never_async() -> u64 {
    inline_never_work().await
}

// CHECK: noinline
#[inline(never)]
#[no_mangle]
pub async fn inline_never_work() -> u64 {
    // Do enough work that LLVM would want to inline this
    let mut sum: u64 = 0;
    let values = [1u64, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    for &v in values.iter() {
        sum = sum.wrapping_add(v.wrapping_mul(v));
    }
    sum
}
