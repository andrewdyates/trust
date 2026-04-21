// Compiler:
//
// Run-time:
//   stdout: Success
//   status: signal

fn main() {
    std::panic::set_hook(Box::new(|_| {
        println!("Success");
        std::process::abort();
    }));

    let arg_count = std::env::args().count();
    let int = isize::MAX;
    let _int = int + arg_count as isize; // overflow

    // If overflow checking is disabled, we should reach here.
    #[cfg(not(debug_assertions))]
    // SAFETY: calling libc exit/abort to terminate the process.
    unsafe {
        println!("Success");
        std::process::abort();
    }
}
