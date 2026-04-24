
#[cfg_attr(target_arch = "wasm32", path = "dir/dir1/dir2/wasm32.rs")]
#[cfg_attr(not(target_arch = "wasm32"), path = "dir/dir1/dir3/wasm32.rs")]
mod wasm32;

#[some_attr(path = "somewhere.rs")]
mod other;
