use sp1_primitives::consts::fd::FD_PUBLIC_VALUES;
use sp1_zkvm::{read_vec_raw, syscalls::syscall_write};

fn read_input<const N: usize>() -> [u8; N] {
    // Use SP1's fresh, aligned input region. Hint syscalls initialize memory;
    // reusing a previously written stack buffer is not their memory contract.
    let input = read_vec_raw();
    assert_eq!(input.len, N, "unexpected SP1 input length");
    // SAFETY: read_vec_raw initialized exactly input.len bytes, which is N.
    unsafe { input.ptr.cast::<[u8; N]>().read() }
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_sp1_read_u32() -> u32 {
    u32::from_le_bytes(read_input())
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_sp1_read_u64() -> u64 {
    u64::from_le_bytes(read_input())
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_sp1_commit_u32(value: u32) {
    let bytes = value.to_le_bytes();
    syscall_write(FD_PUBLIC_VALUES, bytes.as_ptr(), bytes.len());
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_sp1_commit_u64(value: u64) {
    let bytes = value.to_le_bytes();
    syscall_write(FD_PUBLIC_VALUES, bytes.as_ptr(), bytes.len());
}
