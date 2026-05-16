//! Runtime intrinsics for u256 (256-bit integer) arithmetic.
//!
//! These functions are registered as imported symbols in the Cranelift JIT,
//! enabling Sonatina IR with I256 operations to execute natively.
//!
//! Representation: u256 as `[u64; 4]` in little-endian limb order
//! (limb[0] is least significant).

/// u256 addition: result = a + b (wrapping)
#[unsafe(no_mangle)]
pub extern "C" fn __u256_add(a: *const [u64; 4], b: *const [u64; 4], result: *mut [u64; 4]) {
    let a = unsafe { &*a };
    let b = unsafe { &*b };
    let r = unsafe { &mut *result };
    let mut carry = 0u64;
    for i in 0..4 {
        let (s1, c1) = a[i].overflowing_add(b[i]);
        let (s2, c2) = s1.overflowing_add(carry);
        r[i] = s2;
        carry = (c1 as u64) + (c2 as u64);
    }
}

/// u256 subtraction: result = a - b (wrapping)
#[unsafe(no_mangle)]
pub extern "C" fn __u256_sub(a: *const [u64; 4], b: *const [u64; 4], result: *mut [u64; 4]) {
    let a = unsafe { &*a };
    let b = unsafe { &*b };
    let r = unsafe { &mut *result };
    let mut borrow = 0u64;
    for i in 0..4 {
        let (s1, c1) = a[i].overflowing_sub(b[i]);
        let (s2, c2) = s1.overflowing_sub(borrow);
        r[i] = s2;
        borrow = (c1 as u64) + (c2 as u64);
    }
}

/// u256 equality: returns 1 if a == b, 0 otherwise
#[unsafe(no_mangle)]
pub extern "C" fn __u256_eq(a: *const [u64; 4], b: *const [u64; 4]) -> u64 {
    let a = unsafe { &*a };
    let b = unsafe { &*b };
    (a == b) as u64
}

/// u256 less-than (unsigned): returns 1 if a < b, 0 otherwise
#[unsafe(no_mangle)]
pub extern "C" fn __u256_lt(a: *const [u64; 4], b: *const [u64; 4]) -> u64 {
    let a = unsafe { &*a };
    let b = unsafe { &*b };
    for i in (0..4).rev() {
        if a[i] < b[i] {
            return 1;
        }
        if a[i] > b[i] {
            return 0;
        }
    }
    0
}

/// u256 is-zero: returns 1 if a == 0, 0 otherwise
#[unsafe(no_mangle)]
pub extern "C" fn __u256_is_zero(a: *const [u64; 4]) -> u64 {
    let a = unsafe { &*a };
    (a[0] | a[1] | a[2] | a[3] == 0) as u64
}

/// u256 multiplication: result = a * b (wrapping, lower 256 bits)
#[unsafe(no_mangle)]
pub extern "C" fn __u256_mul(a: *const [u64; 4], b: *const [u64; 4], result: *mut [u64; 4]) {
    let a = unsafe { &*a };
    let b = unsafe { &*b };
    let r = unsafe { &mut *result };
    *r = [0u64; 4];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            if i + j >= 4 {
                break;
            }
            let prod = (a[i] as u128) * (b[j] as u128) + (r[i + j] as u128) + carry;
            r[i + j] = prod as u64;
            carry = prod >> 64;
        }
    }
}

/// u256 addmod: result = (a + b) % m
#[unsafe(no_mangle)]
pub extern "C" fn __u256_addmod(
    a: *const [u64; 4],
    b: *const [u64; 4],
    m: *const [u64; 4],
    result: *mut [u64; 4],
) {
    let a = unsafe { &*a };
    let b = unsafe { &*b };
    let m = unsafe { &*m };
    let r = unsafe { &mut *result };

    // Add with carry into 5 limbs
    let mut sum = [0u64; 5];
    let mut carry = 0u64;
    for i in 0..4 {
        let (s1, c1) = a[i].overflowing_add(b[i]);
        let (s2, c2) = s1.overflowing_add(carry);
        sum[i] = s2;
        carry = (c1 as u64) + (c2 as u64);
    }
    sum[4] = carry;

    // Reduce: while sum >= m, subtract m
    // Simple approach for MVP — not optimized
    loop {
        let mut ge = false;
        for i in (0..5).rev() {
            let mi = if i < 4 { m[i] } else { 0 };
            if sum[i] > mi {
                ge = true;
                break;
            }
            if sum[i] < mi {
                break;
            }
            if i == 0 {
                ge = true;
            }
        }
        if !ge {
            break;
        }

        let mut borrow = 0u64;
        for i in 0..5 {
            let mi = if i < 4 { m[i] } else { 0 };
            let (s1, c1) = sum[i].overflowing_sub(mi);
            let (s2, c2) = s1.overflowing_sub(borrow);
            sum[i] = s2;
            borrow = (c1 as u64) + (c2 as u64);
        }
    }

    r.copy_from_slice(&sum[..4]);
}

/// u256 mulmod: result = (a * b) % m
#[unsafe(no_mangle)]
pub extern "C" fn __u256_mulmod(
    a: *const [u64; 4],
    b: *const [u64; 4],
    m: *const [u64; 4],
    result: *mut [u64; 4],
) {
    let a = unsafe { &*a };
    let b = unsafe { &*b };
    let m = unsafe { &*m };
    let r = unsafe { &mut *result };

    // Full 512-bit product
    let mut prod = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let p = (a[i] as u128) * (b[j] as u128) + (prod[i + j] as u128) + carry;
            prod[i + j] = p as u64;
            carry = p >> 64;
        }
        prod[i + 4] = carry as u64;
    }

    // Reduce 512-bit product modulo m using repeated subtraction
    // This is O(n) where n is the quotient — fine for small values,
    // needs Barrett/Montgomery reduction for production use
    let mut remainder = prod;
    loop {
        // Check if remainder >= m (comparing upper limbs first)
        let mut ge = false;
        let mut all_upper_zero = true;
        for i in (4..8).rev() {
            if remainder[i] > 0 {
                ge = true;
                all_upper_zero = false;
                break;
            }
        }
        if all_upper_zero {
            for i in (0..4).rev() {
                if remainder[i] > m[i] {
                    ge = true;
                    break;
                }
                if remainder[i] < m[i] {
                    break;
                }
                if i == 0 {
                    ge = true;
                }
            }
        }
        if !ge {
            break;
        }

        // Subtract m from remainder
        let mut borrow = 0u64;
        for i in 0..8 {
            let mi = if i < 4 { m[i] } else { 0 };
            let (s1, c1) = remainder[i].overflowing_sub(mi);
            let (s2, c2) = s1.overflowing_sub(borrow);
            remainder[i] = s2;
            borrow = (c1 as u64) + (c2 as u64);
        }
    }

    r.copy_from_slice(&remainder[..4]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u256_add() {
        let a = [3u64, 0, 0, 0];
        let b = [4u64, 0, 0, 0];
        let mut r = [0u64; 4];
        __u256_add(&a, &b, &mut r);
        assert_eq!(r, [7, 0, 0, 0]);
    }

    #[test]
    fn test_u256_mul() {
        let a = [7u64, 0, 0, 0];
        let b = [3u64, 0, 0, 0];
        let mut r = [0u64; 4];
        __u256_mul(&a, &b, &mut r);
        assert_eq!(r, [21, 0, 0, 0]);
    }

    #[test]
    fn test_u256_addmod_small() {
        let a = [42u64, 0, 0, 0];
        let b = [17u64, 0, 0, 0];
        let m = [100u64, 0, 0, 0];
        let mut r = [0u64; 4];
        __u256_addmod(&a, &b, &m, &mut r);
        assert_eq!(r, [59, 0, 0, 0]); // 42 + 17 = 59 < 100
    }

    #[test]
    fn test_u256_addmod_with_reduction() {
        let a = [90u64, 0, 0, 0];
        let b = [20u64, 0, 0, 0];
        let m = [100u64, 0, 0, 0];
        let mut r = [0u64; 4];
        __u256_addmod(&a, &b, &m, &mut r);
        assert_eq!(r, [10, 0, 0, 0]); // (90 + 20) % 100 = 10
    }

    #[test]
    fn test_u256_mulmod_small() {
        let a = [7u64, 0, 0, 0];
        let b = [3u64, 0, 0, 0];
        let m = [100u64, 0, 0, 0];
        let mut r = [0u64; 4];
        __u256_mulmod(&a, &b, &m, &mut r);
        assert_eq!(r, [21, 0, 0, 0]); // 7 * 3 = 21 < 100
    }

    #[test]
    fn test_u256_eq() {
        let a = [42u64, 0, 0, 0];
        let b = [42u64, 0, 0, 0];
        let c = [43u64, 0, 0, 0];
        assert_eq!(__u256_eq(&a, &b), 1);
        assert_eq!(__u256_eq(&a, &c), 0);
    }

    #[test]
    fn test_u256_pow5() {
        // 3^5 = 243 via mulmod chain
        let three = [3u64, 0, 0, 0];
        let m = [u64::MAX, u64::MAX, u64::MAX, u64::MAX]; // huge modulus
        let mut x2 = [0u64; 4];
        let mut x4 = [0u64; 4];
        let mut x5 = [0u64; 4];
        __u256_mulmod(&three, &three, &m, &mut x2); // 9
        __u256_mulmod(&x2, &x2, &m, &mut x4); // 81
        __u256_mulmod(&x4, &three, &m, &mut x5); // 243
        assert_eq!(x5, [243, 0, 0, 0]);
    }
}
