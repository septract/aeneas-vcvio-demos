//! Stream-cipher combiner: XOR a 32-byte keystream block with a 32-byte message.
//! This is the extracted, meaty (loop over a fixed-size array) piece of demo 2;
//! the keystream itself comes from a PRG modelled abstractly on the Lean side.
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits.

pub fn combine(ks: [u8; 32], m: [u8; 32]) -> [u8; 32] {
    let mut c = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        c[i] = ks[i] ^ m[i];
        i += 1;
    }
    c
}
