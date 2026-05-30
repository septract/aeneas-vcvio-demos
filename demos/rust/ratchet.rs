//! One symmetric-ratchet step's deterministic glue: split a 64-byte KDF/PRG output
//! block into the next 32-byte chain key and a 32-byte message key. The KDF/PRG itself
//! is modelled abstractly on the Lean side (its security is the hardness assumption);
//! this is the in-subset plumbing the security proof treats as value-adequate.
//! Kept inside the Aeneas-supported Rust subset: no unsafe, no FFI, no traits.

pub fn ratchet_split(block: [u8; 64]) -> ([u8; 32], [u8; 32]) {
    let mut ck = [0u8; 32]; // next chain key = block[0..32]
    let mut mk = [0u8; 32]; // message key    = block[32..64]
    let mut i = 0;
    while i < 32 {
        ck[i] = block[i];
        mk[i] = block[32 + i];
        i += 1;
    }
    (ck, mk)
}
