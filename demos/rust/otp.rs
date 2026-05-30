//! One-time pad over a single fixed-width word (u64 "block").
//! Minimal end-to-end demo: no loop, so Aeneas extracts a straight-line
//! function and value-adequacy is provable by computation.
//! XOR is self-inverse: this is both encrypt and decrypt.

pub fn xor(k: u64, m: u64) -> u64 {
    k ^ m
}
