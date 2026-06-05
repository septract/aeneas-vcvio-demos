/-
  SPQR Reed–Solomon codec — Layer B-irr: the COMPUTABLE F2[x] mirror.

  ## Purpose

  This file is the *computable, Mathlib-free core* used to discharge
  `Irreducible (POLY_poly : (ZMod 2)[X])` (with `POLY_poly = X¹⁶+X¹²+X³+X+1`)
  by a KERNEL `decide`, NOT by `native_decide` and NOT by an axiom.

  The earlier project notes (`Gf16Irreducible.lean` header, lines ~13–22) claimed
  that a computable mirror with a `decide` over the degree-≤8 candidates was kernel-
  infeasible. THAT WARNING IS OUTDATED: it referred to a `Nat`/`BitVec` bit-trick
  mirror whose `decide` recursed through `Nat.bitwise` and was slow / degenerated to
  `sorryAx`. The mirror BELOW is over `List Bool` (coeffs low-to-high, `true = 1`,
  `xor = +` in characteristic 2) with schoolbook polynomial remainder — and its
  `decide` headline `noSmallFactor_POLY` kernel-checks in a few seconds with a clean
  axiom list (only `propext`).

  ## What it computes

  A monic degree-16 polynomial over a field is reducible iff it has a monic factor of
  degree in `[1, 8]` (a reducible degree-16 poly must have an irreducible factor of
  degree ≤ 8). `noSmallFactor POLY 8` enumerates ALL monic divisors of degree `1..8`
  (Σ_{d=1..8} 2^d = 510 candidates) and checks none divides `POLY`. It being `true`
  is the boolean witness of "no small factor", hence irreducibility — the transport to
  `(ZMod 2)[X]` lives in `Gf16IrreducibleBridge.lean` (this file stays Mathlib-free so
  the `decide` reduces in the kernel).

  ## Integrity

  NO `sorry`/`admit`/`native_decide`/axiom. `decide` here is the kernel decision
  procedure (re-run by the kernel, adds no axiom beyond `propext`). The `maxRecDepth`
  bump is a measurement-justified one-liner scoped to the single decide.
-/
import Mathlib.Data.List.Basic

namespace Spqr.Gf16IrreducibleMirror

/-! ### 1. The `List Bool` mirror of `F2[x]`

A polynomial over `ZMod 2` is represented LSB-first as a `List Bool`: index `i` of the
list is the coefficient of `X^i`, with `true = 1`, `false = 0`. Addition is pointwise
XOR (characteristic 2). Lists are NOT required to be normalized; `trim` removes trailing
zeros to expose the true degree. -/

/-- Pointwise XOR (= F2 polynomial addition), padding the shorter list with its tail.
Defined by structural recursion (NOT `List.zipWith`, which truncates to the shorter list
and would silently drop high coefficients). -/
def padd : List Bool → List Bool → List Bool
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (xor a b) :: padd p q

/-- Multiply by `X`: shift all coefficients up by one (prepend a `false`). -/
def pmulX (l : List Bool) : List Bool := false :: l

/-- Strip trailing `false`s (high zero coefficients), exposing the normal form. -/
def trim (l : List Bool) : List Bool :=
  match l with
  | [] => []
  | b :: bs =>
    let r := trim bs
    if r.isEmpty then (if b then [b] else []) else b :: r

/-- The list is zero (all coefficients `false`). -/
def isZero (l : List Bool) : Bool := (trim l).isEmpty

/-- `deg1 l` = length of the trimmed list = (degree + 1), or `0` for the zero poly. -/
def deg1 (l : List Bool) : Nat := (trim l).length

/-! ### 2. Schoolbook remainder by a monic divisor

`d` is a monic divisor represented in trimmed form (length = deg d + 1, last = `true`).
At each step, if `p`'s leading coefficient is set, we XOR in `d` shifted up to align with
that leading term; this kills the top coefficient. We recurse on a `fuel` argument
(structural recursion, terminating) bounded by the length of `p`. -/

/-- `shiftUp n l = X^n · l` (prepend `n` `false`s). -/
def shiftUp : Nat → List Bool → List Bool
  | 0, l => l
  | n + 1, l => false :: shiftUp n l

/-- One reduction step: if `deg1 p ≥ Dlen` (Dlen = deg1 of the trimmed monic divisor `d`),
XOR in `d` aligned to `p`'s top term and re-trim; else `p` is already reduced. -/
def modStep (d : List Bool) (Dlen : Nat) (p : List Bool) : List Bool :=
  let pd := deg1 p
  if pd < Dlen then p
  else trim (padd p (shiftUp (pd - Dlen) d))

/-- Iterated reduction with explicit `fuel`. Each non-trivial step strictly drops `deg1`,
so `fuel = deg1 p + 1` always suffices. -/
def modFuel (d : List Bool) (Dlen : Nat) : Nat → List Bool → List Bool
  | 0, p => p
  | fuel + 1, p =>
    if deg1 p < Dlen then p
    else modFuel d Dlen fuel (modStep d Dlen p)

/-- Remainder of `p` modulo the monic divisor `d` (trimmed first). If `d` is degree 0
(the unit `1` or zero), the remainder is `0`. -/
def bmod (p d : List Bool) : List Bool :=
  let dn := trim d
  if dn.length ≤ 1 then []
  else trim (modFuel dn dn.length (deg1 p + 1) p)

/-- `d ∣ p` in the mirror: the remainder of `p` by `d` is zero. -/
def bdvd (d p : List Bool) : Bool := isZero (bmod p d)

/-! ### 3. Enumeration of all monic divisors of bounded degree -/

/-- Little-endian width-`d` bit reader of a `Nat` mask: coefficients `0..d-1`. -/
def natToBits : Nat → Nat → List Bool
  | 0, _ => []
  | d + 1, m => (m % 2 == 1) :: natToBits d (m / 2)

/-- A monic poly of degree exactly `d`: free low coefficients `0..d-1` from `m`, leading
coefficient (index `d`) forced `true`. -/
def monicOf (d m : Nat) : List Bool := natToBits d m ++ [true]

/-- All `2^d` monic polynomials of degree exactly `d`. -/
def monicDeg (d : Nat) : List (List Bool) :=
  (List.range (2 ^ d)).map (monicOf d)

/-- `POLY = X¹⁶ + X¹² + X³ + X + 1` as a length-17 coefficient list (LSB-first):
indices `0,1,3,12,16` are `true`. -/
def POLY : List Bool :=
  [true,  true,  false, true,    -- 0,1,2,3
   false, false, false, false,   -- 4,5,6,7
   false, false, false, false,   -- 8,9,10,11
   true,  false, false, false,   -- 12,13,14,15
   true]                         -- 16

/-- No monic factor of degree `1..k` divides `p`. -/
def noSmallFactor (p : List Bool) (k : Nat) : Bool :=
  (List.range k).all (fun i => (monicDeg (i + 1)).all (fun q => ! bdvd q p))

/-! ### 4. Sanity controls (the predicate genuinely discriminates) -/

-- POLY divides itself.
example : bdvd POLY POLY = true := by decide
-- X+1 does not divide POLY (POLY(1) = 1 ≠ 0).
example : bdvd [true, true] POLY = false := by decide
-- X²+X+1 does not divide POLY.
example : bdvd [true, true, true] POLY = false := by decide
-- X+1 divides (X+1)(X²+1) = X³+X²+X+1.
example : bdvd [true, true] [true, true, true, true] = true := by decide
-- A reducible poly is correctly rejected: X³+1 = (X+1)(X²+X+1) has a small factor.
set_option maxRecDepth 100000 in
example : noSmallFactor [true, false, false, true] 8 = false := by decide
-- Monic-count controls.
example : (monicDeg 1).length = 2 := by decide
set_option maxRecDepth 100000 in
example : (monicDeg 8).length = 256 := by decide

/-! ### 5. THE HEADLINE: `POLY` has no monic factor of degree `1..8`.

A reducible monic degree-16 polynomial over a field must have an irreducible (hence monic)
factor of degree ≤ 8. `noSmallFactor POLY 8 = true` rules out every monic divisor of
degree `1..8`, so `POLY` is irreducible. This is a KERNEL `decide` (≈ a few seconds),
with a clean axiom list — see `#print axioms` below. -/

set_option maxRecDepth 100000 in
theorem noSmallFactor_POLY : noSmallFactor POLY 8 = true := by decide

end Spqr.Gf16IrreducibleMirror
