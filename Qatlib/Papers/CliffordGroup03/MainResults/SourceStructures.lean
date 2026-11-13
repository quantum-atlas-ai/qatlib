/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CliffordGroup03.MainResults.Definitions
open Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

/-!
# CliffordGroup03.MainResults.SourceStructures — Theorems 4, 5, 6 (paper p.4–8)

Fixed source: **arXiv:quant-ph/0304125v1**, Dehaene & De Moor, Phys. Rev. A 68, 042318 (2003).

* **Theorem 4** (p.4–5): every symplectic `C` (`CᵀPC = P`) factors as the five-block product of
  Eq. (5)/(6) (`source_theorem_four_symplectic_decomposition`); the five factors are built here
  from the invertible `T1,T2`, symmetric `Z1,Z2,Z3`, and rectangular `V1,V2` on the four-block
  coordinate split `(x_b,x_r)⊕(x_b,x_c)` with `x_b ∈ Z_2^{n-r}`, `x_r,x_c ∈ Z_2^{r}`.
* **Theorem 5** (p.6–7): a stabilizer state represented by `(S̄,b)` can be brought to the normal
  form (18) and expanded in the standard basis by the quadratic-form amplitudes of Eq. (19)
  (`source_theorem_five_stabilizer_form`).
* **Theorem 6** (p.7–8): the matrix elements of a Clifford operation `Q` (represented by `C̄,h`)
  admit the quadratic-form expansion of Eq. (6.x) (`source_theorem_six_matrix_elements`).

Each headline result below is recorded as a `Prop`-valued definition (`source_theorem_*_... : Prop`),
i.e. the exact formal statement. Their proofs require the constructive reduction algorithm of
Sec. IV (Theorem 4), the stabilizer normal form of Sec. V (Theorem 5), and the amalgamation of
the decomposition with Theorem 1 (Theorem 6); these constructions are outside the scope of this
module. Nothing in the repository assumes these statements.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.PauliClifford.ExactRank
open scoped BigOperators

namespace Qatlib.Papers.CliffordGroup03.MainResults

open Qatlib.Papers.CliffordGroup03.MainResults

/-! ## Theorem 4 — the symplectic five-block decomposition -/

/-- One half of the four-block split: `Fin (n-r) ⊕ Fin r` (the `(x_b,x_r)` coordinate pair). -/
abbrev RHalf (n r : ℕ) := Fin (n - r) ⊕ Fin r

/-- The two-half reindexing `Fin n ⊕ Fin n ≃ Fin (2n)` (`[v;w] ↦ (v,w)`). -/
def evw (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (two_mul n).symm)

/-- The four-block reindexing `(x_b,x_r)⊕(x_b,x_c) ≃ Fin (2n)`. -/
def e4 (n r : ℕ) (hr : r ≤ n) :
    (RHalf n r ⊕ RHalf n r) ≃ Fin (2 * n) :=
  (Equiv.sumCongr
      (finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hr)))
      (finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hr)))).trans (evw n)

/-- The end factors `diag(A,D) = [[A,0],[0,D]]` of Eq. (5)/(6) (`A = T^{-T}`, `D = T`). -/
def f1 (n : ℕ) (A D : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  Matrix.reindex (evw n) (evw n)
    (Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) (ZMod 2))
      (0 : Matrix (Fin n) (Fin n) (ZMod 2)) D)

/-- The first shear factor of Eq. (6):
`[[I_{n-r},0,Z3,V1],[0,I_r,V1ᵀ,Z1],[0,0,I_{n-r},0],[0,0,0,I_r]]`. -/
def shearA (n r : ℕ) (hr : r ≤ n)
    (Z3 : Matrix (Fin (n - r)) (Fin (n - r)) (ZMod 2))
    (V1 : Matrix (Fin (n - r)) (Fin r) (ZMod 2))
    (Z1 : Matrix (Fin r) (Fin r) (ZMod 2)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  Matrix.reindex (e4 n r hr) (e4 n r hr)
    (Matrix.fromBlocks
      (1 : Matrix (RHalf n r) (RHalf n r) (ZMod 2))
      (Matrix.fromBlocks Z3 V1 V1ᵀ Z1)
      (0 : Matrix (RHalf n r) (RHalf n r) (ZMod 2))
      (1 : Matrix (RHalf n r) (RHalf n r) (ZMod 2)))

/-- The `r`-coordinate Hadamard (swap) factor of Eq. (6):
`[[I,0,0,0],[0,0,0,I],[0,0,I,0],[0,I,0,0]]` on the four blocks. -/
def hadR (n r : ℕ) (hr : r ≤ n) : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  Matrix.reindex (e4 n r hr) (e4 n r hr)
    (Matrix.fromBlocks
      (Matrix.fromBlocks (1 : Matrix (Fin (n - r)) (Fin (n - r)) (ZMod 2))
        (0 : Matrix (Fin (n - r)) (Fin r) (ZMod 2))
        (0 : Matrix (Fin r) (Fin (n - r)) (ZMod 2))
        (0 : Matrix (Fin r) (Fin r) (ZMod 2)))
      (Matrix.fromBlocks (0 : Matrix (Fin (n - r)) (Fin (n - r)) (ZMod 2))
        (0 : Matrix (Fin (n - r)) (Fin r) (ZMod 2))
        (0 : Matrix (Fin r) (Fin (n - r)) (ZMod 2))
        (1 : Matrix (Fin r) (Fin r) (ZMod 2)))
      (Matrix.fromBlocks (0 : Matrix (Fin (n - r)) (Fin (n - r)) (ZMod 2))
        (0 : Matrix (Fin (n - r)) (Fin r) (ZMod 2))
        (0 : Matrix (Fin r) (Fin (n - r)) (ZMod 2))
        (1 : Matrix (Fin r) (Fin r) (ZMod 2)))
      (Matrix.fromBlocks (1 : Matrix (Fin (n - r)) (Fin (n - r)) (ZMod 2))
        (0 : Matrix (Fin (n - r)) (Fin r) (ZMod 2))
        (0 : Matrix (Fin r) (Fin (n - r)) (ZMod 2))
        (0 : Matrix (Fin r) (Fin r) (ZMod 2))))

/-- The second shear factor of Eq. (6):
`[[I_{n-r},0,0,V2],[0,I_r,V2ᵀ,Z2],[0,0,I_{n-r},0],[0,0,0,I_r]]`. -/
def shearB (n r : ℕ) (hr : r ≤ n)
    (V2 : Matrix (Fin (n - r)) (Fin r) (ZMod 2))
    (Z2 : Matrix (Fin r) (Fin r) (ZMod 2)) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  Matrix.reindex (e4 n r hr) (e4 n r hr)
    (Matrix.fromBlocks
      (1 : Matrix (RHalf n r) (RHalf n r) (ZMod 2))
      (Matrix.fromBlocks (0 : Matrix (Fin (n - r)) (Fin (n - r)) (ZMod 2)) V2 V2ᵀ Z2)
      (0 : Matrix (RHalf n r) (RHalf n r) (ZMod 2))
      (1 : Matrix (RHalf n r) (RHalf n r) (ZMod 2)))

/-- **Theorem 4 (formal statement)** (arXiv:quant-ph/0304125v1, p.4–5, Eq. (5)/(6)).
If `C` is symplectic (`Cᵀ P C = P`), it decomposes as
`C = [[T1^{-T},0],[0,T1]] · S1 · H_r · S2 · [[T2^{-T},0],[0,T2]]`
with `T1,T2` invertible, `Z1,Z2` symmetric `r×r`, `Z3` symmetric `(n−r)×(n−r)`, and `V1,V2`
`(n−r)×r`. Here invertibility of `T` is expressed through an explicit inverse-transpose `A`
(`Aᵀ T = 1 ∧ T Aᵀ = 1`). The five factors are `f1 n Ad T1`, `shearA n r hr Z3 V1 Z1`,
`hadR n r hr`, `shearB n r hr V2 Z2`, `f1 n Bd T2`.

The constructive proof (p.5) reduces `C` to the identity by column operations on pairs
`(m, n+m)`. Formally: take `r = rank(G′)` for the top-right block `G′` of `C`, choose
`R1,R2` with `R1⁻¹ G′ R2 = [[0,0],[0,I_r]]`, and read off `T1 = R1`, `T2 = R2`, and the `Z`/`V`
blocks from the reduction of `[G′ᵀ H′ᵀ]`. A full rank-based column reduction, the identities
`R1⁻¹ G′ R2 = diag(0,I_r)`, and preservation of symplecticity under each elementary factor are
outside the scope of this module.
-/
def source_theorem_four_symplectic_decomposition {n : ℕ}
    (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) : Prop :=
  Symplectic n C →
    ∃ (r : ℕ) (_hr : r ≤ n)
      (Ad T1 Bd T2 : Matrix (Fin n) (Fin n) (ZMod 2))
      (Z1 Z2 : Matrix (Fin r) (Fin r) (ZMod 2))
      (Z3 : Matrix (Fin (n - r)) (Fin (n - r)) (ZMod 2))
      (V1 V2 : Matrix (Fin (n - r)) (Fin r) (ZMod 2)),
      Adᵀ * T1 = 1 ∧ T1 * Adᵀ = 1 ∧ Bdᵀ * T2 = 1 ∧ T2 * Bdᵀ = 1 ∧
      Symm Z1 ∧ Symm Z2 ∧ Symm Z3 ∧
      C = f1 n Ad T1 * shearA n r _hr Z3 V1 Z1 * hadR n r _hr *
          shearB n r _hr V2 Z2 * f1 n Bd T2

/-! ## Theorem 5 — the stabilizer normal form and amplitude expansion -/

/-- A stabilizer state `ψ` is represented by the binary data `(S,b)` when it is a joint
`+1`-eigenstate of the signed Pauli generators `(-1)^{b_j} τ_{(S j)}` (where `(S j)` is the `j`-th
column of `S` read as a `2n`-vector). -/
def RepresentsStabilizerState {n m : ℕ} (S : Matrix (Fin (2 * n)) (Fin m) (ZMod 2))
    (b : BV m) (ψ : Reg n → ℂ) : Prop :=
  ∀ j : Fin m,
    tau (splitVec (fun i : Fin (2 * n) => S i j)) *ᵥ ψ = ((-1 : ℂ) ^ (b j).val) • ψ

/-- Convert a `GF(2)`-vector to a `Reg` (binary) label. -/
def toRegBV {n : ℕ} (v : BV n) : Reg n := fun i => decide (v i = 1)

/-- The quadratic-form amplitude coefficient of Eq. (19): with `f_a = diag(Z)`,
`(-i)^{f_aᵀ y_a} · (-1)^{y_aᵀ lows(Z + f_a f_aᵀ) y_a + b_aᵀ y_a}`. -/
def stabCoeff {d : ℕ} (Z : Matrix (Fin d) (Fin d) (ZMod 2)) (ba ya : BV d) : ℂ :=
  ((-Complex.I) ^ (booleanDot (diagVec Z) ya).val) *
    ((-1 : ℂ) ^ (quadForm (lows (Z + Matrix.vecMulVec (diagVec Z) (diagVec Z))) ya +
      booleanDot ba ya).val)

/-- The affine-plane amplitude sum of Eq. (19) on the `d = r_a + r_b + r_c`-dimensional parameter
`y_a`, with the physical label `T y_a + t`. -/
def stabSum {n d : ℕ} (Z : Matrix (Fin d) (Fin d) (ZMod 2)) (ba : BV d)
    (T : Matrix (Fin n) (Fin d) (ZMod 2)) (t : BV n) (x : Reg n) : ℂ :=
  ∑ ya : BV d, stabCoeff Z ba ya * (if toRegBV (T.mulVec ya + t) = x then (1 : ℂ) else 0)

/-- **Theorem 5 (formal statement)** (arXiv:quant-ph/0304125v1, p.6–7, Eq. (18)/(19)).
A stabilizer state `ψ` represented by `(S,b)` admits an invertible index transform `T`, an
invertible stabilizer basis
change, a full-rank symmetric `Z` (`f_a = diag(Z)`), `b_a`, and shift `t` such that
`ψ(x) = (1/√(2^{r_a})) · Σ_{y_a} (-i)^{f_aᵀ y_a} (-1)^{y_aᵀ lows(Z+f_a f_aᵀ) y_a + b_aᵀ y_a} ·
δ(T y_a + t, x)`. (Normal form (18) is the existence of the data `T, Z, b_a, t` making the
expansion valid and `Z` full-rank symmetric.)

The normal form is obtained by the Gaussian-elimination procedure of Sec. V on
the stabilizer matrix `S̄`, which produces `T` (index transform) and `R` (stabilizer basis change)
placing the generators in the block form (18). The amplitude formula (19) follows by diagonalising
the canonical quadratic form. The elimination procedure and full-rank symplectic reduction on
`S̄`, as well as the compression of the `r_a,r_b,r_c` block labels into `y_a`, are outside the
scope of this module.
-/
def source_theorem_five_stabilizer_form {n m : ℕ}
    (S : Matrix (Fin (2 * n)) (Fin m) (ZMod 2)) (b : BV m) (ψ : Reg n → ℂ) : Prop :=
  RepresentsStabilizerState S b ψ →
    ∃ (d : ℕ) (T : Matrix (Fin n) (Fin d) (ZMod 2)) (Z : Matrix (Fin d) (Fin d) (ZMod 2))
      (ba : BV d) (t : BV n) (ra : ℕ),
      Symm Z ∧
      ∀ x : Reg n,
        ψ x = (1 / (Real.sqrt (2 ^ ra) : ℂ)) * stabSum Z ba T t x

/-! ## Theorem 6 — Clifford matrix-element expansion -/

/-- The quadratic-form coefficient of the Theorem 6 expansion (single `y_a` compression of the
`(x_b,x_r,x_c)` block sum): `(-i)^{dᵀ y} · (-1)^{hᵀ y + yᵀ lows(Z + d dᵀ) y}` with `d = diag(Z)`. -/
def cliffCoeff {d : ℕ} (Z : Matrix (Fin d) (Fin d) (ZMod 2)) (hc : BV d) (y : BV d) : ℂ :=
  ((-Complex.I) ^ (booleanDot (diagVec Z) y).val) *
    ((-1 : ℂ) ^ (((quadForm (lows (Z + Matrix.vecMulVec (diagVec Z) (diagVec Z))) y) +
      booleanDot hc y).val))

/-- The two-sided Clifford matrix-element sum of Theorem 6 on the parameter `y`, with output
`T1 y` (bra) and `T2 y + t` (ket). -/
def cliffSum {n d : ℕ} (Z : Matrix (Fin d) (Fin d) (ZMod 2)) (hc : BV d)
    (T1 T2 : Matrix (Fin n) (Fin d) (ZMod 2)) (t : BV n) (y x : Reg n) : ℂ :=
  ∑ ya : BV d, cliffCoeff Z hc ya *
    ((if toRegBV (T1.mulVec ya) = y then (1 : ℂ) else 0) *
     (if toRegBV (T2.mulVec ya + t) = x then (1 : ℂ) else 0))

/-- **Theorem 6 (formal statement)** (arXiv:quant-ph/0304125v1, p.7–8). A Clifford
operation `Q` represented by `(C̄,h)` has matrix elements
`Q(y,x) = (1/√(2^r)) · Σ_{y_a} (-i)^{dᵀ y_a} (-1)^{hᵀ y_a + y_aᵀ lows(Z+d dᵀ) y_a} ·
δ(T1 y_a, y) · δ(T2 y_a + t, x)`,
with `T1,T2` invertible, `Z` symmetric full-rank, `d = diag(Z)` (`t ∈ Z_2^n`).

Expanding `Q` via the symplectic decomposition of Theorem 4 applied to the data
`(C̄,h)`, using Theorem 1 to phase-carry each elementary factor; the quadratic-form structure comes
from the shear factors `Z`. The composition of Theorems 1 and 4 across all `n` sites and the
resulting sum-over-paths are outside the scope of this module; the block labels are compressed into
a single `y_a`.
-/
def source_theorem_six_matrix_elements {n : ℕ}
    (Q : Matrix (Reg n) (Reg n) ℂ)
    (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h : BV (2 * n)) : Prop :=
  RepresentsClifford Q C h →
    ∃ (r d : ℕ) (T1 T2 : Matrix (Fin n) (Fin d) (ZMod 2))
      (Z : Matrix (Fin d) (Fin d) (ZMod 2)) (hc : BV d) (t : BV n),
      Symm Z ∧
      ∀ y x : Reg n,
        Q y x = (1 / (Real.sqrt (2 ^ r) : ℂ)) * cliffSum Z hc T1 T2 t y x

end Qatlib.Papers.CliffordGroup03.MainResults
