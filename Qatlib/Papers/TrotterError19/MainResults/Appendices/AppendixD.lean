/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Qatlib.Papers.TrotterError19.MainResults.SourceModel

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Filter Asymptotics

open Qatlib.Papers.TrotterError19.MainResults

namespace Qatlib.Papers.TrotterError19.MainResults.Appendices

section

/-- The paper's asymptotic notation `O(·)` in the number of orbitals
`n → ∞` (Section 2.1), spelled as Mathlib's `IsBigO atTop`. -/
abbrev BigO (f g : ℕ → ℝ) : Prop := f =O[atTop] g

/-- The coefficient data of the electronic-structure Hamiltonian (57),
represented by the six vector norms that Proposition D.2 constrains:
`‖·‖∞` and `‖·‖₁` for the kinetic vector `t⃗`, the potential vector `u⃗` and
the repulsion vector `v⃗`, each as a function of the orbital count `n`. -/
structure ElectronicStructureCoefficients where
  /-- `‖t⃗‖∞` as a function of `n`. -/
  kineticInf : ℕ → ℝ
  /-- `‖t⃗‖₁` as a function of `n`. -/
  kineticOne : ℕ → ℝ
  /-- `‖u⃗‖∞` as a function of `n`. -/
  potentialInf : ℕ → ℝ
  /-- `‖u⃗‖₁` as a function of `n`. -/
  potentialOne : ℕ → ℝ
  /-- `‖v⃗‖∞` as a function of `n`. -/
  repulsionInf : ℕ → ℝ
  /-- `‖v⃗‖₁` as a function of `n`. -/
  repulsionOne : ℕ → ℝ

/-- The commutator `[X,Y] = XY − YX` of an associative (noncommutative) ring. -/
def brk {R : Type*} [Mul R] [Sub R] (X Y : R) : R := X * Y - Y * X

/-- **Derivation identity for the bracket** (used in the proof of Lemma D.3,
Eq. (199), third line): `[W, N·M] = [W,N]·M + N·[W,M]`.  This is a pure ring
identity that holds in any noncommutative ring. -/
theorem commutator_mul_nested {R : Type*} [Ring R] (W N M : R) :
    brk W (N * M) = brk W N * M + N * brk W M := by
  unfold brk
  noncomm_ring

/-- **Lemma D.3, Eq. (199), third commutation rule**, derived from the second
rule: if `[A_j†A_k, N_l] = δ_{kl} A_j†A_l − δ_{jl} A_l†A_k` for every `l`,
then the same derivation property gives
`[A_j†A_k, N_lN_m] = (δ_{kl}A_j†A_l − δ_{jl}A_l†A_k)N_m
 + N_l(δ_{km}A_j†A_m − δ_{jm}A_m†A_k)`.

This formalises the passage from Eq. (199) line 2 to line 3 in the source. -/
theorem lemmaD3_rule3 {R : Type*} [Ring R]
    (w N M δklAjAlδjlAlAk δkmAjAmδjmAmAk : R)
    (h2 : brk w N = δklAjAlδjlAlAk)
    (h2m : brk w M = δkmAjAmδjmAmAk) :
    brk w (N * M) = δklAjAlδjlAlAk * M + N * δkmAjAmδjmAmAk := by
  rw [commutator_mul_nested, h2, h2m]

/-- A second-quantized operator, represented by the two quantities that
Proposition D.4 constrains: its number of layers and the 1-norm of its
coefficient vector. -/
structure SecondQuantizedOperator where
  /-- Number of layers `q` (paper's definition below Eq. (199)). -/
  layers : ℕ
  /-- The 1-norm `‖w⃗‖₁` of the coefficient vector. -/
  coeffOne : ℝ

end

end Qatlib.Papers.TrotterError19.MainResults.Appendices
