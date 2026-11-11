/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Data.Complex.BigOperators
import Qatlib.Foundations.PureStateMath.MixedState

set_option backward.isDefEq.respectTransparency false

/-!
# UnitaryLearn09 — Choi-state fidelity of unitary channels

Fixed source: Bisio–Chiribella–D'Ariano–Facchini–Perinotti,
*Optimal quantum learning of a unitary transformation*, arXiv:0903.0543v2
(PDF SHA-256 7740f8bf94c88b19a046c4c627cda8edf148bf92fe178c381fd20bceede57048),
Section II (Eqs. (1)–(4)) and the fidelity (8) following Fig. 1.

The paper measures the quality of a learning machine by the channel fidelity
between the emulated channel `C_U` and the target unitary channel `U`, i.e. the
fidelity between the Choi-Jamiolkowski states `C_U/d` and `|U⟩⟩⟨⟨U|/d`
(Sec. III, before Eq. (8)).  For a unitary channel the Choi state is the
rank-one projector on the vectorization `|U⟩⟩` of Eq. (1), so this fidelity is
`‖Tr[U† Û]‖²/d²`.

This file formalizes that scalar and its basic laws: the vectorized inner
product is the Hilbert–Schmidt trace `⟨⟨A|B⟩⟩ = Tr[A†B]`, the unitary channel
fidelity is one on identical unitaries, is symmetric, and is at most one.
The optimization results of the paper (quantum combs, Schur duality over the
irreducible decomposition of `U^{⊗N}`) are not formalized here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder

namespace Qatlib.Papers.UnitaryLearn09.MainResults

variable {I : Type*} [Fintype I]

/-- Paper Eq. (1): the vectorized inner product `⟨⟨A|B⟩⟩`.  It is Mathlib's
column-stacking vectorization `Matrix.vec`, which differs from the paper's
`|A⟩⟩ = ∑_{m,n} A_{mn}|m⟩|n⟩` only by the order of the two tensor factors. -/
def pairOverlap (A B : Matrix I I ℂ) : ℂ := star (Matrix.vec A) ⬝ᵥ Matrix.vec B

/-- The vectorized inner product is the Hilbert–Schmidt trace
`⟨⟨A|B⟩⟩ = Tr[A†B]`; this is the bridge from the paper's Eq. (1) to the trace
normalization used in Eq. (8). -/
theorem pairOverlap_eq_trace (A B : Matrix I I ℂ) :
    pairOverlap A B = (Aᴴ * B).trace :=
  Matrix.star_vec_dotProduct_vec A B

/-- Paper Eq. (8) for a unitary target: the channel fidelity of the unitary
channel `U` with the estimate `V`.  It is the fidelity of the corresponding
Choi-Jamiolkowski states `|U⟩⟩⟨⟨U|/d` and `|V⟩⟩⟨⟨V|/d`. -/
def unitaryChannelFidelity (U V : Matrix I I ℂ) : ℝ :=
  ‖(Uᴴ * V).trace‖ ^ 2 / (Fintype.card I : ℝ) ^ 2

/-- The unitary channel fidelity is the squared normalized vectorized overlap,
so `|U⟩⟩` and `|V⟩⟩` really are the Choi vectors entering Eq. (8). -/
theorem unitaryChannelFidelity_eq_pairOverlap (U V : Matrix I I ℂ) :
    unitaryChannelFidelity U V =
      ‖pairOverlap U V‖ ^ 2 / (Fintype.card I : ℝ) ^ 2 := by
  rw [unitaryChannelFidelity, pairOverlap_eq_trace]

/-- A unitary channel reproduced exactly has unit fidelity:
`F(U, U) = ‖Tr[U†U]‖²/d² = 1`. -/
theorem unitaryChannelFidelity_self [DecidableEq I] {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hd : 0 < Fintype.card I) :
    unitaryChannelFidelity U U = 1 := by
  have hUU : Uᴴ * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  have htrace : (Uᴴ * U).trace = (Fintype.card I : ℂ) := by
    rw [hUU, Matrix.trace_one]
  have hcard : ((Fintype.card I : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  rw [unitaryChannelFidelity, htrace, Complex.norm_natCast]
  field_simp

/-- Conjugating the trace of `U†V` gives the trace of `V†U`, hence the unitary
channel fidelity is symmetric in target and estimate. -/
theorem unitaryChannelFidelity_symm (U V : Matrix I I ℂ) :
    unitaryChannelFidelity U V = unitaryChannelFidelity V U := by
  unfold unitaryChannelFidelity
  have h : (Vᴴ * U).trace = (starRingEnd ℂ) ((Uᴴ * V).trace) := by
    have hconj : Vᴴ * U = (Uᴴ * V)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hconj, Matrix.trace_conjTranspose]
    rfl
  rw [h, Complex.norm_conj]

/-- The squared Frobenius mass of a matrix is the real part of `Tr[A†A]`. -/
theorem sum_normSq_eq_trace_re (A : Matrix I I ℂ) :
    ∑ p : I × I, ‖A p.1 p.2‖ ^ 2 = ((Aᴴ * A).trace).re := by
  rw [Matrix.trace, Complex.re_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re]

/-- A unitary matrix has squared Frobenius mass equal to its dimension,
`∑_{ij} ‖A_{ij}‖² = d`. -/
theorem sum_normSq_eq_card [DecidableEq I] {A : Matrix I I ℂ} (hA : Aᴴ * A = 1) :
    ∑ p : I × I, ‖A p.1 p.2‖ ^ 2 = (Fintype.card I : ℝ) := by
  rw [sum_normSq_eq_trace_re, hA, Matrix.trace_one]
  simp

/-- Cauchy–Schwarz on the diagonal bounds the trace of a unitary matrix by its
dimension: `‖Tr A‖ ≤ d`. -/
theorem norm_trace_le_card [DecidableEq I] {A : Matrix I I ℂ} (hA : Aᴴ * A = 1) :
    ‖A.trace‖ ≤ (Fintype.card I : ℝ) := by
  have hcard : (0 : ℝ) ≤ (Fintype.card I : ℝ) := by positivity
  have hrow : ∑ i : I, ‖A i i‖ ^ 2 ≤ (Fintype.card I : ℝ) := by
    calc ∑ i : I, ‖A i i‖ ^ 2
        ≤ ∑ i : I, ∑ j : I, ‖A i j‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Finset.single_le_sum (f := fun j : I => ‖A i j‖ ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)
      _ = ∑ p : I × I, ‖A p.1 p.2‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
      _ = (Fintype.card I : ℝ) := sum_normSq_eq_card hA
  have hcs : (∑ i : I, ‖A i i‖) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i : I, ‖A i i‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun i : I => ‖A i i‖) (g := fun _ : I => (1 : ℝ))
    simpa [mul_comm] using h
  have htrace : ‖A.trace‖ ≤ ∑ i : I, ‖A i i‖ := by
    rw [Matrix.trace]
    exact norm_sum_le _ _
  have hsquare : ‖A.trace‖ ^ 2 ≤ (Fintype.card I : ℝ) ^ 2 := by
    nlinarith [norm_nonneg A.trace, htrace, hrow, hcs, hcard]
  nlinarith [norm_nonneg A.trace, hsquare, hcard]

/-- The unitary channel fidelity respects the unit interval: `F(U,V) ≤ 1`. -/
theorem unitaryChannelFidelity_le_one [DecidableEq I] {U V : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hd : 0 < Fintype.card I) : unitaryChannelFidelity U V ≤ 1 := by
  have hUU : Uᴴ * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.mpr hUU
  have hVV : Vᴴ * V = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hV
    exact hV
  have hprod : (Uᴴ * V)ᴴ * (Uᴴ * V) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ V, hUU', Matrix.one_mul, hVV]
  have hbound := norm_trace_le_card hprod
  have hcard : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hd
  rw [unitaryChannelFidelity, div_le_one (by positivity)]
  nlinarith [norm_nonneg ((Uᴴ * V).trace), hbound]

end Qatlib.Papers.UnitaryLearn09.MainResults
