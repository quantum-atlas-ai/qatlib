/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option backward.isDefEq.respectTransparency false

/-!
# Range and Dual-Witness Characterizations of Span Programs

This module proves Lemma 2.2 on equivalent primal and dual characterizations of the
Boolean function computed by a span program: `f_P(x) = 1` iff the target vector lies
in `Range(A Π(x))`, and `f_P(x) = 0` iff there exists a dual witness `|w'⟩` satisfying
`⟨t|w'⟩ ≠ 0` and `A† Π(x) |w'⟩ = 0`.

## Main statements

* `lemma_2_2_range_characterization`: `f_P(x) = true` iff some linear combination of
  available input vectors equals `P.target`.
* `lemma_2_2_dual_witness`: if `f_P(x) = false`, there exists `w'` with
  `Inner P.target w' ≠ 0` orthogonal to all available input vectors.
* `lemma_2_2_dual_witness_converse`: any vector `w'` with `Inner P.target w' ≠ 0`
  orthogonal to all available input vectors forces `f_P(x) = false`.

## References

* [Reichardt, 2009][Reichardt2009SpanPrograms], Section 2, Lemma 2.2, p. 8.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.SpanProgReich09.MainResults.Section2

open Qatlib.Papers.SpanProgReich09.MainResults
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

variable {n : ℕ}

/-- **Lemma 2.2, range form**: `f_P(x) = 1` iff the target vector lies in the range
of `A Π(x)`, i.e. iff some combination of available input vectors equals `|t⟩`. -/
theorem lemma_2_2_range_characterization (P : SpanProgram n) (x : BitString n) :
    (P.fP x = true ↔ ∃ w : Fin P.idx → ℂ, P.combo x w = P.target) := by
  unfold SpanProgram.fP
  by_cases h : ∃ w : Fin P.idx → ℂ, P.combo x w = P.target
  · simp [h]
  · simp [h]

/-- **Lemma 2.2, dual-witness form**: if `f_P(x) = 0`, then there is a dual witness
`|w'⟩` with `⟨t|w'⟩ ≠ 0` and `⟨v_i|w'⟩ = 0` for every available input vector `i ∈ I(x)`. -/
theorem lemma_2_2_dual_witness (P : SpanProgram n) (x : BitString n)
    (hfalse : P.fP x = false) :
    ∃ w' : Fin P.dim → ℂ,
      Inner P.target w' ≠ 0 ∧
        ∀ i : Fin P.idx, P.Available x i → P.dualCoord w' i = 0 := by
  classical
  let S : Submodule ℂ (EuclideanSpace ℂ (Fin P.dim)) := Submodule.span ℂ
    {v | ∃ i : Fin P.idx, P.Available x i ∧ v = WithLp.toLp 2 (P.vec i)}
  let t : EuclideanSpace ℂ (Fin P.dim) := WithLp.toLp 2 P.target
  have ht : t ∉ S := by
    intro ht
    let v : Fin P.idx → EuclideanSpace ℂ (Fin P.dim) :=
      fun i => P.piCoeff x i • WithLp.toLp 2 (P.vec i)
    have hS : S ≤ Submodule.span ℂ (Set.range v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      have hv : v i ∈ Submodule.span ℂ (Set.range v) :=
        Submodule.subset_span (Set.mem_range_self i)
      simpa [v, SpanProgram.piCoeff, hi] using hv
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hS ht)
    have hc : P.combo x w = P.target := by
      funext r
      have h := congrArg (fun z : EuclideanSpace ℂ (Fin P.dim) => z r) hw
      simpa [v, t, SpanProgram.combo, Finset.sum_apply, mul_comm, mul_left_comm,
        mul_assoc] using h
    have htrue := (lemma_2_2_range_characterization P x).mpr ⟨w, hc⟩
    simp [hfalse] at htrue
  let u := t - S.starProjection t
  have hu : u ≠ 0 := by
    intro hu
    have he : t = S.starProjection t := sub_eq_zero.mp hu
    exact ht (he ▸ S.starProjection_apply_mem t)
  have huo : u ∈ Sᗮ := S.sub_starProjection_mem_orthogonal t
  have hinner (v w : EuclideanSpace ℂ (Fin P.dim)) :
      inner ℂ v w = Inner v.ofLp w.ofLp := by
    simp [PiLp.inner_apply, inner_apply, RCLike.inner_apply, mul_comm]
  refine ⟨u.ofLp, ?_, ?_⟩
  · rw [← hinner t u]
    have huu : inner ℂ u u = inner ℂ t u := by
      dsimp only [u]
      rw [inner_sub_left, S.inner_right_of_mem_orthogonal
        (S.starProjection_apply_mem t) huo, sub_zero]
    rw [← huu]
    exact inner_self_ne_zero.mpr hu
  · intro i hi
    rw [SpanProgram.dualCoord, ← hinner (WithLp.toLp 2 (P.vec i)) u]
    exact S.inner_right_of_mem_orthogonal (Submodule.subset_span ⟨i, hi, rfl⟩) huo

/-- **Lemma 2.2, converse of the dual-witness form**: if a vector `|w'⟩` has
`⟨t|w'⟩ ≠ 0` and is orthogonal to all available input vectors, then `f_P(x) = 0`. -/
theorem lemma_2_2_dual_witness_converse (P : SpanProgram n) (x : BitString n)
    (w' : Fin P.dim → ℂ) (ht : Inner P.target w' ≠ 0)
    (hav : ∀ i : Fin P.idx, P.Available x i → P.dualCoord w' i = 0) :
    P.fP x = false := by
  classical
  cases hf : P.fP x with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨w, hw⟩ := (lemma_2_2_range_characterization P x).mp hf
    have hc : star (Inner (P.combo x w) w') =
        ∑ i, P.piCoeff x i * w i * star (P.dualCoord w' i) := by
      simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply,
        SpanProgram.combo, SpanProgram.dualCoord, star_sum, star_mul', star_star,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      ring
    have hz : star (Inner P.target w') = 0 := by
      rw [← hw, hc]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : P.Available x i
      · simp [hav i hi]
      · simp [SpanProgram.piCoeff, hi]
    exact ht (star_eq_zero.mp hz)

end Qatlib.Papers.SpanProgReich09.MainResults.Section2
