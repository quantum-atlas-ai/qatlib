/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel
public import Qatlib.Foundations.PureStateMath.DualSep.FiniteDual

@[expose] public section


/-! # The dual-witness characterization in Lemma 2.2

Source: arXiv:0904.2759v1, page 8, Lemma 2.2 and its following paragraph.
These results use the pinned finite span-program model and prove the actual
nonzero dual witness in both directions. They do not establish the separate
printed projection-range formula or the bit-query algorithm.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SpanProgReich09.MainResults
open Qatlib.Foundations.PureStateMath.DualSep

namespace Qatlib.Papers.SpanProgReich09.MainResults

variable {n : ℕ}

/-- The source available-vector combination is a genuine complex linear map. -/
def comboMap (P : SpanProgram n) (x : BitString n) :
    (Fin P.idx → ℂ) →ₗ[ℂ] (Fin P.dim → ℂ) where
  toFun := P.combo x
  map_add' u v := by
    ext r
    simp [SpanProgram.combo, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    ext r
    simp only [SpanProgram.combo, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- An available source input vector is in the range of its actual combination map. -/
theorem vecInRange (P : SpanProgram n) (x : BitString n) (i : Fin P.idx)
    (hi : P.Available x i) : P.vec i ∈ (comboMap P x).range := by
  refine ⟨Pi.single i 1, ?_⟩
  ext r
  simp [comboMap, SpanProgram.combo, SpanProgram.piCoeff, hi, Pi.single_apply]

/-- Orthogonality to all available vectors annihilates every available combination. -/
theorem comboPairZero (P : SpanProgram n) (x : BitString n)
    (w' : Fin P.dim → ℂ)
    (hav : ∀ i, P.Available x i → P.dualCoord w' i = 0)
    (w : Fin P.idx → ℂ) : Inner (P.combo x w) w' = 0 := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply,
    SpanProgram.combo, star_sum,
    star_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have hp : (∑ r, star (P.vec i r) * (star (w i) * star (P.piCoeff x i)) * w' r)
      = star (P.piCoeff x i) * star (w i) * P.dualCoord w' i := by
    simp only [SpanProgram.dualCoord, Qatlib.Foundations.PureStateMath.Inner,
      dotProduct, Pi.star_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hp]
  by_cases hi : P.Available x i
  · rw [hav i hi, mul_zero]
  · simp [SpanProgram.piCoeff, hi]

/-- A rejected input has a nonzero dual witness, as stated after Lemma 2.2. -/
theorem dualWitness (P : SpanProgram n) (x : BitString n)
    (hfalse : P.fP x = false) :
    ∃ w' : Fin P.dim → ℂ, Inner P.target w' ≠ 0 ∧
      ∀ i, P.Available x i → P.dualCoord w' i = 0 := by
  have ht : P.target ∉ (comboMap P x).range := by
    rintro ⟨w, hw⟩
    have hex : ∃ w, P.combo x w = P.target := ⟨w, hw⟩
    simp [SpanProgram.fP, hex] at hfalse
  obtain ⟨w', ht', hw'⟩ := orthogSep (comboMap P x).range P.target ht
  refine ⟨w', ht', ?_⟩
  intro i hi
  exact hw' (P.vec i) (vecInRange P x i hi)

/-- A nonzero pairing orthogonal to all available vectors excludes acceptance. -/
theorem dualConverse (P : SpanProgram n) (x : BitString n)
    (w' : Fin P.dim → ℂ) (ht : Inner P.target w' ≠ 0)
    (hav : ∀ i, P.Available x i → P.dualCoord w' i = 0) :
    P.fP x = false := by
  have hn : ¬ ∃ w, P.combo x w = P.target := by
    rintro ⟨w, hw⟩
    have hz := comboPairZero P x w' hav w
    rw [hw] at hz
    exact ht hz
  simp [SpanProgram.fP, hn]

/-- The source rejection predicate is equivalent to existence of a genuine dual witness. -/
theorem dualIff (P : SpanProgram n) (x : BitString n) :
    P.fP x = false ↔ ∃ w' : Fin P.dim → ℂ, Inner P.target w' ≠ 0 ∧
      ∀ i, P.Available x i → P.dualCoord w' i = 0 := by
  constructor
  · exact dualWitness P x
  · rintro ⟨w', ht, hav⟩
    exact dualConverse P x w' ht hav

end Qatlib.Papers.SpanProgReich09.MainResults
