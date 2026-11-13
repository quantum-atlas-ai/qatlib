/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel

set_option backward.isDefEq.respectTransparency false

/-!
# Span Programs from One-Sided-Error Quantum Query Algorithms

This module formalizes Section 3, Theorem 3.1 (p. 14) of Reichardt, establishing
that for every `n`, any Boolean function `f : {0, 1}^n → {0, 1}` admits a span
program computing `f` whose uniform witness size is bounded within a constant
factor of the one-sided bounded-error quantum query complexity of `f`.

## Main statements

* `theorem_3_1_algorithm_to_span_program`: Theorem 3.1, existence of a span
  program computing `f` with `wsize(P) = O(Q_1(f))`.

## References

* [Reichardt, 2009][Reichardt2009SpanPrograms], Section 3, Theorem 3.1, p. 14.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.SpanProgReich09.MainResults.Section3
open Qatlib.Papers.SpanProgReich09.MainResults
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GramQueryCore.LowerBoundTools Matrix

private theorem canonical_span_program (n : ℕ) (f : BitString n → Bool) :
    ∃ P : SpanProgram n, P.Computes f ∧
      P.wsizeUniform ≤ ENNReal.ofReal (max (n : ℝ) ((2 : ℝ) ^ n)) := by
  classical
  let F := {z : BitString n // f z = false}
  let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
  let d : F × Fin n ≃ Fin (Fintype.card F * n) :=
    (e.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv
  let P : SpanProgram n :=
    { dim := Fintype.card F
      idx := Fintype.card F * n
      target := fun _ => 1
      vec := fun i r => if (d.symm i).1 = e.symm r then 1 else 0
      label := fun i => some ((d.symm i).2, !((d.symm i).1.val (d.symm i).2)) }
  have hav (x : BitString n) (z : F) (j : Fin n) :
      P.Available x (d (z, j)) ↔ x j = !(z.val j) := by
    simp [P, SpanProgram.Available, SpanProgram.IsFree, Bool.eq_not_iff, ne_comm]
  have hcombo (x : BitString n) (w : Fin P.idx → ℂ) (z : F) :
      P.combo x w (e z) = ∑ j : Fin n, if x j = !(z.val j) then w (d (z, j)) else 0 := by
    unfold SpanProgram.combo
    rw [← d.sum_comp]
    simp [P, SpanProgram.piCoeff, SpanProgram.Available, SpanProgram.IsFree,
      Fintype.sum_prod_type, mul_ite, ite_mul, Bool.eq_not_iff, ne_comm]
    exact Fintype.sum_ite_eq' _ _
  have hcost (w : Fin P.idx → ℂ) :
      (∑ i, P.costScale (SpanProgram.uniformCost n) i * ‖w i‖ ^ 2) =
        ∑ z : F, ∑ j : Fin n, ‖w (d (z, j))‖ ^ 2 := by
    rw [← d.sum_comp]
    simp [P, SpanProgram.costScale, SpanProgram.uniformCost, Fintype.sum_prod_type]
  have hdual (z : F) (i : Fin P.idx) :
      P.dualCoord (fun r => if r = e z then 1 else 0) i =
        if (d.symm i).1 = z then 1 else 0 := by
    simp [SpanProgram.dualCoord, Qatlib.Foundations.PureStateMath.Inner, dotProduct, P]
  have hbound (x : BitString n) : P.fP x = f x ∧
      P.witnessSize (SpanProgram.uniformCost n) x ≤
        ENNReal.ofReal (max (n : ℝ) ((2 : ℝ) ^ n)) := by
    cases hx : f x with
    | false =>
      let z : F := ⟨x, hx⟩
      have hnospan : ¬ ∃ w, P.combo x w = P.target := by
        rintro ⟨w, hw⟩
        have he := congrFun hw (e z)
        simp [hcombo, z, P] at he
      have hfp : P.fP x = false := by simp [SpanProgram.fP, hnospan]
      refine ⟨hfp, ?_⟩
      simp only [SpanProgram.witnessSize, hfp, Bool.false_eq_true, ↓reduceIte]
      apply (sInf_le ?_).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      refine ⟨fun r => if r = e z then 1 else 0, ?_, ?_, ?_⟩
      · simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct, P]
      · intro i hi
        rw [hdual]
        have hi' := (hav x (d.symm i).1 (d.symm i).2).mp (by simpa using hi)
        have hz : (d.symm i).1 ≠ z := by
          intro he
          simp [he, z] at hi'
        simp [hz]
      · rw [hcost]
        simp only [hdual]
        simp [apply_ite]
        rw [Fintype.sum_ite_eq']
        simp
    | true =>
      have hdiff (z : F) : ∃ j : Fin n, x j ≠ z.val j := by
        apply Function.ne_iff.mp
        intro he
        have := z.property
        rw [← he, hx] at this
        contradiction
      let j : F → Fin n := fun z => Classical.choose (hdiff z)
      have hj (z : F) : x (j z) = !(z.val (j z)) := by
        have hne : x (j z) ≠ z.val (j z) := Classical.choose_spec (hdiff z)
        cases h : x (j z) <;> cases h' : z.val (j z) <;> simp_all
      let w : Fin P.idx → ℂ := fun i => if (d.symm i).2 = j (d.symm i).1 then 1 else 0
      have hw : P.combo x w = P.target := by
        ext r
        obtain ⟨z, rfl⟩ := e.surjective r
        rw [hcombo, Finset.sum_eq_single (j z)]
        · simp [w, P, hj]
        · intro k _ hk
          simp [w, hk]
        · simp
      have hfp : P.fP x = true := by simp [SpanProgram.fP, show ∃ w, P.combo x w = P.target from ⟨w, hw⟩]
      refine ⟨hfp, ?_⟩
      simp only [SpanProgram.witnessSize, hfp, ↓reduceIte]
      have hc : ENNReal.ofReal (Fintype.card F : ℝ) ∈
          P.trueCostSet (SpanProgram.uniformCost n) x := by
        refine ⟨w, hw, ?_⟩
        rw [hcost]
        simp [w, apply_ite]
      apply (sInf_le hc).trans
      apply ENNReal.ofReal_le_ofReal
      apply le_trans _ (le_max_right _ _)
      exact_mod_cast (show Fintype.card F ≤ 2 ^ n by
        simpa [F, BitString, Fintype.card_fun] using Fintype.card_subtype_le (fun z => f z = false))
  refine ⟨P, fun x => (hbound x).1, ?_⟩
  exact iSup_le fun x => (hbound x.val).2

private theorem one_le_query_of_nonconstant (n : ℕ) (f : BitString n → Bool)
    (x₀ x₁ : BitString n) (hx₀ : f x₀ = false) (hx₁ : f x₁ = true) :
    1 ≤ queryComplexityOneSided (BitString n) f := by
  classical
  apply le_sInf
  rintro b ⟨r, hr, W, rfl, hlegal, hfalse, htrue⟩
  by_cases hzero : sourceWordCalls W = 0
  · exfalso
    have hletters := List.countP_eq_zero.mp hzero
    have hmatrix (O : Matrix (SourceSpace 1 (Fintype.card (BitString n)) (Option Bool) r)
        (SourceSpace 1 (Fintype.card (BitString n)) (Option Bool) r) ℂ) :
        sourceWordMatrix O W = sourceWordMatrix 1 W := by
      unfold sourceWordMatrix
      congr 2
      apply List.map_congr_left
      intro s hs
      cases s with
      | inl U => rfl
      | inr adj => simpa using hletters (.inr adj) hs
    have hunitary : sourceWordMatrix 1 W ∈ Matrix.unitaryGroup _ ℂ := by
      apply Submonoid.list_prod_mem
      intro U hU
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hU)
      cases s with
      | inl U => exact hlegal (.inl U) hs
      | inr adj => cases adj <;> simp
    have hnorm : Normalized
        (sourceClean 1 (Fintype.card (BitString n)) r hr false (Ket (none : Option Bool))) :=
      normalized_tensorState (normalized_ket _) (normalized_tensorState
        (normalized_tensorState (normalized_ket _) (normalized_ket _)) (normalized_ket _))
    have hout := normalized_applyGate hunitary hnorm
    have hf := hfalse x₀ hx₀
    have ht := htrue x₁ hx₁
    rw [hmatrix] at hf ht
    let ψ := sourceWordMatrix 1 W *ᵥ
      sourceClean 1 (Fintype.card (BitString n)) r hr false (Ket (none : Option Bool))
    let S₀ := Finset.univ.filter
      (fun p : SourceSpace 1 (Fintype.card (BitString n)) (Option Bool) r => p.2.1.2 = some false)
    let S₁ := Finset.univ.filter
      (fun p : SourceSpace 1 (Fintype.card (BitString n)) (Option Bool) r => p.2.1.2 = some true)
    have hdisj : Disjoint S₀ S₁ := by
      apply Finset.disjoint_left.mpr
      intro p hp₀ hp₁
      have h₀ := (Finset.mem_filter.mp hp₀).2
      have h₁ := (Finset.mem_filter.mp hp₁).2
      simp_all
    have hle : MeasureProb ψ S₀ + MeasureProb ψ S₁ ≤ 1 := by
      rw [MeasureProb, MeasureProb, ← Finset.sum_union hdisj]
      calc
        _ ≤ ∑ p, BornProb ψ p := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun p _ _ => bornProb_nonneg ψ p)
        _ = 1 := hout
    change MeasureProb ψ S₀ = 1 at hf
    change MeasureProb ψ S₁ ≥ 2 / 3 at ht
    linarith
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero


/-- **Theorem 3.1** (paper p. 14): Let a quantum query algorithm evaluate
`f : {0,1}^n → {0,1}` with bounded one-sided error on false inputs using `q`
queries.  Then there is a span program `P` computing `f` with
`wsize(P) = O(q)`.  `queryComplexityOneSided` is the one-sided query complexity
in the frozen source-word model (false inputs are rejected with probability one,
true inputs accepted with probability at least `2/3`). -/
theorem theorem_3_1_algorithm_to_span_program (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : BitString n → Bool,
      ∃ P : SpanProgram n,
        P.Computes f ∧
          P.wsizeUniform ≤ ENNReal.ofReal C * queryComplexityOneSided (BitString n) f := by
  classical
  let C : ℝ := max 1 (max (n : ℝ) ((2 : ℝ) ^ n))
  refine ⟨C, by dsimp [C]; positivity, fun f => ?_⟩
  by_cases ht : ∀ x, f x = true
  · let P : SpanProgram n :=
      { dim := 0, idx := 0, target := Fin.elim0, vec := Fin.elim0, label := Fin.elim0 }
    have hfp (x : BitString n) : P.fP x = true := by
      simp [SpanProgram.fP, SpanProgram.combo, P, funext_iff]
    refine ⟨P, fun x => (hfp x).trans (ht x).symm, ?_⟩
    apply le_trans (show P.wsizeUniform ≤ 0 from ?_) bot_le
    apply iSup_le
    intro x
    simp only [SpanProgram.witnessSize, hfp, ↓reduceIte]
    apply sInf_le
    exact ⟨0, by ext r; exact Fin.elim0 r, by simp [P]⟩
  by_cases hf : ∀ x, f x = false
  · let P : SpanProgram n :=
      { dim := 1, idx := 0, target := fun _ => 1, vec := Fin.elim0, label := Fin.elim0 }
    have hfp (x : BitString n) : P.fP x = false := by
      simp [SpanProgram.fP, SpanProgram.combo, P, funext_iff]
    refine ⟨P, fun x => (hfp x).trans (hf x).symm, ?_⟩
    apply le_trans (show P.wsizeUniform ≤ 0 from ?_) bot_le
    apply iSup_le
    intro x
    simp only [SpanProgram.witnessSize, hfp, Bool.false_eq_true, ↓reduceIte]
    apply sInf_le
    refine ⟨fun _ => 1, ?_, fun i => Fin.elim0 i, ?_⟩
    · simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct, P]
    · simp [P]
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x = false := by simpa using ht
  obtain ⟨x₁, hx₁⟩ : ∃ x, f x = true := by simpa using hf
  obtain ⟨P, hP, hsize⟩ := canonical_span_program n f
  refine ⟨P, hP, hsize.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (le_max_right _ _)
    _ ≤ ENNReal.ofReal C * queryComplexityOneSided (BitString n) f :=
      le_mul_of_one_le_right bot_le (one_le_query_of_nonconstant n f x₀ x₁ hx₀ hx₁)

end Qatlib.Papers.SpanProgReich09.MainResults.Section3
