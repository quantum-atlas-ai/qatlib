/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.FullLayerCF.FullLayerCFDenoiseUniquePStat
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundaryAmpl

/-!
# Candidate recovery without a uniqueness guarantee

`fullLayerCFDenoiseUniqueP_answer` proves successful-window mass, continued-fraction recovery,
repeated candidate-record success, and verification and query bounds. The module also refutes
`FullLayerCFDenoiseUniquePOriginal` and exhibits two planted periods for the same oracle,
distinguishing the candidate guarantee from an unsupported uniqueness claim in the setting of
[Cornwell2014].

## Main statements

* `aqCandidateRecord_actual_hit`: Under the noisy-progression assumptions, R samples record the
  planted period with probability at least 1−(1−`aqErrorSuccessLower N M L P`)ᴿ and use at most
  R(k+3) queries.
* `same_oracle_two_planted_periods`: The marked set in `Fin 128` formed from the length-four
  progression of step 2 and noise {8,12} also arises from step 4 and noise {2,6}; both
  candidates pass verification.
* `fullLayerCFDenoiseUniqueP_answer`: Proves the corrected candidate-record contract: positive
  window mass, continued-fraction recovery, repeated inclusion of the planted period,
  verification of all recorded candidates, and the stated query cap; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.LegendreWindow
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.FullLayerCF

/-- The original proposed recovery contract, requiring a repeated first-output success bound, a
wrong-period triple-correlation bound, and a query cap under the stated noisy-progression
assumptions. -/
def FullLayerCFDenoiseUniquePOriginal : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (s M L P B R v : ℕ) (G : Finset (Fin N)) (h : Fin N → Bool),
    2 ≤ M → 2 ≤ P → s + (M - 1) * P < N → M * P ≤ N → P ≤ B → 2 * B ^ 2 < N →
    G.card = L → Disjoint G (aqProgressionSet N s M P) →
    2 * (M + L) ≤ N → (L : ℝ) < 2 * (M : ℝ) / Real.pi → 0 < R → 0 < v →
    (∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) →
    let C := aqProgressionSet N s M P ∪ G
    let T := M + L
    let w : Fin N → ℝ := fun y => BornProb (aqState N hN T C) y
    let q := aqErrorSuccessLower N M L P
    let k := aqRounds N T
    (0 < q ∧ q ≤ 1) ∧
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin R → Fin N =>
        (aqRetry h s M B k (List.ofFn ω)).1 = some P), ∏ r, w (ω r)) ≥
      1 - (1 - q) ^ R ∧
    (∀ q' : ℕ, q' ≠ P → q' ≤ B →
      ((Finset.univ.filter (fun x : Fin N =>
          (h x) && (h ⟨(x.val + q') % N, Nat.mod_lt _ hN⟩) &&
          (h ⟨(x.val + 2 * q') % N, Nat.mod_lt _ hN⟩))).card : ℝ) ≤
        (C.card : ℝ) / 2) ∧
    (∀ ω : Fin R → Fin N, (aqRetry h s M B k (List.ofFn ω)).2 ≤ R * (k + 3 * v))

/-- The original contract `FullLayerCFDenoiseUniquePOriginal` is false. -/
theorem fullLayerCFDenoiseUniqueP_false : ¬ FullLayerCFDenoiseUniquePOriginal := by
  intro h
  let A := aqProgressionSet 16 0 2 2
  let mark : Fin 16 → Bool := fun x => decide (x ∈ A)
  have hl : (0 : ℝ) < 2 * (2 : ℝ) / Real.pi := by positivity
  have hh := h 16 (by decide) 0 2 0 2 2 1 1 ∅ mark
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp) (by decide) (by exact_mod_cast hl) (by decide) (by decide)
    (by intro x; simp [mark, A])
  have hb := hh.2.2.1 0 (by decide) (by decide)
  have hfilter : (Finset.univ.filter (fun x : Fin 16 =>
      (mark x) && (mark ⟨(x.val + 0) % 16, Nat.mod_lt _ (by decide)⟩) &&
      (mark ⟨(x.val + 2 * 0) % 16, Nat.mod_lt _ (by decide)⟩))) = A := by
    ext x
    have hx : (⟨x.val % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16) = x := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt x.isLt
    simp [hx, mark]
  have hcard : A.card = 2 := aqProgression_card 16 0 2 2 (by decide) (by decide) (by decide)
  change ((Finset.univ.filter _).card : ℝ) ≤ ((A ∪ ∅).card : ℝ) / 2 at hb
  rw [hfilter, Finset.union_empty, hcard] at hb
  norm_num at hb

/-- A repetition procedure that records only hits of z succeeds exactly when some element of the
input list maps to `some z`. -/
private theorem repeat_hit_iff {I Z : Type} [DecidableEq Z]
    (a : I → Option Z) (z : Z) (xs : List I) :
    (aqRepeat (fun x => (if a x = some z then some () else none, 0)) 0 xs).1 =
      some () ↔ ∃ x ∈ xs, a x = some z := by
  induction xs with
  | nil => simp [aqRepeat]
  | cons x xs ih =>
    by_cases hx : a x = some z
    · simp [aqRepeat, hx]
    · simp [aqRepeat, hx, ih]

/-- For normalized nonnegative sampling weights with single-sample hit mass at least q > 0, the
probability of at least one hit in R product samples is at least 1−(1−q)ᴿ. -/
theorem fresh_candidate_hit_lower {I Z : Type} [Fintype I] [DecidableEq I]
    [DecidableEq Z] (w : I → ℝ) (a : I → Option Z) (z : Z) (q : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∑ x, w x = 1) (hq : 0 < q)
    (hp : q ≤ ∑ x, if a x = some z then w x else 0) (R : ℕ) :
    1 - (1 - q) ^ R ≤
      ∑ ω : Fin R → I, if (∃ r, a (ω r) = some z) then aqProductMass w ω else 0 := by
  let b : I → Option Unit × ℕ := fun x =>
    (if a x = some z then some () else none, 0)
  have hs (x : I) : (b x).1 = none ∨ (b x).1 = some () := by
    dsimp [b]
    split <;> simp
  have hc (x : I) : 0 + (b x).2 ≤ 0 := by simp [b]
  have hp' : q ≤ ∑ x, if (b x).1 = some () then w x else 0 := by
    simpa [b] using! hp
  have hr := (aqRepeat_fresh_bounds w b () 0 0 q hw0 hw hq hs hc hp' R).1
  rw [Finset.sum_filter] at hr
  refine hr.trans_eq ?_
  apply Finset.sum_congr rfl
  intro ω _
  have he : (aqRepeat b 0 (List.ofFn ω)).1 = some () ↔ ∃ r, a (ω r) = some z := by
    rw [repeat_hit_iff]
    constructor
    · rintro ⟨x, hx, ha⟩
      obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨r, ha⟩
    · rintro ⟨r, ha⟩
      exact ⟨ω r, List.mem_ofFn.mpr ⟨r, rfl⟩, ha⟩
  simp only [he]

/-- A period belongs to `aqCandidateRecord` exactly when some input sample makes `aqAttempt`
return that period. -/
theorem aqCandidateRecord_mem {N : ℕ} (h : Fin N → Bool) (s M B P : ℕ)
    (xs : List (Fin N)) :
    P ∈ aqCandidateRecord h s M B xs ↔ ∃ y ∈ xs, (aqAttempt h s M B y).1 = some P := by
  exact List.mem_filterMap

/-- Every period in `aqCandidateRecord` passes `aqVerify`. -/
theorem aqCandidateRecord_verified {N : ℕ} (h : Fin N → Bool) (s M B : ℕ)
    (xs : List (Fin N)) (p : ℕ) (hp : p ∈ aqCandidateRecord h s M B xs) :
    (aqVerify h s M p).1 = true := by
  obtain ⟨y, _hy, hy⟩ := (aqCandidateRecord_mem h s M B p xs).mp hp
  unfold aqAttempt at hy
  (try dsimp only at hy)
  split at hy
  · simp at hy
  · (try dsimp only at hy)
    split at hy
    · rename_i hv
      rw [Option.some.inj hy] at hv
      exact hv
    · simp at hy

/-- The query cost of recording candidates from a list is at most its length times k+3. -/
theorem aqCandidateRecordQueries_cap {N : ℕ} (h : Fin N → Bool) (s M B k : ℕ)
    (xs : List (Fin N)) : aqCandidateRecordQueries h s M B k xs ≤ xs.length * (k + 3) := by
  have hc (y : Fin N) : (aqAttempt h s M B y).2.1 ≤ 3 := by
    unfold aqAttempt
    (try dsimp only)
    split
    · simp
    · exact aqVerify_cost _ _ _ _
  induction xs with
  | nil => simp [aqCandidateRecordQueries]
  | cons y ys ih =>
    simp only [aqCandidateRecordQueries, List.map_cons, List.sum_cons, List.length_cons]
    have hy := hc y
    unfold aqCandidateRecordQueries at ih
    nlinarith

/-- Under the noisy-progression assumptions, R samples record the planted period with
probability at least 1−(1−`aqErrorSuccessLower N M L P`)ᴿ and use at most R(k+3) queries. -/
theorem aqCandidateRecord_actual_hit (N : ℕ) (hN : 0 < N) (s M L P B R : ℕ)
    (G : Finset (Fin N)) (h : Fin N → Bool)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N) (hMP : M * P ≤ N)
    (hPB : P ≤ B) (hsepB : 2 * B ^ 2 < N) (hG : G.card = L)
    (hdis : Disjoint G (aqProgressionSet N s M P)) (hhalf : 2 * (M + L) ≤ N)
    (hsep : (L : ℝ) < 2 * (M : ℝ) / Real.pi)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) :
    let C := aqProgressionSet N s M P ∪ G
    let w : Fin N → ℝ := fun y => BornProb (aqState N hN (M + L) C) y
    (∑ ω : Fin R → Fin N, if P ∈ aqCandidateRecord h s M B (List.ofFn ω)
      then aqProductMass w ω else 0) ≥ 1 - (1 - aqErrorSuccessLower N M L P) ^ R ∧
    (∀ ω : Fin R → Fin N,
      aqCandidateRecordQueries h s M B (aqRounds N (M + L)) (List.ofFn ω) ≤
        R * (aqRounds N (M + L) + 3)) := by
  (try dsimp only)
  let w : Fin N → ℝ := fun y => BornProb
    (aqState N hN (M + L) (aqProgressionSet N s M P ∪ G)) y
  let a : Fin N → Option ℕ := fun y => (aqAttempt h s M B y).1
  have hw0 : ∀ y, 0 ≤ w y := fun y => bornProb_nonneg _ y
  have hw : (∑ y, w y) = 1 := (aq_error_word_counts N hN (M + L)
    (aqProgressionSet N s M P ∪ G)).2.2.2.2
  have hq := (aq_error_window_mass_lower N hN s M L P G h hM hP hb hMP
    hG hdis hhalf hsep hmark).1
  have ha : ∀ y, y ∈ aqGoodWindow N P → a y = some P := by
    intro y hy
    exact (aq_error_attempt_sound_and_counts N s M P B G h y hM hP hb hPB hsepB hmark).1 hy
  have hp := aq_error_attempt_mass_lower N hN s M L P B G h P a ha
    hM hP hb hMP hPB hsepB hG hdis hhalf hsep hmark
  have hh := fresh_candidate_hit_lower w a P (aqErrorSuccessLower N M L P) hw0 hw hq hp R
  refine ⟨?_, ?_⟩
  · refine hh.trans_eq ?_
    apply Finset.sum_congr rfl
    intro ω _
    have he : P ∈ aqCandidateRecord h s M B (List.ofFn ω) ↔ ∃ r, a (ω r) = some P := by
      rw [aqCandidateRecord_mem]
      constructor
      · rintro ⟨y, hy, ha⟩
        obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
        exact ⟨r, ha⟩
      · rintro ⟨r, ha⟩
        exact ⟨ω r, List.mem_ofFn.mpr ⟨r, rfl⟩, ha⟩
    simp only [he, w]
  · intro ω
    simpa using! aqCandidateRecordQueries_cap h s M B (aqRounds N (M + L)) (List.ofFn ω)

/-- The original unique-period contract fails even using a counterexample with a positive
candidate displacement. -/
theorem fullLayerCFDenoiseUniqueP_positive_displacement_false :
    ¬ FullLayerCFDenoiseUniquePOriginal := by
  intro h
  let G : Finset (Fin 128) := {1, 3, 5, 7}
  let C := aqProgressionSet 128 0 8 2 ∪ G
  let mark : Fin 128 → Bool := fun x => decide (x ∈ C)
  have hl : (4 : ℝ) < 2 * (8 : ℝ) / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_lt_four]
  have hh := h 128 (by decide) 0 8 4 2 2 1 1 G mark
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hl (by decide) (by decide)
    (by intro x; rfl)
  have hb := hh.2.2.1 1 (by decide) (by decide)
  have hcard : C.card = 12 := by decide
  have htriples : (Finset.univ.filter (fun x : Fin 128 =>
      (mark x) && (mark ⟨(x.val + 1) % 128, Nat.mod_lt _ (by decide)⟩) &&
      (mark ⟨(x.val + 2 * 1) % 128, Nat.mod_lt _ (by decide)⟩))).card = 7 := by
    decide
  change ((Finset.univ.filter _).card : ℝ) ≤ (C.card : ℝ) / 2 at hb
  rw [hcard, htriples] at hb
  norm_num at hb

/-- The marked set in `Fin 128` formed from the length-four progression of step 2 and noise
{8,12} also arises from step 4 and noise {2,6}; both candidates pass verification. -/
theorem same_oracle_two_planted_periods :
    let G2 : Finset (Fin 128) := {8, 12}
    let G4 : Finset (Fin 128) := {2, 6}
    let C2 := aqProgressionSet 128 0 4 2 ∪ G2
    let C4 := aqProgressionSet 128 0 4 4 ∪ G4
    let h : Fin 128 → Bool := fun x => decide (x ∈ C2)
    G2.card = 2 ∧ G4.card = 2 ∧
    Disjoint G2 (aqProgressionSet 128 0 4 2) ∧
    Disjoint G4 (aqProgressionSet 128 0 4 4) ∧
    C2 = C4 ∧ (2 : ℝ) < 2 * (4 : ℝ) / Real.pi ∧
    (aqVerify h 0 4 2).1 = true ∧ (aqVerify h 0 4 4).1 = true := by
  (try dsimp only)
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, by decide⟩
  apply (lt_div_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_lt_four]

/-- A sample in `aqSourceSuccessfulWindow N P`, with P ≥ 2, yields a reduced fraction a/P among
the continued-fraction convergents, with denominator P. -/
theorem aqSourceSuccessfulWindow_cf (N P : ℕ) (hP : 2 ≤ P)
    (y : Fin N) (hy : y ∈ aqSourceSuccessfulWindow N P) :
    ∃ a n : ℕ, a < P ∧ Nat.Coprime a P ∧
      (a : ℚ) / P = ((y.val : ℝ) / N).convergent n ∧
      (((y.val : ℝ) / N).convergent n).den = P := by
  obtain ⟨a, ha, hcop, hw⟩ := (Finset.mem_filter.mp hy).2
  let q : ℚ := (a : ℚ) / P
  have hden : q.den = P := by
    have hd := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (P : ℤ))
      (by exact_mod_cast (show 0 < P by omega)) (by simpa using! hcop)
    have hd' : (((a : ℚ) / P).den : ℤ) = (P : ℤ) := by
      simpa only [Int.cast_natCast, Int.natAbs_natCast] using! hd
    exact Int.natCast_inj.mp hd'
  have hwR0 : |(y.val : ℝ) / N - (a : ℝ) / P| ≤ 1 / (2 * (P : ℝ) ^ 2) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hw
    push_cast at hh
    exact hh
  have hwR : |(y.val : ℝ) / N - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hden]
    simpa only [q, Rat.cast_div, Rat.cast_natCast] using! hwR0
  obtain ⟨n, hn⟩ := legendre_nonstrict_den_ge_two _ q (by rw [hden]; exact hP) hwR
  exact ⟨a, n, ha, hcop, hn, hn ▸ hden⟩

/-- When P > 0 and P² ≤ N, `aqGoodWindow N P` is contained in `aqSourceSuccessfulWindow N P`. -/
theorem aqGoodWindow_subset_source (N P : ℕ) (_hN : 0 < N) (hP : 0 < P)
    (hsize : P ^ 2 ≤ N) : aqGoodWindow N P ⊆ aqSourceSuccessfulWindow N P := by
  intro y hy
  obtain ⟨a, ha, hcop, hw⟩ := (Finset.mem_filter.mp hy).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, hcop, hw.trans ?_⟩
  apply one_div_le_one_div_of_le (by positivity)
  have hh : (P : ℚ) ^ 2 ≤ N := by exact_mod_cast hsize
  linarith

/-- Under the noisy-progression and size assumptions, `aqSourceSuccessfulWindow N P` has mass at
least the strictly positive `aqErrorSuccessLower N M L P`. -/
theorem aqSourceSuccessfulWindow_actual_mass (N : ℕ) (hN : 0 < N) (s M L P : ℕ)
    (G : Finset (Fin N)) (h : Fin N → Bool)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N) (hMP : M * P ≤ N)
    (hsize : P ^ 2 ≤ N) (hG : G.card = L)
    (hdis : Disjoint G (aqProgressionSet N s M P)) (hhalf : 2 * (M + L) ≤ N)
    (hsep : (L : ℝ) < 2 * (M : ℝ) / Real.pi)
    (hmark : ∀ x, h x = decide (x ∈ aqProgressionSet N s M P ∪ G)) :
    0 < aqErrorSuccessLower N M L P ∧
    aqErrorSuccessLower N M L P ≤
      MeasureProb (aqState N hN (M + L) (aqProgressionSet N s M P ∪ G))
        (aqSourceSuccessfulWindow N P) := by
  have hh := aq_error_window_mass_lower N hN s M L P G h hM hP hb hMP hG hdis
    hhalf hsep hmark
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (aqGoodWindow_subset_source N P hN (by omega) hsize)
    (fun y _ _ => bornProb_nonneg _ y)

/-- Proves the corrected candidate-record contract: positive window mass, continued-fraction
recovery, repeated inclusion of the planted period, verification of all recorded candidates,
and the stated query cap; see [Cornwell2014]. -/
theorem fullLayerCFDenoiseUniqueP_answer : FullLayerCFDenoiseUniqueP := by
  intro N hN s M L P B R v G h hM hP hb hMP hPB hsepB hG hdis hhalf hsep _hR hv hmark
  (try dsimp only)
  have hsize : P ^ 2 ≤ N := by nlinarith
  have hwin := aq_error_window_mass_lower N hN s M L P G h hM hP hb hMP
    hG hdis hhalf hsep hmark
  have hmass := aqSourceSuccessfulWindow_actual_mass N hN s M L P G h hM hP hb hMP
    hsize hG hdis hhalf hsep hmark
  have hrecord := aqCandidateRecord_actual_hit N hN s M L P B R G h hM hP hb hMP
    hPB hsepB hG hdis hhalf hsep hmark
  have hnorm := (aq_error_word_counts N hN (M + L)
    (aqProgressionSet N s M P ∪ G)).2.2.2.2
  have hcap : MeasureProb
      (aqState N hN (M + L) (aqProgressionSet N s M P ∪ G)) (aqGoodWindow N P) ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => bornProb_nonneg _ y)
  refine ⟨⟨hwin.1, hwin.2.trans hcap⟩, hmass.2,
    (fun y hy => aqSourceSuccessfulWindow_cf N P hP y hy), hrecord.1, ?_, ?_⟩
  · intro ω p hp
    exact aqCandidateRecord_verified h s M B (List.ofFn ω) p hp
  · intro ω
    exact (hrecord.2 ω).trans (Nat.mul_le_mul_left R (by omega))

end Qatlib.Concepts.AmpTransform.FullLayerCF
