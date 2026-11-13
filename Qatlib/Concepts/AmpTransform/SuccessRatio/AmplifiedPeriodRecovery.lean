/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedProgressionWindow
import Qatlib.Concepts.HspRecovery.CfOrder.CountedContinuedFractionDecoder

/-!
# Verified period recovery from amplified Fourier samples

`aqAttempt` combines continued fraction decoding with a counted membership verifier for a marked
arithmetic progression. The retry procedures establish recovery probabilities, worst case query
caps, and expected query bounds, including recovery over a finite list of possible offsets. See
[Cornwell2014] for background.

## Main statements

* `amplified_progression_actual_cf_decode_and_counts`: Under the progression and separation
  hypotheses, a decoded attempt returns only the true period, succeeds on the good window, and
  satisfies the stated membership and continued fraction operation counts. See [Cornwell2014].
* `amplified_progression_actual_fresh_retry`: Under the progression and separation hypotheses,
  fresh amplified samples have normalized product mass, period recovery succeeds with mass at
  least `1 - (1 - q)^R`, costs at most `R * (k + 3)`, and has expected cost at most `(k + 3) /
  q`. See [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace Qatlib.Concepts.AmpTransform.SuccessRatio
open scoped Classical BigOperators

/-- Checks a candidate offset and period at three progression positions, returning acceptance
and the number of membership queries. -/
def aqVerify {N : ℕ} (f : Fin N→Bool) (s M q : ℕ) : Bool×ℕ :=
  if h:0< q ∧ s< N ∧ s+q< N ∧ s+(M-1)*q< N then
    ([⟨s,h.2.1⟩,⟨s+q,h.2.2.1⟩,⟨s+(M-1)*q,h.2.2.2⟩]:List (Fin N)).foldl
      (fun a x=>(a.1 && f x,a.2+1)) (true,0)
  else (false,0)
/-- Decodes a Fourier sample by continued fractions and verifies its candidate period, returning
the optional period together with membership and decoder operation counts. -/
def aqAttempt {N : ℕ} (f : Fin N→Bool) (s M B : ℕ) (y : Fin N) : Option ℕ×ℕ×ℕ×ℕ :=
  let d:= cfRationalDecode B N y.val;
  match d.1 with
  | none => (none,0,d.2.1,d.2.2)
  | some c => let v:= aqVerify f s M c.2;
      (if v.1 then some c.2 else none,v.2,d.2.1,d.2.2)
/-- Tries successive samples until period verification succeeds, adding the fixed cost `k` and
the verification cost for each attempted sample. -/
def aqRetry {N : ℕ} (f : Fin N→Bool) (s M B k : ℕ) : List (Fin N)→Option ℕ×ℕ
  | [] => (none,0)
  | y::ys => let t:= aqAttempt f s M B y;
      match t.1 with
      | some q => (some q,k+t.2.1)
      | none => let a:= aqRetry f s M B k ys; (a.1,a.2+k+t.2.1)
/-- Scans candidate offsets for a fixed period, returning the first verified offset and the
accumulated membership query count. -/
def aqOffsetScan {N : ℕ} (f : Fin N→Bool) (M q : ℕ) : List ℕ→Option ℕ×ℕ
  | [] => (none,0)
  | s::ss => let v:= aqVerify f s M q;
      if v.1 then (some s,v.2) else let a:= aqOffsetScan f M q ss; (a.1,a.2+v.2)
/-- Decodes a sample and scans the supplied offsets for a verified offset and period, retaining
membership and continued fraction operation counts. -/
def aqOffsetAttempt {N : ℕ} (f : Fin N→Bool) (M B : ℕ) (offsets : List ℕ)
    (y : Fin N) : Option (ℕ×ℕ)×ℕ×ℕ×ℕ :=
  let d:= cfRationalDecode B N y.val;
  match d.1 with
  | none => (none,0,d.2.1,d.2.2)
  | some c => let a:= aqOffsetScan f M c.2 offsets;
      (a.1.map (fun s=>(s,c.2)),a.2,d.2.1,d.2.2)
/-- Retries offset and period recovery on successive samples, accumulating the fixed preparation
cost and the membership verification cost. -/
def aqOffsetRetry {N : ℕ} (f : Fin N→Bool) (M B k : ℕ) (offsets : List ℕ) :
    List (Fin N)→Option (ℕ×ℕ)×ℕ
  | [] => (none,0)
  | y::ys => let t:= aqOffsetAttempt f M B offsets y;
      match t.1 with
      | some z => (some z,k+t.2.1)
      | none => let a:= aqOffsetRetry f M B k offsets ys; (a.1,a.2+k+t.2.1)
/-- The Born weight of a Fourier outcome for the amplified state of the specified arithmetic
progression. -/
noncomputable def aqWeight (N : ℕ) (hN : 0< N) (M s P : ℕ) (y : Fin N) : ℝ :=
  BornProb (aqState N hN M (aqProgressionSet N s M P)) y
/-- The product of the amplified Fourier Born weights along a finite record of fresh samples. -/
noncomputable def aqFreshMass (N : ℕ) (hN : 0< N) (M s P : ℕ) {R : ℕ} (ω : Fin R→Fin N) : ℝ :=
  ∏ r,aqWeight N hN M s P (ω r)

/-- The progression verifier uses at most three membership queries. -/
theorem aqVerify_cost {N : ℕ} (f : Fin N → Bool) (s M q : ℕ) : (aqVerify f s M q).2 ≤ 3 := by
  unfold aqVerify
  split <;> simp

/-- Under the nonwrapping marked progression promise with at least two points and positive
period, verification accepts exactly the true offset and period. -/
theorem aqVerify_sound {N : ℕ} (f : Fin N → Bool) (s M P s1 q : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hb : s+(M-1)*P < N)
    (hf : AQMarkPromise f s M P) :
    (aqVerify f s1 M q).1 = true ↔ s1 = s ∧ q = P := by
  unfold aqVerify
  split
  · rename_i h
    simp only [List.foldl_cons, List.foldl_nil, Bool.true_and, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨h0,h1⟩,h2⟩
      rw [hf] at h0 h1 h2
      have hm0 := of_decide_eq_true h0
      have hm1 := of_decide_eq_true h1
      have hm2 := of_decide_eq_true h2
      obtain ⟨r,hr,er⟩ := (Finset.mem_filter.mp hm0).2
      obtain ⟨t,ht,et⟩ := (Finset.mem_filter.mp hm1).2
      obtain ⟨u,hu,eu⟩ := (Finset.mem_filter.mp hm2).2
      simp only [Finset.mem_range] at hr ht hu er et eu
      have hrt : r < t := by
        by_contra hn
        have hh := Nat.mul_le_mul_right P (show t ≤ r by omega)
        omega
      have hqP : P ≤ q := by
        have hh := Nat.mul_le_mul_right P (show r+1 ≤ t by omega)
        nlinarith
      have hlast := Nat.mul_le_mul_right P (show u ≤ M-1 by omega)
      have hspan := Nat.mul_le_mul_left (M-1) hqP
      have hprod : (M-1)*q = (M-1)*P := by nlinarith
      have eqp : q = P := Nat.eq_of_mul_eq_mul_left (by omega : 0 < M-1) hprod
      have er0 : r*P = 0 := by rw [eqp] at eu; nlinarith
      have eqs : s1 = s := by omega
      exact ⟨eqs,eqp⟩
    · rintro ⟨rfl,rfl⟩
      rw [hf,hf,hf]
      simp only [decide_eq_true_eq]
      refine ⟨⟨?_,?_⟩,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,0,Finset.mem_range.mpr (by omega),by simp⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,1,Finset.mem_range.mpr hM,by simp⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,M-1,Finset.mem_range.mpr (by omega),rfl⟩
  · rename_i hn
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨he,hq⟩
    rw [he,hq] at hn
    apply hn
    refine ⟨hP,by omega,?_,hb⟩
    have hh := Nat.mul_le_mul_right P (show 1 ≤ M-1 by omega)
    simp only [one_mul] at hh
    omega

/-- Under the marked progression promise, the verifier accepts exactly the true period and
offset and uses at most three membership queries. -/
theorem amplified_progression_paid_verification_soundness : ∀ (N s M P q : ℕ) (f : Fin N→Bool),
  2≤ M → 0< P → s+(M-1)*P< N → AQMarkPromise f s M P →
  ((aqVerify f s M q).1= true ↔ q= P) ∧
  (∀ s1 : ℕ,(aqVerify f s1 M q).1= true ↔ s1= s ∧ q= P) ∧
  (∀ s1 : ℕ,(aqVerify f s1 M q).2≤3) := by
  intro N s M P q f hM hP hb hf
  refine ⟨?_,fun s1 => aqVerify_sound f s M P s1 q hM hP hb hf,fun s1 => aqVerify_cost f s1 M q⟩
  simpa using! aqVerify_sound f s M P s q hM hP hb hf

/-- A sample in `aqGoodWindow` decodes to a rational with denominator `P` when `P ≤ B` and `2 *
B^2 < N`. -/
theorem aq_good_decode (N P B : ℕ) (y : Fin N) (hP : 0 < P) (hPB : P ≤ B)
    (hsep : 2*B^2 < N) (hy : y ∈ aqGoodWindow N P) :
    ∃ a, (cfRationalDecode B N y.val).1 = some (a,P) := by
  obtain ⟨a,ha,hcop,hw⟩ := (Finset.mem_filter.mp hy).2
  have hNR : (0:ℚ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw' : |(y.val:ℚ)/N-(a:ℚ)/P| ≤ 1/(N:ℚ) := hw.trans (by
    apply one_div_le_one_div_of_le hNR
    linarith)
  exact ⟨a,(continued_fraction_unique_window_decode_and_counts B N y.val a P hP hPB ha hcop hsep y.isLt hw').1⟩

/-- Under the progression and separation hypotheses, a decoded attempt returns only the true
period, succeeds on the good window, and satisfies the stated membership and continued
fraction operation counts. See [Cornwell2014]. -/
theorem amplified_progression_actual_cf_decode_and_counts : ∀ (N s M P B : ℕ) (f : Fin N→Bool) (y : Fin N),
  2≤ M → 2≤ P → s+(M-1)*P< N → P≤ B → 2*B^2< N → AQMarkPromise f s M P →
  ((aqAttempt f s M B y).1= none ∨ (aqAttempt f s M B y).1= some P) ∧
  (y∈aqGoodWindow N P → (aqAttempt f s M B y).1= some P) ∧
  (aqAttempt f s M B y).2.1≤3 ∧
  (aqAttempt f s M B y).2.2.1≤ cfDepth N+1 ∧
  (aqAttempt f s M B y).2.2.2=(cfDepth N+1)*(cfDepth N+2)/2 := by
  intro N s M P B f y hM hP hb hPB hsep hf
  have hsound := fun q => aqVerify_sound f s M P s q hM (by omega) hb hf
  have hd := continued_fraction_bad_output_soundness_and_work B N y.val
  have hg : (cfRationalDecode B N y.val).2.2 = (cfDepth N+1)*(cfDepth N+2)/2 := by
    simp [cfRationalDecode, (show N ≠ 0 by omega), cfGenerationWork_eq]
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold aqAttempt
    (try dsimp only)
    split
    · exact Or.inl rfl
    · rename_i c hc
      (try dsimp only)
      split
      · rename_i hv
        have hq := (hsound c.2).mp hv
        simp only [true_and] at hq
        exact Or.inr (congrArg some hq)
      · exact Or.inl rfl
  · intro hy
    obtain ⟨a,ha⟩ := aq_good_decode N P B y (by omega) hPB hsep hy
    have hv : (aqVerify f s M P).1 = true := (hsound P).mpr ⟨rfl,rfl⟩
    simp [aqAttempt,ha,hv]
  · unfold aqAttempt
    (try dsimp only)
    split
    · simp
    · exact aqVerify_cost _ _ _ _
  · unfold aqAttempt
    (try dsimp only)
    split <;> exact hd.1
  · unfold aqAttempt
    (try dsimp only)
    split <;> exact hg

/-- Offset scanning returns only the true offset with the true period, finds it when present in
the list, and uses at most three membership queries per listed offset. -/
theorem aqOffsetScan_spec {N : ℕ} (f : Fin N → Bool) (s M P q : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hb : s+(M-1)*P < N) (hf : AQMarkPromise f s M P)
    (offsets : List ℕ) :
    ((aqOffsetScan f M q offsets).1 = none ∨ ((aqOffsetScan f M q offsets).1 = some s ∧ q = P)) ∧
    (q = P → s ∈ offsets → (aqOffsetScan f M q offsets).1 = some s) ∧
    (aqOffsetScan f M q offsets).2 ≤ 3*offsets.length := by
  induction offsets with
  | nil => simp [aqOffsetScan]
  | cons x xs ih =>
    have hv := aqVerify_sound f s M P x q hM hP hb hf
    by_cases hx : (aqVerify f x M q).1 = true
    · obtain ⟨he,hq⟩ := hv.mp hx
      simp only [aqOffsetScan,hx,ite_true,List.length_cons]
      refine ⟨Or.inr ⟨congrArg some he,hq⟩,?_,?_⟩
      · intro _ _; exact congrArg some he
      · exact (aqVerify_cost f x M q).trans (by omega)
    · have hxfalse : (aqVerify f x M q).1 = false := Bool.eq_false_iff.mpr hx
      simp only [aqOffsetScan,hxfalse,Bool.false_eq_true,ite_false,List.length_cons]
      refine ⟨ih.1,?_,?_⟩
      · intro hq hs
        have hxs : x ≠ s := by
          intro he
          exact hx (hv.mpr ⟨he,hq⟩)
        exact ih.2.1 hq
            (by rcases List.mem_cons.mp hs with he | hh; exact False.elim (hxs he.symm); exact hh)
      · have hc := aqVerify_cost f x M q
        omega

/-- Under the progression promise and decoder separation bound, scanning a list containing the
true offset recovers only the true offset and period, succeeds on the good window, and
satisfies the stated operation bounds. -/
theorem amplified_progression_finite_offset_set_actual_recovery : ∀ (N s M P B : ℕ) (f : Fin N→Bool) (offsets : List ℕ) (y : Fin N),
  2≤ M → 2≤ P → s+(M-1)*P< N → P≤ B → 2*B^2< N → AQMarkPromise f s M P → s∈offsets →
  ((aqOffsetAttempt f M B offsets y).1= none ∨ (aqOffsetAttempt f M B offsets y).1= some (s,P)) ∧
  (y∈aqGoodWindow N P → (aqOffsetAttempt f M B offsets y).1= some (s,P)) ∧
  (aqOffsetAttempt f M B offsets y).2.1≤3*offsets.length ∧
  (aqOffsetAttempt f M B offsets y).2.2.1≤ cfDepth N+1 ∧
  (aqOffsetAttempt f M B offsets y).2.2.2=(cfDepth N+1)*(cfDepth N+2)/2 := by
  intro N s M P B f offsets y hM hP hb hPB hsep hf hs
  have hv := fun q => aqOffsetScan_spec f s M P q hM (by omega) hb hf offsets
  have hd := continued_fraction_bad_output_soundness_and_work B N y.val
  have hg : (cfRationalDecode B N y.val).2.2 = (cfDepth N+1)*(cfDepth N+2)/2 := by
    simp [cfRationalDecode, (show N ≠ 0 by omega), cfGenerationWork_eq]
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold aqOffsetAttempt
    (try dsimp only)
    split
    · exact Or.inl rfl
    · rename_i c hc
      rcases (hv c.2).1 with hn | ⟨he,hq⟩
      · simp [hn]
      · simp only [he,Option.map_some]; exact Or.inr (by rw [hq])
  · intro hy
    obtain ⟨a,ha⟩ := aq_good_decode N P B y (by omega) hPB hsep hy
    simp [aqOffsetAttempt,ha,(hv P).2.1 rfl hs]
  · unfold aqOffsetAttempt
    (try dsimp only)
    split
    · simp
    · exact (hv _).2.2
  · unfold aqOffsetAttempt
    (try dsimp only)
    split <;> exact hd.1
  · unfold aqOffsetAttempt
    (try dsimp only)
    split <;> exact hg

/-- Repeats a counted partial procedure until its first success, charging a fixed overhead `k`
on every attempted input. -/
def aqRepeat {I Z : Type} (a : I → Option Z × ℕ) (k : ℕ) : List I → Option Z × ℕ
  | [] => (none,0)
  | x::xs => match (a x).1 with
    | some z => (some z,k+(a x).2)
    | none => let t := aqRepeat a k xs; (t.1,t.2+k+(a x).2)

/-- The product of the weights assigned by `w` to the entries of a finite sample record. -/
noncomputable def aqProductMass {I : Type} (w : I → ℝ) {R : ℕ} (ω : Fin R → I) : ℝ :=
  ∏ r, w (ω r)

/-- A sum over records of length `R + 1` decomposes into a sum over the first entry and the
remaining record. -/
theorem aq_sum_records_succ {I : Type} [Fintype I] (R : ℕ) (F : (Fin (R+1) → I) → ℝ) :
    (∑ ω, F ω) = ∑ x, ∑ τ : Fin R → I, F (Fin.cons x τ) := by
  rw [← (Fin.consEquiv (fun _ : Fin (R+1) => I)).sum_comp F]
  exact Fintype.sum_prod_type _

/-- The product weight of a record with first entry `x` factors as `w x` times the tail weight. -/
@[simp] theorem aqProductMass_cons {I : Type} (w : I → ℝ) {R : ℕ} (x : I) (τ : Fin R → I) :
    aqProductMass w (Fin.cons x τ) = w x * aqProductMass w τ := by
  simp [aqProductMass,Fin.prod_univ_succ]

/-- Product weights on records of any finite length sum to one when the single sample weights
sum to one. -/
theorem aqProductMass_total {I : Type} [Fintype I] (w : I → ℝ) (hw : ∑ x,w x = 1) (R : ℕ) :
    (∑ ω : Fin R → I, aqProductMass w ω) = 1 := by
  induction R with
  | zero => simp [aqProductMass]
  | succ R ih =>
    rw [aq_sum_records_succ]
    simp only [aqProductMass_cons,← Finset.mul_sum,ih,mul_one,hw]

/-- Repeating a procedure that returns only `z` or fails preserves this property and costs at
most the list length times the per-attempt cap. -/
theorem aqRepeat_sound_cap {I Z : Type} (a : I → Option Z × ℕ) (z : Z) (k C : ℕ)
    (hs : ∀ x,(a x).1 = none ∨ (a x).1 = some z) (hc : ∀ x,k+(a x).2 ≤ C) (xs : List I) :
    ((aqRepeat a k xs).1 = none ∨ (aqRepeat a k xs).1 = some z) ∧
    (aqRepeat a k xs).2 ≤ xs.length*C := by
  induction xs with
  | nil => simp [aqRepeat]
  | cons x xs ih =>
    rcases hs x with hn | hz
    · simp only [aqRepeat,hn,List.length_cons]
      exact ⟨ih.1,by have hh := hc x; have hi := ih.2; nlinarith⟩
    · simp only [aqRepeat,hz,List.length_cons]
      exact ⟨Or.inr True.intro,(hc x).trans (by nlinarith)⟩

/-- The total product weight of records on which every attempt fails is the single attempt
failure weight raised to `R`. -/
theorem aqRepeat_timeout {I Z : Type} [Fintype I] (w : I → ℝ) (a : I → Option Z × ℕ) (k R : ℕ) :
    (∑ ω : Fin R → I, if (aqRepeat a k (List.ofFn ω)).1 = none then aqProductMass w ω else 0) =
      (∑ x, if (a x).1 = none then w x else 0)^R := by
  induction R with
  | zero => simp [aqRepeat,aqProductMass]
  | succ R ih =>
    rw [aq_sum_records_succ]
    have hx (x : I) :
        (∑ τ : Fin R → I, if (aqRepeat a k (List.ofFn (Fin.cons x τ))).1 = none
          then aqProductMass w (Fin.cons x τ) else 0) =
        (if (a x).1 = none then w x else 0)*(∑ x, if (a x).1 = none then w x else 0)^R := by
      cases hn : (a x).1 with
      | none =>
        simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,aqRepeat,hn,aqProductMass_cons,ite_true]
        have he (τ : Fin R → I) :
            (if (aqRepeat a k (List.ofFn τ)).1 = none then w x*aqProductMass w τ else 0) =
            w x*(if (aqRepeat a k (List.ofFn τ)).1 = none then aqProductMass w τ else 0) := by split <;> simp_all
        simp_rw [he]
        rw [← Finset.mul_sum,ih]
      | some z => simp [List.ofFn_succ,aqRepeat,hn]
    simp_rw [hx]
    rw [← Finset.sum_mul,pow_succ,mul_comm]

/-- For normalized nonnegative weights and success probability at least positive `q`, the
expected retry cost is at most `C / q` when each attempt costs at most `C`. -/
theorem aqRepeat_expected {I Z : Type} [Fintype I] (w : I → ℝ) (a : I → Option Z × ℕ)
    (k C : ℕ) (q : ℝ) (hw0 : ∀ x,0 ≤ w x) (hw : ∑ x,w x = 1) (hq : 0 < q)
    (hb : (∑ x, if (a x).1 = none then w x else 0) ≤ 1-q)
    (hc : ∀ x,k+(a x).2 ≤ C) (R : ℕ) :
    (∑ ω : Fin R → I, aqProductMass w ω*((aqRepeat a k (List.ofFn ω)).2:ℝ)) ≤ (C:ℝ)/q := by
  induction R with
  | zero => simp only [List.ofFn_zero,aqRepeat,Nat.cast_zero,mul_zero,Finset.sum_const_zero]; positivity
  | succ R ih =>
    rw [aq_sum_records_succ]
    have hx (x : I) :
        (∑ τ : Fin R → I, aqProductMass w (Fin.cons x τ)*
          ((aqRepeat a k (List.ofFn (Fin.cons x τ))).2:ℝ)) ≤
        w x*(C:ℝ)+(if (a x).1 = none then w x else 0)*((C:ℝ)/q) := by
      have hcx : ((k+(a x).2:ℕ):ℝ) ≤ C := by exact_mod_cast hc x
      cases hn : (a x).1 with
      | none =>
        simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,aqRepeat,hn,aqProductMass_cons,
          Nat.cast_add,ite_true]
        have he : (∑ τ : Fin R → I, w x*aqProductMass w τ*
            (((aqRepeat a k (List.ofFn τ)).2:ℝ)+(k:ℝ)+((a x).2:ℝ))) =
            w x*(∑ τ : Fin R → I, aqProductMass w τ*((aqRepeat a k (List.ofFn τ)).2:ℝ))+
              w x*((k:ℝ)+((a x).2:ℝ)) := by
          simp_rw [mul_add,mul_assoc,Finset.sum_add_distrib]
          simp only [← Finset.mul_sum,← Finset.sum_mul,aqProductMass_total w hw R,one_mul]
          ring
        rw [he]
        have hi := mul_le_mul_of_nonneg_left ih (hw0 x)
        have hi2 := mul_le_mul_of_nonneg_left hcx (hw0 x)
        push_cast at hi2
        linarith
      | some z =>
        simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,aqRepeat,hn,aqProductMass_cons,
          Option.some_ne_none,ite_false,zero_mul,add_zero]
        rw [show (∑ τ : Fin R → I,w x*aqProductMass w τ*((k+(a x).2:ℕ):ℝ)) =
          w x*((k+(a x).2:ℕ):ℝ) by
          simp only [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,aqProductMass_total w hw R,one_mul]]
        exact mul_le_mul_of_nonneg_left hcx (hw0 x)
    calc
      _ ≤ ∑ x, (w x*(C:ℝ)+(if (a x).1 = none then w x else 0)*((C:ℝ)/q)) := Finset.sum_le_sum (fun x _ => hx x)
      _ = (C:ℝ)+(∑ x, if (a x).1 = none then w x else 0)*((C:ℝ)/q) := by
        rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,hw,one_mul]
      _ ≤ (C:ℝ)+(1-q)*((C:ℝ)/q) := by gcongr
      _ = (C:ℝ)/q := by field_simp; ring

/-- A sound retry procedure with success mass at least positive `q` succeeds within `R` fresh
samples with mass at least `1 - (1 - q)^R`, has cost at most `R * C`, and has expected cost
at most `C / q`. -/
theorem aqRepeat_fresh_bounds {I Z : Type} [Fintype I] [DecidableEq I] [DecidableEq Z]
    (w : I → ℝ) (a : I → Option Z × ℕ) (z : Z) (k C : ℕ) (q : ℝ)
    (hw0 : ∀ x,0 ≤ w x) (hw : ∑ x,w x = 1) (hq : 0 < q)
    (hs : ∀ x,(a x).1 = none ∨ (a x).1 = some z) (hc : ∀ x,k+(a x).2 ≤ C)
    (hp : q ≤ ∑ x, if (a x).1 = some z then w x else 0) (R : ℕ) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin R → I => (aqRepeat a k (List.ofFn ω)).1 = some z),aqProductMass w ω) ≥ 1-(1-q)^R ∧
    (∀ ω : Fin R → I,(aqRepeat a k (List.ofFn ω)).2 ≤ R*C) ∧
    (∑ ω : Fin R → I, aqProductMass w ω*((aqRepeat a k (List.ofFn ω)).2:ℝ)) ≤ (C:ℝ)/q := by
  let b : ℝ := ∑ x,if (a x).1 = none then w x else 0
  have hb0 : 0 ≤ b := Finset.sum_nonneg (fun x _ => by split <;> simp_all)
  have hsplit : b+(∑ x,if (a x).1 = some z then w x else 0) = 1 := by
    rw [← hw,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases hs x with hn | hz
    · simp [hn]
    · simp [hz]
  have hb : b ≤ 1-q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have htot := aqProductMass_total w hw R
  have hfail := aqRepeat_timeout w a k R
  have hsucc : (∑ ω ∈ Finset.univ.filter (fun ω : Fin R → I => (aqRepeat a k (List.ofFn ω)).1 = some z),aqProductMass w ω) = 1-b^R := by
    rw [Finset.sum_filter]
    have he : (∑ ω : Fin R → I,if (aqRepeat a k (List.ofFn ω)).1 = some z then aqProductMass w ω else 0)+
        (∑ ω : Fin R → I,if (aqRepeat a k (List.ofFn ω)).1 = none then aqProductMass w ω else 0) = 1 := by
      rw [← htot,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      rcases (aqRepeat_sound_cap a z k C hs hc (List.ofFn ω)).1 with hn | hz
      · simp [hn]
      · simp [hz]
    change _ = b^R at hfail
    linarith
  refine ⟨?_,?_,aqRepeat_expected w a k C q hw0 hw hq hb hc R⟩
  · rw [hsucc]
    have hpw : b^R ≤ (1-q)^R := pow_le_pow_left₀ hb0 hb R
    linarith
  · intro ω
    simpa using! (aqRepeat_sound_cap a z k C hs hc (List.ofFn ω)).2

/-- `aqRetry` is the generic retry procedure applied to the result and membership cost of
`aqAttempt`. -/
theorem aqRetry_as_repeat {N : ℕ} (f : Fin N → Bool) (s M B k : ℕ) (xs : List (Fin N)) :
    aqRetry f s M B k xs = aqRepeat (fun y => ((aqAttempt f s M B y).1,(aqAttempt f s M B y).2.1)) k xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [aqRetry,aqRepeat]
    cases hn : (aqAttempt f s M B x).1 <;> simp [ih]

/-- `aqOffsetRetry` is the generic retry procedure applied to the result and membership cost of
`aqOffsetAttempt`. -/
theorem aqOffsetRetry_as_repeat {N : ℕ} (f : Fin N → Bool) (M B k : ℕ) (offsets : List ℕ) (xs : List (Fin N)) :
    aqOffsetRetry f M B k offsets xs = aqRepeat (fun y => ((aqOffsetAttempt f M B offsets y).1,(aqOffsetAttempt f M B offsets y).2.1)) k xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [aqOffsetRetry,aqRepeat]
    cases hn : (aqOffsetAttempt f M B offsets x).1 <;> simp [ih]

/-- Any decoder that returns `z` throughout the good window has amplified success mass at least
`aqSuccessLower` under the stated progression and separation bounds. -/
theorem aq_attempt_mass_lower {N : ℕ} (hN : 0 < N) (s M P B : ℕ)
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s+(M-1)*P < N) (hMN : 2*M ≤ N)
    (hMP : M*P ≤ N) (hPB : P ≤ B) (hsep : 2*B^2 < N)
    {Z : Type} [DecidableEq Z] (z : Z) (a : Fin N → Option Z)
    (ha : ∀ y,y ∈ aqGoodWindow N P → a y = some z) :
    aqSuccessLower N M P ≤ ∑ y,if a y = some z then aqWeight N hN M s P y else 0 := by
  have hwin :=
      amplified_progression_actual_rational_window_mass N hN s M P B hM hP hb hMN hMP hPB hsep
  apply hwin.2.1.trans
  have he : MeasureProb (aqState N hN M (aqProgressionSet N s M P)) (aqGoodWindow N P) =
      ∑ y,if y ∈ aqGoodWindow N P then aqWeight N hN M s P y else 0 := by
    simp [Finset.sum_ite_mem,MeasureProb,aqWeight]
  rw [he]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : y ∈ aqGoodWindow N P
  · simp [hy,ha y hy]
  · simp only [hy,ite_false]
    split
    · exact bornProb_nonneg _ _
    · exact le_rfl

/-- Under the progression and separation hypotheses, fresh amplified samples have normalized
product mass, period recovery succeeds with mass at least `1 - (1 - q)^R`, costs at most `R
* (k + 3)`, and has expected cost at most `(k + 3) / q`. See [Cornwell2014]. -/
theorem amplified_progression_actual_fresh_retry : ∀ (N : ℕ) (hN : 0< N) (s M P B R : ℕ) (f : Fin N→Bool),
  2≤ M → 2≤ P → s+(M-1)*P< N → 2*M≤ N → M*P≤ N → P≤ B → 2*B^2< N → AQMarkPromise f s M P →
  let k:= aqRounds N M;
  let q:= aqSuccessLower N M P;
  (∑ ω : Fin R→Fin N,aqFreshMass N hN M s P ω)=1 ∧
  (∑ ω∈Finset.univ.filter (fun ω : Fin R→Fin N =>
    (aqRetry f s M B k (List.ofFn ω)).1= some P),aqFreshMass N hN M s P ω)≥1-(1-q)^R ∧
  (∀ ω : Fin R→Fin N,(aqRetry f s M B k (List.ofFn ω)).2≤ R*(k+3)) ∧
  (∑ ω : Fin R→Fin N,aqFreshMass N hN M s P ω*((aqRetry f s M B k (List.ofFn ω)).2:ℝ))≤
    ((k+3:ℕ):ℝ)/q
 := by
  intro N hN s M P B R f hM hP hb hMN hMP hPB hsep hf
  (try dsimp only)
  let a : Fin N → Option ℕ × ℕ := fun y => ((aqAttempt f s M B y).1,(aqAttempt f s M B y).2.1)
  have hspec :=
      fun y => amplified_progression_actual_cf_decode_and_counts N s M P B f y hM hP hb hPB hsep hf
  have hn :=
      (amplified_progression_actual_circuit_and_counts N hN s M P (by omega) (by omega) hb (by omega)).2.2.1
  have hw : (∑ y,aqWeight N hN M s P y) = 1 := by
    simpa [MeasureProb,aqWeight] using! measureProb_univ hn
  have hq :=
      (amplified_progression_actual_rational_window_mass N hN s M P B hM hP hb hMN hMP hPB hsep).1
  have hp := aq_attempt_mass_lower hN s M P B hM hP hb hMN hMP hPB hsep P (fun y => (a y).1)
    (fun y hy => (hspec y).2.1 hy)
  have hr := aqRepeat_fresh_bounds (aqWeight N hN M s P) a P (aqRounds N M) (aqRounds N M+3)
    (aqSuccessLower N M P) (fun y => bornProb_nonneg _ _) hw hq (fun y => (hspec y).1)
    (fun y => by dsimp [a]; have hc := (hspec y).2.2.1; omega) hp R
  refine ⟨?_,?_,?_,?_⟩
  · exact aqProductMass_total _ hw R
  · simpa only [aqRetry_as_repeat,aqFreshMass,aqProductMass,a] using! hr.1
  · simpa only [aqRetry_as_repeat,a] using! hr.2.1
  · simpa only [aqRetry_as_repeat,aqFreshMass,aqProductMass,a] using! hr.2.2

/-- For a candidate list containing the true offset, fresh retries recover the offset and period
with mass at least `1 - (1 - q)^R` and satisfy the stated worst case and expected query
bounds. See [Cornwell2014]. -/
theorem amplified_progression_finite_offset_set_fresh_retry : ∀ (N : ℕ) (hN : 0< N) (s M P B R : ℕ)
    (f : Fin N→Bool) (offsets : List ℕ),
  2≤ M → 2≤ P → s+(M-1)*P< N → 2*M≤ N → M*P≤ N → P≤ B → 2*B^2< N → AQMarkPromise f s M P → s∈offsets →
  let k:= aqRounds N M;
  let q:= aqSuccessLower N M P;
  (∑ ω∈Finset.univ.filter (fun ω : Fin R→Fin N =>
    (aqOffsetRetry f M B k offsets (List.ofFn ω)).1= some (s,P)),aqFreshMass N hN M s P ω)≥1-(1-q)^R ∧
  (∀ ω : Fin R→Fin N,(aqOffsetRetry f M B k offsets (List.ofFn ω)).2≤ R*(k+3*offsets.length)) ∧
  (∑ ω : Fin R→Fin N,aqFreshMass N hN M s P ω*((aqOffsetRetry f M B k offsets (List.ofFn ω)).2:ℝ))≤
    ((k+3*offsets.length:ℕ):ℝ)/q
 := by
  intro N hN s M P B R f offsets hM hP hb hMN hMP hPB hsep hf hs
  (try dsimp only)
  let a : Fin N → Option (ℕ×ℕ) × ℕ :=
      fun y => ((aqOffsetAttempt f M B offsets y).1,(aqOffsetAttempt f M B offsets y).2.1)
  have hspec :=
      fun y => amplified_progression_finite_offset_set_actual_recovery N s M P B f offsets y hM hP hb hPB hsep hf hs
  have hn :=
      (amplified_progression_actual_circuit_and_counts N hN s M P (by omega) (by omega) hb (by omega)).2.2.1
  have hw : (∑ y,aqWeight N hN M s P y) = 1 := by
    simpa [MeasureProb,aqWeight] using! measureProb_univ hn
  have hq :=
      (amplified_progression_actual_rational_window_mass N hN s M P B hM hP hb hMN hMP hPB hsep).1
  have hp := aq_attempt_mass_lower hN s M P B hM hP hb hMN hMP hPB hsep (s,P) (fun y => (a y).1)
    (fun y hy => (hspec y).2.1 hy)
  have hr := aqRepeat_fresh_bounds (aqWeight N hN M s P) a (s,P) (aqRounds N M) (aqRounds N M+3*offsets.length)
    (aqSuccessLower N M P) (fun y => bornProb_nonneg _ _) hw hq (fun y => (hspec y).1)
    (fun y => by dsimp [a]; have hc := (hspec y).2.2.1; omega) hp R
  refine ⟨?_,?_,?_⟩
  · simpa only [aqOffsetRetry_as_repeat,aqFreshMass,aqProductMass,a] using! hr.1
  · simpa only [aqOffsetRetry_as_repeat,a] using! hr.2.1
  · simpa only [aqOffsetRetry_as_repeat,aqFreshMass,aqProductMass,a] using! hr.2.2

end Qatlib.Concepts.AmpTransform.SuccessRatio
