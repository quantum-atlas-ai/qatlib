/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteMaximumLikelihood
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Sample identification and finite abelian characters

`SampleEfficientIdentification` specifies a logarithmic-in-confidence sample bound for
identifying a finite family of distributions. The module proves this property for the stated
Borel measurement law and separately proves separation by finite abelian characters, two
ingredients in the setting of [DenneyMooreRussell2008].

## Main statements

* `borel_hsp_efficient`: the prescribed measurement law supports sample-efficient
  identification.
* `characters_separate_points`: complex multiplicative characters distinguish distinct finite
  abelian group elements.

## References

* [Denney et al., 2008][DenneyMooreRussell2008]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.PSL2ConjStab08.MainResults.BorelAffineSolvability

/-- The property that some positive constant bounds the number of independent samples by `C *
(log (1 / δ) + 1)` while allowing identification of every parameter with probability at
least `1 − δ`. -/
def SampleEfficientIdentification {X : Type*} [Fintype X] [DecidableEq X]
    (law : X → FinDist X) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ n : ℕ, (n : ℝ) ≤ C * (Real.log (1 / δ) + 1) ∧
      ∃ identify : (Fin n → X) → X,
        ∀ x : X, 1 - δ ≤ (law x).probEvent (fun ω => identify ω = x)

/-- For `m + 1 ≥ 3`, the finite measurement law with mass `1 − 1 / (m + 1)` at the parameter and
equal remaining masses possesses `SampleEfficientIdentification`. See
[DenneyMooreRussell2008]. -/
theorem borel_hsp_efficient (m : ℕ) (hq : 3 ≤ m + 1)
    (law : Fin (m + 1) → FinDist (Fin (m + 1)))
    (hlaw : ∀ b ℓ : Fin (m + 1), (law b).prob ℓ =
      if ℓ = b then 1 - 1 / ((m + 1 : ℕ) : ℝ)
      else 1 / (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1))) :
    SampleEfficientIdentification law := by

  classical
  set r : ℝ := ((m + 1 : ℕ) : ℝ) with hr
  have hr3 : (3 : ℝ) ≤ r := by rw [hr]; exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hr1' : (1 : ℝ) < r - 1 := by linarith
  have hlawR : ∀ b ℓ : Fin (m + 1), (law b).prob ℓ =
      if ℓ = b then 1 - 1 / r else 1 / (r * (r - 1)) := by
    intro b ℓ; rw [hr]; exact hlaw b ℓ
  set L : ℝ := Real.log (r - 1) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hr1'
  set R : ℝ := ((r - 1) ^ 2 - 1) / (r * (r - 1)) with hR
  have hden : 0 < r * (r - 1) := mul_pos hr0 hr1
  have hnum : 0 < (r - 1) ^ 2 - 1 := by
    nlinarith [hr1', mul_pos hr1 hr1]
  have hRpos : 0 < R := by rw [hR]; exact div_pos hnum hden
  set D : ℝ := 2 * L * R with hD
  have hDpos : 0 < D := by
    rw [hD]; exact mul_pos (mul_pos (by norm_num) hLpos) hRpos
  set kk : ℝ := R ^ 2 / 2 with hk
  have hkpos : 0 < kk := by
    rw [hk]; exact div_pos (pow_pos hRpos 2) (by norm_num)

  have hpos : ∀ c x : Fin (m + 1), 0 < (law c).prob x := by
    intro c x
    rw [hlawR c x]
    by_cases hx : x = c
    · rw [if_pos hx, show (1 : ℝ) - 1 / r = (r - 1) / r by field_simp]
      exact div_pos hr1 hr0
    · rw [if_neg hx]; exact div_pos (by norm_num) hden

  have hpSne : (1 : ℝ) - 1 / r ≠ 0 := by
    have h : (1 : ℝ) - 1 / r = (r - 1) / r := by field_simp
    rw [h]; exact div_ne_zero hr1.ne' hr0.ne'
  have hpDne : 1 / (r * (r - 1)) ≠ 0 := div_ne_zero (by norm_num) hden.ne'
  have hratio : (1 - 1 / r) / (1 / (r * (r - 1))) = (r - 1) ^ 2 := by
    have h : (1 : ℝ) - 1 / r = (r - 1) / r := by field_simp
    rw [h]; field_simp
  have hdiff : Real.log (1 - 1 / r) - Real.log (1 / (r * (r - 1))) = 2 * L := by
    rw [← Real.log_div hpSne hpDne, hratio, Real.log_pow, hL]
    norm_num
  have hdiff' : Real.log (1 / (r * (r - 1))) - Real.log (1 - 1 / r) = -(2 * L) := by
    rw [← hdiff]; ring

  have hratioVal : ∀ (c truth : Fin (m + 1)), c ≠ truth → ∀ x : Fin (m + 1),
      Real.log ((law c).prob x) - Real.log ((law truth).prob x)
        = (if x = c then 2 * L else 0) + (if x = truth then -(2 * L) else 0) := by
    intro c truth hc x
    rw [hlawR c x, hlawR truth x]
    by_cases hxc : x = c
    · have hxt : ¬ (x = truth) := by rw [hxc]; exact hc
      simp only [if_pos hxc, if_neg hxt]
      linarith [hdiff]
    · by_cases hxt : x = truth
      · simp only [if_neg hxc, if_pos hxt]
        linarith [hdiff']
      · simp only [if_neg hxc, if_neg hxt]
        ring

  have hmeanVal : ∀ (c truth : Fin (m + 1)), c ≠ truth →
      (law truth).expect
        (fun x => Real.log ((law c).prob x) - Real.log ((law truth).prob x)) = -D := by
    intro c truth hc
    have hPc : (law truth).prob c = 1 / (r * (r - 1)) := by
      rw [hlawR truth c, if_neg hc]
    have hPt : (law truth).prob truth = 1 - 1 / r := by
      rw [hlawR truth truth, if_pos rfl]
    have hDS : 1 / (r * (r - 1)) - (1 - 1 / r) = -R := by
      rw [hR]
      have h : (1 : ℝ) - 1 / r = (r - 1) / r := by field_simp
      rw [h]; field_simp; ring
    have hSumC : ∑ x : Fin (m + 1),
        (law truth).prob x * (if x = c then 2 * L else 0) = (law truth).prob c * (2 * L) := by
      rw [Finset.sum_eq_single (a := c)
        (fun x _ hx => by rw [if_neg hx, mul_zero])
        (fun hx => absurd (Finset.mem_univ c) hx)]
      rw [if_pos rfl]
    have hSumT : ∑ x : Fin (m + 1),
        (law truth).prob x * (if x = truth then -(2 * L) else 0) =
        (law truth).prob truth * (-(2 * L)) := by
      rw [Finset.sum_eq_single (a := truth)
        (fun x _ hx => by rw [if_neg hx, mul_zero])
        (fun hx => absurd (Finset.mem_univ truth) hx)]
      rw [if_pos rfl]
    rw [FinDist.expect]
    calc ∑ x, (law truth).prob x *
            (Real.log ((law c).prob x) - Real.log ((law truth).prob x))
        = ∑ x, (law truth).prob x *
            ((if x = c then 2 * L else 0) + (if x = truth then -(2 * L) else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hratioVal c truth hc x]
      _ = (∑ x, (law truth).prob x * (if x = c then 2 * L else 0))
            + ∑ x, (law truth).prob x * (if x = truth then -(2 * L) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (law truth).prob c * (2 * L) + (law truth).prob truth * (-(2 * L)) := by
          rw [hSumC, hSumT]
      _ = -D := by
          rw [hPc, hPt, hD]
          rw [show (1 / (r * (r - 1))) * (2 * L) + (1 - 1 / r) * (-(2 * L))
              = 2 * L * (1 / (r * (r - 1)) - (1 - 1 / r)) by ring]
          rw [hDS]; ring

  refine ⟨(Real.log r + 1) / kk + 1, ?_, ?_⟩
  · positivity
  · intro δ hδ hδ1
    set P : ℝ := Real.log (1 / δ) with hP
    have hPpos : 0 < P := by
      rw [hP]
      apply Real.log_pos
      rw [one_div]
      exact (one_lt_inv_iff₀).mpr ⟨hδ, hδ1⟩
    have hApos : 0 < Real.log r := Real.log_pos (by linarith)
    let n : ℕ := Nat.ceil ((Real.log r + P) / kk)
    have hnpos : 0 < n := by
      apply Nat.ceil_pos.mpr
      exact div_pos (by linarith) hkpos
    refine ⟨n, ?_, FiniteMaximumLikelihood.decode law, ?_⟩
    · have hceil : (n : ℝ) < (Real.log r + P) / kk + 1 :=
        Nat.ceil_lt_add_one (le_of_lt (div_pos (by linarith) hkpos))
      have hkey : (Real.log r + P) / kk + 1 ≤
          ((Real.log r + 1) / kk + 1) * (P + 1) := by
        have hdiffkey : 0 ≤ ((Real.log r + 1) / kk + 1) * (P + 1) -
            ((Real.log r + P) / kk + 1) := by
          field_simp
          nlinarith [hApos, hPpos, hkpos, mul_pos hApos hPpos, mul_pos hkpos hPpos]
        linarith
      have hfin : (n : ℝ) ≤ ((Real.log r + 1) / kk + 1) * (P + 1) := by linarith
      simpa [hP] using hfin
    · intro truth
      have hnlower : Real.log r + P ≤ (n : ℝ) * kk := by
        have hle : (Real.log r + P) / kk ≤ (n : ℝ) := Nat.le_ceil _
        have hmul := mul_le_mul_of_nonneg_right hle hkpos.le
        rwa [div_mul_cancel₀ _ hkpos.ne'] at hmul
      have hfail : (law truth).probEvent
          (fun w : Fin n → Fin (m + 1) =>
            FiniteMaximumLikelihood.decode law w ≠ truth) ≤ δ := by
        have hb := FiniteMaximumLikelihood.log_error_bound (m := m) (n := n) law truth
          (fun _ => -(2 * L)) (fun _ => 2 * L) (fun _ => D)
          hpos hnpos
          (fun c _ => by linarith [hLpos])
          (fun c _ => hDpos)
          (fun c hc x => ?_)
          (fun c hc => hmeanVal c truth hc)
        · refine hb.trans ?_
          have hterm : (∑ c with c ≠ truth,
              Real.exp (-2 * (n : ℝ) * ((fun _ : Fin (m + 1) => D) c) ^ 2 /
                (((fun _ : Fin (m + 1) => 2 * L) c) -
                  ((fun _ : Fin (m + 1) => -(2 * L)) c)) ^ 2))
              = ∑ c with c ≠ truth, Real.exp (-(n : ℝ) * kk) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [show (fun _ : Fin (m + 1) => D) c = D from rfl,
                show (fun _ : Fin (m + 1) => 2 * L) c = 2 * L from rfl,
                show (fun _ : Fin (m + 1) => -(2 * L)) c = -(2 * L) from rfl]
            congr 1
            rw [hk, hD]
            field_simp
            ring
          rw [hterm]
          have hconst : (∑ c with c ≠ truth, Real.exp (-(n : ℝ) * kk))
              = ((Finset.univ.filter (fun c : Fin (m + 1) => c ≠ truth)).card : ℝ) *
                Real.exp (-(n : ℝ) * kk) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          rw [hconst]
          have hcard : ((Finset.univ.filter
              (fun c : Fin (m + 1) => c ≠ truth)).card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
            have := Finset.card_filter_le (Finset.univ : Finset (Fin (m + 1)))
              (fun c => c ≠ truth)
            simp only [Finset.card_univ, Fintype.card_fin] at this
            exact_mod_cast this
          calc ((Finset.univ.filter (fun c : Fin (m + 1) => c ≠ truth)).card : ℝ) *
                Real.exp (-(n : ℝ) * kk)
              ≤ ((m + 1 : ℕ) : ℝ) * Real.exp (-(n : ℝ) * kk) :=
                mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
            _ ≤ ((m + 1 : ℕ) : ℝ) * Real.exp (-(Real.log r + P)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Real.exp_le_exp.mpr
                linarith [hnlower]
            _ = δ := by
                have hmr : ((m + 1 : ℕ) : ℝ) = r := hr.symm
                rw [hmr, show -(Real.log r + P) = -Real.log r + -P by ring,
                    Real.exp_add, Real.exp_neg, Real.exp_neg,
                    Real.exp_log hr0, hP,
                    Real.exp_log (by positivity : (0 : ℝ) < 1 / δ)]
                field_simp
        · rw [Set.mem_Icc, hratioVal c truth hc x]
          have hval : (if x = c then 2 * L else 0) + (if x = truth then -(2 * L) else 0) = 2 * L
              ∨ (if x = c then 2 * L else 0) + (if x = truth then -(2 * L) else 0) = -(2 * L)
              ∨ (if x = c then 2 * L else 0) + (if x = truth then -(2 * L) else 0) = 0 := by
            by_cases hxc : x = c
            · left
              rw [if_pos hxc, if_neg (by rw [hxc]; exact hc)]
              ring
            · by_cases hxt : x = truth
              · right; left
                rw [if_neg hxc, if_pos hxt]
                ring
              · right; right
                rw [if_neg hxc, if_neg hxt]
                ring
          rcases hval with h | h | h <;> rw [h] <;> constructor <;> linarith [hLpos]

      have hcompl : (law truth).probEvent
            (fun w : Fin n → Fin (m + 1) =>
              FiniteMaximumLikelihood.decode law w = truth) +
          (law truth).probEvent
            (fun w : Fin n → Fin (m + 1) =>
              FiniteMaximumLikelihood.decode law w ≠ truth) = 1 := by
        rw [FinDist.probEvent, FinDist.probEvent]
        rw [Finset.sum_filter_add_sum_filter_not (Finset.univ)
          (fun w : Fin n → Fin (m + 1) => FiniteMaximumLikelihood.decode law w = truth)
          (fun w => (law truth).probOf w)]
        rw [FinDist.sum_probOf]
      linarith [hcompl, hfail]

/-- Distinct elements of a finite commutative group are separated by a multiplicative character
with values in the nonzero complex numbers. See [DenneyMooreRussell2008]. -/
theorem characters_separate_points (A : Type*) [CommGroup A] [Fintype A]
    [DecidableEq A] :
    ∀ a b : A, a ≠ b → ∃ χ : A →* ℂˣ, χ a ≠ χ b := by

  intro a b hab
  haveI : Finite A := Finite.of_fintype A
  haveI : NeZero (Monoid.exponent A) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent A) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ (Monoid.exponent A)
  by_contra h
  simp only [not_exists, not_not] at h
  exact hab ((CommGroup.forall_apply_eq_apply_iff (G := A) (M := ℂ)).mp h)

end Qatlib.Papers.PSL2ConjStab08.MainResults.BorelAffineSolvability
