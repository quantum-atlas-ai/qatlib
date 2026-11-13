/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrder
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Smooth order conditions for product formulas

The predicate `trotterOrder F n` expresses a local bound proportional to `|t| ^ n` at zero. For
smooth functions it is equivalent to vanishing lower derivatives; for matrix product formulas,
`general_trotter_four_order_conditions` relates additive error, left and right normalized
differential defects, and multiplicative error. For background, see [ChildsEtAl2021Trotter].

## Main statements

* `trotter_smooth_order_iff`: order is characterized by vanishing jets.
* `general_trotter_four_order_conditions`: equivalence of four matrix error order conditions.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Asymptotics Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ContDiff Topology

/-- The property that `‖F t‖` is bounded by a positive constant times `|t| ^ n` on some
positive-radius neighborhood of zero. -/
def trotterOrder {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (n : ℕ) : Prop :=
  ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ ∀ t : ℝ, |t| ≤ t₀ → ‖F t‖ ≤ c*|t|^n

/-- The local norm-bound definition of `trotterOrder F n` is equivalent to `F =O[𝓝 0] (fun t =>
t ^ n)`. -/
theorem trotterOrder_iff_isBigO {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (n : ℕ) :
    trotterOrder F n ↔ F =O[𝓝 0] (fun t : ℝ => t^n) := by
  constructor
  · rintro ⟨c, t₀, hc, ht₀, h⟩
    apply IsBigO.of_bound c
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) ht₀] with t ht
    simpa only [norm_pow, Real.norm_eq_abs] using!
        h t (by simpa [Metric.mem_closedBall, Real.dist_eq] using! ht)
  · intro h
    obtain ⟨c, hc, hb⟩ := isBigO_iff'.mp h
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hb
    refine ⟨c, δ/2, hc, by positivity, ?_⟩
    intro t ht
    have hmem : t ∈ Metric.ball (0 : ℝ) δ := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      linarith
    simpa only [norm_pow, Real.norm_eq_abs] using! hd hmem

/-- If all derivatives below degree `n` vanish at zero, the degree-`n` Taylor polynomial
consists only of its leading monomial. -/
theorem trotter_taylor_leading {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (n : ℕ) (h : ∀ j, j < n → iteratedDeriv j F 0 = 0) (t : ℝ) :
    taylorWithinEval F n Set.univ 0 t = t^n • ((n.factorial : ℝ)⁻¹ • iteratedDeriv n F 0) := by
  rw [taylor_within_apply]
  simp only [sub_zero, iteratedDerivWithin_univ]
  rw [Finset.sum_eq_single n]
  · rw [smul_smul, mul_comm]
  · intro j hj hjn
    have hj' : j < n := by have := Finset.mem_range.mp hj; omega
    rw [h j hj', smul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- A monomial `t ↦ t ^ n • a` that is little-o of `t ^ n` at zero has coefficient `a = 0`. -/
theorem trotter_monomial_littleO_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (n : ℕ) (h : (fun t : ℝ => t^n • a) =o[𝓝 0] (fun t : ℝ => t^n)) : a = 0 := by
  by_contra ha
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using! ht
  obtain ⟨t, ht, hb⟩ := (hne.and ((h.bound (by positivity : 0 < ‖a‖/2)).filter_mono
    nhdsWithin_le_nhds)).exists
  have ht0 : 0 < ‖t^n‖ := norm_pos_iff.mpr (pow_ne_zero n ht)
  rw [norm_smul] at hb
  have hh : ‖a‖ ≤ ‖a‖/2 := (mul_le_mul_iff_right₀ ht0).mp (by simpa only [mul_comm] using! hb)
  linarith

/-- For an infinitely differentiable function, order `p + 1` at zero is equivalent to vanishing
derivatives of all orders at most `p`. -/
theorem trotter_smooth_order_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    trotterOrder F (p+1) ↔ ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0 := by
  rw [trotterOrder_iff_isBigO]
  constructor
  · intro hO j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      let a := (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
      have ht : ∀ t, taylorWithinEval F j Set.univ 0 t = t^j • a :=
        trotter_taylor_leading F j (fun k hk => ih k hk (by omega))
      have hr : (fun t => F t - t^j • a) =o[𝓝 0] (fun t : ℝ => t^j) := by
        have hh :=
            taylor_isLittleO_univ (x₀ := 0) (hF.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))
        simp only [sub_zero] at hh
        convert! hh using 1
        funext t; rw [ht t]
      have hf : F =o[𝓝 0] (fun t : ℝ => t^j) :=
        hO.trans_isLittleO (isLittleO_pow_pow (by omega : j < p+1))
      have hp : (fun t : ℝ => t^j • a) =o[𝓝 0] (fun t : ℝ => t^j) := by
        convert! hf.sub hr using 1
        funext t; abel
      have ha := trotter_monomial_littleO_zero a j hp
      exact (smul_eq_zero.mp ha).resolve_left (by positivity : (j.factorial : ℝ)⁻¹ ≠ 0)
  · intro hjets
    let a := ((p+1).factorial : ℝ)⁻¹ • iteratedDeriv (p+1) F 0
    have ht : ∀ t, taylorWithinEval F (p+1) Set.univ 0 t = t^(p+1) • a :=
      trotter_taylor_leading F (p+1) (fun j hj => hjets j (by omega))
    have hr : (fun t => F t - t^(p+1) • a) =o[𝓝 0] (fun t : ℝ => t^(p+1)) := by
      have hh := taylor_isLittleO_univ (x₀ := 0)
        (hF.of_le (by exact_mod_cast (le_top : ((p+1 : ℕ) : ℕ∞) ≤ ⊤)))
      simp only [sub_zero] at hh
      convert! hh using 1
      funext t; rw [ht t]
    have hp : (fun t : ℝ => t^(p+1) • a) =O[𝓝 0] (fun t : ℝ => t^(p+1)) := by
      apply IsBigO.of_bound ‖a‖
      exact Eventually.of_forall (fun t => by rw [norm_smul, mul_comm])
    convert! hr.isBigO.add hp using 1
    funext t; abel

/-- A smooth matrix function is bounded near zero by a constant times `|t| ^ (p + 1)` exactly
when its jets through order `p` vanish [ChildsEtAl2021Trotter]. -/
theorem smooth_matrix_order_iff_zero_jets :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (F : ℝ → Matrix I I ℂ)
      (p : ℕ), ContDiff ℝ ∞ F →
      ((∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ ∀ t : ℝ, |t| ≤ t₀ →
        ‖F t‖ ≤ c*|t|^(p+1)) ↔
        ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0) := by
  intro I _ _ F p hF
  exact trotter_smooth_order_iff F p hF

/-- A smooth matrix function has order `n` exactly when all of its derivatives at zero of orders
below `n` vanish. -/
theorem trotter_matrix_order_jets {I : Type} [Fintype I] [DecidableEq I]
    (F : ℝ → Matrix I I ℂ) (n : ℕ) (hF : ContDiff ℝ ∞ F) :
    trotterOrder F n ↔ ∀ j : ℕ, j < n → iteratedDeriv j F 0 = 0 := by
  cases n with
  | zero =>
    constructor
    · intro _ j hj; omega
    · intro _
      rw [trotterOrder_iff_isBigO]
      simpa only [pow_zero] using! hF.continuous.continuousAt.tendsto.isBigO_one ℝ
  | succ n =>
    simpa only [Nat.lt_succ_iff] using! smooth_matrix_order_iff_zero_jets I F n hF

/-- The matrix exponential curve `t ↦ exp (t • H)` is infinitely differentiable over `ℝ`. -/
theorem trotter_exp_contDiff {I : Type} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp (t • H)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) (t • H)).contDiffAt.comp t
    ((contDiff_id.smul contDiff_const).contDiffAt)

/-- The `n`th derivative at zero of `t ↦ exp (t • H)` is `H ^ n`. -/
theorem trotter_exp_jets {I : Type} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => NormedSpace.exp (t • H)) 0 = H^n := by
  have hd : deriv (fun t : ℝ => NormedSpace.exp (t • H)) =
      (fun t : ℝ => H * NormedSpace.exp (t • H)) := by
    funext t
    exact (hasDerivAt_exp_smul_const' H t).deriv
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul H
      ((trotter_exp_contDiff H).contDiffAt.of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))), ih, pow_succ']

/-- Multiplying on the left by the ring inverse of a matrix curve continuous at zero with value
one preserves and reflects local order. -/
theorem trotter_order_inverse_left {I : Type} [Fintype I] [DecidableEq I]
    (S F : ℝ → Matrix I I ℂ) (n : ℕ) (hSc : ContinuousAt S 0) (hS0 : S 0 = 1) :
    trotterOrder F n ↔ trotterOrder (fun t => Ring.inverse (S t)*F t) n := by
  have hunit : ∀ᶠ t in 𝓝 0, IsUnit (S t) :=
    hSc.tendsto.eventually (Units.isOpen.mem_nhds (by rw [hS0]; exact isUnit_one))
  have hi : ContinuousAt Ring.inverse (S 0) := by
    rw [hS0]
    exact (contDiffAt_ringInverse ℝ (n := 0) (1 : (Matrix I I ℂ)ˣ)).continuousAt
  have hb := (hi.comp hSc).tendsto.isBigO_one ℝ
  have hs := hSc.tendsto.isBigO_one ℝ
  simp only [trotterOrder_iff_isBigO]
  constructor
  · intro h
    simpa only [one_mul] using! hb.mul h
  · intro h
    have hh : (fun t => S t*(Ring.inverse (S t)*F t)) =O[𝓝 0] (fun t : ℝ => t^n) := by
      simpa only [one_mul] using! hs.mul h
    apply hh.congr' _ EventuallyEq.rfl
    filter_upwards [hunit] with t ht
    exact Ring.mul_inverse_cancel_left (S t) (F t) ht

/-- Multiplying on the right by the ring inverse of a matrix curve continuous at zero with value
one preserves and reflects local order. -/
theorem trotter_order_inverse_right {I : Type} [Fintype I] [DecidableEq I]
    (S F : ℝ → Matrix I I ℂ) (n : ℕ) (hSc : ContinuousAt S 0) (hS0 : S 0 = 1) :
    trotterOrder F n ↔ trotterOrder (fun t => F t*Ring.inverse (S t)) n := by
  have hunit : ∀ᶠ t in 𝓝 0, IsUnit (S t) :=
    hSc.tendsto.eventually (Units.isOpen.mem_nhds (by rw [hS0]; exact isUnit_one))
  have hi : ContinuousAt Ring.inverse (S 0) := by
    rw [hS0]
    exact (contDiffAt_ringInverse ℝ (n := 0) (1 : (Matrix I I ℂ)ˣ)).continuousAt
  have hb := (hi.comp hSc).tendsto.isBigO_one ℝ
  have hs := hSc.tendsto.isBigO_one ℝ
  simp only [trotterOrder_iff_isBigO]
  constructor
  · intro h
    simpa only [mul_one] using! h.mul hb
  · intro h
    have hh : (fun t => (F t*Ring.inverse (S t))*S t) =O[𝓝 0] (fun t : ℝ => t^n) := by
      simpa only [mul_one] using! h.mul hs
    apply hh.congr' _ EventuallyEq.rfl
    filter_upwards [hunit] with t ht
    exact Ring.inverse_mul_cancel_right (S t) (F t) ht

/-- For smooth `S` with `S 0 = 1`, additive error order `p + 1`, both inverse-normalized
differential defect orders `p`, and multiplicative error order `p + 1` are equivalent
[Childs et al., Theorem 9][ChildsEtAl2021Trotter]. -/
theorem general_trotter_four_order_conditions :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (H : Matrix I I ℂ)
      (S : ℝ → Matrix I I ℂ) (p : ℕ), ContDiff ℝ ∞ S → S 0 = 1 →
      let D := fun t => deriv S t - H*S t
      let T := fun t => Ring.inverse (S t)*D t
      let E := fun t => D t*Ring.inverse (S t)
      let M := fun t => NormedSpace.exp ((-t) • H)*S t - 1
      let O := fun (F : ℝ → Matrix I I ℂ) (n : ℕ) =>
        ∃ c t₀ : ℝ, 0 < c ∧ 0 < t₀ ∧ ∀ t : ℝ, |t| ≤ t₀ → ‖F t‖ ≤ c*|t|^n
      (O (fun t => S t - NormedSpace.exp (t • H)) (p+1) ↔ O T p) ∧
      (O T p ↔ O E p) ∧ (O E p ↔ O M (p+1)) := by
  intro I _ _ H S p hS hS0
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _
  let P := fun t : ℝ => NormedSpace.exp (t • H)
  let A := fun t : ℝ => S t-P t
  let D := fun t : ℝ => deriv S t-H*S t
  have hP : ContDiff ℝ ∞ P := trotter_exp_contDiff H
  have hA : ContDiff ℝ ∞ A := hS.sub hP
  have hdS : ContDiff ℝ ∞ (deriv S) := (contDiff_infty_iff_deriv.mp hS).2
  have hD : ContDiff ℝ ∞ D := hdS.sub (contDiff_const.mul hS)
  have hjetA (j : ℕ) : iteratedDeriv j A 0 = iteratedDeriv j S 0-H^j := by
    rw [iteratedDeriv_fun_sub (hS.contDiffAt.of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))) (hP.contDiffAt.of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))), trotter_exp_jets]
  have hjetD (j : ℕ) : iteratedDeriv j D 0 = iteratedDeriv (j+1) S 0-H*iteratedDeriv j S 0 := by
    rw [iteratedDeriv_fun_sub (hdS.contDiffAt.of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))) ((contDiff_const.mul hS).contDiffAt.of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))), ← iteratedDeriv_succ',
      iteratedDeriv_const_mul H (hS.contDiffAt.of_le
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
  have hAD : trotterOrder A (p+1) ↔ trotterOrder D p := by
    rw [trotter_matrix_order_jets A _ hA, trotter_matrix_order_jets D _ hD]
    constructor
    · intro h j hj
      rw [hjetD, sub_eq_zero]
      have h₁ := h j (by omega)
      have h₂ := h (j+1) (by omega)
      rw [hjetA, sub_eq_zero] at h₁ h₂
      rw [h₁, h₂, pow_succ']
    · intro h j hj
      have hsjet : ∀ n : ℕ, n ≤ p → iteratedDeriv n S 0 = H^n := by
        intro n
        induction n with
        | zero => intro _; simpa using! hS0
        | succ n ih =>
          intro hn
          have hd := h n (by omega)
          rw [hjetD, sub_eq_zero, ih (by omega)] at hd
          simpa only [pow_succ'] using! hd
      rw [hjetA, hsjet j (by omega), sub_self]
  have hDT := trotter_order_inverse_left S D p hS.continuous.continuousAt hS0
  have hDE := trotter_order_inverse_right S D p hS.continuous.continuousAt hS0
  have hAM : trotterOrder A (p+1) ↔
      trotterOrder (fun t => NormedSpace.exp ((-t) • H)*S t-1) (p+1) := by
    have hh := trotter_order_inverse_left P A (p+1) hP.continuous.continuousAt (by simp [P])
    convert! hh using 2
    funext t
    dsimp [P, A]
    rw [mul_sub, Ring.inverse_mul_cancel _ (NormedSpace.isUnit_exp _), Ring.inverse_exp, neg_smul]
  change (trotterOrder A (p+1) ↔ trotterOrder (fun t => Ring.inverse (S t)*D t) p) ∧
    (trotterOrder (fun t => Ring.inverse (S t)*D t) p ↔ trotterOrder (fun t => D t*Ring.inverse (S t)) p) ∧
    (trotterOrder (fun t => D t*Ring.inverse (S t)) p ↔
      trotterOrder (fun t => NormedSpace.exp ((-t) • H)*S t-1) (p+1))
  exact ⟨hAD.trans hDT, hDT.symm.trans hDE, hDE.symm.trans (hAD.symm.trans hAM)⟩

end Qatlib.Concepts.TrotterFormula.GeneralOrder
