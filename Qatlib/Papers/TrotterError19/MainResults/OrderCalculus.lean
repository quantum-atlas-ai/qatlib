/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterError19.MainResults.Appendices.AppendixB
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Differentiation and integration of order conditions

Rules 3 and 4 of Proposition B.3 in arXiv:1912.08854v3 use a shift of
the Taylor jets at zero. Prove the shifts with the finite differentiability
orders required by the Taylor and fundamental theorems of calculus.
-/

set_option autoImplicit false

noncomputable section

open Asymptotics Filter
open scoped ContDiff Topology
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Papers.TrotterError19.MainResults

namespace Qatlib.Papers.TrotterError19.MainResults

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite `C^p` regularity suffices for the order-`p` Taylor jet criterion. -/
theorem finite_order_jets (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ (p : ℕ∞ω) F) :
    OrderCondition F p ↔ ∀ j : ℕ, j < p → iteratedDeriv j F 0 = 0 := by
  change trotterOrder F p ↔ _
  rw [trotterOrder_iff_isBigO]
  constructor
  · intro hO j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hj
        let a := (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
        have ht (t : ℝ) : taylorWithinEval F j Set.univ 0 t = t ^ j • a :=
          trotter_taylor_leading F j (fun k hk => ih k hk (hk.trans hj)) t
        have hFj : ContDiff ℝ (j : ℕ∞ω) F := hF.of_le (by exact_mod_cast hj.le)
        have hr : (fun t => F t - t ^ j • a) =o[𝓝 0] (fun t : ℝ => t ^ j) := by
          have h := taylor_isLittleO_univ (x₀ := 0) hFj
          simpa only [sub_zero, ht] using h
        have hf : F =o[𝓝 0] (fun t : ℝ => t ^ j) :=
          hO.trans_isLittleO (isLittleO_pow_pow hj)
        have hm : (fun t : ℝ => t ^ j • a) =o[𝓝 0] (fun t : ℝ => t ^ j) := by
          convert! hf.sub hr using 1
          funext t
          abel
        have ha := trotter_monomial_littleO_zero a j hm
        exact (smul_eq_zero.mp ha).resolve_left (by positivity : (j.factorial : ℝ)⁻¹ ≠ 0)
  · intro hjets
    let a := (p.factorial : ℝ)⁻¹ • iteratedDeriv p F 0
    have ht (t : ℝ) : taylorWithinEval F p Set.univ 0 t = t ^ p • a :=
      trotter_taylor_leading F p hjets t
    have hr : (fun t => F t - t ^ p • a) =o[𝓝 0] (fun t : ℝ => t ^ p) := by
      simpa only [sub_zero, ht] using taylor_isLittleO_univ (x₀ := 0) hF
    have hm : (fun t : ℝ => t ^ p • a) =O[𝓝 0] (fun t : ℝ => t ^ p) := by
      apply IsBigO.of_bound ‖a‖
      exact Eventually.of_forall (fun t => by rw [norm_smul, mul_comm])
    convert! hr.isBigO.add hm using 1
    funext t
    abel

/-- Proposition B.3 rule 3, with `C^(p+1)` regularity. -/
theorem propB3_differentiation (F : ℝ → E) (p : ℕ)
    (hF : ContDiff ℝ ((p : ℕ∞ω) + 1) F) :
    OrderCondition F (p + 1) ↔ F 0 = 0 ∧ OrderCondition (deriv F) p := by
  have hd : ContDiff ℝ (p : ℕ∞ω) (deriv F) := hF.deriv'
  have hFc : ContDiff ℝ ((p + 1 : ℕ) : ℕ∞ω) F := by simpa using hF
  rw [finite_order_jets F (p + 1) hFc, finite_order_jets (deriv F) p hd]
  constructor
  · intro h
    refine ⟨h 0 (by omega), fun j hj => ?_⟩
    simpa only [iteratedDeriv_succ'] using h (j + 1) (by omega)
  · rintro ⟨h0, hdj⟩ j hj
    cases j with
    | zero => exact h0
    | succ j => simpa only [iteratedDeriv_succ'] using hdj j (by omega)

/-- Proposition B.3 rule 4, with `C^p` regularity of the integrand. -/
theorem propB3_integration [CompleteSpace E] (F : ℝ → E) (p : ℕ)
    (hF : ContDiff ℝ (p : ℕ∞ω) F) :
    OrderCondition F p ↔ OrderCondition (fun t => ∫ τ in (0 : ℝ)..t, F τ) (p + 1) := by
  let G : ℝ → E := fun t => ∫ τ in (0 : ℝ)..t, F τ
  have hd : deriv G = F := funext (fun t => Continuous.deriv_integral F hF.continuous 0 t)
  have hG : ContDiff ℝ ((p : ℕ∞ω) + 1) G := by
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun t => (hF.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt.differentiableAt,
      by simp, ?_⟩
    rwa [hd]
  change OrderCondition F p ↔ OrderCondition G (p + 1)
  rw [propB3_differentiation G p hG, hd]
  simp [G]

end Qatlib.Papers.TrotterError19.MainResults
