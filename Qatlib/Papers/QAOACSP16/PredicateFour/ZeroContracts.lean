/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOACSP16.TypicalQaoa.XorSupport
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Nonempty zero-objective counterexamples to legacy strict QAOA advantage contracts.

The witnesses have one variable, one nonempty singleton scope, and the genuine
uniform Boolean coefficient law. Every coefficient and objective value is zero.
The complete legacy contracts are negated at these concrete finite types.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPModel
open Qatlib.Papers.QAOACSP16.PredicateFour.CSPFamily
open Qatlib.Papers.QAOACSP16.TypicalQaoa.QaoaState
open Qatlib.Papers.QAOACSP16.TypicalQaoa.XorSupport
open scoped BigOperators

namespace Qatlib.Papers.QAOACSP16.PredicateFour.ZeroContracts

/-- One nonempty XOR constraint with a uniform sign register and identically zero coefficients. -/
def zeroXor : XorFamily (Fin 1) Bool where
  m := 1
  hm := by decide
  scope := fun _ => {(0 : Fin 1)}
  scope_nonempty := fun _ => Finset.singleton_nonempty _
  coeff := fun _ _ => 0
  law := uniformBool
  coeff_zero_mean := by
    intro l
    simp [FinDist.expect]
  varBound := 0
  coeff_var_le := by
    intro l
    simp [FinDist.variance, FinDist.expect]

/-- The witness has arity at most one, with a genuinely nonempty scope. -/
theorem zero_xor_arity : zeroXor.toFamily.BoundedArity 1 := by
  intro l
  simp [zeroXor, XorFamily.toFamily]

/-- The single constraint gives a degree bound of one. -/
theorem zero_xor_degree : zeroXor.toFamily.BoundedDegree 1 := by
  intro v
  have hcard : (Finset.univ : Finset (Fin zeroXor.m)).card = 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (show zeroXor.m = 1 from rfl)
  exact (Finset.card_filter_le _ _).trans hcard.le

/-- Every angle choice and coefficient draw has zero QAOA expected objective. -/
theorem zero_xor_value (ω : Fin zeroXor.toFamily.m → Bool) (γ β : ℝ) :
    qaoaExpectedValue (zeroXor.toFamily.instance ω) γ β = 0 := by
  simp [qaoaExpectedValue, satValue, CSPFamily.instance, sampledInstance,
    XorFamily.toFamily, XorFamily.pred, zeroXor]

/-- Averaging the zero objective under the actual independent instance law still gives zero. -/
theorem zero_xor_mean (γ β : ℝ) :
    zeroXor.toFamily.instanceLaw.expect
      (fun ω => qaoaExpectedValue (zeroXor.toFamily.instance ω) γ β) = 0 := by
  simp [FinDist.expect, zero_xor_value]

/-- the stated model fails as a complete universally quantified contract, even on one variable. -/
theorem xor_expectation_contract_false :
    ¬ (∀ (F : XorFamily (Fin 1) Bool) (k : ℕ),
      0 ≤ F.varBound → F.toFamily.BoundedArity k →
      ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 0 < D → F.toFamily.BoundedDegree D →
        ∃ γ β : ℝ,
          c * (F.m : ℝ) / Real.sqrt (D : ℝ) ≤
            F.toFamily.instanceLaw.expect
              (fun ω => qaoaExpectedValue (F.toFamily.instance ω) γ β)) := by
  intro h
  obtain ⟨c, hc, hD⟩ := h zeroXor 1 (by norm_num [zeroXor]) zero_xor_arity
  obtain ⟨γ, β, hbound⟩ := hD 1 (by decide) zero_xor_degree
  rw [zero_xor_mean γ β] at hbound
  norm_num [zeroXor] at hbound
  exact (not_le_of_gt hc) hbound

/-- The zero predicates satisfy the actual Boolean-range assumption. -/
theorem zero_xor_boolean : zeroXor.toFamily.BooleanValues := by
  intro l p z
  simp [XorFamily.toFamily, XorFamily.pred, zeroXor]

/-- the stated model fails with all typicality, arity and Boolean-range hypotheses satisfied. -/
theorem typical_expectation_contract_false :
    ¬ (∀ (F : CSPFamily (Fin 1) Bool) (k : ℕ),
      F.Typical → F.BoundedArity k → F.BooleanValues →
      ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 0 < D → F.BoundedDegree D →
        ∃ γ β : ℝ,
          F.muFamily * (F.m : ℝ) + c * (F.m : ℝ) / Real.sqrt (D : ℝ) ≤
              F.instanceLaw.expect (fun ω => qaoaExpectedValue (F.instance ω) γ β) ∧
            F.instanceLaw.variance (fun ω => qaoaExpectedValue (F.instance ω) γ β) ≤
              (F.m : ℝ) *
                ((k : ℝ) * ((k : ℝ) - 1) * (D : ℝ) + (k : ℝ)) *
                  ((D : ℝ) + 1)) := by
  intro h
  obtain ⟨c, hc, hD⟩ := h zeroXor.toFamily 1
    (XorFamily.toFamily_typical zeroXor) zero_xor_arity zero_xor_boolean
  obtain ⟨γ, β, hmean, _hvariance⟩ := hD 1 (by decide) zero_xor_degree
  rw [XorFamily.muFamily_eq_zero zeroXor, zero_xor_mean γ β] at hmean
  norm_num [zeroXor, XorFamily.toFamily] at hmean
  exact (not_le_of_gt hc) hmean

/-- A concrete sampled instance of the same one-constraint zero family. -/
def zeroInstance : CSPInstance (Fin 1) :=
  zeroXor.toFamily.instance (fun _ => false)

/-- A single-constraint instance has no pair of distinct overlapping constraints. -/
theorem zero_instance_no_overlap : NoOverlapping zeroInstance := by
  intro l l' hne
  have hm : zeroInstance.m = 1 := rfl
  let : Subsingleton (Fin zeroInstance.m) := by
    rw [hm]
    infer_instance
  exact (hne (Subsingleton.elim l l')).elim

/-- The concrete zero instance has degree at most one. -/
theorem zero_instance_degree : BoundedDegree zeroInstance 1 := by
  intro v
  have hcard : (Finset.univ : Finset (Fin zeroInstance.m)).card = 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (show zeroInstance.m = 1 from rfl)
  exact (Finset.card_filter_le _ _).trans hcard.le

/-- The uniform-assignment baseline of the zero instance is zero. -/
theorem zero_instance_mu : mu zeroInstance = 0 := by
  simp [mu, constraintMean, uniformExpect, zeroInstance, CSPFamily.instance,
    sampledInstance, XorFamily.toFamily, XorFamily.pred, zeroXor]

/-- the stated model fails with a nonempty, nonoverlapping, degree-one instance. -/
theorem no_overlap_contract_false :
    ¬ (∀ X : CSPInstance (Fin 1), NoOverlapping X →
      ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 0 < D → BoundedDegree X D →
        ∃ γ β : ℝ,
          mu X * (X.m : ℝ) + c * (X.m : ℝ) / Real.sqrt (D : ℝ) ≤
            qaoaExpectedValue X γ β) := by
  intro h
  obtain ⟨c, hc, hD⟩ := h zeroInstance zero_instance_no_overlap
  obtain ⟨γ, β, hbound⟩ := hD 1 (by decide) zero_instance_degree
  have hvalue : qaoaExpectedValue zeroInstance γ β = 0 :=
    zero_xor_value (fun _ => false) γ β
  rw [zero_instance_mu, hvalue] at hbound
  norm_num [zeroInstance, CSPFamily.instance, sampledInstance,
    XorFamily.toFamily, zeroXor] at hbound
  exact (not_le_of_gt hc) hbound

end Qatlib.Papers.QAOACSP16.PredicateFour.ZeroContracts
