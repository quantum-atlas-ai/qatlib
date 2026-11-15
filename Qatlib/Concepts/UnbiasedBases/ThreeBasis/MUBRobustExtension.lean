/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MutuallyUnbiased
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis
open scoped BigOperators

abbrev BasisArray (k d : ℕ) := Fin k → Fin d → QState (Fin d)
variable {k d : ℕ}

def IsCommonUnbiased (B : BasisArray k d) (ψ : QState (Fin d)) : Prop :=
  ∀ r j, Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B r j) ψ) = (1 : ℝ) / d

noncomputable def commonResidual (B : BasisArray k d) (ψ : QState (Fin d)) : ℝ :=
  ∑ r : Fin k, ∑ j : Fin d,
    (Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B r j) ψ) - (1 : ℝ) / d) ^ 2

/-- The common unbiasedness residual is nonnegative. -/
theorem commonResidual_nonneg (B : BasisArray k d) (ψ : QState (Fin d)) :
    0 ≤ commonResidual B ψ := by
  apply Finset.sum_nonneg
  intro r _
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- The common residual vanishes exactly for a common unbiased vector. -/
theorem commonResidual_eq_zero_iff (B : BasisArray k d) (ψ : QState (Fin d)) :
    commonResidual B ψ = 0 ↔ IsCommonUnbiased B ψ := by
  constructor
  · intro h r j
    have hr : (∑ j : Fin d,
        (Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B r j) ψ) - (1 : ℝ) / d) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mp h r (Finset.mem_univ _)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp
      hr j (Finset.mem_univ _)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hj)
  · intro h
    change ∀ r j, Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (B r j) ψ) =
        (1 : ℝ) / d at h
    simp [commonResidual, h]

/-- The common residual is positive for any vector that is not common unbiased. -/
theorem commonResidual_pos (B : BasisArray k d) (ψ : QState (Fin d))
    (h : ¬ IsCommonUnbiased B ψ) : 0 < commonResidual B ψ := by
  have hn := commonResidual_nonneg B ψ
  have hne : commonResidual B ψ ≠ 0 := (commonResidual_eq_zero_iff B ψ).not.mpr h
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- The common residual is jointly continuous in the basis array and the vector. -/
theorem continuous_commonResidual :
    Continuous (fun p : BasisArray k d × QState (Fin d) => commonResidual p.1 p.2) := by
  unfold commonResidual
  simp only [inner_apply]
  fun_prop

/-- On a nonempty compact set with no common unbiased vector, the common residual has a uniform
positive lower bound. -/
theorem commonResidual_uniform_gap (B : BasisArray k d)
    (S : Set (QState (Fin d))) (hS : IsCompact S) (hne : S.Nonempty)
    (hno : ∀ ψ ∈ S, ¬ IsCommonUnbiased B ψ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ψ ∈ S, ε ≤ commonResidual B ψ := by
  have hc : Continuous (commonResidual B) := by
    unfold commonResidual
    simp only [inner_apply]
    fun_prop
  obtain ⟨ψ, hψ, hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
  exact ⟨commonResidual B ψ, commonResidual_pos B ψ (hno ψ hψ),
    fun φ hφ => hmin hφ⟩

/-- Absence of common unbiased vectors on a compact set persists under sufficiently small
perturbations of the basis array. -/
theorem no_commonUnbiased_stable_on_compact (B : BasisArray k d)
    (S : Set (QState (Fin d))) (hS : IsCompact S)
    (hno : ∀ ψ ∈ S, ¬ IsCommonUnbiased B ψ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ C : BasisArray k d,
      dist C B < δ → ∀ ψ ∈ S, ¬ IsCommonUnbiased C ψ := by
  let N : Set (BasisArray k d × QState (Fin d)) :=
    {p | 0 < commonResidual p.1 p.2}
  have hN : IsOpen N := by
    exact isOpen_lt (continuous_const : Continuous (fun _ : BasisArray k d × QState (Fin d) => (0 : ℝ)))
      (continuous_commonResidual (k := k) (d := d))

  have hprod : ({B} : Set (BasisArray k d)) ×ˢ S ⊆ N := by
    rintro ⟨C, ψ⟩ ⟨hC, hψ⟩
    have hCB : C = B := Set.mem_singleton_iff.mp hC
    subst C
    exact commonResidual_pos B ψ (hno ψ hψ)
  obtain ⟨U, V, hU, _, hBU, hSV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hS hN hprod
  have hBU' : B ∈ U := hBU (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU B hBU'
  refine ⟨δ, hδ, ?_⟩
  intro C hC ψ hψ hcommon
  have hCU : C ∈ U := @hball C (Metric.mem_ball.mpr hC)
  have hp : 0 < commonResidual C ψ := @hUV (C, ψ) ⟨hCU, hSV hψ⟩
  rw [(commonResidual_eq_zero_iff C ψ).mpr hcommon] at hp
  exact (lt_irrefl 0) hp

/-- Every normalized state lies in the closed unit ball centered at zero. -/
theorem normalized_mem_unit_closedBall (ψ : QState (Fin d)) (hψ : Normalized ψ) :
    ψ ∈ Metric.closedBall (0 : QState (Fin d)) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  intro i
  have hs : ‖ψ i‖ ^ 2 ≤ ∑ j : Fin d, ‖ψ j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j‖) (Finset.mem_univ i)
  have hsum : (∑ j : Fin d, ‖ψ j‖ ^ 2) = 1 := hψ
  rw [hsum] at hs
  nlinarith [norm_nonneg (ψ i)]

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
