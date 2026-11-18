/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux

@[expose] public section


/-! # Entropy inequalities in the actual density-matrix model

These are finite-dimensional entropy, conditional entropy, mutual information,
and strong subadditivity targets of arXiv:1106.1445v8.
All marginal conversions are explicit.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.QEntropy

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open scoped ComplexOrder

/-- Entropy is subadditive for the actual density and its partial traces. -/
theorem entropy_le_sum_marginal_entropies
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) :
    entropy ρ ≤ entropy (marginR ρ) + entropy (marginL ρ) := by
  simpa [entropy, marginR, marginL] using Sᵥₙ_subadditivity (state ρ)

/-- Conditioning does not increase entropy in the density-matrix model. -/
theorem Hcond_le_entropy_marginR
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : Hcond ρ ≤ entropy (marginR ρ) := by
  unfold Hcond
  linarith [entropy_le_sum_marginal_entropies ρ]

/-- Mutual information of a finite bipartite density is nonnegative. -/
theorem mutualInfo_nonneg
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : 0 ≤ mutualInfo ρ := by
  unfold mutualInfo
  linarith [entropy_le_sum_marginal_entropies ρ]

/-- Strong subadditivity, with the conditioning system in the middle. -/
theorem entropy_strong_subadditivity
    {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ρ : Dens (A × C × B)) :
    entropy ρ + entropy (localState (state ρ).traceLeft.traceRight) ≤
      entropy (localState (state ρ).assoc'.traceRight) +
        entropy (localState (state ρ).traceLeft) := by
  simpa [entropy] using Sᵥₙ_strong_subadditivity (state ρ)

/-- Conditional quantum mutual information is nonnegative. -/
theorem cmi_nonneg
    {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ρ : Dens (A × C × B)) : 0 ≤ cmi ρ := by
  unfold cmi
  linarith [entropy_strong_subadditivity ρ]

/-- The magnitude of conditional entropy is bounded by the first dimension. -/
theorem abs_Hcond_le_log_card
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Dens (A × B)) : |Hcond ρ| ≤ Real.log (Fintype.card A) := by
  have hu := Sᵥₙ_le_log_d (state ρ).traceRight
  simp only [Finset.card_univ] at hu
  have hl := Sᵥₙ_triangle_subaddivity (state ρ)
  have hn := Sᵥₙ_nonneg (state ρ).traceRight
  have hs := Sᵥₙ_subadditivity (state ρ)
  simp only [abs_sub_le_iff] at hl
  rw [abs_le]
  simp only [Hcond, entropy, marginL, state_localState]
  constructor <;> linarith [hl.1, hl.2]

/-- Ordered trace-one densities are equal; the order restriction is essential. -/
theorem relEnt_le_of_posSemidef_sub_densities {d : ℕ} (ρ σ σ' : Dens (Fin d))
    (h : (σ'.val - σ.val).PosSemidef) : relEnt ρ σ' ≤ relEnt ρ σ := by
  have ht : Matrix.trace (σ'.val - σ.val) = 0 := by
    rw [Matrix.trace_sub, σ'.property.2, σ.property.2, sub_self]
  have heq : σ' = σ := Subtype.ext (sub_eq_zero.mp (h.trace_eq_zero_iff.mp ht))
  rw [heq]

/-- Every extended quantum relative entropy has a nonnegative real projection.
The old equality characterization additionally needs a finiteness assumption. -/
theorem projected_relative_nonneg {d : ℕ} (ρ σ : Dens (Fin d)) : 0 ≤ relEntR ρ σ := by
  exact ENNReal.toReal_nonneg

end Qatlib.Papers.QShannonWilde11.MainResults.QEntropy
