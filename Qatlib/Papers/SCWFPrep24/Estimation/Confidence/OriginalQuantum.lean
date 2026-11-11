/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorBasis

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Original Quantum

Every actual prior point supplies Q copies of one original physical spinor, with its fixed sign field and one fixed local phase assignment.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorBasis
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhaseLaw
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

/-- Every actual prior point supplies Q copies of one original physical spinor, with its fixed sign field and one fixed local phase assignment. -/
def originalInput (d N : ℕ) (h4 : 4∣N) (b : ℝ) (Q : ℕ)
    (z : (PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1))) :
    QState (Fin Q → (Fin (d+1) → Fin N) × Bool) :=
  originalSuppliedCopies (fun a => pairedWeakSpin b z.1 (GridMatching.originalGrid d N h4 a)) Q z.2

/-- Normalization of every actual original input follows from its internal pointwise weak spins, including Q zero. -/
theorem originalInput_normalized (d N : ℕ) [NeZero N] (h4 : 4∣N) (b : ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (Q : ℕ)
    (z : (PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1))) :
    Normalized (originalInput d N h4 b Q z) := by
  apply originalSuppliedCopies_normalized
  exact weak_qubit_mass b (fun a => siteSign z.1 (GridMatching.originalGrid d N h4 a)) hb0 hb1
    (fun a => siteSign_unit z.1 (GridMatching.originalGrid d N h4 a))

/-- The same true original physical input prior has exactly the literal sign/shared-phase mixture entries. -/
theorem original_prior_input_entry (d N : ℕ) (h4 : 4∣N) (b ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) (Q : ℕ)
    (x y : Fin Q → (Fin (d+1) → Fin N) × Bool) :
    priorOnGrid (GridMatching.originalGrid d N h4) b ρ Q x y=
      ∑ z,((originalPriorLaw d N ρ hlo hhi Q).prob z : ℂ)*originalInput d N h4 b Q z x*
        star (originalInput d N h4 b Q z y) := by
  simp only [priorOnGrid,phaseMean_eq_real_law,Fintype.sum_prod_type,originalPriorLaw,finitePairLaw,
    originalInput,Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- The one known full finite basis names every original Q-copy coordinate and is independent of all hidden signs, phases and hypotheses. -/
def originalFiniteBasis (d N : ℕ) (h4 : 4∣N) (Q : ℕ) :
    Fin (Fintype.card (Fin Q → (PairLabels d N × Bool) × Bool)) ≃
      (Fin Q → (Fin (d+1) → Fin N) × Bool) :=
  (Fintype.equivFin (Fin Q → (PairLabels d N × Bool) × Bool)).symm.trans
    (copyBasisEquiv (GridMatching.originalGrid d N h4) Q).symm

/-- The actual complete original input vector in the same one known finite coordinate basis. -/
def encodedOriginalInput (d N : ℕ) (h4 : 4∣N) (b : ℝ) (Q : ℕ)
    (z : (PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1))) :
    QState (Fin (Fintype.card (Fin Q → (PairLabels d N × Bool) × Bool))) :=
  fun i => originalInput d N h4 b Q z (originalFiniteBasis d N h4 Q i)

/-- Naming every complete original coordinate by a known bijection preserves the actual physical normalization. -/
theorem encodedOriginalInput_normalized (d N : ℕ) [NeZero N] (h4 : 4∣N) (b : ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (Q : ℕ)
    (z : (PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1))) :
    Normalized (encodedOriginalInput d N h4 b Q z) := by
  have hn := originalInput_normalized d N h4 b hb0 hb1 Q z
  exact (Equiv.sum_comp (originalFiniteBasis d N h4 Q) (fun x => ‖originalInput d N h4 b Q z x‖^2)).trans hn

/-- The full quantum prior and the true physical sign/shared-phase input law are the same mixture of the same complete original vectors. -/
theorem original_quantum_prior_mixture (d N : ℕ) (h4 : 4∣N) (b ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) (Q : ℕ) :
    encodedGridPrior (GridMatching.originalGrid d N h4) b ρ Q=
      ∑ z,((originalPriorLaw d N ρ hlo hhi Q).prob z : ℂ) • outerProduct (encodedOriginalInput d N h4 b Q z) := by
  ext i j
  simp only [encodedGridPrior,Matrix.submatrix_apply,Function.comp_apply,original_prior_input_entry d N h4 b ρ hlo hhi Q,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,outerProduct,Matrix.of_apply,encodedOriginalInput,
    originalFiniteBasis,Equiv.trans_apply]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Complex.star_def]
  ring

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorBasis

/-- The full original-grid priors obey the exact source squared-fidelity lower bound with the original M equal to N to the physical dimension. -/
theorem original_physical_full_fidelity (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (Q : ℕ) :
    Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
      min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/(N^(d+1) : ℕ)))≤
    (Qatlib.Concepts.MixedFidelity.FidelityMetric.Froot
      (encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (3/4) Q)
      (encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) (-3/4) Q))^2 := by
  have hK := GridMatching.original_block_range N hN h4
  let : NeZero (N/4) := ⟨by omega⟩
  have hf := original_grid_full_fidelity (GridMatching.originalGrid d N h4) N Q hN
  simpa only [Fintype.card_fun,Fintype.card_fin] using hf

/-- Both true original physical priors are legal complete input density operators, with no positivity, trace or fidelity certificate supplied by the consumer. -/
theorem original_physical_prior_legal (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) (Q : ℕ) :
    Qatlib.Foundations.PureStateMath.IsDensityOperator
      (encodedGridPrior (GridMatching.originalGrid d N h4) (128/((N : ℝ)^2)) ρ Q) := by
  have hK := GridMatching.original_block_range N hN h4
  let : NeZero (N/4) := ⟨by omega⟩
  have hb := original_weak_excitation N hN
  exact encodedGridPrior_legal (GridMatching.originalGrid d N h4) _ ρ Q hb.1 (by linarith [hb.2]) hlo hhi

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
