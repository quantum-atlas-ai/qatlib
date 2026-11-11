/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ReferenceModel.LocalRationalPauliQDrift

/-!
# A rational XZ qDRIFT example

This module instantiates the rational Pauli qDRIFT construction with the one-qubit Hamiltonian
`(1/3) X - (2/3) Z`. It computes the dyadic coefficient table and the actual gate count, then
combines simulation, sampling, phase, and coefficient errors in the setting of [Campbell2019].

## Main statements

* `localXZ_dyadic_table`: the weights at precision two are `1` and `3`.
* `localXZ_qdrift_gateCount`: each selected X term adds two gates to the baseline path length.
* `local_rational_xz_qdrift_actual_consumer`: the resulting finite-reference trace norm error
  bound.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false

open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RandCompile.EffectiveInput
open Qatlib.Concepts.RandCompile.FairBitSampling
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.RandCompile.ReferenceModel
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option maxHeartbeats 1000000

/-- The rational coefficient pair `(1/3, -2/3)` for the XZ Hamiltonian example. -/
def localXZCoefficients : Fin 2 → ℚ := ![1/3,-2/3]

/-- The one-qubit Pauli labels selecting X for the first component and Z for the second. -/
def localXZLabels (j : Fin 2) : Fin 1 → Fin 4 := fun _ => if j = 0 then 1 else 3

/-- The labeled one-qubit Pauli strings are respectively `pauliX` and `pauliZ`. -/
theorem localXZ_pauli_matrix (j : Fin 2) :
    pauliStringMatrix 1 (localXZLabels j) = if j = 0 then pauliX else pauliZ := by
  have h0 : (bitVecEquiv 1).symm (0 : Fin 2) (0 : Fin 1) = false := rfl
  have h1 : (bitVecEquiv 1).symm (1 : Fin 2) (0 : Fin 1) = true := rfl
  fin_cases j <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [pauliStringMatrix,localXZLabels,localPauliMatrix,tensorPauliProduct,
      relabelGate,pauliProductDensity,boolEquivFin2,h0,h1,pauliX,pauliZ]

/-- At precision two, the dyadic coefficients are `(1, -3)`, the absolute weights are `(1, 3)`,
and their total is four. -/
theorem localXZ_dyadic_table :
    (∀ j : Fin 2, dyadicCoefficient 2 (localXZCoefficients j) = (![1,-3] : Fin 2 → ℤ) j) ∧
    dyadicWeights 2 localXZCoefficients = (![1,3] : Fin 2 → ℕ) ∧
    weightTotal (dyadicWeights 2 localXZCoefficients) = 4 := by
  constructor
  · intro j
    fin_cases j <;> norm_num [dyadicCoefficient,localXZCoefficients]
  constructor
  · funext j
    fin_cases j <;> norm_num [dyadicWeights,dyadicCoefficient,localXZCoefficients]
  · norm_num [weightTotal,Fin.sum_univ_two,dyadicWeights,dyadicCoefficient,localXZCoefficients]

/-- The X component has gate cost three and the Z component has gate cost one. -/
private theorem localXZ_gateCost (j : Fin 2) :
    localPauliGateCost 1 (localXZLabels j) = 1+2*(if j = 0 then 1 else 0) := by
  fin_cases j <;> decide

/-- An `N`-step XZ path uses `N + 2*c` gates, where `c` is the number of sampled X components. -/
theorem localXZ_qdrift_gateCount (N R k : ℕ) (t : ℚ)
    (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights 2 localXZCoefficients)))) :
    GateCount (reflectionCompile (localPauliQdriftSteps 1 2 N R k localXZCoefficients 0 localXZLabels t ω)) =
      N + 2*(Finset.univ.filter (fun i : Fin N =>
        (fairQdriftPick (dyadicWeights 2 localXZCoefficients) 0 R (ω i)).1 = 0)).card := by
  have hc := (localPauliQdrift_path_gates 1 2 N R k localXZCoefficients 0 localXZLabels t ω).2.2.1
  rw [localXZ_dyadic_table.2.2,if_neg (by decide)] at hc
  rw [hc]
  simp only [localXZ_gateCost]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  congr 1
  congr 1
  exact (Finset.card_filter _ _).symm

/-- For positive `N` and `|2*t/N| ≤ 1`, the XZ implementation has gate count `N+2*c` and
reference trace norm error bounded by `(4*t^2/N + 2*N*(1/2)^R + 2*N*(1/2)^k +
|t|/2)*Matrix.traceNorm X`. -/
theorem local_rational_xz_qdrift_actual_consumer :
    ∀ (N R k r : ℕ) (t : ℚ) (X : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ)
      (ω : Fin N → Fin R → Reg
        (Nat.clog 2 (weightTotal (dyadicWeights 2 (![1/3,-2/3] : Fin 2 → ℚ))))),
      0 < N → |2*t/(N:ℚ)| ≤ 1 →
      let a := (![1/3,-2/3] : Fin 2 → ℚ)
      let v := fun j : Fin 2 => fun _ : Fin 1 => if j = 0 then (1 : Fin 4) else 3
      let gs := localPauliQdriftSteps 1 2 N R k a 0 v t ω
      let c := (Finset.univ.filter (fun i : Fin N =>
        (fairQdriftPick (dyadicWeights 2 a) 0 R (ω i)).1 = 0)).card
      let V := TensorGate (HamiltonianEvolution ((1/3 : ℂ) • pauliX-(2/3 : ℂ) • pauliZ) (t:ℝ))
        (1 : Operator r)
      GateCount (reflectionCompile gs) = N+2*c ∧
      Matrix.traceNorm (localPauliQdriftOutput 1 2 N R k a 0 v t r X-V*X*Vᴴ) ≤
        (4*(t:ℝ)^2/(N:ℝ)+2*N*(1/2:ℝ)^R+2*N*(1/2:ℝ)^k+|(t:ℝ)|/2)*Matrix.traceNorm X := by
  intro N R k r t X ω hN ht
  (try dsimp only)
  refine ⟨localXZ_qdrift_gateCount N R k t ω,?_⟩
  have hW : 0 < weightTotal (dyadicWeights 2 localXZCoefficients) := by
    rw [localXZ_dyadic_table.2.2]
    decide
  have ha : (∑ j : Fin 2, |(localXZCoefficients j:ℝ)-(localXZCoefficients j:ℝ)|) ≤ 0 := by simp
  have hangle : |2*t*(weightTotal (dyadicWeights 2 localXZCoefficients):ℚ)/((2:ℚ)^2*N)| ≤ 1 := by
    rw [localXZ_dyadic_table.2.2]
    convert! ht using 1
    congr 1
    field_simp
    ring
  have hH : (∑ j : Fin 2,(localXZCoefficients j:ℂ) • pauliStringMatrix 1 (localXZLabels j)) =
      (1/3 : ℂ) • pauliX-(2/3 : ℂ) • pauliZ := by
    simp only [localXZ_pauli_matrix,Fin.sum_univ_two,localXZCoefficients]
    norm_num
    module
  have he := local_quantized_pauli_qdrift_actual_total_error 2 1 2 N R k r localXZCoefficients
    (fun j => (localXZCoefficients j:ℝ)) 0 localXZLabels t 0 X hN hW ha hangle
  dsimp only at he
  simp only [Complex.ofReal_ratCast,hH,localXZ_dyadic_table.2.2] at he
  norm_num at he
  convert! he using 1
  ring

end Qatlib.Concepts.RandCompile.ReferenceModel
