/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.DigitEndpoint.SimQdriftDefs
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary

/-!
# Synthesis and phase estimation counterexamples

This module identifies a fixed finite gate synthesis obstruction and an explicit phase
estimation count counterexample. `exponential_synthesis_gap` gives a positive distance from a
scalar Hamiltonian evolution to every legal one wire word.

`not_clause28` and `not_clause29` refute their displayed conjunctions through the synthesis and
count components, respectively. They delimit proposed implementation extensions of the qDRIFT
framework of [Campbell2019].

## Main statements

* `exponential_synthesis_gap`: a norm gap of at least `1 / 32`.
* `pe_chain_count_counterexample`: the proposed phase estimation count bound fails.
* `not_clause28`: the conjunction containing universal synthesis is false.
* `not_clause29`: the conjunction containing the proposed chain count bound is false.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.DiamondQdrift.SignedBridge

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling
open Qatlib.Concepts.RandCompile.ReferenceModel

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint
open Matrix Qatlib.Concepts.DiamondQdrift.QuantizerCert Qatlib.Concepts.DiamondQdrift.SignedBridge
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

/-- The fixed gate word matrix equals the finite code word matrix. -/
theorem fixedGateWordMatrix_eq_code (n : ℕ) (W : List FiniteGateCode) :
    fixedGateWordMatrix n W = finiteCodeWordMatrix n W := by
  induction W with
  | nil => rfl
  | cons g W ih =>
    simp only [fixedGateWordMatrix, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton, finite_phase_word_cons]
    rw [← ih]
    rfl

/-- Evolution of the identity Hamiltonian at the negative argument of `finiteGaussianScalar`
equals the corresponding scalar gate. -/
theorem gaussian_identity_evolution :
    HamiltonianEvolution (1 : Matrix (Reg 1) (Reg 1) ℂ)
      (-Complex.arg finiteGaussianScalar) = finiteGaussianScalarGate := by
  have harg : Complex.exp ((Complex.arg finiteGaussianScalar : ℂ) * Complex.I) =
      finiteGaussianScalar := by
    simpa only [finite_phase_gaussian_norm, Complex.ofReal_one, one_mul] using
      Complex.norm_mul_exp_arg_mul_I finiteGaussianScalar
  unfold HamiltonianEvolution finiteGaussianScalarGate
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
    ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_one, Pi.coe_exp,
    ← Complex.exp_eq_exp_ℂ]
  rw [show -Complex.I * ((-Complex.arg finiteGaussianScalar : ℝ) : ℂ) =
    (Complex.arg finiteGaussianScalar : ℂ) * Complex.I by push_cast; ring, harg]

/-- Every legal one wire finite gate word has operator norm distance at least `1 / 32` from the
specified scalar identity Hamiltonian evolution. -/
theorem exponential_synthesis_gap (W : List FiniteGateCode) (hW : finiteWordLegal 1 W = true) :
    (1 / 32 : ℝ) ≤ ‖fixedGateWordMatrix 1 W -
      HamiltonianEvolution (1 : Matrix (Reg 1) (Reg 1) ℂ) (-Complex.arg finiteGaussianScalar)‖ := by
  rw [gaussian_identity_evolution, fixedGateWordMatrix_eq_code]
  exact (finite_gaussian_scalar_obstruction.2.2 W hW).1

/-- The displayed conjunction of qDRIFT, finite coin, and finite gate synthesis claims is false
because its universal synthesis component conflicts with `exponential_synthesis_gap`. -/
theorem not_clause28 : ¬ (

  (∀ (L D : ℕ) (d : FinDist (Fin L)) (K : Fin L → Operator D)
      (lam t : ℝ) (n : ℕ),
    0 ≤ lam → 0 < n →
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    finiteDiamondDistance (exactQdriftMap d K lam t n)
        (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t)) ≤
      ENNReal.ofReal (2 * lam ^ 2 * t ^ 2 / (n : ℝ)) ∧
      (∀ eps : ℝ, 0 < eps →
        let N := qdriftSteps lam t (2 * eps)
        0 < N ∧ (N : ℝ) ≤ 2 * lam ^ 2 * t ^ 2 / eps + 1 ∧
          finiteDiamondDistance (exactQdriftMap d K lam t N)
              (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t)) ≤
            ENNReal.ofReal eps)) ∧

  (∀ (L D : ℕ) (w : Fin L → ℕ) (j0 : Fin L) (K : Fin L → Operator D)
      (tQ εQ : ℚ),
    0 < weightTotal w → 0 < εQ → εQ ≤ 1 →
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    let W := weightTotal w
    let R := fairBitTightFuel W tQ εQ
    let n := fairBitTightSteps W tQ εQ R (Nat.ceil (8 * (W : ℚ) ^ 2 * tQ ^ 2 / εQ) + 2)
    fairBitTightCert W tQ εQ R n = true ∧
      (∀ m, m < n → fairBitTightCert W tQ εQ R m ≠ true) ∧
      n ≤ Nat.ceil (8 * (W : ℚ) ^ 2 * tQ ^ 2 / εQ) + 2 ∧
      n ≤ 4 * (max 1 (Nat.ceil (2 * (W : ℚ) ^ 2 * tQ ^ 2 / εQ))) + 2 ∧
      n ≤ max 1 (Nat.ceil (16 * (W : ℚ) ^ 2 * tQ ^ 2 / εQ)) + 2 ∧
      n ≤ fairQdriftSteps W (Nat.ceil |tQ|) (Nat.clog 2 (Nat.ceil (8 / εQ))) ∧
      finiteDiamondDistance (fairQdriftActualMap w j0 n R K (tQ : ℝ))
          (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) (tQ : ℝ))) ≤
        ENNReal.ofReal (εQ : ℝ)) ∧

  (∀ (m : ℕ) (Kc : Matrix (Reg m) (Reg m) ℂ),
    1 ≤ m → Kc.IsHermitian → ‖Kc‖ ≤ 1 →
    ∀ (θ η : ℝ), 0 < η →
    ∃ W : List FiniteGateCode,
      finiteWordLegal m W = true ∧
        QueryCount (finiteCodeCircuit m W) = 0 ∧
        ‖fixedGateWordMatrix m W - HamiltonianEvolution Kc θ‖ ≤ η ∧
        W.length ≤ expSynthGateBound m θ η) ∧

  (∃ Kc : Matrix (Reg 2) (Reg 2) ℂ,
    Kc = regEmbed (by decide) witnessProjectorTerm ∧
      Kc.IsHermitian ∧ ‖Kc‖ ≤ 1 ∧
      ∃ W : List FiniteGateCode,
        finiteWordLegal 2 W = true ∧
          QueryCount (finiteCodeCircuit 2 W) = 0 ∧
          ‖fixedGateWordMatrix 2 W - HamiltonianEvolution Kc 1‖ ≤ 1 / 16 ∧
          W.length ≤ expSynthGateBound 2 1 (1 / 16)) ∧

  (∀ (L D : ℕ) (w : Fin L → ℕ) (j0 : Fin L) (K : Fin L → Operator D)
      (tQ : ℚ) (n R : ℕ) (η : ℝ),
    0 < n → 0 < weightTotal w →
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) → 0 < η →
    ∀ ω : Fin n → Fin R → Reg (Nat.clog 2 (weightTotal w)),
      let U : (Fin R → Reg (Nat.clog 2 (weightTotal w))) → Operator D :=
        fun bits => HamiltonianEvolution (K (fairQdriftPick w j0 R bits).1)
          ((tQ : ℝ) * (weightTotal w : ℝ) / (n : ℝ))
      ∃ (m : ℕ) (W : List FiniteGateCode) (hD : D ≤ 2 ^ m),
        finiteWordLegal m W = true ∧
          QueryCount (finiteCodeCircuit m W) = 0 ∧
          ‖fixedGateWordMatrix m W - regEmbed hD (mixturePathOperator U ω)‖ ≤ η ∧
          W.length ≤
            n * (expSynthGateBound m
                    |(tQ : ℝ) * (weightTotal w : ℝ) / (n : ℝ)| (η / (n : ℝ)) +
                (2 ^ m) ^ 2 + 8) ∧
          (∑ i, (fairQdriftPick w j0 R (ω i)).2.1) ≤
            n * Nat.clog 2 (weightTotal w) * R ∧
          (∑ i, (fairQdriftPick w j0 R (ω i)).2.2) ≤ n * L * R)
) := by
  intro h
  obtain ⟨W, hW, _, herr, _⟩ := h.2.2.1 1 1 (by decide)
    (by simp) (by simp) (-Complex.arg finiteGaussianScalar) (1 / 64) (by norm_num)
  have hgap := exponential_synthesis_gap W hW
  linarith

/-- At coefficient mass one, energy precision `1 / 8`, and failure parameter `1 / 2`, the
proposed phase estimation count upper bound is strictly smaller than `peChainTotalCount`. -/
theorem pe_chain_count_counterexample :
    peChainRounds (1 / 2) * (peChainBits (1 / 8) + 1) *
      (Nat.ceil (1369 * ((peChainBits (1 / 8) + 1 : ℕ) : ℝ) * (1 : ℝ)^2 /
        ((1 / 8 : ℝ)^2 * (1 / 2 : ℝ)^3)) + 1) < peChainTotalCount 1 (1 / 8) (1 / 2) := by
  have hb : peChainBits (1 / 8) = 5 := by norm_num [peChainBits, Nat.clog]; decide
  have hr : peChainRounds (1 / 2) = 151 := by norm_num [peChainRounds, Nat.clog]; decide
  have hs : peChainTimeSq (1 / 8) = 1365 := by
    unfold peChainTimeSq
    rw [hb]
    norm_num [peChainTimes, Fin.sum_univ_succ]
  have hq (j : Fin 6) : peChainQuerySteps 1 (1 / 8) (1 / 2) j.val = 16773120 := by
    fin_cases j <;> norm_num [peChainQuerySteps, peChainErrorShare, hb, hs, peChainTimes]
  have ht : peChainTotalCount 1 (1 / 8) (1 / 2) = 15196446720 := by
    unfold peChainTotalCount
    rw [hr, hb]
    simp only [hq]
    norm_num
  rw [ht]
  norm_num [hb, hr]

/-- The displayed conjunction of controlled evolution, postselection, and resource claims is
false because its phase estimation chain count bound conflicts with the explicit
counterexample. -/
theorem not_clause29 : ¬ (

  (∀ (D : ℕ) (H : Operator D) (θ : ℝ),
      HamiltonianEvolution (dilatedTerm H) θ =
        controlledOperator (HamiltonianEvolution H θ)) ∧
  (∀ (L D : ℕ) (d : FinDist (Fin L)) (K : Fin L → Operator D)
      (lam t : ℝ) (n : ℕ) (eps : ℝ),
    0 ≤ lam → 0 < n → 0 < eps →
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    let Kc := fun j => dilatedTerm (K j)
    (exactQdriftMap d Kc lam t n =
        mixturePowerMap d
          (fun j => controlledOperator (HamiltonianEvolution (K j) (t * lam / (n : ℝ)))) n) ∧
      (qdriftHamiltonian d Kc lam = dilatedTerm (qdriftHamiltonian d K lam)) ∧
      (finiteDiamondDistance (exactQdriftMap d Kc lam t n)
          (conjBranch (HamiltonianEvolution (qdriftHamiltonian d Kc lam) t)) ≤
        ENNReal.ofReal (2 * lam ^ 2 * t ^ 2 / (n : ℝ))) ∧
      (0 < qdriftSteps lam t (2 * eps) ∧
        finiteDiamondDistance
            (exactQdriftMap d Kc lam t (qdriftSteps lam t (2 * eps)))
            (conjBranch (HamiltonianEvolution (qdriftHamiltonian d Kc lam) t)) ≤
          ENNReal.ofReal eps)) ∧

  (∀ (Λ : Operator 2 →ₗ[ℂ] Operator 2) (δ : ℝ),
    0 < δ → δ ≤ 1 / 4 →
    finiteDiamondDistance Λ
        (conjBranch (HamiltonianEvolution witnessProjectorTerm (Real.pi / 2))) ≤
      ENNReal.ofReal δ →
    Matrix.traceNorm
        (controlBlockMap Λ noFreeLunchWitness -
          conjBranch
            (controlledOperator (HamiltonianEvolution witnessProjectorTerm (Real.pi / 2)))
            noFreeLunchWitness) ≥
      Matrix.traceNorm noFreeLunchWitness) ∧

  (∀ (D : ℕ) (Φ Ψ : Operator D →ₗ[ℂ] Operator D) (P X : Operator D)
      (δ p : ℝ),
    P * P = P → Pᴴ = P → 0 < δ →
    0 ≤ selectiveMass Ψ P X →
    Matrix.traceNorm (selectiveOutput Ψ P X) = selectiveMass Ψ P X →
    0 ≤ selectiveMass Φ P X →
    Matrix.traceNorm (selectiveOutput Φ P X) = selectiveMass Φ P X →
    selectiveMass Ψ P X = p →
    2 * δ * Matrix.traceNorm X < p →
    finiteDiamondDistance Φ Ψ ≤ ENNReal.ofReal δ →
    p - 2 * δ * Matrix.traceNorm X ≤ selectiveMass Φ P X ∧
      Matrix.traceNorm (conditionalOutput Φ P X - conditionalOutput Ψ P X) ≤
        4 * δ * Matrix.traceNorm X / (p - 2 * δ * Matrix.traceNorm X)) ∧

  (∀ δ p : ℝ,
    0 < δ → δ ≤ 1 / 4 → 2 * δ ≤ p → p ≤ 1 / 2 →
      let Φ : Operator 3 →ₗ[ℂ] Operator 3 := LinearMap.id
      let Ψ := postSelectWitnessPerturb δ
      let X := postSelectWitnessState p
      let P := postSelectWitnessEvent
      IsPSDOperator X ∧
        (Matrix.trace X).re = 1 ∧
        selectiveMass Φ P X = p ∧
        selectiveMass Ψ P X = p + 2 * δ * (1 - p) ∧
        finiteDiamondDistance Φ Ψ ≤ ENNReal.ofReal δ ∧
        4 * δ * (1 - p) / (p + 2 * δ * (1 - p)) ≤
          Matrix.traceNorm (conditionalOutput Φ P X - conditionalOutput Ψ P X)) ∧

  (∀ (L : ℕ) (bigLam t eps : ℝ),
    0 < eps →
    tableIQdriftCount (bigLam * (L : ℝ)) t eps =
      max 1 (Nat.ceil (2 * (L : ℝ) ^ 2 * (bigLam * t) ^ 2 / eps)) ∧
      (1 ≤ bigLam →
        tableIQdriftCount (Real.sqrt (bigLam * (L : ℝ))) t eps ≤
          max 1 (Nat.ceil (2 * (L : ℝ) * (bigLam * t) ^ 2 / eps)))) ∧
  (∀ (L : ℕ) (lam bigLam deltaE pf : ℝ),
    0 < bigLam → 0 < deltaE → 0 < pf → pf < 1 →
    133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3) ≤
      69 * (L : ℝ) ^ 2 * bigLam * Real.sqrt bigLam /
        (deltaE * Real.sqrt deltaE * pf ^ 2) →
    tableIQdriftPeCount lam deltaE pf ≤ tableITrotterBaseline L bigLam deltaE pf) ∧

  (∀ (lam deltaE pf : ℝ),
    0 ≤ lam → 0 < deltaE → deltaE ≤ 1 → 0 < pf → pf < 1 →
    peChainTotalCount lam deltaE pf ≤
      peChainRounds pf * (peChainBits deltaE + 1) *
        (Nat.ceil
            (1369 * ((peChainBits deltaE + 1 : ℕ) : ℝ) * lam ^ 2 / (deltaE ^ 2 * pf ^ 3)) +
          1) ∧
      ∀ j, j ≤ peChainBits deltaE →
        2 * lam ^ 2 * (peChainTimes j) ^ 2 ≤
          peChainErrorShare deltaE pf j * (peChainQuerySteps lam deltaE pf j : ℝ) ∧
      majorityFailure (2 / 5) (peChainRounds pf) ≤ pf / 2) ∧
  (∀ (L D : ℕ) (d : FinDist (Fin L)) (K : Fin L → Operator D)
      (lam deltaE pf : ℝ),
    0 ≤ lam → 0 < deltaE → 0 < pf → pf < 1 →
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    ∀ j, j ≤ peChainBits deltaE →
      finiteDiamondDistance
          (exactQdriftMap d (fun i => dilatedTerm (K i)) lam (peChainTimes j)
            (peChainQuerySteps lam deltaE pf j))
          (conjBranch
              (HamiltonianEvolution
                (qdriftHamiltonian d (fun i => dilatedTerm (K i)) lam) (peChainTimes j))) ≤
        ENNReal.ofReal (peChainErrorShare deltaE pf j))
) := by
  intro h
  have hc := (h.2.2.2.2.2.2.2.1 1 (1 / 8) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1
  exact (not_lt_of_ge hc) pe_chain_count_counterexample

end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
