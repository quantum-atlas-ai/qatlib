/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMetropolis11.GibbsMixing.GibbsMetropolisDefs

/-!
# Finite-precision Metropolis bounds

This module develops a dyadic acceptance approximation in the quantum Metropolis setting of
[TemmeEtAl2011]. It proves completeness and trace identities for QPE readout branches split by
the finite-bit coin, together with stochasticity, approximate Gibbs stationarity, and a
conditional Gibbs minorization for the associated finite-state kernel.

The iteration estimates bound the accumulated L1 defect by the initial defect plus `n * D *
fairBitGrid k`. A resource ledger records explicit symbolic counts and is combined with this
finite-precision error budget.

## Main statements

* `qpeFairBitKraus_complete` and `qpeFairBit_total` establish completeness and total trace
  preservation.
* `fairBitKernel_approxStationary` bounds each Gibbs stationarity defect by the dyadic grid
  spacing.
* `fairBitKernel_minorization` gives an explicit minorization under bounded nonnegative energies
  and a sufficiently fine grid.
* `fairBitEvolve_defect_le` and `gibbsRunLedger_of_budget` combine accumulated error control
  with ledger counts.
* `fairBitKernel_bridge` relates the finite-bit kernel to the ideal thermal kernel.

## References

* [Temme et al., 2011][TemmeEtAl2011], *Quantum Metropolis Sampling*, Eqs. (2)-(3), Section 3.2,
  and the detailed-balance discussion.
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.StageAQUANTUMGIBBS
open Qatlib.Concepts.MbqcFlow.FlowDecision.StageAQUANTUMGIBBS
open Qatlib.Papers.QMetropolis11.GibbsMixing.StageBGIBBSMETROPOLIS

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing
namespace StageBGIBBSMETROPOLIS

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder

/-- For an acceptance parameter in `[0, 1]`, its finite-bit approximation also lies in `[0, 1]`. -/
theorem fairBitAccept_mem (k : ℕ) (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    0 ≤ fairBitAccept k f ∧ fairBitAccept k f ≤ 1 := by
  unfold fairBitAccept Qatlib.Concepts.RiskEstimation.PopulationGap.fairBitAcceptMass
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hfloor : (Nat.floor ((2 : ℝ) ^ k * f) : ℝ) ≤ (2 : ℝ) ^ k * f :=
    Nat.floor_le (mul_nonneg (by positivity) hf0)
  have hx1 : (2 : ℝ) ^ k * f ≤ (2 : ℝ) ^ k := by
    have h := mul_le_mul_of_nonneg_left hf1 h2.le
    simpa using h
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt h2)
  · rw [div_le_one h2]
    exact hfloor.trans hx1

/-- For `0 ≤ f ≤ 1`, the absolute error of the finite-bit acceptance approximation is at most
the dyadic grid spacing `fairBitGrid k`. -/
theorem fairBitAccept_error (k : ℕ) (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    |fairBitAccept k f - f| ≤ fairBitGrid k := by
  unfold fairBitAccept Qatlib.Concepts.RiskEstimation.PopulationGap.fairBitAcceptMass
  set x : ℝ := (2 : ℝ) ^ k * f with hx
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hfloor_le : (Nat.floor x : ℝ) ≤ x := Nat.floor_le (mul_nonneg (by positivity) hf0)
  have hfloor_lt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  have hdist : |(Nat.floor x : ℝ) - x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hkey : (Nat.floor x : ℝ) / (2 : ℝ) ^ k - f = ((Nat.floor x : ℝ) - x) / (2 : ℝ) ^ k := by
    rw [hx]
    field_simp
  rw [hkey, abs_div, abs_of_pos h2]
  have hlt : |((Nat.floor x : ℝ) - x)| / (2 : ℝ) ^ k < 1 / (2 : ℝ) ^ k :=
    div_lt_div_of_pos_right hdist h2
  unfold fairBitGrid
  rw [one_div] at hlt
  exact hlt.le

/-- The finite-bit acceptance rule assigns zero mass to the zero acceptance parameter. -/
theorem fairBitAccept_zero (k : ℕ) : fairBitAccept k 0 = 0 := by
  unfold fairBitAccept Qatlib.Concepts.RiskEstimation.PopulationGap.fairBitAcceptMass
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [mul_zero, Nat.floor_zero, Nat.cast_zero, zero_div]

/-- At acceptance parameter one, the finite-bit acceptance mass is at least `1 - fairBitGrid k`. -/
theorem fairBitAccept_one_lower (k : ℕ) : 1 - fairBitGrid k ≤ fairBitAccept k 1 := by
  have hmem := fairBitAccept_mem k 1 (by norm_num) (by norm_num)
  have herr := fairBitAccept_error k 1 (by norm_num) (by norm_num)
  rw [abs_le] at herr
  linarith

/-- The rejecting and accepting branch masses sum to one for every real acceptance parameter. -/
theorem fairBitBranchMass_sum (k : ℕ) (f : ℝ) :
    fairBitBranchMass k f false + fairBitBranchMass k f true = 1 := by
  simp [fairBitBranchMass]

/-- The QPE readout Kraus operator for label `z`, scaled by the square root of the finite-bit
coin branch mass. The branch acceptance compares the old label with `z` through their label
energies. -/
noncomputable def qpeFairBitKraus {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (β : ℝ) (k : ℕ) (old : Fin G.levels) :
    Fin G.levels × Bool → Matrix (QpeSpace G D) (QpeSpace G D) ℂ :=
  fun zb =>
    acceptScale (fairBitBranchMass k
      (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old zb.1) zb.2)
      • (qpeKraus O G zb.1)

/-- For `0 ≤ f ≤ 1`, splitting a fixed QPE readout into the two finite-bit coin branches
preserves its effect operator: the branch sum of `Kᴴ * K` equals the original QPE effect. -/
theorem qpeFairBit_branch_complete {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (k : ℕ) (z : Fin G.levels) (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    ∑ b : Bool, (acceptScale (fairBitBranchMass k f b) • (qpeKraus O G z))ᴴ
        * (acceptScale (fairBitBranchMass k f b) • (qpeKraus O G z))
      = (qpeKraus O G z)ᴴ * (qpeKraus O G z) := by
  have hm0 : 0 ≤ fairBitBranchMass k f false := by
    unfold fairBitBranchMass
    simp only [Bool.false_eq_true, if_false]
    linarith [fairBitAccept_mem k f hf0 hf1]
  have hm1 : 0 ≤ fairBitBranchMass k f true := by
    unfold fairBitBranchMass
    simp only [Bool.true_eq, if_true]
    linarith [fairBitAccept_mem k f hf0 hf1]
  calc ∑ b : Bool, (acceptScale (fairBitBranchMass k f b) • (qpeKraus O G z))ᴴ
        * (acceptScale (fairBitBranchMass k f b) • (qpeKraus O G z))
      = (acceptScale (fairBitBranchMass k f true) • (qpeKraus O G z))ᴴ
          * (acceptScale (fairBitBranchMass k f true) • (qpeKraus O G z))
        + (acceptScale (fairBitBranchMass k f false) • (qpeKraus O G z))ᴴ
          * (acceptScale (fairBitBranchMass k f false) • (qpeKraus O G z)) := by
          rw [Fintype.sum_bool]
    _ = ((fairBitBranchMass k f true + fairBitBranchMass k f false : ℝ) : ℂ)
          • ((qpeKraus O G z)ᴴ * (qpeKraus O G z)) := by
          simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, acceptScale_star]
          rw [smul_mul_smul, smul_mul_smul, acceptScale_sq hm0, acceptScale_sq hm1]
          rw [← add_smul]
          congr 1
          push_cast
          ring
    _ = (qpeKraus O G z)ᴴ * (qpeKraus O G z) := by
          have hreorder : (fairBitBranchMass k f true + fairBitBranchMass k f false : ℝ)
              = (fairBitBranchMass k f false + fairBitBranchMass k f true : ℝ) := add_comm _ _
          rw [hreorder, fairBitBranchMass_sum]
          simp

/-- The finite-bit QPE branch operators are complete: the sum of `Kᴴ * K` over readout labels
and Boolean outcomes is the identity. -/
theorem qpeFairBitKraus_complete {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (β : ℝ) (k : ℕ) (old : Fin G.levels) :
    (∑ zb : Fin G.levels × Bool,
        (qpeFairBitKraus O G β k old zb)ᴴ * (qpeFairBitKraus O G β k old zb)) = 1 := by
  have hqpe : (∑ j : Fin G.levels, (qpeKraus O G j)ᴴ * (qpeKraus O G j)) = 1 :=
    qpeKraus_complete O G
  have hbranch : ∀ z : Fin G.levels,
      ∑ b : Bool,
          (qpeFairBitKraus O G β k old (z, b))ᴴ * (qpeFairBitKraus O G β k old (z, b))
        = (qpeKraus O G z)ᴴ * (qpeKraus O G z) := by
    intro z
    have hz0 : 0 ≤ Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z := by
      exact le_of_lt (thermalAcceptance_pos
        (fun w => Qatlib.Concepts.RiskEstimation.PopulationGap.labelEnergy O.time G.levels w) β old z)
    have hz1 : Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z ≤ 1 := by
      exact thermalAcceptance_le_one
        (fun w => Qatlib.Concepts.RiskEstimation.PopulationGap.labelEnergy O.time G.levels w) β old z
    have hrewrite : ∀ b : Bool, qpeFairBitKraus O G β k old (z, b)
        = acceptScale (fairBitBranchMass k
            (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) b) • (qpeKraus O G z) := by
      intro b
      simp [qpeFairBitKraus]
    simp only [hrewrite]
    exact qpeFairBit_branch_complete O G k z
      (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) hz0 hz1
  rw [Fintype.sum_prod_type]
  calc (∑ z : Fin G.levels, ∑ b : Bool,
        (qpeFairBitKraus O G β k old (z, b))ᴴ * (qpeFairBitKraus O G β k old (z, b)))
      = ∑ z : Fin G.levels, (qpeKraus O G z)ᴴ * (qpeKraus O G z) := by
          apply Finset.sum_congr rfl
          intro z _
          exact hbranch z
    _ = 1 := hqpe

/-- For any input matrix, the output of a finite-bit QPE branch equals its real branch mass
times the unscaled QPE readout output. -/
theorem qpeFairBit_branch_eq {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (β : ℝ) (k : ℕ) (old : Fin G.levels) (z : Fin G.levels) (b : Bool)
    (ρ : Matrix (QpeSpace G D) (QpeSpace G D) ℂ) :
    (qpeFairBitKraus O G β k old (z, b)) * ρ * (qpeFairBitKraus O G β k old (z, b))ᴴ
      = ((fairBitBranchMass k (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) b
          : ℝ) : ℂ)
          • ((qpeKraus O G z) * ρ * (qpeKraus O G z)ᴴ) := by
  have hz0 : 0 ≤ Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z := by
    exact le_of_lt (thermalAcceptance_pos
      (fun w => Qatlib.Concepts.RiskEstimation.PopulationGap.labelEnergy O.time G.levels w) β old z)
  have hm0 : 0 ≤ fairBitBranchMass k
      (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) b := by
    unfold fairBitBranchMass
    split
    · linarith [fairBitAccept_mem k _ hz0 (by
        exact thermalAcceptance_le_one
          (fun w => Qatlib.Concepts.RiskEstimation.PopulationGap.labelEnergy O.time G.levels w) β old z)]
    · linarith [fairBitAccept_mem k _ hz0 (by
        exact thermalAcceptance_le_one
          (fun w => Qatlib.Concepts.RiskEstimation.PopulationGap.labelEnergy O.time G.levels w) β old z)]
  have hrewrite : qpeFairBitKraus O G β k old (z, b)
      = acceptScale (fairBitBranchMass k
          (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) b) • (qpeKraus O G z) := by
    simp [qpeFairBitKraus]
  rw [hrewrite]
  simp only [Matrix.conjTranspose_smul, acceptScale_star]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [acceptScale_sq hm0]

/-- The trace of a finite-bit QPE branch output equals its branch mass times the trace of the
corresponding unscaled QPE readout output. The equality holds for arbitrary input matrices. -/
theorem qpeFairBit_branchMass {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (β : ℝ) (k : ℕ) (old : Fin G.levels) (ρ : Matrix (QpeSpace G D) (QpeSpace G D) ℂ)
    (z : Fin G.levels) (b : Bool) :
    Matrix.trace ((qpeFairBitKraus O G β k old (z, b)) * ρ
      * (qpeFairBitKraus O G β k old (z, b))ᴴ)
      = ((fairBitBranchMass k
          (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) b : ℝ) : ℂ)
          * Matrix.trace ((qpeKraus O G z) * ρ * (qpeKraus O G z)ᴴ) := by
  have hz0 : 0 ≤ Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z := by
    exact le_of_lt (thermalAcceptance_pos
      (fun w => Qatlib.Concepts.RiskEstimation.PopulationGap.labelEnergy O.time G.levels w) β old z)
  have hz1 : Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z ≤ 1 := by
    exact thermalAcceptance_le_one
      (fun w => Qatlib.Concepts.RiskEstimation.PopulationGap.labelEnergy O.time G.levels w) β old z
  have hm0 : 0 ≤ fairBitBranchMass k
      (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) b := by
    unfold fairBitBranchMass
    split
    · linarith [fairBitAccept_mem k _ hz0 hz1]
    · linarith [fairBitAccept_mem k _ hz0 hz1]
  have hrewrite : qpeFairBitKraus O G β k old (z, b)
      = acceptScale (fairBitBranchMass k
          (Qatlib.Concepts.RiskEstimation.PopulationGap.labelAcceptance O.time G.levels β old z) b) • (qpeKraus O G z) := by
    simp [qpeFairBitKraus]
  rw [hrewrite]
  simp only [Matrix.conjTranspose_smul, acceptScale_star]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [acceptScale_sq hm0, Matrix.trace_smul]
  rfl

/-- The absolute detailed-balance defect of the finite-bit acceptance rule is bounded by
`fairBitGrid k` times the sum of the two unnormalized Gibbs weights. The bound compares the
rounded rule with the exact Metropolis acceptance of Eq. (3) in [TemmeEtAl2011]. -/
theorem fairBitAccept_detailed_balance_error {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (i j : Fin D) :
    |Real.exp (-β * E i) * fairBitAccept k (thermalAcceptance E β i j)
      - Real.exp (-β * E j) * fairBitAccept k (thermalAcceptance E β j i)|
      ≤ fairBitGrid k * (Real.exp (-β * E i) + Real.exp (-β * E j)) := by
  have hfi0 : 0 ≤ thermalAcceptance E β i j := le_of_lt (thermalAcceptance_pos E β i j)
  have hfi1 : thermalAcceptance E β i j ≤ 1 := thermalAcceptance_le_one E β i j
  have hfj0 : 0 ≤ thermalAcceptance E β j i := le_of_lt (thermalAcceptance_pos E β j i)
  have hfj1 : thermalAcceptance E β j i ≤ 1 := thermalAcceptance_le_one E β j i
  have herr_i : |fairBitAccept k (thermalAcceptance E β i j) - thermalAcceptance E β i j|
      ≤ fairBitGrid k := fairBitAccept_error k _ hfi0 hfi1
  have herr_j : |fairBitAccept k (thermalAcceptance E β j i) - thermalAcceptance E β j i|
      ≤ fairBitGrid k := fairBitAccept_error k _ hfj0 hfj1
  have hdet : Real.exp (-β * E i) * thermalAcceptance E β i j
      = Real.exp (-β * E j) * thermalAcceptance E β j i :=
    thermalAcceptance_detailed E β i j
  have hkey : Real.exp (-β * E i) * fairBitAccept k (thermalAcceptance E β i j)
      - Real.exp (-β * E j) * fairBitAccept k (thermalAcceptance E β j i)
      = Real.exp (-β * E i)
          * (fairBitAccept k (thermalAcceptance E β i j) - thermalAcceptance E β i j)
        - Real.exp (-β * E j)
          * (fairBitAccept k (thermalAcceptance E β j i) - thermalAcceptance E β j i) := by
    linear_combination hdet
  rw [hkey, abs_le]
  have h1u : Real.exp (-β * E i) * (fairBitAccept k (thermalAcceptance E β i j)
        - thermalAcceptance E β i j)
      ≤ Real.exp (-β * E i) * fairBitGrid k :=
    mul_le_mul_of_nonneg_left (abs_le.mp herr_i).2 (le_of_lt (Real.exp_pos _))
  have h1l : Real.exp (-β * E i) * (-fairBitGrid k)
      ≤ Real.exp (-β * E i) * (fairBitAccept k (thermalAcceptance E β i j)
        - thermalAcceptance E β i j) :=
    mul_le_mul_of_nonneg_left (abs_le.mp herr_i).1 (le_of_lt (Real.exp_pos _))
  have h2u : Real.exp (-β * E j) * (fairBitAccept k (thermalAcceptance E β j i)
        - thermalAcceptance E β j i)
      ≤ Real.exp (-β * E j) * fairBitGrid k :=
    mul_le_mul_of_nonneg_left (abs_le.mp herr_j).2 (le_of_lt (Real.exp_pos _))
  have h2l : Real.exp (-β * E j) * (-fairBitGrid k)
      ≤ Real.exp (-β * E j) * (fairBitAccept k (thermalAcceptance E β j i)
        - thermalAcceptance E β j i) :=
    mul_le_mul_of_nonneg_left (abs_le.mp herr_j).1 (le_of_lt (Real.exp_pos _))
  constructor
  · linarith
  · linarith

/-- For distinct states in a nonempty state space, the transition entry is the finite-bit
thermal acceptance divided by the number of states. -/
theorem fairBitKernel_offdiag {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (hD : 0 < D) (i j : Fin D) (hij : i ≠ j) :
    fairBitKernel E β k i j = fairBitAccept k (thermalAcceptance E β i j) / (D : ℝ) := by
  simp [fairBitKernel, hij]

/-- Every off-diagonal entry of the finite-bit Metropolis kernel is nonnegative when the state
space is nonempty. -/
theorem fairBitKernel_offdiag_nonneg {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (hD : 0 < D) (i j : Fin D) (hij : i ≠ j) :
    0 ≤ fairBitKernel E β k i j := by
  rw [fairBitKernel_offdiag E β k hD i j hij]
  have hmem := fairBitAccept_mem k (thermalAcceptance E β i j)
    (le_of_lt (thermalAcceptance_pos E β i j)) (thermalAcceptance_le_one E β i j)
  exact div_nonneg hmem.1 (by exact_mod_cast hD.le)

/-- Each row of the finite-bit Metropolis kernel sums to one when the state space is nonempty. -/
theorem fairBitKernel_row_sum {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (i : Fin D) : ∑ j : Fin D, fairBitKernel E β k i j = 1 := by
  have hins : (Finset.univ : Finset (Fin D)) = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  have hni : i ∉ Finset.univ.erase i := Finset.notMem_erase i Finset.univ
  rw [hins, Finset.sum_insert hni]
  have hoff : ∀ j ∈ (Finset.univ : Finset (Fin D)).erase i,
      fairBitKernel E β k i j
        = fairBitAccept k (thermalAcceptance E β i j) / (D : ℝ) := by
    intro j hj
    rw [fairBitKernel_offdiag E β k hD i j (Ne.symm (Finset.ne_of_mem_erase hj))]
  rw [Finset.sum_congr rfl hoff]
  rw [fairBitKernel, if_pos rfl]
  have hsumdiv : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j') / (D : ℝ))
      = (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j')) / (D : ℝ) :=
    (Finset.sum_div (Finset.univ.erase i)
      (fun j' => fairBitAccept k (thermalAcceptance E β i j')) (D : ℝ)).symm
  rw [hsumdiv]
  ring

/-- Every diagonal entry of the finite-bit Metropolis kernel is strictly positive when the state
space is nonempty. -/
theorem fairBitKernel_diag_pos {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (i : Fin D) : 0 < fairBitKernel E β k i i := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hcard : ((Finset.univ : Finset (Fin D)).erase i).card = D - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j')) ≤ ((D - 1 : ℕ) : ℝ) := by
    calc (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j'))
        ≤ ∑ _ ∈ (Finset.univ : Finset (Fin D)).erase i, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          have hm := fairBitAccept_mem k (thermalAcceptance E β i j')
            (le_of_lt (thermalAcceptance_pos E β i j'))
            (thermalAcceptance_le_one E β i j')
          exact hm.2
      _ = (((Finset.univ : Finset (Fin D)).erase i).card : ℝ) := by
          simp [Finset.sum_const]
      _ = ((D - 1 : ℕ) : ℝ) := by
          rw [hcard]
  have hsumdiv : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j') / (D : ℝ))
      = (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j')) / (D : ℝ) :=
    (Finset.sum_div (Finset.univ.erase i)
      (fun j' => fairBitAccept k (thermalAcceptance E β i j')) (D : ℝ)).symm
  rw [fairBitKernel, if_pos rfl, hsumdiv]
  have hfrac : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j')) / (D : ℝ)
      ≤ ((D - 1 : ℕ) : ℝ) / (D : ℝ) := div_le_div_of_nonneg_right hsum hDpos.le
  have hlt : ((D - 1 : ℕ) : ℝ) / (D : ℝ) < 1 := by
    rw [div_lt_one hDpos]
    have hcast : ((D - 1 : ℕ) : ℝ) < (D : ℝ) := by
      exact_mod_cast (by omega : D - 1 < D)
    exact hcast
  linarith

/-- The symbolic resource ledger for `n` steps: `n` energy measurements and proposal gates, `n *
levels` controlled powers and inverse-QFT gates, and `n * k` coin bits. Its quantum and
classical peak entries are `levels + D` and `k`, respectively. -/
noncomputable def gibbsRunLedger (D levels k n : ℕ) : GibbsRunLedger where
  energyMeasurements := n
  controlledPowers := n * levels
  inverseQftGates := n * levels
  proposalGates := n
  coinBits := n * k
  quantumPeak := levels + D
  classicalPeak := k

/-- All seven entries of the run ledger equal their defining symbolic counts for measurements,
controlled powers, inverse-QFT gates, proposals, coin bits, and peak quantum and classical
space. -/
theorem gibbsRunLedger_counts (D levels k n : ℕ) :
    (gibbsRunLedger D levels k n).energyMeasurements = n ∧
      (gibbsRunLedger D levels k n).controlledPowers = n * levels ∧
      (gibbsRunLedger D levels k n).inverseQftGates = n * levels ∧
      (gibbsRunLedger D levels k n).proposalGates = n ∧
      (gibbsRunLedger D levels k n).coinBits = n * k ∧
      (gibbsRunLedger D levels k n).quantumPeak = levels + D ∧
      (gibbsRunLedger D levels k n).classicalPeak = k :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The run ledger records exactly `n * k` coin bits for `n` steps with coin precision `k`. -/
theorem gibbsRunLedger_coinBits (D levels k n : ℕ) :
    (gibbsRunLedger D levels k n).coinBits = n * k := rfl

/-- Summing the traces of all finite-bit QPE branch outputs preserves the trace of any input
matrix. -/
theorem qpeFairBit_total {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) (β : ℝ) (k : ℕ)
    (old : Fin G.levels) (ρ : Matrix (QpeSpace G D) (QpeSpace G D) ℂ) :
    (∑ zb : Fin G.levels × Bool,
      Matrix.trace ((qpeFairBitKraus O G β k old zb) * ρ
        * (qpeFairBitKraus O G β k old zb)ᴴ)) = Matrix.trace ρ := by
  classical
  have hcycle : ∀ zb : Fin G.levels × Bool,
      Matrix.trace ((qpeFairBitKraus O G β k old zb) * ρ
          * (qpeFairBitKraus O G β k old zb)ᴴ)
        = Matrix.trace ((qpeFairBitKraus O G β k old zb)ᴴ
            * (qpeFairBitKraus O G β k old zb) * ρ) := by
    intro zb
    rw [Matrix.trace_mul_cycle]
  calc (∑ zb : Fin G.levels × Bool,
        Matrix.trace ((qpeFairBitKraus O G β k old zb) * ρ
          * (qpeFairBitKraus O G β k old zb)ᴴ))
      = ∑ zb : Fin G.levels × Bool,
        Matrix.trace ((qpeFairBitKraus O G β k old zb)ᴴ
          * (qpeFairBitKraus O G β k old zb) * ρ) :=
        Finset.sum_congr rfl fun zb _ => hcycle zb
    _ = Matrix.trace ((∑ zb : Fin G.levels × Bool,
          (qpeFairBitKraus O G β k old zb)ᴴ * (qpeFairBitKraus O G β k old zb)) * ρ) := by
        rw [← Matrix.trace_sum, ← Finset.sum_mul]
    _ = Matrix.trace (1 * ρ) := by rw [qpeFairBitKraus_complete O G β k old]
    _ = Matrix.trace ρ := by rw [Matrix.one_mul]

/-- If the input matrix has trace one, the traces of all finite-bit QPE branch outputs sum to
one. -/
theorem qpeFairBit_total_eq {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) (β : ℝ) (k : ℕ)
    (old : Fin G.levels) (ρ : Matrix (QpeSpace G D) (QpeSpace G D) ℂ)
    (hρ : Matrix.trace ρ = 1) :
    (∑ zb : Fin G.levels × Bool,
      Matrix.trace ((qpeFairBitKraus O G β k old zb) * ρ
        * (qpeFairBitKraus O G β k old zb)ᴴ)) = 1 := by
  rw [qpeFairBit_total O G β k old ρ]
  exact hρ

/-- The scalar acceptance weight for proposal `c`: its ensemble weight times thermal acceptance
when both endpoints are the least-index representatives of their energies, and zero
otherwise. This is the scalar factor used in the acceptance-map expression associated with
[TemmeEtAl2011]. -/
noncomputable def temmeAcceptWeight {D : ℕ} (E : Fin D → ℝ)
    (ens : Qatlib.Concepts.RiskEstimation.PopulationGap.ProposalEnsemble D)
    (β : ℝ) (i j : Fin D) (c : Fin ens.count) : ℝ :=
  ((if Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E i
      ∧ Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E j then (1 : ℝ) else 0)
    * ens.weight c * thermalAcceptance E β i j)

/-- The representative-restricted scalar acceptance weight is nonnegative for a legal proposal
ensemble. -/
theorem temmeAcceptWeight_nonneg {D : ℕ} (E : Fin D → ℝ)
    (ens : Qatlib.Concepts.RiskEstimation.PopulationGap.ProposalEnsemble D)
    (β : ℝ) (hEns : Qatlib.Concepts.RiskEstimation.PopulationGap.proposalEnsembleLegal ens)
    (i j : Fin D) (c : Fin ens.count) :
    0 ≤ temmeAcceptWeight E ens β i j c := by
  unfold temmeAcceptWeight
  have hw : 0 ≤ ens.weight c := hEns.1 c
  have ha : 0 ≤ thermalAcceptance E β i j := (thermalAcceptance_pos E β i j).le
  by_cases h : Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E i
      ∧ Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E j
  · rw [if_pos h]
    positivity
  · rw [if_neg h]
    positivity

/-- For each proposal in a legal ensemble, the scalar acceptance weights satisfy detailed
balance with the unnormalized Gibbs weights. This is a scalar identity for the acceptance
factors associated with [TemmeEtAl2011]. -/
theorem temmeAccept_detailed_balance {D : ℕ} (E : Fin D → ℝ)
    (ens : Qatlib.Concepts.RiskEstimation.PopulationGap.ProposalEnsemble D)
    (β : ℝ) (hEns : Qatlib.Concepts.RiskEstimation.PopulationGap.proposalEnsembleLegal ens)
    (i j : Fin D) (c : Fin ens.count) :
    Real.exp (-β * E i) * temmeAcceptWeight E ens β i j c
      = Real.exp (-β * E j) * temmeAcceptWeight E ens β j i c := by
  unfold temmeAcceptWeight
  by_cases hab : (Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E i
      ∧ Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E j)
  · have hba : (Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E j
        ∧ Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E i) := ⟨hab.2, hab.1⟩
    have hdet := thermalAcceptance_detailed E β i j
    simp only [temmeAcceptWeight, if_pos hab, if_pos hba]
    calc Real.exp (-β * E i) * (1 * ens.weight c * thermalAcceptance E β i j)
        = (Real.exp (-β * E i) * thermalAcceptance E β i j) * ens.weight c := by ring
      _ = (Real.exp (-β * E j) * thermalAcceptance E β j i) * ens.weight c := by rw [hdet]
      _ = Real.exp (-β * E j) * (1 * ens.weight c * thermalAcceptance E β j i) := by ring
  · have hnba : ¬ (Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E j
        ∧ Qatlib.Concepts.RiskEstimation.PopulationGap.isEnergyRep E i) := by
      intro hconj
      exact hab ⟨hconj.2, hconj.1⟩
    simp only [temmeAcceptWeight, if_neg hab, if_neg hnba]
    ring

/-- The diagonal Gibbs probability at a state is its Boltzmann weight `exp (-β * E i)` divided
by the diagonal Gibbs partition function. -/
theorem fairBitKernel_gibbsProb {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (hD : 0 < D) (i : Fin D) :
    (diagonalGibbsDist D hD E β).prob i
      = Real.exp (-β * E i) / diagonalGibbsPartition D E β :=
  diagonalGibbsDist_prob D hD E β i

/-- For two states, the normalized Gibbs-weighted acceptance imbalance is at most `fairBitGrid
k` times the sum of their Gibbs probabilities. -/
private theorem fairBit_pair_defect {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (i j : Fin D) :
    |(diagonalGibbsDist D hD E β).prob i * fairBitAccept k (thermalAcceptance E β i j)
      - (diagonalGibbsDist D hD E β).prob j * fairBitAccept k (thermalAcceptance E β j i)|
      ≤ fairBitGrid k * ((diagonalGibbsDist D hD E β).prob i
          + (diagonalGibbsDist D hD E β).prob j) := by
  have hZ : 0 < diagonalGibbsPartition D E β := diagonalGibbsPartition_pos D hD E β
  have herr := fairBitAccept_detailed_balance_error E β k i j
  rw [diagonalGibbsDist_prob D hD E β i, diagonalGibbsDist_prob D hD E β j]
  have h1 : (Real.exp (-β * E i) / diagonalGibbsPartition D E β)
      * fairBitAccept k (thermalAcceptance E β i j)
      = (Real.exp (-β * E i) * fairBitAccept k (thermalAcceptance E β i j))
        / diagonalGibbsPartition D E β :=
    div_mul_eq_mul_div _ _ _
  have h2 : (Real.exp (-β * E j) / diagonalGibbsPartition D E β)
      * fairBitAccept k (thermalAcceptance E β j i)
      = (Real.exp (-β * E j) * fairBitAccept k (thermalAcceptance E β j i))
        / diagonalGibbsPartition D E β :=
    div_mul_eq_mul_div _ _ _
  have hquot : |(Real.exp (-β * E i) * fairBitAccept k (thermalAcceptance E β i j)
      - Real.exp (-β * E j) * fairBitAccept k (thermalAcceptance E β j i))
      / diagonalGibbsPartition D E β|
      = |Real.exp (-β * E i) * fairBitAccept k (thermalAcceptance E β i j)
        - Real.exp (-β * E j) * fairBitAccept k (thermalAcceptance E β j i)|
        / diagonalGibbsPartition D E β := by
    simp only [abs_div, abs_of_nonneg hZ.le]
  rw [h1, h2, ← sub_div, hquot, ← add_div, ← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hZ).2 herr

/-- Applying the finite-bit kernel to the diagonal Gibbs distribution changes each coordinate by
at most `fairBitGrid k`. -/
theorem fairBitKernel_approxStationary {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (hD : 0 < D) (j : Fin D) :
    |(∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j)
      - (diagonalGibbsDist D hD E β).prob j| ≤ fairBitGrid k := by
  classical
  set S : Finset (Fin D) := (Finset.univ : Finset (Fin D)).erase j with hSdef
  have hS : S = (Finset.univ : Finset (Fin D)).erase j := rfl
  have hsplit : (∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j)
      = (∑ i ∈ S, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j)
        + (diagonalGibbsDist D hD E β).prob j * fairBitKernel E β k j j := by
    rw [hS]
    symm
    exact Finset.sum_erase_add _ _ (Finset.mem_univ j)
  have hoff : ∀ i ∈ S,
      (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j
        = (diagonalGibbsDist D hD E β).prob i
          * (fairBitAccept k (thermalAcceptance E β i j) / (D : ℝ)) := by
    intro i hi
    rw [hS] at hi
    rw [fairBitKernel_offdiag E β k hD i j (Finset.ne_of_mem_erase hi)]
  have hdiag : fairBitKernel E β k j j
      = 1 - ∑ j' ∈ S, fairBitAccept k (thermalAcceptance E β j j') / (D : ℝ) := by
    rw [hS, fairBitKernel, if_pos rfl]
  have hmain : (∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j)
        - (diagonalGibbsDist D hD E β).prob j
      = ∑ i ∈ S, (((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ)) := by
    rw [hsplit, hdiag, Finset.sum_congr rfl hoff]
    have hrename : (∑ j' ∈ S, fairBitAccept k (thermalAcceptance E β j j') / (D : ℝ))
        = ∑ i ∈ S, fairBitAccept k (thermalAcceptance E β j i) / (D : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    have hA : (∑ i ∈ S, (diagonalGibbsDist D hD E β).prob i
          * (fairBitAccept k (thermalAcceptance E β i j) / (D : ℝ)))
        = ∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob i
          * fairBitAccept k (thermalAcceptance E β i j)) / (D : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hB : (diagonalGibbsDist D hD E β).prob j
          * (∑ i ∈ S, fairBitAccept k (thermalAcceptance E β j i) / (D : ℝ))
        = ∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob j
          * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hrearr : (∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)) / (D : ℝ))
          + ((diagonalGibbsDist D hD E β).prob j
            - ∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob j
              * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ))
          - (diagonalGibbsDist D hD E β).prob j
        = (∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)) / (D : ℝ))
          - ∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ) := by
      ring
    rw [hA, hrename, mul_sub, mul_one, hB, hrearr, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have habs : |∑ i ∈ S, (((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ))|
      ≤ (∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))|) / (D : ℝ) := by
    calc |∑ i ∈ S, (((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ))|
        ≤ ∑ i ∈ S, |(((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))| / (D : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [abs_div,
              abs_of_nonneg (show (0 : ℝ) ≤ (D : ℝ) from by exact_mod_cast hD.le)]
      _ = (∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))|) / (D : ℝ) :=
        (Finset.sum_div _ _ _).symm
  have hbound : (∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))|)
      ≤ ∑ i ∈ S, (fairBitGrid k
        * ((diagonalGibbsDist D hD E β).prob i
          + (diagonalGibbsDist D hD E β).prob j)) :=
    Finset.sum_le_sum fun i _ => fairBit_pair_defect E β k hD i j
  have hcard : S.card = D - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hsplit' : (∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i)
      = (∑ i ∈ S, (diagonalGibbsDist D hD E β).prob i)
        + (diagonalGibbsDist D hD E β).prob j := by
    rw [hS]
    symm
    exact Finset.sum_erase_add _ _ (Finset.mem_univ j)
  have hsum1 : (∑ i : Fin D, (diagonalGibbsDist D hD E β).prob i) = 1 :=
    (diagonalGibbsDist D hD E β).sum_one
  have herase : (∑ i ∈ S, (diagonalGibbsDist D hD E β).prob i)
      = 1 - (diagonalGibbsDist D hD E β).prob j := by
    linarith
  have hpi0 : 0 ≤ (diagonalGibbsDist D hD E β).prob j :=
    (diagonalGibbsDist D hD E β).nonneg j
  have hpi1 : (diagonalGibbsDist D hD E β).prob j ≤ 1 := by
    have herase0 : 0 ≤ ∑ i ∈ S, (diagonalGibbsDist D hD E β).prob i :=
      Finset.sum_nonneg fun i _ => (diagonalGibbsDist D hD E β).nonneg i
    linarith
  have htot : (∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob i
        + (diagonalGibbsDist D hD E β).prob j)) ≤ (D : ℝ) := by
    have hsplit2 : (∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob i
          + (diagonalGibbsDist D hD E β).prob j))
        = (∑ i ∈ S, (diagonalGibbsDist D hD E β).prob i)
          + S.card * (diagonalGibbsDist D hD E β).prob j := by
      rw [Finset.sum_add_distrib]
      have hconst : (∑ i ∈ S, (diagonalGibbsDist D hD E β).prob j)
          = S.card * (diagonalGibbsDist D hD E β).prob j := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
      rw [hconst]
    rw [hsplit2, herase, hcard]
    have hcastD : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
    rw [hcastD]
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    by_cases hD2 : 2 ≤ D
    · have hD2r : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD2
      have hmul : ((D : ℝ) - 2) * (diagonalGibbsDist D hD E β).prob j ≤ (D : ℝ) - 2 := by
        nlinarith [hpi1]
      linarith
    · have hDr : (D : ℝ) < 2 := by exact_mod_cast (by omega)
      have hmul : ((D : ℝ) - 2) * (diagonalGibbsDist D hD E β).prob j ≤ 0 := by
        nlinarith [hpi0]
      linarith
  have htotal : (∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))|)
      ≤ (D : ℝ) * fairBitGrid k := by
    calc (∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))|)
        ≤ ∑ i ∈ S, (fairBitGrid k
            * ((diagonalGibbsDist D hD E β).prob i
              + (diagonalGibbsDist D hD E β).prob j)) := hbound
      _ = fairBitGrid k * (∑ i ∈ S, ((diagonalGibbsDist D hD E β).prob i
            + (diagonalGibbsDist D hD E β).prob j)) := by rw [Finset.mul_sum]
      _ ≤ fairBitGrid k * (D : ℝ) :=
        mul_le_mul_of_nonneg_left htot (by unfold fairBitGrid; positivity)
      _ = (D : ℝ) * fairBitGrid k := by ring
  rw [hmain]
  have hfin1 : |∑ i ∈ S, (((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i)) / (D : ℝ))|
      ≤ (∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))|) / (D : ℝ) := habs
  have hfin2 : (∑ i ∈ S, |((diagonalGibbsDist D hD E β).prob i
            * fairBitAccept k (thermalAcceptance E β i j)
          - (diagonalGibbsDist D hD E β).prob j
            * fairBitAccept k (thermalAcceptance E β j i))|) / (D : ℝ)
      ≤ ((D : ℝ) * fairBitGrid k) / (D : ℝ) :=
    div_le_div_of_nonneg_right htotal (by exact_mod_cast hD.le)
  have hfin3 : ((D : ℝ) * fairBitGrid k) / (D : ℝ) ≤ fairBitGrid k := by
    have heq : ((D : ℝ) * fairBitGrid k) / (D : ℝ) = fairBitGrid k := by
      have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      field_simp
    exact le_of_eq heq
  exact hfin1.trans (hfin2.trans hfin3)

/-- With nonnegative inverse temperature and nonnegative energies, thermal acceptance from any
state to `j` is at least `exp (-β * E j)`. -/
private theorem accept_lower_bound {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hE : ∀ i, 0 ≤ E i) (i j : Fin D) :
    Real.exp (-β * E j) ≤ thermalAcceptance E β i j := by
  have harg : -β * (E j - E i) = (-β * E j) - (-β * E i) := by ring
  rw [thermalAcceptance, harg]
  rcases le_or_gt (Real.exp ((-β * E j) - (-β * E i))) 1 with h | h
  · rw [min_eq_right h]
    have h1 : Real.exp (-β * E i) ≤ 1 := by
      have hle : -β * E i ≤ 0 := by
        have := mul_nonneg hβ (hE i)
        linarith
      simpa using Real.exp_le_exp.mpr hle
    have hid : Real.exp (-β * E j)
        = Real.exp (-β * E i) * Real.exp ((-β * E j) - (-β * E i)) := by
      have heq : (-β * E i : ℝ) + ((-β * E j) - (-β * E i)) = -β * E j := by ring
      rw [← Real.exp_add, heq]
    rw [hid]
    have hmul : Real.exp (-β * E i) * Real.exp ((-β * E j) - (-β * E i))
        ≤ Real.exp ((-β * E j) - (-β * E i)) := by
      have h : Real.exp ((-β * E j) - (-β * E i)) * Real.exp (-β * E i)
          ≤ Real.exp ((-β * E j) - (-β * E i)) * 1 :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))
      calc Real.exp (-β * E i) * Real.exp ((-β * E j) - (-β * E i))
          = Real.exp ((-β * E j) - (-β * E i)) * Real.exp (-β * E i) := by ring
        _ ≤ Real.exp ((-β * E j) - (-β * E i)) * 1 := h
        _ = Real.exp ((-β * E j) - (-β * E i)) := by ring
    exact hmul
  · rw [min_eq_left h.le]
    have hle : -β * E j ≤ 0 := by
      have := mul_nonneg hβ (hE j)
      linarith
    simpa using Real.exp_le_exp.mpr hle

/-- If `0 ≤ E i ≤ R`, `β ≥ 0`, and `fairBitGrid k < exp (-β * R)`, then `exp (-β * R) * (exp (-β
* R) - fairBitGrid k)` lies strictly between zero and one. -/
theorem fairBitKernel_minorization_const {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (hD : 0 < D) (R : ℝ) (hβ : 0 ≤ β) (hE : ∀ i, 0 ≤ E i) (hER : ∀ i, E i ≤ R)
    (hgrid : fairBitGrid k < Real.exp (-β * R)) :
    0 < Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k) ∧
      Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k) < 1 := by
  have hR0 : 0 ≤ R := le_trans (hE ⟨0, hD⟩) (hER ⟨0, hD⟩)
  have hexpR : 0 < Real.exp (-β * R) := Real.exp_pos _
  have hexpR1 : Real.exp (-β * R) ≤ 1 := by
    have hle : -β * R ≤ 0 := by
      have := mul_nonneg hβ hR0
      linarith
    simpa using Real.exp_le_exp.mpr hle
  have hgridpos : 0 < fairBitGrid k := by
    unfold fairBitGrid
    positivity
  constructor
  · have hdiff : 0 < Real.exp (-β * R) - fairBitGrid k := by linarith
    exact mul_pos hexpR hdiff
  · have hsq : Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k)
        < Real.exp (-β * R) * Real.exp (-β * R) := by
      nlinarith [hgridpos]
    nlinarith [hexpR1]

/-- For nonnegative inverse temperature, energies in `[0, R]`, and `fairBitGrid k < exp (-β *
R)`, every transition entry dominates the target Gibbs probability times `exp (-β * R) *
(exp (-β * R) - fairBitGrid k)`. -/
theorem fairBitKernel_minorization {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (hD : 0 < D) (R : ℝ) (hβ : 0 ≤ β) (hE : ∀ i, 0 ≤ E i) (hER : ∀ i, E i ≤ R)
    (hgrid : fairBitGrid k < Real.exp (-β * R)) (i j : Fin D) :
    Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k)
        * (diagonalGibbsDist D hD E β).prob j
      ≤ fairBitKernel E β k i j := by
  have hR0 : 0 ≤ R := le_trans (hE ⟨0, hD⟩) (hER ⟨0, hD⟩)
  have hZ : 0 < diagonalGibbsPartition D E β := diagonalGibbsPartition_pos D hD E β
  have hexpR : 0 < Real.exp (-β * R) := Real.exp_pos _
  have hexpR1 : Real.exp (-β * R) ≤ 1 := by
    have hle : -β * R ≤ 0 := by
      have := mul_nonneg hβ hR0
      linarith
    simpa using Real.exp_le_exp.mpr hle
  have hgridpos : 0 ≤ fairBitGrid k := by
    unfold fairBitGrid
    positivity
  have hweight_le : ∀ k' : Fin D, Real.exp (-β * E k') ≤ 1 := by
    intro k'
    have hle : -β * E k' ≤ 0 := by
      have := mul_nonneg hβ (hE k')
      linarith
    simpa using Real.exp_le_exp.mpr hle
  have hweight_ge : ∀ k' : Fin D, Real.exp (-β * E k') ≥ Real.exp (-β * R) := by
    intro k'
    have hle : -β * R ≤ -β * E k' := by
      have := mul_nonneg hβ (sub_nonneg.mpr (hER k'))
      linarith
    simpa using Real.exp_le_exp.mpr hle
  have hZbound : (D : ℝ) * Real.exp (-β * R) ≤ diagonalGibbsPartition D E β := by
    calc (D : ℝ) * Real.exp (-β * R)
        = ∑ _ : Fin D, Real.exp (-β * R) := by
          rw [Finset.sum_const]
          simp [Fintype.card_fin]
      _ ≤ ∑ k' : Fin D, Real.exp (-β * E k') := by
          refine Finset.sum_le_sum fun k' _ => ?_
          exact hweight_ge k'
  have hpi_bound : (diagonalGibbsDist D hD E β).prob j
      ≤ 1 / ((D : ℝ) * Real.exp (-β * R)) := by
    rw [diagonalGibbsDist_prob D hD E β j]
    have hnum : Real.exp (-β * E j) ≤ 1 := hweight_le j
    have hden : 0 < (D : ℝ) * Real.exp (-β * R) := by positivity
    rw [div_le_div_iff₀ hZ hden]
    have hmul : Real.exp (-β * E j) * ((D : ℝ) * Real.exp (-β * R))
        ≤ 1 * ((D : ℝ) * Real.exp (-β * R)) :=
      mul_le_mul_of_nonneg_right hnum hden.le
    nlinarith
  have heta : 0 < Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k) :=
    (fairBitKernel_minorization_const E β k hD R hβ hE hER hgrid).1
  have hkey : Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k)
        * (diagonalGibbsDist D hD E β).prob j
      ≤ (Real.exp (-β * R) - fairBitGrid k) / (D : ℝ) := by
    have hnonneg : 0 ≤ Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k) :=
      heta.le
    have h1 : Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k)
        * (diagonalGibbsDist D hD E β).prob j
        ≤ Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k)
          * (1 / ((D : ℝ) * Real.exp (-β * R))) :=
      mul_le_mul_of_nonneg_left hpi_bound hnonneg
    have h2 : Real.exp (-β * R) * (Real.exp (-β * R) - fairBitGrid k)
        * (1 / ((D : ℝ) * Real.exp (-β * R)))
        = (Real.exp (-β * R) - fairBitGrid k) / (D : ℝ) := by
      field_simp
    exact h1.trans_eq h2
  by_cases hij : i = j
  · subst j
    have hcard : ((Finset.univ : Finset (Fin D)).erase i).card = D - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
    have hsum : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
        fairBitAccept k (thermalAcceptance E β i j')) ≤ (D : ℝ) - 1 := by
      calc (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
          fairBitAccept k (thermalAcceptance E β i j'))
          ≤ ∑ _ ∈ (Finset.univ : Finset (Fin D)).erase i, (1 : ℝ) := by
            refine Finset.sum_le_sum fun j' _ => ?_
            have hm := fairBitAccept_mem k (thermalAcceptance E β i j')
              (le_of_lt (thermalAcceptance_pos E β i j'))
              (thermalAcceptance_le_one E β i j')
            exact hm.2
        _ = (((Finset.univ : Finset (Fin D)).erase i).card : ℝ) := by
            simp [Finset.sum_const]
        _ = (D : ℝ) - 1 := by rw [hcard, hcast]
    have hdiag : 1 / (D : ℝ) ≤ fairBitKernel E β k i i := by
      have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
      have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      rw [fairBitKernel, if_pos rfl, div_le_iff₀ hDpos, sub_mul, one_mul]
      have hcancel : (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
          fairBitAccept k (thermalAcceptance E β i j') / (D : ℝ)) * (D : ℝ)
          = ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
            fairBitAccept k (thermalAcceptance E β i j') := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j' _
        exact div_mul_cancel₀ _ hDne
      rw [hcancel]
      linarith [hsum]
    have h2 : (Real.exp (-β * R) - fairBitGrid k) / (D : ℝ) ≤ 1 / (D : ℝ) := by
      have hdiff : Real.exp (-β * R) - fairBitGrid k ≤ 1 := by linarith
      exact div_le_div_of_nonneg_right hdiff (by exact_mod_cast hD.le)
    exact hkey.trans (h2.trans hdiag)
  · have hoff : fairBitKernel E β k i j
        = fairBitAccept k (thermalAcceptance E β i j) / (D : ℝ) :=
      fairBitKernel_offdiag E β k hD i j hij
    have haccept : fairBitAccept k (thermalAcceptance E β i j)
        ≥ Real.exp (-β * R) - fairBitGrid k := by
      have herr : |fairBitAccept k (thermalAcceptance E β i j)
          - thermalAcceptance E β i j| ≤ fairBitGrid k :=
        fairBitAccept_error k _ (le_of_lt (thermalAcceptance_pos E β i j))
          (thermalAcceptance_le_one E β i j)
      have hlow : Real.exp (-β * R) ≤ thermalAcceptance E β i j := by
        have hlb := accept_lower_bound E β hβ hE i j
        have hge : Real.exp (-β * E j) ≥ Real.exp (-β * R) := by
          have hle : -β * R ≤ -β * E j := by
            have := mul_nonneg hβ (sub_nonneg.mpr (hER j))
            linarith
          simpa using Real.exp_le_exp.mpr hle
        linarith
      have h2 := (abs_le.mp herr).1
      linarith
    have h3 : (Real.exp (-β * R) - fairBitGrid k) / (D : ℝ)
        ≤ fairBitAccept k (thermalAcceptance E β i j) / (D : ℝ) :=
      div_le_div_of_nonneg_right haccept (by exact_mod_cast hD.le)
    exact hkey.trans (h3.trans_eq hoff.symm)

/-- Every entry of the finite-bit Metropolis kernel is nonnegative when the state space is
nonempty. -/
theorem fairBitKernel_nonneg {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (i j : Fin D) : 0 ≤ fairBitKernel E β k i j := by
  by_cases hij : i = j
  · subst j
    exact (fairBitKernel_diag_pos E β k hD i).le
  · exact fairBitKernel_offdiag_nonneg E β k hD i j hij

/-- Every entry of the finite-bit Metropolis kernel is at most one when the state space is
nonempty. -/
theorem fairBitKernel_le_one {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (i j : Fin D) : fairBitKernel E β k i j ≤ 1 := by
  have hsum := fairBitKernel_row_sum E β k hD i
  have hnonneg : 0 ≤ fairBitKernel E β k i j :=
    fairBitKernel_nonneg E β k hD i j
  have heq : (∑ j' : Fin D, fairBitKernel E β k i j')
      = (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase j, fairBitKernel E β k i j')
        + fairBitKernel E β k i j :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
  have hrest : 0 ≤ (∑ j' ∈ (Finset.univ : Finset (Fin D)).erase j,
      fairBitKernel E β k i j') :=
    Finset.sum_nonneg fun j' _ => fairBitKernel_nonneg E β k hD i j'
  rw [heq] at hsum
  linarith

/-- One finite-bit Metropolis step increases the L1 distance from the diagonal Gibbs probability
vector by at most `D * fairBitGrid k`. The estimate holds for any real input vector. -/
theorem fairBitStep_defect_le {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (p : Fin D → ℝ) :
    (∑ j, |fairBitStep E β k p j - (diagonalGibbsDist D hD E β).prob j|)
      ≤ (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|)
        + (D : ℝ) * fairBitGrid k := by
  classical
  have hsplit : ∀ j : Fin D,
      fairBitStep E β k p j - (diagonalGibbsDist D hD E β).prob j
        = (∑ i, (p i - (diagonalGibbsDist D hD E β).prob i) * fairBitKernel E β k i j)
          + ((∑ i, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j)
            - (diagonalGibbsDist D hD E β).prob j) := by
    intro j
    rw [fairBitStep]
    have h1 : (∑ i, (p i - (diagonalGibbsDist D hD E β).prob i)
          * fairBitKernel E β k i j)
        = (∑ i, p i * fairBitKernel E β k i j)
          - (∑ i, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j) := by
      calc (∑ i, (p i - (diagonalGibbsDist D hD E β).prob i)
            * fairBitKernel E β k i j)
          = ∑ i, (p i * fairBitKernel E β k i j
            - (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = (∑ i, p i * fairBitKernel E β k i j)
            - (∑ i, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j) := by
              rw [← Finset.sum_sub_distrib]
    rw [h1]
    ring
  have hfirst : ∀ j : Fin D,
      |(∑ i, (p i - (diagonalGibbsDist D hD E β).prob i) * fairBitKernel E β k i j)|
        ≤ ∑ i, |p i - (diagonalGibbsDist D hD E β).prob i| * fairBitKernel E β k i j := by
    intro j
    calc |∑ i, (p i - (diagonalGibbsDist D hD E β).prob i) * fairBitKernel E β k i j|
        ≤ ∑ i, |(p i - (diagonalGibbsDist D hD E β).prob i)
            * fairBitKernel E β k i j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|
            * fairBitKernel E β k i j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_of_nonneg (fairBitKernel_nonneg E β k hD i j)]
  have hsecond : ∀ j : Fin D,
      |(∑ i, (diagonalGibbsDist D hD E β).prob i * fairBitKernel E β k i j)
        - (diagonalGibbsDist D hD E β).prob j| ≤ fairBitGrid k :=
    fun j => fairBitKernel_approxStationary E β k hD j
  have hper : ∀ j : Fin D,
      |fairBitStep E β k p j - (diagonalGibbsDist D hD E β).prob j|
        ≤ (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|
            * fairBitKernel E β k i j) + fairBitGrid k := by
    intro j
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add (hfirst j) (hsecond j))
  have hswap : (∑ j, |fairBitStep E β k p j
        - (diagonalGibbsDist D hD E β).prob j|)
      ≤ (∑ j, (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|
          * fairBitKernel E β k i j))
        + (D : ℝ) * fairBitGrid k := by
    calc (∑ j, |fairBitStep E β k p j
          - (diagonalGibbsDist D hD E β).prob j|)
        ≤ ∑ j, ((∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|
            * fairBitKernel E β k i j) + fairBitGrid k) :=
          Finset.sum_le_sum fun j _ => hper j
      _ = (∑ j, (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|
            * fairBitKernel E β k i j))
          + (D : ℝ) * fairBitGrid k := by
            rw [Finset.sum_add_distrib]
            have hconst : (∑ j : Fin D, fairBitGrid k) = (D : ℝ) * fairBitGrid k := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp only [nsmul_eq_mul]
            rw [hconst]
  have hreorder : (∑ j, (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|
          * fairBitKernel E β k i j))
      = ∑ i, (|p i - (diagonalGibbsDist D hD E β).prob i|
          * (∑ j, fairBitKernel E β k i j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hrows : ∀ i : Fin D, (∑ j, fairBitKernel E β k i j) = 1 :=
    fun i => fairBitKernel_row_sum E β k hD i
  have h1 := hswap
  rw [hreorder] at h1
  have h2 : (∑ i, (|p i - (diagonalGibbsDist D hD E β).prob i|
          * (∑ j, fairBitKernel E β k i j)))
      = ∑ i, |p i - (diagonalGibbsDist D hD E β).prob i| := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hrows i]
    simp
  rw [h2] at h1
  have hnonneg : 0 ≤ (D : ℝ) * fairBitGrid k := by
    unfold fairBitGrid
    positivity
  linarith

/-- After `n` finite-bit Metropolis steps, the L1 distance from the diagonal Gibbs probability
vector is at most the initial distance plus `n * D * fairBitGrid k`. -/
theorem fairBitEvolve_defect_le {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (n : ℕ) (p : Fin D → ℝ) :
    (∑ j, |fairBitEvolve E β k n p j - (diagonalGibbsDist D hD E β).prob j|)
      ≤ (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|)
        + (n : ℝ) * ((D : ℝ) * fairBitGrid k) := by
  induction n generalizing p with
  | zero =>
      have h0 : fairBitEvolve E β k 0 p = p := rfl
      rw [h0]
      simp
  | succ n ih =>
      have hstep := fairBitStep_defect_le E β k hD p
      have hrec := ih (fairBitStep E β k p)
      have hdef : fairBitEvolve E β k (n + 1) p
          = fairBitEvolve E β k n (fairBitStep E β k p) := rfl
      rw [hdef, Nat.cast_succ]
      have hmono : ((n : ℝ) + 1) * ((D : ℝ) * fairBitGrid k)
          = (n : ℝ) * ((D : ℝ) * fairBitGrid k) + ((D : ℝ) * fairBitGrid k) := by ring
      rw [hmono]
      linarith

/-- If the initial L1 defect is at most `δ₀` and `n * D * fairBitGrid k ≤ ε - δ₀`, the L1 defect
after `n` steps is at most `ε`. -/
theorem fairBitEvolve_error_budget {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (δ₀ ε : ℝ) (n : ℕ) (p : Fin D → ℝ)
    (hδ : (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|) ≤ δ₀)
    (hbudget : (n : ℝ) * ((D : ℝ) * fairBitGrid k) ≤ ε - δ₀) :
    (∑ j, |fairBitEvolve E β k n p j - (diagonalGibbsDist D hD E β).prob j|) ≤ ε := by
  have h := fairBitEvolve_defect_le E β k hD n p
  linarith

/-- The budget inequality `n * D * fairBitGrid k ≤ ε - δ₀` bounds the step count by `(ε - δ₀) /
(D * fairBitGrid k)` for a nonempty state space. -/
theorem fairBitEvolve_step_budget {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (δ₀ ε : ℝ) (n : ℕ) (p : Fin D → ℝ)
    (hbudget : (n : ℝ) * ((D : ℝ) * fairBitGrid k) ≤ ε - δ₀) :
    (n : ℝ) ≤ (ε - δ₀) / ((D : ℝ) * fairBitGrid k) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hgridpos : 0 < fairBitGrid k := by
    unfold fairBitGrid
    positivity
  have hden : 0 < (D : ℝ) * fairBitGrid k := by positivity
  rw [le_div_iff₀ hden]
  nlinarith

/-- Under the initial-defect and accumulated-error budget hypotheses, the final L1 defect is at
most `ε`. The same statement records `n` measurements, `n * levels` controlled powers, `n *
k` coin bits, and quantum peak `levels + D` in the symbolic ledger. -/
theorem gibbsRunLedger_of_budget {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D)
    (levels : ℕ) (δ₀ ε : ℝ) (n : ℕ) (p : Fin D → ℝ)
    (hδ : (∑ i, |p i - (diagonalGibbsDist D hD E β).prob i|) ≤ δ₀)
    (hbudget : (n : ℝ) * ((D : ℝ) * fairBitGrid k) ≤ ε - δ₀) :
    (gibbsRunLedger D levels k n).energyMeasurements = n ∧
      (gibbsRunLedger D levels k n).controlledPowers = n * levels ∧
      (gibbsRunLedger D levels k n).coinBits = n * k ∧
      (gibbsRunLedger D levels k n).quantumPeak = levels + D ∧
      (∑ j, |fairBitEvolve E β k n p j - (diagonalGibbsDist D hD E β).prob j|) ≤ ε :=
  ⟨rfl, rfl, rfl, rfl, fairBitEvolve_error_budget E β k hD δ₀ ε n p hδ hbudget⟩

/-- For distinct states in a nonempty state space, the finite-bit kernel entry differs from the
ideal thermal-kernel entry by at most `fairBitGrid k / D`. -/
theorem fairBitKernel_close_thermalKernel {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (hD : 0 < D) (i j : Fin D) (hij : i ≠ j) :
    |fairBitKernel E β k i j - thermalKernel D E β i j| ≤ fairBitGrid k / (D : ℝ) := by
  rw [fairBitKernel_offdiag E β k hD i j hij, thermalKernel_offdiag D E β hij]
  have herr := fairBitAccept_error k _ (le_of_lt (thermalAcceptance_pos E β i j))
    (thermalAcceptance_le_one E β i j)
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hquot : |fairBitAccept k (thermalAcceptance E β i j) / (D : ℝ)
        - thermalAcceptance E β i j / (D : ℝ)|
      = |fairBitAccept k (thermalAcceptance E β i j) - thermalAcceptance E β i j| / (D : ℝ) := by
    simp only [← sub_div, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ (D : ℝ) from by exact_mod_cast hD.le)]
  rw [hquot]
  exact div_le_div_of_nonneg_right herr (by positivity)

/-- Both the finite-bit and ideal thermal kernels have row sums one, and their off-diagonal
entries differ by at most `fairBitGrid k / D` when the state space is nonempty. -/
theorem fairBitKernel_bridge {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) (hD : 0 < D) :
    (∀ i : Fin D, (∑ j, fairBitKernel E β k i j) = 1) ∧
      (∀ i : Fin D, (∑ j, thermalKernel D E β i j) = 1) ∧
      (∀ i j : Fin D, i ≠ j →
        |fairBitKernel E β k i j - thermalKernel D E β i j| ≤ fairBitGrid k / (D : ℝ)) := by
  refine ⟨fun i => fairBitKernel_row_sum E β k hD i, ?_, ?_⟩
  · intro i
    have hrow : ∑ j, thermalKernel D E β i j = 1 := by
      have hins : (Finset.univ : Finset (Fin D)) = insert i (Finset.univ.erase i) :=
        (Finset.insert_erase (Finset.mem_univ i)).symm
      have hni : i ∉ Finset.univ.erase i := Finset.notMem_erase i Finset.univ
      have hoff : ∀ j ∈ (Finset.univ : Finset (Fin D)).erase i,
          thermalKernel D E β i j = thermalAcceptance E β i j / (D : ℝ) := by
        intro j hj
        rw [thermalKernel, if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
      rw [hins, Finset.sum_insert hni, thermalKernel, if_pos rfl,
        Finset.sum_congr rfl hoff]
      ring
    exact hrow
  · intro i j hij
    exact fairBitKernel_close_thermalKernel E β k hD i j hij

end StageBGIBBSMETROPOLIS
end Qatlib.Papers.QMetropolis11.GibbsMixing
