/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC

open Qatlib
open scoped BigOperators ComplexOrder

variable {D E n : ℕ}

theorem schmidtSpectrum_nonneg (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) (j : Fin D) :
    0 ≤ schmidtSpectrum ψ hψ j := by
  have hM : 0 ≤ (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M := by
    rw [HermitianMat.zero_le_iff]
    exact (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ).property.1
  exact HermitianMat.eigenvalues_nonneg hM j

theorem schmidtSpectrum_sum_eq_one (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    (∑ j, schmidtSpectrum ψ hψ j) = 1 := by
  have h1 : (∑ j, schmidtSpectrum ψ hψ j)
      = (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M.trace := by
    have h := HermitianMat.sum_eigenvalues_eq_trace
      (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M
    exact h
  rw [h1, HermitianMat.trace_eq_re_trace]
  have hmat : (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M.mat
      = (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ).val := rfl
  rw [hmat]
  have htr := (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ).property.2
  rw [htr]
  simp

theorem entropy_eq_schmidtEntropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ = schmidtEntropy ψ hψ := by
  unfold Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy schmidtEntropy
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, HermitianMat.trace_cfc_eq]
  rfl

theorem schmidtUnitary_conjTranspose_mem (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    (schmidtUnitary ψ hψ).val.conjTranspose ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have hU := Unitary.mul_star_self_of_mem (schmidtUnitary ψ hψ).2
  rwa [Matrix.star_eq_conjTranspose] at hU

theorem schmidtRotated_normalized (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Normalized (schmidtRotated ψ hψ) := by
  unfold schmidtRotated
  exact normalized_applyGate
    (tensorGate_unitary (schmidtUnitary_conjTranspose_mem ψ hψ)
      (by rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_one]; simp)) hψ

theorem reducedDensity_eq_conj_diagonal (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ).val
      = (schmidtUnitary ψ hψ).val
        * Matrix.diagonal (fun j => ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
        * (schmidtUnitary ψ hψ).val.conjTranspose := by
  have h := HermitianMat.eq_conj_diagonal (reducedHermitian ψ hψ)
  have hmat : (reducedHermitian ψ hψ).mat
      = (HermitianMat.conj (schmidtUnitary ψ hψ).val
          (HermitianMat.diagonal ℂ (schmidtSpectrum ψ hψ))).mat := by
    exact congrArg HermitianMat.mat h
  rw [HermitianMat.conj_apply_mat, HermitianMat.diagonal_mat] at hmat
  have hval : (reducedHermitian ψ hψ).mat
      = (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ).val := rfl
  rw [hval] at hmat
  exact hmat

theorem partialTrace_outerProduct_schmidtRotated
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    PartialTrace (outerProduct (schmidtRotated ψ hψ))
      = Matrix.diagonal (fun j => ((schmidtSpectrum ψ hψ j : ℝ) : ℂ)) := by
  have hU : (schmidtUnitary ψ hψ).val.conjTranspose
      * (schmidtUnitary ψ hψ).val = 1 := by
    have h := Unitary.star_mul_self_of_mem (schmidtUnitary ψ hψ).2
    rwa [Matrix.star_eq_conjTranspose] at h
  have hU2 : (schmidtUnitary ψ hψ).val.conjTranspose.conjTranspose
      = (schmidtUnitary ψ hψ).val := Matrix.conjTranspose_conjTranspose _
  have hstep : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      (schmidtUnitary ψ hψ).val.conjTranspose * ((schmidtUnitary ψ hψ).val * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  calc PartialTrace (outerProduct (schmidtRotated ψ hψ))
      = (schmidtUnitary ψ hψ).val.conjTranspose
        * (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ).val
        * (schmidtUnitary ψ hψ).val.conjTranspose.conjTranspose := by
        rw [schmidtRotated, partialTrace_outerProduct_apply_tensorLeft,
          ← Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity_val ψ hψ]
      _ = (schmidtUnitary ψ hψ).val.conjTranspose
        * ((schmidtUnitary ψ hψ).val
          * (Matrix.diagonal (fun j => ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
            * ((schmidtUnitary ψ hψ).val.conjTranspose
              * (schmidtUnitary ψ hψ).val.conjTranspose.conjTranspose))) := by
        rw [reducedDensity_eq_conj_diagonal]
        simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun j => ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
          * ((schmidtUnitary ψ hψ).val.conjTranspose
            * (schmidtUnitary ψ hψ).val.conjTranspose.conjTranspose) := by
        exact hstep _
      _ = Matrix.diagonal (fun j => ((schmidtSpectrum ψ hψ j : ℝ) : ℂ)) := by
        rw [hU2, hU, Matrix.mul_one]

theorem branchMass_nonneg (I : DiagonalInstrument D n) (spec : Fin D → ℝ)
    (hspec : ∀ j, 0 ≤ spec j) (i : Fin n) : 0 ≤ branchMass I spec i := by
  unfold branchMass
  exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hspec j)

theorem branchMass_sum_eq_spec (I : DiagonalInstrument D n) (spec : Fin D → ℝ) :
    (∑ i, branchMass I spec i) = (∑ j, spec j) := by
  have hswap : (∑ i, ∑ j, I.entry i j ^ 2 * spec j)
      = ∑ j, (∑ i, I.entry i j ^ 2) * spec j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc (∑ i, I.entry i j ^ 2 * spec j) = ∑ i, spec j * I.entry i j ^ 2 := by
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = spec j * ∑ i, I.entry i j ^ 2 := by
          exact (Finset.mul_sum (Finset.univ : Finset (Fin n))
            (fun i => I.entry i j ^ 2) (spec j)).symm
        _ = (∑ i, I.entry i j ^ 2) * spec j := mul_comm _ _
  unfold branchMass
  rw [hswap]
  calc (∑ j, (∑ i, I.entry i j ^ 2) * spec j) = ∑ j, spec j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [I.hcomplete j]
        ring

theorem branchMass_sum_eq_one (I : DiagonalInstrument D n) (spec : Fin D → ℝ)
    (hsum : (∑ j, spec j) = 1) : (∑ i, branchMass I spec i) = 1 := by
  rw [branchMass_sum_eq_spec, hsum]

theorem branchSpectrum_nonneg (I : DiagonalInstrument D n) (spec : Fin D → ℝ)
    (hspec : ∀ j, 0 ≤ spec j) (i : Fin n) (j : Fin D) : 0 ≤ branchSpectrum I spec i j := by
  unfold branchSpectrum
  by_cases hp : branchMass I spec i = 0
  · simp [hp]
  · exact div_nonneg (mul_nonneg (sq_nonneg _) (hspec j)) (branchMass_nonneg I spec hspec i)

theorem branchSpectrum_sum_eq_one (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (i : Fin n)
    (hp : 0 < branchMass I spec i) : (∑ j, branchSpectrum I spec i j) = 1 := by
  unfold branchSpectrum
  have hnum : (∑ j, I.entry i j ^ 2 * spec j) = branchMass I spec i := rfl
  have hmul : (∑ j, (I.entry i j ^ 2 * spec j) / branchMass I spec i)
      * branchMass I spec i = ∑ j, I.entry i j ^ 2 * spec j := by
    calc (∑ j, (I.entry i j ^ 2 * spec j) / branchMass I spec i) * branchMass I spec i
        = ∑ j, ((I.entry i j ^ 2 * spec j) / branchMass I spec i) * branchMass I spec i := by
          rw [Finset.sum_mul]
        _ = ∑ j, I.entry i j ^ 2 * spec j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          field_simp
  have h' : branchMass I spec i
      * (∑ j, (I.entry i j ^ 2 * spec j) / branchMass I spec i)
      = branchMass I spec i * 1 := by
    rw [mul_comm, hmul, hnum, mul_one]
  exact mul_left_cancel₀ hp.ne' h'

theorem branchMass_mul_branchSpectrum (I : DiagonalInstrument D n) (spec : Fin D → ℝ)
    (hspec : ∀ j, 0 ≤ spec j) (i : Fin n) (j : Fin D) :
    branchMass I spec i * branchSpectrum I spec i j = I.entry i j ^ 2 * spec j := by
  have hnonneg : ∀ k, 0 ≤ I.entry i k ^ 2 * spec k :=
    fun k => mul_nonneg (sq_nonneg _) (hspec k)
  by_cases hp : branchMass I spec i = 0
  · have hterm : I.entry i j ^ 2 * spec j ≤ branchMass I spec i := by
      unfold branchMass
      exact Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
    have hz : I.entry i j ^ 2 * spec j = 0 := by
      have h1 : I.entry i j ^ 2 * spec j ≤ 0 := by simpa [hp] using hterm
      have h2 : 0 ≤ I.entry i j ^ 2 * spec j := hnonneg j
      linarith
    unfold branchSpectrum
    rw [hp, hz, zero_mul]
  · unfold branchSpectrum
    field_simp

theorem weighted_branchSpectrum_eq_spec (I : DiagonalInstrument D n) (spec : Fin D → ℝ)
    (hspec : ∀ j, 0 ≤ spec j) (j : Fin D) :
    (∑ i, branchMass I spec i * branchSpectrum I spec i j) = spec j := by
  calc (∑ i, branchMass I spec i * branchSpectrum I spec i j)
      = ∑ i, I.entry i j ^ 2 * spec j :=
        Finset.sum_congr rfl fun i _ => branchMass_mul_branchSpectrum I spec hspec i j
    _ = (∑ i, I.entry i j ^ 2) * spec j := by
        rw [Finset.sum_mul]
    _ = spec j := by rw [I.hcomplete j]; ring

theorem branch_partialTrace (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) :
    PartialTrace (outerProduct (schmidtBranch ψ hψ I i))
      = Matrix.diagonal (fun j => ((I.entry i j ^ 2 * schmidtSpectrum ψ hψ j : ℝ) : ℂ)) := by
  rw [schmidtBranch, partialTrace_outerProduct_apply_tensorLeft,
    partialTrace_outerProduct_schmidtRotated]
  have hD : (I.op i).conjTranspose = Matrix.diagonal (fun j => (I.entry i j : ℂ)) := by
    rw [DiagonalInstrument.op, Matrix.diagonal_conjTranspose]
    ext a b
    simp [Matrix.diagonal_apply]
  rw [hD]
  ext a b
  by_cases h : a = b
  · subst h
    simp [Matrix.diagonal_apply, Matrix.mul_apply, DiagonalInstrument.op]
    ring
  · simp [Matrix.diagonal_apply, Matrix.mul_apply, DiagonalInstrument.op, h]

noncomputable def diagonalDensity {I : Type} [Fintype I] [DecidableEq I] (c : I → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hsum : (∑ i, c i) = 1) : Qatlib.Concepts.QuantumEntropy.EntropyCalculus.Density I := by
  have hpsd : (Matrix.diagonal (fun i => (c i : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    exact fun i => Complex.zero_le_real.mpr (hc i)
  have htr : Matrix.trace (Matrix.diagonal (fun i => (c i : ℂ))) = 1 := by
    rw [Matrix.trace, Matrix.diag_diagonal]
    rw [← Complex.ofReal_sum, hsum]
    norm_num
  exact ⟨Matrix.diagonal (fun i => (c i : ℂ)), ⟨hpsd, htr⟩⟩

theorem entropy_diagonal {I : Type} [Fintype I] [DecidableEq I] (c : I → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hsum : (∑ i, c i) = 1) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy (diagonalDensity c hc hsum) = ∑ i, Real.negMulLog (c i) := by
  have hM : (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (diagonalDensity c hc hsum)).M = HermitianMat.diagonal ℂ c := by
    ext1
    rfl
  unfold Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, hM, HermitianMat.cfc_diagonal, HermitianMat.trace_diagonal]
  rfl

theorem branch_entropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) (hp : 0 < branchMass I (schmidtSpectrum ψ hψ) i) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
        (diagonalDensity (branchSpectrum I (schmidtSpectrum ψ hψ) i)
          (branchSpectrum_nonneg I (schmidtSpectrum ψ hψ) (schmidtSpectrum_nonneg ψ hψ) i)
          (branchSpectrum_sum_eq_one I (schmidtSpectrum ψ hψ) i hp))
      = ∑ j, Real.negMulLog (branchSpectrum I (schmidtSpectrum ψ hψ) i j) :=
  entropy_diagonal _ _ _

theorem negMulLog_jensen {m k : ℕ} (w : Fin m → ℝ) (x : Fin m → Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw0 : (∑ i, w i) = 1) (hx : ∀ i j, 0 ≤ x i j) (j : Fin k) :
    (∑ i, w i * Real.negMulLog (x i j)) ≤ Real.negMulLog (∑ i, w i * x i j) := by
  have h := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset (Fin m))) (w := w) (p := fun i => x i j)
    (fun i _ => hw i) (by simp [hw0]) (fun i _ => hx i j)
  simpa using h

theorem diagonalInstrument_average_entropy_le
    (I : DiagonalInstrument D n) (spec : Fin D → ℝ)
    (hspec : ∀ j, 0 ≤ spec j) (hsum : (∑ j, spec j) = 1) :
    (∑ i, branchMass I spec i * (∑ j, Real.negMulLog (branchSpectrum I spec i j)))
      ≤ ∑ j, Real.negMulLog (spec j) := by
  have hj : ∀ j, (∑ i, branchMass I spec i * Real.negMulLog (branchSpectrum I spec i j))
      ≤ Real.negMulLog (∑ i, branchMass I spec i * branchSpectrum I spec i j) := by
    intro j
    have h := negMulLog_jensen (fun i => branchMass I spec i)
      (fun i j => branchSpectrum I spec i j)
      (branchMass_nonneg I spec hspec) (branchMass_sum_eq_one I spec hsum)
      (branchSpectrum_nonneg I spec hspec) j
    exact h
  calc (∑ i, branchMass I spec i * (∑ j, Real.negMulLog (branchSpectrum I spec i j)))
      = ∑ i, ∑ j, branchMass I spec i * Real.negMulLog (branchSpectrum I spec i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.mul_sum (Finset.univ : Finset (Fin D))
          (fun j => Real.negMulLog (branchSpectrum I spec i j)) (branchMass I spec i)
      _ = ∑ j, ∑ i, branchMass I spec i * Real.negMulLog (branchSpectrum I spec i j) :=
        Finset.sum_comm
      _ ≤ ∑ j, Real.negMulLog (∑ i, branchMass I spec i * branchSpectrum I spec i j) :=
        Finset.sum_le_sum fun j _ => hj j
      _ = ∑ j, Real.negMulLog (spec j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [weighted_branchSpectrum_eq_spec I spec hspec j]

theorem diagonalInstrument_average_entropy_le_state
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) (I : DiagonalInstrument D n) :
    (∑ i, branchMass I (schmidtSpectrum ψ hψ) i *
        (∑ j, Real.negMulLog (branchSpectrum I (schmidtSpectrum ψ hψ) i j)))
      ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ := by
  rw [entropy_eq_schmidtEntropy]
  exact diagonalInstrument_average_entropy_le I (schmidtSpectrum ψ hψ)
    (schmidtSpectrum_nonneg ψ hψ) (schmidtSpectrum_sum_eq_one ψ hψ)

inductive DiagonalLoccTree (D : ℕ) : Type

  | halt : DiagonalLoccTree D

  | node (n : ℕ) (I : DiagonalInstrument D n) (next : Fin n → DiagonalLoccTree D) :
      DiagonalLoccTree D

noncomputable def treeAverageEntropy : DiagonalLoccTree D → (Fin D → ℝ) → ℝ
  | .halt, spec => ∑ j, Real.negMulLog (spec j)
  | .node n I next, spec =>
      ∑ i, branchMass I spec i * treeAverageEntropy (next i) (branchSpectrum I spec i)

theorem treeAverageEntropy_le (T : DiagonalLoccTree D) (spec : Fin D → ℝ)
    (hspec : ∀ j, 0 ≤ spec j) (hsum : (∑ j, spec j) = 1) :
    treeAverageEntropy T spec ≤ ∑ j, Real.negMulLog (spec j) := by
  induction T generalizing spec with
  | halt => exact le_rfl
  | node n I next ih =>
      calc (∑ i, branchMass I spec i * treeAverageEntropy (next i) (branchSpectrum I spec i))
          ≤ ∑ i, branchMass I spec i * (∑ j, Real.negMulLog (branchSpectrum I spec i j)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases hp : branchMass I spec i = 0
            · simp [hp]
            · have hpos : 0 < branchMass I spec i :=
                lt_of_le_of_ne (branchMass_nonneg I spec hspec i) (Ne.symm hp)
              refine mul_le_mul_of_nonneg_left
                (ih i (branchSpectrum I spec i)
                  (branchSpectrum_nonneg I spec hspec i)
                  (branchSpectrum_sum_eq_one I spec i hpos)) (branchMass_nonneg I spec hspec i)
        _ ≤ ∑ j, Real.negMulLog (spec j) :=
          diagonalInstrument_average_entropy_le I spec hspec hsum

def schmidtBasisInstrument (D : ℕ) : DiagonalInstrument D D where
  entry := fun i j => if i = j then 1 else 0
  hcomplete := by
    intro j
    simp [Finset.sum_ite_eq', Finset.mem_univ]

theorem schmidtBasis_branchMass (D : ℕ) (spec : Fin D → ℝ) (i : Fin D) :
    branchMass (schmidtBasisInstrument D) spec i = spec i := by
  unfold branchMass
  simp [schmidtBasisInstrument, Finset.mem_univ]

theorem schmidtBasis_branchSpectrum (D : ℕ) (spec : Fin D → ℝ) (i : Fin D)
    (hp : 0 < branchMass (schmidtBasisInstrument D) spec i) :
    branchSpectrum (schmidtBasisInstrument D) spec i
      = fun j => if i = j then 1 else 0 := by
  have hmass : branchMass (schmidtBasisInstrument D) spec i = spec i :=
    schmidtBasis_branchMass D spec i
  have hpos : 0 < spec i := by rw [← hmass]; exact hp
  funext j
  unfold branchSpectrum
  rw [hmass]
  by_cases h : i = j
  · subst h
    simp [schmidtBasisInstrument, hpos.ne']
  · simp [schmidtBasisInstrument, h]

theorem schmidtBasis_branch_entropy_zero (D : ℕ) (spec : Fin D → ℝ) (i : Fin D)
    (hp : 0 < branchMass (schmidtBasisInstrument D) spec i) :
    (∑ j, Real.negMulLog (branchSpectrum (schmidtBasisInstrument D) spec i j)) = 0 := by
  classical
  rw [schmidtBasis_branchSpectrum D spec i hp]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem schmidtBasis_average_entropy_zero (D : ℕ) (spec : Fin D → ℝ)
    (hspec : ∀ j, 0 ≤ spec j) :
    (∑ i, branchMass (schmidtBasisInstrument D) spec i *
        (∑ j, Real.negMulLog (branchSpectrum (schmidtBasisInstrument D) spec i j))) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases hp : branchMass (schmidtBasisInstrument D) spec i = 0
  · simp [hp]
  · have hpos : 0 < branchMass (schmidtBasisInstrument D) spec i :=
      lt_of_le_of_ne (branchMass_nonneg (schmidtBasisInstrument D) spec hspec i) (Ne.symm hp)
    rw [schmidtBasis_branch_entropy_zero D spec i hpos, mul_zero]

theorem schmidtBasis_strict (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (hpos : 0 < Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ) :
    (∑ i, branchMass (schmidtBasisInstrument D) (schmidtSpectrum ψ hψ) i *
        (∑ j, Real.negMulLog
          (branchSpectrum (schmidtBasisInstrument D) (schmidtSpectrum ψ hψ) i j)))
      < Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ := by
  rw [schmidtBasis_average_entropy_zero D (schmidtSpectrum ψ hψ)
    (schmidtSpectrum_nonneg ψ hψ)]
  exact hpos

theorem bell_schmidtBasis_strict (s : Bool × Bool) :
    (∑ i, branchMass (schmidtBasisInstrument 2)
        (schmidtSpectrum (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s)
          (Qatlib.Concepts.UnbiasedBases.ThreeBasis.bell_normalized s)) i *
        (∑ j, Real.negMulLog
          (branchSpectrum (schmidtBasisInstrument 2)
            (schmidtSpectrum (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s)
              (Qatlib.Concepts.UnbiasedBases.ThreeBasis.bell_normalized s)) i j)))
      < Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s)
          (Qatlib.Concepts.UnbiasedBases.ThreeBasis.bell_normalized s) := by
  refine schmidtBasis_strict (Qatlib.Concepts.FiniteLocc.LOCCProgram.bell s)
    (Qatlib.Concepts.UnbiasedBases.ThreeBasis.bell_normalized s) ?_
  rw [Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy_bell]
  have : (0 : ℝ) < Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    simpa using this
  exact this

theorem roundLedger_outcomeBits (D E n : ℕ) :
    (diagonalRoundLedger D E n).outcomeBits
      = Nat.ceil (Real.log ((n : ℝ)) / Real.log 2) := rfl

theorem loccBits_stepA (D E : ℕ) (n : ℕ) (ks : Fin n → Operator D)
    (next : Fin n → Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E) :
    Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccBits (.stepA n ks next)
      = outcomeCostBits n + Finset.univ.sup (fun i => Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccBits (next i)) := rfl

noncomputable def branchExecution (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n)
    (hp : 0 < branchMass I (schmidtSpectrum ψ hψ) i) : LoccExecution D E n where
  outcome := i
  mass := branchMass I (schmidtSpectrum ψ hψ) i
  entropy := ∑ j, Real.negMulLog (branchSpectrum I (schmidtSpectrum ψ hψ) i j)
  ledger := diagonalRoundLedger D E n

theorem branchExecution_mass (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n)
    (hp : 0 < branchMass I (schmidtSpectrum ψ hψ) i) :
    (branchExecution ψ hψ I i hp).mass = branchMass I (schmidtSpectrum ψ hψ) i := rfl

theorem branchExecution_entropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n)
    (hp : 0 < branchMass I (schmidtSpectrum ψ hψ) i) :
    (branchExecution ψ hψ I i hp).entropy
      = Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
          (diagonalDensity (branchSpectrum I (schmidtSpectrum ψ hψ) i)
            (branchSpectrum_nonneg I (schmidtSpectrum ψ hψ) (schmidtSpectrum_nonneg ψ hψ) i)
            (branchSpectrum_sum_eq_one I (schmidtSpectrum ψ hψ) i hp)) := by
  rw [branch_entropy (ψ) (hψ) (I) (i) hp]
  rfl

def MeasurementMajorization (I : DiagonalInstrument D n) (spec : Fin D → ℝ) : Prop :=
  ∀ i, Qatlib.Concepts.FiniteLocc.LOCCProgram.Majorizes spec (branchSpectrum I spec i)

def SchurConcavityShannon : Prop :=
  ∀ (a b : Fin D → ℝ), Qatlib.Concepts.FiniteLocc.LOCCProgram.Majorizes a b →
    (∑ j, Real.negMulLog (a j)) ≤ ∑ j, Real.negMulLog (b j)

theorem schmidtDiagonal_is_the_specialized_instance
    (I : DiagonalInstrument D n) (spec : Fin D → ℝ) (hspec : ∀ j, 0 ≤ spec j)
    (hsum : (∑ j, spec j) = 1) :
    (∑ i, branchMass I spec i * (∑ j, Real.negMulLog (branchSpectrum I spec i j)))
      ≤ ∑ j, Real.negMulLog (spec j) :=
  diagonalInstrument_average_entropy_le I spec hspec hsum

theorem rotationWeight_eq (c s : ℝ) (k l : Fin D) (dir : Fin 2) (j : Fin D) :
    rotationWeight c s k l dir j = Complex.normSq (rotationVector c s k l dir j) := by
  classical
  by_cases hd : dir.val = 0
  · by_cases hjk : j = k
    · subst hjk
      simp [rotationWeight, rotationVector, hd, Complex.normSq_ofReal, pow_two]
    · by_cases hjl : j = l
      · subst hjl
        simp [rotationWeight, rotationVector, hd, hjk, Complex.normSq_ofReal, pow_two]
      · simp [rotationWeight, rotationVector, hd, hjk, hjl, Complex.normSq_zero]
  · by_cases hjk : j = k
    · subst hjk
      simp [rotationWeight, rotationVector, hd, Complex.normSq_ofReal, pow_two]
    · by_cases hjl : j = l
      · subst hjl
        simp [rotationWeight, rotationVector, hd, hjk, Complex.normSq_ofReal, pow_two]
      · simp [rotationWeight, rotationVector, hd, hjk, hjl, Complex.normSq_zero]

theorem rotationWeight_sum_eq_one (c s : ℝ) (k l : Fin D) (dir : Fin 2)
    (hkl : k ≠ l) (hrot : c ^ 2 + s ^ 2 = 1) :
    (∑ j : Fin D, rotationWeight c s k l dir j) = 1 := by
  classical
  by_cases hd : dir.val = 0
  · have hsplit : (∑ j : Fin D, rotationWeight c s k l dir j)
        = (∑ j : Fin D, (if j = k then c ^ 2 else 0))
          + (∑ j : Fin D, (if j = l then s ^ 2 else 0)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjk : j = k
      · subst hjk
        simp [rotationWeight, hd, hkl]
      · by_cases hjl : j = l
        · subst hjl
          simp [rotationWeight, hd, hjk]
        · simp [rotationWeight, hd, hjk, hjl]
    have hk : (∑ j : Fin D, (if j = k then c ^ 2 else 0)) = c ^ 2 := by
      rw [Fintype.sum_ite_eq' k (fun _ => c ^ 2)]
    have hl : (∑ j : Fin D, (if j = l then s ^ 2 else 0)) = s ^ 2 := by
      rw [Fintype.sum_ite_eq' l (fun _ => s ^ 2)]
    rw [hsplit, hk, hl]
    exact hrot
  · have hsplit : (∑ j : Fin D, rotationWeight c s k l dir j)
        = (∑ j : Fin D, (if j = k then s ^ 2 else 0))
          + (∑ j : Fin D, (if j = l then c ^ 2 else 0)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjk : j = k
      · subst hjk
        simp [rotationWeight, hd, hkl]
      · by_cases hjl : j = l
        · subst hjl
          simp [rotationWeight, hd, hjk]
        · simp [rotationWeight, hd, hjk, hjl]
    have hk : (∑ j : Fin D, (if j = k then s ^ 2 else 0)) = s ^ 2 := by
      rw [Fintype.sum_ite_eq' k (fun _ => s ^ 2)]
    have hl : (∑ j : Fin D, (if j = l then c ^ 2 else 0)) = c ^ 2 := by
      rw [Fintype.sum_ite_eq' l (fun _ => c ^ 2)]
    rw [hsplit, hk, hl]
    simpa [add_comm] using hrot

theorem rotationProjector_conjTranspose (c s : ℝ) (k l : Fin D) (dir : Fin 2) :
    (rotationProjector c s k l dir).conjTranspose = rotationProjector c s k l dir := by
  ext i j
  simp [rotationProjector, outerProduct_apply, Matrix.conjTranspose_apply]
  ring

theorem rotationBranchMass_eq (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (c s : ℝ) (k l : Fin D) (dir : Fin 2) (hkl : k ≠ l) (hrot : c ^ 2 + s ^ 2 = 1) :
    (∑ i, ‖rotationBranchState ψ hψ c s k l dir i‖ ^ 2)
      = rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir := by
  classical
  let P : Operator D := rotationProjector c s k l dir
  let S : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.diagonal (fun j => ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
  have hred : PartialTrace (outerProduct (schmidtRotated ψ hψ)) = S := by
    simp only [S]
    exact partialTrace_outerProduct_schmidtRotated ψ hψ
  have htrace : Matrix.trace (outerProduct (rotationBranchState ψ hψ c s k l dir))
      = Matrix.trace (P * (PartialTrace (outerProduct (schmidtRotated ψ hψ))) * P.conjTranspose) := by
    rw [rotationBranchState, ← trace_partialTrace, partialTrace_outerProduct_apply_tensorLeft]
  have hherm : P.conjTranspose = P := by
    simp only [P]
    exact rotationProjector_conjTranspose c s k l dir
  have hP : ∀ i j, P i j
      = (rotationVector c s k l dir i) * (starRingEnd ℂ) (rotationVector c s k l dir j) := by
    intro i j
    simp [P, rotationProjector, outerProduct_apply]
  have hmul : ∀ i j, (P * S) i j
      = (rotationVector c s k l dir i) * (starRingEnd ℂ) (rotationVector c s k l dir j)
        * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ) := by
    intro i j
    rw [Matrix.mul_apply]
    have hsingle : (∑ m : Fin D, P i m * S m j) = P i j * S j j := by
      have hform : (fun m : Fin D => P i m * S m j)
          = fun m => if m = j then (P i m * S j j) else 0 := by
        funext m
        by_cases hm : m = j
        · subst hm
          simp [S]
        · simp [S, hm]
      rw [hform, Fintype.sum_ite_eq']
    rw [hsingle]
    simp [P, S, rotationProjector, outerProduct_apply]
  have hmass : (∑ j : Fin D, (rotationWeight c s k l dir j : ℂ)
        * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
      = ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ) := by
    have h' : (∑ j : Fin D, (rotationWeight c s k l dir j : ℂ)
          * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
        = (∑ j : Fin D, ((rotationWeight c s k l dir j * schmidtSpectrum ψ hψ j : ℝ) : ℂ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.ofReal_mul]
    rw [h', ← Complex.ofReal_sum]
    rfl
  have hentry : ∀ i, (P * S * P) i i
      = (Complex.normSq (rotationVector c s k l dir i) : ℂ)
        * ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ) := by
    intro i
    have hsum1 : (∑ j : Fin D, (P * S) i j * P j i)
        = ∑ j : Fin D, ((rotationVector c s k l dir i)
            * (starRingEnd ℂ) (rotationVector c s k l dir j)
            * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
            * ((rotationVector c s k l dir j)
            * (starRingEnd ℂ) (rotationVector c s k l dir i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hmul i j, hP j i]
    have hsum2 : (∑ j : Fin D, ((rotationVector c s k l dir i)
            * (starRingEnd ℂ) (rotationVector c s k l dir j)
            * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
            * ((rotationVector c s k l dir j)
            * (starRingEnd ℂ) (rotationVector c s k l dir i)))
        = ((rotationVector c s k l dir i) * (starRingEnd ℂ) (rotationVector c s k l dir i) : ℂ)
            * ((∑ j : Fin D, (rotationWeight c s k l dir j : ℂ)
                * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ)) : ℂ) := by
          have h' : ∀ j, ((rotationVector c s k l dir i)
                * (starRingEnd ℂ) (rotationVector c s k l dir j)
                * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ))
                * ((rotationVector c s k l dir j)
                * (starRingEnd ℂ) (rotationVector c s k l dir i))
              = ((rotationVector c s k l dir i)
                  * (starRingEnd ℂ) (rotationVector c s k l dir i) : ℂ)
                * ((rotationWeight c s k l dir j : ℂ)
                  * ((schmidtSpectrum ψ hψ j : ℝ) : ℂ)) := by
            intro j
            have hwl : rotationWeight c s k l dir j
                = Complex.normSq (rotationVector c s k l dir j) :=
              rotationWeight_eq c s k l dir j
            rw [hwl, Complex.normSq_eq_conj_mul_self]; ring
          rw [Finset.sum_congr rfl fun j _ => h' j, ← Finset.mul_sum]
    rw [Matrix.mul_apply, hsum1, hsum2, hmass, Complex.normSq_eq_conj_mul_self]
    ring
  have hnorm : (∑ i : Fin D, (Complex.normSq (rotationVector c s k l dir i) : ℂ)) = 1 := by
    have hsum : (∑ i : Fin D, Complex.normSq (rotationVector c s k l dir i)) = 1 := by
      have h' : (∑ i : Fin D, Complex.normSq (rotationVector c s k l dir i))
          = ∑ i : Fin D, rotationWeight c s k l dir i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (rotationWeight_eq c s k l dir i).symm
      rw [h', rotationWeight_sum_eq_one c s k l dir hkl hrot]
    rw [← Complex.ofReal_sum, hsum]
    simp
  have hsum : (∑ i : Fin D, (P * S * P) i i)
      = ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ) := by
    calc (∑ i : Fin D, (P * S * P) i i)
        = ∑ i : Fin D, (Complex.normSq (rotationVector c s k l dir i) : ℂ)
            * ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact hentry i
      _ = (∑ i : Fin D, (Complex.normSq (rotationVector c s k l dir i) : ℂ))
            * ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ) := by
        exact (Finset.sum_mul (Finset.univ : Finset (Fin D))
          (fun i => (Complex.normSq (rotationVector c s k l dir i) : ℂ))
          ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ)).symm
      _ = ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ) := by
        rw [hnorm]
        ring
  have hmain : Matrix.trace (P * S * P)
      = ((rotationBranchMass (schmidtSpectrum ψ hψ) c s k l dir : ℝ) : ℂ) := by
    rw [Matrix.trace]
    exact hsum
  have hnormmass : (∑ i, ‖rotationBranchState ψ hψ c s k l dir i‖ ^ 2)
      = (Matrix.trace (outerProduct (rotationBranchState ψ hψ c s k l dir))).re := by
    rw [trace_outerProduct, Complex.ofReal_re]
  rw [hnormmass, htrace, hred, hherm, hmain]
  simp [Complex.ofReal_re]

theorem rotationBranchMass_tTransform (spec : Fin D → ℝ) (c s : ℝ) (k l : Fin D)
    (dir : Fin 2) (hkl : k ≠ l) :
    rotationBranchMass spec c s k l dir
      = (if dir.val = 0 then c ^ 2 * spec k + s ^ 2 * spec l
          else s ^ 2 * spec k + c ^ 2 * spec l) := by
  classical
  by_cases hd : dir.val = 0
  · rw [rotationBranchMass]
    have hsplit : (∑ j : Fin D, rotationWeight c s k l dir j * spec j)
        = (∑ j : Fin D, (if j = k then c ^ 2 * spec j else 0))
          + (∑ j : Fin D, (if j = l then s ^ 2 * spec j else 0)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjk : j = k
      · subst hjk
        simp [rotationWeight, hd, hkl]
      · by_cases hjl : j = l
        · subst hjl
          simp [rotationWeight, hd, hjk]
        · simp [rotationWeight, hd, hjk, hjl]
    rw [hsplit, Fintype.sum_ite_eq' k (fun j => c ^ 2 * spec j),
      Fintype.sum_ite_eq' l (fun j => s ^ 2 * spec j)]
    simp [hd]
  · rw [rotationBranchMass]
    have hsplit : (∑ j : Fin D, rotationWeight c s k l dir j * spec j)
        = (∑ j : Fin D, (if j = k then s ^ 2 * spec j else 0))
          + (∑ j : Fin D, (if j = l then c ^ 2 * spec j else 0)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjk : j = k
      · subst hjk
        simp [rotationWeight, hd, hkl]
      · by_cases hjl : j = l
        · subst hjl
          simp [rotationWeight, hd, hjk]
        · simp [rotationWeight, hd, hjk, hjl]
    rw [hsplit, Fintype.sum_ite_eq' k (fun j => s ^ 2 * spec j),
      Fintype.sum_ite_eq' l (fun j => c ^ 2 * spec j)]
    simp [hd]

theorem tTransformSpectrum_of_ne (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) (j : Fin D)
    (hjk : j ≠ k) (hjl : j ≠ l) :
    tTransformSpectrum spec θ k l j = spec j := by
  simp [tTransformSpectrum, hjk, hjl]

theorem tTransformSpectrum_k (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) :
    tTransformSpectrum spec θ k l k = θ * spec k + (1 - θ) * spec l := by
  by_cases hkl : k = l
  · subst hkl
    simp [tTransformSpectrum]
    ring
  · have hkl' : l ≠ k := fun h => hkl h.symm
    simp [tTransformSpectrum, hkl]
    ring

theorem tTransformSpectrum_l (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) :
    tTransformSpectrum spec θ k l l = (1 - θ) * spec k + θ * spec l := by
  by_cases hkl : k = l
  · subst hkl
    simp [tTransformSpectrum]
    ring
  · have hkl' : l ≠ k := fun h => hkl h.symm
    simp [tTransformSpectrum, hkl']
    ring

theorem tTransformSpectrum_sum_eq_spec (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) :
    (∑ j, tTransformSpectrum spec θ k l j) = (∑ j, spec j) := by
  classical
  have h1 : (∑ j, (if j = k then spec l - spec k else 0)) = spec l - spec k :=
    Fintype.sum_ite_eq' k (fun _ => spec l - spec k)
  have h2 : (∑ j, (if j = l then spec k - spec l else 0)) = spec k - spec l :=
    Fintype.sum_ite_eq' l (fun _ => spec k - spec l)
  calc (∑ j, tTransformSpectrum spec θ k l j)
      = (∑ j, spec j) + (1 - θ) * ((∑ j, (if j = k then spec l - spec k else 0))
          + (∑ j, (if j = l then spec k - spec l else 0))) := by
        simp only [tTransformSpectrum]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ = (∑ j, spec j) := by rw [h1, h2]; ring

theorem tTransformSpectrum_nonneg (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D)
    (hspec : ∀ j, 0 ≤ spec j) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : Fin D) :
    0 ≤ tTransformSpectrum spec θ k l j := by
  by_cases hjk : j = k
  · rw [hjk, tTransformSpectrum_k]
    have h1 : 0 ≤ θ * spec k := mul_nonneg hθ0 (hspec k)
    have h2 : 0 ≤ (1 - θ) * spec l := mul_nonneg (by linarith) (hspec l)
    linarith
  · by_cases hjl : j = l
    · rw [hjl, tTransformSpectrum_l]
      have h1 : 0 ≤ (1 - θ) * spec k := mul_nonneg (by linarith) (hspec k)
      have h2 : 0 ≤ θ * spec l := mul_nonneg hθ0 (hspec l)
      linarith
    · rw [tTransformSpectrum_of_ne spec θ k l j hjk hjl]
      exact hspec j

theorem tTransformInstrument_entry_zero (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j) (j : Fin D) :
    (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 0 j ^ 2
      = tTransformFilter spec p θ k l j := by
  have h : (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 0 j
      = Real.sqrt (tTransformFilter spec p θ k l j) := by
    simp [tTransformInstrument]
  rw [h, Real.sq_sqrt (hfilter0 j)]

theorem tTransformInstrument_entry_one (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j) (j : Fin D) :
    (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 1 j ^ 2
      = 1 - tTransformFilter spec p θ k l j := by
  have h : (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 1 j
      = Real.sqrt (1 - tTransformFilter spec p θ k l j) := by
    simp [tTransformInstrument]
  rw [h, Real.sq_sqrt (by have := hfilter j; linarith)]

theorem tTransform_branchMass (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j)
    (hpos : ∀ j, 0 < spec j) (hsum : (∑ j, spec j) = 1) :
    branchMass (tTransformInstrument D spec p θ k l hfilter hfilter0) spec 0 = p := by
  classical
  have hpoint : ∀ j, (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 0 j ^ 2
        * spec j = p * tTransformSpectrum spec θ k l j := by
    intro j
    rw [tTransformInstrument_entry_zero spec p θ k l hfilter hfilter0 j]
    simp only [tTransformFilter]
    have hj : spec j ≠ 0 := ne_of_gt (hpos j)
    field_simp
  have hmain : (∑ j, (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 0 j ^ 2
        * spec j)
      = ∑ j, p * tTransformSpectrum spec θ k l j := by
    refine Fintype.sum_congr _ _ ?_
    exact hpoint
  have hmul : (∑ j, p * tTransformSpectrum spec θ k l j)
      = p * (∑ j, tTransformSpectrum spec θ k l j) :=
    (Finset.mul_sum (Finset.univ : Finset (Fin D))
      (fun j => tTransformSpectrum spec θ k l j) p).symm
  rw [branchMass, hmain, hmul, tTransformSpectrum_sum_eq_spec spec θ k l, hsum]
  ring

theorem tTransform_branchSpectrum (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j)
    (hpos : ∀ j, 0 < spec j) (hp : 0 < p) (hsum : (∑ j, spec j) = 1) :
    branchSpectrum (tTransformInstrument D spec p θ k l hfilter hfilter0) spec 0
      = tTransformSpectrum spec θ k l := by
  classical
  funext j
  have hmass := tTransform_branchMass spec p θ k l hfilter hfilter0 hpos hsum
  unfold branchSpectrum
  rw [hmass]
  rw [tTransformInstrument_entry_zero spec p θ k l hfilter hfilter0 j]
  simp only [tTransformFilter]
  have hj : spec j ≠ 0 := ne_of_gt (hpos j)
  have hp0 : p ≠ 0 := ne_of_gt hp
  field_simp

theorem tTransform_branch_partialTrace (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j)
    (hpos : ∀ j, 0 < spec j) (hsum : (∑ j, spec j) = 1)
    (hspec : schmidtSpectrum ψ hψ = spec) :
    PartialTrace (outerProduct
        (schmidtBranch ψ hψ (tTransformInstrument D spec p θ k l hfilter hfilter0) 0))
      = Matrix.diagonal (fun j => ((p * tTransformSpectrum spec θ k l j : ℝ) : ℂ)) := by
  classical
  rw [branch_partialTrace]
  ext a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.diagonal_apply]
    rw [tTransformInstrument_entry_zero spec p θ k l hfilter hfilter0 a]
    rw [hspec]
    simp only [tTransformFilter]
    have ha : spec a ≠ 0 := ne_of_gt (hpos a)
    field_simp
  · simp only [Matrix.diagonal_apply, h, if_false]

theorem tTransform_branch_entropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter (schmidtSpectrum ψ hψ) p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter (schmidtSpectrum ψ hψ) p θ k l j)
    (hpos : ∀ j, 0 < schmidtSpectrum ψ hψ j) (hp : 0 < p)
    (hmass : 0 < branchMass
      (tTransformInstrument D (schmidtSpectrum ψ hψ) p θ k l hfilter hfilter0)
      (schmidtSpectrum ψ hψ) 0) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
        (diagonalDensity
          (branchSpectrum
            (tTransformInstrument D (schmidtSpectrum ψ hψ) p θ k l hfilter hfilter0)
            (schmidtSpectrum ψ hψ) 0)
          (branchSpectrum_nonneg
            (tTransformInstrument D (schmidtSpectrum ψ hψ) p θ k l hfilter hfilter0)
            (schmidtSpectrum ψ hψ) (schmidtSpectrum_nonneg ψ hψ) 0)
          (branchSpectrum_sum_eq_one
            (tTransformInstrument D (schmidtSpectrum ψ hψ) p θ k l hfilter hfilter0)
            (schmidtSpectrum ψ hψ) 0 hmass))
      = (∑ j, Real.negMulLog (tTransformSpectrum (schmidtSpectrum ψ hψ) θ k l j)) := by
  have hbspec : branchSpectrum
        (tTransformInstrument D (schmidtSpectrum ψ hψ) p θ k l hfilter hfilter0)
        (schmidtSpectrum ψ hψ) 0 = tTransformSpectrum (schmidtSpectrum ψ hψ) θ k l := by
    exact tTransform_branchSpectrum (schmidtSpectrum ψ hψ) p θ k l hfilter hfilter0 hpos hp
      (schmidtSpectrum_sum_eq_one ψ hψ)
  rw [branch_entropy ψ hψ
      (tTransformInstrument D (schmidtSpectrum ψ hψ) p θ k l hfilter hfilter0) 0 hmass]
  rw [hbspec]

theorem tTransformSpectrum_entropy_ge (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D)
    (hspec : ∀ j, 0 ≤ spec j) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∑ j, Real.negMulLog (tTransformSpectrum spec θ k l j))
      ≥ (∑ j, Real.negMulLog (spec j)) := by
  classical
  by_cases hkl : k = l
  · have hid : ∀ j, tTransformSpectrum spec θ k l j = spec j := by
      intro j
      by_cases hj : j = k
      · have hjl : j = l := hkl ▸ hj
        have hlk : l = k := hkl.symm
        rw [hjl]
        simp [tTransformSpectrum, hlk]
      · have hjl : j ≠ l := by
          intro h
          exact hj (hkl.symm ▸ h)
        simp only [tTransformSpectrum]
        rw [if_neg hj, if_neg hjl]
        ring
    have hpoint : ∀ j, Real.negMulLog (tTransformSpectrum spec θ k l j)
        = Real.negMulLog (spec j) := by
      intro j
      exact congrArg Real.negMulLog (hid j)
    have hA : (∑ j, Real.negMulLog (tTransformSpectrum spec θ k l j))
        = ∑ j, Real.negMulLog (spec j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      exact hpoint j
    calc (∑ j, Real.negMulLog (tTransformSpectrum spec θ k l j))
        = ∑ j, Real.negMulLog (spec j) := hA
      _ ≥ ∑ j, Real.negMulLog (spec j) := le_rfl
  · have hkl' : l ≠ k := fun h => hkl h.symm
    have hpair : Real.negMulLog (tTransformSpectrum spec θ k l k)
        + Real.negMulLog (tTransformSpectrum spec θ k l l)
        ≥ Real.negMulLog (spec k) + Real.negMulLog (spec l) := by
      have hk : θ * Real.negMulLog (spec k) + (1 - θ) * Real.negMulLog (spec l)
          ≤ Real.negMulLog (θ * spec k + (1 - θ) * spec l) := by
        have hj := negMulLog_jensen (m := 2) (k := 1)
          (w := fun i => if i = 0 then θ else 1 - θ)
          (x := fun i _ => if i = 0 then spec k else spec l)
          (fun i => by
            by_cases hi : i = 0
            · simp [hi]; exact hθ0
            · simp [hi]; linarith)
          (by simp [Fin.sum_univ_two])
          (fun i _ => by
            by_cases hi : i = 0
            · simp [hi]; exact hspec k
            · simp [hi]; exact hspec l) 0
        simpa [Fin.sum_univ_two] using hj
      have hl : (1 - θ) * Real.negMulLog (spec k) + θ * Real.negMulLog (spec l)
          ≤ Real.negMulLog ((1 - θ) * spec k + θ * spec l) := by
        have hj := negMulLog_jensen (m := 2) (k := 1)
          (w := fun i => if i = 0 then 1 - θ else θ)
          (x := fun i _ => if i = 0 then spec k else spec l)
          (fun i => by
            by_cases hi : i = 0
            · simp [hi]; linarith
            · simp [hi]; exact hθ0)
          (by simp [Fin.sum_univ_two])
          (fun i _ => by
            by_cases hi : i = 0
            · simp [hi]; exact hspec k
            · simp [hi]; exact hspec l) 0
        simpa [Fin.sum_univ_two] using hj
      rw [tTransformSpectrum_k, tTransformSpectrum_l]
      linarith
    have hsplit : (∑ j, Real.negMulLog (tTransformSpectrum spec θ k l j))
        - (∑ j, Real.negMulLog (spec j))
          = (Real.negMulLog (tTransformSpectrum spec θ k l l) - Real.negMulLog (spec l))
            + (Real.negMulLog (tTransformSpectrum spec θ k l k) - Real.negMulLog (spec k)) := by
      have hout : ∀ j, j ≠ k → j ≠ l →
          Real.negMulLog (tTransformSpectrum spec θ k l j) - Real.negMulLog (spec j) = 0 := by
        intro j hjk hjl
        rw [tTransformSpectrum_of_ne spec θ k l j hjk hjl]
        ring
      have hzero : ∀ j ∈ ((Finset.univ : Finset (Fin D)).erase k).erase l,
          Real.negMulLog (tTransformSpectrum spec θ k l j) - Real.negMulLog (spec j) = 0 := by
        intro j hj
        have hjmem : j ∈ (Finset.univ : Finset (Fin D)).erase k :=
          (Finset.mem_erase.mp hj).2
        have hjne_l : j ≠ l := (Finset.mem_erase.mp hj).1
        have hjne_k : j ≠ k := (Finset.mem_erase.mp hjmem).1
        exact hout j hjne_k hjne_l
      have hsum : (∑ j, (Real.negMulLog (tTransformSpectrum spec θ k l j)
          - Real.negMulLog (spec j)))
          = (Real.negMulLog (tTransformSpectrum spec θ k l l) - Real.negMulLog (spec l))
            + (Real.negMulLog (tTransformSpectrum spec θ k l k) - Real.negMulLog (spec k)) := by
        calc (∑ j, (Real.negMulLog (tTransformSpectrum spec θ k l j)
              - Real.negMulLog (spec j)))
            = (∑ j ∈ (Finset.univ : Finset (Fin D)).erase k,
                (Real.negMulLog (tTransformSpectrum spec θ k l j) - Real.negMulLog (spec j)))
              + (Real.negMulLog (tTransformSpectrum spec θ k l k) - Real.negMulLog (spec k)) := by
                symm
                exact Finset.sum_erase_add _ _ (Finset.mem_univ k)
          _ = (∑ j ∈ ((Finset.univ : Finset (Fin D)).erase k).erase l,
                (Real.negMulLog (tTransformSpectrum spec θ k l j) - Real.negMulLog (spec j)))
              + (Real.negMulLog (tTransformSpectrum spec θ k l l) - Real.negMulLog (spec l))
              + (Real.negMulLog (tTransformSpectrum spec θ k l k) - Real.negMulLog (spec k)) := by
                have h2 : (∑ j ∈ ((Finset.univ : Finset (Fin D)).erase k).erase l,
                    (Real.negMulLog (tTransformSpectrum spec θ k l j)
                      - Real.negMulLog (spec j)))
                  + (Real.negMulLog (tTransformSpectrum spec θ k l l) - Real.negMulLog (spec l))
                  = ∑ j ∈ (Finset.univ : Finset (Fin D)).erase k,
                    (Real.negMulLog (tTransformSpectrum spec θ k l j)
                      - Real.negMulLog (spec j)) :=
                  Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hkl', Finset.mem_univ l⟩)
                rw [h2]
          _ = (Real.negMulLog (tTransformSpectrum spec θ k l l) - Real.negMulLog (spec l))
              + (Real.negMulLog (tTransformSpectrum spec θ k l k) - Real.negMulLog (spec k)) := by
                rw [Finset.sum_eq_zero hzero]
                ring
      rw [← hsum]
      simp only [Finset.sum_sub_distrib]
    linarith [hsplit, hpair]

theorem branchMass_eq_norm (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (I : DiagonalInstrument D n) (i : Fin n) :
    (∑ j, ‖schmidtBranch ψ hψ I i j‖ ^ 2) = branchMass I (schmidtSpectrum ψ hψ) i := by
  have htrace : Matrix.trace (outerProduct (schmidtBranch ψ hψ I i))
      = ((branchMass I (schmidtSpectrum ψ hψ) i : ℝ) : ℂ) := by
    rw [← trace_partialTrace, branch_partialTrace]
    rw [Matrix.trace, Matrix.diag_diagonal]
    have h' : (∑ j : Fin D, ((I.entry i j ^ 2 * schmidtSpectrum ψ hψ j : ℝ) : ℂ))
        = ((∑ j, I.entry i j ^ 2 * schmidtSpectrum ψ hψ j : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sum]
    rw [h']
    rfl
  rw [trace_outerProduct] at htrace
  exact Complex.ofReal_inj.mp htrace

theorem tTransform_branchProbability (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j)
    (hpos : ∀ j, 0 < spec j) (hsum : (∑ j, spec j) = 1)
    (hspec : schmidtSpectrum ψ hψ = spec) :
    (∑ j, ‖schmidtBranch ψ hψ
        (tTransformInstrument D spec p θ k l hfilter hfilter0) 0 j‖ ^ 2) = p := by
  rw [branchMass_eq_norm]
  rw [hspec]
  exact tTransform_branchMass spec p θ k l hfilter hfilter0 hpos hsum

theorem tTransform_average_entropy_le (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j) :
    (∑ i, branchMass (tTransformInstrument D spec p θ k l hfilter hfilter0)
          (schmidtSpectrum ψ hψ) i
        * (∑ j, Real.negMulLog (branchSpectrum
            (tTransformInstrument D spec p θ k l hfilter hfilter0) (schmidtSpectrum ψ hψ) i j)))
      ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ :=
  diagonalInstrument_average_entropy_le_state ψ hψ
    (tTransformInstrument D spec p θ k l hfilter hfilter0)

def TTransformCriterion (D E : ℕ) (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D) : Prop :=
  (∀ j, 0 < spec j) ∧
  (∀ j, 0 ≤ tTransformFilter spec p θ k l j) ∧
  (∀ j, tTransformFilter spec p θ k l j ≤ 1) ∧
  (0 < p) ∧
  (∑ j, spec j) = 1 ∧
  (∀ (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ), schmidtSpectrum ψ hψ = spec →
    ∃ (I : DiagonalInstrument D 2),
      branchMass I spec 0 = p ∧
      branchSpectrum I spec 0 = tTransformSpectrum spec θ k l ∧
      (∀ j, PartialTrace (outerProduct (schmidtBranch ψ hψ I 0)) j j
        = ((p * tTransformSpectrum spec θ k l j : ℝ) : ℂ)) ∧
      (∑ j, Real.negMulLog (tTransformSpectrum spec θ k l j))
        ≥ (∑ j, Real.negMulLog (spec j)))

theorem tTransformCriterion (D E : ℕ) (spec : Fin D → ℝ) (p θ : ℝ) (k l : Fin D)
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j)
    (hpos : ∀ j, 0 < spec j) (hp : 0 < p) (hsum : (∑ j, spec j) = 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    TTransformCriterion D E spec p θ k l := by
  refine ⟨hpos, hfilter0, hfilter, hp, hsum, ?_⟩
  intro ψ hψ hspec
  refine ⟨tTransformInstrument D spec p θ k l hfilter hfilter0, ?_, ?_, ?_, ?_⟩
  · exact tTransform_branchMass spec p θ k l hfilter hfilter0 hpos hsum
  · exact tTransform_branchSpectrum spec p θ k l hfilter hfilter0 hpos hp hsum
  · intro j
    have hpt := tTransform_branch_partialTrace ψ hψ spec p θ k l hfilter hfilter0
      hpos hsum hspec
    rw [hpt]
    simp
  · exact tTransformSpectrum_entropy_ge spec θ k l (fun j => le_of_lt (hpos j)) hθ0 hθ1

theorem hermitian_eigenvalues_congr {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    hA.eigenvalues = hB.eigenvalues := by
  subst h
  rfl

theorem schmidtSpectrum_apply_tensorRight (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (V : Matrix (Fin E) (Fin E) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ)
    (hψ' : Normalized (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ)) :
    schmidtSpectrum (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ) hψ'
      = schmidtSpectrum ψ hψ := by
  unfold schmidtSpectrum
  have hmat : PartialTrace (outerProduct
      (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ))
      = PartialTrace (outerProduct ψ) :=
    partialTrace_outerProduct_apply_tensorRight ψ V hV
  have hL : (((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity
      (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ) hψ')).M).mat)
      = (((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M).mat) := by
    have e1 : (((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity
        (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ) hψ')).M).mat)
        = PartialTrace (outerProduct (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ)) := by
      show (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state _).m = _
      rw [Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state_m,
          Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity_val]
    have e2 : (((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M).mat)
        = PartialTrace (outerProduct ψ) := by
      show (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state _).m = _
      rw [Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state_m,
          Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity_val]
    rw [e1, e2, hmat]
  have hA : (((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity
      (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ) hψ')).M).mat).IsHermitian :=
    ((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity
      (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ) hψ')).M).H
  have hB : (((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M).mat).IsHermitian :=
    ((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)).M).H
  exact hermitian_eigenvalues_congr hA hB hL

end Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
