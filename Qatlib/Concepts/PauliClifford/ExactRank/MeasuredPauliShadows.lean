/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.MatrixTensor
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Observed Pauli measurements and fresh records

This module realizes single-qubit Pauli measurements as observed circuits through
`pauliAxisProgram`, then combines uniformly chosen axes with their Boolean outcomes in
`pauliShadowRecordInstrument` and `pauliRecordDist`. The explicit basis changes, projectors, and
Kraus operators connect matrix-level measurements to the record model used for classical shadows
[HuangKuengPreskill2020].

The product constructions `pauliProductDensity` and `pauliProductRecordKraus` identify Born
weights of fresh product-state measurements with independent record probabilities.
`pauliFreshResourceCounts` records the number of programs and the sums of their maximum leaf
gate, measurement, and query counts in the given circuit syntax.

## Main statements

* `pauli_axis_actual_leaf` identifies each selected observed leaf with its Pauli projector and
  recorded outcome.
* `pauli_record_kraus_and_mass` proves Kraus completeness and computes instrument branches and
  masses.
* `pauli_product_fresh_records` combines product-state normalization with independent record
  probabilities.
* `pauli_fresh_actual_resources` gives the resource tuple `(n, 2*n, n, 0)`.
* `pauliGroupedBornWeight_eq_probOf` factors grouped Born weights into block probabilities.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.InstrumentCore.Measurement

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.PauliClifford.ExactRank

open Matrix
open scoped ComplexOrder Kronecker

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-- The single-qubit basis change used to measure the selected Pauli axis: a normalized Hadamard
matrix for axis zero, its displayed complex variant for axis one, and the identity for axis
two. -/
noncomputable def pauliBasisMatrix (a : Fin 3) : Operator 2 :=
  if a = 0 then (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]
  else if a = 1 then (Real.sqrt 2 : ℂ)⁻¹ • !![1, -Complex.I; 1, Complex.I]
  else 1

/-- At axis zero, the basis-change matrix is `!![1, 1; 1, -1]` scaled by `1 / sqrt 2`. -/
@[simp] theorem pauliBasisMatrix_zero :
    pauliBasisMatrix 0 = (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1] := rfl

/-- At axis one, the basis-change matrix is `!![1, -Complex.I; 1, Complex.I]` scaled by `1 /
sqrt 2`. -/
@[simp] theorem pauliBasisMatrix_one :
    pauliBasisMatrix 1 = (Real.sqrt 2 : ℂ)⁻¹ • !![1, -Complex.I; 1, Complex.I] := rfl

/-- At axis two, the basis-change matrix is the identity. -/
@[simp] theorem pauliBasisMatrix_two : pauliBasisMatrix 2 = 1 := rfl

/-- The conjugate transpose times the unnormalized Hadamard matrix is twice the identity. -/
private theorem rawX_mul_self :
    (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![1, 1; 1, -1]
      = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> norm_num

/-- The conjugate transpose times the displayed unnormalized axis-one basis matrix is twice the
identity. -/
private theorem rawY_mul_self :
    (!![1, -Complex.I; 1, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        * !![1, -Complex.I; 1, Complex.I]
      = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> ring_nf

/-- Conjugating `pauliZ` by the unnormalized Hadamard matrix gives twice `pauliX`. -/
private theorem rawX_conj_z :
    (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * pauliZ * !![1, 1; 1, -1]
      = (2 : ℂ) • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> ring_nf

/-- Conjugating `pauliZ` by the displayed unnormalized axis-one basis matrix gives twice
`pauliY`. -/
private theorem rawY_conj_z :
    (!![1, -Complex.I; 1, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * pauliZ
        * !![1, -Complex.I; 1, Complex.I]
      = (2 : ℂ) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, pauliY, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> ring_nf

/-- A complex scalar fixed by conjugation can be pulled out unchanged from the
conjugate-transposed left matrix in a matrix product. -/
private theorem conjTranspose_smul_real_mul {c : ℂ} (hc : star c = c)
    {U V : Matrix (Fin 2) (Fin 2) ℂ} :
    ((c • U)ᴴ * V) = c • (Uᴴ * V) := by
  rw [Matrix.conjTranspose_smul, hc, Matrix.smul_mul]

/-- Every selected Pauli basis-change matrix belongs to the unitary group. -/
theorem pauliBasisMatrix_unitary (a : Fin 3) :
    pauliBasisMatrix a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  obtain ⟨i, hi⟩ := a
  interval_cases i
  · show (((Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
        * ((Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]) = 1
    rw [conjTranspose_smul_real_mul (by simp : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹),
      Matrix.mul_smul, rawX_mul_self, smul_smul, smul_smul, inv_sqrt2_mul_self]
    module
  · show (((Real.sqrt 2 : ℂ)⁻¹ • !![1, -Complex.I; 1, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
        * ((Real.sqrt 2 : ℂ)⁻¹ • !![1, -Complex.I; 1, Complex.I]) = 1
    rw [conjTranspose_smul_real_mul (by simp : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹),
      Matrix.mul_smul, rawY_mul_self, smul_smul, smul_smul, inv_sqrt2_mul_self]
    module
  · show ((1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * 1 = 1
    simp

/-- Conjugating `pauliZ` by the selected basis-change matrix gives the corresponding Pauli
matrix. -/
theorem pauliBasisMatrix_conj_z (a : Fin 3) :
    (pauliBasisMatrix a)ᴴ * pauliZ * pauliBasisMatrix a = pauliMatrix a := by
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 2⁻¹ := inv_sqrt2_mul_self
  obtain ⟨i, hi⟩ := a
  interval_cases i
  · show (((Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * pauliZ
        * ((Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]) = pauliX
    rw [Matrix.conjTranspose_smul]
    rw [show star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ from by simp]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, rawX_conj_z,
      smul_smul, hsq]
    module
  · show (((Real.sqrt 2 : ℂ)⁻¹ • !![1, -Complex.I; 1, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
        * pauliZ * ((Real.sqrt 2 : ℂ)⁻¹ • !![1, -Complex.I; 1, Complex.I]) = pauliY
    rw [Matrix.conjTranspose_smul]
    rw [show star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ from by simp]
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, rawY_conj_z,
      smul_smul, hsq]
    module
  · show ((1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * pauliZ * 1 = pauliZ
    simp

/-- Each of the three Pauli matrices equals its conjugate transpose. -/
theorem pauliMatrix_conjTranspose (a : Fin 3) : (pauliMatrix a)ᴴ = pauliMatrix a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

/-- Each of the three Pauli matrices squares to the identity. -/
theorem pauliMatrix_mul_self (a : Fin 3) : pauliMatrix a * pauliMatrix a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every Boolean-outcome Pauli projector equals its conjugate transpose. -/
theorem pauliProjector_conjTranspose (a : Fin 3) (b : Bool) :
    (PauliProjector a b)ᴴ = PauliProjector a b := by
  rw [PauliProjector, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, pauliMatrix_conjTranspose]
  have h1 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num [Complex.ofReal_div]]
    exact Complex.conj_ofReal _
  have h2 : star (if b then (1 : ℂ) else -1) = if b then (1 : ℂ) else -1 := by
    cases b <;> simp
  rw [h1, h2]

/-- Every Boolean-outcome Pauli projector is idempotent. -/
theorem pauliProjector_mul_self (a : Fin 3) (b : Bool) :
    PauliProjector a b * PauliProjector a b = PauliProjector a b := by
  set σ := pauliMatrix a
  set s : ℂ := if b then 1 else -1
  have hσ : σ * σ = 1 := pauliMatrix_mul_self a
  have hs : s * s = 1 := by
    cases b <;> simp [s]
  have hcore : (1 + s • σ) * (1 + s • σ) = (2 : ℂ) • (1 + s • σ) := by
    have e1 : (1 + s • σ) * (1 + s • σ) = 1 + s • σ + (s • σ + (s * s) • (σ * σ)) := by
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
    rw [e1, hs, hσ]
    module
  rw [PauliProjector]
  show (1 / 2 : ℂ) • (1 + s • σ) * ((1 / 2 : ℂ) • (1 + s • σ)) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcore]
  module

/-- For each Pauli axis, both outcome matrices are orthogonal projectors and their
conjugate-square sum is the identity. -/
theorem pauli_measurement_projectors (a : Fin 3) :
    (∀ b, IsOrthogonalProjector (PauliProjector a b)) ∧
      (∑ b : Bool, (PauliProjector a b)ᴴ * PauliProjector a b) = 1 := by
  refine ⟨fun b => ⟨pauliProjector_mul_self a b, pauliProjector_conjTranspose a b⟩, ?_⟩
  have : ∀ b : Bool, (PauliProjector a b)ᴴ * PauliProjector a b = PauliProjector a b :=
    fun b => by rw [pauliProjector_conjTranspose, pauliProjector_mul_self]
  rw [Finset.sum_congr rfl fun b _ => this b]
  exact pauliProjector_sum a

/-- The observed circuit that applies the selected basis change, measures in the computational
basis, applies the inverse basis change, and halts with output `true`. -/
noncomputable def pauliAxisProgram (a : Fin 3) : ObservedCircuit (Fin 2) :=
  .step (.gate (pauliBasisMatrix a))
    (.measure 2 id fun _ => .step (.gate (pauliBasisMatrix a)ᴴ) (.halt true))

/-- The observed Pauli-axis circuit has exactly two leaves. -/
theorem observedLeafCount_pauliAxisProgram (a : Fin 3) :
    observedLeafCount (pauliAxisProgram a) = 2 := by
  simp [pauliAxisProgram, observedLeafCount]

/-- The observed leaf list consists of the two conjugated computational-basis projectors in
outcome order zero then one. Each leaf has output `true`, zero queries, two gates, one
measurement, and its corresponding recorded outcome. -/
theorem observedKrausLeaves_pauliAxisProgram (a : Fin 3) :
    observedKrausLeaves 1 (pauliAxisProgram a) =
      [ ⟨(pauliBasisMatrix a)ᴴ * Projector {0} * pauliBasisMatrix a, true, 0, 2, 1,
          [(2, 0)]⟩,
        ⟨(pauliBasisMatrix a)ᴴ * Projector {1} * pauliBasisMatrix a, true, 0, 2, 1,
          [(2, 1)]⟩ ] := by
  simp [pauliAxisProgram, observedKrausLeaves, Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedKrausLeaf.prepend,
    List.ofFn_succ, List.ofFn_zero, Finset.filter_eq', Matrix.mul_assoc]

/-- The leaf index associated with a Boolean Pauli outcome, choosing leaf zero for `true` and
leaf one for `false`. -/
def pauliLeafIndex (a : Fin 3) (b : Bool) : Fin (observedLeafCount (pauliAxisProgram a)) :=
  if b then ⟨0, by rw [observedLeafCount_pauliAxisProgram]; norm_num⟩
  else ⟨1, by rw [observedLeafCount_pauliAxisProgram]; norm_num⟩

/-- Equal lists have equal elements at the same natural index after transporting the index bound
across the list equality. -/
private theorem list_get_congr {α : Type*} {l l' : List α} (h : l = l') (i : Fin l.length) :
    l.get i = l'.get ⟨i.val, by rw [← h]; exact i.isLt⟩ := by
  subst h
  rfl

/-- Leaf zero has the conjugated computational-basis-zero projector as its operator and records
outcome `(2, 0)`. It halts with output `true` after zero queries, two gates, and one
measurement. -/
theorem observedLeaf_pauliAxisProgram_zero (a : Fin 3)
    (h : 0 < observedLeafCount (pauliAxisProgram a)) :
    observedLeaf 1 (pauliAxisProgram a) ⟨0, h⟩ =
      ⟨(pauliBasisMatrix a)ᴴ * Projector {0} * pauliBasisMatrix a, true, 0, 2, 1,
        [(2, 0)]⟩ := by
  rw [observedLeaf]
  rw [show (Fin.cast _ ⟨0, h⟩ : Fin (observedKrausLeaves 1 (pauliAxisProgram a)).length)
      = ⟨0, by rw [observedKrausLeaves_length, observedLeafCount_pauliAxisProgram]; norm_num⟩ from rfl]
  rw [list_get_congr (observedKrausLeaves_pauliAxisProgram a)]
  rfl

/-- Leaf one has the conjugated computational-basis-one projector as its operator and records
outcome `(2, 1)`. It halts with output `true` after zero queries, two gates, and one
measurement. -/
theorem observedLeaf_pauliAxisProgram_one (a : Fin 3)
    (h : 1 < observedLeafCount (pauliAxisProgram a)) :
    observedLeaf 1 (pauliAxisProgram a) ⟨1, h⟩ =
      ⟨(pauliBasisMatrix a)ᴴ * Projector {1} * pauliBasisMatrix a, true, 0, 2, 1,
        [(2, 1)]⟩ := by
  rw [observedLeaf]
  rw [show (Fin.cast _ ⟨1, h⟩ : Fin (observedKrausLeaves 1 (pauliAxisProgram a)).length)
      = ⟨1, by rw [observedKrausLeaves_length, observedLeafCount_pauliAxisProgram]; norm_num⟩ from rfl]
  rw [list_get_congr (observedKrausLeaves_pauliAxisProgram a)]
  rfl

/-- The Pauli basis matrix is unitary, and the associated observed circuit is well formed with
two leaves. Every leaf uses zero queries, two gates, and one measurement. -/
theorem pauli_axis_program_legality_resources (a : Fin 3) :
    pauliBasisMatrix a ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      observedWellFormed (pauliAxisProgram a) ∧ observedLeafCount (pauliAxisProgram a) = 2 ∧
      (∀ i : Fin (observedLeafCount (pauliAxisProgram a)), (observedLeaf 1 (pauliAxisProgram a) i).queries=0 ∧ (observedLeaf 1 (pauliAxisProgram a) i).gates=2 ∧ (observedLeaf 1 (pauliAxisProgram a) i).measurements=1) := by
  have hB := pauliBasisMatrix_unitary a
  have hBH : (pauliBasisMatrix a)ᴴ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have h2 := Matrix.mem_unitaryGroup_iff.mp hB
    rw [Matrix.star_eq_conjTranspose] at h2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  refine ⟨hB, ?_, observedLeafCount_pauliAxisProgram a, ?_⟩
  · exact ⟨hB, fun _ => ⟨hBH, trivial⟩⟩
  · intro i
    have hmem : observedLeaf 1 (pauliAxisProgram a) i
        ∈ observedKrausLeaves 1 (pauliAxisProgram a) := List.get_mem _ _
    rw [observedKrausLeaves_pauliAxisProgram] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h0 | h1
    · rw [h0]; exact ⟨rfl, rfl, rfl⟩
    · rw [h1]; exact ⟨rfl, rfl, rfl⟩

/-- The computational-basis-zero projector is `(1 + pauliZ) / 2`. -/
theorem projector_zero_eq : Projector ({0} : Finset (Fin 2))
    = (1 / 2 : ℂ) • (1 + pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Projector, pauliZ, Matrix.smul_apply, Matrix.add_apply]

/-- The computational-basis-one projector is `(1 - pauliZ) / 2`. -/
theorem projector_one_eq : Projector ({1} : Finset (Fin 2))
    = (1 / 2 : ℂ) • (1 + (-1 : ℂ) • pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Projector, pauliZ, Matrix.smul_apply, Matrix.add_apply]

/-- Conjugating the computational-basis projector selected by the Boolean outcome gives
`PauliProjector a b`, with `true` selecting basis index zero. -/
theorem axis_leaf_operator (a : Fin 3) (b : Bool) :
    (pauliBasisMatrix a)ᴴ * Projector {if b then (0 : Fin 2) else 1} * pauliBasisMatrix a
      = PauliProjector a b := by
  have hun : (pauliBasisMatrix a)ᴴ * pauliBasisMatrix a = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp (pauliBasisMatrix_unitary a)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcz := pauliBasisMatrix_conj_z a
  cases b with
  | false =>
    show (pauliBasisMatrix a)ᴴ * Projector ({1} : Finset (Fin 2)) * pauliBasisMatrix a
        = PauliProjector a false
    calc (pauliBasisMatrix a)ᴴ * Projector ({1} : Finset (Fin 2)) * pauliBasisMatrix a
        = (1 / 2 : ℂ) • ((pauliBasisMatrix a)ᴴ * (1 + (-1 : ℂ) • pauliZ)
            * pauliBasisMatrix a) := by
          rw [projector_one_eq, Matrix.mul_smul, Matrix.smul_mul]
      _ = (1 / 2 : ℂ) • (1 + (-1 : ℂ) • pauliMatrix a) := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
            Matrix.smul_mul, hun, hcz]
      _ = PauliProjector a false := rfl
  | true =>
    show (pauliBasisMatrix a)ᴴ * Projector ({0} : Finset (Fin 2)) * pauliBasisMatrix a
        = PauliProjector a true
    calc (pauliBasisMatrix a)ᴴ * Projector ({0} : Finset (Fin 2)) * pauliBasisMatrix a
        = (1 / 2 : ℂ) • ((pauliBasisMatrix a)ᴴ * (1 + pauliZ) * pauliBasisMatrix a) := by
          rw [projector_zero_eq, Matrix.mul_smul, Matrix.smul_mul]
      _ = (1 / 2 : ℂ) • (1 + pauliMatrix a) := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hun, hcz]
      _ = PauliProjector a true := by
          rw [PauliProjector]
          simp only [if_true, one_smul]

/-- The leaf selected by `pauliLeafIndex a b` has operator `PauliProjector a b` and records `(2,
0)` for `true` or `(2, 1)` for `false`. -/
theorem pauli_axis_actual_leaf (a : Fin 3) (b : Bool) :
    (observedLeaf 1 (pauliAxisProgram a) (pauliLeafIndex a b)).operator = PauliProjector a b ∧
      (observedLeaf 1 (pauliAxisProgram a) (pauliLeafIndex a b)).outcomes = [(2, if b then 0 else 1)] := by
  cases b with
  | false =>
    have hleaf : observedLeaf 1 (pauliAxisProgram a) (pauliLeafIndex a false)
        = ⟨(pauliBasisMatrix a)ᴴ * Projector {1} * pauliBasisMatrix a, true, 0, 2, 1,
            [(2, 1)]⟩ := by
      rw [observedLeaf]
      rw [show (Fin.cast _ (pauliLeafIndex a false) :
            Fin (observedKrausLeaves 1 (pauliAxisProgram a)).length)
          = ⟨1, by rw [observedKrausLeaves_length, observedLeafCount_pauliAxisProgram]; norm_num⟩ from rfl]
      rw [list_get_congr (observedKrausLeaves_pauliAxisProgram a)]
      rfl
    rw [hleaf]
    exact ⟨axis_leaf_operator a false, rfl⟩
  | true =>
    have hleaf : observedLeaf 1 (pauliAxisProgram a) (pauliLeafIndex a true)
        = ⟨(pauliBasisMatrix a)ᴴ * Projector {0} * pauliBasisMatrix a, true, 0, 2, 1,
            [(2, 0)]⟩ := by
      rw [observedLeaf]
      rw [show (Fin.cast _ (pauliLeafIndex a true) :
            Fin (observedKrausLeaves 1 (pauliAxisProgram a)).length)
          = ⟨0, by rw [observedKrausLeaves_length, observedLeafCount_pauliAxisProgram]; norm_num⟩ from rfl]
      rw [list_get_congr (observedKrausLeaves_pauliAxisProgram a)]
      rfl
    rw [hleaf]
    exact ⟨axis_leaf_operator a true, rfl⟩

/-- The Kraus operator for an axis-outcome record, given by its Pauli projector scaled by `sqrt
(1 / 3)`. -/
noncomputable def pauliRecordKraus (o : Fin 3 × Bool) : Operator 2 :=
  (Real.sqrt (1 / 3) : ℂ) • PauliProjector o.1 o.2

/-- The complex coercion of `sqrt (1 / 3)` multiplied by itself equals `1 / 3`. -/
theorem sqrt_third_mul_self :
    ((Real.sqrt (1 / 3) : ℂ)) * ((Real.sqrt (1 / 3) : ℂ)) = 1 / 3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)]
  norm_num [Complex.ofReal_div]

/-- The conjugate square of a record Kraus operator is one third of the corresponding Pauli
projector. -/
theorem pauliRecordKraus_conj_mul (o : Fin 3 × Bool) :
    (pauliRecordKraus o)ᴴ * pauliRecordKraus o = (1 / 3 : ℂ) • PauliProjector o.1 o.2 := by
  rw [pauliRecordKraus, Matrix.conjTranspose_smul]
  rw [show star (Real.sqrt (1 / 3) : ℂ) = (Real.sqrt (1 / 3) : ℂ) from by
    simp [Complex.conj_ofReal]]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt_third_mul_self,
    pauliProjector_conjTranspose, pauliProjector_mul_self]

/-- The six axis-outcome Kraus operators satisfy the completeness relation: their conjugate
squares sum to the identity. -/
theorem pauliRecordKraus_complete :
    ∑ o : Fin 3 × Bool, (pauliRecordKraus o)ᴴ * pauliRecordKraus o = 1 := by
  calc ∑ o : Fin 3 × Bool, (pauliRecordKraus o)ᴴ * pauliRecordKraus o
      = ∑ o : Fin 3 × Bool, (1 / 3 : ℂ) • PauliProjector o.1 o.2 :=
        Finset.sum_congr rfl fun o _ => pauliRecordKraus_conj_mul o
    _ = ∑ a : Fin 3, ∑ b : Bool, (1 / 3 : ℂ) • PauliProjector a b :=
        Fintype.sum_prod_type' (fun a b => (1 / 3 : ℂ) • PauliProjector a b)
    _ = ∑ a : Fin 3, (1 / 3 : ℂ) • (1 : Operator 2) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.smul_sum, pauliProjector_sum]
    _ = (1 / 3 : ℂ) • ∑ a : Fin 3, (1 : Operator 2) := by
        rw [← Finset.smul_sum]
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul]
        module

/-- The six-outcome quantum instrument constructed from the complete family of Pauli record
Kraus operators. -/
noncomputable def pauliShadowRecordInstrument : Instrument (Fin 3 × Bool) 2 2 :=
  Instrument.ofKraus pauliRecordKraus pauliRecordKraus_complete

/-- The record Kraus family is complete, and each instrument branch is conjugation by its record
Kraus operator. Its mass is one third of the real trace of the corresponding Pauli projector
times the input matrix. -/
theorem pauli_record_kraus_and_mass :
    (∑ o : Fin 3 × Bool, (pauliRecordKraus o)ᴴ * pauliRecordKraus o) = 1 ∧
      (∀ (ρ : Operator 2) (o : Fin 3 × Bool), pauliShadowRecordInstrument.branch o ρ = conjBranch (pauliRecordKraus o) ρ ∧
        instrumentProb pauliShadowRecordInstrument ρ o = (1/3) * (Matrix.trace (PauliProjector o.1 o.2 * ρ)).re) := by
  refine ⟨pauliRecordKraus_complete, fun ρ o => ⟨rfl, ?_⟩⟩
  have htrace : Matrix.trace (pauliRecordKraus o * ρ * (pauliRecordKraus o)ᴴ)
      = (1 / 3 : ℂ) * Matrix.trace (PauliProjector o.1 o.2 * ρ) := by
    rw [pauliRecordKraus, Matrix.conjTranspose_smul]
    rw [show star (Real.sqrt (1 / 3) : ℂ) = (Real.sqrt (1 / 3) : ℂ) from by
      simp [Complex.conj_ofReal]]
    rw [pauliProjector_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, sqrt_third_mul_self, Matrix.trace_smul, smul_eq_mul]
    rw [Matrix.trace_mul_cycle, pauliProjector_mul_self]
  have hmain : instrumentProb pauliShadowRecordInstrument ρ o
      = ((1 / 3 : ℂ) * Matrix.trace (PauliProjector o.1 o.2 * ρ)).re := by
    show (Matrix.trace (pauliShadowRecordInstrument.branch o ρ)).re = _
    rw [show pauliShadowRecordInstrument.branch o ρ
        = pauliRecordKraus o * ρ * (pauliRecordKraus o)ᴴ from rfl, htrace]
  rw [hmain]
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by norm_num [Complex.ofReal_div]]
  simp [Complex.mul_re]

/-- The finite distribution on axis-outcome records obtained by applying
`pauliShadowRecordInstrument` to the supplied density operator. -/
noncomputable def pauliRecordDist (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    FinDist (Fin 3 × Bool) where
  prob o := instrumentProb pauliShadowRecordInstrument ρ o
  nonneg o := instrumentProb_nonneg _ hρ.1 o
  sum_one := sum_instrumentProb_isDensityOperator _ hρ

/-- Each record probability equals its instrument probability, and the probabilities of the two
outcomes of any fixed axis sum to one third. -/
theorem pauli_record_dist_physical (ρ : Operator 2) (hρ : IsDensityOperator ρ) (a : Fin 3) (b : Bool) :
    (pauliRecordDist ρ hρ).prob (a, b) = instrumentProb pauliShadowRecordInstrument ρ (a, b) ∧
      (∑ b : Bool, (pauliRecordDist ρ hρ).prob (a, b)) = 1/3 := by
  refine ⟨rfl, ?_⟩
  have h1 : ∀ b : Bool, (pauliRecordDist ρ hρ).prob (a, b)
      = (1/3) * (Matrix.trace (PauliProjector a b * ρ)).re :=
    fun b => (pauli_record_kraus_and_mass.2 ρ (a, b)).2
  rw [Finset.sum_congr rfl fun b _ => h1 b, ← Finset.mul_sum]
  have htr : (∑ b : Bool, (Matrix.trace (PauliProjector a b * ρ)).re) = 1 := by
    rw [← Complex.re_sum]
    have h2 : (∑ b : Bool, Matrix.trace (PauliProjector a b * ρ)) = Matrix.trace ρ := by
      rw [← Matrix.trace_sum, ← Finset.sum_mul, pauliProjector_sum, Matrix.one_mul]
    rw [h2, hρ.2]
    rfl
  rw [htr, mul_one]

/-- The single-qubit observable with real identity coefficient `c` and real Pauli coefficients
`θ`. -/
noncomputable def pauliObservable (c : ℝ) (θ : Fin 3 → ℝ) : Operator 2 :=
  (c : ℂ) • 1 + ∑ a : Fin 3, (θ a : ℂ) • pauliMatrix a

/-- The real snapshot estimate `c + 3 * s * θ a` for record `(a, b)`, where `s` is one for
`true` and minus one for `false`. -/
def pauliSnapshotValue (c : ℝ) (θ : Fin 3 → ℝ) (o : Fin 3 × Bool) : ℝ :=
  c + 3 * (if o.2 then 1 else -1) * θ o.1

/-- The matrix on Boolean registers formed by multiplying the entries of the local Kraus
operators specified by the record tuple. -/
noncomputable def pauliProductRecordKraus {n : ℕ} (ω : Fin n → Fin 3 × Bool) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y =>
    ∏ i, (pauliRecordKraus (ω i)) (boolEquivFin2 (x i)) (boolEquivFin2 (y i))

/-- The equivalence that separates a Boolean register of length `n + 1` into its first `n` bits
and its final bit represented in `Fin 2`. -/
def regProdEquiv (n : ℕ) : Reg (n + 1) ≃ Reg n × Fin 2 :=
  (regSuccEquiv n).trans (Equiv.prodCongr (Equiv.refl _) boolEquivFin2)

/-- Pulling back both indices of a square matrix along an equivalence preserves its trace. -/
private theorem trace_submatrix_of_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (σ : ι ≃ κ) (M : Matrix κ κ ℂ) :
    Matrix.trace (M.submatrix σ σ) = Matrix.trace M := by
  show ∑ i, M (σ i) (σ i) = ∑ k, M k k
  exact Equiv.sum_comp σ (fun k => M k k)

/-- An entrywise product matrix on `n + 1` Boolean coordinates is the Kronecker product of the
first `n` factors and the final factor, pulled back along `regProdEquiv`. -/
private theorem prodEntryMatrix_succ {n : ℕ} (M : Fin (n + 1) → Operator 2) :
    (Matrix.of fun x y => ∏ i, (M i) (boolEquivFin2 (x i)) (boolEquivFin2 (y i)) :
        Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      = (((Matrix.of fun x y => ∏ i, (M (Fin.castAdd 1 i)) (boolEquivFin2 (x i))
              (boolEquivFin2 (y i))) : Matrix (Reg n) (Reg n) ℂ) ⊗ₖ
          (M (Fin.natAdd n 0))).submatrix (regProdEquiv n) (regProdEquiv n) := by
  ext x y
  have hfst : ∀ i : Fin n, (regProdEquiv n x).1 i = x (Fin.castAdd 1 i) := fun i => rfl
  have hsnd : (regProdEquiv n x).2 = boolEquivFin2 (x (Fin.natAdd n 0)) := rfl
  have hfsty : ∀ i : Fin n, (regProdEquiv n y).1 i = y (Fin.castAdd 1 i) := fun i => rfl
  have hsndy : (regProdEquiv n y).2 = boolEquivFin2 (y (Fin.natAdd n 0)) := rfl
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
    hfst, hfsty, hsnd, hsndy]
  rw [Fin.prod_univ_add, Fin.prod_univ_one]

/-- The product matrix on `n + 1` coordinates decomposes into the Kronecker product of its first
`n` factors and its final factor after reindexing by `regProdEquiv`. -/
theorem pauliProductDensity_succ {n : ℕ} (ρ : Fin (n + 1) → Operator 2) :
    pauliProductDensity ρ
      = ((pauliProductDensity (fun i => ρ (Fin.castAdd 1 i)) ⊗ₖ
          ρ (Fin.natAdd n 0))).submatrix (regProdEquiv n) (regProdEquiv n) :=
  prodEntryMatrix_succ ρ

/-- The product record Kraus matrix on `n + 1` coordinates decomposes into its first `n`
coordinates and its final local Kraus operator through a reindexed Kronecker product. -/
theorem pauliProductRecordKraus_succ {n : ℕ} (ω : Fin (n + 1) → Fin 3 × Bool) :
    pauliProductRecordKraus ω
      = ((pauliProductRecordKraus (fun i => ω (Fin.castAdd 1 i)) ⊗ₖ
          pauliRecordKraus (ω (Fin.natAdd n 0)))).submatrix (regProdEquiv n) (regProdEquiv n) :=
  prodEntryMatrix_succ (fun i => pauliRecordKraus (ω i))

/-- The product matrix of an empty family is the identity on the zero-bit register. -/
private theorem pauliProductDensity_zero (ρ : Fin 0 → Operator 2) :
    pauliProductDensity ρ = 1 := by
  ext x y
  rw [show x = y from Subsingleton.elim x y]
  simp [pauliProductDensity, Matrix.one_apply_eq]

/-- The product Kraus matrix of an empty record tuple is the identity on the zero-bit register. -/
private theorem pauliProductRecordKraus_zero (ω : Fin 0 → Fin 3 × Bool) :
    pauliProductRecordKraus ω = 1 := by
  ext x y
  rw [show x = y from Subsingleton.elim x y]
  simp [pauliProductRecordKraus, Matrix.one_apply_eq]

/-- If every local factor is a density operator, the product matrix is positive semidefinite and
has trace one. -/
theorem pauliProductDensity_isDensity {n : ℕ} (ρ : Fin n → Operator 2)
    (hρ : ∀ i, IsDensityOperator (ρ i)) :
    (pauliProductDensity ρ).PosSemidef ∧ Matrix.trace (pauliProductDensity ρ) = 1 := by
  induction n with
  | zero =>
    rw [pauliProductDensity_zero ρ]
    exact ⟨Matrix.PosSemidef.one, by simp [Matrix.trace_one]⟩
  | succ n ih =>
    rw [pauliProductDensity_succ ρ]
    have ih' := ih (fun i => ρ (Fin.castAdd 1 i)) (fun i => hρ (Fin.castAdd 1 i))
    have hlast := hρ (Fin.natAdd n 0)
    refine ⟨(Matrix.posSemidef_submatrix_equiv _).mpr
      (Matrix.PosSemidef.kronecker ih'.1 hlast.1), ?_⟩
    rw [trace_submatrix_of_equiv, Matrix.trace_kronecker, ih'.2, hlast.2, mul_one]

/-- For a single-qubit density operator, the complex trace of a record Kraus branch equals the
real instrument probability coerced to the complex numbers. -/
theorem trace_productRecordKraus_single (σ : Operator 2) (hσ : IsDensityOperator σ)
    (o : Fin 3 × Bool) :
    Matrix.trace (pauliRecordKraus o * σ * (pauliRecordKraus o)ᴴ)
      = ((instrumentProb pauliShadowRecordInstrument σ o : ℝ) : ℂ) := by
  have hpsd : (pauliRecordKraus o * σ * (pauliRecordKraus o)ᴴ).PosSemidef := by
    have h := (completelyPositive_conjBranch (pauliRecordKraus o)).positive hσ.1
    rwa [conjBranch_apply] at h
  have him : (Matrix.trace (pauliRecordKraus o * σ * (pauliRecordKraus o)ᴴ)).im = 0 :=
    (RCLike.nonneg_iff.mp hpsd.trace_nonneg).2
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩
  · rw [Complex.ofReal_re]
    rfl
  · rw [him]
    rfl

/-- For a product of local density operators, the real trace of the joint record Kraus branch
equals the probability of that record tuple under the independent local record laws. -/
theorem pauliProductRecordKraus_trace {n : ℕ} (ρ : Fin n → Operator 2)
    (hρ : ∀ i, IsDensityOperator (ρ i)) (ω : Fin n → Fin 3 × Bool) :
    (Matrix.trace (pauliProductRecordKraus ω * pauliProductDensity ρ
        * (pauliProductRecordKraus ω)ᴴ)).re
      = (independentSampleLaw (fun i => pauliRecordDist (ρ i) (hρ i))).prob ω := by
  induction n with
  | zero =>
    rw [pauliProductRecordKraus_zero ω, pauliProductDensity_zero ρ, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
    have hRHS : (independentSampleLaw (fun i => pauliRecordDist (ρ i) (hρ i))).prob ω = 1 := by
      show (∏ i : Fin 0, (pauliRecordDist (ρ i) (hρ i)).prob (ω i)) = 1
      simp
    rw [hRHS]
    simp [Matrix.trace_one]
  | succ n ih =>
    rw [pauliProductRecordKraus_succ ω, pauliProductDensity_succ ρ,
      Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      trace_submatrix_of_equiv, Matrix.trace_kronecker]
    have htail := ih (fun i => ρ (Fin.castAdd 1 i)) (fun i => hρ (Fin.castAdd 1 i))
      (fun i => ω (Fin.castAdd 1 i))
    have hlast := trace_productRecordKraus_single (ρ (Fin.natAdd n 0)) (hρ (Fin.natAdd n 0))
      (ω (Fin.natAdd n 0))
    rw [hlast]
    rw [show ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).re = z.re * r from fun z r => by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]]
    rw [htail]
    show (∏ i : Fin n, (pauliRecordDist (ρ (Fin.castAdd 1 i)) (hρ (Fin.castAdd 1 i))).prob
          (ω (Fin.castAdd 1 i))) *
        (pauliRecordDist (ρ (Fin.natAdd n 0)) (hρ (Fin.natAdd n 0))).prob (ω (Fin.natAdd n 0))
      = ∏ i : Fin (n + 1), (pauliRecordDist (ρ i) (hρ i)).prob (ω i)
    rw [Fin.prod_univ_add, Fin.prod_univ_one]

/-- The product of local density operators is positive semidefinite with trace one, and each
joint record Born weight equals its probability under the independent local record laws. -/
theorem pauli_product_fresh_records {n : ℕ} (ρ : Fin n → Operator 2)
    (hρ : ∀ i, IsDensityOperator (ρ i)) (ω : Fin n → Fin 3 × Bool) :
    (pauliProductDensity ρ).PosSemidef ∧ Matrix.trace (pauliProductDensity ρ) = 1 ∧
      (Matrix.trace (pauliProductRecordKraus ω * pauliProductDensity ρ * (pauliProductRecordKraus ω)ᴴ)).re =
        (independentSampleLaw (fun i => pauliRecordDist (ρ i) (hρ i))).prob ω :=
  ⟨(pauliProductDensity_isDensity ρ hρ).1, (pauliProductDensity_isDensity ρ hρ).2,
    pauliProductRecordKraus_trace ρ hρ ω⟩

/-- The maximum of a natural-valued statistic over the observed Kraus leaves of a circuit,
computed by folding from zero. -/
noncomputable def leafMaxOf (prog : ObservedCircuit (Fin 2)) (f : ObservedKrausLeaf 2 → ℕ) : ℕ :=
  (observedKrausLeaves 1 prog).foldl (fun m leaf => max m (f leaf)) 0

/-- For every axis, the maximum leaf counts of the observed Pauli program are two gates, one
measurement, and zero queries. -/
theorem leafMaxOf_pauliAxisProgram (a : Fin 3) :
    leafMaxOf (pauliAxisProgram a) ObservedKrausLeaf.gates = 2 ∧
    leafMaxOf (pauliAxisProgram a) ObservedKrausLeaf.measurements = 1 ∧
    leafMaxOf (pauliAxisProgram a) ObservedKrausLeaf.queries = 0 := by
  rw [leafMaxOf, leafMaxOf, leafMaxOf, observedKrausLeaves_pauliAxisProgram]
  exact ⟨rfl, rfl, rfl⟩

/-- The tuple containing the number of selected Pauli-axis programs and the sums of their
maximum leaf gate, measurement, and query counts. -/
noncomputable def pauliFreshResourceCounts {n : ℕ} (axes : Fin n → Fin 3) : ℕ × ℕ × ℕ × ℕ :=
  let progs := List.ofFn (fun i => pauliAxisProgram (axes i))
  (progs.length,
    (progs.map fun prog => leafMaxOf prog ObservedKrausLeaf.gates).sum,
    (progs.map fun prog => leafMaxOf prog ObservedKrausLeaf.measurements).sum,
    (progs.map fun prog => leafMaxOf prog ObservedKrausLeaf.queries).sum)

/-- For `n` selected axes, the resource tuple is `(n, 2*n, n, 0)`: `n` programs, `2*n` gates,
`n` measurements, and zero queries in the given circuit syntax. -/
theorem pauli_fresh_actual_resources {n : ℕ} (axes : Fin n → Fin 3) :
    pauliFreshResourceCounts axes = (n, 2*n, n, 0) := by
  have hg : ∀ i : Fin n, leafMaxOf (pauliAxisProgram (axes i)) ObservedKrausLeaf.gates = 2 :=
    fun i => (leafMaxOf_pauliAxisProgram (axes i)).1
  have hm : ∀ i : Fin n, leafMaxOf (pauliAxisProgram (axes i)) ObservedKrausLeaf.measurements = 1 :=
    fun i => (leafMaxOf_pauliAxisProgram (axes i)).2.1
  have hq : ∀ i : Fin n, leafMaxOf (pauliAxisProgram (axes i)) ObservedKrausLeaf.queries = 0 :=
    fun i => (leafMaxOf_pauliAxisProgram (axes i)).2.2
  simp only [pauliFreshResourceCounts, List.length_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, hg, hm, hq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp [mul_comm, mul_one, mul_zero]

/-- The real Born weight of a `K` by `L` record array measured on `K * L` copies of the input
matrix, with indices flattened using `finProdFinEquiv`. -/
noncomputable def pauliGroupedBornWeight {K L : ℕ} (ρ : Operator 2)
    (ω : Fin K → Fin L → Fin 3 × Bool) : ℝ :=
  (Matrix.trace (pauliProductRecordKraus (fun t : Fin (K * L) =>
      ω (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
    * pauliProductDensity (fun _ : Fin (K * L) => ρ)
    * (pauliProductRecordKraus (fun t : Fin (K * L) =>
      ω (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2))ᴴ)).re

/-- For a density operator, the grouped Born weight equals the product over blocks of their
independent record-sequence probabilities. -/
theorem pauliGroupedBornWeight_eq_probOf {K L : ℕ} (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (ω : Fin K → Fin L → Fin 3 × Bool) :
    pauliGroupedBornWeight ρ ω = ∏ k, (pauliRecordDist ρ hρ).probOf (ω k) := by
  rw [pauliGroupedBornWeight, (pauli_product_fresh_records (fun _ : Fin (K*L) => ρ)
    (fun _ => hρ)
    (fun t : Fin (K*L) => ω (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)).2.2]
  show (∏ t : Fin (K * L), (pauliRecordDist ρ hρ).prob
      (ω (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)) = _
  rw [Equiv.prod_comp finProdFinEquiv.symm
    (fun p => (pauliRecordDist ρ hρ).prob (ω p.1 p.2)), Fintype.prod_prod_type]
  rfl

end Qatlib.Concepts.PauliClifford.ExactRank
