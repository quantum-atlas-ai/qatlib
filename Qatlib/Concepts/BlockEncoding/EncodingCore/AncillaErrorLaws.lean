/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Independent ancillas and block-encoding products

`independentLiftLeft` and `independentLiftRight` extend two operators to separate ancilla
registers sharing one data register. Their compressed product equals the product of the original
compressions, and each lift preserves unitarity.

`independent_ancilla_blockEncoding_product` propagates normalization and approximation errors
through multiplication. `encodingProductCircuit` realizes the lifted product using two gates.

For background, see [GilyenSuLowWiebe2019].

## Main statements

* `independent_ancilla_lift_laws`: combines isometry, unitarity, and exact compression
  identities.
* `independent_ancilla_blockEncoding_product`: gives scale `α * β` and error `β * ε + α * η + ε
  * η`.
* `encoding_product_run_cost`: verifies the circuit action and its two-gate, zero-query cost.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Concepts.BlockEncoding.EncodingCore

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open scoped Matrix.Norms.L2Operator

variable {J K I : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I]

/-- Lifts an operator on the first ancilla and data registers while acting as identity on the
second ancilla. -/
def independentLiftLeft (U : Matrix (J × I) (J × I) ℂ) : Matrix ((J × K) × I) ((J × K) × I) ℂ :=
  Matrix.of fun x y => U (x.1.1, x.2) (y.1.1, y.2) * (if x.1.2 = y.1.2 then 1 else 0)

/-- Lifts an operator on the second ancilla and data registers while acting as identity on the
first ancilla. -/
def independentLiftRight (V : Matrix (K × I) (K × I) ℂ) : Matrix ((J × K) × I) ((J × K) × I) ℂ :=
  Matrix.of fun x y => (if x.1.1 = y.1.1 then 1 else 0) * V (x.1.2, x.2) (y.1.2, y.2)

/-- Reorders the first ancilla, data, and second ancilla into the joint ancilla-data index type. -/
private def liftLeftEquiv : (J × I) × K ≃ (J × K) × I where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun y := ((y.1.1, y.2), y.1.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Reassociates the first ancilla with the second-ancilla and data pair into the joint index
type. -/
private def liftRightEquiv : J × (K × I) ≃ (J × K) × I where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun y := (y.1.1, (y.1.2, y.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

omit [Fintype J] [DecidableEq J] [Fintype K] [Fintype I] [DecidableEq I] in

/-- The left independent lift is a relabeled tensor product of `U` with identity. -/
theorem independentLiftLeft_eq (U : Matrix (J × I) (J × I) ℂ) :
    independentLiftLeft U = relabelGate liftLeftEquiv (TensorGate U (1 : Matrix K K ℂ)) := rfl

omit [Fintype J] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] in

/-- The right independent lift is a relabeled tensor product of identity with `V`. -/
theorem independentLiftRight_eq (V : Matrix (K × I) (K × I) ℂ) :
    independentLiftRight V = relabelGate liftRightEquiv (TensorGate (1 : Matrix J J ℂ) V) := rfl

/-- Relabeling a unitary matrix along an equivalence preserves unitarity. -/
theorem relabelGate_mem_unitary {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T]
    [DecidableEq T] {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ) (e : S ≃ T) :
    relabelGate e U ∈ Matrix.unitaryGroup T ℂ := by
  have hu : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
  have hu' : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hmul : ∀ A B : Matrix S S ℂ, relabelGate e (A * B) = relabelGate e A * relabelGate e B := by
    intro A B
    ext i j
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact (e.symm.sum_comp fun k => A (e.symm i) k * B k (e.symm j)).symm
  have hstar : ∀ A : Matrix S S ℂ, (relabelGate e A)ᴴ = relabelGate e Aᴴ := by
    intro A
    ext i j
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  have hone : relabelGate e (1 : Matrix S S ℂ) = 1 := by
    ext i j
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
      e.symm.injective.eq_iff]
  constructor
  · rw [Matrix.star_eq_conjTranspose, hstar, ← hmul, hu', hone]
  · rw [Matrix.star_eq_conjTranspose, hstar, ← hmul, hu, hone]

/-- The left independent lift of a unitary matrix is unitary. -/
theorem independentLiftLeft_unitary {U : Matrix (J × I) (J × I) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ) :
    independentLiftLeft U ∈ Matrix.unitaryGroup ((J × K) × I) ℂ := by
  rw [independentLiftLeft_eq]
  exact relabelGate_mem_unitary (tensorGate_unitary hU (Matrix.unitaryGroup K ℂ).one_mem)
    liftLeftEquiv

/-- The right independent lift of a unitary matrix is unitary. -/
theorem independentLiftRight_unitary {V : Matrix (K × I) (K × I) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (K × I) ℂ) :
    independentLiftRight V ∈ Matrix.unitaryGroup ((J × K) × I) ℂ := by
  rw [independentLiftRight_eq]
  exact relabelGate_mem_unitary (tensorGate_unitary (Matrix.unitaryGroup J ℂ).one_mem hV)
    liftRightEquiv

omit [DecidableEq I] in

/-- At fixed ancilla values, the matrix product of independent lifts reduces to the product sum
over the shared data register. -/
theorem independent_lift_mul_apply (j₀ : J) (k₀ : K) (U : Matrix (J × I) (J × I) ℂ)
    (V : Matrix (K × I) (K × I) ℂ) (i₁ i₂ : I) :
    ∑ z : (J × K) × I,
        independentLiftLeft U ((j₀, k₀), i₁) z * independentLiftRight V z ((j₀, k₀), i₂)
      = ∑ s : I, U (j₀, i₁) (j₀, s) * V (k₀, s) (k₀, i₂) := by
  have hkey : ∀ z : (J × K) × I,
      independentLiftLeft U ((j₀, k₀), i₁) z * independentLiftRight V z ((j₀, k₀), i₂)
        = (if z.1 = (j₀, k₀) then (1 : ℂ) else 0)
            * (U (j₀, i₁) (z.1.1, z.2) * V (z.1.2, z.2) (k₀, i₂)) := by
    intro z
    obtain ⟨⟨a, b⟩, t⟩ := z
    by_cases hab : (a, b) = (j₀, k₀)
    · obtain ⟨ha, hb⟩ := Prod.ext_iff.mp hab
      subst ha
      subst hb
      simp [independentLiftLeft, independentLiftRight]
    · rw [ite_eq_right hab]
      by_cases ha : a = j₀
      · have hb : ¬(b = k₀) := fun h => hab (by rw [ha, h])
        have hne : ¬(k₀ = b) := fun h => hb h.symm
        simp only [independentLiftLeft, independentLiftRight, Matrix.of_apply, ite_eq_left ha,
          ite_eq_right hne]
        ring
      · simp only [independentLiftLeft, independentLiftRight, Matrix.of_apply, ite_eq_right ha]
        ring
  rw [Finset.sum_congr rfl fun z _ => hkey z]
  calc ∑ z : (J × K) × I, (if z.1 = (j₀, k₀) then (1 : ℂ) else 0)
        * (U (j₀, i₁) (z.1.1, z.2) * V (z.1.2, z.2) (k₀, i₂))
    _ = ∑ p : J × K, ∑ t : I, (if p = (j₀, k₀) then (1 : ℂ) else 0)
        * (U (j₀, i₁) (p.1, t) * V (p.2, t) (k₀, i₂)) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ p : J × K, (if p = (j₀, k₀) then (1 : ℂ) else 0)
        * (∑ t : I, U (j₀, i₁) (p.1, t) * V (p.2, t) (k₀, i₂)) :=
          Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ t : I, U (j₀, i₁) (j₀, t) * V (k₀, t) (k₀, i₂) :=
          sum_fiber_mul_left (j₀, k₀)
            (fun p => ∑ t : I, U (j₀, i₁) (p.1, t) * V (p.2, t) (k₀, i₂))

/-- Packages the fiber isometries, preservation of unitarity by independent lifts, and the
identity expressing joint compression as a product of compressions. -/
theorem independent_ancilla_lift_laws (j₀ : J) (k₀ : K)
    (U : Matrix (J × I) (J × I) ℂ) (V : Matrix (K × I) (K × I) ℂ) :
    IsIsometry (encodingFiber (I := I) j₀) ∧ IsIsometry (jointEncodingFiber (I := I) j₀ k₀) ∧
    (U ∈ Matrix.unitaryGroup (J × I) ℂ →
      independentLiftLeft (K := K) U ∈ Matrix.unitaryGroup ((J × K) × I) ℂ) ∧
    (V ∈ Matrix.unitaryGroup (K × I) ℂ →
      independentLiftRight (J := J) V ∈ Matrix.unitaryGroup ((J × K) × I) ℂ) ∧
    compress (jointEncodingFiber j₀ k₀) (independentLiftLeft U * independentLiftRight V)
        (jointEncodingFiber j₀ k₀) =
      compress (encodingFiber j₀) U (encodingFiber j₀) * compress (encodingFiber k₀) V (encodingFiber k₀) := by
  refine ⟨encodingFiber_isIsometry j₀, jointEncodingFiber_isIsometry j₀ k₀,
    independentLiftLeft_unitary, independentLiftRight_unitary, ?_⟩
  ext i₁ i₂
  simp only [jointEncodingFiber]
  rw [compress_encodingFiber_eq, Matrix.mul_apply, independent_lift_mul_apply,
    Matrix.mul_apply]
  simp only [compress_encodingFiber_eq]

/-- The product of two compatible isometric matrices is isometric. -/
theorem IsIsometry.mul {H M I : Type*} [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]
    [Fintype I] [DecidableEq I] {P : Matrix H M ℂ} {L : Matrix M I ℂ}
    (hP : IsIsometry P) (hL : IsIsometry L) : IsIsometry (P * L) := by
  have e : (P * L)ᴴ * (P * L) = Lᴴ * L := by
    calc (P * L)ᴴ * (P * L) = (Lᴴ * Pᴴ) * (P * L) := by rw [Matrix.conjTranspose_mul]
      _ = Lᴴ * (Pᴴ * (P * L)) := by rw [Matrix.mul_assoc]
      _ = Lᴴ * ((Pᴴ * P) * L) := by rw [Matrix.mul_assoc Pᴴ P L]
      _ = Lᴴ * ((1 : Matrix M M ℂ) * L) := by rw [hP]
      _ = Lᴴ * L := by rw [Matrix.one_mul]
  unfold IsIsometry at hL ⊢
  rw [e, hL]

/-- Multiplication by an isometric matrix preserves the Euclidean norm of a state vector. -/
theorem isometry_mulVec_norm {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    [DecidableEq O]
    {L : Matrix H O ℂ} (hL : IsIsometry L) (v : QState O) :
    ‖toEuclidean_fromVec (L *ᵥ v)‖ = ‖toEuclidean_fromVec v‖ := by
  have hkey : Inner (L *ᵥ v) (L *ᵥ v) = Inner v v := by
    show (star (L *ᵥ v) ⬝ᵥ (L *ᵥ v)) = star v ⬝ᵥ v
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hL,
      Matrix.one_mulVec]
  have h1 : ‖toEuclidean_fromVec (L *ᵥ v)‖ ^ 2 = ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_sq_eq_re_inner, norm_toEuclidean_sq_eq_re_inner, hkey]
  rw [← Real.sqrt_sq (norm_nonneg (toEuclidean_fromVec (L *ᵥ v))),
    ← Real.sqrt_sq (norm_nonneg (toEuclidean_fromVec v)), h1]

/-- The operator norm of an isometric matrix is at most one. -/
theorem isometry_norm_le {H O : Type*} [Fintype H] [DecidableEq H] [Fintype O]
    [DecidableEq O] {L : Matrix H O ℂ} (hL : IsIsometry L) : ‖L‖ ≤ 1 := by
  refine l2_opNorm_le_of_mulVec_le zero_le_one L fun v => ?_
  rw [one_mul]
  exact (isometry_mulVec_norm hL v).le

set_option maxHeartbeats 1000000 in

/-- The compression of a unitary between isometric frames has operator norm at most one. -/
theorem l2_norm_compress_le_one {H I O : Type*} [Fintype H] [DecidableEq H] [Fintype I]
    [DecidableEq I] [Fintype O] [DecidableEq O] {L : Matrix H O ℂ} {U : Matrix H H ℂ}
    {R : Matrix H I ℂ} (hL : IsIsometry L) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hR : IsIsometry R) : ‖compress L U R‖ ≤ 1 := by
  have h1 : ‖compress L U R‖ ≤ ‖Lᴴ‖ * (‖U‖ * ‖R‖) := by
    have hstep1 : ‖Lᴴ * (U * R)‖ ≤ ‖Lᴴ‖ * ‖U * R‖ := Matrix.l2_opNorm_mul Lᴴ (U * R)
    have hstep2 : ‖U * R‖ ≤ ‖U‖ * ‖R‖ := Matrix.l2_opNorm_mul U R
    have hassoc : compress L U R = Lᴴ * U * R := rfl
    rw [hassoc]
    calc ‖Lᴴ * U * R‖ = ‖Lᴴ * (U * R)‖ := by rw [Matrix.mul_assoc]
      _ ≤ ‖Lᴴ‖ * ‖U * R‖ := hstep1
      _ ≤ ‖Lᴴ‖ * (‖U‖ * ‖R‖) := mul_le_mul_of_nonneg_left hstep2 (norm_nonneg _)
  have hL1 : ‖Lᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact isometry_norm_le hL
  have hR1 : ‖R‖ ≤ 1 := isometry_norm_le hR
  have hU1 : ‖U‖ ≤ 1 := l2_norm_unitary_le_one hU
  refine h1.trans ?_
  have hprod : ‖Lᴴ‖ * (‖U‖ * ‖R‖) ≤ 1 * (1 * 1) :=
    mul_le_mul hL1 (mul_le_mul hU1 hR1 (norm_nonneg R) zero_le_one)
      (mul_nonneg (norm_nonneg U) (norm_nonneg R)) zero_le_one
  norm_num at hprod
  exact hprod

set_option maxHeartbeats 1000000 in

/-- Multiplying block encodings on independent ancillas gives a block encoding of `A * B` with
scale `α * β` and error `β * ε + α * η + ε * η`. -/
theorem independent_ancilla_blockEncoding_product (j₀ : J) (k₀ : K) (A B : Matrix I I ℂ)
    (U : Matrix (J × I) (J × I) ℂ) (V : Matrix (K × I) (K × I) ℂ) (α β ε η : ℝ)
    (h1 : BlockEncoding A U (encodingFiber j₀) (encodingFiber j₀) α ε)
    (h2 : BlockEncoding B V (encodingFiber k₀) (encodingFiber k₀) β η) :
    BlockEncoding (A * B) (independentLiftLeft U * independentLiftRight V)
      (jointEncodingFiber j₀ k₀) (jointEncodingFiber j₀ k₀) (α * β) (β * ε + α * η + ε * η) := by
  have hcU : ‖compress (encodingFiber j₀) U (encodingFiber j₀)‖ ≤ 1 :=
    l2_norm_compress_le_one h1.left_isometry h1.unitary h1.right_isometry
  have hcV : ‖compress (encodingFiber k₀) V (encodingFiber k₀)‖ ≤ 1 :=
    l2_norm_compress_le_one h2.left_isometry h2.unitary h2.right_isometry
  have hB : ‖B‖ ≤ η + β := by
    calc ‖B‖ = ‖(B - β • compress (encodingFiber k₀) V (encodingFiber k₀))
          + β • compress (encodingFiber k₀) V (encodingFiber k₀)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖B - β • compress (encodingFiber k₀) V (encodingFiber k₀)‖
          + ‖β • compress (encodingFiber k₀) V (encodingFiber k₀)‖ := norm_add_le _ _
      _ ≤ η + β := by
          refine add_le_add h2.error_le ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos h2.normalization_pos]
          exact (mul_le_mul_of_nonneg_left hcV (le_of_lt h2.normalization_pos)).trans_eq
            (mul_one β)
  have hexpr : (α * β) • compress (jointEncodingFiber j₀ k₀)
      (independentLiftLeft U * independentLiftRight V) (jointEncodingFiber j₀ k₀)
      = (α • compress (encodingFiber j₀) U (encodingFiber j₀))
        * (β • compress (encodingFiber k₀) V (encodingFiber k₀)) := by
    rw [(independent_ancilla_lift_laws j₀ k₀ U V).2.2.2.2]
    ext i₁ i₂
    simp only [Matrix.smul_apply, Matrix.mul_apply, Complex.real_smul, Complex.ofReal_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  refine ⟨(Matrix.unitaryGroup ((J × K) × I) ℂ).mul_mem
    (independentLiftLeft_unitary h1.unitary) (independentLiftRight_unitary h2.unitary),
    jointEncodingFiber_isIsometry j₀ k₀, jointEncodingFiber_isIsometry j₀ k₀,
    mul_pos h1.normalization_pos h2.normalization_pos,
    add_nonneg (add_nonneg (mul_nonneg (le_of_lt h2.normalization_pos) h1.error_nonneg)
        (mul_nonneg (le_of_lt h1.normalization_pos) h2.error_nonneg))
      (mul_nonneg h1.error_nonneg h2.error_nonneg), ?_⟩
  calc ‖A * B - (α * β) • compress (jointEncodingFiber j₀ k₀)
        (independentLiftLeft U * independentLiftRight V) (jointEncodingFiber j₀ k₀)‖
      = ‖A * B - (α • compress (encodingFiber j₀) U (encodingFiber j₀))
          * (β • compress (encodingFiber k₀) V (encodingFiber k₀))‖ := by rw [hexpr]
    _ ≤ ‖A - α • compress (encodingFiber j₀) U (encodingFiber j₀)‖ * ‖B‖
        + ‖α • compress (encodingFiber j₀) U (encodingFiber j₀)‖
          * ‖B - β • compress (encodingFiber k₀) V (encodingFiber k₀)‖ :=
        l2_norm_mul_sub_mul_le A B
          (α • compress (encodingFiber j₀) U (encodingFiber j₀))
          (β • compress (encodingFiber k₀) V (encodingFiber k₀))
    _ ≤ ε * (η + β) + α * η := by
        refine add_le_add (mul_le_mul h1.error_le hB (norm_nonneg B) h1.error_nonneg) ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos h1.normalization_pos]
        exact mul_le_mul
          ((mul_le_mul_of_nonneg_left hcU (le_of_lt h1.normalization_pos)).trans_eq
            (mul_one α)) h2.error_le (norm_nonneg _)
          (le_of_lt h1.normalization_pos)
    _ = β * ε + α * η + ε * η := by ring

/-- The two-gate circuit applying the right independent lift first and the left independent lift
second. -/
def encodingProductCircuit (U : Matrix (J × I) (J × I) ℂ) (V : Matrix (K × I) (K × I) ℂ) :
    Circuit ((J × K) × I) :=
  [Step.gate (independentLiftRight V), Step.gate (independentLiftLeft U)]

/-- The product circuit applies the product of the two lifts, uses zero queries and two gates,
and is unitary when both original operators are unitary. -/
theorem encoding_product_run_cost (U : Matrix (J × I) (J × I) ℂ) (V : Matrix (K × I) (K × I) ℂ)
    (ψ : QState ((J × K) × I)) :
    Run 1 (encodingProductCircuit U V) ψ
      = ApplyGate (independentLiftLeft U * independentLiftRight V) ψ ∧
    QueryCount (encodingProductCircuit U V) = 0 ∧
    GateCount (encodingProductCircuit U V) = 2 ∧
    (U ∈ Matrix.unitaryGroup (J × I) ℂ → V ∈ Matrix.unitaryGroup (K × I) ℂ →
      IsUnitaryCircuit (encodingProductCircuit U V)) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · show independentLiftLeft U *ᵥ (independentLiftRight V *ᵥ ψ)
      = (independentLiftLeft U * independentLiftRight V) *ᵥ ψ
    rw [Matrix.mulVec_mulVec]
  · intro hU hV
    simp only [encodingProductCircuit, isUnitaryCircuit_gate]
    exact ⟨independentLiftRight_unitary hV, independentLiftLeft_unitary hU,
      isUnitaryCircuit_nil⟩

end Qatlib.Concepts.BlockEncoding.EncodingCore
