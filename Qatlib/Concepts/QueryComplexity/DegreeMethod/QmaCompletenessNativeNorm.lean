/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeEnergy
import Qatlib.Concepts.SpectralReadout.PhaseReadout.QmaCompletenessNoBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessEntryBounds
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Norm bounds and dyadic scaling for local terms

This module converts local-table energy estimates into absolute quadratic bounds and
operator-norm bounds for Hermitian matrices. It also bounds weighted clock-pair penalties and
defines the power-of-two scale `scaleDen` that dominates both `32` and the clock weight `J`.

Increasing the dyadic width scales a represented matrix by the corresponding inverse power of
two. These estimates normalize the local terms used in the circuit-to-Hamiltonian framework of
[KitaevShenVyalyi2002].

## Main statements

* `local_table_abs`: Five-qubit terms with bounded entries have absolute energy at most `32 *
  mass ψ`.
* `l2norm_le_of_quadratic`: A uniform Hermitian quadratic bound controls the Euclidean operator
  norm.
* `scaleDen_bounds`: The chosen scale dominates the required constants with a linear size bound.
* `scaled_quadratic_bound`: Dyadic scaling turns the quadratic bound into a bound by state mass.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib  Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped Classical BigOperators
set_option autoImplicit false
noncomputable section

/-- Negates both integer coefficient tables of a local term while preserving its support. -/
def negTerm {N : ℕ} (t : IntegerLocalTerm N) : IntegerLocalTerm N :=
  ⟨t.support, fun u v => -t.re u v, fun u v => -t.im u v⟩

/-- Negating both integer numerators negates their dyadic complex value. -/
theorem dyadic_neg (b : ℕ) (r i : ℤ) :
    dyadicValue b (-r) (-i) = -dyadicValue b r i := by
  unfold dyadicValue
  push_cast
  ring

/-- Interpreting the negated local term gives the negative of the original interpreted matrix. -/
theorem value_negTerm {N : ℕ} (b : ℕ) (t : IntegerLocalTerm N) :
    value b (negTerm t) = -value b t := by
  ext x y
  change partitionLift (split t.support)
    (fun u v => dyadicValue b (-t.re u v) (-t.im u v)) x y =
    -(partitionLift (split t.support)
      (fun u v => dyadicValue b (t.re u v) (t.im u v)) x y)
  rw [partitionLift_apply, partitionLift_apply]
  split_ifs <;> simp only [dyadic_neg, neg_zero]

/-- Negating a matrix negates its energy on every state. -/
theorem energy_neg {I : Type} [Fintype I] (H : Matrix I I ℂ) (ψ : QState I) :
    energy (-H) ψ = -energy H ψ := by
  simpa using energy_matrix_real_smul (-1) H ψ

/-- A matrix represented by a term on at most five qubits with entry norms at most one has
absolute energy at most `32 * mass ψ`. -/
theorem local_table_abs {m n : ℕ} (b : ℕ) (t : IntegerLocalTerm (m+n))
    (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ)
    (ht : t.support.card ≤ 5)
    (hv : value b t=Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm H)
    (hH : ∀p q, ‖H p q‖ ≤ 1) (ψ : QState (Clock m×Reg n)) :
    |energy H ψ| ≤ (32:ℝ)*mass ψ := by
  have hlo := local_table_lower b t H ht hv hH ψ
  have hneg : value b (negTerm t)=
      Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm (-H) := by
    rw [value_negTerm, hv]
    rfl
  have hne : ∀p q, ‖(-H) p q‖ ≤ 1 := by
    intro p q
    simpa only [Matrix.neg_apply, norm_neg] using hH p q
  have hup := local_table_lower b (negTerm t) (-H) ht hneg hne ψ
  rw [energy_neg] at hup
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A matrix represented by a term on at most five qubits with entry norms at most one has
absolute energy at most `32` on normalized states. -/
theorem local_table_abs_normalized {m n : ℕ} (b : ℕ) (t : IntegerLocalTerm (m+n))
    (H : Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ) (ht : t.support.card ≤ 5)
    (hv : value b t=Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm H)
    (hH : ∀p q, ‖H p q‖ ≤ 1) (ψ : QState (Clock m×Reg n)) (hψ : Normalized ψ) :
    |energy H ψ| ≤ 32 := by
  have h := local_table_abs b t H ht hv hH ψ
  change mass ψ=1 at hψ
  simpa only [hψ, mul_one] using h

/-- A clock-pair penalty weighted by a natural number `J` has energy between zero and `J * mass
ψ`. -/
theorem clockPair_energy_bounds {m n : ℕ} (J : ℕ) (i j : Fin m)
    (ψ : QState (Clock m×Reg n)) :
    0  ≤  energy ((J:ℂ) • TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) ψ ∧
    energy ((J:ℂ) • TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) ψ  ≤  (J:ℝ)*mass ψ := by
  let w : Clock m×Reg n → ℝ := fun p =>
    if i < j ∧ p.1 i=false ∧ p.1 j=true then 1 else 0
  have hI : (1:Matrix (Reg n) (Reg n) ℂ)=Matrix.diagonal (fun _ => (1:ℂ)) :=
    Matrix.diagonal_one.symm
  have hD : TensorGate (pairPenalty i j) (1:Matrix (Reg n) (Reg n) ℂ) =
      Matrix.diagonal (fun p => (w p:ℂ)) := by
    rw [hI]
    unfold TensorGate pairPenalty
    rw [Matrix.diagonal_kronecker_diagonal]
    ext p q
    by_cases he : p=q
    · subst q
      simp only [Matrix.diagonal_apply_eq,mul_one]
      dsimp [w]
      split_ifs <;> norm_num
    · simp [he]
  have hw : ∀p, 0 ≤ w p ∧ w p ≤ 1 := by
    intro p
    dsimp [w]
    split_ifs <;> norm_num
  have he : energy (TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) ψ = ∑p,w p*‖ψ p‖^2 := by
    rw [hD, energy_diagonal]
  have h0 : 0 ≤ energy (TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) ψ := by
    rw [he]
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (hw p).1 (sq_nonneg _))
  have h1 : energy (TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) ψ  ≤  mass ψ := by
    rw [he]
    exact Finset.sum_le_sum (fun p _ => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw p).2 (sq_nonneg ‖ψ p‖))
  have hJ : energy ((J:ℂ) • TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) ψ =
      (J:ℝ)*energy (TensorGate (pairPenalty i j) (1:Matrix (Reg n) (Reg n) ℂ)) ψ := by
    simpa using energy_matrix_real_smul (J:ℝ)
      (TensorGate (pairPenalty i j) (1:Matrix (Reg n) (Reg n) ℂ)) ψ
  rw [hJ]
  exact ⟨mul_nonneg (Nat.cast_nonneg J) h0,
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg J)⟩

/-- The absolute energy of the clock-pair penalty weighted by `J` is at most `J * mass ψ`. -/
theorem clockPair_energy_abs {m n : ℕ} (J : ℕ) (i j : Fin m)
    (ψ : QState (Clock m×Reg n)) :
    |energy ((J:ℂ) • TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) ψ|  ≤  (J:ℝ)*mass ψ := by
  have h := clockPair_energy_bounds J i j ψ
  rw [abs_of_nonneg h.1]
  exact h.2

/-- A clock-pair penalty tensored with the work identity and weighted by a natural number is
Hermitian. -/
theorem clockPair_hermitian {m n : ℕ} (J : ℕ) (i j : Fin m) :
    Matrix.IsHermitian ((J:ℂ) • TensorGate (pairPenalty i j)
      (1:Matrix (Reg n) (Reg n) ℂ)) := by
  change (((J:ℂ) • TensorGate (pairPenalty i j)
    (1:Matrix (Reg n) (Reg n) ℂ))ᴴ) = _
  simp only [Matrix.conjTranspose_smul, tensorGate_conjTranspose,
    (pairPenalty_hermitian i j).eq, Matrix.conjTranspose_one]
  simp

/-- A Hermitian matrix whose absolute energy is bounded by `B` times state mass has Euclidean
operator norm at most the nonnegative constant `B`. -/
theorem l2norm_le_of_quadratic {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hHerm : Matrix.IsHermitian H) (B : ℝ) (hB : 0 ≤ B)
    (hQuad : ∀ψ : QState I, |energy H ψ| ≤ B*mass ψ) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) H‖ ≤ B := by
  have hs : (Matrix.toEuclideanCLM (𝕜:=ℂ) H :
      EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  have he (x : EuclideanSpace ℂ I) :
      (Matrix.toEuclideanCLM (𝕜:=ℂ) H).reApplyInnerSelf x =
        energy H (WithLp.ofLp x) := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
    simp only [PiLp.inner_apply, RCLike.inner_apply', energy,
        Qatlib.Foundations.PureStateMath.inner_apply]
    congr 1
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hs]
  apply ciSup_le
  intro x
  by_cases hx : x=0
  · simpa only [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero] using hB
  · have hp : 0<‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    change |(Matrix.toEuclideanCLM (𝕜:=ℂ) H).reApplyInnerSelf x / ‖x‖^2| ≤ B
    rw [abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).2
    rw [he]
    have hm : mass (WithLp.ofLp x)=‖x‖^2 := (EuclideanSpace.norm_sq_eq x).symm
    simpa only [hm] using hQuad (WithLp.ofLp x)

/-- The dyadic scaling exponent `Nat.log2 (32 + J) + 1`. -/
def scaleBits (J : ℕ) : ℕ := (32+J).log2+1
/-- The power-of-two scaling denominator `2^(scaleBits J)`. -/
def scaleDen (J : ℕ) : ℕ := 2^(scaleBits J)

/-- The scaling denominator dominates `32` and `J`, while both the denominator and its exponent
are at most `2 * (32 + J)`. -/
theorem scaleDen_bounds (J : ℕ) :
    32 ≤ scaleDen J ∧ J ≤ scaleDen J ∧ scaleDen J ≤ 2*(32+J) ∧
      scaleBits J ≤ 2*(32+J) := by
  have hlo : 32+J < scaleDen J := Nat.lt_log2_self (n:=32+J)
  have hp := Nat.log2_self_le (n:=32+J) (by omega)
  have hhi : scaleDen J ≤ 2*(32+J) := by
    unfold scaleDen scaleBits
    rw [pow_succ]
    omega
  have hq : scaleBits J < scaleDen J := Nat.lt_two_pow_self (n:=scaleBits J)
  omega

/-- Increasing the dyadic width by `q` multiplies the represented complex value by `2^(-q)`. -/
theorem dyadic_width_shift (b q : ℕ) (r i : ℤ) :
    dyadicValue (b+q) r i = ((2:ℂ)^q)⁻¹ * dyadicValue b r i := by
  unfold dyadicValue
  rw [pow_add]
  field_simp

/-- Increasing the width of a local term by `q` scales its interpreted matrix by the inverse of
`2^q`. -/
theorem value_width_shift {N : ℕ} (b q : ℕ) (t : IntegerLocalTerm N) :
    value (b+q) t = (((2:ℝ)^q)⁻¹:ℂ) • value b t := by
  ext x y
  simp only [value, partitionLift_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [dyadic_width_shift]
    push_cast
    rfl
  · simp

/-- Scaling a matrix by `2^(-q)` bounds its absolute energy by state mass whenever its original
quadratic bound is at most `2^q`. -/
theorem scaled_quadratic_bound {I : Type} [Fintype I]
    (H : Matrix I I ℂ) (q : ℕ) (B : ℝ)
    (hB : B ≤ (2:ℝ)^q)
    (hQ : ∀ψ : QState I, |energy H ψ| ≤ B*mass ψ) (ψ : QState I) :
    |energy ((((2:ℝ)^q)⁻¹:ℂ) • H) ψ| ≤ mass ψ := by
  have hp : 0 < (2:ℝ)^q := by positivity
  have he:=energy_matrix_real_smul (((2:ℝ)^q)⁻¹) H ψ
  push_cast at he
  rw [show ((2:ℝ):ℂ)=(2:ℂ) by norm_num]
  rw [he,abs_mul,abs_of_nonneg (inv_nonneg.mpr hp.le)]
  have hs := mul_le_mul_of_nonneg_left (hQ ψ) (inv_nonneg.mpr hp.le)
  have hb := mul_le_mul_of_nonneg_right hB (mass_nonneg ψ)
  have ht := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)
  calc
    ((2:ℝ)^q)⁻¹ * |energy H ψ|  ≤  ((2:ℝ)^q)⁻¹*(B*mass ψ) := hs
    _  ≤  ((2:ℝ)^q)⁻¹*((2:ℝ)^q*mass ψ) := ht
    _ = mass ψ := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
