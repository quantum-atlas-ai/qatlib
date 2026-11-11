/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.CollectiveRisk.Data.CollectiveOptimum
import Mathlib.MeasureTheory.VectorMeasure.Operations
import Mathlib.MeasureTheory.VectorMeasure.Order

/-!
# Collective Postprocessing

Collective Risk constructions for Copy Decision.
Defines `jointBornHom`, `finiteJointDecode`, `GeneralJointPOVM`.
Proves `continuous_jointBornHom`, `jointBorn_nonneg`, `jointBorn_smul`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError
open MeasureTheory Matrix
open scoped ComplexOrder Function

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Definition of joint Born Hom in the Collective Risk construction. -/
def jointBornHom (x : EuclideanSpace ℂ α) : HermitianMat α ℂ →+ ℝ where
  toFun E := jointBorn E x
  map_zero' := by simp [jointBorn]
  map_add' E F := by simp [jointBorn, HermitianMat.mat_add]

/-- The stated copy-decision construction satisfies `continuous_jointBornHom` with the complete displayed premises. -/
lemma continuous_jointBornHom (x : EuclideanSpace ℂ α) : Continuous (jointBornHom x) := by
  change Continuous (fun E : HermitianMat α ℂ => (∑ i, (∑ j, E.mat i j*x j)*star (x i)).re)
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    HermitianMat.continuous_mat)).mul continuous_const

/-- The stated copy-decision construction satisfies `jointBorn_nonneg` with the complete displayed premises. -/
lemma jointBorn_nonneg (E : HermitianMat α ℂ) (hE : 0 ≤ E) (x : EuclideanSpace ℂ α) :
    0 ≤ jointBorn E x := by
  have h := HermitianMat.inner_mulVec_nonneg hE (WithLp.ofLp x)
  have hr : 0 ≤ (star (WithLp.ofLp x) ⬝ᵥ (E.mat *ᵥ WithLp.ofLp x)).re := h.1
  change 0 ≤ (∑ i, (E.mat *ᵥ WithLp.ofLp x) i*star (x i)).re
  simpa only [dotProduct, Pi.star_apply, mul_comm] using hr

/-- The stated copy-decision construction satisfies `jointBorn_smul` with the complete displayed premises. -/
lemma jointBorn_smul (r : ℝ) (E : HermitianMat α ℂ) (x : EuclideanSpace ℂ α) :
    jointBorn (r • E) x=r*jointBorn E x := by
  change (inner ℂ x ((r • E.mat).toEuclideanLin x)).re=_
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r E.mat, map_smul,
    LinearMap.smul_apply, inner_smul_right]
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- The stated copy-decision construction satisfies `jointBorn_sum` with the complete displayed premises. -/
lemma jointBorn_sum {m : ℕ} (Λ : POVM (Fin m) α) (x : EuclideanSpace ℂ α) :
    ∑ a, jointBorn (Λ.mats a) x=‖x‖^2 := by
  have h := congrArg (jointBornHom x) Λ.normalized
  simpa [jointBornHom, jointBorn, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h

/-- Definition of finite Joint Decode in the Collective Risk construction. -/
def finiteJointDecode {m : ℕ} (Λ : POVM (Fin m) α) (p : Fin m → TerminalDecision) :
    POVM (Fin 3) α where
  mats i := ∑ a, (p a).prob i • Λ.mats a
  nonneg i := Finset.sum_nonneg (fun a _ => smul_nonneg ((p a).nonneg i) (Λ.nonneg a))
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, TerminalDecision.total, one_smul]
    exact Λ.normalized

/-- Exact coarse effects for arbitrary finite observations followed by
randomized classical guesses. The original unnormalized Born masses remain. -/
theorem finiteJointDecode_error {N m : ℕ} (Λ : POVM (Fin m) (Fin N → Fin 2))
    (p : Fin m → TerminalDecision) (q : Fin 3 → ℝ) :
    jointError (finiteJointDecode Λ p) q=
      ∑ a, ∑ i, q i*jointBorn (Λ.mats a) (copyState N (trineState i))*(1-(p a).prob i) := by
  have hb (i : Fin 3) :
      jointBorn ((finiteJointDecode Λ p).mats i) (copyState N (trineState i))=
        ∑ a, (p a).prob i*jointBorn (Λ.mats a) (copyState N (trineState i)) := by
    change jointBorn (∑ a, (p a).prob i • Λ.mats a) (copyState N (trineState i))=_
    calc
      _ = ∑ a, (jointBornHom _) ((p a).prob i • Λ.mats a) := map_sum (jointBornHom _) _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        exact jointBorn_smul _ _ _
  unfold jointError
  simp_rw [hb]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hm : ∑ a, jointBorn (Λ.mats a) (copyState N (trineState i))=1 := by
    rw [jointBorn_sum, trine_copies_unit, one_pow]
  calc
    _ = q i*((∑ a, jointBorn (Λ.mats a) (copyState N (trineState i)))-
        ∑ a, (p a).prob i*jointBorn (Λ.mats a) (copyState N (trineState i))) := by rw [hm]
    _ = _ := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- A countably additive POVM with arbitrary measurable observations on the
entire original tensor register. It supplies effects, not outcome/risk oracles. -/
structure GeneralJointPOVM (N : ℕ) (Y : Type) [MeasurableSpace Y] where
  effects : VectorMeasure Y (HermitianMat (Fin N → Fin 2) ℂ)
  nonneg : ∀ B, MeasurableSet B → 0 ≤ effects B
  normalized : effects Set.univ=1

namespace GeneralJointPOVM
variable {N : ℕ} {Y : Type} [MeasurableSpace Y] (M : GeneralJointPOVM N Y)

include M in
/-- The stated copy-decision construction satisfies `outcome_nonempty` with the complete displayed premises. -/
lemma outcome_nonempty : Nonempty Y := by
  by_contra h
  have hu : (Set.univ : Set Y)=∅ := by ext y; exact (h ⟨y⟩).elim
  have hz : (1:HermitianMat (Fin N → Fin 2) ℂ)=0 := by
    rw [← M.normalized, hu, VectorMeasure.empty]
  have he := congrArg (fun E : HermitianMat (Fin N → Fin 2) ℂ => E.mat (fun _ => 0) (fun _ => 0)) hz
  norm_num at he

/-- Definition of born Signed in the Collective Risk construction. -/
def bornSigned (x : EuclideanSpace ℂ (Fin N → Fin 2)) : SignedMeasure Y :=
  M.effects.mapRange (jointBornHom x) (continuous_jointBornHom x)

/-- The stated copy-decision construction satisfies `bornSigned_positive` with the complete displayed premises. -/
lemma bornSigned_positive (x : EuclideanSpace ℂ (Fin N → Fin 2)) :
    0 ≤[Set.univ] M.bornSigned x := by
  apply (VectorMeasure.restrict_le_restrict_iff _ _ MeasurableSet.univ).2
  intro B hB _
  exact jointBorn_nonneg _ (M.nonneg B hB) x

/-- Definition of born Measure in the Collective Risk construction. -/
def bornMeasure (x : EuclideanSpace ℂ (Fin N → Fin 2)) : Measure Y :=
  (M.bornSigned x).toMeasureOfZeroLE Set.univ MeasurableSet.univ (M.bornSigned_positive x)

/-- Typeclass instance for born Measure finite in the Collective Risk construction. -/
instance bornMeasure_finite (x : EuclideanSpace ℂ (Fin N → Fin 2)) :
    IsFiniteMeasure (M.bornMeasure x) := by unfold bornMeasure; infer_instance

/-- The stated copy-decision construction satisfies `bornMeasure_real` with the complete displayed premises. -/
lemma bornMeasure_real (x : EuclideanSpace ℂ (Fin N → Fin 2)) {B : Set Y}
    (hB : MeasurableSet B) : (M.bornMeasure x).real B=jointBorn (M.effects B) x := by
  unfold bornMeasure
  rw [SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hB]
  simp only [Set.univ_inter]
  rfl

/-- Typeclass instance for trine Born probability in the Collective Risk construction. -/
instance trineBorn_probability (i : Fin 3) :
    IsProbabilityMeasure (M.bornMeasure (copyState N (trineState i))) where
  measure_univ := by
    have h := M.bornMeasure_real (copyState N (trineState i)) MeasurableSet.univ
    rw [M.normalized] at h
    have hn : jointBorn (1:HermitianMat (Fin N → Fin 2) ℂ) (copyState N (trineState i))=1 := by
      simp [jointBorn, inner_self_eq_norm_sq_to_K, trine_copies_unit]
    rw [hn] at h
    simpa only [measureReal_def, ENNReal.toReal_eq_one_iff] using h

/-- Definition of coarsen in the Collective Risk construction. -/
def coarsen {m : ℕ} (B : Fin m → Set Y) (hB : ∀ a, MeasurableSet (B a))
    (hd : Pairwise (Disjoint on B)) (hu : ⋃ a, B a=Set.univ) :
    POVM (Fin m) (Fin N → Fin 2) where
  mats a := M.effects (B a)
  nonneg a := M.nonneg _ (hB a)
  normalized := by
    have h := M.effects.of_disjoint_iUnion hB hd
    rw [tsum_fintype, hu, M.normalized] at h
    exact h.symm

/-- The stated copy-decision construction satisfies `coarsen_born` with the complete displayed premises. -/
theorem coarsen_born {m : ℕ} (B : Fin m → Set Y) (hB : ∀ a, MeasurableSet (B a))
    (hd : Pairwise (Disjoint on B)) (hu : ⋃ a, B a=Set.univ) (a : Fin m)
    (x : EuclideanSpace ℂ (Fin N → Fin 2)) :
    jointBorn ((M.coarsen B hB hd hu).mats a) x=(M.bornMeasure x).real (B a) :=
  (M.bornMeasure_real x (hB a)).symm

/-- Definition of decode in the Collective Risk construction. -/
def decode (d : Y → Fin 3) (hd : Measurable d) : POVM (Fin 3) (Fin N → Fin 2) where
  mats i := M.effects (d ⁻¹' {i})
  nonneg i := M.nonneg _ (hd (MeasurableSet.singleton i))
  normalized := by
    have hB (i : Fin 3) : MeasurableSet (d ⁻¹' {i}) := hd (MeasurableSet.singleton i)
    have hdis : Pairwise (Disjoint on (fun i : Fin 3 => d ⁻¹' {i})) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro y hyi hyj
      exact hij (hyi.symm.trans hyj)
    have hu : (⋃ i : Fin 3, d ⁻¹' {i})=Set.univ := by ext y; simp
    have h := M.effects.of_disjoint_iUnion hB hdis
    rw [tsum_fintype, hu, M.normalized] at h
    exact h.symm

/-- Definition of decoded Error in the Collective Risk construction. -/
def decodedError (d : Y → Fin 3) (q : Fin 3 → ℝ) : ℝ :=
  ∑ i, q i*(1-(M.bornMeasure (copyState N (trineState i))).real (d ⁻¹' {i}))

/-- Arbitrary measurable observations can be deterministically decoded without
changing any actual correct-decision Born mass or the original weighted risk. -/
theorem decode_error (d : Y → Fin 3) (hd : Measurable d) (q : Fin 3 → ℝ) :
    jointError (M.decode d hd) q=M.decodedError d q := by
  unfold jointError decodedError
  apply Finset.sum_congr rfl
  intro i _
  rw [M.bornMeasure_real _ (hd (MeasurableSet.singleton i))]
  rfl

/-- The stated copy-decision construction satisfies `decoded_uniform_lower` with the complete displayed premises. -/
theorem decoded_uniform_lower (d : Y → Fin 3) (hd : Measurable d) :
    (1/4:ℝ)^N/(2*(1+(1/2:ℝ)^N)) ≤ M.decodedError d (fun _ => 1/3) := by
  rw [← M.decode_error d hd]
  exact jointPOVM_uniform_lower _

end GeneralJointPOVM
end Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
