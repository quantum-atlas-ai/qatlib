/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.POVMPolicy
import Mathlib.MeasureTheory.VectorMeasure.Operations
import Mathlib.MeasureTheory.VectorMeasure.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# General POVM

Qubit Measure constructions for Copy Decision.
Defines `qubitBornHom`, `GeneralQubitPOVM`, `bornSigned`.
Proves `qubitBorn_add`, `qubitBorn_zero`, `qubitBorn_one`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.QubitMeasure.Data
open Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Foundations.DecisionRisk.HarmonicError

open MeasureTheory
open Matrix
open scoped ComplexOrder
open scoped Function

/-- The stated copy-decision construction satisfies `qubitBorn_add` with the complete displayed premises. -/
lemma qubitBorn_add (E F : HermitianMat (Fin 2) ℂ) (x : Qubit) :
    qubitBorn (E+F) x=qubitBorn E x+qubitBorn F x := by
  simp [qubitBorn, HermitianMat.mat_add]

/-- The stated copy-decision construction satisfies `qubitBorn_zero` with the complete displayed premises. -/
lemma qubitBorn_zero (x : Qubit) : qubitBorn 0 x=0 := by simp [qubitBorn]

/-- The stated copy-decision construction satisfies `qubitBorn_one` with the complete displayed premises. -/
lemma qubitBorn_one (x : Qubit) : qubitBorn 1 x=‖x‖^2 := by
  simp [qubitBorn, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- The stated copy-decision construction satisfies `qubitBorn_nonneg` with the complete displayed premises. -/
lemma qubitBorn_nonneg (E : HermitianMat (Fin 2) ℂ) (hE : 0 ≤ E) (x : Qubit) :
    0 ≤ qubitBorn E x := by
  have h := HermitianMat.inner_mulVec_nonneg hE (WithLp.ofLp x)
  have hr : 0 ≤ (star (WithLp.ofLp x) ⬝ᵥ (E.mat *ᵥ WithLp.ofLp x)).re := h.1
  change 0 ≤ (∑ i, (E.mat *ᵥ WithLp.ofLp x) i * star (x i)).re
  simpa only [dotProduct, Pi.star_apply, mul_comm] using hr

/-- Definition of qubit Born Hom in the Qubit Measure construction. -/
def qubitBornHom (x : Qubit) : HermitianMat (Fin 2) ℂ →+ ℝ where
  toFun E := qubitBorn E x
  map_zero' := qubitBorn_zero x
  map_add' E F := qubitBorn_add E F x

/-- The stated copy-decision construction satisfies `continuous_qubitBornHom` with the complete displayed premises. -/
lemma continuous_qubitBornHom (x : Qubit) : Continuous (qubitBornHom x) := by
  change Continuous (fun E : HermitianMat (Fin 2) ℂ =>
    (∑ i, (∑ j, E.mat i j*x j)*star (x i)).re)
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    HermitianMat.continuous_mat)).mul continuous_const

/-- An actual countably additive qubit POVM on an arbitrary measurable outcome
space. Only effect positivity and normalization are added to a vector measure;
neither outcome probabilities nor achievable risks are supplied as oracles. -/
structure GeneralQubitPOVM (Y : Type*) [MeasurableSpace Y] where
  effects : VectorMeasure Y (HermitianMat (Fin 2) ℂ)
  nonneg : ∀ B, MeasurableSet B → 0 ≤ effects B
  normalized : effects Set.univ=1

namespace GeneralQubitPOVM
variable {Y : Type*} [MeasurableSpace Y] (M : GeneralQubitPOVM Y)

include M in
/-- The stated copy-decision construction satisfies `outcome_nonempty` with the complete displayed premises. -/
lemma outcome_nonempty : Nonempty Y := by
  by_contra h
  have hu : (Set.univ : Set Y)=∅ := by
    ext y
    exact (h ⟨y⟩).elim
  have hz : (1 : HermitianMat (Fin 2) ℂ)=0 := by
    rw [← M.normalized, hu, VectorMeasure.empty]
  have he := congrArg (fun E : HermitianMat (Fin 2) ℂ => E.mat 0 0) hz
  norm_num at he

/-- Born signed measure is a continuous additive image of the SAME effects. -/
def bornSigned (x : Qubit) : SignedMeasure Y :=
  M.effects.mapRange (qubitBornHom x) (continuous_qubitBornHom x)

/-- The stated copy-decision construction satisfies `bornSigned_positive` with the complete displayed premises. -/
lemma bornSigned_positive (x : Qubit) : 0 ≤[Set.univ] M.bornSigned x := by
  apply (VectorMeasure.restrict_le_restrict_iff _ _ MeasurableSet.univ).2
  intro B hB _
  change 0 ≤ qubitBorn (M.effects B) x
  exact qubitBorn_nonneg _ (M.nonneg B hB) x

/-- Physical Born probability measure, DERIVED from the positive effects. -/
def bornMeasure (x : Qubit) : Measure Y :=
  (M.bornSigned x).toMeasureOfZeroLE Set.univ MeasurableSet.univ (M.bornSigned_positive x)

/-- Typeclass instance for born Measure finite in the Qubit Measure construction. -/
instance bornMeasure_finite (x : Qubit) : IsFiniteMeasure (M.bornMeasure x) := by
  unfold bornMeasure
  infer_instance

/-- The stated copy-decision construction satisfies `bornMeasure_real` with the complete displayed premises. -/
theorem bornMeasure_real (x : Qubit) {B : Set Y} (hB : MeasurableSet B) :
    (M.bornMeasure x).real B=qubitBorn (M.effects B) x := by
  unfold bornMeasure
  rw [SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hB]
  simp only [Set.univ_inter]
  rfl

/-- The stated copy-decision construction satisfies `bornMeasure_univ_real` with the complete displayed premises. -/
lemma bornMeasure_univ_real (x : Qubit) :
    (M.bornMeasure x).real Set.univ=‖x‖^2 := by
  rw [M.bornMeasure_real x MeasurableSet.univ, M.normalized, qubitBorn_one]

/-- Typeclass instance for trine Born probability in the Qubit Measure construction. -/
instance trineBorn_probability (i : Fin 3) :
    IsProbabilityMeasure (M.bornMeasure (trineState i)) where
  measure_univ := by
    have h := M.bornMeasure_univ_real (trineState i)
    rw [trineState_unit, one_pow] at h
    simpa only [measureReal_def, ENNReal.toReal_eq_one_iff] using h

/-- A finite measurable partition produces an actual finite POVM. Empty and
zero-Born-mass cells are retained, so operator completeness is preserved. -/
def coarsen {m : ℕ} (B : Fin m → Set Y) (hB : ∀ a, MeasurableSet (B a))
    (hd : Pairwise (Disjoint on B)) (hu : ⋃ a, B a=Set.univ) : POVM (Fin m) (Fin 2) where
  mats a := M.effects (B a)
  nonneg a := M.nonneg _ (hB a)
  normalized := by
    have h := M.effects.of_disjoint_iUnion hB hd
    rw [tsum_fintype, hu, M.normalized] at h
    exact h.symm

/-- Coarsening preserves every input's actual Born mass in every box. -/
theorem coarsen_born {m : ℕ} (B : Fin m → Set Y) (hB : ∀ a, MeasurableSet (B a))
    (hd : Pairwise (Disjoint on B)) (hu : ⋃ a, B a=Set.univ) (a : Fin m) (x : Qubit) :
    qubitBorn ((M.coarsen B hB hd hu).mats a) x=(M.bornMeasure x).real (B a) :=
  (M.bornMeasure_real x (hB a)).symm

end GeneralQubitPOVM
end Qatlib.Concepts.CopyDecision.QubitMeasure.Data
