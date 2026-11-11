/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.TensorPauliTwirl
import QuantumInfo.ForMathlib.HermitianMat.Unitary
import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliOrbitPOVM

/-!
# Finite Pauli-orbit probabilities and event cardinality identities.

This module extends the corresponding public results with finite proved identities.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ShadowModels.ProductPOVM

open Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators RealInnerProductSpace
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

/-- Every actual Pauli-orbit effect has a strictly positive normalized trace,
bounded above by one even for the empty register. -/
theorem pauliOrbit_trace_mem_Ioc (n : ℕ) (ρ : MState (Reg n)) (w : PauliWord n) :
    ((pauliOrbitPOVM n ρ).mats w).trace ∈ Set.Ioc (0 : ℝ) 1 := by
  rw [pauliOrbit_trace]
  constructor
  · exact inv_pos.mpr (qubitDimension_pos n)
  · apply inv_le_one_of_one_le₀
    dsimp [qubitDimension]
    exact one_le_pow₀ (by norm_num)

/-- The scalar traces of all Pauli-orbit effects sum to the Hilbert dimension,
the trace-level shadow of POVM normalization. -/
theorem pauliOrbit_trace_sum (n : ℕ) (ρ : MState (Reg n)) :
    (∑ w : PauliWord n, ((pauliOrbitPOVM n ρ).mats w).trace) = qubitDimension n := by
  simp_rw [pauliOrbit_trace]
  have hcard : Fintype.card (PauliWord n) = 4 ^ n := by
    have hpauli : Fintype.card Pauli1 = 4 := by rfl
    simp [PauliWord, hpauli]
  rw [Finset.sum_const, Finset.card_univ, hcard]
  dsimp [qubitDimension]
  norm_num [nsmul_eq_mul, Nat.cast_pow]
  field_simp
  calc
    (4 : ℝ)^n = (2^2)^n := by norm_num
    _ = 2^(2*n) := by rw [← pow_mul]
    _ = 2^(n*2) := by rw [Nat.mul_comm]
    _ = (2^n)^2 := by rw [pow_mul]

/-- The trace-normalized mass assigned to one Pauli-orbit effect. -/
def pauliOrbitTraceMass (n : ℕ) (ρ : MState (Reg n)) (w : PauliWord n) : ℝ :=
  (qubitDimension n)⁻¹ * ((pauliOrbitPOVM n ρ).mats w).trace

/-- Every trace-normalized Pauli-orbit mass is nonnegative. -/
theorem pauliOrbitTraceMass_nonneg (n : ℕ) (ρ : MState (Reg n)) (w : PauliWord n) :
    0 ≤ pauliOrbitTraceMass n ρ w := by
  unfold pauliOrbitTraceMass
  rw [pauliOrbit_trace]
  exact mul_nonneg (inv_nonneg.mpr (qubitDimension_pos n).le)
    (inv_nonneg.mpr (qubitDimension_pos n).le)

/-- Every individual Pauli-orbit probability mass is strictly positive. -/
theorem pauliOrbitTraceMass_pos (n : ℕ) (ρ : MState (Reg n)) (w : PauliWord n) :
    0 < pauliOrbitTraceMass n ρ w := by
  unfold pauliOrbitTraceMass
  rw [pauliOrbit_trace]
  exact mul_pos (inv_pos.mpr (qubitDimension_pos n))
    (inv_pos.mpr (qubitDimension_pos n))

/-- Every Pauli word receives the same exact trace-normalized mass. -/
theorem pauliOrbitTraceMass_eq_inv_sq (n : ℕ) (ρ : MState (Reg n)) (w : PauliWord n) :
    pauliOrbitTraceMass n ρ w = (qubitDimension n)⁻¹ ^ 2 := by
  unfold pauliOrbitTraceMass
  rw [pauliOrbit_trace]
  ring

/-- Each trace-normalized Pauli-orbit mass lies in the probability interval. -/
theorem pauliOrbitTraceMass_mem_Icc (n : ℕ) (ρ : MState (Reg n)) (w : PauliWord n) :
    pauliOrbitTraceMass n ρ w ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact pauliOrbitTraceMass_nonneg n ρ w
  · rw [pauliOrbitTraceMass_eq_inv_sq]
    apply (sq_le_one_iff₀ (inv_nonneg.mpr (qubitDimension_pos n).le)).2
    apply inv_le_one_of_one_le₀
    dsimp [qubitDimension]
    exact one_le_pow₀ (by norm_num)

/-- The trace-normalized masses form a probability distribution over Pauli words. -/
theorem pauliOrbitTraceMass_sum (n : ℕ) (ρ : MState (Reg n)) :
    (∑ w : PauliWord n, pauliOrbitTraceMass n ρ w) = 1 := by
  unfold pauliOrbitTraceMass
  rw [← Finset.mul_sum, pauliOrbit_trace_sum]
  field_simp [ne_of_gt (qubitDimension_pos n)]

/-- The trace-normalized mass of any finite subset of Pauli words is at most one. -/
theorem pauliOrbitTraceMass_sum_subset_le_one (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) ≤ 1 := by
  calc
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) ≤
        ∑ w : PauliWord n, pauliOrbitTraceMass n ρ w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ S
      · intro w hw hws
        exact pauliOrbitTraceMass_nonneg n ρ w
    _ = 1 := pauliOrbitTraceMass_sum n ρ

/-- Every nonempty finite Pauli-word event has strictly positive mass. -/
theorem pauliOrbitTraceMass_sum_pos (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) (hS : S.Nonempty) :
    0 < (∑ w ∈ S, pauliOrbitTraceMass n ρ w) := by
  apply Finset.sum_pos'
  · intro w hw
    exact pauliOrbitTraceMass_nonneg n ρ w
  · obtain ⟨w, hw⟩ := hS
    exact ⟨w, hw, pauliOrbitTraceMass_pos n ρ w⟩

/-- Uniformity makes every finite subset mass equal its cardinality times one
Pauli-word mass. -/
theorem pauliOrbitTraceMass_sum_subset_eq (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) =
      (S.card : ℝ) * (qubitDimension n)⁻¹ ^ 2 := by
  simp_rw [pauliOrbitTraceMass_eq_inv_sq]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Uniform Pauli-orbit masses make event mass equality equivalent to equal
finite cardinality. -/
theorem pauliOrbitTraceMass_sum_eq_iff_card_eq (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) =
      ∑ w ∈ T, pauliOrbitTraceMass n ρ w ↔ S.card = T.card := by
  rw [pauliOrbitTraceMass_sum_subset_eq, pauliOrbitTraceMass_sum_subset_eq]
  constructor
  · intro h
    have hc : (0 : ℝ) < (qubitDimension n)⁻¹ ^ 2 :=
      sq_pos_of_pos (inv_pos.mpr (qubitDimension_pos n))
    have hcast : (S.card : ℝ) = T.card := by
      exact (mul_right_cancel₀ (ne_of_gt hc)) h
    exact_mod_cast hcast
  · intro h
    simpa [h]

/-- The event mass is its cardinality divided by the number of Pauli words. -/
theorem pauliOrbitTraceMass_sum_eq_card_ratio (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) =
      (S.card : ℝ) / Fintype.card (PauliWord n) := by
  rw [pauliOrbitTraceMass_sum_subset_eq]
  have hcard : (Fintype.card (PauliWord n) : ℝ) = qubitDimension n ^ 2 := by
    have hpauli : Fintype.card Pauli1 = 4 := by rfl
    simp [PauliWord, hpauli, qubitDimension, Nat.cast_pow]
    calc
      (4 : ℝ)^n = (2^2)^n := by norm_num
      _ = 2^(2*n) := by rw [← pow_mul]
      _ = 2^(n*2) := by rw [Nat.mul_comm]
      _ = (2^n)^2 := by rw [pow_mul]
  rw [hcard]
  field_simp [ne_of_gt (qubitDimension_pos n)]

/-- Strict cardinality ordering gives strict event-mass ordering. -/
theorem pauliOrbitTraceMass_sum_lt_of_card_lt (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) (hcard : S.card < T.card) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) <
      ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
  rw [pauliOrbitTraceMass_sum_subset_eq, pauliOrbitTraceMass_sum_subset_eq]
  have hcast : (S.card : ℝ) < T.card := by exact_mod_cast hcard
  have hpos : (0 : ℝ) < (qubitDimension n)⁻¹ ^ 2 :=
    sq_pos_of_pos (inv_pos.mpr (qubitDimension_pos n))
  exact mul_lt_mul_of_pos_right hcast hpos

/-- A proper finite-event inclusion gives strict Pauli-orbit mass growth. -/
theorem pauliOrbitTraceMass_sum_lt_of_subset (n : ℕ) (ρ : MState (Reg n))
    {S T : Finset (PauliWord n)} (hST : S ⊂ T) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) <
      ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
  exact pauliOrbitTraceMass_sum_lt_of_card_lt n ρ S T (Finset.card_lt_card hST)

/-- The complement mass is the probability complement of a finite Pauli-word event. -/
theorem pauliOrbitTraceMass_sum_compl (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    (∑ w ∈ Sᶜ, pauliOrbitTraceMass n ρ w) =
      1 - ∑ w ∈ S, pauliOrbitTraceMass n ρ w := by
  rw [← pauliOrbitTraceMass_sum n ρ]
  have h := Finset.sum_add_sum_compl S (fun w => pauliOrbitTraceMass n ρ w)
  linarith

/-- Every proper finite Pauli-word event has mass strictly below one. -/
theorem pauliOrbitTraceMass_sum_lt_one (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) (hS : S ≠ Finset.univ) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) < 1 := by
  have hcomp : Sᶜ.Nonempty := by
    by_contra hcomp
    have he : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcomp
    exact hS ((Finset.compl_eq_empty_iff S).mp he)
  have hp := pauliOrbitTraceMass_sum_pos n ρ Sᶜ hcomp
  have hrel := pauliOrbitTraceMass_sum_compl n ρ S
  linarith

/-- Total Pauli-orbit probability mass characterizes the full event. -/
theorem pauliOrbitTraceMass_sum_eq_one_iff (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) = 1 ↔ S = Finset.univ := by
  constructor
  · intro hmass
    by_contra hS
    have hlt := pauliOrbitTraceMass_sum_lt_one n ρ S hS
    linarith
  · intro hS
    subst S
    exact pauliOrbitTraceMass_sum n ρ

/-- Zero Pauli-orbit probability mass characterizes the empty event. -/
theorem pauliOrbitTraceMass_sum_eq_zero_iff (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) = 0 ↔ S = ∅ := by
  constructor
  · intro hmass
    by_contra hS
    have hpos := pauliOrbitTraceMass_sum_pos n ρ S
      (Finset.nonempty_iff_ne_empty.mpr hS)
    linarith
  · intro hS
    subst S
    simp

/-- Strictly positive finite event mass characterizes nonemptiness. -/
theorem pauliOrbitTraceMass_sum_pos_iff (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    0 < (∑ w ∈ S, pauliOrbitTraceMass n ρ w) ↔ S.Nonempty := by
  constructor
  · intro hpos
    by_contra hS
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hz := (pauliOrbitTraceMass_sum_eq_zero_iff n ρ S).2 he
    linarith
  · intro hS
    exact pauliOrbitTraceMass_sum_pos n ρ S hS

/-- A nonempty proper finite event has probability mass strictly inside the
open unit interval. -/
theorem pauliOrbitTraceMass_sum_mem_Ioo (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨pauliOrbitTraceMass_sum_pos n ρ S hS,
    pauliOrbitTraceMass_sum_lt_one n ρ S hproper⟩

/-- The open probability interval exactly characterizes nonempty proper events. -/
theorem pauliOrbitTraceMass_sum_mem_Ioo_iff (n : ℕ) (ρ : MState (Reg n))
    (S : Finset (PauliWord n)) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) ∈ Set.Ioo (0 : ℝ) 1 ↔
      S.Nonempty ∧ S ≠ Finset.univ := by
  constructor
  · intro h
    constructor
    · by_contra hS
      have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hz := (pauliOrbitTraceMass_sum_eq_zero_iff n ρ S).2 he
      linarith [h.1, hz]
    · by_contra hS
      have ho := (pauliOrbitTraceMass_sum_eq_one_iff n ρ S).2 hS
      linarith [h.2, ho]
  · rintro ⟨hS, hproper⟩
    exact pauliOrbitTraceMass_sum_mem_Ioo n ρ S hS hproper

/-- Pauli-orbit probability mass is monotone under finite-event inclusion. -/
theorem pauliOrbitTraceMass_sum_mono (n : ℕ) (ρ : MState (Reg n))
    {S T : Finset (PauliWord n)} (hST : S ⊆ T) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) ≤
      ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun w hw hws =>
    pauliOrbitTraceMass_nonneg n ρ w)

/-- The mass of a finite event difference is the difference of its masses. -/
theorem pauliOrbitTraceMass_sum_sdiff (n : ℕ) (ρ : MState (Reg n))
    {S T : Finset (PauliWord n)} (hT : T ⊆ S) :
    (∑ w ∈ S \ T, pauliOrbitTraceMass n ρ w) =
      (∑ w ∈ S, pauliOrbitTraceMass n ρ w) -
        ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
  have h := Finset.sum_sdiff hT (f := fun w => pauliOrbitTraceMass n ρ w)
  linarith

/-- Disjoint finite Pauli-word events have additive probability mass. -/
theorem pauliOrbitTraceMass_sum_union (n : ℕ) (ρ : MState (Reg n))
    {S T : Finset (PauliWord n)} (hST : Disjoint S T) :
    (∑ w ∈ S ∪ T, pauliOrbitTraceMass n ρ w) =
      (∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
        ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
  rw [Finset.sum_union hST]

/-- Finite-event probability mass is subadditive under arbitrary unions. -/
theorem pauliOrbitTraceMass_sum_union_le (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) :
    (∑ w ∈ S ∪ T, pauliOrbitTraceMass n ρ w) ≤
      (∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
        ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
  have hdisj : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hUnion : S ∪ (T \ S) = S ∪ T := by
    ext x
    simp
  calc
    (∑ w ∈ S ∪ T, pauliOrbitTraceMass n ρ w) =
        (∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
          ∑ w ∈ T \ S, pauliOrbitTraceMass n ρ w := by
      rw [← hUnion]
      exact pauliOrbitTraceMass_sum_union n ρ hdisj
    _ ≤ (∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
          ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
      exact add_le_add_right
        (pauliOrbitTraceMass_sum_mono n ρ (S := T \ S) (T := T) Finset.sdiff_subset) _

/-- The union mass obeys both the total-probability bound and the union bound. -/
theorem pauliOrbitTraceMass_sum_union_le_min (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) :
    (∑ w ∈ S ∪ T, pauliOrbitTraceMass n ρ w) ≤
      min 1 ((∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
        ∑ w ∈ T, pauliOrbitTraceMass n ρ w) := by
  exact le_min
    (pauliOrbitTraceMass_sum_subset_le_one n ρ (S ∪ T))
    (pauliOrbitTraceMass_sum_union_le n ρ S T)

/-- The union mass lies between the larger event mass and the sharp union bound. -/
theorem pauliOrbitTraceMass_sum_union_mem_Icc (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) :
    (∑ w ∈ S ∪ T, pauliOrbitTraceMass n ρ w) ∈ Set.Icc
      (max (∑ w ∈ S, pauliOrbitTraceMass n ρ w)
        (∑ w ∈ T, pauliOrbitTraceMass n ρ w))
      (min 1 ((∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
        ∑ w ∈ T, pauliOrbitTraceMass n ρ w)) := by
  constructor
  · apply max_le
    · exact pauliOrbitTraceMass_sum_mono n ρ Finset.subset_union_left
    · exact pauliOrbitTraceMass_sum_mono n ρ Finset.subset_union_right
  · exact pauliOrbitTraceMass_sum_union_le_min n ρ S T

/-- Intersection mass is bounded by the mass of either participating event. -/
theorem pauliOrbitTraceMass_sum_inter_le_left (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) :
    (∑ w ∈ S ∩ T, pauliOrbitTraceMass n ρ w) ≤
      ∑ w ∈ S, pauliOrbitTraceMass n ρ w :=
  pauliOrbitTraceMass_sum_mono n ρ Finset.inter_subset_left

/-- The probability mass of an intersection is at most that of its right event. -/
theorem pauliOrbitTraceMass_sum_inter_le_right (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) :
    (∑ w ∈ S ∩ T, pauliOrbitTraceMass n ρ w) ≤
      ∑ w ∈ T, pauliOrbitTraceMass n ρ w :=
  pauliOrbitTraceMass_sum_mono n ρ Finset.inter_subset_right

/-- A disjoint finite partition of all Pauli words has total mass one. -/
theorem pauliOrbitTraceMass_sum_partition (n : ℕ) (ρ : MState (Reg n))
    {S T : Finset (PauliWord n)} (hST : Disjoint S T)
    (hcover : S ∪ T = Finset.univ) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
      ∑ w ∈ T, pauliOrbitTraceMass n ρ w = 1 := by
  calc
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
        ∑ w ∈ T, pauliOrbitTraceMass n ρ w =
        ∑ w ∈ S ∪ T, pauliOrbitTraceMass n ρ w :=
      (pauliOrbitTraceMass_sum_union n ρ hST).symm
    _ = ∑ w ∈ (Finset.univ : Finset (PauliWord n)), pauliOrbitTraceMass n ρ w := by
      rw [hcover]
    _ = 1 := pauliOrbitTraceMass_sum n ρ

/-- Refining an event splits its mass into the old event and its new shell. -/
theorem pauliOrbitTraceMass_sum_refine (n : ℕ) (ρ : MState (Reg n))
    {S T : Finset (PauliWord n)} (hST : S ⊆ T) :
    (∑ w ∈ S, pauliOrbitTraceMass n ρ w) +
      ∑ w ∈ T \ S, pauliOrbitTraceMass n ρ w =
        ∑ w ∈ T, pauliOrbitTraceMass n ρ w := by
  have h := Finset.sum_sdiff hST (f := fun w => pauliOrbitTraceMass n ρ w)
  linarith

/-- Every finite event shell has probability mass in the unit interval. -/
theorem pauliOrbitTraceMass_sum_sdiff_mem_Icc (n : ℕ) (ρ : MState (Reg n))
    (S T : Finset (PauliWord n)) :
    (∑ w ∈ T \ S, pauliOrbitTraceMass n ρ w) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro w hw
    exact pauliOrbitTraceMass_nonneg n ρ w
  · exact pauliOrbitTraceMass_sum_subset_le_one n ρ (T \ S)

/-- Refinement increments are exactly the nonnegative shell mass and stay in
the probability interval. -/
theorem pauliOrbitTraceMass_sum_refine_mem_Icc (n : ℕ) (ρ : MState (Reg n))
    {S T : Finset (PauliWord n)} (hST : S ⊆ T) :
    ((∑ w ∈ T, pauliOrbitTraceMass n ρ w) -
      ∑ w ∈ S, pauliOrbitTraceMass n ρ w) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← pauliOrbitTraceMass_sum_sdiff n ρ hST]
  exact pauliOrbitTraceMass_sum_sdiff_mem_Icc n ρ S T

end Qatlib.Concepts.ShadowModels.ProductPOVM
