/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Erasure

/-! # Scalar support retained from the original SpacetimeLB26 contribution

This file proves conditional arithmetic or abstract combinatorial implications. Its
hypotheses must be read literally: final overlap, survival, contraction, code existence,
distance or threshold fields are not constructions of the corresponding physical objects.
The paper metadata records these interfaces as partial support, separately from the
new native Bell and adaptive erasure producers. Fixed source: arXiv2608.26272v1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.Erasure

open Qatlib.Papers.SpacetimeLB26.ScalarSupport.Erasure

open scoped BigOperators
open Finset

/-! ## Finite record averaging interface -/

/- The paper's Eq. (E5) averages the `1/2` fidelity loss on complete-erasure
records with the trivial fidelity bound on all other records.  The following
finite interface makes precisely that averaging step explicit.  It does not
construct a record law or a conditional quantum state: those remain fields of
the interface and must be supplied by a physical producer. -/

/-- Finite record data sufficient for the complete-erasure averaging step.

`weight` is a normalized finite record law, `survives` marks records on which
complete erasure was avoided, and `fidelity` is the conditional decoded
entanglement fidelity.  The two fidelity inequalities are the only physical
premises: every fidelity is at most one, while a complete-erasure record has
fidelity at most one half. -/
structure FiniteRecordFidelityData (N : ℕ) where
  weight : Fin N → ℝ
  survives : Fin N → Bool
  fidelity : Fin N → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_one : (∑ i, weight i) = 1
  fidelity_le_one : ∀ i, fidelity i ≤ 1
  erased_fidelity_le_half : ∀ i, survives i ≠ true → fidelity i ≤ 1 / 2

/-- Probability mass of the records that avoid complete erasure. -/
def survivalMass {N : ℕ} (d : FiniteRecordFidelityData N) : ℝ :=
  ∑ i, if d.survives i = true then d.weight i else 0

/- The record interface carries a genuine finite probability mass: the
   surviving branch is nonnegative and cannot exceed the total normalized
   record mass.  These bounds let downstream consumers use `survivalMass` as
   a probability parameter without rebuilding the finite sum argument. -/

/-- The finite survival event has nonnegative mass. -/
theorem survivalMass_nonneg {N : ℕ} (d : FiniteRecordFidelityData N) :
    0 ≤ survivalMass d := by
  unfold survivalMass
  exact Finset.sum_nonneg (fun i _ => by
    by_cases hi : d.survives i = true
    · simpa [hi] using d.weight_nonneg i
    · simp [hi])

/-- The finite survival event has mass at most one. -/
theorem survivalMass_le_one {N : ℕ} (d : FiniteRecordFidelityData N) :
    survivalMass d ≤ 1 := by
  unfold survivalMass
  calc
    (∑ i, if d.survives i = true then d.weight i else 0) ≤
        ∑ i, d.weight i := by
      exact Finset.sum_le_sum (fun i _ => by
        by_cases hi : d.survives i = true
        · simp [hi]
        · simpa [hi] using d.weight_nonneg i)
    _ = 1 := d.weight_sum_one

/-- The finite-record average of the conditional fidelities. -/
def finalFidelity {N : ℕ} (d : FiniteRecordFidelityData N) : ℝ :=
  ∑ i, d.weight i * d.fidelity i

/-- Finite record averaging gives Eq. (E5): complete-erasure mass causes at
least half a unit of infidelity. -/
theorem finite_record_e5 {N : ℕ} (d : FiniteRecordFidelityData N) :
    1 - finalFidelity d ≥ (1 / 2) * (1 - survivalMass d) := by
  have hterm : ∀ i : Fin N,
      d.weight i * d.fidelity i ≤
        (if d.survives i = true then d.weight i else d.weight i / 2) := by
    intro i
    by_cases hi : d.survives i = true
    · simp [hi]
      exact mul_le_of_le_one_right (d.weight_nonneg i) (d.fidelity_le_one i)
    · simp [hi]
      have hhalf : d.fidelity i ≤ (2 : ℝ)⁻¹ := by
        simpa [one_div] using d.erased_fidelity_le_half i hi
      exact (mul_le_mul_of_nonneg_left hhalf (d.weight_nonneg i))
  have hsum : finalFidelity d ≤
      ∑ i : Fin N, (if d.survives i = true then d.weight i else d.weight i / 2) := by
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have hsplit :
      (∑ i : Fin N, (if d.survives i = true then d.weight i else d.weight i / 2)) =
        (1 + survivalMass d) / 2 := by
    calc
      (∑ i : Fin N, (if d.survives i = true then d.weight i else d.weight i / 2)) =
          ∑ i : Fin N, ((d.weight i +
            (if d.survives i = true then d.weight i else 0)) / 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hsi : d.survives i = true
        · simp [hsi]
        · simp [hsi]
      _ = ((∑ i : Fin N, d.weight i) +
          (∑ i : Fin N, if d.survives i = true then d.weight i else 0)) / 2 := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
      _ = (1 + survivalMass d) / 2 := by
        rw [d.weight_sum_one]
        rfl
  have hupper : finalFidelity d ≤ (1 + survivalMass d) / 2 := by
    exact hsum.trans_eq hsplit
  dsimp [finalFidelity] at hupper
  dsimp [finalFidelity, survivalMass] at hupper ⊢
  nlinarith [hupper]

/-- A supplied survival upper bound transports the finite-record averaging
estimate to the exact scalar premise used by `erasure_one_qubit_bound`.
The survival bound may come from the native adaptive erasure producer, while
the fidelity fields remain the explicit physical interface above. -/
theorem finite_record_e5_of_survival_upper {N : ℕ}
    (d : FiniteRecordFidelityData N) (survivalUpper : ℝ)
    (hsurvival : survivalMass d ≤ survivalUpper) :
    1 - finalFidelity d ≥ (1 / 2) * (1 - survivalUpper) := by
  have hE5 := finite_record_e5 d
  nlinarith

/-! ## A finite two-record consumer -/

/-- A two-atom finite record law with one surviving branch and one complete-erasure
branch.  The constructor exposes the noise parameter and width, while the
conditional fidelity inequalities remain the explicit physical premises stored
in `FiniteRecordFidelityData`; this definition does not construct a circuit or
a conditional quantum state. -/
def twoRecordData (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteRecordFidelityData 2 :=
  { weight := fun i => if i = 0 then 1 - p ^ n else p ^ n
    survives := fun i => if i = 0 then true else false
    fidelity := fun i => if i = 0 then 1 else 1 / 2
    weight_nonneg := by
      intro i
      fin_cases i
      · exact sub_nonneg.mpr (pow_le_one₀ hp0 hp1)
      · exact pow_nonneg hp0 _
    weight_sum_one := by
      simp [Fin.sum_univ_two]
    fidelity_le_one := by
      intro i
      fin_cases i <;> norm_num
    erased_fidelity_le_half := by
      intro i hi
      fin_cases i
      · simp at hi
      · norm_num }

/-- The surviving mass of the two-record consumer is exactly `1 - p^n`. -/
theorem twoRecordData_survivalMass (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    survivalMass (twoRecordData p n hp0 hp1) = 1 - p ^ n := by
  simp [survivalMass, twoRecordData, Fin.sum_univ_two]

/-- The finite-record fidelity of the two-record consumer is `1 - p^n/2`.
The one-half fidelity premise on the erased branch is still supplied through
the data structure rather than inferred from this arithmetic identity. -/
theorem twoRecordData_finalFidelity (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    finalFidelity (twoRecordData p n hp0 hp1) = 1 - p ^ n / 2 := by
  simp [finalFidelity, twoRecordData, Fin.sum_univ_two] <;> ring

/-- The two-record fidelity is the average of the unit-fidelity surviving branch
and the half-fidelity complete-erasure branch, expressed directly through the
survival mass. -/
theorem twoRecordData_finalFidelity_eq_survival_average (p : ℝ) (n : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    finalFidelity (twoRecordData p n hp0 hp1) =
      (1 + survivalMass (twoRecordData p n hp0 hp1)) / 2 := by
  rw [twoRecordData_finalFidelity p n hp0 hp1,
    twoRecordData_survivalMass p n hp0 hp1]
  ring

/-- The same finite two-record law exposes the exact infidelity carried by its
complete-erasure branch.  This is the equality form of the averaging step and
is independent of any circuit realization of the record premises. -/
theorem twoRecordData_infidelity_eq_survival_loss (p : ℝ) (n : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - finalFidelity (twoRecordData p n hp0 hp1) =
      (1 - survivalMass (twoRecordData p n hp0 hp1)) / 2 := by
  rw [twoRecordData_finalFidelity p n hp0 hp1,
    twoRecordData_survivalMass p n hp0 hp1]
  ring

/-- The elementary exponential bound gives a survival upper bound for the
two-record consumer. -/
theorem twoRecordData_survival_upper (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    survivalMass (twoRecordData p n hp0 hp1) ≤ Real.exp (-(p ^ n)) := by
  rw [twoRecordData_survivalMass p n hp0 hp1]
  exact Real.one_sub_le_exp_neg _

/-- Concrete finite consumer for the E5 bridge: the two-record law obeys the
exponential survival upper bound, so its averaged fidelity obeys the corresponding
half-infidelity lower bound.  The result consumes the explicit fidelity premises
of `twoRecordData` and does not assert a physical realization of those premises. -/
theorem twoRecordData_e5_exp_bound (p : ℝ) (n : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - finalFidelity (twoRecordData p n hp0 hp1) ≥
      (1 / 2) * (1 - Real.exp (-(p ^ n))) := by
  exact finite_record_e5_of_survival_upper
    (twoRecordData p n hp0 hp1) (Real.exp (-(p ^ n)))
    (twoRecordData_survival_upper p n hp0 hp1)

/-! ## Lemma 11 — probability of avoiding complete erasure -/

/-! ## Theorem 12 — one-qubit circuit-size bound for erasure noise -/

/-! ## Proposition 13 — one execution retains the full logical dimension -/

/-! ## Corollary 14 — combined circuit-size lower bound for erasure noise -/

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.Erasure
