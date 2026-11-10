/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.ECDLPResource17.InvalidBorn.CoherentRun
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.InvalidBorn

open Qatlib.Concepts.CurveGroups.AffineAdd
open Qatlib.Concepts.FiniteCounts.OffsetWord
open Qatlib.Concepts.TensorRegisters.CohGraph

noncomputable def actualOverlap {K : Type*} [Field K] [DecidableEq K] {w : ℕ}
    (E : FieldEncoding K w) {a b : K} (P : (shortCurve a b).Point) (m n : ℕ)
    (a0 : AddSubgroup.zmultiples P) : ℂ :=
  inner ℂ
    (graphState (fun kl : (Fin (n+1) → Bool) × (Fin (n+1) → Bool) =>
      bitRun E (pointBits E (a0 : (shortCurve a b).Point))
        (cyclicWord P m (List.ofFn kl.1) (List.ofFn kl.2))))
    (graphState (fun kl : (Fin (n+1) → Bool) × (Fin (n+1) → Bool) =>
      pointBits E ((a0 + binaryValue (List.ofFn kl.1) • cyclicGenerator P +
        binaryValue (List.ofFn kl.2) • (m • cyclicGenerator P) : AddSubgroup.zmultiples P) :
          (shortCurve a b).Point)))

theorem source_expected_overlap (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w)
    {a b : ZMod p} (P : (shortCurve a b).Point) (m n : ℕ)
    (h : letI := cyclicFintype P
      (Finset.univ.erase (0 : AddSubgroup.zmultiples P)).Nonempty) :
    let E := primeFieldEncoding p w hp
    letI := cyclicFintype P
    let p0 := PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h
    (∑ a0, (p0 a0).toReal * (1 - (actualOverlap E P m n a0).re)) ≤
      (8*(n+1) : ℕ) / (Fintype.card (AddSubgroup.zmultiples P) - 1 : ℕ) := by
  letI := cyclicFintype P
  have hj := source_joint_bit_failure p w hp P m n h
  dsimp only at hj ⊢
  rw [joint_event_reverse] at hj
  have he : ∀ a0 : AddSubgroup.zmultiples P,
      1 - (actualOverlap (primeFieldEncoding p w hp) P m n a0).re =
      ((PMF.uniformOfFintype' ((Fin (n+1) → Bool) × (Fin (n+1) → Bool))).toOuterMeasure
        {kl | bitError (primeFieldEncoding p w hp) P m (List.ofFn kl.1) (List.ofFn kl.2) a0}).toReal :=
    fun a0 => source_coherent_defect p w hp P m n a0
  simp_rw [he]
  exact hj

theorem normSq_fidelity_defect_le (z : ℂ) : 1 - Complex.normSq z ≤ 2 * (1-z.re) := by
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (z.re-1), sq_nonneg z.im]

theorem source_expected_fidelity_loss (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w)
    {a b : ZMod p} (P : (shortCurve a b).Point) (m n : ℕ)
    (h : letI := cyclicFintype P
      (Finset.univ.erase (0 : AddSubgroup.zmultiples P)).Nonempty) :
    let E := primeFieldEncoding p w hp
    letI := cyclicFintype P
    let p0 := PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h
    (∑ a0, (p0 a0).toReal * (1 - Complex.normSq (actualOverlap E P m n a0))) ≤
      2 * ((8*(n+1) : ℕ) / (Fintype.card (AddSubgroup.zmultiples P) - 1 : ℕ)) := by
  letI := cyclicFintype P
  have ho := source_expected_overlap p w hp P m n h
  calc
    _ ≤ ∑ a0, ((PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h) a0).toReal *
        (2 * (1 - (actualOverlap (primeFieldEncoding p w hp) P m n a0).re)) := by
      apply Finset.sum_le_sum
      intro a0 _
      exact mul_le_mul_of_nonneg_left (normSq_fidelity_defect_le _) ENNReal.toReal_nonneg
    _ = 2 * ∑ a0, ((PMF.uniformOfFinset (Finset.univ.erase (0 : AddSubgroup.zmultiples P)) h) a0).toReal *
        (1 - (actualOverlap (primeFieldEncoding p w hp) P m n a0).re) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a0 _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ho (by norm_num)

end Qatlib.Papers.ECDLPResource17.InvalidBorn
