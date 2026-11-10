/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.RandomHashLaw
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.RandomRecovery

open LinearCodeProgram RandomHashLaw

variable {A m n k : ℕ} [NeZero A] [NeZero k]

noncomputable def decoder (candidates : Fin k → Fin n → ZMod A)
    (g : Fin m → Fin n → ZMod A) (z : Fin m → ZMod A) : Fin k := by
  classical
  exact if h : ∃ t, response g (candidates t) = z then Classical.choose h else 0

omit [NeZero A] in

theorem error_implies_collision (candidates : Fin k → Fin n → ZMod A)
    (g : Fin m → Fin n → ZMod A) (t : Fin k)
    (herr : decoder candidates g (response g (candidates t)) ≠ t) :
    ∃ j : {j : Fin k // j ≠ t}, response g (candidates j) = response g (candidates t) := by
  classical
  have hex : ∃ j, response g (candidates j) = response g (candidates t) := ⟨t,rfl⟩
  rw [decoder, dif_pos hex] at herr
  exact ⟨⟨Classical.choose hex,herr⟩, Classical.choose_spec hex⟩

omit [NeZero k] in

theorem collision_union_bound [Fact (Nat.Prime A)]
    (candidates : Fin k → Fin n → ZMod A) (hinj : Function.Injective candidates) (t : Fin k) :
    (matrixLaw A m n).toOuterMeasure
      {g | ∃ j : {j : Fin k // j ≠ t}, response g (candidates j) = response g (candidates t)} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/A^m) := by
  classical
  have he : {g : Fin m → Fin n → ZMod A |
      ∃ j : {j : Fin k // j ≠ t}, response g (candidates j) = response g (candidates t)} =
      ⋃ j : {j : Fin k // j ≠ t}, {g | response g (candidates j) = response g (candidates t)} := by
    ext g
    simp
  rw [he]
  have hu := MeasureTheory.measure_iUnion_le (μ := (matrixLaw A m n).toOuterMeasure)
    (fun j : {j : Fin k // j ≠ t} => {g | response g (candidates j) = response g (candidates t)})
  have hp (j : {j : Fin k // j ≠ t}) :
      (matrixLaw A m n).toOuterMeasure {g | response g (candidates j) = response g (candidates t)} =
        (1:ENNReal)/A^m := pair_collision _ _ (hinj.ne j.property)
  have hc : Fintype.card {j : Fin k // j ≠ t} = k-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ ≤ _ := hu
    _ = _ := by
      simp_rw [hp]
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]

noncomputable def experiment (candidates : Fin k → Fin n → ZMod A) (t : Fin k) : PMF (Fin k) :=
  (matrixLaw A m n).bind fun g =>
    (outputLaw g (candidates t)).map (fun p => decoder candidates g p.1.1)

theorem experiment_eq (candidates : Fin k → Fin n → ZMod A) (t : Fin k) :
    experiment (m:=m) candidates t =
      (matrixLaw A m n).map (fun g => decoder candidates g (response g (candidates t))) := by
  unfold experiment PMF.map
  apply congrArg (PMF.bind (matrixLaw A m n))
  funext g
  exact outputLaw_decoded g (candidates t) (decoder candidates g)

theorem recovery_error_bound [Fact (Nat.Prime A)]
    (candidates : Fin k → Fin n → ZMod A) (hinj : Function.Injective candidates) (t : Fin k) :
    (experiment (m:=m) candidates t).toOuterMeasure {out | out ≠ t} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/A^m) := by
  rw [experiment_eq, PMF.toOuterMeasure_map_apply]
  exact ((matrixLaw A m n).toOuterMeasure.mono
    (fun _ herr => error_implies_collision candidates _ t herr)).trans
      (collision_union_bound candidates hinj t)

omit [NeZero k] in

theorem general_collision_union_bound
    (candidates : Fin k → Fin n → ZMod A) (hinj : Function.Injective candidates) (t : Fin k) :
    (matrixLaw A m n).toOuterMeasure
      {g | ∃ j : {j : Fin k // j ≠ t}, response g (candidates j) = response g (candidates t)} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/2^m) := by
  classical
  have he : {g : Fin m → Fin n → ZMod A |
      ∃ j : {j : Fin k // j ≠ t}, response g (candidates j) = response g (candidates t)} =
      ⋃ j : {j : Fin k // j ≠ t}, {g | response g (candidates j) = response g (candidates t)} := by
    ext g
    simp
  rw [he]
  have hu := MeasureTheory.measure_iUnion_le (μ := (matrixLaw A m n).toOuterMeasure)
    (fun j : {j : Fin k // j ≠ t} => {g | response g (candidates j) = response g (candidates t)})
  have hc : Fintype.card {j : Fin k // j ≠ t} = k-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ ≤ _ := hu
    _ ≤ ∑' _ : {j : Fin k // j ≠ t}, (1:ENNReal)/2^m :=
      ENNReal.tsum_le_tsum (fun j => pair_collision_le_binary _ _ (hinj.ne j.property))
    _ = _ := by simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]

theorem general_recovery_error_bound
    (candidates : Fin k → Fin n → ZMod A) (hinj : Function.Injective candidates) (t : Fin k) :
    (experiment (m:=m) candidates t).toOuterMeasure {out | out ≠ t} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/2^m) := by
  rw [experiment_eq, PMF.toOuterMeasure_map_apply]
  exact ((matrixLaw A m n).toOuterMeasure.mono
    (fun _ herr => error_implies_collision candidates _ t herr)).trans
      (general_collision_union_bound candidates hinj t)

noncomputable def priorExperiment (candidates : Fin k → Fin n → ZMod A) (prior : PMF (Fin k)) :
    PMF (Fin k × Fin k) := prior.bind fun t => (experiment (m:=m) candidates t).map (fun out => (t,out))

theorem prior_error_bound
    (candidates : Fin k → Fin n → ZMod A) (hinj : Function.Injective candidates) (prior : PMF (Fin k)) :
    (priorExperiment (m:=m) candidates prior).toOuterMeasure {p | p.2 ≠ p.1} ≤
      ((k-1:ℕ):ENNReal) * ((1:ENNReal)/2^m) := by
  rw [priorExperiment, PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' t, prior t * (((k-1:ℕ):ENNReal) * ((1:ENNReal)/2^m)) := by
      apply ENNReal.tsum_le_tsum
      intro t
      apply mul_le_mul' le_rfl
      rw [PMF.toOuterMeasure_map_apply]
      exact general_recovery_error_bound candidates hinj t
    _ = _ := by rw [ENNReal.tsum_mul_right, prior.tsum_coe, one_mul]

theorem integer_redundancy_bound (k l : ℕ) :
    ((k-1:ℕ):ENNReal) * ((1:ENNReal)/2^(Nat.clog 2 k+l)) ≤ (1:ENNReal)/2^l := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have hk : ((k-1:ℕ):ℝ) ≤ (2:ℝ)^(Nat.clog 2 k) := by
    exact_mod_cast (Nat.sub_le k 1).trans (Nat.le_pow_clog (by decide) k)
  have hp : (0:ℝ) < 2^(Nat.clog 2 k) := by positivity
  have hdiv : ((k-1:ℕ):ℝ) / 2^(Nat.clog 2 k) ≤ 1 := (div_le_one hp).2 hk
  have h := mul_le_mul_of_nonneg_right hdiv (show (0:ℝ) ≤ (2^l)⁻¹ by positivity)
  simpa only [pow_add, one_div, mul_inv_rev, div_eq_mul_inv, one_mul, mul_assoc,
    mul_comm ((2:ℝ)^l)⁻¹] using h

theorem prior_redundancy_bound
    (candidates : Fin k → Fin n → ZMod A) (hinj : Function.Injective candidates)
    (prior : PMF (Fin k)) (l : ℕ) :
    (priorExperiment (m:=Nat.clog 2 k+l) candidates prior).toOuterMeasure {p | p.2 ≠ p.1} ≤
      (1:ENNReal)/2^l :=
  (prior_error_bound candidates hinj prior).trans (integer_redundancy_bound k l)

end Qatlib.Papers.SingleQuery97.MainResults.RandomRecovery
