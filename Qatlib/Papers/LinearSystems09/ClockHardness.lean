/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinearSystems09.ClockHardness

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable def clockedContraction {n : ℕ} (T : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Real.exp (-(1 / (T : ℝ))) : ℂ) • U

noncomputable def clockedMatrix {n : ℕ} (T : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 0 (1 - clockedContraction T U) (1 - clockedContraction T U)ᴴ 0

theorem source_A34_isHermitian {n : ℕ} (T : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    (clockedMatrix T U).IsHermitian := by
  rw [clockedMatrix, Matrix.isHermitian_fromBlocks_iff]
  refine ⟨?_, rfl, ?_, ?_⟩ <;> simp [Matrix.IsHermitian]

theorem source_A34_block_action {n : ℕ} (T : ℕ) (U : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n → ℂ) :
    clockedMatrix T U *ᵥ Sum.elim x y =
      Sum.elim ((1 - clockedContraction T U) *ᵥ y) ((1 - clockedContraction T U)ᴴ *ᵥ x) := by
  rw [clockedMatrix, Matrix.fromBlocks_mulVec]
  simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]

theorem source_A35_neumann_truncation {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    (1 - X) * (Finset.range m).sum (fun k => X ^ k) = 1 - X ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ']
      noncomm_ring

theorem source_A35_clocked_pow {n : ℕ} (T : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (clockedContraction T U) ^ k =
      ((Real.exp (-(1 / (T : ℝ))) : ℂ) ^ k) • U ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp [clockedContraction, smul_smul, pow_succ, mul_comm]

theorem source_A34_dimension (n : ℕ) (T : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    Fintype.card (Fin n ⊕ Fin n) = 2 * (Fintype.card (Fin n)) := by
  simp [Fintype.card_sum]
  omega

noncomputable def clockDamping (T : ℕ) : ℝ := Real.exp (-(1 / (T : ℝ)))

theorem clockedContraction_eq_smul {n : ℕ} (T : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) :
    clockedContraction T U = (clockDamping T : ℂ) • U := by
  simp [clockedContraction, clockDamping]

theorem coe_clockDamping_norm (T : ℕ) :
    ‖((clockDamping T : ℝ) : ℂ)‖ = clockDamping T := by
  rw [Complex.norm_real,
    Real.norm_of_nonneg (show (0:ℝ) ≤ clockDamping T from le_of_lt (Real.exp_pos _))]

theorem clockDamping_pos (T : ℕ) : 0 < clockDamping T := Real.exp_pos _

theorem clockDamping_nonneg (T : ℕ) : 0 ≤ clockDamping T := le_of_lt (clockDamping_pos T)

theorem clockDamping_lt_one {T : ℕ} (hT : 1 ≤ T) : clockDamping T < 1 := by
  rw [clockDamping, Real.exp_lt_one_iff]
  have hT' : (0:ℝ) < (T:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hT)
  have : (0:ℝ) < 1 / (T:ℝ) := by positivity
  linarith

theorem clockDamping_le_ratio {T : ℕ} (hT : 1 ≤ T) :
    clockDamping T ≤ (T:ℝ)/((T:ℝ)+1) := by
  rw [clockDamping, Real.exp_neg]
  have hT' : (0:ℝ) < (T:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hT)
  have hb_pos : (0:ℝ) < 1 + 1/(T:ℝ) := by positivity
  have h := Real.add_one_le_exp (1/(T:ℝ))
  have h' : 1 + 1/(T:ℝ) ≤ Real.exp (1/(T:ℝ)) := by linarith
  have h2 : (Real.exp (1/(T:ℝ)))⁻¹ ≤ (1 + 1/(T:ℝ))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hb_pos h'
  have h3 : (1 + 1/(T:ℝ))⁻¹ = (T:ℝ)/((T:ℝ)+1) := by field_simp
  rw [h3] at h2
  exact h2

theorem clockedContraction_norm_le {n : ℕ} [NeZero n] (T : ℕ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖clockedContraction T U‖ ≤ clockDamping T := by
  have hnorm : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
  have heq : ‖clockedContraction T U‖ = clockDamping T := by
    rw [clockedContraction_eq_smul, norm_smul, coe_clockDamping_norm, hnorm, mul_one]
  exact le_of_eq heq

theorem clockedBlock_norm_le {n : ℕ} [NeZero n] (T : ℕ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖(1 : Matrix (Fin n) (Fin n) ℂ) - clockedContraction T U‖ ≤ 1 + clockDamping T := by
  have h := clockedContraction_norm_le T U hU
  calc ‖(1 : Matrix (Fin n) (Fin n) ℂ) - clockedContraction T U‖
      ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖clockedContraction T U‖ := norm_sub_le _ _
    _ ≤ 1 + clockDamping T := by rw [norm_one]; linarith

theorem clockedNeumann_norm_le {n : ℕ} [NeZero n] (T : ℕ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hT : 1 ≤ T) :
    ‖∑' k : ℕ, (clockedContraction T U) ^ k‖ ≤ (1 - clockDamping T)⁻¹ := by
  have hcle : ‖clockedContraction T U‖ ≤ clockDamping T := clockedContraction_norm_le T U hU
  have hlt : ‖clockedContraction T U‖ < 1 := lt_of_le_of_lt hcle (clockDamping_lt_one hT)
  have hbound := tsum_geometric_le_of_norm_lt_one (clockedContraction T U) hlt
  have hone : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := norm_one
  rw [hone] at hbound
  simp only [sub_self, zero_add] at hbound
  have hpos1 : (0:ℝ) < 1 - clockDamping T := by linarith [clockDamping_lt_one hT]
  have hstep : (1 - ‖clockedContraction T U‖)⁻¹ ≤ (1 - clockDamping T)⁻¹ := by
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le hpos1
    linarith
  exact le_trans hbound hstep

theorem source_A34_condition_number {n : ℕ} [NeZero n] (T : ℕ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hT : 1 ≤ T) :
    ‖(1 : Matrix (Fin n) (Fin n) ℂ) - clockedContraction T U‖ *
      ‖∑' k : ℕ, (clockedContraction T U) ^ k‖ ≤ 2 * (T:ℝ) + 1 := by
  have hb := clockedBlock_norm_le T U hU
  have hn := clockedNeumann_norm_le T U hU hT
  have hbnn : 0 ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ) - clockedContraction T U‖ := norm_nonneg _
  have hnnn : 0 ≤ ‖∑' k : ℕ, (clockedContraction T U) ^ k‖ := norm_nonneg _
  have hcle : clockDamping T ≤ (T:ℝ)/((T:ℝ)+1) := clockDamping_le_ratio hT
  have step1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ) - clockedContraction T U‖ *
      ‖∑' k : ℕ, (clockedContraction T U) ^ k‖ ≤ (1 + clockDamping T) * (1 - clockDamping T)⁻¹ :=
    mul_le_mul hb hn hnnn (by rw [clockDamping]; positivity)
  have hratio : (1 + clockDamping T) * (1 - clockDamping T)⁻¹ ≤ 2 * (T:ℝ) + 1 := by
    have hc1 : clockDamping T < 1 := clockDamping_lt_one hT
    have hpos : (0:ℝ) < 1 - clockDamping T := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have hmul : (2*(T:ℝ)+2) * clockDamping T ≤ (2*(T:ℝ)+2) * ((T:ℝ)/((T:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hcle (by positivity)
    have heq : (2*(T:ℝ)+2) * ((T:ℝ)/((T:ℝ)+1)) = 2*(T:ℝ) := by field_simp
    nlinarith [hmul, heq.le, heq.ge]
  linarith [step1, hratio]

noncomputable def clockWeight (T k : ℕ) : ℝ := clockDamping T ^ (2 * k)

theorem clockDamping_pow_fourT {T : ℕ} (hT : 1 ≤ T) :
    clockDamping T ^ (4 * T) = Real.exp (-4) := by
  have hT' : (0:ℝ) < (T:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hT)
  rw [clockDamping, ← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem source_A37_window_mass {T : ℕ} (hT : 1 ≤ T) :
    (T:ℝ) * Real.exp (-4) ≤ ∑ k ∈ Finset.Icc (T+1) (2*T), clockWeight T k := by
  have hcard : (Finset.Icc (T+1) (2*T)).card = T := by
    rw [Nat.card_Icc]
    omega
  have hterm : ∀ k ∈ Finset.Icc (T+1) (2*T), Real.exp (-4) ≤ clockWeight T k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk2 : 2 * k ≤ 4 * T := by omega
    have hcn : clockDamping T ^ (4 * T) ≤ clockDamping T ^ (2 * k) :=
      pow_le_pow_of_le_one (clockDamping_nonneg T) (le_of_lt (clockDamping_lt_one hT)) hk2
    rw [clockDamping_pow_fourT hT] at hcn
    show Real.exp (-4) ≤ clockDamping T ^ (2 * k)
    exact hcn
  calc (T:ℝ) * Real.exp (-4)
      = (Finset.Icc (T+1) (2*T)).card • Real.exp (-4) := by
          rw [hcard, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Icc (T+1) (2*T), clockWeight T k := by
          apply Finset.card_nsmul_le_sum
          intro k hk
          exact hterm k hk

theorem geomIter_bound (T : ℕ → ℝ) (δ : ℝ) (hT0 : 1 ≤ T 0) (hδ2 : δ ≤ 2)
    (hstep : ∀ i, T (i + 1) ≤ (T i) ^ (1 - δ / 2)) (hT : ∀ i, 1 ≤ T i) :
    ∀ i, T i ≤ (T 0) ^ ((1 - δ / 2) ^ i) := by
  intro i
  induction i with
  | zero => rw [pow_zero, Real.rpow_one]
  | succ i ih =>
      have hexp : (0 : ℝ) ≤ 1 - δ / 2 := by linarith
      calc T (i + 1) ≤ (T i) ^ (1 - δ / 2) := hstep i
        _ ≤ ((T 0) ^ ((1 - δ / 2) ^ i)) ^ (1 - δ / 2) :=
              Real.rpow_le_rpow (by linarith [hT i]) ih hexp
        _ = (T 0) ^ ((1 - δ / 2) ^ i * (1 - δ / 2)) :=
              (Real.rpow_mul (by linarith : (0 : ℝ) ≤ T 0) _ _).symm
        _ = (T 0) ^ ((1 - δ / 2) ^ (i + 1)) := by rw [pow_succ]

theorem geomIter_stop (T : ℕ → ℝ) (δ : ℝ) (hT0 : 1 ≤ T 0) (hδ2 : δ ≤ 2)
    (hstep : ∀ i, T (i + 1) ≤ (T i) ^ (1 - δ / 2)) (hT : ∀ i, 1 ≤ T i)
    {K : ℝ} (hK : 1 ≤ K) (ℓ : ℕ)
    (hℓ : ((1 - δ / 2) ^ ℓ) * Real.log (T 0) ≤ Real.log K) :
    T ℓ ≤ K := by
  have hbound := geomIter_bound T δ hT0 hδ2 hstep hT ℓ
  have hT0pos : (0 : ℝ) < T 0 := by linarith
  have hKpos : (0 : ℝ) < K := by linarith
  calc T ℓ ≤ (T 0) ^ ((1 - δ / 2) ^ ℓ) := hbound
    _ ≤ K := (Real.rpow_le_iff_le_log hT0pos hKpos).mpr hℓ

theorem geom_exponent_tendsto_zero (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ < 4) :
    Filter.Tendsto (fun i : ℕ => (1 - δ / 2) ^ i) Filter.atTop (nhds 0) := by
  rw [tendsto_pow_atTop_nhds_zero_iff, abs_lt]
  constructor <;> linarith

theorem source_A37_full_dimension (n T : ℕ) :
    18 * T * 2 ^ n = 3 * (6 * T * 2 ^ n) := by ring

theorem clockDamping_pow {T : ℕ} (hT : 1 ≤ T) (k : ℕ) :
    clockDamping T ^ k = Real.exp (-(((k : ℕ) : ℝ) / (T : ℝ))) := by
  have hT' : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hT'
  rw [clockDamping, ← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem clockWeight_eq_exp {T : ℕ} (hT : 1 ≤ T) (k : ℕ) :
    clockWeight T k = Real.exp (-(((2 * k : ℕ) : ℝ) / (T : ℝ))) := by
  unfold clockWeight
  rw [clockDamping_pow hT]

end Qatlib.Papers.LinearSystems09.ClockHardness
