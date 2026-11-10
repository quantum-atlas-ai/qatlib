/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Basic.Unique
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Defs

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Qatlib.Papers.AnyCircuit08.MainResults

abbrev Amplitude (X : Type) := X → ℂ

def IsUnitVector {X : Type} [Fintype X] (ψ : Amplitude X) : Prop :=
  ∑ x, ‖ψ x‖ ^ 2 = 1

def IsUnitary {X : Type} [Fintype X] [DecidableEq X] (U : X → X → ℂ) : Prop :=
  (∀ a b, ∑ x, U a x * star (U b x) = if a = b then 1 else 0) ∧
  (∀ x y : X, ∑ a, star (U a x) * U a y = if x = y then 1 else 0)

def oracleSign {A X : Type} (f : A → X → Bool) (a : A) (x : X) : ℂ :=
  if f a x then -1 else 1

noncomputable def oracleState {A X : Type} [Fintype X]
    (f : A → X → Bool) (a : A) : Amplitude X :=
  fun x => (1 / (Real.sqrt (Fintype.card X) : ℂ)) * oracleSign f a x

structure SingleLevelOracleProblem (A X : Type) where
  f : A → X → Bool

def SolvesSingleLevel {A X : Type} [Fintype X]
    (P : SingleLevelOracleProblem A X) (U : A → X → ℂ) (δ : ℝ) : Prop :=
  ∀ a, δ ≤ ‖∑ x, U a x * oracleState P.f a x‖ ^ 2

structure RecursiveOracleProblem (X A : Type) where
  ℓ : ℕ
  f : A → X → Bool
  secret : List X → A
  answer : Bool

def RecursiveOracleProblem.query {X A : Type} [Inhabited X] [DecidableEq A]
    (P : RecursiveOracleProblem X A) : List X → Option A → Option Bool :=
  fun xs a? =>
    if xs.length < P.ℓ then
      match a? with
      | some a =>
          if xs.length = 0 then
            (if a = P.secret [] then some P.answer else none)
          else
            (if a = P.secret xs then
              some (P.f (P.secret xs.dropLast) xs.getLast!) else none)
      | none => none
    else
      match a? with
      | some _ => none
      | none =>
          if xs.length = P.ℓ then
            some (P.f (P.secret xs.dropLast) xs.getLast!) else none

def IsDispersing {X : Type} [Fintype X] [DecidableEq X]
    (U : X → X → ℂ) (α β : ℝ) : Prop :=
  ∃ A : Finset X, (A.card : ℝ) ≥ (Fintype.card X : ℝ) ^ α ∧
    ∀ a ∈ A, ∑ x, ‖U a x‖ ≥ β * Real.sqrt (Fintype.card X)

def IsPseudoDispersing {M W X : Type} [Fintype M] [Fintype W] [Fintype X] [DecidableEq M]
    (U : M → W → X → ℂ) (α β : ℝ) : Prop :=
  ∃ A : Finset M, (A.card : ℝ) ≥ (Fintype.card X : ℝ) ^ α ∧
    ∀ a ∈ A, ∃ ψ : Amplitude W, IsUnitVector ψ ∧
      ∑ x, ‖∑ w, ψ w * U a w x‖ ≥ β * Real.sqrt (Fintype.card X)

lemma integral_abs_cos_zero_two_pi :
    (∫ φ in (0:ℝ)..(2 * Real.pi), |Real.cos φ|) = 4 := by
  have hcont : Continuous (fun x : ℝ => |Real.cos x|) := by fun_prop
  have hper : Function.Periodic (fun x : ℝ => |Real.cos x|) Real.pi := by
    intro x
    change |Real.cos (x + Real.pi)| = |Real.cos x|
    rw [Real.cos_add_pi, abs_neg]
  have hsplit : (∫ φ in (0:ℝ)..(2 * Real.pi), |Real.cos φ|)
      = (∫ φ in (0:ℝ)..Real.pi, |Real.cos φ|)
        + ∫ φ in Real.pi..(2 * Real.pi), |Real.cos φ| := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hshift : (∫ φ in Real.pi..(2 * Real.pi), |Real.cos φ|)
      = ∫ φ in (0:ℝ)..Real.pi, |Real.cos φ| := by
    have h := hper.intervalIntegral_add_eq (t := Real.pi) (s := 0)
    simpa [two_mul, zero_add] using h
  have hshift2 : (∫ φ in (0:ℝ)..Real.pi, |Real.cos φ|)
      = ∫ φ in (-(Real.pi/2))..(Real.pi/2), |Real.cos φ| := by
    have h := hper.intervalIntegral_add_eq (t := 0) (s := -(Real.pi/2))
    simpa [zero_add, show -(Real.pi/2) + Real.pi = Real.pi/2 by ring] using h
  have hcos : (∫ φ in (-(Real.pi/2))..(Real.pi/2), |Real.cos φ|)
      = ∫ φ in (-(Real.pi/2))..(Real.pi/2), Real.cos φ := by
    apply intervalIntegral.integral_congr
    intro φ hφ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hφ
    change |Real.cos φ| = Real.cos φ
    rw [abs_of_nonneg]
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le hφ.1 hφ.2
  rw [hsplit, hshift, hshift2, hcos, integral_cos]
  simp
  ring

lemma integral_norm_re_exp (z : ℂ) :
    (∫ φ in (0:ℝ)..(2 * Real.pi), ‖(Complex.exp (-(φ:ℂ) * Complex.I) * z).re‖) = 4 * ‖z‖ := by
  have hpt : ∀ φ : ℝ,
      ‖(Complex.exp (-(φ:ℂ) * Complex.I) * z).re‖ = ‖z‖ * |Real.cos (φ - (z.arg:ℝ))| := by
    intro φ
    have hz : (‖z‖ : ℂ) * Complex.exp ((z.arg : ℝ) * Complex.I) = z :=
      Complex.norm_mul_exp_arg_mul_I z
    have hexp : Complex.exp (-(φ:ℂ) * Complex.I) * Complex.exp ((z.arg : ℝ) * Complex.I)
        = Complex.exp (((z.arg : ℝ) - φ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hval : Complex.exp (-(φ:ℂ) * Complex.I) * z
        = (‖z‖ : ℂ) * Complex.exp (((z.arg : ℝ) - φ) * Complex.I) := by
      conv_lhs => rw [← hz]
      rw [← mul_assoc, mul_comm (Complex.exp (-(φ:ℂ) * Complex.I)) (‖z‖ : ℂ), mul_assoc, hexp]
    have hre : (Complex.exp (-(φ:ℂ) * Complex.I) * z).re
        = ‖z‖ * Real.cos ((z.arg : ℝ) - φ) := by
      rw [hval, Complex.re_ofReal_mul, Complex.exp_re]
      simp
    rw [hre, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg z)]
    congr 2
    rw [show (z.arg : ℝ) - φ = -(φ - (z.arg : ℝ)) by ring, Real.cos_neg]
  have hcongr : (∫ φ in (0:ℝ)..(2 * Real.pi), ‖(Complex.exp (-(φ:ℂ) * Complex.I) * z).re‖)
      = ∫ φ in (0:ℝ)..(2 * Real.pi), ‖z‖ * |Real.cos (φ - (z.arg:ℝ))| := by
    apply intervalIntegral.integral_congr
    intro φ _
    exact hpt φ
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hsub : (∫ φ in (0:ℝ)..(2 * Real.pi), |Real.cos (φ - (z.arg:ℝ))|)
      = ∫ ψ in (0 - (z.arg:ℝ))..(2 * Real.pi - (z.arg:ℝ)), |Real.cos ψ| :=
    intervalIntegral.integral_comp_sub_right (fun ψ => |Real.cos ψ|) (z.arg : ℝ)
  rw [hsub]
  have hper : Function.Periodic (fun x : ℝ => |Real.cos x|) (2 * Real.pi) := by
    intro x
    change |Real.cos (x + 2 * Real.pi)| = |Real.cos x|
    rw [Real.cos_add_two_pi]
  have hperEq : (∫ ψ in (0 - (z.arg:ℝ))..(2 * Real.pi - (z.arg:ℝ)), |Real.cos ψ|)
      = ∫ ψ in (0:ℝ)..(2 * Real.pi), |Real.cos ψ| := by
    have h := hper.intervalIntegral_add_eq (t := 0 - (z.arg:ℝ)) (s := 0)
    simpa [zero_add, show -(z.arg:ℝ) + 2 * Real.pi = 2 * Real.pi - (z.arg:ℝ) by ring] using h
  rw [hperEq, integral_abs_cos_zero_two_pi]
  ring

theorem lemma10_signs {X : Type} [Fintype X] (x : X → ℂ) :
    ∃ θ : X → ℤ, (∀ k, θ k = 1 ∨ θ k = -1) ∧
      (2 / Real.pi) * (∑ k, ‖x k‖) ≤ ‖∑ k, (θ k : ℂ) * x k‖ := by
  set F : ℝ → ℝ := fun φ => ∑ k : X, ‖(Complex.exp (-(φ:ℂ) * Complex.I) * x k).re‖
  have hcont : Continuous F := by
    unfold F; fun_prop
  have hInt : (∫ φ in (0:ℝ)..(2 * Real.pi), F φ) = 4 * (∑ k, ‖x k‖) := by
    unfold F
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [integral_norm_re_exp]
      rw [Finset.mul_sum]
    · intro k _
      exact (by fun_prop : Continuous (fun φ : ℝ =>
        ‖(Complex.exp (-(φ:ℂ) * Complex.I) * x k).re‖)).intervalIntegrable _ _
  have hvol_ne : volume (Set.Ioc (0:ℝ) (2 * Real.pi)) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos]))
  have hvol_top : volume (Set.Ioc (0:ℝ) (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hint : IntegrableOn F (Set.Ioc (0:ℝ) (2 * Real.pi)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1
      (hcont.intervalIntegrable _ _)
  obtain ⟨φ, _, hφle⟩ := exists_setAverage_le (μ := volume) (s := Set.Ioc (0:ℝ) (2 * Real.pi))
    hvol_ne hvol_top hint
  have hvol_real : (volume.real (Set.Ioc (0:ℝ) (2 * Real.pi))) = 2 * Real.pi := by
    rw [MeasureTheory.Measure.real_def, Real.volume_Ioc, sub_zero]
    rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hsa : (⨍ a in Set.Ioc (0:ℝ) (2 * Real.pi), F a ∂volume)
      = (2 / Real.pi) * (∑ k, ‖x k‖) := by
    rw [setAverage_eq, smul_eq_mul, hvol_real,
      ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 2 * Real.pi by positivity), hInt]
    field_simp
    ring
  rw [hsa] at hφle
  refine ⟨fun k => if 0 ≤ (Complex.exp (-(φ:ℂ) * Complex.I) * x k).re then 1 else -1, ?_, ?_⟩
  · intro k
    dsimp only
    split_ifs <;> simp
  · set z : X → ℂ := fun k => Complex.exp (-(φ:ℂ) * Complex.I) * x k
    have hstep : F φ ≤ ‖∑ k, ((if 0 ≤ (z k).re then (1:ℤ) else -1) : ℂ) * z k‖ := by
      have hre : (∑ k, ((if 0 ≤ (z k).re then (1:ℤ) else -1) : ℂ) * z k).re = F φ := by
        unfold F z
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : 0 ≤ (Complex.exp (-(φ:ℂ) * Complex.I) * x k).re
        · rw [if_pos h]
          push_cast
          rw [one_mul, Real.norm_eq_abs, abs_of_nonneg h]
        · rw [if_neg h]
          have hneg : (Complex.exp (-(φ:ℂ) * Complex.I) * x k).re < 0 := lt_of_not_ge h
          push_cast
          rw [neg_one_mul, Complex.neg_re, Real.norm_eq_abs, abs_of_neg hneg]
      calc F φ = |(∑ k, ((if 0 ≤ (z k).re then (1:ℤ) else -1) : ℂ) * z k).re| := by
              rw [hre, abs_of_nonneg]
              unfold F
              positivity
        _ ≤ ‖∑ k, ((if 0 ≤ (z k).re then (1:ℤ) else -1) : ℂ) * z k‖ :=
              Complex.abs_re_le_norm _
    have heq : (∑ k, ((if 0 ≤ (z k).re then (1:ℤ) else -1) : ℂ) * z k)
        = Complex.exp (-(φ:ℂ) * Complex.I)
          * ∑ k, ((if 0 ≤ (z k).re then (1:ℤ) else -1) : ℂ) * x k := by
      unfold z
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [heq, norm_mul] at hstep
    have hnorm : ‖Complex.exp (-(φ:ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [hnorm, one_mul] at hstep
    exact le_trans hφle (by simpa [z] using hstep)

theorem theorem9_quantum_part
    {M W X : Type} [Fintype M] [Fintype W] [Fintype X] [DecidableEq M] [Nonempty X]
    (U : M → W → X → ℂ) {α β : ℝ} (hβ : 0 ≤ β)
    (hpd : IsPseudoDispersing U α β) :
    ∃ A : Finset M, (A.card : ℝ) ≥ (Fintype.card X : ℝ) ^ α ∧
      ∀ a ∈ A, ∃ θ : X → ℤ, (∀ x, θ x = 1 ∨ θ x = -1) ∧
        ∃ ψ : Amplitude W, IsUnitVector ψ ∧
          (2 / Real.pi * β) ^ 2 ≤
            ‖(1 / (Real.sqrt (Fintype.card X) : ℂ)) *
              ∑ x, (θ x : ℂ) * ∑ w, ψ w * U a w x‖ ^ 2 := by
  obtain ⟨A, hA, hforall⟩ := hpd
  refine ⟨A, hA, ?_⟩
  intro a ha
  obtain ⟨ψ, hψ, hsum⟩ := hforall a ha
  set z : X → ℂ := fun x => ∑ w, ψ w * U a w x with hz
  obtain ⟨θ, hθsign, hθ⟩ := lemma10_signs z
  refine ⟨θ, hθsign, ψ, hψ, ?_⟩
  have hNpos_nat : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
  have hNpos : (0:ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hNpos_nat
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card X) := Real.sqrt_pos.mpr hNpos
  have hsum' : β * Real.sqrt (Fintype.card X) ≤ ∑ x, ‖z x‖ := by
    simpa [z] using hsum
  have hθ' : (2 / Real.pi) * (∑ x, ‖z x‖) ≤ ‖∑ x, (θ x : ℂ) * z x‖ := hθ
  have hπ : 0 ≤ 2 / Real.pi := by positivity
  have hstep : (2 / Real.pi * β) * Real.sqrt (Fintype.card X)
      ≤ ‖∑ x, (θ x : ℂ) * z x‖ := by
    calc (2 / Real.pi * β) * Real.sqrt (Fintype.card X)
        = (2 / Real.pi) * (β * Real.sqrt (Fintype.card X)) := by ring
      _ ≤ (2 / Real.pi) * (∑ x, ‖z x‖) := by gcongr
      _ ≤ ‖∑ x, (θ x : ℂ) * z x‖ := hθ'
  have hnormc : ‖(1 / (Real.sqrt (Fintype.card X) : ℂ))‖ = 1 / Real.sqrt (Fintype.card X) := by
    rw [norm_div, norm_one]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos]
  have hlow : 2 / Real.pi * β
      ≤ ‖(1 / (Real.sqrt (Fintype.card X) : ℂ)) * ∑ x, (θ x : ℂ) * z x‖ := by
    have h1 : (0:ℝ) ≤ 1 / Real.sqrt (Fintype.card X) :=
      le_of_lt (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hstep h1
    have heq : (1 / Real.sqrt (Fintype.card X)) *
        ((2 / Real.pi * β) * Real.sqrt (Fintype.card X)) = 2 / Real.pi * β := by
      field_simp
    rw [heq] at hmul
    rw [norm_mul, hnormc]
    exact hmul
  have hsq : (2 / Real.pi * β) ^ 2
      ≤ ‖(1 / (Real.sqrt (Fintype.card X) : ℂ)) * ∑ x, (θ x : ℂ) * z x‖ ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hlow
  simpa [z] using hsq

structure ClassicalQueryAlgorithm (A : Type) (q : ℕ) where
  transcript : A → (Fin q → Bool)
  output : (Fin q → Bool) → Option A

noncomputable def ClassicalQueryAlgorithm.successSet {A : Type} {q : ℕ}
    [Fintype A] [DecidableEq A] (alg : ClassicalQueryAlgorithm A q) : Finset A :=
  Finset.univ.filter (fun a => alg.output (alg.transcript a) = some a)

theorem successSet_card_le {A : Type} [Fintype A] [DecidableEq A] {q : ℕ}
    (alg : ClassicalQueryAlgorithm A q) : alg.successSet.card ≤ 2 ^ q := by
  classical
  have hmaps : Set.MapsTo alg.transcript ↑alg.successSet
      ↑(Finset.univ : Finset (Fin q → Bool)) := fun a _ => Finset.mem_univ _
  have hinj : Set.InjOn alg.transcript ↑alg.successSet := by
    intro a ha b hb hab
    have ha' : alg.output (alg.transcript a) = some a := by
      have hmem : a ∈ alg.successSet := ha
      simp only [ClassicalQueryAlgorithm.successSet, Finset.mem_filter] at hmem
      exact hmem.2
    have hb' : alg.output (alg.transcript b) = some b := by
      have hmem : b ∈ alg.successSet := hb
      simp only [ClassicalQueryAlgorithm.successSet, Finset.mem_filter] at hmem
      exact hmem.2
    have hab' : a = b := by
      apply Option.some.inj
      rw [← ha', hab, hb']
    exact hab'
  have hcard := Finset.card_le_card_of_injOn alg.transcript hmaps hinj
  have huniv : (Finset.univ : Finset (Fin q → Bool)).card = 2 ^ q := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  simpa [huniv] using hcard

theorem theorem9_classical_average
    {A : Type} [Fintype A] [DecidableEq A] {n q : ℕ} {α : ℝ}
    (hA : (2:ℝ) ^ (α * (n:ℝ)) ≤ (Fintype.card A : ℝ))
    (alg : ClassicalQueryAlgorithm A q) :
    (alg.successSet.card : ℝ) / (Fintype.card A : ℝ)
      ≤ (2:ℝ) ^ ((q:ℝ) - α * (n:ℝ)) := by
  have hpow2_pos : (0:ℝ) < (2:ℝ) ^ (α * (n:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hApos : (0:ℝ) < (Fintype.card A : ℝ) := lt_of_lt_of_le hpow2_pos hA
  have hcle : (alg.successSet.card : ℝ) ≤ (2:ℝ) ^ (q:ℝ) := by
    have h1 : alg.successSet.card ≤ 2 ^ q := successSet_card_le alg
    have h2 : (alg.successSet.card : ℝ) ≤ ((2:ℝ) ^ q) := by exact_mod_cast h1
    rwa [← Real.rpow_natCast] at h2
  have h2q_pos : (0:ℝ) < (2:ℝ) ^ (q:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul : (alg.successSet.card : ℝ) * (2:ℝ) ^ (α * (n:ℝ))
      ≤ (2:ℝ) ^ (q:ℝ) * (Fintype.card A : ℝ) := by
    have h := mul_le_mul hcle hA (le_of_lt hpow2_pos) (le_of_lt h2q_pos)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [div_le_iff₀ hApos]
  rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ hpow2_pos]
  exact hmul

theorem theorem9_classical_lower_bound
    {A : Type} [Fintype A] [DecidableEq A] {n q : ℕ} {α δ : ℝ}
    (hA : (2:ℝ) ^ (α * (n:ℝ)) ≤ (Fintype.card A : ℝ))
    (hδ : 0 < δ)
    (alg : ClassicalQueryAlgorithm A q)
    (hsucc : δ ≤ (alg.successSet.card : ℝ) / (Fintype.card A : ℝ)) :
    α * (n:ℝ) + Real.logb 2 δ ≤ (q:ℝ) := by
  have h1 := theorem9_classical_average hA alg
  have h2 : δ ≤ (2:ℝ) ^ ((q:ℝ) - α * (n:ℝ)) := le_trans hsucc h1
  have hexp_pos : (0:ℝ) < (2:ℝ) ^ ((q:ℝ) - α * (n:ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlog := Real.logb_le_logb_of_le (b := (2:ℝ)) (by norm_num) hδ h2
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  linarith

def findQueryCount (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => m * (findQueryCount m j + 1)

lemma findQueryCount_closed (m j : ℕ) :
    ((m:ℝ) - 1) * (findQueryCount m j : ℝ) = (m:ℝ)^(j+1) - (m:ℝ) := by
  induction j with
  | zero => simp [findQueryCount]
  | succ j ih =>
      rw [findQueryCount]
      push_cast
      have hp : (m:ℝ)^(j+1+1) = (m:ℝ)^(j+1) * (m:ℝ) := by rw [pow_succ]
      nlinarith [ih, hp]

lemma findQueryCount_le_pow (m j : ℕ) (hm : 2 ≤ m) :
    findQueryCount m j ≤ m ^ (j + 1) := by
  have hclosed := findQueryCount_closed m j
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hq_nonneg : (0:ℝ) ≤ (findQueryCount m j : ℝ) := by positivity
  have hm1 : (1:ℝ) ≤ (m:ℝ) - 1 := by linarith
  have hle1 : (findQueryCount m j : ℝ) ≤ ((m:ℝ)-1) * (findQueryCount m j : ℝ) := by
    nlinarith [hm1, hq_nonneg]
  have hle2 : ((m:ℝ)-1) * (findQueryCount m j : ℝ) ≤ (m:ℝ)^(j+1) := by
    rw [hclosed]
    have hpow : (0:ℝ) ≤ (m:ℝ)^(j+1) := pow_nonneg (by linarith) _
    linarith
  have hcast : (findQueryCount m j : ℝ) ≤ (m:ℝ)^(j+1) := le_trans hle1 hle2
  exact_mod_cast hcast

private lemma nat_le_two_pow (c : ℕ) : c ≤ 2 ^ c := by
  induction c with
  | zero => decide
  | succ d ih =>
      calc d + 1 ≤ 2 ^ d + 2 ^ d := by
            have h2 : 0 < 2 ^ d := pow_pos (by norm_num) d
            omega
        _ = 2 ^ (d + 1) := by rw [pow_succ]; ring

theorem findQueryCount_polynomial (c k n : ℕ) (hc : 2 ≤ c)
    (hn : c ≤ n) (hk : 2 ^ k ≤ n) :
    findQueryCount c k ≤ n ^ (c + 1) := by
  have hcle : c ≤ 2 ^ c := nat_le_two_pow c
  calc findQueryCount c k ≤ c ^ (k + 1) := findQueryCount_le_pow c k hc
    _ = c * c ^ k := by rw [pow_succ, mul_comm]
    _ ≤ c * (2 ^ c) ^ k := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hcle k)
    _ = c * 2 ^ (c * k) := by rw [← pow_mul]
    _ = c * (2 ^ k) ^ c := by rw [mul_comm c k, pow_mul]
    _ ≤ c * n ^ c := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hk c)
    _ ≤ n * n ^ c := Nat.mul_le_mul_right (n ^ c) hn
    _ = n ^ (c + 1) := by rw [pow_succ, mul_comm]

theorem repetition_failure_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ)
    (hm : (4 / δ) * Real.log (8 / δ) ≤ (m:ℝ)) :
    (1 - δ / 2) ^ m ≤ (δ / 8) ^ 2 := by
  have hdel : (0:ℝ) < δ / 2 := by linarith
  have h1 : 1 - δ / 2 ≤ Real.exp (-(δ / 2)) := by
    have := Real.add_one_le_exp (-(δ / 2))
    linarith
  have h2 : (1 - δ / 2) ^ m ≤ (Real.exp (-(δ / 2))) ^ m :=
    pow_le_pow_left₀ (by linarith) h1 m
  have h3 : (Real.exp (-(δ / 2))) ^ m = Real.exp (-(δ / 2) * m) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmul : 2 * Real.log (8 / δ) ≤ (δ / 2) * (m:ℝ) := by
    have h4 : (δ / 2) * ((4 / δ) * Real.log (8 / δ)) = 2 * Real.log (8 / δ) := by
      field_simp
      ring
    calc 2 * Real.log (8 / δ) = (δ / 2) * ((4 / δ) * Real.log (8 / δ)) := h4.symm
      _ ≤ (δ / 2) * (m:ℝ) := mul_le_mul_of_nonneg_left hm hdel.le
  have h5 : Real.exp (-(δ / 2) * (m:ℝ)) ≤ Real.exp (-(2 * Real.log (8 / δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h6 : Real.exp (-(2 * Real.log (8 / δ))) = (δ / 8) ^ 2 := by
    have hlog : Real.log (8 / δ) = -Real.log (δ / 8) := by
      rw [show (8:ℝ) / δ = (δ / 8)⁻¹ by field_simp]
      rw [Real.log_inv]
    rw [hlog]
    have hexp : (-(2 * (-Real.log (δ / 8))) : ℝ) = (2:ℕ) * Real.log (δ / 8) := by
      push_cast
      ring
    rw [hexp, Real.exp_nat_mul, Real.exp_log (by positivity)]
  calc (1 - δ / 2) ^ m ≤ (Real.exp (-(δ / 2))) ^ m := h2
    _ = Real.exp (-(δ / 2) * m) := h3
    _ ≤ Real.exp (-(2 * Real.log (8 / δ))) := h5
    _ = (δ / 8) ^ 2 := h6

theorem theorem4_find_polynomial_time
    (c : ℕ) (hc : 2 ≤ c) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∀ n k : ℕ, c ≤ n → 2 ^ k ≤ n → findQueryCount c k ≤ n ^ (c + 1)) ∧
    (2 / 3 ≤ 1 - (δ / 8) ^ 2) ∧
    (∀ m : ℕ, (4 / δ) * Real.log (8 / δ) ≤ (m:ℝ) →
      (1 - δ / 2) ^ m ≤ (δ / 8) ^ 2) := by
  refine ⟨fun n k hn hk => findQueryCount_polynomial c k n hc hn hk, ?_,
    fun m hm => repetition_failure_bound hδ0 hδ1 m hm⟩
  have hle : δ / 8 ≤ 1 / 8 := by linarith
  have h8nn : (0:ℝ) ≤ δ / 8 := by linarith
  have hsq : (δ / 8) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ h8nn hle 2
  have hsmall : (1 / 8 : ℝ) ^ 2 = 1 / 64 := by norm_num
  rw [hsmall] at hsq
  linarith

def fibre {A σ : Type} [Fintype A] [DecidableEq σ] (φ : A → σ) (y : σ) : Finset A :=
  Finset.univ.filter (fun a => φ a = y)

theorem card_bad_fibres_le {A σ : Type} [Fintype A] [Fintype σ] [DecidableEq σ]
    [DecidableEq A] (φ : A → σ) {B : ℝ} (hB : 0 ≤ B) :
    ((Finset.univ.filter (fun a => ((fibre φ (φ a)).card : ℝ) ≤ B)).card : ℝ)
      ≤ (Fintype.card σ : ℝ) * B := by
  classical
  set s : Finset σ := Finset.univ.filter (fun y => ((fibre φ y).card : ℝ) ≤ B) with hs
  have hsub : Finset.univ.filter (fun a => ((fibre φ (φ a)).card : ℝ) ≤ B)
      ⊆ s.biUnion (fun y => fibre φ y) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.mem_biUnion.mpr ⟨φ a, by simp [hs, ha], by simp [fibre]⟩
  have hc := Finset.card_le_card hsub
  have h2 : (s.biUnion (fun y => fibre φ y)).card ≤ ∑ y ∈ s, (fibre φ y).card :=
    Finset.card_biUnion_le
  have h3 : ((∑ y ∈ s, (fibre φ y).card : ℕ) : ℝ) ≤ ∑ _y ∈ s, B := by
    push_cast
    apply Finset.sum_le_sum
    intro y hy
    have hy' : y ∈ s := hy
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    exact hy'
  have h4 : (∑ _y ∈ s, B) = (s.card : ℝ) * B := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have h5 : (s.card : ℝ) ≤ (Fintype.card σ : ℝ) := by
    have hle : s.card ≤ (Finset.univ : Finset σ).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa using hle
  calc ((Finset.univ.filter (fun a => ((fibre φ (φ a)).card : ℝ) ≤ B)).card : ℝ)
      ≤ ((s.biUnion (fun y => fibre φ y)).card : ℝ) := by exact_mod_cast hc
    _ ≤ ((∑ y ∈ s, (fibre φ y).card : ℕ) : ℝ) := by exact_mod_cast h2
    _ ≤ ∑ _y ∈ s, B := h3
    _ = (s.card : ℝ) * B := h4
    _ ≤ (Fintype.card σ : ℝ) * B := mul_le_mul_of_nonneg_right h5 hB

theorem internal_node_hit_probability
    {A : Type} [Fintype A] [DecidableEq A] (k Q : ℕ) (φ : A → (Fin k → Bool))
    (hM : 1 < Fintype.card A)
    (hQ : (Q:ℝ) < (Fintype.card A : ℝ) ^ (1/3:ℝ)) :
    ((Finset.univ.filter (fun a =>
        ((fibre φ (φ a)).card : ℝ)
          ≤ (Fintype.card A : ℝ) ^ (2/3:ℝ) / (2:ℝ) ^ k)).card : ℝ)
        / (Fintype.card A : ℝ) ≤ (Fintype.card A : ℝ) ^ (-(1/3:ℝ)) ∧
    (∀ a : A, (Fintype.card A : ℝ) ^ (1/3:ℝ) ≤ ((fibre φ (φ a)).card : ℝ) →
      (1:ℝ) / (((fibre φ (φ a)).card : ℝ) - (Q:ℝ))
        ≤ 1 / ((Fintype.card A : ℝ) ^ (1/3:ℝ) - (Q:ℝ))) := by
  have hMpos : (0:ℝ) < (Fintype.card A : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hM)
  have hBpos : (0:ℝ) < (Fintype.card A : ℝ) ^ (2/3:ℝ) := Real.rpow_pos_of_pos hMpos _
  have h2kpos : (0:ℝ) < (2:ℝ) ^ k := by positivity
  constructor
  · have hB : (0:ℝ) ≤ (Fintype.card A : ℝ) ^ (2/3:ℝ) / (2:ℝ) ^ k :=
      le_of_lt (div_pos hBpos h2kpos)
    have hbound := card_bad_fibres_le φ (B := (Fintype.card A : ℝ) ^ (2/3:ℝ) / (2:ℝ) ^ k) hB
    have hcardσ : (Fintype.card (Fin k → Bool) : ℝ) = (2:ℝ) ^ k := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      push_cast
      ring
    rw [hcardσ] at hbound
    have h2kne : (2:ℝ) ^ k ≠ 0 := ne_of_gt h2kpos
    have hbad : ((Finset.univ.filter (fun a =>
        ((fibre φ (φ a)).card : ℝ)
          ≤ (Fintype.card A : ℝ) ^ (2/3:ℝ) / (2:ℝ) ^ k)).card : ℝ)
        ≤ (Fintype.card A : ℝ) ^ (2/3:ℝ) := by
      calc ((Finset.univ.filter (fun a =>
            ((fibre φ (φ a)).card : ℝ)
              ≤ (Fintype.card A : ℝ) ^ (2/3:ℝ) / (2:ℝ) ^ k)).card : ℝ)
          ≤ (2:ℝ) ^ k * ((Fintype.card A : ℝ) ^ (2/3:ℝ) / (2:ℝ) ^ k) := hbound
        _ = (Fintype.card A : ℝ) ^ (2/3:ℝ) := by field_simp
    have hstep : (Fintype.card A : ℝ) ^ (2/3:ℝ) / (Fintype.card A : ℝ)
        = (Fintype.card A : ℝ) ^ (-(1/3:ℝ)) := by
      nth_rewrite 2 [show (Fintype.card A : ℝ) = (Fintype.card A : ℝ) ^ (1:ℝ) from
        (Real.rpow_one _).symm]
      rw [← Real.rpow_sub hMpos]
      rw [show (2/3:ℝ) - 1 = -(1/3) by norm_num]
    have heq : (Fintype.card A : ℝ) ^ (2/3:ℝ)
        = (Fintype.card A : ℝ) ^ (-(1/3:ℝ)) * (Fintype.card A : ℝ) := by
      rw [← hstep]
      field_simp
    rw [div_le_iff₀ hMpos]
    exact le_trans hbad heq.le
  · intro a ha
    have hcube_pos : (0:ℝ) < (Fintype.card A : ℝ) ^ (1/3:ℝ) := Real.rpow_pos_of_pos hMpos _
    have hden : (0:ℝ) < (Fintype.card A : ℝ) ^ (1/3:ℝ) - (Q:ℝ) := by linarith
    have hle : (Fintype.card A : ℝ) ^ (1/3:ℝ) - (Q:ℝ)
        ≤ ((fibre φ (φ a)).card : ℝ) - (Q:ℝ) := by linarith
    exact one_div_le_one_div_of_le hden hle

lemma logb_two_rpow (α : ℝ) (n : ℕ) :
    Real.logb 2 ((2:ℝ) ^ (α * (n:ℝ))) = α * (n:ℝ) := by
  rw [Real.logb_rpow (by norm_num) (by norm_num)]

theorem theorem6_classical_superpolynomial_bound
    (n Q ℓ : ℕ) {M : ℝ} (hM : 1 < M) {c : ℝ} (hc : 0 < c)
    (p : ℝ)
    (hbound : p ≤ 1 / 2 + max ((Q:ℝ) / (M ^ (1/3:ℝ) - (Q:ℝ)))
        ((Q:ℝ) * (Real.logb 2 M / 3) ^ (-(ℓ:ℤ))))
    (hterm₁ : (Q:ℝ) / (M ^ (1/3:ℝ) - (Q:ℝ))
        ≤ (n:ℝ) ^ (-(c * Real.logb 2 (n:ℝ))))
    (hterm₂ : (Q:ℝ) * (Real.logb 2 M / 3) ^ (-(ℓ:ℤ))
        ≤ (n:ℝ) ^ (-(c * Real.logb 2 (n:ℝ)))) :
    p ≤ 1 / 2 + (n:ℝ) ^ (-(c * Real.logb 2 (n:ℝ))) := by
  have hmax : max ((Q:ℝ) / (M ^ (1/3:ℝ) - (Q:ℝ)))
      ((Q:ℝ) * (Real.logb 2 M / 3) ^ (-(ℓ:ℤ)))
      ≤ (n:ℝ) ^ (-(c * Real.logb 2 (n:ℝ))) := max_le hterm₁ hterm₂
  linarith

structure GroupFourierData (G : Type) [Group G] [Fintype G]
    (Irr : Type) [Fintype Irr] where
  d : Irr → ℕ
  d_pos : ∀ lam, 0 < d lam
  sum_sq : ∑ lam, d lam ^ 2 = Fintype.card G
  U : (Σ lam : Irr, Fin (d lam) × Fin (d lam)) → G → ℂ

lemma group_fourier_alpha_ge_half
    {G : Type} [Group G] [Fintype G] {Irr : Type} [Fintype Irr]
    (D : GroupFourierData G Irr) (hG : 1 < Fintype.card G) :
    (1 / 2 : ℝ) ≤ Real.log (∑ lam, (D.d lam : ℝ)) / Real.log (Fintype.card G) := by
  have hd_nonneg : ∀ lam, (0:ℝ) ≤ (D.d lam : ℝ) := fun lam => by positivity
  have hS_nonneg : (0:ℝ) ≤ ∑ lam, (D.d lam : ℝ) :=
    Finset.sum_nonneg (fun lam _ => hd_nonneg lam)

  have hsquare : (∑ lam, (D.d lam : ℝ))^2 = ∑ i, ∑ j, (D.d i : ℝ) * (D.d j : ℝ) := by
    rw [sq, Finset.sum_mul_sum]

  have hdiag_le : ∑ lam, (D.d lam : ℝ)^2 ≤ (∑ lam, (D.d lam : ℝ))^2 := by
    rw [hsquare]
    apply Finset.sum_le_sum
    intro i _
    have hsingle : (D.d i : ℝ) ≤ ∑ j, (D.d j : ℝ) :=
      Finset.single_le_sum (fun j _ => hd_nonneg j) (Finset.mem_univ i)
    calc (D.d i : ℝ)^2 = (D.d i : ℝ) * (D.d i : ℝ) := by ring
      _ ≤ (D.d i : ℝ) * ∑ j, (D.d j : ℝ) :=
          mul_le_mul_of_nonneg_left hsingle (hd_nonneg i)
      _ = ∑ j, (D.d i : ℝ) * (D.d j : ℝ) := by rw [Finset.mul_sum]

  have hsumsq : (∑ lam, (D.d lam : ℝ)^2) = (Fintype.card G : ℝ) := by
    rw [← D.sum_sq]
    push_cast
    ring

  have hcard_le : (Fintype.card G : ℝ) ≤ (∑ lam, (D.d lam : ℝ))^2 := by
    rw [← hsumsq]
    exact hdiag_le
  have hsqrt_le : Real.sqrt (Fintype.card G : ℝ) ≤ ∑ lam, (D.d lam : ℝ) := by
    calc Real.sqrt (Fintype.card G : ℝ) ≤ Real.sqrt ((∑ lam, (D.d lam : ℝ))^2) :=
          Real.sqrt_le_sqrt hcard_le
      _ = ∑ lam, (D.d lam : ℝ) := Real.sqrt_sq hS_nonneg
  have hcard_pos : (0:ℝ) < (Fintype.card G : ℝ) := by
    have h : 0 < Fintype.card G := lt_trans Nat.zero_lt_one hG
    exact_mod_cast h
  have hlog_le : Real.log (Real.sqrt (Fintype.card G : ℝ)) ≤
      Real.log (∑ lam, (D.d lam : ℝ)) :=
    Real.log_le_log (Real.sqrt_pos.mpr hcard_pos) hsqrt_le
  rw [Real.log_sqrt (le_of_lt hcard_pos)] at hlog_le
  have hGlog_pos : 0 < Real.log (Fintype.card G : ℝ) :=
    Real.log_pos (by exact_mod_cast hG)
  rw [le_div_iff₀ hGlog_pos]
  have hhalf : (1/2 : ℝ) * Real.log (Fintype.card G : ℝ) =
      Real.log (Fintype.card G : ℝ) / 2 := by ring
  rw [hhalf]
  exact hlog_le

theorem group_fourier_row_card
    {G : Type} [Group G] [Fintype G] {Irr : Type} [Fintype Irr]
    (D : GroupFourierData G Irr) :
    Fintype.card (Σ lam : Irr, Fin (D.d lam) × Fin (D.d lam)) = Fintype.card G := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have hsq : ∀ lam, D.d lam * D.d lam = D.d lam ^ 2 := fun lam => by ring
  simp only [hsq]
  exact D.sum_sq

theorem theorem11_fourier_pseudo_dispersing
    {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {Irr : Type} [Fintype Irr] [DecidableEq Irr]
    (D : GroupFourierData G Irr) (hG : 1 < Fintype.card G)
    (hα1 : Real.log (∑ lam, (D.d lam : ℝ)) / Real.log (Fintype.card G) ≤ 1)
    (hrow : ∀ a : (Σ lam : Irr, Fin (D.d lam) × Fin (D.d lam)),
      (1 / Real.sqrt 2) * Real.sqrt (Fintype.card G) ≤ ∑ g, ‖D.U a g‖) :
    IsPseudoDispersing
      (fun (a : Σ lam : Irr, Fin (D.d lam) × Fin (D.d lam)) (_ : PUnit) (g : G) => D.U a g)
      (Real.log (∑ lam, (D.d lam : ℝ)) / Real.log (Fintype.card G)) (1 / Real.sqrt 2) := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · have hα0 : (0:ℝ) ≤ Real.log (∑ lam, (D.d lam : ℝ)) / Real.log (Fintype.card G) :=
      le_trans (by norm_num) (group_fourier_alpha_ge_half D hG)
    have hcard : (Finset.univ :
        Finset (Σ lam : Irr, Fin (D.d lam) × Fin (D.d lam))).card = Fintype.card G := by
      rw [Finset.card_univ, group_fourier_row_card D]
    rw [hcard]
    have hG1 : (1:ℝ) ≤ (Fintype.card G : ℝ) := by
      exact_mod_cast (le_of_lt hG)
    exact Real.rpow_le_self_of_one_le hG1 hα1
  · intro a _
    refine ⟨fun _ => 1, ?_, ?_⟩
    · simp [IsUnitVector]
    · simpa using hrow a

noncomputable def cyclicQFT (N : ℕ) [NeZero N] (a x : ZMod N) : ℂ :=
  (1 / (Real.sqrt N : ℂ)) *
    Complex.exp (((2 * Real.pi * ((a * x).val : ℝ) / N : ℝ)) * Complex.I)

theorem cyclicQFT_row_norm (N : ℕ) [NeZero N] (a : ZMod N) :
    ∑ x : ZMod N, ‖cyclicQFT N a x‖ = Real.sqrt N := by
  have hNpos : (0:ℝ) < (N:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt_pos : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNpos
  have hpt : ∀ x : ZMod N, ‖cyclicQFT N a x‖ = 1 / Real.sqrt N := by
    intro x
    unfold cyclicQFT
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt_pos]
  rw [Finset.sum_congr rfl (fun x _ => hpt x)]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [nsmul_eq_mul, mul_one_div, div_eq_iff (ne_of_gt hsqrt_pos)]
  nlinarith [Real.sq_sqrt hNpos.le]

theorem cyclicQFT_dispersing (N : ℕ) [NeZero N] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hN : 1 < N) :
    IsDispersing (cyclicQFT N) α 1 := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · have hcard : ((Finset.univ : Finset (ZMod N)).card : ℝ) = (N:ℝ) := by
      rw [Finset.card_univ, ZMod.card]
    have hXcard : (Fintype.card (ZMod N) : ℝ) = (N:ℝ) := by
      rw [ZMod.card]
    rw [hcard, hXcard]
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (le_of_lt hN)
    exact Real.rpow_le_self_of_one_le hN1 hα1
  · intro a _
    rw [cyclicQFT_row_norm]
    simp

theorem l1_ge_fourth_moment {X : Type} [Fintype X] (y : X → ℝ) (hy : ∀ x, 0 ≤ y x) :
    (∑ x, y x ^ 2) ^ 3 ≤ (∑ x, y x) ^ 2 * (∑ x, y x ^ 4) := by
  set A : ℝ := ∑ x, y x ^ 2 with hAdef
  set B : ℝ := ∑ x, y x with hBdef
  set C : ℝ := ∑ x, y x ^ 3 with hCdef
  set D : ℝ := ∑ x, y x ^ 4 with hDdef
  have hAnn : 0 ≤ A := Finset.sum_nonneg (fun x _ => pow_nonneg (hy x) 2)
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun x _ => hy x)
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun x _ => pow_nonneg (hy x) 3)
  have hDnn : 0 ≤ D := Finset.sum_nonneg (fun x _ => pow_nonneg (hy x) 4)

  have h1 : A ^ 2 ≤ B * C := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun x => Real.sqrt (y x)) (g := fun x => y x * Real.sqrt (y x))

    have hfg : ∀ x, Real.sqrt (y x) * (y x * Real.sqrt (y x)) = y x ^ 2 := by
      intro x
      have hsq : Real.sqrt (y x) * Real.sqrt (y x) = y x := Real.mul_self_sqrt (hy x)
      calc Real.sqrt (y x) * (y x * Real.sqrt (y x))
          = y x * (Real.sqrt (y x) * Real.sqrt (y x)) := by ring
        _ = y x * y x := by rw [hsq]
        _ = y x ^ 2 := by ring
    have hf2 : ∀ x, (Real.sqrt (y x)) ^ 2 = y x := fun x => Real.sq_sqrt (hy x)
    have hg2 : ∀ x, (y x * Real.sqrt (y x)) ^ 2 = y x ^ 3 := by
      intro x
      have hsq : Real.sqrt (y x) * Real.sqrt (y x) = y x := Real.mul_self_sqrt (hy x)
      calc (y x * Real.sqrt (y x)) ^ 2
          = y x ^ 2 * (Real.sqrt (y x) * Real.sqrt (y x)) := by ring
        _ = y x ^ 2 * y x := by rw [hsq]
        _ = y x ^ 3 := by ring
    rw [Finset.sum_congr rfl (fun x _ => hfg x),
      Finset.sum_congr rfl (fun x _ => hf2 x),
      Finset.sum_congr rfl (fun x _ => hg2 x)] at hcs
    simpa only [← hAdef, ← hBdef, ← hCdef] using hcs

  have h2 : C ^ 2 ≤ A * D := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := fun x => y x) (g := fun x => y x ^ 2)
    have hfg : ∀ x, y x * y x ^ 2 = y x ^ 3 := fun x => by ring
    have hf2 : ∀ x, (y x) ^ 2 = y x ^ 2 := fun x => rfl
    have hg2 : ∀ x, (y x ^ 2) ^ 2 = y x ^ 4 := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => hfg x),
      Finset.sum_congr rfl (fun x _ => hf2 x),
      Finset.sum_congr rfl (fun x _ => hg2 x)] at hcs
    simpa only [← hAdef, ← hCdef, ← hDdef] using hcs

  have h4 : A ^ 4 ≤ B ^ 2 * (A * D) := by
    calc A ^ 4 = (A ^ 2) ^ 2 := by ring
      _ ≤ (B * C) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = B ^ 2 * C ^ 2 := by ring
      _ ≤ B ^ 2 * (A * D) := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · have hall : ∀ x, y x = 0 := by
      intro x
      have hx2 : y x ^ 2 = 0 := by
        have hle : y x ^ 2 ≤ A := by
          rw [hAdef]
          exact Finset.single_le_sum (fun i _ => pow_nonneg (hy i) 2) (Finset.mem_univ x)
        rw [← hA0] at hle
        exact le_antisymm hle (pow_nonneg (hy x) 2)
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hx2
    have hA0' : A = 0 := hA0.symm
    rw [hA0']
    have hB0 : B = 0 := by
      rw [hBdef]
      exact Finset.sum_eq_zero (fun x _ => hall x)
    rw [hB0]
    simp
  · have hdiv : A ^ 3 ≤ B ^ 2 * D := by
      have hkey : A * A ^ 3 ≤ A * (B ^ 2 * D) := by
        calc A * A ^ 3 = A ^ 4 := by ring
          _ ≤ B ^ 2 * (A * D) := h4
          _ = A * (B ^ 2 * D) := by ring
      exact le_of_mul_le_mul_left hkey hApos
    simpa only [← hAdef, ← hBdef, ← hDdef] using hdiv

theorem card_bad_of_fourth_moment {X : Type} [Fintype X] (y : X → ℝ) (hy : ∀ x, 0 ≤ y x)
    {T c : ℝ} (hc : 0 < c) (hT : ∑ x, y x ^ 4 ≤ T) :
    ((Finset.univ.filter (fun x => c ≤ y x ^ 4)).card : ℝ) * c ≤ T := by
  set S : Finset X := Finset.univ.filter (fun x => c ≤ y x ^ 4) with hS
  have h1 : ∑ x ∈ S, c ≤ ∑ x ∈ S, y x ^ 4 := by
    apply Finset.sum_le_sum
    intro x hx
    have hx' : x ∈ S := hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    exact hx'
  have h2 : (∑ x ∈ S, y x ^ 4) ≤ T := by
    refine le_trans ?_ hT
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro x _ _
    exact pow_nonneg (hy x) 4
  have h3 : (∑ x ∈ S, c) = (S.card : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h3] at h1
  exact le_trans h1 h2

theorem theorem12_random_circuits_dispersing
    (N : ℕ) [NeZero N] (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β)
    (y : ZMod N → ℝ) (hy : ∀ x, 0 ≤ y x) (hunit : ∑ x, y x ^ 2 = 1)
    (hQ : ∑ x, y x ^ 4 ≤ 1 / ((N:ℝ) * β ^ 2)) :
    (N:ℝ) * β ^ 2 ≤ (∑ x, y x) ^ 2 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNβ : (0:ℝ) < (N:ℝ) * β ^ 2 := by positivity
  have hmain := l1_ge_fourth_moment y hy
  rw [hunit] at hmain
  norm_num at hmain

  have hDpos : (0:ℝ) < ∑ x, y x ^ 4 := by
    rcases eq_or_lt_of_le (Finset.sum_nonneg (fun x _ => pow_nonneg (hy x) 4)) with h0 | hpos
    · exfalso
      rw [← h0] at hmain
      simp at hmain
      linarith
    · exact hpos
  have hmain' : 1 ≤ (∑ x, y x) ^ 2 * (∑ x, y x ^ 4) := hmain
  have hDle : (∑ x, y x ^ 4) ≤ 1 / ((N:ℝ) * β ^ 2) := hQ
  have hDpos' : (0:ℝ) < 1 / ((N:ℝ) * β ^ 2) := by positivity
  have hstep : 1 ≤ (∑ x, y x) ^ 2 * (1 / ((N:ℝ) * β ^ 2)) := by
    calc (1:ℝ) ≤ (∑ x, y x) ^ 2 * (∑ x, y x ^ 4) := hmain'
      _ ≤ (∑ x, y x) ^ 2 * (1 / ((N:ℝ) * β ^ 2)) :=
          mul_le_mul_of_nonneg_left hDle (by positivity)

  have h2 : 1 * ((N:ℝ) * β ^ 2)
      ≤ ((∑ x, y x) ^ 2 * (1 / ((N:ℝ) * β ^ 2))) * ((N:ℝ) * β ^ 2) :=
    mul_le_mul_of_nonneg_right hstep hNβ.le
  have heq : ((∑ x, y x) ^ 2 * (1 / ((N:ℝ) * β ^ 2))) * ((N:ℝ) * β ^ 2)
      = (∑ x, y x) ^ 2 := by
    field_simp
  rw [heq] at h2
  simpa using h2

abbrev PauliString (n : ℕ) := Fin n → Fin 4

noncomputable def stationaryWeight (n : ℕ) (p : PauliString n) : ℝ :=
  if p = 0 then (1:ℝ) / (2:ℝ)^n else 1 / ((4:ℝ)^n + (2:ℝ)^n)

noncomputable def randomCircuitStep (n : ℕ) (μ : PauliString n → ℝ) : PauliString n → ℝ :=
  fun q =>
    if n < 2 then μ q
    else
      (1 / (((n * (n - 1) : ℕ)) : ℝ)) *
        ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then
          (∑ p : PauliString n,
            μ p *
              (if p i = 0 ∧ p j = 0 then
                (if q = p then 1 else 0)
               else if q i = 0 ∧ q j = 0 then 0
               else if (∀ k : Fin n, k ≠ i → k ≠ j → q k = p k) then (1 / 15 : ℝ)
               else 0))
        else 0

theorem lemma13_stationary_values (n : ℕ) :
    stationaryWeight n 0 = (1:ℝ) / (2:ℝ)^n ∧
      ∀ p : PauliString n, p ≠ 0 →
        stationaryWeight n p = (1:ℝ) / ((4:ℝ)^n + (2:ℝ)^n) := by
  refine ⟨?_, ?_⟩
  · simp [stationaryWeight]
  · intro p hp
    simp [stationaryWeight, hp]

theorem stationaryWeight_sum (n : ℕ) :
    ∑ p : PauliString n, stationaryWeight n p = 1 := by
  classical
  have hcard : Fintype.card (PauliString n) = 4 ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hz : stationaryWeight n 0 = 1 / (2:ℝ)^n := by simp [stationaryWeight]
  have hconst : ∀ p ∈ (Finset.univ.erase (0 : PauliString n)),
      stationaryWeight n p = 1 / ((4:ℝ)^n + (2:ℝ)^n) := by
    intro p hp
    have hpne : p ≠ 0 := Finset.ne_of_mem_erase hp
    simp [stationaryWeight, hpne]
  have hsum_erase : ∑ p ∈ (Finset.univ.erase (0 : PauliString n)), stationaryWeight n p
      = ((Finset.univ.erase (0 : PauliString n)).card : ℝ)
          * (1 / ((4:ℝ)^n + (2:ℝ)^n)) := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard_erase : (Finset.univ.erase (0 : PauliString n)).card = 4 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
  have hsplit : ∑ p : PauliString n, stationaryWeight n p
      = stationaryWeight n 0
        + ∑ p ∈ (Finset.univ.erase (0 : PauliString n)), stationaryWeight n p := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (PauliString n))
      (fun p => stationaryWeight n p) (Finset.mem_univ (0 : PauliString n))
    rw [← h]
    ring
  rw [hsplit, hz, hsum_erase, hcard_erase]
  have h4sub : (1:ℕ) ≤ 4 ^ n := by
    simpa using Nat.pow_le_pow_left (show (1:ℕ) ≤ 4 by norm_num) n
  have hcast : ((4 ^ n - 1 : ℕ) : ℝ) = (4:ℝ)^n - 1 := by
    rw [Nat.cast_sub h4sub]
    push_cast
    ring
  rw [hcast]
  have h2 : (0:ℝ) < (2:ℝ)^n := by positivity
  have h2n : (2:ℝ)^n ≠ 0 := ne_of_gt h2
  have h4n : (4:ℝ)^n + (2:ℝ)^n ≠ 0 := by positivity
  have hpow : (2:ℝ) ^ (n * 2) = (4:ℝ) ^ n := by
    rw [mul_comm, pow_mul]
    norm_num
  field_simp
  ring_nf
  rw [hpow]

theorem lemma13_markov_chain_properties (n : ℕ) (hn : 2 ≤ n) :
    (∀ p : PauliString n, p ≠ 0 → 0 < stationaryWeight n p) ∧
    (∑ p : PauliString n, stationaryWeight n p = 1) ∧
    (stationaryWeight n 0 = (1:ℝ) / (2:ℝ)^n) := by
  refine ⟨?_, stationaryWeight_sum n, ?_⟩
  · intro p hp
    rw [stationaryWeight, if_neg hp]
    positivity
  · simp [stationaryWeight]

theorem theorem2_superpolynomial_speedup
    (c : ℕ) (hc : 2 ≤ c) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∀ n k : ℕ, c ≤ n → 2 ^ k ≤ n → findQueryCount c k ≤ n ^ (c + 1)) ∧
    (∀ (n Q ℓ : ℕ) (M cc : ℝ), 1 < M → 0 < cc →
      ∀ p : ℝ, p ≤ 1 / 2 + max ((Q:ℝ) / (M ^ (1/3:ℝ) - (Q:ℝ)))
          ((Q:ℝ) * (Real.logb 2 M / 3) ^ (-(ℓ:ℤ))) →
      (Q:ℝ) / (M ^ (1/3:ℝ) - (Q:ℝ)) ≤ (n:ℝ) ^ (-(cc * Real.logb 2 (n:ℝ))) →
      (Q:ℝ) * (Real.logb 2 M / 3) ^ (-(ℓ:ℤ))
        ≤ (n:ℝ) ^ (-(cc * Real.logb 2 (n:ℝ))) →
      p ≤ 1 / 2 + (n:ℝ) ^ (-(cc * Real.logb 2 (n:ℝ)))) := by
  refine ⟨fun n k hn hk => findQueryCount_polynomial c k n hc hn hk, ?_⟩
  intro n Q ℓ M cc hM hc' p hb h1 h2
  exact theorem6_classical_superpolynomial_bound n Q ℓ hM hc' p hb h1 h2

end Qatlib.Papers.AnyCircuit08.MainResults
