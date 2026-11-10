/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
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
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Defs
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

theorem entropy_ratio_zero (d:ℕ) :
    Tendsto (fun N:ℕ=>Real.log ((N:ℝ)^d+1)/(N:ℝ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun N:ℕ=>Real.log (N:ℝ)/(N:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun N:ℕ=>(Real.log 2+(d:ℝ)*Real.log (N:ℝ))/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [add_div,mul_div_assoc,mul_zero,add_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add (hl.const_mul (d:ℝ))
  apply squeeze_zero' _ _ hb
  · exact Filter.Eventually.of_forall fun N=>div_nonneg
      (Real.log_nonneg (by have hp:=pow_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) d;linarith)) (Nat.cast_nonneg N)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hn:(1:ℝ)≤N := by exact_mod_cast hN
    have hn0:(0:ℝ)<N := by linarith
    have hp : (N:ℝ)^d+1≤2*(N:ℝ)^d := by have h:=one_le_pow₀ hn (n:=d);linarith
    apply div_le_div_of_nonneg_right _ hn0.le
    have hh:=Real.log_le_log (by positivity : (0:ℝ)<(N:ℝ)^d+1) hp
    refine hh.trans_eq ?_
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero d hn0.ne'),Real.log_pow]

theorem grid_entropy_tail_zero (d:ℕ) (c:ℝ) (hc:0<c) :
    Tendsto (fun N:ℕ=>(((N:ℝ)^d+1)^N)*Real.exp (-c*(N:ℝ)^2)) atTop (𝓝 0) := by
  have hsmall := (entropy_ratio_zero d).eventually (eventually_lt_nhds (show (0:ℝ)<c/2 by linarith))
  have hlarge : ∀ᶠ N:ℕ in atTop,2/c≤(N:ℝ) :=
    (tendsto_atTop.1 (tendsto_natCast_atTop_atTop : Tendsto (fun N:ℕ=>(N:ℝ)) atTop atTop)) (2/c)
  have hb : ∀ᶠ N:ℕ in atTop,(((N:ℝ)^d+1)^N)*Real.exp (-c*(N:ℝ)^2)≤Real.exp (-(N:ℝ)) := by
    filter_upwards [hsmall,hlarge,eventually_ge_atTop 1] with N hs hl hN
    have hn:(0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hlog : Real.log ((N:ℝ)^d+1)≤(c/2)*(N:ℝ) :=
      (div_le_iff₀ hn).mp hs.le
    have hcN : 1≤(c/2)*(N:ℝ) := by
      have h := (div_le_iff₀ hc).mp hl
      linarith
    have he : (((N:ℝ)^d+1)^N)*Real.exp (-c*(N:ℝ)^2)=
        Real.exp ((N:ℝ)*Real.log ((N:ℝ)^d+1)-c*(N:ℝ)^2) := by
      rw [show ((N:ℝ)^d+1)^N=Real.exp ((N:ℝ)*Real.log ((N:ℝ)^d+1)) by
        rw [Real.exp_nat_mul,Real.exp_log (by positivity)],← Real.exp_add]
      congr 1
      ring
    rw [he]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog hn.le,mul_le_mul_of_nonneg_right hcN hn.le]
  exact squeeze_zero' (Filter.Eventually.of_forall (fun N=>by positivity)) hb
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)

theorem polynomial_gaussian_tail_zero (d:ℕ) (c:ℝ) (hc:0<c) :
    Tendsto (fun N:ℕ=>(N:ℝ)^d*Real.exp (-c*(N:ℝ)^2)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N=>by positivity)) _
      (grid_entropy_tail_zero d c hc)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn:(1:ℝ)≤N := by exact_mod_cast hN
  have hbase : 1≤(N:ℝ)^d+1 := by
    have hp : (0:ℝ)≤(N:ℝ)^d := by positivity
    linarith
  have hp : (N:ℝ)^d≤((N:ℝ)^d+1)^N := by
    calc
      _ ≤ (N:ℝ)^d+1 := by linarith
      _ ≤ _ := le_self_pow₀ hbase (by omega)
  exact mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
