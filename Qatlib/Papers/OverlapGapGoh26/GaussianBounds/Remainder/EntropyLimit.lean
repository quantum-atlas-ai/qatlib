/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Entropy and Gaussian decay limits

`entropy_ratio_zero` controls the logarithm of a polynomial grid size relative to the dimension.
It yields `grid_entropy_tail_zero` and `polynomial_gaussian_tail_zero`, showing that Gaussian
decay in `N²` dominates the grid entropy and polynomial factors occurring in the remainder
estimates associated with [GohMuller2026].

## Main statements

* `entropy_ratio_zero`: For every natural degree `d`, `log(N^d+1)/N` tends to zero as `N` tends
  to infinity.
* `grid_entropy_tail_zero`: For `c > 0`, the product `(N^d+1)^N * exp(-cN²)` tends to zero as
  `N` tends to infinity.
* `polynomial_gaussian_tail_zero`: For `c > 0`, the product `N^d * exp(-cN²)` tends to zero as
  `N` tends to infinity.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

/-- For every natural degree `d`, `log(N^d+1)/N` tends to zero as `N` tends to infinity. -/
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

/-- For `c > 0`, the product `(N^d+1)^N * exp(-cN²)` tends to zero as `N` tends to infinity. -/
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

/-- For `c > 0`, the product `N^d * exp(-cN²)` tends to zero as `N` tends to infinity. -/
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
