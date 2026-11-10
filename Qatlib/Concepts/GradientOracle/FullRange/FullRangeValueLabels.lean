/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeValueGradient
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.FullRange
open Matrix
open scoped Classical

theorem full_range_value_oracle_eq_addOracle {X : Type} [Fintype X] [DecidableEq X]
    (N : ℕ) [NeZero N] (v : X → ZMod N) : gradientValueOracle N v = AddOracle v := by
  rw [addOracle_eq_permMatrix]
  ext x y
  simp [gradientValueOracle,permMatrix,addOracleEquiv,Prod.ext_iff]

theorem full_range_integer_bounds {X : Type} (K k : ℕ) (f : X → ℝ) (lo s R : ℝ)
    (hs : 0<s) (_hR : 0≤R) (hguard : s*R<(2:ℝ)^K)
    (hf : ∀ x,lo≤f x ∧ f x≤lo+R) (x : X) :
    0≤fullRangeInteger k f lo s x ∧ fullRangeInteger k f lo s x<(2^(K+k):ℕ) ∧
    ((fullRangeValueTable K k f lo s x).val:ℤ)=fullRangeInteger k f lo s x := by
  let y := (2:ℝ)^k*s*(f x-lo)
  have hy0 : 0≤y := mul_nonneg (by positivity) (sub_nonneg.mpr (hf x).1)
  have hy : y<(2:ℝ)^(K+k) := by
    have hm := mul_lt_mul_of_pos_left hguard (by positivity : (0:ℝ)<(2:ℝ)^k)
    have hb := mul_le_mul_of_nonneg_left (show s*(f x-lo) ≤ s*R by nlinarith [(hf x).2])
      (by positivity : (0:ℝ)≤(2:ℝ)^k)
    dsimp only [y]
    rw [pow_add] at ⊢
    nlinarith only [hm,hb]
  have hi0 : 0≤fullRangeInteger k f lo s x := Int.floor_nonneg.mpr hy0
  have hiL : fullRangeInteger k f lo s x<(2^(K+k):ℕ) := by
    apply Int.floor_lt.mpr
    dsimp only [y] at hy
    exact_mod_cast hy
  refine ⟨hi0,hiL,?_⟩
  unfold fullRangeValueTable
  rw [ZMod.val_intCast,Int.emod_eq_of_lt hi0 hiL]

theorem full_range_decoding_precision {X : Type} (K k : ℕ) (f : X → ℝ) (lo s R : ℝ)
    (hs : 0<s) (hR : 0≤R) (hguard : s*R<(2:ℝ)^K)
    (hf : ∀ x,lo≤f x ∧ f x≤lo+R) (x : X) :
    0≤f x-(lo+((fullRangeValueTable K k f lo s x).val:ℝ)/(s*(2:ℝ)^k)) ∧
    f x-(lo+((fullRangeValueTable K k f lo s x).val:ℝ)/(s*(2:ℝ)^k))<1/(s*(2:ℝ)^k) := by
  let y := (2:ℝ)^k*s*(f x-lo)
  have hv : ((fullRangeValueTable K k f lo s x).val:ℝ)=(fullRangeInteger k f lo s x:ℝ) := by
    exact_mod_cast (full_range_integer_bounds K k f lo s R hs hR hguard hf x).2.2
  have hden : 0<s*(2:ℝ)^k := by positivity
  have hl : (fullRangeInteger k f lo s x:ℝ) ≤ y := Int.floor_le y
  have hu : y < (fullRangeInteger k f lo s x:ℝ)+1 := Int.lt_floor_add_one y
  have he : f x-(lo+((fullRangeValueTable K k f lo s x).val:ℝ)/(s*(2:ℝ)^k)) =
      (y-(fullRangeInteger k f lo s x:ℝ))/(s*(2:ℝ)^k) := by
    rw [hv]
    dsimp only [y]
    field_simp
    ring
  rw [he]
  constructor
  · exact div_nonneg (by exact sub_nonneg.mpr hl) hden.le
  · exact (div_lt_div_iff_of_pos_right hden).mpr (by linarith)

theorem full_range_basis_value_query {X : Type} [Fintype X] [DecidableEq X]
    (K k : ℕ) (f : X → ℝ) (lo s : ℝ) (x : X) :
    ApplyGate (gradientValueOracle (2^(K+k)) (fullRangeValueTable K k f lo s)) (Ket (x,0)) =
      Ket (x,fullRangeValueTable K k f lo s x) := by
  rw [full_range_value_oracle_eq_addOracle,applyGate_addOracle_ket]
  simp

end Qatlib.Concepts.GradientOracle.FullRange
