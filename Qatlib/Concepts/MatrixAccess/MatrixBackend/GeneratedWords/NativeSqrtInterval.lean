/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

/-! The actual integer-isqrt dyadic enclosure used by the native parameter
producer. This is the numerator/denominator formula of sqrt_interval, with
its degenerate exact-square branch and actual radicand-size statistic. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords


/-- Construction for native Sqrt Radicand in the native sqrt interval model. -/
def nativeSqrtRadicand (q : ℚ) (p : ℕ) : ℕ := q.num.toNat*2^(2*p)/q.den

/-- Construction for native Sqrt Interval in the native sqrt interval model. -/
def nativeSqrtInterval (q : ℚ) (p : ℕ) : ℚ × ℚ × ℕ :=
  let n := nativeSqrtRadicand q p
  let lo := (Nat.sqrt n : ℚ)/(2 : ℚ)^p
  (lo,if lo^2=q then lo else lo+1/(2 : ℚ)^p,Nat.size n)

/-- The finite construction in `NativeSqrtInterval` satisfies `nativeSqrtRadicand_floor` under the displayed hypotheses. -/
theorem nativeSqrtRadicand_floor (q : ℚ) (p : ℕ) (hq : 0≤q) :
    nativeSqrtRadicand q p=⌊q*(2 : ℚ)^(2*p)⌋₊ := by
  have hn : (q.num.toNat : ℚ)=(q.num : ℚ) := by
    exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq))
  have hrep : (q.num.toNat : ℚ)/(q.den : ℚ)=q := by rw [hn]; exact q.num_div_den
  have harg : ((q.num.toNat*2^(2*p) : ℕ) : ℚ)/(q.den : ℚ)=q*(2 : ℚ)^(2*p) := by
    push_cast
    calc
      _ = ((q.num.toNat : ℚ)/(q.den : ℚ))*(2 : ℚ)^(2*p) := by ring
      _ = _ := by rw [hrep]
  unfold nativeSqrtRadicand
  rw [←Rat.natFloor_natCast_div_natCast,harg]

/-- The finite construction in `NativeSqrtInterval` satisfies `nativeSqrtInterval_rational` under the displayed hypotheses. -/
theorem nativeSqrtInterval_rational (q : ℚ) (p : ℕ) (hq : 0≤q) :
    let b := nativeSqrtInterval q p
    0≤b.1 ∧ b.1≤b.2.1 ∧ b.1^2≤q ∧ q≤b.2.1^2 ∧
      b.2.1-b.1≤1/(2 : ℚ)^p ∧ b.2.2=Nat.size (nativeSqrtRadicand q p) := by
  let n := nativeSqrtRadicand q p
  let S : ℚ := 2^p
  let lo : ℚ := (Nat.sqrt n : ℚ)/S
  have hS : 0<S := by dsimp [S]; positivity
  have hp : (2 : ℚ)^(2*p)=S^2 := by dsimp [S]; rw [Nat.mul_comm 2 p,pow_mul]
  have hnlo : (n : ℚ)≤q*S^2 := by
    have hh := Nat.floor_le (show 0≤q*(2 : ℚ)^(2*p) by positivity)
    rw [←nativeSqrtRadicand_floor q p hq,hp] at hh
    exact hh
  have hnhi : q*S^2<(n : ℚ)+1 := by
    have hh := Nat.lt_floor_add_one (q*(2 : ℚ)^(2*p))
    rw [←nativeSqrtRadicand_floor q p hq,hp] at hh
    exact hh
  have hml : ((Nat.sqrt n : ℚ)^2)≤(n : ℚ) := by exact_mod_cast Nat.sqrt_le' n
  have hmhu : (n : ℚ)+1≤((Nat.sqrt n : ℚ)+1)^2 := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_succ_sqrt' n))
  have hlo0 : 0≤lo := by dsimp [lo]; positivity
  have hl : lo^2≤q := by
    dsimp [lo]
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hS)).mpr (hml.trans hnlo)
  have hh : q≤(lo+1/S)^2 := by
    have he : lo+1/S=((Nat.sqrt n : ℚ)+1)/S := by dsimp [lo]; ring
    rw [he,div_pow]
    exact (le_div_iff₀ (sq_pos_of_pos hS)).mpr (hnhi.le.trans hmhu)
  change 0≤lo ∧ lo≤(if lo^2=q then lo else lo+1/S) ∧ lo^2≤q ∧
    q≤(if lo^2=q then lo else lo+1/S)^2 ∧
    (if lo^2=q then lo else lo+1/S)-lo≤1/S ∧ _
  split_ifs with hExact
  · exact ⟨hlo0,le_rfl,hl,hExact.ge,(by simpa only [sub_self] using (one_div_pos.mpr hS).le),rfl⟩
  · refine ⟨hlo0,?_,hl,hh,?_,rfl⟩
    · linarith [one_div_pos.mpr hS]
    · linarith


/-- The finite construction in `NativeSqrtInterval` satisfies `nativeSqrtInterval_real` under the displayed hypotheses. -/
theorem nativeSqrtInterval_real (q : ℚ) (p : ℕ) (hq : 0≤q) :
      ((nativeSqrtInterval q p).1 : ℝ)≤Real.sqrt (q : ℝ) ∧ Real.sqrt (q : ℝ)≤((nativeSqrtInterval q p).2.1 : ℝ) ∧
      |Real.sqrt (q : ℝ)-((nativeSqrtInterval q p).1 : ℝ)|≤1/(2 : ℝ)^p ∧
      |((((nativeSqrtInterval q p).1+(nativeSqrtInterval q p).2.1)/2 : ℚ) : ℝ)-Real.sqrt (q : ℝ)|≤1/(2*(2 : ℝ)^p) := by
  obtain ⟨hl0,hlh,hlq,hqh,hw,_⟩ := nativeSqrtInterval_rational q p hq
  have hl0r : (0 : ℝ)≤((nativeSqrtInterval q p).1 : ℝ) := by exact_mod_cast hl0
  have hh0r : (0 : ℝ)≤((nativeSqrtInterval q p).2.1 : ℝ) := by exact_mod_cast (hl0.trans hlh)
  have hlqr : ((nativeSqrtInterval q p).1 : ℝ)^2≤(q : ℝ) := by exact_mod_cast hlq
  have hqhr : (q : ℝ)≤((nativeSqrtInterval q p).2.1 : ℝ)^2 := by exact_mod_cast hqh
  have hwr : ((nativeSqrtInterval q p).2.1 : ℝ)-((nativeSqrtInterval q p).1 : ℝ)≤1/(2 : ℝ)^p := by
    have hh : (((nativeSqrtInterval q p).2.1-(nativeSqrtInterval q p).1 : ℚ) : ℝ)≤((1/(2 : ℚ)^p : ℚ) : ℝ) := Rat.cast_le.mpr hw
    push_cast at hh
    exact hh
  have hsq := Real.sq_sqrt (show (0 : ℝ)≤q by exact_mod_cast hq)
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hlo : ((nativeSqrtInterval q p).1 : ℝ)≤Real.sqrt (q : ℝ) := by nlinarith
  have hhi : Real.sqrt (q : ℝ)≤((nativeSqrtInterval q p).2.1 : ℝ) := by nlinarith
  refine ⟨hlo,hhi,?_,?_⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  · push_cast
    rw [abs_le,show 1/(2*(2 : ℝ)^p)=(1/(2 : ℝ)^p)/2 by ring]
    constructor <;> linarith

/-- The finite construction in `NativeSqrtInterval` satisfies `nativeSqrtInterval_lower_one` under the displayed hypotheses. -/
theorem nativeSqrtInterval_lower_one (q : ℚ) (p : ℕ) (hq : 1≤q) :
    1≤(nativeSqrtInterval q p).1 := by
  have hq0 : 0≤q := by linarith
  have hn : (2^p)^2≤nativeSqrtRadicand q p := by
    rw [nativeSqrtRadicand_floor q p hq0]
    apply Nat.le_floor
    push_cast
    rw [←pow_mul,show p*2=2*p by omega]
    exact le_mul_of_one_le_left (by positivity) hq
  have hm : 2^p≤Nat.sqrt (nativeSqrtRadicand q p) := Nat.le_sqrt'.mpr hn
  change (1 : ℚ)≤(Nat.sqrt (nativeSqrtRadicand q p) : ℚ)/(2 : ℚ)^p
  apply (le_div_iff₀ (by positivity : (0 : ℚ)<2^p)).mpr
  simpa only [one_mul,Nat.cast_pow,Nat.cast_ofNat] using (show ((2^p : ℕ) : ℚ)≤Nat.sqrt (nativeSqrtRadicand q p) by exact_mod_cast hm)

/-- The finite construction in `NativeSqrtInterval` satisfies `nativeSqrtInterval_operand_bits` under the displayed hypotheses. -/
theorem nativeSqrtInterval_operand_bits (q : ℚ) (p : ℕ) :
    (nativeSqrtInterval q p).2.2≤Nat.size q.num.toNat+2*p := by
  change Nat.size (nativeSqrtRadicand q p)≤_
  apply Nat.size_le.mpr
  have hn : nativeSqrtRadicand q p≤q.num.toNat*2^(2*p) := Nat.div_le_self _ _
  have hh : q.num.toNat*2^(2*p)<2^(Nat.size q.num.toNat+2*p) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
  exact hn.trans_lt hh

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
