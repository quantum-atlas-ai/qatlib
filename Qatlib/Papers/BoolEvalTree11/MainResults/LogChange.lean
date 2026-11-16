/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.Models
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! # The complete old finite logarithmic change estimate

A derivative barrier proves the actual uniform scalar inequality. The old
comment's proposed inequality 1/(1-c)<=1+2c^2 is false; it is not used here.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.LogChange

/-- The scalar barrier whose nonnegativity bounds the logarithmic range. -/
def barrier (u : ℝ) : ℝ := 2*u+4*u^3-Real.log (1+u)+Real.log (1-u)

/-- Its exact derivative away from the two logarithmic poles. -/
def slope (u : ℝ) : ℝ := 2+12*u^2-(1+u)⁻¹-(1-u)⁻¹

/-- Differentiation of the actual polynomial and two logarithms. -/
theorem barrierDeriv (u : ℝ) (hp : 1+u≠0) (hm : 1-u≠0) :
    HasDerivAt barrier (slope u) u := by
  have hi := hasDerivAt_id u
  have hl := (hi.const_mul 2).add ((hi.pow 3).const_mul 4)
  have ha := ((hasDerivAt_const u 1).add hi).log hp
  have hb := ((hasDerivAt_const u 1).sub hi).log hm
  convert (hl.sub ha).add hb using 1
  · funext t; simp [barrier, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  · simp [slope, div_eq_mul_inv, Pi.add_apply, Pi.sub_apply, id_eq]; ring

/-- The derivative is nonnegative on the full interval below one half. -/
theorem slopeNonneg (u : ℝ) (hu : 0≤u) (hh : u<1/2) : 0≤slope u := by
  have hp : 0<1+u := by linarith
  have hm : 0<1-u := by linarith
  have hs : u^2≤(1/2:ℝ)^2 := pow_le_pow_left₀ hu (le_of_lt hh) 2
  have he : slope u=u^2*(10-12*u^2)/((1+u)*(1-u)) := by
    unfold slope
    field_simp
    ring
  rw [he]
  exact div_nonneg (mul_nonneg (sq_nonneg u) (by nlinarith)) (mul_pos hp hm).le

/-- The worst possible endpoint logarithmic range has the displayed cubic envelope. -/
theorem envelope (c : ℝ) (hc : 0≤c) (hc1 : c<1/2) :
    Real.log (1+c)-Real.log (1-c)≤2*c*(1+2*c^2) := by
  have hd (u : ℝ) (hu : u∈Set.Icc (0:ℝ) c) : HasDerivAt barrier (slope u) u :=
    barrierDeriv u (ne_of_gt (by linarith [hu.1])) (ne_of_gt (by linarith [hu.2]))
  have hm : MonotoneOn barrier (Set.Icc (0:ℝ) c) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 c)
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
      (fun u hu => slopeNonneg u (interior_subset hu).1
        (lt_of_le_of_lt (interior_subset hu).2 hc1))
  have hh := hm (show (0:ℝ)∈Set.Icc 0 c from ⟨le_refl _,hc⟩)
    (show c∈Set.Icc (0:ℝ) c from ⟨hc,le_refl _⟩) hc
  have h0 : barrier 0=0 := by norm_num [barrier]
  rw [h0] at hh
  unfold barrier at hh
  nlinarith

/-- The entire old logarithmic-change target, with all its actual hypotheses. -/
theorem logChange (c p_i p_f : ℝ) (hc : 0≤c) (hc1 : c<1/2)
    (hi : 0<p_i) (hf : 0<p_f)
    (hpi : |p_i-1|≤c) (hpf : |p_f-1|≤c) :
    |Real.log p_f-Real.log p_i|≤2*c*(1+2*c^2) := by
  have hp : 0<1-c := by linarith
  have hil := Real.log_le_log hp (show 1-c≤p_i by linarith [(abs_le.mp hpi).1])
  have hih := Real.log_le_log hi (show p_i≤1+c by linarith [(abs_le.mp hpi).2])
  have hfl := Real.log_le_log hp (show 1-c≤p_f by linarith [(abs_le.mp hpf).1])
  have hfh := Real.log_le_log hf (show p_f≤1+c by linarith [(abs_le.mp hpf).2])
  apply abs_le.mpr
  constructor <;> linarith [envelope c hc hc1]

end Qatlib.Papers.BoolEvalTree11.MainResults.LogChange
