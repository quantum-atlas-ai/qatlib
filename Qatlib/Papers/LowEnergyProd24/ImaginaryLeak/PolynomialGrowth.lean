/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Set Filter
open scoped Topology
namespace Qatlib.Papers.LowEnergyProd24.ImaginaryLeak

theorem polynomial_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ→E) (C δ b : ℝ) (p : ℕ) (hδ : 0 ≤ δ)
    (hf : ContinuousOn f (Icc 0 b))
    (hf' : ∀t∈Ico 0 b,HasDerivWithinAt f (f' t) (Ici t) t)
    (h0 : ‖f 0‖ ≤ δ) (hbound : ∀t∈Ico 0 b,‖f' t‖ ≤ C*t^p*‖f t‖)
    (t : ℝ) (ht : t∈Icc 0 b) :
    ‖f t‖ ≤ δ*Real.exp (C*t^(p+1)/(p+1)) := by
  have hp : (p+1:ℝ)≠0 := by positivity
  have heps : ∀ε∈Ioi (0:ℝ),‖f t‖ ≤ (δ+ε)*Real.exp (C*t^(p+1)/(p+1)+ε*t) := by
    intro ε hε
    change 0 < ε at hε
    let B : ℝ→ℝ:=fun x=>(δ+ε)*Real.exp (C*x^(p+1)/(p+1)+ε*x)
    have hB : ∀x,HasDerivAt B (B x*(C*x^p+ε)) x := by
      intro x
      have hi : HasDerivAt (fun y:ℝ=>C*y^(p+1)/(p+1)+ε*y) (C*x^p+ε) x := by
        convert! ((((hasDerivAt_id x).pow (p+1)).const_mul C).div_const (p+1)).add ((hasDerivAt_id x).const_mul ε) using 1
        try simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,id_eq]
        (try field_simp)
      convert! hi.exp.const_mul (δ+ε) using 1
      try dsimp only [B]
      ring
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary hf hf' (B:=B)
        (B':=fun x=>B x*(C*x^p+ε)) ?_ hB ?_ ht
    · dsimp only [B]
      simpa using h0.trans (le_add_of_nonneg_right hε.le)
    · intro x hx hboundary
      have hpos : 0 < B x := mul_pos (by linarith) (Real.exp_pos _)
      have hb:=hbound x hx
      rw [hboundary] at hb
      have he : 0 < ε*B x := mul_pos hε hpos
      try dsimp only at *
      nlinarith [he]
  have hc : Continuous (fun ε:ℝ=>(δ+ε)*Real.exp (C*t^(p+1)/(p+1)+ε*t)) := by fun_prop
  have hlim := hc.continuousAt.tendsto.mono_left (show (𝓝[>] (0:ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hb : ∀ᶠε:ℝ in 𝓝[>] 0,‖f t‖ ≤ (δ+ε)*Real.exp (C*t^(p+1)/(p+1)+ε*t) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact heps ε hε
  simpa only [add_zero,zero_mul] using le_of_tendsto_of_tendsto tendsto_const_nhds hlim hb

end Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
