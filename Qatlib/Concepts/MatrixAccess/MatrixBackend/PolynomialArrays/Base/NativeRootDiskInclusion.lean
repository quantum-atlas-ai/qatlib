/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

set_option backward.isDefEq.respectTransparency false

/-! Principal mathematical acceptance bridge of the exact rational root checker.
This does not yet implement integer Horner, disk completeness or source replay. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial

/-- The finite construction in `NativeRootDiskInclusion` satisfies `polynomial_root_disk_of_norm_ratio` under the displayed hypotheses. -/
theorem polynomial_root_disk_of_norm_ratio (f : ℂ[X]) (hf : 0<f.natDegree)
    (c : ℂ) (r : ℝ) (hr : 0<r)
    (hbound : (f.natDegree : ℝ)*‖f.eval c‖≤r*‖f.derivative.eval c‖) :
    ∃ z : ℂ, f.eval z=0 ∧ ‖z-c‖≤r := by
  classical
  by_cases hc : f.eval c=0
  · exact ⟨c,hc,by simpa using hr.le⟩
  have hf0 : f≠0 := by
    intro h
    simp [h] at hc
  have hsplit : f.Splits := IsAlgClosed.splits f
  have hcard : f.roots.card=f.natDegree := hsplit.natDegree_eq_card_roots.symm
  have hnonempty : f.roots≠0 := by
    intro hz
    simp [hz] at hcard
    omega
  by_contra! hnone
  have hfar : ∀ z∈f.roots,r<‖c-z‖ := by
    intro z hz
    have he : f.eval z=0 := (Polynomial.mem_roots hf0).mp hz
    simpa only [norm_sub_rev] using hnone z he
  have hterms : ∀ z∈f.roots,‖(1 : ℂ)/(c-z)‖<(1 : ℝ)/r := by
    intro z hz
    simpa only [norm_div,norm_one] using one_div_lt_one_div_of_lt hr (hfar z hz)
  have hstrict := Multiset.sum_lt_sum_of_nonempty
    (s := f.roots) (f := fun z : ℂ => ‖(1 : ℂ)/(c-z)‖)
    (g := fun _ : ℂ => (1 : ℝ)/r) hnonempty hterms
  have hsum : (f.roots.map (fun z : ℂ => ‖(1 : ℂ)/(c-z)‖)).sum<
      (f.natDegree : ℝ)/r := by
    simpa [hcard,div_eq_mul_inv] using hstrict
  have hnorm : ‖f.derivative.eval c/f.eval c‖<(f.natDegree : ℝ)/r := by
    rw [hsplit.eval_derivative_div_eval_of_ne_zero hc]
    have hsumNorm : ‖(f.roots.map (fun z : ℂ => (1 : ℂ)/(c-z))).sum‖≤
        (f.roots.map (fun z : ℂ => ‖(1 : ℂ)/(c-z)‖)).sum := by
      simpa only [Multiset.map_map,Function.comp_def] using
        norm_multiset_sum_le (f.roots.map (fun z : ℂ => (1 : ℂ)/(c-z)))
    exact hsumNorm.trans_lt hsum
  have hlower : (f.natDegree : ℝ)/r≤‖f.derivative.eval c‖/‖f.eval c‖ := by
    apply (div_le_div_iff₀ hr (norm_pos_iff.mpr hc)).mpr
    simpa only [mul_comm] using hbound
  rw [norm_div] at hnorm
  exact (not_lt_of_ge hlower) hnorm

/-- Exactly the conservative L1/L-infinity acceptance inequality used by the
rational verifier. No floating residual threshold or simple-root premise. -/
theorem polynomial_root_disk_of_coordinate_test (f : ℂ[X]) (hf : 0<f.natDegree)
    (c : ℂ) (r : ℝ) (hr : 0<r)
    (hbound : (f.natDegree : ℝ)*(|(f.eval c).re|+|(f.eval c).im|)≤
      r*max |(f.derivative.eval c).re| |(f.derivative.eval c).im|) :
    ∃ z : ℂ, f.eval z=0 ∧ ‖z-c‖≤r := by
  apply polynomial_root_disk_of_norm_ratio f hf c r hr
  calc
    _≤(f.natDegree : ℝ)*(|(f.eval c).re|+|(f.eval c).im|) :=
      mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im _) (Nat.cast_nonneg _)
    _≤r*max |(f.derivative.eval c).re| |(f.derivative.eval c).im| := hbound
    _≤r*‖f.derivative.eval c‖ := mul_le_mul_of_nonneg_left
      (max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)) hr.le

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
