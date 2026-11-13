/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.BranchProofs.SdpLargerBranchPrimalWitnessStat

/-!
# Primal witness for the larger branch

`sdpLargerBranchPrimalWitness` constructs a positive semidefinite primal witness by rescaling a
density operator satisfying the larger-branch separation condition. The witness satisfies all
constraints, has trace at most R, and attains objective at least (1 − δ)α.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpLargerBranchPrimalWitness`: Under the larger-branch separation and parameter hypotheses,
  there exists a positive semidefinite primal feasible operator of trace at most R and objective
  at least (1 − δ)α. See [BrandaoSvore2017].

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SdpMmwSolver.BranchProofs

open Matrix
open scoped BigOperators ComplexOrder

/-- Under the larger-branch separation and parameter hypotheses, there exists a positive
semidefinite primal feasible operator of trace at most R and objective at least (1 − δ)α.
See [BrandaoSvore2017]. -/
theorem sdpLargerBranchPrimalWitness : SdpLargerBranchPrimalWitness := by
  intro D m A Cv b sigma j0 alpha R delta eps ha hR hd hd1 he heb hb hA0 hb0 hs hsep
  let a : Fin m → ℝ := fun i => (Matrix.trace (A i * sigma)).re
  let c : ℝ := (Matrix.trace (Cv * sigma)).re
  let v := c - 3 * alpha * eps
  let w := alpha * (1 - 3 * R * eps)
  have hsmall : eps * (16 * R) ≤ delta := (le_div_iff₀ (by positivity)).mp heb
  have hw : 0 < w := by dsimp [w]; nlinarith
  have hv : 0 < v := by
    by_contra hv
    have hzero := hsep (fun _ => 0) (by simp) (by simpa [v, c] using! (le_of_not_gt hv))
    simp only [zero_mul, Finset.sum_const_zero] at hzero
    exact (not_le_of_gt hw) hzero
  let lam := w / v
  have hlam : 0 < lam := div_pos hw hv
  have hlamv : lam * v = w := div_mul_cancel₀ w hv.ne'
  have hfeas : ∀ i, lam * a i ≤ b i := by
    intro i
    by_contra hbad
    have hbad' : b i < lam * a i := lt_of_not_ge hbad
    have hai : 0 < a i := by nlinarith [hb i]
    let y : Fin m → ℝ := fun j => if j = i then v / a i else 0
    have hyn : ∀ j, 0 ≤ y j := by intro j; dsimp [y]; split_ifs <;> positivity
    have hytrace : (∑ j, y j * (Matrix.trace (A j * sigma)).re) = v := by
      change (∑ j, (if j = i then v / a i else 0) * a j) = v
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact div_mul_cancel₀ v hai.ne'
    have hycost := hsep y hyn (by rw [hytrace])
    change w ≤ ∑ j, (if j = i then v / a i else 0) * b j at hycost
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hycost
    have hlow := mul_le_mul_of_nonneg_right hycost hai.le
    have hidentity : (v / a i * b i) * a i = v * b i := by field_simp
    rw [hidentity] at hlow
    have hstrict := mul_lt_mul_of_pos_right hbad' hv
    have hidentity' : (lam * a i) * v = w * a i := by rw [mul_right_comm, hlamv]
    rw [hidentity'] at hstrict
    linarith
  have haj0 : a j0 = 1 := by simp [a, hA0, hs.2]
  have hlamR : lam ≤ R := by
    have h := hfeas j0
    rwa [haj0, mul_one, hb0] at h
  refine ⟨lam • sigma, ?_, ?_, ?_, ?_⟩
  · exact hs.1.smul (by exact_mod_cast hlam.le)
  · intro i
    simpa only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] using! hfeas i
  · simpa only [Matrix.trace_smul, Complex.smul_re, hs.2, Complex.one_re,
      smul_eq_mul, mul_one] using! hlamR
  · have htarget : (1 - delta) * alpha ≤ w := by dsimp [w]; nlinarith
    have hcv : v ≤ c := by dsimp [v]; nlinarith
    have h := mul_le_mul_of_nonneg_left hcv hlam.le
    rw [hlamv] at h
    simpa only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] using!
        htarget.trans h

end Qatlib.Concepts.SdpMmwSolver.BranchProofs
