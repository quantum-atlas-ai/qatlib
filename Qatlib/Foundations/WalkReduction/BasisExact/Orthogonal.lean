/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.FourDefs

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.WalkReduction.BasisExact

def basisMatrix (u a b v w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0;
     0,3*u/w,0,a*v/w;
     0,3*a/w,-b/v,-9*u/(w*v);
     0,a*b/w,3/v,-3*u*b/(w*v)]

theorem basisMatrix_orthogonal (n u a b v w : ℝ)
    (hu : u^2=2) (ha : a^2=n-4) (hb : b^2=n-5)
    (hv : v^2=n+4) (hw : w^2=n^2+2) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    (basisMatrix u a b v w).transpose * basisMatrix u a b v w = 1 := by
  have hv4 : v^4=(n+4)^2 := by rw [show v^4=(v^2)^2 by ring,hv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisMatrix,Matrix.mul_apply,Fin.sum_univ_four]
  all_goals field_simp [hv0,hw0]
  all_goals ring_nf
  all_goals simp only [hu,ha,hb,hv,hw,hv4]
  all_goals ring

def sourceBasis (n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  basisMatrix (Real.sqrt 2) (Real.sqrt (n-4)) (Real.sqrt (n-5))
    (Real.sqrt (n+4)) (Real.sqrt (n^2+2))

theorem sourceBasis_orthogonal {n : ℝ} (hn : 6 ≤ n) :
    (sourceBasis n).transpose * sourceBasis n = 1 := by
  apply basisMatrix_orthogonal n
  · exact Real.sq_sqrt (by norm_num)
  · exact Real.sq_sqrt (by linarith)
  · exact Real.sq_sqrt (by linarith)
  · exact Real.sq_sqrt (by linarith)
  · exact Real.sq_sqrt (by positivity)
  · exact (Real.sqrt_pos.mpr (by linarith)).ne'
  · exact (Real.sqrt_pos.mpr (by positivity)).ne'

end Qatlib.Foundations.WalkReduction.BasisExact
