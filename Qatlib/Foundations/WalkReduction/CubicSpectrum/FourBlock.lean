/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.CubicSpectrum.Native
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.WalkReduction.CubicSpectrum

def leadingFour (γ n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1,0,0,-γ*Real.sqrt (3*n);
     0,-γ*(3*n-9),0,0;
     0,0,-γ*(2*n-17),-γ*(-2*Real.sqrt (2*n));
     -γ*Real.sqrt (3*n),0,-γ*(-2*Real.sqrt (2*n)),-γ*(n-2)]

def liftThree (v : Fin 3 → ℝ) : Fin 4 → ℝ := ![v 0,0,v 1,v 2]

theorem leadingFour_lift (γ n : ℝ) (v : Fin 3 → ℝ) :
    (leadingFour γ n).mulVec (liftThree v) = liftThree ((Hred0 γ n).mulVec v) := by
  ext i
  fin_cases i <;> simp [leadingFour,liftThree,Hred0,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,Fin.sum_univ_four]

theorem liftThree_injective : Function.Injective liftThree := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 2
  · exact congrFun h 3

theorem native_eigenvector_lift {γ n lam : ℝ} (v : Fin 3 → ℝ)
    (hv : Module.End.HasEigenvector (Hred0 γ n).toLin' lam v) :
    Module.End.HasEigenvector (leadingFour γ n).toLin' lam (liftThree v) := by
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff] at hv ⊢
  refine ⟨?_,?_⟩
  · change (leadingFour γ n).mulVec (liftThree v) = _
    rw [leadingFour_lift,show (Hred0 γ n).mulVec v = lam • v from hv.1]
    ext i
    fin_cases i <;> simp [liftThree]
  · intro h
    apply hv.2
    apply liftThree_injective
    have hz : liftThree (0 : Fin 3 → ℝ) = 0 := by
      ext i
      fin_cases i <;> rfl
    exact h.trans hz.symm

theorem leadingFour_nearby {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, |lam-(-1-1/(2*n))| ≤ 54/n^2 ∧
      ∃ v : Fin 4 → ℝ, Module.End.HasEigenvector (leadingFour (gammaC n) n).toLin' lam v := by
  obtain ⟨lam,hb,v,hv⟩ := nearby_native_eigenvalue hn
  exact ⟨lam,hb,liftThree v,native_eigenvector_lift v hv⟩

end Qatlib.Foundations.WalkReduction.CubicSpectrum
