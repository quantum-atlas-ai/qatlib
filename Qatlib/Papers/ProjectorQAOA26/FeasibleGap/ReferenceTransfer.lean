/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Matrix Matrix.Norms.L2Operator
open Qatlib.Papers.ProjectorQAOA26.StageStability
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
variable {I : Type} [Fintype I] [DecidableEq I]

def referenceHamiltonian (E : I → ℝ) (reference : I → ℂ) (s : ℝ) : Matrix I I ℂ :=
  (1-s)•learnedGenerator reference+s•costOperator E

omit [Fintype I] in

theorem referenceHamiltonian_hermitian (E : I → ℝ) (reference : I → ℂ) (s : ℝ) :
    (referenceHamiltonian E reference s).IsHermitian := by
  have hr : (learnedGenerator reference).IsHermitian := learnedGenerator_hermitian reference
  exact (hr.smul (k:=1-s) (by rfl)).add ((costOperator_hermitian E).smul (k:=s) (by rfl))

def referenceGap (E : I → ℝ) (reference : I → ℂ) (hL : 2≤Fintype.card I) (s : ℝ) : ℝ :=
  (referenceHamiltonian_hermitian E reference s).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩-
    (referenceHamiltonian_hermitian E reference s).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩

omit [Fintype I] in

theorem referenceHamiltonian_sub (E : I → ℝ) (u v : I → ℂ) (s : ℝ) :
    referenceHamiltonian E u s-referenceHamiltonian E v s=(1-s)•(learnedGenerator u-learnedGenerator v) := by
  unfold referenceHamiltonian
  module

theorem referenceHamiltonian_distance (E : I → ℝ) (u v : I → ℂ) (hu : l2norm u=1) (hv : l2norm v=1) (s : ℝ) :
    ‖referenceHamiltonian E u s-referenceHamiltonian E v s‖=
      |1-s| *Real.sqrt (1-l2abs u v^2) := by
  rw [referenceHamiltonian_sub,norm_smul,Real.norm_eq_abs]
  have he : learnedGenerator u-learnedGenerator v=-(rankOne u-rankOne v) := by
    unfold learnedGenerator;abel
  rw [he,norm_neg,opNorm_rankOne_sub hu hv]

theorem referenceGap_transport (E : I → ℝ) (u v : I → ℂ) (hu : l2norm u=1) (hv : l2norm v=1)
    (hL : 2≤Fintype.card I) (s : ℝ) :
    |referenceGap E u hL s-referenceGap E v hL s|≤2*|1-s| *phaseDist u v := by
  have hw:=(ordered_hermitian_weyl_and_hoffman_wielandt I (referenceHamiltonian E u s) (referenceHamiltonian E v s)
    (referenceHamiltonian_hermitian E u s) (referenceHamiltonian_hermitian E v s)).1
  have h0:=hw ⟨Fintype.card I-2,by omega⟩
  have h1:=hw ⟨Fintype.card I-1,by omega⟩
  dsimp only [orderedHermitianValues] at h0 h1
  have hnorm : ‖referenceHamiltonian E u s-referenceHamiltonian E v s‖≤|1-s| *phaseDist u v := by
    rw [referenceHamiltonian_sub,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (mixerGen_diff_le hu hv) (abs_nonneg _)
  have ht:=abs_sub ((referenceHamiltonian_hermitian E u s).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩-
    (referenceHamiltonian_hermitian E v s).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩)
    ((referenceHamiltonian_hermitian E u s).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩-
    (referenceHamiltonian_hermitian E v s).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩)
  unfold referenceGap
  have he (a b c d : ℝ) : (a-b)-(c-d)=(a-c)-(b-d) := by ring
  rw [he]
  linarith

theorem learned_reference_gap (E : I → ℝ) (u : I → ℂ) (hu : l2norm u=1)
    (hL : 2≤Fintype.card I) (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) :
    |referenceGap E u hL s-spectralGap E hL s|≤2*phaseDist u (uniformReference (I:=I)) := by
  have hcard : 0<Fintype.card I := by omega
  letI : Nonempty I:=Fintype.card_pos_iff.mp hcard
  have h:=referenceGap_transport E u uniformReference hu uniformReference_normalized hL s
  have he : referenceGap E uniformReference hL s=spectralGap E hL s := rfl
  rw [he] at h
  have habs : |1-s|≤1 := abs_le.mpr ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hm:=mul_le_mul_of_nonneg_right habs (phaseDist_nonneg u (uniformReference (I:=I)))
  nlinarith
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
