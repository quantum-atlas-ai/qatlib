/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformDefs
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.SecularAlgebra
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.UniformCurve
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.LowestPair
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator
open Qatlib.Papers.ProjectorQAOA26.StageStability
open Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

omit [DecidableEq I] [Nonempty I] in

theorem uniformReference_weight (i : I) : Complex.normSq (uniformReference i)=1/(Fintype.card I:ℝ) := by
  simp only [uniformReference,Complex.normSq_ofReal]
  rw [← pow_two,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

omit [DecidableEq I] in

theorem uniformReference_ne_zero : (uniformReference (I:=I))≠0 := by
  intro h
  have hn:=uniformReference_normalized (I:=I)
  rw [h] at hn
  simp [l2norm] at hn

def rankOneOperator (E : I → ℝ) (a : ℝ) : Matrix I I ℂ :=
  diagonalMinusRankOne E uniformReference a

omit [Nonempty I] in

theorem rankOneOperator_hermitian (E : I → ℝ) (a : ℝ) : (rankOneOperator E a).IsHermitian :=
  hermitian E uniformReference a

omit [DecidableEq I] [Nonempty I] in

theorem actual_secular_curve (E : I → ℝ) (z : ℝ) :
    secularSum E (uniformReference (I:=I)) z=uniformCurve E z := by
  simp only [secularSum,uniformReference_weight,uniformCurve,div_eq_mul_inv,Finset.mul_sum]

theorem actual_secular_iff_eigenvalue (E : I → ℝ) (a z : ℝ) (hpole : ∀ i,E i≠z) :
    a*uniformCurve E z=1 ↔ hasRealEigenvalue (rankOneOperator E a) z := by
  rw [← actual_secular_curve E z]
  exact secular_iff_eigenvalue E uniformReference a z hpole uniformReference_ne_zero

omit [Nonempty I] in

theorem actual_nonpole_line (E : I → ℝ) (a z : ℝ) (hpole : ∀ i,E i≠z) (x : I → ℂ)
    (hx : rankOneOperator E a*ᵥx=(z:ℂ)•x) : ∃ c : ℂ,x=c•resolventVector E uniformReference z :=
  ⟨_,eigenvector_scalar E uniformReference x a z hpole hx⟩

omit [Nonempty I] in

theorem hamiltonian_rankOne (E : I → ℝ) (s : ℝ) (hs : s≠0) :
    hamiltonian E s=(1-s)•(1 : Matrix I I ℂ)+s•rankOneOperator E ((1-s)/s) := by
  have hsc : (s:ℂ)≠0 := by exact_mod_cast hs
  ext i j
  simp only [hamiltonian,uniformMixer,learnedGenerator,rankOneOperator,diagonalMinusRankOne,
    costOperator,rankOne,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    Complex.real_smul,smul_eq_mul]
  push_cast
  field_simp [hsc]
  ring

omit [Fintype I] [DecidableEq I] [Nonempty I] in

theorem negative_nonpole (E : I → ℝ) (hE : ∀ i,0≤E i) (z : ℝ) (hz : z<0) : ∀ i,E i≠z := by
  intro i
  linarith [hE i]

omit [Fintype I] [Nonempty I] in

theorem small_positive_nonpole (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (z : ℝ) (hz : z∈Set.Ioo (0:ℝ) 1) : ∀ i,E i≠z := by
  intro i
  by_cases hi : i=zero
  · subst i
    rw [hzero]
    linarith [hz.1]
  · linarith [hE i hi,hz.2]
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
