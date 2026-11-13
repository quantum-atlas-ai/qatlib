/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.FeasibleGap.UniformDefs
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.SecularAlgebra
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.UniformCurve
import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.LowestPair

/-!
# Secular equations for the uniform-reference interpolation

This module specializes rank-one secular equations to `uniformReference` and rewrites
`hamiltonian` as a scalar shift of `rankOneOperator`. It characterizes eigenvalues and
eigenspaces away from cost poles, as used in the uniform feasible-gap analysis of
[ZhouAnLiu2026].

## Main statements

* `actual_secular_iff_eigenvalue`: Away from all cost poles, `z` is a real eigenvalue of
  `rankOneOperator E a` exactly when `a * uniformCurve E z = 1`, as in [ZhouAnLiu2026].
* `actual_nonpole_line`: Away from the cost poles, every eigenvector at `z` of the uniform
  rank-one perturbation is a scalar multiple of the corresponding resolvent vector.
* `hamiltonian_rankOne`: For nonzero `s`, the interpolation Hamiltonian is `(1 - s)` times the
  identity plus `s` times `rankOneOperator E ((1 - s) / s)`.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator
open Qatlib.Papers.ProjectorQAOA26.StageStability
open Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

omit [DecidableEq I] [Nonempty I] in

/-- Each coordinate of the uniform reference has squared magnitude `1 / L`, where `L` is the
index cardinality. -/
theorem uniformReference_weight (i : I) : Complex.normSq (uniformReference i)=1/(Fintype.card I:ℝ) := by
  simp only [uniformReference,Complex.normSq_ofReal]
  rw [← pow_two,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

omit [DecidableEq I] in

/-- The uniform reference vector is nonzero. -/
theorem uniformReference_ne_zero : (uniformReference (I:=I))≠0 := by
  intro h
  have hn:=uniformReference_normalized (I:=I)
  rw [h] at hn
  simp [l2norm] at hn

/-- The diagonal cost operator minus `a` times the rank-one operator of the uniform reference. -/
def rankOneOperator (E : I → ℝ) (a : ℝ) : Matrix I I ℂ :=
  diagonalMinusRankOne E uniformReference a

omit [Nonempty I] in

/-- The uniform rank-one perturbation of the real diagonal cost operator is Hermitian. -/
theorem rankOneOperator_hermitian (E : I → ℝ) (a : ℝ) : (rankOneOperator E a).IsHermitian :=
  hermitian E uniformReference a

omit [DecidableEq I] [Nonempty I] in

/-- The secular sum weighted by the uniform reference equals `uniformCurve`. -/
theorem actual_secular_curve (E : I → ℝ) (z : ℝ) :
    secularSum E (uniformReference (I:=I)) z=uniformCurve E z := by
  simp only [secularSum,uniformReference_weight,uniformCurve,div_eq_mul_inv,Finset.mul_sum]

/-- Away from all cost poles, `z` is a real eigenvalue of `rankOneOperator E a` exactly when `a
* uniformCurve E z = 1`, as in [ZhouAnLiu2026]. -/
theorem actual_secular_iff_eigenvalue (E : I → ℝ) (a z : ℝ) (hpole : ∀ i,E i≠z) :
    a*uniformCurve E z=1 ↔ hasRealEigenvalue (rankOneOperator E a) z := by
  rw [← actual_secular_curve E z]
  exact secular_iff_eigenvalue E uniformReference a z hpole uniformReference_ne_zero

omit [Nonempty I] in

/-- Away from the cost poles, every eigenvector at `z` of the uniform rank-one perturbation is a
scalar multiple of the corresponding resolvent vector. -/
theorem actual_nonpole_line (E : I → ℝ) (a z : ℝ) (hpole : ∀ i,E i≠z) (x : I → ℂ)
    (hx : rankOneOperator E a*ᵥx=(z:ℂ)•x) : ∃ c : ℂ,x=c•resolventVector E uniformReference z :=
  ⟨_,eigenvector_scalar E uniformReference x a z hpole hx⟩

omit [Nonempty I] in

/-- For nonzero `s`, the interpolation Hamiltonian is `(1 - s)` times the identity plus `s`
times `rankOneOperator E ((1 - s) / s)`. -/
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

/-- A negative real number is distinct from every nonnegative cost. -/
theorem negative_nonpole (E : I → ℝ) (hE : ∀ i,0≤E i) (z : ℝ) (hz : z<0) : ∀ i,E i≠z := by
  intro i
  linarith [hE i]

omit [Fintype I] [Nonempty I] in

/-- If the distinguished cost is zero and all other costs are at least one, every number
strictly between zero and one lies away from all cost poles. -/
theorem small_positive_nonpole (E : I → ℝ) (zero : I) (hzero : E zero=0)
    (hE : ∀ i,i≠zero → 1≤E i) (z : ℝ) (hz : z∈Set.Ioo (0:ℝ) 1) : ∀ i,E i≠z := by
  intro i
  by_cases hi : i=zero
  · subst i
    rw [hzero]
    linarith [hz.1]
  · linarith [hE i hi,hz.2]
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
