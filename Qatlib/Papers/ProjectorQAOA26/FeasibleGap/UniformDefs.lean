/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.CoherentReplay
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation

/-!
# Uniform-reference Hamiltonians and minimum spectral gaps

This module defines the normalized uniform reference, its complementary-projector mixer, and the
interpolation `hamiltonian` with a diagonal cost operator. It defines the lowest-two-eigenvalue
gap and its minimum on the unit interval for the feasible-space analysis of [ZhouAnLiu2026].

## Main statements

* `spectralGap_lipschitz`: The spectral gap changes by at most `2 * ‖costOperator E -
  uniformMixer‖ * |s - t|` between two interpolation parameters.
* `exists_gap_minimizer`: The spectral gap attains a minimum on the closed unit interval.
* `minimumGap_le`: The minimum gap is no greater than the gap at any parameter in the closed
  unit interval.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.FeasibleGap
open scoped Classical Matrix Matrix.Norms.L2Operator
open Qatlib.Papers.ProjectorQAOA26.StageStability
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The constant complex reference vector with amplitude `1 / sqrt L`, where `L` is the index
cardinality. -/
def uniformReference : I → ℂ := fun _ => ((1/Real.sqrt (Fintype.card I:ℝ):ℝ):ℂ)

omit [DecidableEq I] in

/-- The uniform reference vector has Euclidean norm one. -/
theorem uniformReference_normalized : l2norm (uniformReference (I:=I))=1 := by
  have hL : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hs : Real.sqrt (Fintype.card I:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  have hh : (Real.sqrt (Fintype.card I:ℝ))^2=(Fintype.card I:ℝ) := Real.sq_sqrt hL.le
  unfold l2norm uniformReference
  simp only [Complex.normSq_ofReal,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have he : (Fintype.card I:ℝ)*(1/Real.sqrt (Fintype.card I:ℝ))^2=1 := by
    field_simp
    exact hh.symm
  rw [← pow_two,he,Real.sqrt_one]

/-- The diagonal complex matrix whose diagonal entries are the real costs `E`. -/
def costOperator (E : I → ℝ) : Matrix I I ℂ := Matrix.diagonal (fun i => (E i:ℂ))

omit [Fintype I] [Nonempty I] in

/-- A diagonal operator with real costs is Hermitian. -/
theorem costOperator_hermitian (E : I → ℝ) : (costOperator E).IsHermitian := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [costOperator,Matrix.conjTranspose_apply]
  · simp [costOperator,Matrix.conjTranspose_apply,h,Ne.symm h]

/-- The complementary-projector generator associated with the uniform reference vector. -/
def uniformMixer : Matrix I I ℂ := learnedGenerator (uniformReference (I:=I))

omit [Nonempty I] in

/-- The uniform-reference mixer is Hermitian. -/
theorem uniformMixer_hermitian : (uniformMixer (I:=I)).IsHermitian :=
  learnedGenerator_hermitian _

/-- The linear interpolation between `uniformMixer` and the diagonal cost operator, with weights
`1 - s` and `s`. -/
def hamiltonian (E : I → ℝ) (s : ℝ) : Matrix I I ℂ :=
  (1-s)•uniformMixer+s•costOperator E

omit [Nonempty I] in

/-- The uniform-reference interpolation Hamiltonian is Hermitian for every real parameter. -/
theorem hamiltonian_hermitian (E : I → ℝ) (s : ℝ) : (hamiltonian E s).IsHermitian := by
  exact ((uniformMixer_hermitian (I:=I)).smul (k:=1-s) (by rfl)).add
    ((costOperator_hermitian E).smul (k:=s) (by rfl))

/-- The difference between the second-lowest and lowest eigenvalues of `hamiltonian`. -/
def spectralGap (E : I → ℝ) (hL : 2≤Fintype.card I) (s : ℝ) : ℝ :=
  (hamiltonian_hermitian E s).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩-
    (hamiltonian_hermitian E s).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩

omit [Nonempty I] in

/-- The lowest-two-eigenvalue spectral gap is nonnegative. -/
theorem spectralGap_nonneg (E : I → ℝ) (hL : 2≤Fintype.card I) (s : ℝ) :
    0 ≤ spectralGap E hL s := by
  unfold spectralGap
  apply sub_nonneg.mpr
  apply (hamiltonian_hermitian E s).eigenvalues₀_antitone
  change Fintype.card I-2≤Fintype.card I-1
  omega

omit [Nonempty I] in

/-- The difference of Hamiltonians at `s` and `t` is `(s - t)` times the difference between the
cost operator and the uniform mixer. -/
theorem hamiltonian_sub (E : I → ℝ) (s t : ℝ) :
    hamiltonian E s-hamiltonian E t=(s-t)•(costOperator E-uniformMixer) := by
  unfold hamiltonian
  module

omit [Nonempty I] in

/-- The spectral gap changes by at most `2 * ‖costOperator E - uniformMixer‖ * |s - t|` between
two interpolation parameters. -/
theorem spectralGap_lipschitz (E : I → ℝ) (hL : 2≤Fintype.card I) (s t : ℝ) :
    |spectralGap E hL s-spectralGap E hL t|≤2*‖costOperator E-uniformMixer‖*|s-t| := by
  have hw:=(ordered_hermitian_weyl_and_hoffman_wielandt I (hamiltonian E s) (hamiltonian E t)
    (hamiltonian_hermitian E s) (hamiltonian_hermitian E t)).1
  have h0:=hw ⟨Fintype.card I-2,by omega⟩
  have h1:=hw ⟨Fintype.card I-1,by omega⟩
  rw [hamiltonian_sub,norm_smul,Real.norm_eq_abs] at h0 h1
  dsimp only [orderedHermitianValues] at h0 h1
  have ht:=abs_sub ((hamiltonian_hermitian E s).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩-
    (hamiltonian_hermitian E t).eigenvalues₀ ⟨Fintype.card I-2,by omega⟩)
    ((hamiltonian_hermitian E s).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩-
    (hamiltonian_hermitian E t).eigenvalues₀ ⟨Fintype.card I-1,by omega⟩)
  unfold spectralGap
  have he (a b c d : ℝ) : (a-b)-(c-d)=(a-c)-(b-d) := by ring
  rw [he]
  nlinarith

omit [Nonempty I] in

/-- The spectral gap is a continuous function of the interpolation parameter. -/
theorem spectralGap_continuous (E : I → ℝ) (hL : 2≤Fintype.card I) : Continuous (spectralGap E hL) := by
  have hlip : LipschitzWith ⟨2*‖costOperator E-uniformMixer‖,by positivity⟩ (spectralGap E hL) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [Real.dist_eq,NNReal.coe_mk] using! spectralGap_lipschitz E hL s t
  exact hlip.continuous

omit [Nonempty I] in

/-- The spectral gap attains a minimum on the closed unit interval. -/
theorem exists_gap_minimizer (E : I → ℝ) (hL : 2≤Fintype.card I) :
    ∃ s∈Set.Icc (0:ℝ) 1,∀ t∈Set.Icc (0:ℝ) 1,spectralGap E hL s≤ spectralGap E hL t := by
  exact isCompact_Icc.exists_isMinOn (by exact ⟨0,by constructor <;> norm_num⟩)
    (spectralGap_continuous E hL).continuousOn

/-- A chosen interpolation parameter minimizing the spectral gap on the closed unit interval. -/
def gapMinimizer (E : I → ℝ) (hL : 2≤Fintype.card I) : ℝ :=
    Classical.choose (exists_gap_minimizer E hL)

omit [Nonempty I] in

/-- The chosen gap minimizer belongs to the closed unit interval. -/
theorem gapMinimizer_mem (E : I → ℝ) (hL : 2≤Fintype.card I) : gapMinimizer E hL∈Set.Icc (0:ℝ) 1 :=
  (Classical.choose_spec (exists_gap_minimizer E hL)).1

/-- The spectral gap evaluated at the chosen minimizer on the closed unit interval. -/
def minimumGap (E : I → ℝ) (hL : 2≤Fintype.card I) : ℝ := spectralGap E hL (gapMinimizer E hL)

omit [Nonempty I] in

/-- The minimum gap is no greater than the gap at any parameter in the closed unit interval. -/
theorem minimumGap_le (E : I → ℝ) (hL : 2≤Fintype.card I) (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) :
    minimumGap E hL≤ spectralGap E hL s := (Classical.choose_spec (exists_gap_minimizer E hL)).2 s hs
end Qatlib.Papers.ProjectorQAOA26.FeasibleGap
