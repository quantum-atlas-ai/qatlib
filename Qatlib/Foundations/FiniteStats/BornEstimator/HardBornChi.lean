/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.InvolutionProj
import Qatlib.Foundations.FiniteStats.BornEstimator.MeasurementScore

/-!
# Perturbed Born laws and chi-square identities

This module constructs the maximally mixed `referenceDensity` and its perturbation `hardDensity`
in a traceless Hermitian involution direction. For `0 ≤ ε ≤ 1/3`, the perturbed matrix is
positive semidefinite and has trace one.

Explicit Born probabilities show support containment and give an exact `finiteChiSquare` formula
for any finite POVM. These perturbations provide finite measurement comparisons of the kind used
in [XuEtAl2026].

## Main statements

* `hardDensity`: The density operator `(1 + 3ε A) / card(d)` for a traceless Hermitian
  involution and `0 ≤ ε ≤ 1/3`.
* `hardBorn_support`: An outcome with zero Born probability in the reference state also has zero
  probability in the perturbed state.
* `hardBorn_chiSquare`: The chi-square expression between the perturbed and reference Born laws
  equals `9ε²` times the sum of squared effect inner products with `A` divided by dimension
  times effect trace.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype Ω]

omit [DecidableEq d] in

/-- The cardinality of the nonempty finite Hilbert-space index type is strictly positive as a
real number. -/
theorem hilbertCard_pos : (0:ℝ)<Fintype.card d := by exact_mod_cast Fintype.card_pos

/-- The maximally mixed density operator, equal to the identity divided by the dimension. -/
def referenceDensity : MState d where
  M := (Fintype.card d:ℝ)⁻¹ • 1
  nonneg := smul_nonneg (inv_nonneg.mpr hilbertCard_pos.le) (by positivity)
  tr := by rw [HermitianMat.trace_smul,HermitianMat.trace_one,inv_mul_cancel₀ hilbertCard_pos.ne']

/-- For a Hermitian involution `A` and `0 ≤ ε ≤ 1/3`, the matrix `1 + 3ε A` is positive
semidefinite. -/
theorem hard_numerator_nonneg (A : HermitianMat d ℂ) (hA : A.mat*A.mat=1) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) : 0 ≤ (1 : HermitianMat d ℂ)+(3*ε) • A := by
  have hfirst : 0 ≤ (1-3*ε) • (1 : HermitianMat d ℂ) := smul_nonneg (by linarith) (by positivity)
  have hsecond : 0 ≤ (6*ε) • involutionProjector A false :=
    smul_nonneg (by positivity) (involutionProjector_nonneg A hA false)
  have he : (1 : HermitianMat d ℂ)+(3*ε) • A=
      (1-3*ε) • (1 : HermitianMat d ℂ)+(6*ε) • involutionProjector A false := by
    unfold involutionProjector binarySign
    norm_num
    module
  rw [he]
  exact add_nonneg hfirst hsecond

/-- The density operator `(1 + 3ε A) / card(d)` for a traceless Hermitian involution and `0 ≤ ε
≤ 1/3`. -/
def hardDensity (A : HermitianMat d ℂ) (hA : A.mat*A.mat=1) (htr : A.trace=0)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) : MState d where
  M := (Fintype.card d:ℝ)⁻¹ • (1+(3*ε) • A)
  nonneg := smul_nonneg (inv_nonneg.mpr hilbertCard_pos.le) (hard_numerator_nonneg A hA ε hε0 hε3)
  tr := by rw [HermitianMat.trace_smul,HermitianMat.trace_add,HermitianMat.trace_one,
    HermitianMat.trace_smul,htr,mul_zero,add_zero,inv_mul_cancel₀ hilbertCard_pos.ne']

/-- The Born probability of a POVM outcome in the maximally mixed state is its effect trace
divided by the dimension. -/
theorem referenceBorn_probability (P : POVM Ω d) (s : Ω) :
    ((P.measure (referenceDensity : MState d)) s:ℝ)=(P.mats s).trace/(Fintype.card d:ℝ) := by
  change ⟪P.mats s,(Fintype.card d:ℝ)⁻¹ • (1 : HermitianMat d ℂ)⟫=_
  rw [real_inner_smul_right,HermitianMat.inner_one]
  ring

/-- For the perturbed density operator, the Born probability is the reference probability plus
`3ε` times the effect's inner product with `A`, divided by the dimension. -/
theorem hardBorn_probability (P : POVM Ω d) (A : HermitianMat d ℂ) (hA : A.mat*A.mat=1) (htr : A.trace=0)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) (s : Ω) :
    ((P.measure (hardDensity A hA htr ε hε0 hε3)) s:ℝ)=
      (P.mats s).trace/(Fintype.card d:ℝ)+3*ε*⟪P.mats s,A⟫/(Fintype.card d:ℝ) := by
  change ⟪P.mats s,(Fintype.card d:ℝ)⁻¹ • (1+(3*ε) • A)⟫=_
  rw [real_inner_smul_right,inner_add_right,HermitianMat.inner_one,real_inner_smul_right]
  ring

/-- The finite sum of `(p s - q s)² / q s`, using real division at every outcome. -/
def finiteChiSquare (p q : Ω → ℝ) : ℝ := ∑ s,(p s-q s)^2/q s

/-- An outcome with zero Born probability in the reference state also has zero probability in
the perturbed state. -/
theorem hardBorn_support (P : POVM Ω d) (A : HermitianMat d ℂ) (hA : A.mat*A.mat=1) (htr : A.trace=0)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) (s : Ω)
    (hz : ((P.measure (referenceDensity : MState d)) s:ℝ)=0) :
    ((P.measure (hardDensity A hA htr ε hε0 hε3)) s:ℝ)=0 := by
  rw [referenceBorn_probability] at hz
  have ht : (P.mats s).trace=0 := (div_eq_zero_iff.mp hz).resolve_right hilbertCard_pos.ne'
  have he : P.mats s=0 := by
    by_contra h
    exact (effect_trace_pos _ (P.nonneg s) h).ne' ht
  rw [hardBorn_probability,he]
  simp

/-- The chi-square expression between the perturbed and reference Born laws equals `9ε²` times
the sum of squared effect inner products with `A` divided by dimension times effect trace. -/
theorem hardBorn_chiSquare (P : POVM Ω d) (A : HermitianMat d ℂ) (hA : A.mat*A.mat=1) (htr : A.trace=0)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε3 : ε ≤ 1/3) :
    finiteChiSquare (fun s => ((P.measure (hardDensity A hA htr ε hε0 hε3)) s:ℝ))
      (fun s => ((P.measure (referenceDensity : MState d)) s:ℝ))=
      9*ε^2*(∑ s,⟪P.mats s,A⟫^2/((Fintype.card d:ℝ)*(P.mats s).trace)) := by
  unfold finiteChiSquare
  simp_rw [hardBorn_probability,referenceBorn_probability]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases ht : (P.mats s).trace=0
  · simp [ht]
  · have hd := (hilbertCard_pos (d:=d)).ne'
    field_simp
    ring

end Qatlib.Foundations.FiniteStats.BornEstimator
