/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelPoleCoefficients

/-!
# Auxiliary regulators and residue coefficients

This module defines the normalized polynomial `auxRegulator` and the associated lattice contour
denominator, kernel, sample weights, and auxiliary residue coefficients. It locates all
denominator zeros and computes their derivatives and normalized residues, supplying the
algebraic data for the auxiliary-pole contour formula of [WangEtAl2026].

## Main statements

* `auxRegulator_eq_zero_iff`: the regulator zeros are exactly the auxiliary pole set when it
  excludes `-I`.
* `auxContourDenominator_deriv_ne_zero_of_eq_zero`: the separated target, auxiliary, and lattice
  zeros are simple.
* `auxContour_coefficient_lattice`: the normalized lattice residue is the negative sample
  weight.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators

/-- The product of the normalized factors `(z - p) / (-I - p)` over the auxiliary pole set. -/
noncomputable def auxRegulator (s : Finset ℂ) (z : ℂ) : ℂ :=
  ∏ p ∈ s, (z - p) / (-Complex.I - p)

/-- The product of `z + I`, the auxiliary regulator, and the integer lattice exponential. -/
noncomputable def auxContourDenominator (s : Finset ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  (z + Complex.I) * auxRegulator s z * integerLatticeExponential a z

/-- The scalar numerator `exp (-2 * π * a) - 1` divided by the auxiliary contour denominator. -/
noncomputable def auxContourKernel (s : Finset ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  ((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) / auxContourDenominator s a z

/-- The auxiliary contour kernel acting by scalar multiplication on the numerator value `U z`. -/
noncomputable def auxContourIntegrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ℂ) (a : ℝ) (U : ℂ → E) (z : ℂ) : E :=
  auxContourKernel s a z • U z

/-- The lattice sample weight at `x = k / a`, given by `(exp (-2 * π * a) - 1) / (2 * π * I * a
* (x + I) * auxRegulator s x)`. -/
noncomputable def auxWeight (s : Finset ℂ) (a : ℝ) (k : ℤ) : ℂ :=
  let x : ℂ := (((k : ℝ) / a : ℝ) : ℂ)
  (Real.exp (-2 * Real.pi * a) - 1 : ℝ) /
    (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * (x + Complex.I) * auxRegulator s x)

/-- The product of normalized factors `(p - q) / (-I - q)` over auxiliary poles other than `p`. -/
noncomputable def auxDeletedPoleProduct (s : Finset ℂ) (p : ℂ) : ℂ := by
  classical
  exact ∏ q ∈ s.erase p, (p - q) / (-Complex.I - q)

/-- The lattice pole factor at an auxiliary pole divided by its deleted-pole product. -/
noncomputable def auxResidueCoefficient (s : Finset ℂ) (a : ℝ) (p : ℂ) : ℂ :=
  latticePoleFactor a p / auxDeletedPoleProduct s p

/-- If `-I` is excluded from the auxiliary set, each normalization denominator `-I - p` for a
member `p` is nonzero. -/
theorem auxNormalization_ne_zero {s : Finset ℂ} (hs : -Complex.I ∉ s)
    {p : ℂ} (hp : p ∈ s) : -Complex.I - p ≠ 0 := by
  intro h
  have he : p = -Complex.I := (sub_eq_zero.mp h).symm
  exact hs (he ▸ hp)

/-- The auxiliary regulator is complex differentiable everywhere. -/
theorem auxRegulator_differentiable (s : Finset ℂ) : Differentiable ℂ (auxRegulator s) := by
  unfold auxRegulator
  apply Differentiable.fun_finsetProd
  intro p _
  fun_prop

/-- If the auxiliary set excludes `-I`, the regulator equals one at `-I`. -/
theorem auxRegulator_at_neg_I (s : Finset ℂ) (hs : -Complex.I ∉ s) :
    auxRegulator s (-Complex.I) = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  exact div_self (auxNormalization_ne_zero hs hp)

/-- For an auxiliary set excluding `-I`, the regulator vanishes exactly at the members of that
set. -/
theorem auxRegulator_eq_zero_iff (s : Finset ℂ) (hs : -Complex.I ∉ s) (z : ℂ) :
    auxRegulator s z = 0 ↔ z ∈ s := by
  rw [auxRegulator, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, hp, hterm⟩
    have he : z = p := sub_eq_zero.mp
      ((div_eq_zero_iff.mp hterm).resolve_right (auxNormalization_ne_zero hs hp))
    exact he ▸ hp
  · intro hz
    exact ⟨z, hz, by simp⟩

/-- For an auxiliary pole in a set excluding `-I`, its deleted-pole product is nonzero. -/
theorem auxDeletedPoleProduct_ne_zero (s : Finset ℂ) (hs : -Complex.I ∉ s)
    (p : ℂ) (_hp : p ∈ s) : auxDeletedPoleProduct s p ≠ 0 := by
  classical
  unfold auxDeletedPoleProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  apply div_ne_zero _ (auxNormalization_ne_zero hs (Finset.mem_erase.mp hq).2)
  exact sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hq).1)

/-- At a member `p` of the auxiliary set, the regulator derivative is `auxDeletedPoleProduct s p
/ (-I - p)`. -/
theorem auxRegulator_hasDerivAt_pole (s : Finset ℂ) (p : ℂ) (hp : p ∈ s) :
    HasDerivAt (auxRegulator s) (auxDeletedPoleProduct s p / (-Complex.I - p)) p := by
  classical
  let G : ℂ → ℂ := fun z => ∏ q ∈ s.erase p, (z - q) / (-Complex.I - q)
  have hG : Differentiable ℂ G := by
    apply Differentiable.fun_finsetProd
    intro q _
    fun_prop
  have heq : auxRegulator s = fun z => ((z - p) / (-Complex.I - p)) * G z := by
    funext z
    exact (Finset.mul_prod_erase s (fun q => (z - q) / (-Complex.I - q)) hp).symm
  rw [heq]
  have h := (((hasDerivAt_id p).sub_const p).div_const (-Complex.I - p)).mul (hG p).hasDerivAt
  convert! h using 1
  simp only [id_eq, sub_self, zero_div, zero_mul, add_zero, G, auxDeletedPoleProduct]
  ring

/-- If the auxiliary set excludes `-I` and all real lattice points, the regulator is nonzero at
every real lattice point. -/
theorem auxRegulator_at_lattice_ne_zero (s : Finset ℂ) (hs : -Complex.I ∉ s) (a : ℝ)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ)) (k : ℤ) :
    auxRegulator s (((k : ℝ) / a : ℝ) : ℂ) ≠ 0 := by
  intro h
  have hmem := (auxRegulator_eq_zero_iff s hs _).mp h
  exact hsLattice _ hmem k rfl

/-- For positive `a`, the integer lattice exponential is nonzero at each auxiliary pole that
avoids the real lattice. -/
theorem auxLatticeExponential_ne_zero (s : Finset ℂ) {a : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ)) (p : ℂ) (hp : p ∈ s) :
    integerLatticeExponential a p ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (integerLatticeExponential_eq_zero_iff ha p).mp h
  exact hsLattice p hp k hk

/-- The auxiliary contour denominator is complex differentiable everywhere. -/
theorem auxContourDenominator_differentiable (s : Finset ℂ) (a : ℝ) :
    Differentiable ℂ (auxContourDenominator s a) := by
  exact ((differentiable_id.add_const Complex.I).mul
    (auxRegulator_differentiable s)).mul (integerLatticeExponential_differentiable a)

/-- For positive `a` and an auxiliary set excluding `-I`, the denominator zeros are precisely
`-I`, the auxiliary poles, and the real lattice points `k / a`. -/
theorem auxContourDenominator_eq_zero_iff (s : Finset ℂ) (hs : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a) (z : ℂ) :
    auxContourDenominator s a z = 0 ↔
      z = -Complex.I ∨ z ∈ s ∨ ∃ k : ℤ, z = (((k : ℝ) / a : ℝ) : ℂ) := by
  simp only [auxContourDenominator, mul_eq_zero, auxRegulator_eq_zero_iff s hs,
    integerLatticeExponential_eq_zero_iff ha, add_eq_zero_iff_eq_neg, or_assoc]

/-- The auxiliary contour denominator has the derivative obtained by the product rule for its
linear, regulator, and exponential factors. -/
theorem auxContourDenominator_hasDerivAt (s : Finset ℂ) (a : ℝ) (z : ℂ) :
    HasDerivAt (auxContourDenominator s a)
      ((auxRegulator s z + (z + Complex.I) * deriv (auxRegulator s) z) *
        integerLatticeExponential a z +
        (z + Complex.I) * auxRegulator s z *
          (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) *
            (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)))) z := by
  simpa only [one_mul] using!
    (((hasDerivAt_id z).add_const Complex.I).mul
      ((auxRegulator_differentiable s) z).hasDerivAt).mul
      (integerLatticeExponential_hasDerivAt a z)

/-- For an auxiliary set excluding `-I`, the denominator derivative at `-I` equals `exp (-2 * π
* a) - 1`. -/
theorem auxContourDenominator_hasDerivAt_neg_I (s : Finset ℂ) (hs : -Complex.I ∉ s) (a : ℝ) :
    HasDerivAt (auxContourDenominator s a)
      (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ)) (-Complex.I) := by
  simpa only [neg_add_cancel, zero_mul, add_zero, zero_add,
    auxRegulator_at_neg_I s hs, one_mul, integerLatticeExponential_at_neg_I] using!
    auxContourDenominator_hasDerivAt s a (-Complex.I)

/-- For positive `a` and `x = k / a`, the denominator derivative at `x` is `(-2 * π * I * a) *
(x + I) * auxRegulator s x`. -/
theorem auxContourDenominator_hasDerivAt_lattice (s : Finset ℂ) {a : ℝ} (ha : 0 < a) (k : ℤ) :
    let x : ℂ := (((k : ℝ) / a : ℝ) : ℂ)
    HasDerivAt (auxContourDenominator s a)
      ((-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) * (x + Complex.I) * auxRegulator s x) x := by
  (try dsimp only)
  have he := integerLatticeExponential_at_lattice ha k
  have hexp := sub_eq_zero.mp he
  have h := auxContourDenominator_hasDerivAt s a (((k : ℝ) / a : ℝ) : ℂ)
  rw [he, mul_zero, zero_add, hexp, one_mul] at h
  convert! h using 1
  ring

/-- At an auxiliary pole `p`, the denominator derivative is the negative deleted-pole product
multiplied by the integer lattice exponential at `p`. -/
theorem auxContourDenominator_hasDerivAt_pole (s : Finset ℂ) (hs : -Complex.I ∉ s)
    (a : ℝ) (p : ℂ) (hp : p ∈ s) :
    HasDerivAt (auxContourDenominator s a)
      (-(auxDeletedPoleProduct s p) * integerLatticeExponential a p) p := by
  have hp0 := (auxRegulator_eq_zero_iff s hs p).mpr hp
  have h := auxContourDenominator_hasDerivAt s a p
  rw [hp0, zero_add, mul_zero, zero_mul, add_zero, (auxRegulator_hasDerivAt_pole s p hp).deriv] at h
  convert! h using 1
  have hd := auxNormalization_ne_zero hs hp
  rw [show p + Complex.I = -(-Complex.I - p) by ring]
  simp only [neg_mul, mul_div_cancel₀ _ hd]

/-- For positive `a` and an auxiliary set avoiding the target and lattice, every zero of the
auxiliary contour denominator has nonzero derivative. -/
theorem auxContourDenominator_deriv_ne_zero_of_eq_zero (s : Finset ℂ) (hs : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ))
    (z : ℂ) (hz : auxContourDenominator s a z = 0) : deriv (auxContourDenominator s a) z ≠ 0 := by
  rcases (auxContourDenominator_eq_zero_iff s hs ha z).mp hz with htarget | haux | ⟨k, hlat⟩
  · subst z
    rw [(auxContourDenominator_hasDerivAt_neg_I s hs a).deriv]
    exact integerContourNumerator_ne_zero ha
  · rw [(auxContourDenominator_hasDerivAt_pole s hs a z haux).deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (auxDeletedPoleProduct_ne_zero s hs z haux))
      (auxLatticeExponential_ne_zero s ha hsLattice z haux)
  · subst z
    rw [(auxContourDenominator_hasDerivAt_lattice s ha k).deriv]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) Complex.I_ne_zero) ha'
      · intro h
        have hi := congrArg Complex.im h
        norm_num at hi
    · exact auxRegulator_at_lattice_ne_zero s hs a hsLattice k

/-- For positive `a` and an auxiliary set excluding `-I`, the normalized contour coefficient at
the target pole is one. -/
theorem auxContour_coefficient_neg_I (s : Finset ℂ) (hs : -Complex.I ∉ s) {a : ℝ} (ha : 0 < a) :
    (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
      deriv (auxContourDenominator s a) (-Complex.I)) = 1 := by
  rw [(auxContourDenominator_hasDerivAt_neg_I s hs a).deriv]
  exact div_self (integerContourNumerator_ne_zero ha)

/-- For positive `a`, the normalized contour coefficient at lattice point `k / a` is `-auxWeight
s a k`. -/
theorem auxContour_coefficient_lattice (s : Finset ℂ) {a : ℝ} (ha : 0 < a) (k : ℤ) :
    (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
      deriv (auxContourDenominator s a) (((k : ℝ) / a : ℝ) : ℂ)) = -auxWeight s a k := by
  rw [(auxContourDenominator_hasDerivAt_lattice s ha k).deriv]
  simp only [auxWeight, div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring

/-- At a member of an auxiliary set excluding `-I`, the normalized contour coefficient equals
`auxResidueCoefficient s a p`. -/
theorem auxContour_coefficient_pole (s : Finset ℂ) (hs : -Complex.I ∉ s)
    (a : ℝ) (p : ℂ) (hp : p ∈ s) :
    (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
      deriv (auxContourDenominator s a) p) = auxResidueCoefficient s a p := by
  rw [(auxContourDenominator_hasDerivAt_pole s hs a p hp).deriv]
  simp only [auxResidueCoefficient, latticePoleFactor, integerLatticeExponential,
    div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring

/-- The auxiliary contour integrand equals the inverse denominator acting on `(exp (-2 * π * a)
- 1) • U z`. -/
theorem auxContourIntegrand_eq_denominator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset ℂ) (a : ℝ) (U : ℂ → E) (z : ℂ) :
    auxContourIntegrand s a U z = (auxContourDenominator s a z)⁻¹ •
      (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) • U z) := by
  rw [auxContourIntegrand, auxContourKernel, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- The regulator norm is the product of distances to the auxiliary poles divided by the product
of their distances from `-I`. -/
theorem auxRegulator_norm (s : Finset ℂ) (z : ℂ) :
    ‖auxRegulator s z‖ = (∏ p ∈ s, ‖z - p‖) / (∏ p ∈ s, ‖-Complex.I - p‖) := by
  simp only [auxRegulator, norm_prod, norm_div, Finset.prod_div_distrib]

/-- The kernel norm is the lattice pole factor norm times the auxiliary normalization product,
divided by the distance to `-I` and the product of distances to the auxiliary poles. -/
theorem auxContourKernel_norm (s : Finset ℂ) (a : ℝ) (z : ℂ) :
    ‖auxContourKernel s a z‖ =
      ‖latticePoleFactor a z‖ * (∏ p ∈ s, ‖-Complex.I - p‖) /
        (‖z + Complex.I‖ * ∏ p ∈ s, ‖z - p‖) := by
  simp only [auxContourKernel, auxContourDenominator, latticePoleFactor,
    norm_div, norm_mul, norm_neg, auxRegulator_norm, integerLatticeExponential]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
