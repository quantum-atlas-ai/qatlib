/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalPower
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanRayDifferential

public import Mathlib.LinearAlgebra.StdBasis

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth potentials for the powered Bateman fields

[Kedia2013TyingKnots], equation (6),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
At each physical time, the real and imaginary parts of the covector
`α^p d(β^q)` give electric and magnetic vector potentials for the actual
powered fields. In this smooth choice of potentials the two helicity
densities coincide pointwise. Both scalar factors are transported by
the same spatial ray, which also pulls back the complex potential.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta)
open scoped ComplexConjugate

local notation "BatemanSpace" => ℝ × ℝ × ℝ

/-- The three positively oriented Cartesian directions on a physical slice. -/
def batemanAxis (j : Fin 3) : BatemanSpace :=
  ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] j

/-- The linear identification of triples with their Cartesian coordinates. -/
def batemanCartesianCoordinates : BatemanSpace ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun s := ![s.1, s.2.1, s.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv := by rintro ⟨x, y, z⟩; rfl
  right_inv := by intro v; funext i; fin_cases i <;> rfl
  map_add' := by intro u v; funext i; fin_cases i <;> rfl
  map_smul' := by intro c u; funext i; fin_cases i <;> rfl

/-- The ordered real Cartesian basis of the slice. -/
noncomputable def batemanCartesianBasis : Module.Basis (Fin 3) ℝ BatemanSpace :=
  (Pi.basisFun ℝ (Fin 3)).map batemanCartesianCoordinates.symm

/-- Basis vectors agree with the coordinate derivatives used for the fields. -/
theorem batemanCartesianBasis_apply (j : Fin 3) : batemanCartesianBasis j = batemanAxis j := by
  fin_cases j <;>
    simp [batemanCartesianBasis, Module.Basis.map_apply, Pi.basisFun_apply, batemanCartesianCoordinates, batemanAxis]

/-- The basis coordinates are the literal Cartesian triple entries. -/
theorem batemanCartesianBasis_repr (s : BatemanSpace) :
    ∀ i, batemanCartesianBasis.repr s i = ![s.1, s.2.1, s.2.2] i := by
  intro i
  change (Pi.basisFun ℝ (Fin 3)).repr (batemanCartesianCoordinates s) i = _
  exact Pi.basisFun_repr ℝ (Fin 3) (batemanCartesianCoordinates s) i

/-- The powered first Bateman scalar at fixed time. -/
noncomputable def batemanAlphaPower (p : ℕ) (t : ℝ) (s : BatemanSpace) : ℂ :=
  (batemanPairAt t s).1 ^ p

/-- The powered second Bateman scalar at fixed time. -/
noncomputable def batemanBetaPower (q : ℕ) (t : ℝ) (s : BatemanSpace) : ℂ :=
  (batemanPairAt t s).2 ^ q

/-- The first powered scalar is smooth on each entire physical slice. -/
theorem contDiff_batemanAlphaPower (p : ℕ) (t : ℝ) : ContDiff ℝ ⊤ (batemanAlphaPower p t) := by
  have h : ContDiff ℝ ⊤ (fun s : BatemanSpace => (s.1, s.2.1, s.2.2, t)) := by fun_prop
  exact (contDiff_rationalAlpha.comp h).pow p

/-- The second powered scalar is smooth on each entire physical slice. -/
theorem contDiff_batemanBetaPower (q : ℕ) (t : ℝ) : ContDiff ℝ ⊤ (batemanBetaPower q t) := by
  have h : ContDiff ℝ ⊤ (fun s : BatemanSpace => (s.1, s.2.1, s.2.2, t)) := by fun_prop
  exact (contDiff_rationalBeta.comp h).pow q

/-- Differentiating the first powered scalar in a Cartesian direction gives
the corresponding component of the physical gradient. -/
theorem fderiv_batemanAlphaPower_axis (p : ℕ) (x y z t : ℝ) (j : Fin 3) :
    fderiv ℝ (batemanAlphaPower p t) (x, y, z) (batemanAxis j) =
      alphaPowerGradient p x y z t j := by
  have h := ((contDiff_batemanAlphaPower p t).differentiable (by simp) (x, y, z)).hasFDerivAt
  have hx := (hasDerivAt_id x).prodMk (hasDerivAt_const x (y, z))
  have hy := (hasDerivAt_const y x).prodMk ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have hz := (hasDerivAt_const z x).prodMk ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  fin_cases j
  · exact (h.comp_hasDerivAt x hx).deriv.symm
  · exact (h.comp_hasDerivAt y hy).deriv.symm
  · exact (h.comp_hasDerivAt z hz).deriv.symm

/-- Differentiating the second powered scalar in a Cartesian direction gives
the corresponding component of the physical gradient. -/
theorem fderiv_batemanBetaPower_axis (q : ℕ) (x y z t : ℝ) (j : Fin 3) :
    fderiv ℝ (batemanBetaPower q t) (x, y, z) (batemanAxis j) =
      betaPowerGradient q x y z t j := by
  have h := ((contDiff_batemanBetaPower q t).differentiable (by simp) (x, y, z)).hasFDerivAt
  have hx := (hasDerivAt_id x).prodMk (hasDerivAt_const x (y, z))
  have hy := (hasDerivAt_const y x).prodMk ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have hz := (hasDerivAt_const z x).prodMk ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  fin_cases j
  · exact (h.comp_hasDerivAt x hx).deriv.symm
  · exact (h.comp_hasDerivAt y hy).deriv.symm
  · exact (h.comp_hasDerivAt z hz).deriv.symm

/-- The complex vector potential `α^p d(β^q)` on physical space. -/
noncomputable def batemanPotential (p q : ℕ) (t : ℝ) (s : BatemanSpace) : BatemanSpace →L[ℝ] ℂ :=
  batemanAlphaPower p t s • fderiv ℝ (batemanBetaPower q t) s

/-- The complex covector potential is smooth in space at each fixed time. -/
theorem contDiff_batemanPotential (p q : ℕ) (t : ℝ) :
    ContDiff ℝ ⊤ (batemanPotential p q t) :=
  (contDiff_batemanAlphaPower p t).smul ((contDiff_batemanBetaPower q t).fderiv_right (by simp))

/-- The Cartesian coefficient vector of a complex spatial covector. -/
def batemanCovectorCoefficients (A : BatemanSpace →L[ℝ] ℂ) : Fin 3 → ℂ :=
  fun j => A (batemanAxis j)

/-- The complex Cartesian curl, computed from actual spatial derivatives. -/
noncomputable def batemanCovectorCurl (A : BatemanSpace → BatemanSpace →L[ℝ] ℂ) (x : BatemanSpace) : Fin 3 → ℂ :=
  let D := fderiv ℝ A x
  ![D (batemanAxis 1) (batemanAxis 2) - D (batemanAxis 2) (batemanAxis 1),
    D (batemanAxis 2) (batemanAxis 0) - D (batemanAxis 0) (batemanAxis 2),
    D (batemanAxis 0) (batemanAxis 1) - D (batemanAxis 1) (batemanAxis 0)]

/-- The antisymmetric derivative is the wedge of the two scalar
differentials. The smooth Hessian of the second scalar cancels. -/
theorem batemanPotential_exterior (p q : ℕ) (t : ℝ) (x u v : BatemanSpace) :
    fderiv ℝ (batemanPotential p q t) x u v - fderiv ℝ (batemanPotential p q t) x v u =
      fderiv ℝ (batemanAlphaPower p t) x u * fderiv ℝ (batemanBetaPower q t) x v -
      fderiv ℝ (batemanAlphaPower p t) x v * fderiv ℝ (batemanBetaPower q t) x u := by
  let a := batemanAlphaPower p t
  let b := batemanBetaPower q t
  have ha := (contDiff_batemanAlphaPower p t).differentiable (by simp) x
  have hb := (contDiff_batemanBetaPower q t).of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)
  have hD := (hb.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by simp) x
  have hsym := (hb.contDiffAt (x := x)).isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ 2)
  change fderiv ℝ (fun y => a y • fderiv ℝ b y) x u v -
    fderiv ℝ (fun y => a y • fderiv ℝ b y) x v u = _
  rw [fderiv_fun_smul ha hD]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [hsym.eq u v]
  ring

/-- The chosen complex vector potential has curl equal to the actual
powered Bateman field on every spatial slice. Real and imaginary parts
therefore yield the electric and magnetic curls. -/
theorem batemanCovectorCurl_batemanPotential (p q : ℕ) (x y z t : ℝ) :
    batemanCovectorCurl (batemanPotential p q t) (x, y, z) = rationalPowerField p q x y z t := by
  funext j
  fin_cases j <;>
    simp [batemanCovectorCurl, batemanPotential_exterior, rationalPowerField, cross3,
      fderiv_batemanAlphaPower_axis, fderiv_batemanBetaPower_axis]

/-- Real Cartesian curl of a spatial covector. -/
noncomputable def batemanRealCurl (A : BatemanSpace → BatemanSpace →L[ℝ] ℝ) (x : BatemanSpace) :
    Fin 3 → ℝ :=
  let D := fderiv ℝ A x
  ![D (batemanAxis 1) (batemanAxis 2) - D (batemanAxis 2) (batemanAxis 1),
    D (batemanAxis 2) (batemanAxis 0) - D (batemanAxis 0) (batemanAxis 2),
    D (batemanAxis 0) (batemanAxis 1) - D (batemanAxis 1) (batemanAxis 0)]

/-- A real-linear projection of a complex covector commutes with its
Cartesian curl. -/
theorem batemanRealCurl_project {A : BatemanSpace → BatemanSpace →L[ℝ] ℂ} {x : BatemanSpace}
    (hA : DifferentiableAt ℝ A x) (L : ℂ →L[ℝ] ℝ) (j : Fin 3) :
    batemanRealCurl (fun y => L.comp (A y)) x j = L (batemanCovectorCurl A x j) := by
  have h := fderiv_clm_comp (differentiableAt_const L) hA
  have hD (u v : BatemanSpace) :
      fderiv ℝ (fun y => L.comp (A y)) x u v = L (fderiv ℝ A x u v) := by
    rw [h]
    simp [ContinuousLinearMap.compL_apply]
  fin_cases j <;> simp [batemanRealCurl, batemanCovectorCurl, hD]

/-- The electric vector potential is the real part of the complex gauge. -/
noncomputable def batemanElectricPotential (p q : ℕ) (t : ℝ) (x : BatemanSpace) :
    BatemanSpace →L[ℝ] ℝ :=
  Complex.reCLM.comp (batemanPotential p q t x)

/-- The magnetic vector potential is the imaginary part of the complex gauge. -/
noncomputable def batemanMagneticPotential (p q : ℕ) (t : ℝ) (x : BatemanSpace) :
    BatemanSpace →L[ℝ] ℝ :=
  Complex.imCLM.comp (batemanPotential p q t x)

/-- The real electric potential has curl equal to the actual electric field. -/
theorem batemanRealCurl_electric (p q : ℕ) (x y z t : ℝ) (j : Fin 3) :
    batemanRealCurl (batemanElectricPotential p q t) (x, y, z) j =
      (rationalPowerField p q x y z t j).re := by
  unfold batemanElectricPotential
  rw [batemanRealCurl_project ((contDiff_batemanPotential p q t).differentiable (by simp) _),
    batemanCovectorCurl_batemanPotential]
  rfl

/-- The real magnetic potential has curl equal to the actual magnetic field. -/
theorem batemanRealCurl_magnetic (p q : ℕ) (x y z t : ℝ) (j : Fin 3) :
    batemanRealCurl (batemanMagneticPotential p q t) (x, y, z) j =
      (rationalPowerField p q x y z t j).im := by
  unfold batemanMagneticPotential
  rw [batemanRealCurl_project ((contDiff_batemanPotential p q t).differentiable (by simp) _),
    batemanCovectorCurl_batemanPotential]
  rfl

/-- Taking the complex potential at the ray's image and pulling back its
spatial covector gives exactly the initial potential. -/
theorem batemanPotential_pullback (p q : ℕ) (t : ℝ) (x : BatemanSpace) :
    (batemanPotential p q t (batemanRay t x)).comp (fderiv ℝ (batemanRay t) x) =
      batemanPotential p q 0 x := by
  have hpair (s : BatemanSpace) : batemanPairAt t (batemanRay t s) = batemanPairAt 0 s :=
    batemanPairAt_batemanRay t s
  have hα : batemanAlphaPower p t (batemanRay t x) = batemanAlphaPower p 0 x := by
    simp only [batemanAlphaPower, hpair]
  have hβ : (batemanBetaPower q t) ∘ (batemanRay t) = batemanBetaPower q 0 :=
    funext fun s => by simp only [Function.comp_apply, batemanBetaPower, hpair]
  have hb := (contDiff_batemanBetaPower q t).differentiable (by simp) (batemanRay t x)
  have hRay := (contDiff_bateman_ray t).differentiable (by simp) x
  have hD := (hb.hasFDerivAt.comp x hRay.hasFDerivAt).fderiv
  rw [hβ] at hD
  apply ContinuousLinearMap.ext
  intro u
  simp only [batemanPotential, ContinuousLinearMap.comp_apply, smul_apply, hα]
  rw [hD, ContinuousLinearMap.comp_apply]

/-- Electric helicity density in the real part of the Bateman gauge. -/
noncomputable def batemanElectricHelicityDensity (p q : ℕ) (t : ℝ) (s : BatemanSpace) : ℝ :=
  dot3 (fun j => (batemanPotential p q t s (batemanAxis j)).re)
    (fun j => (rationalPowerField p q s.1 s.2.1 s.2.2 t j).re)

/-- Magnetic helicity density in the imaginary part of the Bateman gauge. -/
noncomputable def batemanMagneticHelicityDensity (p q : ℕ) (t : ℝ) (s : BatemanSpace) : ℝ :=
  dot3 (fun j => (batemanPotential p q t s (batemanAxis j)).im)
    (fun j => (rationalPowerField p q s.1 s.2.1 s.2.2 t j).im)

/-- The complex pairing without conjugation vanishes because the potential
is proportional to the second gradient of the cross product. -/
theorem batemanPotential_dot_field (p q : ℕ) (x y z t : ℝ) :
    dot3 (batemanCovectorCoefficients (batemanPotential p q t (x, y, z)))
      (rationalPowerField p q x y z t) = 0 := by
  simp [batemanCovectorCoefficients, batemanPotential, fderiv_batemanBetaPower_axis,
    rationalPowerField, cross3, dot3]
  ring

/-- The electric and magnetic helicity densities coincide pointwise in
the smooth Bateman gauge. -/
theorem bateman_electric_helicity_eq_magnetic (p q : ℕ) (t : ℝ) (s : BatemanSpace) :
    batemanElectricHelicityDensity p q t s = batemanMagneticHelicityDensity p q t s := by
  rcases s with ⟨x, y, z⟩
  have h := congrArg Complex.re (batemanPotential_dot_field p q x y z t)
  simp only [dot3, Complex.add_re, Complex.mul_re, Complex.zero_re, batemanCovectorCoefficients] at h
  dsimp only [batemanElectricHelicityDensity, batemanMagneticHelicityDensity, dot3, Prod.fst, Prod.snd]
  linarith only [h]

/-- The common density is half the real Hermitian pairing of the complex
potential and its actual curl. -/
theorem bateman_helicity_eq_hermitian (p q : ℕ) (t : ℝ) (s : BatemanSpace) :
    batemanElectricHelicityDensity p q t s =
      (dot3 (fun j => conj (batemanPotential p q t s (batemanAxis j)))
        (rationalPowerField p q s.1 s.2.1 s.2.2 t)).re / 2 := by
  have h := bateman_electric_helicity_eq_magnetic p q t s
  simp only [batemanElectricHelicityDensity, batemanMagneticHelicityDensity, dot3] at h ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
    sub_neg_eq_add]
  linarith only [h]

end Qatlib.Papers.KnotLight13.TorusFamily
