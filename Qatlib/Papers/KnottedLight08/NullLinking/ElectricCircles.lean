/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaDuality
public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticLineTransport

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases

/-!
# Actual closed electric field lines on every time slice

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
A proper quarter-turn transfers every compact magnetic fiber to the
corresponding electric fiber. The parameterizations cover the
literal electric scalar levels and retain nonzero tangents oriented
along the electric field, including at the projective pole.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField

/-- The positive spatial quarter-turn carries electric fibers to
magnetic fibers while preserving their orientations. -/
def electricToMagnetic : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ × ℝ) where
  toFun s := (-s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, -s.1, s.2.2)
  left_inv := by rintro ⟨x, y, z⟩; simp
  right_inv := by rintro ⟨x, y, z⟩; simp
  map_add' := by
    rintro ⟨x, y, z⟩ ⟨a, b, c⟩
    change (-(y + b), x + a, z + c) = (-y + -b, x + a, z + c)
    simp [add_comm]
  map_smul' := by
    rintro k ⟨x, y, z⟩
    change (-(k * y), k * x, k * z) = (k * -y, k * x, k * z)
    rw [mul_neg]

/-- The affine electric fiber at physical time with the pole excluded. -/
def electricFiberAt (t : ℝ) (w : ℂ) : Set (ℝ × ℝ × ℝ) :=
  {s | zetaDen s.1 s.2.1 s.2.2 t ≠ 0 ∧ ranadaZeta s.1 s.2.1 s.2.2 t = w}

/-- Rotation identifies the finite electric and magnetic levels, with
the chart label multiplied by the constant minus i. -/
theorem mem_electricFiberAt_iff (t : ℝ) (w : ℂ) (s : ℝ × ℝ × ℝ) :
    s ∈ electricFiberAt t w ↔ electricToMagnetic s ∈ magneticFiberAt t (-Complex.I * w) := by
  rcases s with ⟨x, y, z⟩
  change (zetaDen x y z t ≠ 0 ∧ ranadaZeta x y z t = w) ↔
    (etaDen (-y) x z t ≠ 0 ∧ ranadaEta (-y) x z t = -Complex.I * w)
  rw [etaDen_quarterTurn, ranadaEta_quarterTurn]
  exact and_congr_right fun _ => ⟨congrArg (-Complex.I * ·),
    mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero)⟩

/-- The electric chart label becomes the magnetic label with real
part v and imaginary part minus u. -/
theorem rotated_electric_label (u v : ℝ) :
    -Complex.I * ((u : ℂ) + Complex.I * (v : ℂ)) =
      ((v : ℂ) + Complex.I * ((-u : ℝ) : ℂ)) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The rotated parameterization for the finite nonzero electric label
with real part u and imaginary part v. -/
def electricCircleAt (u v t θ : ℝ) : ℝ × ℝ × ℝ :=
  electricToMagnetic.symm (magneticCircleAt v (-u) t θ)

/-- The entire projective electric pole is parameterized by the
inverse quarter-turn of the magnetic pole. -/
def electricPoleCircleAt (t θ : ℝ) : ℝ × ℝ × ℝ :=
  electricToMagnetic.symm (magneticPoleCircleAt t θ)

/-- The finite electric parameterization has the full literal affine
fiber for its range. -/
theorem range_electric_circle_at (u v t : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    Set.range (electricCircleAt u v t) = electricFiberAt t ((u : ℂ) + Complex.I * (v : ℂ)) := by
  have ht : 0 < v ^ 2 + (-u) ^ 2 := by simpa only [neg_sq, add_comm] using hd
  ext s
  rw [mem_electricFiberAt_iff, rotated_electric_label, ← range_magnetic_circle_at v (-u) t ht]
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨θ, (electricToMagnetic.apply_symm_apply _).symm⟩
  · rintro ⟨θ, hθ⟩
    refine ⟨θ, ?_⟩
    apply electricToMagnetic.injective
    simpa only [electricCircleAt, LinearEquiv.apply_symm_apply] using hθ

/-- The rotated pole parameterization covers exactly the zero set of
the homogeneous electric denominator. -/
theorem range_electric_pole_circle_at (t : ℝ) :
    Set.range (electricPoleCircleAt t) =
      {s : ℝ × ℝ × ℝ | zetaDen s.1 s.2.1 s.2.2 t = 0} := by
  ext s
  have hP : (zetaDen s.1 s.2.1 s.2.2 t = 0) ↔
      electricToMagnetic s ∈ Set.range (magneticPoleCircleAt t) := by
    rw [range_magnetic_pole_circle_at]
    rcases s with ⟨x, y, z⟩
    change zetaDen x y z t = 0 ↔ etaDen (-y) x z t = 0
    rw [etaDen_quarterTurn]
  change s ∈ Set.range (electricPoleCircleAt t) ↔ zetaDen s.1 s.2.1 s.2.2 t = 0
  rw [hP]
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨θ, (electricToMagnetic.apply_symm_apply _).symm⟩
  · rintro ⟨θ, hθ⟩
    refine ⟨θ, ?_⟩
    apply electricToMagnetic.injective
    simpa only [electricPoleCircleAt, LinearEquiv.apply_symm_apply] using hθ

/-- The finite electric field lines retain the magnetic angular period. -/
theorem electric_circle_at_periodic (u v t : ℝ) :
    Function.Periodic (electricCircleAt u v t) (2 * Real.pi) :=
  fun θ => congrArg electricToMagnetic.symm (magnetic_circle_at_periodic v (-u) t θ)

/-- The pole electric line retains the full angular period. -/
theorem electric_pole_circle_at_periodic (t : ℝ) :
    Function.Periodic (electricPoleCircleAt t) (2 * Real.pi) :=
  fun θ => congrArg electricToMagnetic.symm (magnetic_pole_circle_at_periodic t θ)

/-- The Cartesian electric vector of the actual Rañada field. -/
def ranadaElectricVector (t : ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  cartesianCoordinates.symm (fun j => (ranadaE s.1 s.2.1 s.2.2 t j).re)

/-- The rotation identification of the literal complex fields also
identifies their real Cartesian vectors. -/
theorem ranadaMagneticVector_electricToMagnetic (t : ℝ) (s : ℝ × ℝ × ℝ) :
    ranadaMagneticVector t (electricToMagnetic s) = electricToMagnetic (ranadaElectricVector t s) := by
  rcases s with ⟨x, y, z⟩
  change cartesianCoordinates.symm (fun j => (ranadaB (-y) x z t j).re) =
    electricToMagnetic (cartesianCoordinates.symm (fun j => (ranadaE x y z t j).re))
  rw [ranadaB_quarterTurn_eq_ranadaE]
  apply cartesianCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  fin_cases j <;> rfl

/-- The inverse rotation carries an oriented regular magnetic
parameterization to an oriented regular electric one. -/
private theorem hasDerivAt_electric_of_magnetic (c : ℝ → ℝ × ℝ × ℝ) (t θ μ : ℝ)
    (h : HasDerivAt c (μ • ranadaMagneticVector t (c θ)) θ)
    (hne : μ • ranadaMagneticVector t (c θ) ≠ 0) :
    let e := fun s => electricToMagnetic.symm (c s)
    μ • ranadaElectricVector t (e θ) ≠ 0 ∧
      HasDerivAt e (μ • ranadaElectricVector t (e θ)) θ := by
  let e := fun s => electricToMagnetic.symm (c s)
  have he : electricToMagnetic (e θ) = c θ := electricToMagnetic.apply_symm_apply _
  have hB := ranadaMagneticVector_electricToMagnetic t (e θ)
  rw [he] at hB
  have hT : electricToMagnetic.symm (μ • ranadaMagneticVector t (c θ)) =
      μ • ranadaElectricVector t (e θ) := by
    rw [map_smul, hB, LinearEquiv.symm_apply_apply]
  constructor
  · intro h0
    apply hne
    apply electricToMagnetic.symm.injective
    rw [hT, h0, map_zero]
  · let L := electricToMagnetic.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hD := L.hasFDerivAt.comp_hasDerivAt θ h
    have hEq : L (μ • ranadaMagneticVector t (c θ)) =
        μ • ranadaElectricVector t (e θ) := hT
    exact hD.congr_deriv hEq

/-- At every real time the full compact affine electric field line has
a nonzero tangent with the orientation of the actual electric field. -/
theorem hasDerivAt_electric_circle_at (u v t θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    ∃ μ : ℝ, 0 < μ ∧ (μ • ranadaElectricVector t (electricCircleAt u v t θ)) ≠ 0 ∧
      HasDerivAt (electricCircleAt u v t) (μ • ranadaElectricVector t (electricCircleAt u v t θ)) θ := by
  have hpos : 0 < v ^ 2 + (-u) ^ 2 := by simpa only [neg_sq, add_comm] using hd
  obtain ⟨μ, hμ, hn, h⟩ := hasDerivAt_magnetic_circle_at v (-u) t θ hpos
  exact ⟨μ, hμ, hasDerivAt_electric_of_magnetic (magneticCircleAt v (-u) t) t θ μ h hn⟩

/-- The transported electric pole circle is regular and follows the
actual electric field with its orientation, at every time. -/
theorem hasDerivAt_electric_pole_circle_at (t θ : ℝ) :
    ∃ μ : ℝ, 0 < μ ∧ (μ • ranadaElectricVector t (electricPoleCircleAt t θ)) ≠ 0 ∧
      HasDerivAt (electricPoleCircleAt t) (μ • ranadaElectricVector t (electricPoleCircleAt t θ)) θ := by
  obtain ⟨μ, hμ, hn, h⟩ := hasDerivAt_magnetic_pole_circle_at t θ
  exact ⟨μ, hμ, hasDerivAt_electric_of_magnetic (magneticPoleCircleAt t) t θ μ h hn⟩

end Qatlib.Papers.KnottedLight08.NullLinking
