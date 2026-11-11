/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiracLatGas13.MainResults.PauliRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Exact stream–collide product decomposition of the Dirac evolution (Eqs. (24), (39c)–(40))

Source: J. Yepez, *Quantum lattice gas model of Dirac particles in 1+1 dimensions*,
arXiv:1307.3595v1 (2013), §II C Eq. (24) p. 6, and §III Eqs. (39c), (39d), (40) pp. 7–8.

Claim `c001` (Eq. (24)): the quantum algorithm for a free Dirac particle in 1+1D is the
product of the streams `S₁ᵀS₀` and the collide operator `C`,

  `|ψ(t+τ)⟩ = S₁ᵀ S₀ C |ψ(t)⟩ = e^{-i ℓ h_D/(ℏ c)} |ψ(t)⟩`,

and this is an *exact* factorisation (no Trotter or BCH error terms).  In momentum space
`S₁ᵀS₀ = e^{σ_z ℓ ∂_z} = e^{i p_z ℓ/ℏ}` is a single rotation about `ẑ`, and the
collide operator `C = e^{-i (β₁/2) n̂₁·σ}` is a rotation about `n̂₁ = (cos(β₂/2), -sin(β₂/2), 0)`
with `β₂/2 = -ℓ k_z` (Eqs. (27), (33), (41)).

Claim `c002` (Eqs. (39c)–(40)): the generator is the Dirac Hamiltonian
`h_D = -σ_z c p_z + σ_x m c²`, the finite-`τ` evolution is `U_S^z U_C = e^{-i ℓ h_D/(ℏ c)}`
with `τ` a *finite* grid time (no continuum limit is taken), and the grid scales satisfy
the transcendental equation (40) `E τ/ℏ = sin(E ℓ/(ℏ c))`.

The composite-rotation identity `Rot_zhat_mul_Rot_perp` is the explicit form of Eq. (29a)/(37).
The final specialisation to the Dirac rotation is Eq. (39d).  All results are fully proved.
-/

set_option autoImplicit false

-- The entrywise 2×2 matrix identities below expand to moderately large
-- polynomial goals; give elaboration a larger deterministic heartbeat budget.
set_option maxHeartbeats 2000000

open Matrix

namespace Qatlib.Papers.DiracLatGas13.MainResults

noncomputable section

/-- The `z`-axis unit vector. -/
def zhat : ℝ × ℝ × ℝ := (0, 0, 1)

/-- The stream half-angle `β₂/2 = -ℓ k_z = -ℓ p_z/ℏ` (Eq. (41)). -/
def streamAngle (p ℓ ℏ : ℝ) : ℝ := -(p * ℓ / ℏ)

/-- The stream operator `S₁ᵀ S₀ = e^{σ_z ℓ ∂_z} = e^{i p_z ℓ/ℏ}` in momentum space,
i.e. the Euler-form rotation about `ẑ` by `-ℓ p_z/ℏ` (cf. Eq. (42)). -/
def streamOp (p ℓ ℏ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Rot zhat (streamAngle p ℓ ℏ)

/-- The collide rotation axis `n̂₁ = (cos(β₂/2), -sin(β₂/2), 0)` from Eq. (33). -/
def collideAxis (p ℓ ℏ : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos (streamAngle p ℓ ℏ), -Real.sin (streamAngle p ℓ ℏ), 0)

/-- The collide operator `U_C = e^{-i (β₁/2) n̂₁·σ}` (Eq. (27b) with (33)).  The
argument `a₁` is the half-angle `β₁/2`. -/
def collideOp (p ℓ ℏ a₁ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Rot (collideAxis p ℓ ℏ) a₁

/-- The Dirac Hamiltonian `h_D = -σ_z c p_z + σ_x m c²` (Eq. (39c)). -/
def diracHamiltonian (m c p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauli (m * c ^ 2, 0, -(c * p))

/-- The unit Dirac rotation axis `h_D/E`, Eq. (38). -/
def diracAxis (E m c p : ℝ) : ℝ × ℝ × ℝ :=
  (m * c ^ 2 / E, 0, -(c * p) / E)

/-- The single Dirac rotation `e^{-i ℓ h_D/(ℏ c)} = Rot (h_D/E) (E ℓ/(ℏ c))`, Eq. (39d). -/
def diracRotation (E m c p ℓ ℏ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Rot (diracAxis E m c p) (E * ℓ / (ℏ * c))

/-- `h_D` written in the Pauli basis, `h_D = -(c p_z) σ_z + (m c²) σ_x` (Eq. (39c)). -/
theorem diracHamiltonian_form (m c p : ℝ) :
    diracHamiltonian m c p = (-(c * p)) • sigmaZ + (m * c ^ 2) • sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracHamiltonian, pauli, sigmaX, sigmaY, sigmaZ] <;>
    ring

/-- **Composite-rotation identity** (Eq. (29a) specialised to (33), and Eq. (37)):
a rotation about `ẑ` followed by a rotation about `(cos a₂, -sin a₂, 0)` is the matrix
`(cos a₁ cos a₂) • 1 - (i sin a₁) • σ_x - (i cos a₁ sin a₂) • σ_z`. -/
theorem Rot_zhat_mul_Rot_perp (a₁ a₂ : ℝ) :
    Rot zhat a₂ * Rot (Real.cos a₂, -Real.sin a₂, 0) a₁
      = ((Real.cos a₁ * Real.cos a₂ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - (Complex.I * (Real.sin a₁ : ℂ)) • sigmaX
        - (Complex.I * ((Real.cos a₁ * Real.sin a₂ : ℝ)) : ℂ) • sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [Rot, zhat, pauli, sigmaX, sigmaY, sigmaZ, Matrix.one_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im] <;>
    (try ring) <;> (try linear_combination -Real.sin a₁ * Real.sin_sq_add_cos_sq a₂)

/-- **Eq. (24) / (39d): exact stream–collide product.**  With the paper's trigonometric
identifications
* `sin(β₁/2) = m c² τ/ℏ` (Eq. (34)),
* `cos(β₁/2) sin(β₂/2) = -c p_z τ/ℏ` (Eq. (35)),
* `cos(β₁/2) cos(β₂/2) = √(1-(E τ/ℏ)²)` (Eq. (36b)),

and the grid condition `E τ/ℏ = sin(E ℓ/(ℏ c))` with `cos(E ℓ/(ℏ c)) = √(1-(E τ/ℏ)²)`
(Eq. (40)), the stream–collide product equals the single Dirac rotation
`e^{-i ℓ h_D/(ℏ c)}`.  No Trotter/BCH approximation is used. -/
theorem streamCollide_eq_diracRotation
    (p m c ℏ ℓ τ E a₁ : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hEpos : 0 < E)
    (hsin : Real.sin a₁ = m * c ^ 2 * τ / ℏ)
    (hpc : Real.cos a₁ * Real.sin (streamAngle p ℓ ℏ) = -(c * p * τ / ℏ))
    (hcos : Real.cos a₁ * Real.cos (streamAngle p ℓ ℏ) = Real.sqrt (1 - (E * τ / ℏ) ^ 2))
    (hgrid : E * τ / ℏ = Real.sin (E * ℓ / (ℏ * c)))
    (hcosE : Real.sqrt (1 - (E * τ / ℏ) ^ 2) = Real.cos (E * ℓ / (ℏ * c))) :
    streamOp p ℓ ℏ * collideOp p ℓ ℏ a₁ = diracRotation E m c p ℓ ℏ := by
  have hEne : E ≠ 0 := ne_of_gt hEpos
  -- The three components of the Dirac rotation, matched against (34), (35), (36b).
  have hcos' : Real.cos a₁ * Real.cos (streamAngle p ℓ ℏ) = Real.cos (E * ℓ / (ℏ * c)) := by
    rw [hcos, hcosE]
  have hsin' : Real.sin a₁ = Real.sin (E * ℓ / (ℏ * c)) * (m * c ^ 2 / E) := by
    rw [hsin, ← hgrid]
    field_simp <;> ring
  have hpc' : Real.cos a₁ * Real.sin (streamAngle p ℓ ℏ)
      = -(c * p / E) * Real.sin (E * ℓ / (ℏ * c)) := by
    rw [hpc, ← hgrid]
    field_simp <;> ring
  simp only [streamOp, collideOp, collideAxis, diracRotation, diracAxis]
  rw [Rot_zhat_mul_Rot_perp a₁ (streamAngle p ℓ ℏ)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [Rot, pauli, sigmaX, sigmaY, sigmaZ, Matrix.one_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im, hcos', hsin', hpc'] <;>
    (try field_simp) <;> (try ring)

/-- **Eq. (39d), finite-τ statement (claim c002).**  Because no continuum limit `τ → 0` is
taken anywhere in the derivation, `τ` may be any positive finite grid time; the exact
product identity still holds.  This restates `streamCollide_eq_diracRotation` while making
explicit that `τ` is finite (`0 < τ`). -/
theorem finiteTau_dirac_evolution
    (p m c ℏ ℓ τ E a₁ : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hEpos : 0 < E) (hτpos : 0 < τ)
    (hsin : Real.sin a₁ = m * c ^ 2 * τ / ℏ)
    (hpc : Real.cos a₁ * Real.sin (streamAngle p ℓ ℏ) = -(c * p * τ / ℏ))
    (hcos : Real.cos a₁ * Real.cos (streamAngle p ℓ ℏ) = Real.sqrt (1 - (E * τ / ℏ) ^ 2))
    (hgrid : E * τ / ℏ = Real.sin (E * ℓ / (ℏ * c)))
    (hcosE : Real.sqrt (1 - (E * τ / ℏ) ^ 2) = Real.cos (E * ℓ / (ℏ * c))) :
    streamOp p ℓ ℏ * collideOp p ℓ ℏ a₁ = diracRotation E m c p ℓ ℏ :=
  streamCollide_eq_diracRotation p m c ℏ ℓ τ E a₁ hℏ hc hEpos hsin hpc hcos hgrid hcosE

/-- **Eq. (40): the grid-scale equation.**  Given the trigonometric identification
`cos(E ℓ/(ℏ c)) = √(1-(E τ/ℏ)²)` of Eq. (39d), the grid scales must satisfy
`E τ/ℏ = sin(E ℓ/(ℏ c))`. -/
theorem gridEquation_of_cos
    (E ℏ c ℓ τ : ℝ) (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hEpos : 0 < E)
    (hr : 0 ≤ 1 - (E * τ / ℏ) ^ 2)
    (hcos : Real.cos (E * ℓ / (ℏ * c)) = Real.sqrt (1 - (E * τ / ℏ) ^ 2))
    (hsinpos : 0 ≤ Real.sin (E * ℓ / (ℏ * c)))
    (hτpos : 0 ≤ E * τ / ℏ) :
    E * τ / ℏ = Real.sin (E * ℓ / (ℏ * c)) := by
  have hc2 : Real.cos (E * ℓ / (ℏ * c)) ^ 2 = 1 - (E * τ / ℏ) ^ 2 := by
    rw [hcos, Real.sq_sqrt hr]
  have htrig : Real.sin (E * ℓ / (ℏ * c)) ^ 2 + Real.cos (E * ℓ / (ℏ * c)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hsq : (E * τ / ℏ) ^ 2 = Real.sin (E * ℓ / (ℏ * c)) ^ 2 := by nlinarith [hc2, htrig]
  have hprod : (E * τ / ℏ - Real.sin (E * ℓ / (ℏ * c)))
      * (E * τ / ℏ + Real.sin (E * ℓ / (ℏ * c))) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hprod with h | h
  · linarith
  · linarith

end

end Qatlib.Papers.DiracLatGas13.MainResults
