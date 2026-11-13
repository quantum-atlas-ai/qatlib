/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
import Qatlib.Papers.RydbergMaxCut26.Rounding.NormalizedProjection

/-!
# Rounding physical moment matrices to product states

The physical construction `physicalFit` extracts real unit vectors from the constrained moment
completion of a density matrix. Their off-site dot products reproduce `tParam`; projecting and
normalizing them through `physicalRound` produces a physical Bloch product state with an
explicit edge-energy formula. See [CrostaSaubanereHuber2026].

## Main statements

* `physical_fit_dot`: identifies the Gram dot products with physical correlation parameters.
* `physical_round_density`: proves positivity and trace one of the rounded product state.
* `physical_round_energy`: expresses its QMC energy through rounded edge dot products.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase Qatlib.Papers.RydbergMaxCut26.Rounding.Projection
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch

/-- The real Gram fit vectors of the constrained moment completion `sourceSDP` associated with a
physical density matrix. -/
noncomputable def physicalFit (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) : Fin n → Fin 2×MomentIndex n → ℝ :=
  fitVector (sourceSDP n ρ) (sourceSDP_pos n ρ hρ htr)

/-- Each physical Gram fit vector has squared norm one, as used in the constrained completion
construction of [CrostaSaubanereHuber2026]. -/
theorem physical_fit_unit (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i : Fin n) : ∑ c,(physicalFit n ρ hρ htr i c)^2=1 :=
  fit_unit _ _ (sourceSDP_diag n ρ hρ htr) i

/-- For distinct sites, the dot product of their physical Gram fit vectors equals `tParam`, as
in the constrained completion construction of [CrostaSaubanereHuber2026]. -/
theorem physical_fit_dot (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i j : Fin n) (hij : i≠j) :
    ∑ c,physicalFit n ρ hρ htr i c*physicalFit n ρ hρ htr j c=tParam ρ i j := by
  rw [physicalFit,fit_dot,sourceSDP_xx n ρ i j hij,sourceSDP_yy n ρ i j hij]
  ring

/-- The Bloch vectors obtained by projecting and normalizing the Gram fit vectors of the
physical moment completion. -/
noncomputable def physicalRound (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (R : Fin 3 → Fin 2×MomentIndex n → ℝ) :
    Fin n → Fin 3 → ℝ := roundVector (sourceSDP n ρ) (sourceSDP_pos n ρ hρ htr) R

/-- For every projection matrix, the product state built from the physically rounded Bloch
vectors is positive semidefinite and has trace one; see [CrostaSaubanereHuber2026]. -/
theorem physical_round_density (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (R : Fin 3 → Fin 2×MomentIndex n → ℝ) :
    (productState (physicalRound n ρ hρ htr R)).PosSemidef ∧
      (productState (physicalRound n ρ hρ htr R)).trace=1 :=
  rounded_product_density _ _ R

/-- For distinct edge endpoints, the QMC energy of the physically rounded product state is
`-1/4` times the weighted sum of one minus each rounded edge dot product. -/
theorem physical_round_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Fin 3 → Fin 2×MomentIndex n → ℝ) :
    energy (qmcHamiltonian ends w) (productState (physicalRound n ρ hρ htr R)) =
      -(1/4:ℝ)*∑ e,w e*(1-∑ a,physicalRound n ρ hρ htr R (ends e).1 a*
        physicalRound n ρ hρ htr R (ends e).2 a) := qmc_product_energy ends hends w _
end Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
