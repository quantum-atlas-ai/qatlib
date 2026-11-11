/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalWord

/-!
# Imaginary-time weights for physical product words

The continuous linear map `weightMap` implements conjugation by imaginary-time evolution of the
physical total Hamiltonian. The module shows that this weight fixes exact evolution, preserves
the relevant interaction-picture norm identities, and transports the differential equation for
the relative product word. See [HejaziZiniArrazola2024].

## Main statements

* `physical_weighted_exact`: Imaginary-time weighting by the total Hamiltonian leaves its exact
  real-time evolution unchanged.
* `physical_interaction_norm`: The weighted interaction generator has the same norm as the
  weighted difference between the product generator and the total generator.
* `physical_weighted_derivative`: The derivative of the weighted relative word is the product of
  the weighted interaction generator and the weighted relative word.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The real continuous linear map sending `A` to `exp(lam * h.total) * A * exp(-lam *
h.total)`. -/
def weightMap (h : PhysicalHamiltonian N R M k d J) (lam : ℝ) :
    Matrix (Register N) (Register N) ℂ →L[ℝ] Matrix (Register N) (Register N) ℂ :=
  (right (NormedSpace.exp ((-lam : ℂ) • h.total))).comp (left (NormedSpace.exp ((lam : ℂ) • h.total)))

/-- Applying `weightMap h lam` agrees with imaginary-time weighting by `h.total`. -/
theorem weightMap_apply (h : PhysicalHamiltonian N R M k d J) (lam : ℝ)
    (A : Matrix (Register N) (Register N) ℂ) : weightMap h lam A=weighted h.total A lam := rfl

/-- Imaginary-time weighting by the total Hamiltonian leaves its exact real-time evolution
unchanged. -/
theorem physical_weighted_exact (h : PhysicalHamiltonian N R M k d J) (lam t : ℝ) :
    weighted h.total (evolve h.total t) lam=evolve h.total t := by
  let E := NormedSpace.exp ((lam : ℂ) • h.total)
  let F := NormedSpace.exp ((-lam : ℂ) • h.total)
  let U := evolve h.total t
  have hc : Commute E U :=
    (((Commute.refl h.total).smul_left (lam : ℂ)).smul_right (((-t : ℂ)*Complex.I))).exp
  have he (s : ℝ) : s • h.total=(s : ℂ) • h.total := by ext i j; exact Complex.real_smul
  have hEF : E*F=1 := by
    simpa only [E, F, he, neg_neg, Complex.ofReal_neg] using exp_neg_time_mul h.total (-lam)
  change E*U*F=U
  rw [hc.eq, mul_assoc, hEF, mul_one]

/-- The weighted interaction generator has the same norm as the weighted difference between the
product generator and the total generator. -/
theorem physical_interaction_norm (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    ‖weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) lam‖ =
      ‖weighted h.total (generator (stages.map (stageGenerator h)) t-totalGenerator h) lam‖ := by
  change ‖weighted h.total (NormedSpace.exp ((-t) • totalGenerator h) *
    (generator (stages.map (stageGenerator h)) t-totalGenerator h) * NormedSpace.exp (t • totalGenerator h)) lam‖ = _
  rw [physical_total_exp h (-t), physical_total_exp h t, weighted_mul, weighted_mul,
    physical_weighted_exact, physical_weighted_exact]
  rw [CStarRing.norm_mul_mem_unitary _ (evolve_unitary _ h.total_hermitian t),
    CStarRing.norm_mem_unitary_mul _ (evolve_unitary _ h.total_hermitian (-t))]

/-- The weighted relative product word has the same norm as the weighted approximate product
word. -/
theorem physical_relative_norm (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    ‖weighted h.total (relative h stages t) lam‖=‖weighted h.total (approximate h stages t) lam‖ := by
  have he : relative h stages t=evolve h.total (-t)*approximate h stages t := by
    change NormedSpace.exp ((-t) • totalGenerator h)*word _ t=_
    rw [physical_total_exp]
    rfl
  rw [he, weighted_mul, physical_weighted_exact]
  exact CStarRing.norm_mem_unitary_mul _ (evolve_unitary _ h.total_hermitian (-t))

/-- The derivative of the weighted relative word is the product of the weighted interaction
generator and the weighted relative word. See [HejaziZiniArrazola2024]. -/
theorem physical_weighted_derivative (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    HasDerivAt (fun s => weighted h.total (relative h stages s) lam)
      (weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) lam *
        weighted h.total (relative h stages t) lam) t := by
  have hd := ((interaction_hasDerivAt (totalGenerator h) (stages.map (stageGenerator h)) t).const_mul
    (NormedSpace.exp ((lam : ℂ) • h.total))).mul_const (NormedSpace.exp ((-lam : ℂ) • h.total))
  have heq : weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t * relative h stages t) lam =
      weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) lam *
        weighted h.total (relative h stages t) lam := weighted_mul _ _ _ _
  change HasDerivAt _ (weighted h.total
    (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t * relative h stages t) lam) t at hd
  rw [heq] at hd
  exact hd
end Qatlib.Papers.LowEnergyProd24.CenterTransport
