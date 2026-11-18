/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PolynomialFamily
public import Qatlib.Papers.KnottedLight08.HelicitySpec.Balance

/-!
# Phase-invariant modal helicity and conditional charge conservation

[Kedia2013TyingKnots], conserved quantities after equation (6),
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
Finite complex mode data with fixed real weights define quadratic charges.
Independent unit phase rotations preserve these charges, including the common
1/(p+q) normalization. This finite model is a useful conservation-law interface;
it does not identify those mode weights with spatial integrals of the Bateman
fields or evaluate the energy-normalized Hopfion helicity. The analytic balance
law interface is `Qatlib.Papers.KnottedLight08.HelicitySpec.equal_helicities_propagate`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.Charges

open scoped BigOperators

/-- A finite quadratic modal charge with the torus-family helicity normalization. -/
noncomputable def modalCharge {ι : Type*} [Fintype ι]
    (p q : ℕ) (weight : ι → ℝ) (amplitude : ι → ℂ) : ℝ :=
  (∑ i, weight i * Complex.normSq (amplitude i)) / ((p : ℝ) + (q : ℝ))

/-- Independent unit phase rotations conserve the full weighted quadratic charge. -/
theorem modal_charge_phase_invariant {ι : Type*} [Fintype ι]
    (p q : ℕ) (weight : ι → ℝ) (amplitude phase : ι → ℂ)
    (hphase : ∀ i, Complex.normSq (phase i) = 1) :
    modalCharge p q weight (fun i => phase i * amplitude i) =
      modalCharge p q weight amplitude := by
  simp [modalCharge, Complex.normSq_mul, hphase]

/-- A time-dependent unit phase action therefore has the same charge at every time. -/
theorem modal_charge_conserved {ι : Type*} [Fintype ι]
    (p q : ℕ) (weight : ι → ℝ) (amplitude : ι → ℂ) (phase : ℝ → ι → ℂ)
    (hphase : ∀ t i, Complex.normSq (phase t i) = 1) (s t : ℝ) :
    modalCharge p q weight (fun i => phase s i * amplitude i) =
      modalCharge p q weight (fun i => phase t i * amplitude i) := by
  rw [modal_charge_phase_invariant p q weight amplitude (phase s) (hphase s),
    modal_charge_phase_invariant p q weight amplitude (phase t) (hphase t)]

/-- Squared-amplitude rescaling gives the exact quadratic scaling of helicity charges. -/
theorem modal_charge_scaling {ι : Type*} [Fintype ι]
    (p q : ℕ) (weight : ι → ℝ) (amplitude : ι → ℂ) (scale : ℂ) :
    modalCharge p q weight (fun i => scale * amplitude i) =
      Complex.normSq scale * modalCharge p q weight amplitude := by
  unfold modalCharge
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_mul]
  ring

end Qatlib.Papers.KnotLight13.Charges
