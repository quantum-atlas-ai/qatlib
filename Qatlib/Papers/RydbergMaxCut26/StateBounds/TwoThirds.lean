/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.StateBounds.IsingGround

/-!
# A conditional two-thirds energy guarantee

Scalar certificates combine the secondary-state QMC bound with the ideal X product-state bound
using weights one third and two thirds. For nonnegative edge weights and a secondary ground
density, the better of these two states has QMC energy at most two thirds of the QMC ground
energy. See [CrostaSaubanereHuber2026].

## Main statements

* `actual_two_candidates_optimum`: bounds the better candidate by two thirds of
  `qmcGroundEnergy`.
* `source_nonconstructive_two_thirds`: provides an Ising product ground state with the required
  correlations and QMC energy bounds.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.StateBounds.XBasis
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Ising

namespace Qatlib.Papers.RydbergMaxCut26.StateBounds.TwoThirds

/-- The convex combination of `t` and `-(1 - t) / 4` with weights one third and two thirds
equals two thirds of `-(1 - 3 * t) / 4`. -/
theorem one_third_identity (t : ℝ) :
    (1/3:ℝ)*t+(2/3:ℝ)*(-(1/4:ℝ)*(1-t))=(2/3:ℝ)*(-(1/4:ℝ)*(1-3*t)) := by ring

/-- For nonpositive `t`, the convex combination of the clipped secondary term and ideal product
term equals two thirds of the clipped lower-bound term. -/
theorem negative_certificate_exact (t : ℝ) (ht : t≤0) :
    (1/3:ℝ)*min t 0+(2/3:ℝ)*(-(1/4:ℝ)*(1-t))=
      (2/3:ℝ)*(-(1/4:ℝ)*max (1-3*t) 0) := by
  rw [min_eq_left ht,max_eq_left (by linarith)]
  exact one_third_identity t

/-- For `t ≤ 1`, the convex combination with weights one third and two thirds is at most two
thirds of `-max (1 - 3 * t) 0 / 4`. -/
theorem pointwise_two_thirds (t : ℝ) (ht : t≤1) :
    (1/3:ℝ)*min t 0+(2/3:ℝ)*(-(1/4:ℝ)*(1-t))≤
      (2/3:ℝ)*(-(1/4:ℝ)*max (1-3*t) 0) := by
  by_cases hn : t≤0
  · exact (negative_certificate_exact t hn).le
  · have hp : 0≤t := le_of_lt (lt_of_not_ge hn)
    rw [min_eq_right hp]
    by_cases hg : 0≤1-3*t
    · rw [max_eq_left hg]
      linarith
    · rw [max_eq_right (le_of_not_ge hg)]
      linarith

/-- For nonnegative weights and edge parameters at most one, summing the pointwise two-thirds
certificate gives the corresponding weighted energy inequality. -/
theorem weighted_two_thirds {E : Type*} [Fintype E] (w t : E → ℝ)
    (hw : ∀ e,0≤w e) (ht : ∀ e,t e≤1) :
    (1/3:ℝ)*(∑ e,w e*min (t e) 0)+(2/3:ℝ)*(-(1/4:ℝ)*(∑ e,w e*(1-t e)))≤
      (2/3:ℝ)*(-(1/4:ℝ)*(∑ e,w e*max (1-3*t e) 0)) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun e _ =>
    mul_le_mul_of_nonneg_left (pointwise_two_thirds (t e) (ht e)) (hw e))
  have hL (e : E) : w e*((1/3:ℝ)*min (t e) 0+(2/3:ℝ)*(-(1/4:ℝ)*(1-t e)))=
      (1/3:ℝ)*(w e*min (t e) 0)+((2/3:ℝ)*(-(1/4:ℝ)))*(w e*(1-t e)) := by ring
  have hR (e : E) : w e*((2/3:ℝ)*(-(1/4:ℝ)*max (1-3*t e) 0))=
      ((2/3:ℝ)*(-(1/4:ℝ)))*(w e*max (1-3*t e) 0) := by ring
  simp_rw [hL,hR] at h
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum] at h
  linarith

/-- For nonnegative edge weights, distinct endpoints, and a secondary ground density, the
clipped edge expression `-1/4 * ∑ e, w e * max (1 - 3 * tParam ρR i j) 0` bounds below the
QMC energy of every physical density. -/
theorem actual_clipped_ground_lower {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    -(1/4:ℝ)*(∑ e,w e*max (1-3*tParam ρR (ends e).1 (ends e).2) 0)≤
      energy (qmcHamiltonian ends w) ρ := by
  have h := ground_lower_edges ends hends w ρR hR ρ hρ htr
  have hs : (∑ e,w e*(1-3*tParam ρR (ends e).1 (ends e).2))≤
      ∑ e,w e*max (1-3*tParam ρR (ends e).1 (ends e).2) 0 :=
    Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hw e))
  linarith

/-- The minimum of two real numbers is at most their convex combination with weights one third
and two thirds. -/
theorem min_le_convex_third (x y : ℝ) : min x y≤(1/3:ℝ)*x+(2/3:ℝ)*y := by
  have hx := min_le_left x y
  have hy := min_le_right x y
  linarith

/-- For nonnegative edge weights and a secondary ground density, the minimum of its QMC energy
and the ideal product surrogate is at most two thirds of the QMC energy of any physical
comparison state. -/
theorem actual_source_surrogate_bound {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    min (energy (qmcHamiltonian ends w) ρR)
      (-(1/4:ℝ)*(∑ e,w e*(1-tParam ρR (ends e).1 (ends e).2)))≤
        (2/3:ℝ)*energy (qmcHamiltonian ends w) ρ := by
  have hRup := qmc_energy_upper ends hends w hw ρR hR.1 hR.2.1
  have ht : ∀ e,tParam ρR (ends e).1 (ends e).2≤1 :=
    fun e => (global_t_range ρR hR.1 hR.2.1 _ _ (hends e)).2
  have hcert := weighted_two_thirds w (fun e => tParam ρR (ends e).1 (ends e).2) hw ht
  have hlow := actual_clipped_ground_lower ends hends w hw ρR hR ρ hρ htr
  refine (min_le_convex_third _ _).trans ?_
  linarith

/-- For nonnegative edge weights and a secondary ground density, the smaller QMC energy of that
state and the minimizing X product state is at most two thirds of the QMC energy of any
physical comparison state. -/
theorem actual_two_candidates {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    min (energy (qmcHamiltonian ends w) ρR)
      (energy (qmcHamiltonian ends w) (xDensity (minSpin ends w)))≤
        (2/3:ℝ)*energy (qmcHamiltonian ends w) ρ :=
  (min_le_min le_rfl (actual_ideal_product_upper ends hends w ρR hR.1 hR.2.1)).trans
    (actual_source_surrogate_bound ends hends w hw ρR hR ρ hρ htr)

/-- The infimum of QMC energies over positive semidefinite, trace-one density matrices. -/
def qmcGroundEnergy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ ρ : Matrix (Reg n) (Reg n) ℂ,
    ρ.PosSemidef ∧ ρ.trace=1 ∧ energy (qmcHamiltonian ends w) ρ=e}

/-- For nonnegative edge weights and a secondary ground density, the better of that state and
the minimizing X product state has QMC energy at most two thirds of `qmcGroundEnergy`, as in
[Crosta et al., Observation 6][CrostaSaubanereHuber2026]. -/
theorem actual_two_candidates_optimum {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR) :
    min (energy (qmcHamiltonian ends w) ρR)
      (energy (qmcHamiltonian ends w) (xDensity (minSpin ends w)))≤
        (2/3:ℝ)*qmcGroundEnergy ends w := by
  let m := min (energy (qmcHamiltonian ends w) ρR)
    (energy (qmcHamiltonian ends w) (xDensity (minSpin ends w)))
  have hne : Set.Nonempty {e : ℝ | ∃ ρ : Matrix (Reg n) (Reg n) ℂ,
      ρ.PosSemidef ∧ ρ.trace=1 ∧ energy (qmcHamiltonian ends w) ρ=e} :=
    ⟨energy (qmcHamiltonian ends w) ρR,ρR,hR.1,hR.2.1,rfl⟩
  have hb : (3/2:ℝ)*m≤qmcGroundEnergy ends w := by
    apply le_csInf hne
    rintro e ⟨ρ,hρ,htr,rfl⟩
    have h := actual_two_candidates ends hends w hw ρR hR ρ hρ htr
    change m≤(2/3:ℝ)*energy (qmcHamiltonian ends w) ρ at h
    linarith
  change m≤_
  linarith

/-- If a QMC ground density is given, its energy equals `qmcGroundEnergy`. -/
theorem qmcGroundEnergy_eq_ground {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (ρQ : Matrix (Reg n) (Reg n) ℂ)
    (hQ : GroundDensity (qmcHamiltonian ends w) ρQ) :
    qmcGroundEnergy ends w=energy (qmcHamiltonian ends w) ρQ := by
  let S := {e : ℝ | ∃ ρ : Matrix (Reg n) (Reg n) ℂ,
    ρ.PosSemidef ∧ ρ.trace=1 ∧ energy (qmcHamiltonian ends w) ρ=e}
  have hm : energy (qmcHamiltonian ends w) ρQ∈S := ⟨ρQ,hQ.1,hQ.2.1,rfl⟩
  have hb : BddBelow S := by
    refine ⟨energy (qmcHamiltonian ends w) ρQ,?_⟩
    rintro e ⟨ρ,hρ,htr,rfl⟩
    exact hQ.2.2 ρ hρ htr
  apply le_antisymm (csInf_le hb hm)
  apply le_csInf ⟨_,hm⟩
  rintro e ⟨ρ,hρ,htr,rfl⟩
  exact hQ.2.2 ρ hρ htr

/-- Given secondary and QMC ground densities on a graph with nonnegative weights and distinct
endpoints, an X product Ising ground density exists with zero YY and ZZ edge correlations
and the ideal product energy bound. The better of this product density and the secondary
ground density has QMC energy at most two thirds of the QMC ground energy, as in [Crosta et
al., Observation 6][CrostaSaubanereHuber2026]. -/
theorem source_nonconstructive_two_thirds {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : GroundDensity (qmcHamiltonian ends w) ρQ) :
    ∃ s : Reg n, GroundDensity (isingHamiltonian ends w) (xDensity s) ∧
      (∀ e,corr (xDensity s) (ends e).1 (ends e).2 1=0 ∧ corr (xDensity s) (ends e).1 (ends e).2 2=0) ∧
      energy (qmcHamiltonian ends w) (xDensity s)≤-(1/4:ℝ)*(∑ e,w e*(1-tParam ρR (ends e).1 (ends e).2)) ∧
      min (energy (qmcHamiltonian ends w) ρR) (energy (qmcHamiltonian ends w) (xDensity s))≤
        (2/3:ℝ)*energy (qmcHamiltonian ends w) ρQ := by
  refine ⟨minSpin ends w,actual_ising_ground ends hends w,?_,?_,?_⟩
  · intro e
    exact (x_correlations _ _ _ (hends e)).2
  · exact actual_ideal_product_upper ends hends w ρR hR.1 hR.2.1
  · exact actual_two_candidates ends hends w hw ρR hR ρQ hQ.1 hQ.2.1

end Qatlib.Papers.RydbergMaxCut26.StateBounds.TwoThirds
