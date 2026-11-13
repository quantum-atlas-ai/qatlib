/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualBias
import Qatlib.Papers.AmpInvReqTang26.ForwardHist.TwistedCircuit

/-!
# Bounds for phase-twisted ensemble discrimination

The unbiased average circuit density is invariant under a fixed diagonal phase twist. Combining
this invariance with biased density comparisons bounds `twistedWeightedSuccess` and yields a
forward-query lower bound. This development supports the treatment in [TangWright2025].

## Main statements

* `twisted_unbiased_density`: invariance of the unbiased density.
* `actual_twisted_weighted_born_bound`: success is at most `1/2 + 4 * n * eps^2`.
* `actual_twisted_weighted_lower_bound`: success at least `5/6` requires `n ≥ 1/(12 * eps^2)`.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination

/-- At zero bias, the weighted circuit density equals the uniform phase circuit density. -/
theorem weightedCircuitDensity_zero {d a : ℕ} (q : ℕ) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    weightedCircuitDensity 0 q Alg n=circuitDensity (q := q) Alg n (fun u i => phase q (u i)) := by
  have hw (u : Fin d → Fin q) : (phaseWeight 0 q u:ℂ)=(Fintype.card (Fin d → Fin q):ℂ)⁻¹ := by
    simp [phaseWeight,muEpsWeight]
  ext x y
  simp only [weightedCircuitDensity,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
    Pi.star_apply,smul_eq_mul,circuitDensity,Finset.mul_sum,hw]
  apply Finset.sum_congr rfl
  intro u _
  rw [run_assignment (phase q) Alg n u]

/-- For positive `q` and `n < q`, a fixed unit-modulus diagonal twist of the algorithm leaves
the unbiased weighted density unchanged. -/
theorem twisted_unbiased_density {d a q : ℕ} (hq : 0<q) (D : Fin d → ℂ)
    (hD : ∀i,‖D i‖=1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q) :
    weightedCircuitDensity 0 q (twistedAlgorithm D hD Alg) n=weightedCircuitDensity 0 q Alg n := by
  rw [weightedCircuitDensity_zero,weightedCircuitDensity_zero]
  have ht : circuitDensity (q := q) (twistedAlgorithm D hD Alg) n (fun u i => phase q (u i))=
      circuitDensity (q := q) Alg n (fun u i => D i*phase q (u i)) := by
    ext x y
    simp only [circuitDensity,twistedAlgorithm_run,id_eq]
  rw [ht]
  exact actual_circuit_density_twist hq Alg n hn D hD

/-- The average of the false-outcome mass for the biased circuit and the true-outcome mass for
its phase-twisted algorithm. -/
def twistedWeightedSuccess {d a : ℕ} (eps : ℝ) (q : ℕ) (D : Fin d → ℂ)
    (hD : ∀i,‖D i‖=1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : ℝ :=
  (bornMass (weightedCircuitDensity eps q Alg n) Alg.good false +
    bornMass (weightedCircuitDensity eps q (twistedAlgorithm D hD Alg) n) Alg.good true)/2

/-- For `0 < eps < 1/2`, `q > 1`, and `n < q`, the twisted weighted success is at most `1/2 + 4
* n * eps^2`. -/
theorem actual_twisted_weighted_born_bound {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0<eps) (he1 : eps<1/2) (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q) :
    twistedWeightedSuccess eps q D hD Alg n≤1/2+4*(n:ℝ)*eps^2 := by
  let rho := weightedCircuitDensity 0 q Alg n
  let sigma := weightedCircuitDensity eps q Alg n
  let tau := weightedCircuitDensity eps q (twistedAlgorithm D hD Alg) n
  let delta := 4*(n:ℝ)*eps^2
  have hrho := weightedCircuitDensity_posSemidef 0 q hq (by norm_num) (by norm_num) Alg n
  have htrho := weightedCircuitDensity_trace 0 q (by omega) (by norm_num) (by norm_num) Alg n
  have htrtau := weightedCircuitDensity_trace eps q (by omega) he0.le (by linarith)
    (twistedAlgorithm D hD Alg) n
  have hdomS := actual_weighted_domination eps q hq he0 he1 Alg n hn
  have hdomT := actual_weighted_domination eps q hq he0 he1 (twistedAlgorithm D hD Alg) n hn
  rw [twisted_unbiased_density (by omega) D hD Alg n hn] at hdomT
  have hupper :=
      density_domination_born_bias rho tau hrho htrho htrtau delta
      (by dsimp [delta]; positivity) hdomT Alg.good
  have hlower :=
      density_domination_born_bias_lower rho sigma hrho htrho delta
      (by dsimp [delta]; positivity) hdomS Alg.good
  have htotal := bornMass_total sigma Alg.good
  have htrs := weightedCircuitDensity_trace eps q (by omega) he0.le (by linarith) Alg n
  change Matrix.trace sigma=1 at htrs
  rw [htrs,Complex.one_re] at htotal
  change (bornMass sigma Alg.good false+bornMass tau Alg.good true)/2≤1/2+delta
  nlinarith

/-- When `0 < eps < 1/2` and `q ≥ 1/eps^2`, twisted weighted success at least `5/6` requires `n
≥ 1/(12 * eps^2)`. -/
theorem actual_twisted_weighted_lower_bound {d a q : ℕ} (eps : ℝ) (he0 : 0<eps)
    (he1 : eps<1/2) (hq : 1/eps^2≤(q:ℝ)) (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (hsucc : (5/6:ℝ)≤twistedWeightedSuccess eps q D hD Alg n) : 1/(12*eps^2)≤(n:ℝ) := by
  have he2 : 0<eps^2 := sq_pos_of_pos he0
  have hqp : 1≤(q:ℝ)*eps^2 := (div_le_iff₀ he2).mp hq
  have hq2 : 1<q := by
    by_contra h
    have hqn : q≤1 := by omega
    have hqr : (q:ℝ)≤1 := by exact_mod_cast hqn
    nlinarith
  by_cases hn : n<q
  · have hb := actual_twisted_weighted_born_bound eps q hq2 he0 he1 D hD Alg n hn
    apply (div_le_iff₀ (by positivity : 0<12*eps^2)).mpr
    nlinarith
  · have hqn : (q:ℝ)≤n := by exact_mod_cast (by omega : q≤n)
    have hh : 1/(12*eps^2)≤1/eps^2 := by
      apply div_le_div_of_nonneg_left (by norm_num) he2
      nlinarith
    exact hh.trans (hq.trans hqn)

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
