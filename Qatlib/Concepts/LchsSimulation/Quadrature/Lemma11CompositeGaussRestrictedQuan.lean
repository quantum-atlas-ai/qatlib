/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Quadrature.Lemma11CompositeGaussRestrictedStat
import Qatlib.Concepts.LchsSimulation.Quadrature.CompositeGaussAlgebra

/-!
# Restricted composite Gauss bound for LCHS

`lemma11CompositeGaussRestrictedCorrected` assembles cellwise Gauss remainder bounds into a
global cutoff-interval estimate. The statement explicitly assumes derivative-norm witnesses and
the cellwise remainder inequalities, in addition to the kernel and generator hypotheses. See
[AnChildsLin2026] for the mathematical setting.

## Main statements

* `lemma11CompositeGaussRestrictedCorrected`: Assuming the stated cellwise Gauss remainder
  witnesses, the composite LCHS quadrature error obeys the explicit geometric bound under the
  large-parameter condition `32 ≤ exp(1) * T * Λ`. This is a restricted form of [An, Childs, and
  Lin, Lemma 11][AnChildsLin2026].

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.LchsSimulation.Quadrature
open MeasureTheory Set Matrix
open scoped Classical Matrix.Norms.L2Operator

/-- Assuming the stated cellwise Gauss remainder witnesses, the composite LCHS quadrature error
obeys the explicit geometric bound under the large-parameter condition `32 ≤ exp(1) * T *
Λ`. This is a restricted form of [An, Childs, and Lin, Lemma 11][AnChildsLin2026]. -/
theorem lemma11CompositeGaussRestrictedCorrected : Lemma11CompositeGaussRestrictedCorrected := by
  intro I _ _ L H T β Λ K Q M node weight hL hH hHermL hHermH hT hΛ hlarge hβ hβ1 hK hQ hM hbound
  (try dsimp only)
  let h : ℝ := (2*K:ℝ)/M
  let U := fun k : ℝ=>orderedEvolution (fun u=>Complex.I • (H u+k • L u)) 0 T
  let Φ := fun k : ℝ=>highKernelG β k • U k
  let a := fun n : ℕ=>(-K:ℝ)+h*(n:ℝ)
  let nodeAt := fun m : Fin M=>fun q : Fin Q=>(-K:ℝ)+h*((m:ℝ)+(node q+1)/2)
  let cellSum :=
      fun m : Fin M=>∑ q : Fin Q,((h/2)*weight q*highKernelG β (nodeAt m q)) • U (nodeAt m q)
  let J := fun m : Fin M=>∫ k in a m.val..a (m.val+1),Φ k
  let C := 4/(3*highKernelC β)
  let B := Real.exp 1*T*Λ
  have hh : 0<h := by dsimp [h];positivity
  have hC : 0≤C := by dsimp [C];have hc:=highKernelC_pos β;positivity
  have hB : 0≤B := by dsimp [B];positivity
  intro hs
  obtain ⟨σ,heval,hcell⟩ := hs
  have hσ (m : Fin M) : σ m≤C*((2*Q).factorial:ℝ)*(2*Q+1:ℕ)*B^(2*Q) := by
    obtain ⟨x,_hx,hx⟩ := heval m
    rw [← hx]
    exact near_exponential_lchs_integrand_derivative_bound I L H T β Λ hL hH hHermL hHermH hT hΛ hlarge hβ hβ1 hbound (2*Q) (by omega) x
  have hePow : (2:ℝ)*Q+1=((2*Q+1:ℕ):ℝ) := by push_cast;ring
  have hcellBound (m : Fin M) : ‖J m-cellSum m‖≤C*h^(2*Q+1)*(B/2)^(2*Q) := by
    have hc := hcell m
    change ‖(∫ k in (-K:ℝ)+h*(m:ℝ)..(-K:ℝ)+h*((m:ℝ)+1),Φ k)-cellSum m‖≤
      ((Q.factorial:ℝ)^4*h^((2:ℝ)*Q+1))/((2*Q+1:ℕ)*((2*Q).factorial:ℝ)^3)*σ m at hc
    have hJ : J m=(∫ k in (-K:ℝ)+h*(m:ℝ)..(-K:ℝ)+h*((m:ℝ)+1),Φ k) := by
      simp only [J,a,Nat.cast_add,Nat.cast_one]
    rw [hJ]
    apply hc.trans
    rw [hePow,Real.rpow_natCast]
    calc _≤((Q.factorial:ℝ)^4*h^(2*Q+1))/((2*Q+1:ℕ)*((2*Q).factorial:ℝ)^3)*
             (C*((2*Q).factorial:ℝ)*(2*Q+1:ℕ)*B^(2*Q)) :=
               mul_le_mul_of_nonneg_left (hσ m) (by positivity)
         _≤_ := gauss_cell_budget_le Q C h B hC hh.le hB
  have hUc : Continuous U := by
    have hc :=
        (ordered_unitary_complex_parameter_entire I L H hL hH 0 T).continuous.comp Complex.continuous_ofReal
    simpa only [U,Function.comp_def,Complex.coe_smul] using! hc
  have hΦ : Continuous Φ := (highKernelG_continuous β).smul hUc
  have hMh : (M:ℝ)*h=(2:ℝ)*K := by dsimp [h];field_simp
  have haM : a M=(K:ℝ) := by dsimp [a];nlinarith [hMh]
  have hparts : (∑ m : Fin M,J m)=∫ k in (-K:ℝ)..(K:ℝ),Φ k := by
    have hp := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a) (n := M)
      (fun n _=>hΦ.intervalIntegrable (a n) (a (n+1)))
    have hf := Fin.sum_univ_eq_sum_range (fun n : ℕ=>∫ k in a n..a (n+1),Φ k) M
    calc _=∫ k in a 0..a M,Φ k := hf.trans hp
         _=_ := by rw [haM];simp only [a,Nat.cast_zero,mul_zero,add_zero]
  have hsum : ‖(∑ m : Fin M,cellSum m)-(∫ k in (-K:ℝ)..(K:ℝ),Φ k)‖≤
      (8/(3*highKernelC β))*K*h^(2*Q)*(B/2)^(2*Q) := by
    rw [← hparts,← Finset.sum_sub_distrib]
    calc _≤∑ m : Fin M,‖cellSum m-J m‖ := norm_sum_le _ _
         _≤∑ _m : Fin M,C*h^(2*Q+1)*(B/2)^(2*Q) := Finset.sum_le_sum (fun m _=>by rw [norm_sub_rev];exact hcellBound m)
         _=(M:ℝ)*(C*h^(2*Q+1)*(B/2)^(2*Q)) := by simp
         _=C*((M:ℝ)*h)*h^(2*Q)*(B/2)^(2*Q) := by rw [pow_succ];ring
         _=(8/(3*highKernelC β))*K*h^(2*Q)*(B/2)^(2*Q) := by rw [hMh];dsimp [C];ring
  have heNat : (2:ℝ)*Q=((2*Q:ℕ):ℝ) := by push_cast;ring
  change ‖(∑ m : Fin M,cellSum m)-(∫ k in (-K:ℝ)..(K:ℝ),Φ k)‖≤
    (8/(3*highKernelC β))*K*h^((2:ℝ)*Q)*(B/2)^((2:ℝ)*Q)
  rw [heNat,Real.rpow_natCast,Real.rpow_natCast]
  exact hsum
end Qatlib.Concepts.LchsSimulation.Quadrature
