/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureStat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Error estimates for left-grid source quadrature

A Banach-space left-grid estimate and Lipschitz bounds for the propagated source establish
`inhomogeneousSourceQuadrature`. The module also controls the sampled source mass by its
integral and an explicit derivative-dependent slack. See [AnLiuLin2023] for the mathematical
setting.

## Main statements

* `inh_left_grid_error`: For a continuous Banach-space-valued function with Lipschitz constant
  `C` on `[s, t]`, the left-grid integration error is at most `(t - s) * inhStep Mt s t * C / 2`
  when `Mt > 0`.
* `inhomogeneousSourceQuadrature`: The left-grid source approximation has error bounded by the
  sum of the time-discretization term and the static LCHS tail and grid terms under the stated
  regularity hypotheses.
* `inh_source_mass_quadrature`: The left-grid sum of source norms is at most their integral plus
  `β * (t - s)^2 / (2 * Mt)` when the source derivative has Euclidean norm at most `β`.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.LchsSimulation.WindowLchs
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- The uniform step size is nonnegative when `s ≤ t`. -/
theorem inh_step_nonneg (Mt : ℕ) (s t : ℝ) (hst : s ≤ t) :
    0 ≤ inhStep Mt s t := div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg _)

/-- Every left-grid node belongs to the closed interval from `s` to `t` when `s ≤ t`. -/
theorem inh_node_mem (Mt : ℕ) (s t : ℝ) (hst : s ≤ t) (l : Fin Mt) :
    inhNode Mt s t l ∈ Set.Icc s t := by
  have hm : 0 < (Mt : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt l.isLt)
  have hl : (l : ℝ) ≤ Mt := by exact_mod_cast l.isLt.le
  have hh := inh_step_nonneg Mt s t hst
  have he : (Mt : ℝ) * inhStep Mt s t = t-s := by
    dsimp [inhStep]; field_simp
  constructor
  · dsimp [inhNode]; linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ l) hh]
  · have := mul_le_mul_of_nonneg_right hl hh
    dsimp [inhNode]; linarith

/-- For a continuous Banach-space-valued function with Lipschitz constant `C` on `[s, t]`, the
left-grid integration error is at most `(t - s) * inhStep Mt s t * C / 2` when `Mt > 0`. -/
theorem inh_left_grid_error {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℝ → E) (hF : Continuous F) (s t C : ℝ) (Mt : ℕ)
    (hst : s ≤ t) (hm : 0 < Mt)
    (hLip : ∀ a ∈ Set.Icc s t, ∀ b ∈ Set.Icc s t, ‖F a-F b‖ ≤ C*|a-b|) :
    ‖(∑ l : Fin Mt, inhStep Mt s t • F (inhNode Mt s t l)) -
        ∫ u in s..t, F u‖ ≤ (t-s)*inhStep Mt s t*C/2 := by
  let h := inhStep Mt s t
  let x := fun j : ℕ => s+(j : ℝ)*h
  have hmR : (0 : ℝ) < Mt := by exact_mod_cast hm
  have hh : 0 ≤ h := inh_step_nonneg Mt s t hst
  have hstep (j : ℕ) : x (j+1)-x j = h := by dsimp [x]; push_cast; ring
  have horder (j : ℕ) : x j ≤ x (j+1) := by linarith [hstep j]
  have hx0 : x 0 = s := by simp [x]
  have hxN : x Mt = t := by dsimp [x, h, inhStep]; field_simp; ring
  have hxmem (j : ℕ) (hj : j ≤ Mt) : x j ∈ Set.Icc s t := by
    have hjR : (j : ℝ) ≤ Mt := by exact_mod_cast hj
    constructor
    · dsimp [x]; linarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hh]
    · have := mul_le_mul_of_nonneg_right hjR hh
      have he : (Mt : ℝ)*h = t-s := by dsimp [h, inhStep]; field_simp
      dsimp [x]; linarith
  let D := fun j : ℕ => ∫ u in x j..x (j+1), F (x j)-F u
  have hcell (j : ℕ) (hj : j < Mt) : ‖D j‖ ≤ C*h^2/2 := by
    have ha := hxmem j hj.le
    have hb := hxmem (j+1) (by omega)
    have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (horder j)
      (f := fun u => F (x j)-F u) (g := fun u => C*(u-x j))
      (Filter.Eventually.of_forall (fun u hu => by
        have hu' : u ∈ Set.Icc s t := ⟨ha.1.trans hu.1.le, hu.2.trans hb.2⟩
        have hl := hLip (x j) ha u hu'
        rwa [abs_of_nonpos (by linarith [hu.1]), neg_sub] at hl))
      ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
    change ‖D j‖ ≤ _ at hi
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ : ℝ => x j)
        ((continuous_id : Continuous (fun u : ℝ => u)).intervalIntegrable _ _) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, smul_eq_mul] at hi
    convert! hi using 1
    have heq : x (j+1) = x j+h := by linarith [hstep j]
    rw [heq]; ring
  have he : (∑ l : Fin Mt, h • F (inhNode Mt s t l)) - ∫ u in s..t, F u =
      ∑ j ∈ Finset.range Mt, D j := by
    have hd (j : ℕ) : D j = h • F (x j) - ∫ u in x j..x (j+1), F u := by
      dsimp [D]
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hF.intervalIntegrable _ _),
        intervalIntegral.integral_const, hstep]
    simp_rw [hd]
    rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => hF.intervalIntegrable _ _), hx0, hxN]
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range Mt, ‖D j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range Mt, C*h^2/2 :=
      Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
    _ = (t-s)*h*C/2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have he' : (Mt : ℝ)*h = t-s := by dsimp [h, inhStep]; field_simp
      rw [← he']; ring

/-- The prescribed window cutoff and node count are positive, have grid spacing at most `1 / 2`,
and bound the combined tail and grid budget by `ε` when `T ≤ Λ`. -/
theorem inh_schedule_raw_bound (ε Λ T : ℝ) (hε : 0 < ε) (hΛ : T ≤ Λ) :
    let K := timeDependentLchsWindowCutoff ε
    let N := timeDependentLchsWindowNodes ε Λ
    0 < K ∧ 0 < N ∧ 2*(K : ℝ)/(N : ℝ) ≤ 1/2 ∧
      2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/N)*T ≤ ε := by
  (try dsimp only)
  let K := timeDependentLchsWindowCutoff ε
  let N := timeDependentLchsWindowNodes ε Λ
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcut : 4/(Real.pi*ε) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (4/(Real.pi*ε)))))
  have hnodes : max (4*(K : ℝ)) (4*(K : ℝ)*Λ/ε) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by
      have hnceil : Nat.ceil (max (4*(K : ℝ)) (4*(K : ℝ)*Λ/ε)) ≤ N := le_max_right _ _
      exact_mod_cast hnceil)
  have hmesh : 2*(K : ℝ)/(N : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hNr).mpr
    have := (le_max_left _ _).trans hnodes
    linarith
  have htail : 2/(Real.pi*(K : ℝ)) ≤ ε/2 := by
    apply (div_le_iff₀ (mul_pos Real.pi_pos hKr)).mpr
    have := (div_le_iff₀ (mul_pos Real.pi_pos hε)).mp hcut
    nlinarith
  have hcell : (2*(K : ℝ)/(N : ℝ))*Λ ≤ ε/2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hNr).mpr
    have := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hnodes)
    nlinarith
  refine ⟨hK, hN, hmesh, ?_⟩
  have := mul_le_mul_of_nonneg_left hΛ (by positivity : 0 ≤ 2*(K : ℝ)/(N : ℝ))
  linarith

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The continuous real-linear map sending a coordinate state to its Euclidean-space
representation. -/
private def inhEuclideanMap : QState I →L[ℝ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℂ)).symm.toContinuousLinearMap

omit [DecidableEq I] in

/-- The derivative of a matrix-vector product is the sum of the matrix derivative acting on the
vector and the matrix acting on the vector derivative. -/
private theorem inh_mulVec_deriv {M : ℝ → Matrix I I ℂ} {v : ℝ → QState I}
    {M' : Matrix I I ℂ} {v' : QState I} {u : ℝ}
    (hM : HasDerivAt M M' u) (hv : HasDerivAt v v' u) :
    HasDerivAt (fun z => M z *ᵥ v z) (M' *ᵥ v u+M u *ᵥ v') u := by
  apply hasDerivAt_pi.mpr
  intro i
  have hm (j : I) := hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) j
  have hvj (j : I) := hasDerivAt_pi.mp hv j
  simpa [Matrix.mulVec, dotProduct, Finset.sum_add_distrib] using!
    HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hm j).mul (hvj j))

omit [DecidableEq I] in

/-- A bound `β` on the Euclidean norm of the source derivative gives the Lipschitz estimate `β *
|a - z|` on `[s, t]`. -/
private theorem inh_derivative_lipschitz (b b' : ℝ → QState I) (s t β : ℝ)
    (hd : ∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u)
    (hn : ∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) :
    ∀ a ∈ Set.Icc s t, ∀ z ∈ Set.Icc s t,
      ‖toEuclidean_fromVec (b a)-toEuclidean_fromVec (b z)‖ ≤ β*|a-z| := by
  have he (u : ℝ) (hu : u ∈ Set.Icc s t) :
      HasDerivAt (fun z => toEuclidean_fromVec (b z)) (toEuclidean_fromVec (b' u)) u :=
    (inhEuclideanMap (I := I)).hasFDerivAt.comp_hasDerivAt u (hd u hu.1 hu.2)
  intro a ha z hz
  have hl := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (he u hu).differentiableAt)
    (fun u hu => by rw [(he u hu).deriv]; exact hn u hu.1 hu.2)
    (convex_Icc s t) hz ha
  simpa only [Real.norm_eq_abs] using! hl

/-- The propagated source on `[s, t]` satisfies a Lipschitz bound with constant `(lamL + lamH) *
bmax + β` under the stated continuity, positivity, and norm bounds. -/
private theorem inh_source_lipschitz (L H : ℝ → Matrix I I ℂ) (b b' : ℝ → QState I)
    (s t β lamL lamH bmax : ℝ) (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hd : ∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u)
    (hβ : ∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β)
    (hbmax : ∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b u)‖ ≤ bmax)
    (hlL : ∀ u, ‖L u‖ ≤ lamL) (hlH : ∀ u, ‖H u‖ ≤ lamH) :
    ∀ a ∈ Set.Icc s t, ∀ z ∈ Set.Icc s t,
      ‖toEuclidean_fromVec (orderedEvolution (fun y => L y+Complex.I • H y) a t *ᵥ b a)-
        toEuclidean_fromVec (orderedEvolution (fun y => L y+Complex.I • H y) z t *ᵥ b z)‖ ≤
      ((lamL+lamH)*bmax+β)*|a-z| := by
  let A := fun u => L u+Complex.I • H u
  have hA : Continuous A := by dsimp [A]; fun_prop
  let v := fun u => orderedEvolution A u t *ᵥ b u
  let v' := fun u => (orderedEvolution A u t*A u) *ᵥ b u+
    orderedEvolution A u t *ᵥ b' u
  have hdv (u : ℝ) (hus : s ≤ u) (hut : u ≤ t) : HasDerivAt v (v' u) u :=
    inh_mulVec_deriv (orderedEvolution_hasDerivAt_start A hA t u) (hd u hus hut)
  have hnv (u : ℝ) (hus : s ≤ u) (hut : u ≤ t) :
      ‖toEuclidean_fromVec (v' u)‖ ≤ (lamL+lamH)*bmax+β := by
    have hE : ‖orderedEvolution A u t‖ ≤ 1 := by
      simpa only [one_smul] using!
        (time_dependent_lchs_entire_parameter I L H u t hL hH hPSD hHerm hut).2 1 (by simp)
    have hAu : ‖A u‖ ≤ lamL+lamH := by
      calc
        _ ≤ ‖L u‖+‖Complex.I • H u‖ := norm_add_le _ _
        _ = ‖L u‖+‖H u‖ := by rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ _ := add_le_add (hlL u) (hlH u)
    have hLH : 0 ≤ lamL+lamH := (norm_nonneg _).trans hAu
    have hb0 : 0 ≤ bmax := (norm_nonneg _).trans (hbmax u hus hut)
    change ‖toEuclidean_fromVec (_+_)‖ ≤ _
    simp only [toEuclidean_fromVec, WithLp.toLp_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have he := (norm_mul_le (orderedEvolution A u t) (A u)).trans
        ((mul_le_mul hE hAu (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
      exact (l2_norm_mulVec_fromVec_le _ _).trans
        (mul_le_mul he (hbmax u hus hut) (norm_nonneg _) hLH)
    · exact (l2_norm_mulVec_fromVec_le _ _).trans
        ((mul_le_mul hE (hβ u hus hut) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  exact inh_derivative_lipschitz v v' s t _ hdv hnv

/-- The left-grid source approximation has error bounded by the sum of the time-discretization
term and the static LCHS tail and grid terms under the stated regularity hypotheses. See
[AnLiuLin2023]. -/
theorem inhomogeneousSourceQuadrature : InhomogeneousSourceQuadrature := by
  intro I _ _ L H b b' s t K N Mt β lamL lamH bmax hL hH hb hPSD hHerm hst
    hK hN hMt hd hβ hbmax hlL hlH
  let A := fun u => L u+Complex.I • H u
  let F := fun u => toEuclidean_fromVec (orderedEvolution A u t *ᵥ b u)
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hE : Continuous (fun u => orderedEvolution A u t) :=
    continuous_iff_continuousAt.mpr (fun u => (orderedEvolution_hasDerivAt_start A hA t u).continuousAt)
  have hF : Continuous F := inhEuclideanMap.continuous.comp (hE.matrix_mulVec hb)
  have hleft := inh_left_grid_error F hF s t ((lamL+lamH)*bmax+β) Mt hst hMt
    (inh_source_lipschitz L H b b' s t β lamL lamH bmax hL hH hPSD hHerm hd hβ hbmax hlL hlH)
  let η := 2/(Real.pi*(K : ℝ))+(2*(K : ℝ)/N)*(2/Real.pi+∫ u in s..t, ‖L u‖)
  have hη : 0 ≤ η := by
    have hi : 0 ≤ ∫ u in s..t, ‖L u‖ :=
        intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
    dsimp [η]; positivity
  have hb0 : 0 ≤ bmax := (norm_nonneg _).trans (hbmax s le_rfl hst)
  have hnode (l : Fin Mt) :
      ‖toEuclidean_fromVec
        (((∑ j : Fin N, staticLchsCoeff K N j • inhSourceKUnitary L H s t K N Mt j l) *ᵥ
          b (inhNode Mt s t l))-orderedEvolution A (inhNode Mt s t l) t *ᵥ
            b (inhNode Mt s t l))‖ ≤ η*bmax := by
    have hl := inh_node_mem Mt s t hst l
    have hi := intervalIntegral.integral_mono_interval (μ := volume) (f := fun u => ‖L u‖)
      hl.1 hl.2 le_rfl
      (Filter.Eventually.of_forall (fun u => norm_nonneg (L u))) (hL.norm.intervalIntegrable s t)
    have hq := time_dependent_lchs_quadrature_error I L H (inhNode Mt s t l) t K N
      hL hH hPSD hHerm hl.2 hK hN
    have hq' : ‖(∑ j : Fin N, staticLchsCoeff K N j • inhSourceKUnitary L H s t K N Mt j l)-
        orderedEvolution A (inhNode Mt s t l) t‖ ≤ η :=
      hq.trans (by dsimp [η]; gcongr)
    have hm := l2_norm_mulVec_fromVec_le
      ((∑ j : Fin N, staticLchsCoeff K N j • inhSourceKUnitary L H s t K N Mt j l)-
        orderedEvolution A (inhNode Mt s t l) t) (b (inhNode Mt s t l))
    rw [Matrix.sub_mulVec] at hm
    exact hm.trans (mul_le_mul hq' (hbmax _ hl.1 hl.2) (norm_nonneg _) hη)
  have hk : ‖toEuclidean_fromVec (inhSourceSum L H b s t K N Mt)-
      ∑ l : Fin Mt, inhStep Mt s t • F (inhNode Mt s t l)‖ ≤ (t-s)*bmax*η := by
    change ‖inhEuclideanMap (∑ l : Fin Mt, (inhStep Mt s t : ℂ) • _)-
      ∑ l : Fin Mt, inhStep Mt s t • F (inhNode Mt s t l)‖ ≤ _
    simp only [map_sum, Complex.coe_smul, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum
      (g := fun _ => inhStep Mt s t*(η*bmax)) (fun l _ => ?_)).trans_eq ?_)
    · rw [norm_smul, Real.norm_of_nonneg (inh_step_nonneg Mt s t hst)]
      exact mul_le_mul_of_nonneg_left (hnode l) (inh_step_nonneg Mt s t hst)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have he : (Mt : ℝ)*inhStep Mt s t = t-s := by
        have : (Mt : ℝ) ≠ 0 := by exact_mod_cast hMt.ne'
        dsimp [inhStep]; field_simp
      rw [← he]; ring
  have hint : (∫ u in s..t, F u) = toEuclidean_fromVec (inhSourceResponse L H b s t) :=
    inhEuclideanMap.intervalIntegral_comp_comm ((hE.matrix_mulVec hb).intervalIntegrable s t)
  rw [hint] at hleft
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (toEuclidean_fromVec (inhSourceSum L H b s t K N Mt))
    (∑ l : Fin Mt, inhStep Mt s t • F (inhNode Mt s t l))
    (toEuclidean_fromVec (inhSourceResponse L H b s t))
  change ‖toEuclidean_fromVec (inhSourceSum L H b s t K N Mt)-
    toEuclidean_fromVec (inhSourceResponse L H b s t)‖ ≤ _
  exact ht.trans ((add_le_add hk hleft).trans_eq (by dsimp [η]; ring))

omit [DecidableEq I] in

/-- The left-grid sum of source norms is at most their integral plus `β * (t - s)^2 / (2 * Mt)`
when the source derivative has Euclidean norm at most `β`. -/
theorem inh_source_mass_quadrature (b b' : ℝ → QState I) (s t β : ℝ) (Mt : ℕ)
    (hb : Continuous b) (hst : s ≤ t) (hMt : 0 < Mt)
    (hd : ∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u)
    (hβ : ∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) :
    (∑ l : Fin Mt, inhStep Mt s t*‖toEuclidean_fromVec (b (inhNode Mt s t l))‖) ≤
      (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖)+β*(t-s)^2/(2*(Mt : ℝ)) := by
  have hc : Continuous (fun u => ‖toEuclidean_fromVec (b u)‖) :=
    (inhEuclideanMap.continuous.comp hb).norm
  have hlip := inh_derivative_lipschitz b b' s t β hd hβ
  have he := inh_left_grid_error (fun u => ‖toEuclidean_fromVec (b u)‖) hc s t β Mt hst hMt
    (fun a ha z hz => by
      rw [Real.norm_eq_abs]
      exact (abs_norm_sub_norm_le _ _).trans (hlip a ha z hz))
  simp only [smul_eq_mul, Real.norm_eq_abs] at he
  have hraw := (le_abs_self _).trans he
  have hMr : (Mt : ℝ) ≠ 0 := by exact_mod_cast hMt.ne'
  have heq : (t-s)*inhStep Mt s t*β/2 = β*(t-s)^2/(2*(Mt : ℝ)) := by
    dsimp [inhStep]; field_simp
  rw [heq] at hraw
  linarith

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
