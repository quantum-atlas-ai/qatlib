/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.DiagonalizedLCHS
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder

namespace Qatlib.Papers.KoopmanSim26.SpectralRep

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def cauchyDensity (k : ℝ) : ℝ := 1/(Real.pi*(1+k^2))

noncomputable def cauchyDensityDeriv (k : ℝ) : ℝ := -(2*k)/(Real.pi*(1+k^2)^2)

noncomputable def cauchyLipschitzConst : ℝ := 3*Real.sqrt 3/(8*Real.pi)

private lemma cauchyDensity_nonneg (k : ℝ) : 0 ≤ cauchyDensity k := by
  dsimp [cauchyDensity]; positivity

private lemma cauchyDensity_le_peak (k : ℝ) : cauchyDensity k ≤ 1/Real.pi := by
  dsimp only [cauchyDensity]
  apply div_le_div_of_nonneg_left (by norm_num) Real.pi_pos
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg k)]

private lemma hasDerivAt_cauchyDensity (k : ℝ) :
    HasDerivAt cauchyDensity (cauchyDensityDeriv k) k := by
  have hfun : cauchyDensity = fun k : ℝ => (1+k^2)⁻¹ * Real.pi⁻¹ := by
    funext x; simp [cauchyDensity, one_div, mul_comm]
  have hbase : HasDerivAt (fun x : ℝ => (1+x^2)⁻¹) (-(2*k)/(1+k^2)^2) k := by
    have h1 : HasDerivAt (fun x : ℝ => 1+x^2) (2*k) k := by
      have h := (hasDerivAt_const (x:=k) (c:=(1:ℝ))).add (hasDerivAt_pow 2 k)
      rw [pow_one, zero_add] at h
      exact h
    exact h1.inv (by positivity : (1+k^2 : ℝ) ≠ 0)
  have hmul : HasDerivAt (fun x : ℝ => (1+x^2)⁻¹ * Real.pi⁻¹)
      ((-(2*k)/(1+k^2)^2) * Real.pi⁻¹) k := hbase.mul_const _
  rw [hfun]
  have hv : ((-(2*k)/(1+k^2)^2) * Real.pi⁻¹) = cauchyDensityDeriv k := by
    simp only [cauchyDensityDeriv]; field_simp; try ring
  rw [hv] at hmul
  exact hmul

private lemma abs_cauchyDensityDeriv_le (k : ℝ) : |cauchyDensityDeriv k| ≤ cauchyLipschitzConst := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [cauchyDensityDeriv, cauchyLipschitzConst]
  rw [show (-(2*k)/(Real.pi*(1+k^2)^2)) = -((2*k)/(Real.pi*(1+k^2)^2)) by ring, abs_neg]
  rw [abs_div, abs_of_pos (by positivity : 0 < Real.pi*(1+k^2)^2)]
  rw [div_le_iff₀ (by positivity : 0 < Real.pi*(1+k^2)^2)]
  have hpoly : (3*k^2-1)^2*(3*k^4+14*k^2+27) = 27*(1+k^2)^4 - 256*k^2 := by ring
  have hnonneg : 0 ≤ (3*k^2-1)^2*(3*k^4+14*k^2+27) := by positivity
  have hkey : 256*k^2 ≤ 27*(1+k^2)^4 := by nlinarith [hpoly, hnonneg]
  have hR : ((3*Real.sqrt 3/8)*(1+k^2)^2)^2 = (27/64)*(1+k^2)^4 := by
    have hcoef : (3*Real.sqrt 3/8)^2 = 27/64 := by
      rw [div_pow, mul_pow, hs]; norm_num
    have hrew : ((3*Real.sqrt 3/8)*(1+k^2)^2)^2
        = (3*Real.sqrt 3/8)^2 * ((1+k^2)^2)^2 := by ring
    rw [hrew, hcoef]; ring_nf
  have hsq : |2*k|^2 ≤ ((3*Real.sqrt 3/8)*(1+k^2)^2)^2 := by
    rw [sq_abs, hR]; nlinarith [hkey]
  have hA : 0 ≤ |2*k| := abs_nonneg _
  have hB : 0 ≤ (3*Real.sqrt 3/8)*(1+k^2)^2 := by positivity
  have hfin : |2*k| ≤ (3*Real.sqrt 3/8)*(1+k^2)^2 := by nlinarith [hsq, hA, hB]
  have heq : (3*Real.sqrt 3/8)*(1+k^2)^2 = (3*Real.sqrt 3/(8*Real.pi)) * (Real.pi*(1+k^2)^2) := by
    field_simp
  rw [heq] at hfin
  exact hfin

private lemma cauchyDensity_lipschitz (a b : ℝ) :
    |cauchyDensity a - cauchyDensity b| ≤ cauchyLipschitzConst * |a-b| := by
  rcases le_total a b with hab | hba
  · have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (f:=cauchyDensity) (f':=cauchyDensityDeriv) (C:=cauchyLipschitzConst) (a:=a) (b:=b)
        (fun x _ => (hasDerivAt_cauchyDensity x).hasDerivWithinAt)
        (fun x _ => by rw [Real.norm_eq_abs]; exact abs_cauchyDensityDeriv_le x)
        b ⟨hab, le_rfl⟩
    rw [Real.norm_eq_abs] at h
    rw [abs_sub_comm (cauchyDensity a) (cauchyDensity b)]
    calc |cauchyDensity b - cauchyDensity a| ≤ cauchyLipschitzConst*(b-a) := h
      _ = cauchyLipschitzConst*|a-b| := by rw [abs_sub_comm a b, abs_of_nonneg (by linarith)]
  · have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (f:=cauchyDensity) (f':=cauchyDensityDeriv) (C:=cauchyLipschitzConst) (a:=b) (b:=a)
        (fun x _ => (hasDerivAt_cauchyDensity x).hasDerivWithinAt)
        (fun x _ => by rw [Real.norm_eq_abs]; exact abs_cauchyDensityDeriv_le x)
        a ⟨hba, le_rfl⟩
    rw [Real.norm_eq_abs] at h
    calc |cauchyDensity a - cauchyDensity b| ≤ cauchyLipschitzConst*(a-b) := h
      _ = cauchyLipschitzConst*|a-b| := by rw [abs_of_nonneg (by linarith : 0 ≤ a - b)]

private lemma cauchyDensity_continuous : Continuous cauchyDensity := by
  apply Continuous.div continuous_const
  · fun_prop
  · intro k; positivity

private lemma cauchyDensity_integrable : Integrable cauchyDensity := by
  change Integrable (fun k : ℝ => 1/(Real.pi*(1+k^2)))
  simpa [cauchyDensity, div_eq_mul_inv, _root_.mul_inv_rev, mul_comm] using!
    integrable_inv_one_add_sq.const_mul Real.pi⁻¹

private lemma cauchy_arctan_le (x : ℝ) (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := 0) (b := x) (f := Real.arctan) (f' := fun k : ℝ => (1+k^2)⁻¹) (C := 1)
    (fun k _ => (Real.hasDerivAt_arctan' k).hasDerivWithinAt)
    (fun k _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg k])) x ⟨hx, le_rfl⟩
  have hh : |Real.arctan x| ≤ x := by simpa using! hb
  exact (le_abs_self _).trans hh

private lemma cauchyDensity_tail (K : ℝ) (hK : 0 < K) :
    (∫ k : ℝ in (Set.Ioc (-K) K)ᶜ, cauchyDensity k) ≤ 2/(Real.pi*K) := by
  have he : (Set.Ioc (-K) K)ᶜ = Set.Iic (-K) ∪ Set.Ioi K := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
      not_and_or, not_lt, not_le]
  have hd : Disjoint (Set.Iic (-K)) (Set.Ioi K) := by
    rw [Set.disjoint_left]
    intro x hx hy; simp only [Set.mem_Iic, Set.mem_Ioi] at *; linarith
  rw [he, setIntegral_union hd measurableSet_Ioi cauchyDensity_integrable.integrableOn
    cauchyDensity_integrable.integrableOn]
  have hleft : (∫ k : ℝ in Set.Iic (-K), cauchyDensity k) =
      Real.pi⁻¹*(Real.pi/2-Real.arctan K) := by
    simp only [cauchyDensity, div_eq_mul_inv, _root_.mul_inv_rev, one_mul]
    rw [integral_mul_const, integral_Iic_inv_one_add_sq, Real.arctan_neg]
    ring
  have hright : (∫ k : ℝ in Set.Ioi K, cauchyDensity k) =
      Real.pi⁻¹*(Real.pi/2-Real.arctan K) := by
    simp only [cauchyDensity, div_eq_mul_inv, _root_.mul_inv_rev, one_mul]
    rw [integral_mul_const, integral_Ioi_inv_one_add_sq]
    ring
  rw [hleft, hright, ← Real.arctan_inv_of_pos hK]
  have ha := cauchy_arctan_le K⁻¹ (inv_nonneg.mpr hK.le)
  calc
    _ ≤ Real.pi⁻¹*K⁻¹+Real.pi⁻¹*K⁻¹ := by gcongr
    _ = _ := by ring

section Quadrature

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in

private lemma cauchy_weighted_integrable (V : ℝ → E) (hV : Continuous V)
    (hn : ∀ k, ‖V k‖ ≤ 1) : Integrable (fun k => cauchyDensity k • V k) :=
  cauchyDensity_integrable.smul_bdd 1 hV.aestronglyMeasurable (Filter.Eventually.of_forall hn)

omit [CompleteSpace E] in

private lemma cauchy_weighted_tail (V : ℝ → E) (hV : Continuous V)
    (hn : ∀ k, ‖V k‖ ≤ 1) (K : ℝ) (hK : 0 < K) :
    ‖(∫ k : ℝ, cauchyDensity k • V k) - (∫ k in (-K)..K, cauchyDensity k • V k)‖ ≤
      2/(Real.pi*K) := by
  have hf := cauchy_weighted_integrable V hV hn
  rw [intervalIntegral.integral_of_le (by linarith : -K ≤ K),
    ← integral_add_compl measurableSet_Ioc hf, add_sub_cancel_left]
  apply (MeasureTheory.norm_integral_le_of_norm_le cauchyDensity_integrable.integrableOn
    (Filter.Eventually.of_forall (fun k => ?_))).trans (cauchyDensity_tail K hK)
  rw [norm_smul, Real.norm_of_nonneg (cauchyDensity_nonneg k)]
  simpa using! mul_le_mul_of_nonneg_left (hn k) (cauchyDensity_nonneg k)

private lemma intervalIntegral_abs_sub_right (a h : ℝ) (hh : 0 ≤ h) :
    (∫ k in a..(a+h), |a+h-k|) = h^2/2 := by
  have hcongr : (∫ k in a..(a+h), |a+h-k|) = ∫ k in a..(a+h), (a+h-k) := by
    apply intervalIntegral.integral_congr
    intro k hk
    rw [Set.uIcc_of_le (by linarith : a ≤ a+h)] at hk
    (try dsimp only)
    rw [abs_of_nonneg (by linarith [hk.2] : 0 ≤ a+h-k)]
  rw [hcongr]
  have hF : (∫ k in a..(a+h), (a+h-k)) =
      (-((a+h)-(a+h))^2/2) - (-((a+h)-a)^2/2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => -((a+h)-x)^2/2) (f' := fun x => a+h-x)
    · intro x _
      have h1 : HasDerivAt (fun x : ℝ => (a+h)-x) (-1) x := by
        simpa using! (hasDerivAt_id x).const_sub (a+h)
      have h2 := (h1.pow 2).neg.div_const 2
      convert! h2 using 1
      ring
    · exact (continuous_const.sub continuous_id).intervalIntegrable _ _
  rw [hF]
  ring

private theorem cauchy_weighted_grid_error (V : ℝ → E) (hVc : Continuous V)
    (hn : ∀ k, ‖V k‖ ≤ 1) (T : ℝ) (_hT : 0 ≤ T)
    (hl : ∀ a b, ‖V a - V b‖ ≤ T*|a-b|)
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 0 < N) :
    ‖(∑ j ∈ Finset.range N, ((2*K/(N:ℝ))*cauchyDensity (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ))) •
        V (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ))) -
      (∫ k in (-K)..K, cauchyDensity k • V k)‖ ≤
      (2*K^2/(N:ℝ)) * (cauchyLipschitzConst + T/Real.pi) := by
  let h : ℝ := 2*K/(N:ℝ)
  let x := fun j : ℕ => -K+h*j
  let F := fun k : ℝ => cauchyDensity k • V k
  change ‖(∑ j ∈ Finset.range N, (h*cauchyDensity (x (j+1))) • V (x (j+1))) -
      (∫ k in (-K)..K, F k)‖ ≤ (2*K^2/(N:ℝ))*(cauchyLipschitzConst + T/Real.pi)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNRne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have h0 : 0 ≤ h := by dsimp [h]; positivity
  have hstep (j : ℕ) : x (j+1)-x j = h := by dsimp [x]; push_cast; ring
  have horder (j : ℕ) : x j ≤ x (j+1) := by linarith [hstep j]
  have hx0 : x 0 = -K := by simp [x]
  have hxN : x N = K := by dsimp [x, h]; field_simp; try ring
  have hFc : Continuous F := cauchyDensity_continuous.smul hVc
  have hpoint (j : ℕ) (k : ℝ) (hk : k ∈ Set.Ioc (x j) (x (j+1))) :
      ‖F (x (j+1))-F k‖ ≤ (cauchyLipschitzConst + T/Real.pi)*|x (j+1) - k| := by
    have he : F (x (j+1))-F k = (cauchyDensity (x (j+1))-cauchyDensity k) • V (x (j+1)) +
        cauchyDensity k • (V (x (j+1))-V k) := by dsimp [F]; simp [sub_smul, smul_sub]
    rw [he]
    calc
      _ ≤ ‖(cauchyDensity (x (j+1))-cauchyDensity k) • V (x (j+1))‖ +
          ‖cauchyDensity k • (V (x (j+1))-V k)‖ := norm_add_le _ _
      _ = |cauchyDensity (x (j+1))-cauchyDensity k| * ‖V (x (j+1))‖+
          cauchyDensity k*‖V (x (j+1))-V k‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (cauchyDensity_nonneg k)]
      _ ≤ (cauchyLipschitzConst*|x (j+1) - k|)*1+(1/Real.pi)*(T*|x (j+1) - k|) := by
        apply add_le_add
        · refine mul_le_mul (cauchyDensity_lipschitz (x (j+1)) k) (hn (x (j+1))) (norm_nonneg _) ?_
          have hc0 : 0 ≤ cauchyLipschitzConst := by dsimp [cauchyLipschitzConst]; positivity
          exact mul_nonneg hc0 (abs_nonneg _)
        · refine mul_le_mul (cauchyDensity_le_peak k) (hl (x (j+1)) k) (norm_nonneg _) ?_
          positivity
      _ = (cauchyLipschitzConst + T/Real.pi)*|x (j+1) - k| := by ring
  let D := fun j : ℕ => ∫ k in x j..x (j+1), F (x (j+1))-F k
  have hcell (j : ℕ) : ‖D j‖ ≤ (cauchyLipschitzConst + T/Real.pi)*(h^2/2) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (horder j)
      (f := fun k => F (x (j+1))-F k)
      (g := fun k => (cauchyLipschitzConst + T/Real.pi)*|x (j+1) - k|)
      (Filter.Eventually.of_forall (fun k hk => hpoint j k hk))
      ((continuous_const.mul (continuous_abs.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _)
    have hsub : x (j+1) = x j + h := by linarith [hstep j]
    have hInt : (∫ k in x j..x (j+1), (cauchyLipschitzConst + T/Real.pi)*|x (j+1) - k|) =
        (cauchyLipschitzConst + T/Real.pi)*(h^2/2) := by
      rw [intervalIntegral.integral_const_mul, hsub, intervalIntegral_abs_sub_right _ _ h0]
    exact hi.trans_eq hInt
  have hD : (∑ j ∈ Finset.range N, (h*cauchyDensity (x (j+1))) • V (x (j+1)))-
      (∫ k in (-K)..K, F k) = ∑ j ∈ Finset.range N, D j := by
    have hd (j : ℕ) : D j = (h*cauchyDensity (x (j+1))) • V (x (j+1))-
        (∫ k in x j..x (j+1), F k) := by
      dsimp [D]
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hFc.intervalIntegrable _ _),
        intervalIntegral.integral_const, hstep]
      dsimp [F]
      rw [smul_smul]
    simp_rw [hd]
    rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => hFc.intervalIntegrable _ _), hx0, hxN]
  rw [hD]
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖D j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, (cauchyLipschitzConst + T/Real.pi)*(h^2/2) := Finset.sum_le_sum (fun j _ => hcell j)
    _ = (N:ℝ) * ((cauchyLipschitzConst + T/Real.pi)*(h^2/2)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (2*K^2/(N:ℝ)) * (cauchyLipschitzConst + T/Real.pi) := by
      dsimp only [h]
      field_simp
      try ring

end Quadrature

noncomputable def mesh (K : ℝ) (N : ℕ) : ℝ := 2*K/(N:ℝ)

noncomputable def gridPoint (K : ℝ) (N j : ℕ) : ℝ := -K + mesh K N * j

noncomputable def cauchyQuadrature (L H : Matrix I I ℂ) (t K : ℝ) (N : ℕ) : Matrix I I ℂ :=
  ∑ j ∈ Finset.range N,
    (mesh K N * cauchyDensity (gridPoint K N (j+1))) • spectralUnitary L H t (gridPoint K N (j+1))

theorem spectral_sampling_quadrature_error
    (L H : Matrix I I ℂ) (t K : ℝ) (N : ℕ)
    (hL : (-L).PosSemidef) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (hK : 0 < K) (hN : 0 < N) :
    ‖propagator L H t - cauchyQuadrature L H t K N‖ ≤
      2/(Real.pi*K) + (2*K^2/(N:ℝ))*(cauchyLipschitzConst + t*‖L‖/Real.pi) := by
  have hLh : L.IsHermitian := by simpa using! hL.isHermitian.neg
  let V : ℝ → Matrix I I ℂ := fun k => spectralUnitary L H t k
  have hVc : Continuous V := by
    letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    have hfun : V = fun k => hamiltonianEvolution ((-H) + k • (-L)) t := by
      funext k; exact spectralUnitary_eq_hamiltonianEvolution L H t k
    rw [hfun]
    have h1 : Continuous (fun k : ℝ => (-Complex.I * (t : ℂ)) • (-H + k • -L)) := by fun_prop
    exact NormedSpace.exp_continuous.comp h1
  have hVn (k : ℝ) : ‖V k‖ ≤ 1 := by
    dsimp only [V]
    rw [spectralUnitary_eq_hamiltonianEvolution]
    exact l2_norm_unitary_le_one
      (hamiltonianEvolution_unitary
        (hH.neg.add (hLh.neg.smul (R := ℝ) (IsSelfAdjoint.all k))) t)
  have hVl (a b : ℝ) : ‖V a - V b‖ ≤ (t*‖L‖)*|a-b| := by
    dsimp only [V]
    rw [spectralUnitary_eq_hamiltonianEvolution, spectralUnitary_eq_hamiltonianEvolution]
    have hh := static_lchs_hamiltonian_evolution_stability ((-H)+a • (-L)) ((-H)+b • (-L))
      (hH.neg.add (hLh.neg.smul (R := ℝ) (IsSelfAdjoint.all a)))
      (hH.neg.add (hLh.neg.smul (R := ℝ) (IsSelfAdjoint.all b))) t
    have he : ((-H)+a • (-L)) - ((-H)+b • (-L)) = (a-b) • (-L) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
          Complex.real_smul]
      push_cast
      ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, norm_neg] at hh
    convert! hh using 1
    ring
  have hg := cauchy_weighted_grid_error V hVc hVn (t*‖L‖) (mul_nonneg ht (norm_nonneg L))
    hVl K hK N hN
  have htail := cauchy_weighted_tail V hVc hVn K hK
  have he := (diagonalized_lchs_spectral_representation L H t hL hH ht).2
  have he' : (∫ k : ℝ, cauchyDensity k • V k) = propagator L H t := by
    dsimp only [cauchyDensity, V]; exact he
  have hq : cauchyQuadrature L H t K N = ∑ j ∈ Finset.range N,
      ((2*K/(N:ℝ))*cauchyDensity (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ))) •
        V (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ)) := by
    simp only [cauchyQuadrature, mesh, gridPoint]
    rfl
  rw [hq, ← he']
  have hh := norm_sub_le_norm_sub_add_norm_sub
    (∫ k : ℝ, cauchyDensity k • V k)
    (∫ k in (-K)..K, cauchyDensity k • V k)
    (∑ j ∈ Finset.range N, ((2*K/(N:ℝ))*cauchyDensity (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ))) •
        V (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ)))
  rw [norm_sub_rev (∫ k in (-K)..K, cauchyDensity k • V k)
        (∑ j ∈ Finset.range N, ((2*K/(N:ℝ))*cauchyDensity (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ))) •
          V (-K + (2*K/(N:ℝ))*((j+1:ℕ):ℝ)))] at hh
  exact hh.trans (add_le_add htail hg)

theorem spectral_sampling_convergence
    (L H : Matrix I I ℂ) (t : ℝ) (N : ℕ)
    (hL : (-L).PosSemidef) (hH : H.IsHermitian) (ht : 0 ≤ t) (hN : 0 < N) :
    ‖propagator L H t -
      cauchyQuadrature L H t (((3*Real.sqrt 3 + 8*t*‖L‖)/(4*(N:ℝ)))^(-(1/3):ℝ)) N‖ ≤
      (3/Real.pi) * (((3*Real.sqrt 3 + 8*t*‖L‖)/(4*(N:ℝ)))^(1/3:ℝ)) := by
  set c : ℝ := 3*Real.sqrt 3 + 8*t*‖L‖ with hc_def
  set K : ℝ := (c/(4*(N:ℝ)))^(-(1/3):ℝ) with hK_def
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hcpos : 0 < c := by
    rw [hc_def]
    have h1 : 0 < 3*Real.sqrt 3 := by
      have hs := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3); nlinarith
    have h2 : 0 ≤ 8*t*‖L‖ := by positivity
    linarith
  have hbase : 0 < c/(4*(N:ℝ)) := by positivity
  have hKpos : 0 < K := by
    rw [hK_def]; exact Real.rpow_pos_of_pos hbase _
  have hK3 : K^3 = 4*(N:ℝ)/c := by
    rw [hK_def, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    rw [show (-(1/3):ℝ)*((3:ℕ):ℝ) = -1 by norm_num, Real.rpow_neg_one]
    rw [show (c/(4*(N:ℝ)))⁻¹ = 4*(N:ℝ)/c by field_simp]
  have hCT : cauchyLipschitzConst + t*‖L‖/Real.pi = c/(8*Real.pi) := by
    rw [hc_def, cauchyLipschitzConst]
    field_simp
    try ring
  have hNval : (N:ℝ) = c*K^3/4 := by
    have hKc : c*K^3 = 4*(N:ℝ) := by rw [hK3]; field_simp
    rw [hKc]; ring
  have hb : (c/(4*(N:ℝ)))^(1/3:ℝ) = 1/K := by
    have hKinv : K = (((c/(4*(N:ℝ)))^(1/3:ℝ))⁻¹) := by
      rw [hK_def, Real.rpow_neg hbase.le]
    rw [hKinv]
    simp
  have hmain := spectral_sampling_quadrature_error L H t K N hL hH ht hKpos hN
  refine hmain.trans ?_
  rw [hCT, hb]
  rw [hNval]
  have hKne : K ≠ 0 := ne_of_gt hKpos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  field_simp
  norm_num

end Qatlib.Papers.KoopmanSim26.SpectralRep
