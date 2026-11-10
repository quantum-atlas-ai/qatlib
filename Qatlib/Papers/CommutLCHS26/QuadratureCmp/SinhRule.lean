/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Function.JacobianOneDim
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
open Real Set Filter MeasureTheory
open scoped Topology BigOperators
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid

def pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (f : ℝ → E) (x : ℝ) : E := (η * Real.cosh x) • f (η * Real.sinh x)

theorem scaled_surjective {η : ℝ} (hη : 0 < η) :
    Function.Surjective (fun x : ℝ => η * Real.sinh x) := by
  intro y
  obtain ⟨x, hx⟩ := Real.sinh_surjective (y / η)
  refine ⟨x, ?_⟩
  change η * Real.sinh x = y
  rw [hx]
  field_simp

theorem integral_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} (hη : 0 < η) (f : ℝ → E) :
    (∫ x : ℝ, pullback η f x) = ∫ y : ℝ, f y := by
  have hs : (fun x : ℝ => η * Real.sinh x) '' univ = univ :=
    by rw [Set.image_univ]; exact Set.range_eq_univ.mpr (scaled_surjective hη)
  have hi := integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => ((Real.hasDerivAt_sinh x).const_mul η).hasDerivWithinAt)
    ((Real.sinh_strictMono.const_mul hη).monotone.monotoneOn univ) f
  simpa only [hs, setIntegral_univ, pullback] using! hi.symm

theorem integrable_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} (hη : 0 < η) (f : ℝ → E) :
    Integrable (pullback η f) ↔ Integrable f := by
  have hs : (fun x : ℝ => η * Real.sinh x) '' univ = univ :=
    by rw [Set.image_univ]; exact Set.range_eq_univ.mpr (scaled_surjective hη)
  have hi := integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => ((Real.hasDerivAt_sinh x).const_mul η).hasDerivWithinAt)
    ((Real.sinh_strictMono.const_mul hη).monotone.monotoneOn univ) f
  simpa only [hs, integrableOn_univ, pullback] using! hi.symm

theorem integral_pullback_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : ℝ} (hη : 0 < η) (f : ℝ → E) (Y : ℝ) :
    (∫ x in Ioi Y, pullback η f x) = ∫ y in Ioi (η * Real.sinh Y), f y := by
  have hm := Real.sinh_strictMono.const_mul hη
  have hs : (fun x : ℝ => η * Real.sinh x) '' Ioi Y = Ioi (η * Real.sinh Y) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hm hx
    · intro hy
      obtain ⟨x, rfl⟩ := scaled_surjective hη y
      exact ⟨x, hm.lt_iff_lt.mp hy, rfl⟩
  have hi := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi
    (fun x _ => ((Real.hasDerivAt_sinh x).const_mul η).hasDerivWithinAt) (hm.monotone.monotoneOn (Ioi Y)) f
  simpa only [hs, pullback] using! hi.symm

def bell (kappa x : ℝ) : ℝ := Real.cosh x * Real.exp (-kappa ^ 2 * Real.sinh x ^ 2)

theorem bell_hasDerivAt (kappa x : ℝ) : HasDerivAt (bell kappa)
    (Real.sinh x * Real.exp (-kappa ^ 2 * Real.sinh x ^ 2) *
      (1 - 2 * kappa ^ 2 * Real.cosh x ^ 2)) x := by
  have hd := (Real.hasDerivAt_cosh x).mul
    ((((Real.hasDerivAt_sinh x).pow 2).const_mul (-kappa ^ 2)).exp)
  convert! hd using 1
  dsimp [bell]
  ring

theorem bell_antitone {kappa Y : ℝ} (hkappa : 0 < kappa) (hY : 0 ≤ Y)
    (hlarge : 1 ≤ kappa * Real.sinh Y) : AntitoneOn (bell kappa) (Ici Y) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici Y)
    (by unfold bell; fun_prop) (fun x _ => (bell_hasDerivAt kappa x).hasDerivWithinAt)
  intro x hx
  have hxY : Y ≤ x := interior_subset hx
  have hx₀ : 0 ≤ x := hY.trans hxY
  have hs : 1 ≤ kappa * Real.sinh x := hlarge.trans
    (mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr hxY) hkappa.le)
  have hsq : 1 ≤ kappa ^ 2 * Real.sinh x ^ 2 := by nlinarith [sq_nonneg (kappa * Real.sinh x - 1)]
  have hcos := Real.cosh_sq_sub_sinh_sq x
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (Real.sinh_nonneg_iff.mpr hx₀) (Real.exp_pos _).le
  · nlinarith [sq_nonneg kappa]

theorem scaled_tail_on (f : ℝ → ℝ) (N : ℕ) {h : ℝ} (hh : 0 < h)
    (hf : AntitoneOn f (Ici (h * N))) (hn : ∀ x, 0 ≤ f x) (hi : Integrable f) :
    Summable (fun j : ℕ => f (h * ((N : ℝ) + (j + 1 : ℕ)))) ∧
      h * (∑' j : ℕ, f (h * ((N : ℝ) + (j + 1 : ℕ)))) ≤ ∫ x in Ioi (h * N), f x := by
  have hg : AntitoneOn (fun x : ℝ => f (h * x)) (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact hf (mul_le_mul_of_nonneg_left hx hh.le) (mul_le_mul_of_nonneg_left hy hh.le)
      (mul_le_mul_of_nonneg_left hxy hh.le)
  have ht := antitone_tail_on (fun x => f (h * x)) N hg (fun _ => hn _)
    (hi.comp_mul_left' hh.ne')
  refine ⟨ht.1, ?_⟩
  have he := integral_comp_mul_left_Ioi f (N : ℝ) hh
  have hm := mul_le_mul_of_nonneg_left ht.2 hh.le
  rw [he, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul] at hm
  exact hm

def majorant (c η x : ℝ) : ℝ := η * Real.cosh x * Real.exp (-(η * Real.sinh x) ^ 2 / (4 * c ^ 2))

theorem majorant_eq_pullback (c η : ℝ) : majorant c η =
    pullback η (fun x : ℝ => Real.exp (-x ^ 2 / (4 * c ^ 2))) := by
  rfl

theorem majorant_integrable {c η : ℝ} (hc : 0 < c) (hη : 0 < η) : Integrable (majorant c η) := by
  rw [majorant_eq_pullback]
  exact (integrable_pullback hη _).mpr (gaussian_integrable hc)

theorem majorant_even (c η x : ℝ) : majorant c η (-x) = majorant c η x := by
  simp only [majorant, Real.cosh_neg, Real.sinh_neg, mul_neg, neg_sq]

theorem majorant_antitone {c η Y : ℝ} (hc : 0 < c) (hη : 0 < η) (hY : 0 ≤ Y)
    (hlarge : 1 ≤ η / (2 * c) * Real.sinh Y) : AntitoneOn (majorant c η) (Ici Y) := by
  have he : majorant c η = fun x : ℝ => η * bell (η / (2 * c)) x := by
    funext x
    unfold majorant bell
    have hp : -(η * Real.sinh x) ^ 2 / (4 * c ^ 2) = -(η / (2 * c)) ^ 2 * Real.sinh x ^ 2 := by
      field_simp
      ring
    rw [hp]
    ring
  rw [he]
  intro x hx y hy hxy
  exact mul_le_mul_of_nonneg_left
    (bell_antitone (div_pos hη (by positivity)) hY hlarge hx hy hxy) hη.le

theorem majorant_tail {c η Y : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hY : 0 < Y) :
    (∫ x in Ioi Y, majorant c η x) = c * Real.sqrt Real.pi *
      (1 - Qatlib.Concepts.QsvtCore.ApproxToolkit.erf (η * Real.sinh Y / (2 * c))) := by
  rw [majorant_eq_pullback, integral_pullback_tail hη]
  exact Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.gaussian_tail_erfc
    hc (mul_pos hη (Real.sinh_pos_iff.mpr hY))

open scoped Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

def transformed (n : ℕ) (b c d T η : ℝ) (H L : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  ((η : ℂ) * Complex.cosh z) • integrand n b c d T H L ((η : ℂ) * Complex.sinh z)

theorem transformed_real (n : ℕ) (b c d T η : ℝ) (H L : Matrix ι ι ℂ) (x : ℝ) :
    transformed n b c d T η H L (x : ℂ) =
      pullback η (fun k : ℝ => integrand n b c d T H L (k : ℂ)) x := by
  unfold transformed pullback
  rw [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

theorem actual_integral_change (n : ℕ) (b c d T : ℝ) {η : ℝ} (hη : 0 < η)
    (H L : Matrix ι ι ℂ) :
    (∫ x : ℝ, transformed n b c d T η H L (x : ℂ)) =
      ∫ k : ℝ, integrand n b c d T H L (k : ℂ) := by
  simp only [transformed_real]
  exact integral_pullback hη _

theorem actual_integrability (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η : ℝ} (hT : 0 ≤ T) (hη : 0 < η) :
    Integrable (fun k : ℝ => integrand n b c d T H L (k : ℂ)) ∧
      Integrable (fun x : ℝ => transformed n b c d T η H L (x : ℂ)) := by
  have hf : Integrable (fun k : ℝ => integrand n b c d T H L (k : ℂ)) := by
    simpa using! integrand_integrable n b c d hb hc H L hH hL hT
      (ρ := 0) (y := 0) (by norm_num) (Or.inr hb) (by simp)
  refine ⟨hf, ?_⟩
  simpa only [transformed_real] using! (integrable_pullback hη _).mpr hf

theorem norm_transformed_le (n : ℕ) (b c d : ℝ) (hb : 0 < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (x : ℝ) :
    ‖transformed n b c d T η H L (x : ℂ)‖ ≤ amplitude n b c d 0 0 * majorant c η x := by
  rw [transformed_real, pullback, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ η * Real.cosh x)]
  have he := coefficient_growth_le n b c d hb (ρ := 0) (K := 0) (by norm_num)
    (Or.inr hb) (by norm_num) (z := ((η * Real.sinh x : ℝ) : ℂ)) (by simp)
  simp only [Complex.ofReal_im, Complex.ofReal_re, max_self, zero_mul, Real.exp_zero, mul_one] at he
  have hn := (norm_real_integrand_le n b c d H L hH hL hT _).trans he
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by unfold majorant; ring)

theorem even_tail (f : ℝ → ℝ) (N : ℕ) (h : ℝ) (heven : ∀ x, f (-x) = f x)
    (hsum : Summable (fun j : ℕ => f (h * ((N : ℝ) + (j + 1 : ℕ))))) :
    Summable (fun q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N} => f (h * (q.val : ℝ))) ∧
      (∑' q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N}, f (h * (q.val : ℝ))) =
        2 * ∑' j : ℕ, f (h * ((N : ℝ) + (j + 1 : ℕ))) := by
  let g := fun q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N} => f (h * (q.val : ℝ))
  have hp : (fun j : ℕ => g (tailEquiv N (Sum.inl j))) =
      (fun j : ℕ => f (h * ((N : ℝ) + (j + 1 : ℕ)))) := by
    funext j
    dsimp [g, tailEquiv, tailIndex]
    congr 1
    push_cast
    ring
  have hm : (fun j : ℕ => g (tailEquiv N (Sum.inr j))) =
      (fun j : ℕ => f (h * ((N : ℝ) + (j + 1 : ℕ)))) := by
    funext j
    dsimp [g, tailEquiv, tailIndex]
    push_cast
    convert! heven (h * ((N : ℝ) + ((j : ℝ) + 1))) using 1
    congr 1
    ring
  have hs : Summable (fun j : ℕ ⊕ ℕ => g (tailEquiv N j)) :=
    Summable.sum _ (by change Summable (fun j : ℕ => g (tailEquiv N (Sum.inl j))); rw [hp]; exact hsum)
      (by change Summable (fun j : ℕ => g (tailEquiv N (Sum.inr j))); rw [hm]; exact hsum)
  refine ⟨(tailEquiv N).summable_iff.mp hs, ?_⟩
  calc
    _ = ∑' j : ℕ ⊕ ℕ, g (tailEquiv N j) := ((tailEquiv N).tsum_eq g).symm
    _ = (∑' j : ℕ, g (tailEquiv N (Sum.inl j))) +
        ∑' j : ℕ, g (tailEquiv N (Sum.inr j)) :=
      (hs.comp_injective Sum.inl_injective).tsum_sum (hs.comp_injective Sum.inr_injective)
    _ = _ := by rw [hp, hm]; ring

def finiteIdeal (n : ℕ) (b c d T η h : ℝ) (H L : Matrix ι ι ℂ) (N : ℕ) : Matrix ι ι ℂ :=
  h • ∑ q ∈ Finset.Icc (-(N : ℤ)) N, transformed n b c d T η H L ((h * (q : ℝ) : ℝ) : ℂ)

theorem finite_weighted (n : ℕ) (b c d T η h : ℝ) (H L : Matrix ι ι ℂ) (N : ℕ) :
    finiteIdeal n b c d T η h H L N =
      ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
        (((h * η * Real.cosh (h * (q : ℝ)) : ℝ) : ℂ) *
          coefficient n b c d ((η * Real.sinh (h * (q : ℝ)) : ℝ) : ℂ)) •
          propagator H L T ((η * Real.sinh (h * (q : ℝ)) : ℝ) : ℂ) := by
  rw [finiteIdeal, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [transformed_real, pullback, integrand]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

def latticeTail (n : ℕ) (b c d T η h : ℝ) (H L : Matrix ι ι ℂ) (N : ℕ) : ℝ :=
  h * ∑' q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N},
    ‖transformed n b c d T η H L ((h * (q.val : ℝ) : ℝ) : ℂ)‖

theorem actual_tail_erfc (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η h : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (hh : 0 < h) (N : ℕ)
    (hlarge : 1 ≤ η / (2 * c) * Real.sinh (h * N)) :
    Summable (fun q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N} =>
      ‖transformed n b c d T η H L ((h * (q.val : ℝ) : ℝ) : ℂ)‖) ∧
    latticeTail n b c d T η h H L N ≤
      Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant n b c d *
        (1 - Qatlib.Concepts.QsvtCore.ApproxToolkit.erf (η * Real.sinh (h * N) / (2 * c))) := by
  let C := amplitude n b c d 0 0
  have hC : 0 ≤ C := by dsimp [C, amplitude]; positivity
  have hN : 0 ≤ h * (N : ℝ) := mul_nonneg hh.le (Nat.cast_nonneg _)
  have hp := scaled_tail_on (majorant c η) N hh
    (majorant_antitone hc hη hN hlarge) (fun x => by unfold majorant; positivity)
    (majorant_integrable hc hη)
  have he := even_tail (majorant c η) N h (majorant_even c η) hp.1
  let g := fun q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N} =>
    ‖transformed n b c d T η H L ((h * (q.val : ℝ) : ℝ) : ℂ)‖
  have hgs : Summable g := (he.1.mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun q => norm_transformed_le n b c d hb H L hH hL hT hη _)
  have hY : 0 < h * (N : ℝ) := by
    by_contra! hn
    have hz : h * (N : ℝ) = 0 := le_antisymm hn hN
    norm_num [hz] at hlarge
  refine ⟨hgs, ?_⟩
  calc
    _ ≤ h * ∑' q : {q : ℤ // q ∉ Finset.Icc (-(N : ℤ)) N}, C * majorant c η (h * (q.val : ℝ)) :=
      mul_le_mul_of_nonneg_left (hgs.tsum_le_tsum
        (fun q => norm_transformed_le n b c d hb H L hH hL hT hη _) (he.1.mul_left C)) hh.le
    _ = C * (h * (2 * ∑' j : ℕ, majorant c η (h * ((N : ℝ) + (j + 1 : ℕ))))) := by
      rw [tsum_mul_left, he.2]
      ring
    _ ≤ C * (2 * ∫ x in Ioi (h * N), majorant c η x) := by
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith [hp.2]
    _ = _ := by
      rw [majorant_tail hc hη hY]
      have hcst := amplitude_mul_gaussian n b c d 0 0
      rw [Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.mass_zero] at hcst
      dsimp [C]
      rw [← hcst]
      ring

theorem actual_tail_bounds (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η h : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (hh : 0 < h) (Y : ℝ)
    (hlarge : 1 ≤ η / (2 * c) * Real.sinh (h * cutoff Y h)) :
    latticeTail n b c d T η h H L (cutoff Y h) ≤
      Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant n b c d *
        (1 - Qatlib.Concepts.QsvtCore.ApproxToolkit.erf
          (η * Real.sinh (h * cutoff Y h) / (2 * c))) ∧
    Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant n b c d *
        (1 - Qatlib.Concepts.QsvtCore.ApproxToolkit.erf
          (η * Real.sinh (h * cutoff Y h) / (2 * c))) ≤
      Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant n b c d *
        Real.exp (-(η / (2 * c)) ^ 2 * Real.sinh (h * cutoff Y h) ^ 2) := by
  refine ⟨(actual_tail_erfc n b c d hb hc H L hH hL hT hη hh _ hlarge).2, ?_⟩
  have he := Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.erfc_le_exp hlarge
  have heq : η * Real.sinh (h * cutoff Y h) / (2 * c) =
      η / (2 * c) * Real.sinh (h * cutoff Y h) := by ring
  rw [heq]
  have hexp : -(η / (2 * c) * Real.sinh (h * cutoff Y h)) ^ 2 =
      -(η / (2 * c)) ^ 2 * Real.sinh (h * cutoff Y h) ^ 2 := by ring
  rw [hexp] at he
  exact mul_le_mul_of_nonneg_left he
    (Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant_pos n b c d hb hc).le

def window (c η u : ℝ) : ℝ := max 1 (Real.arsinh (2 * c / η * u))

theorem rounded_sinh_ge {c η h : ℝ} (hc : 0 < c) (hη : 0 < η) (hh : 0 < h) (u : ℝ) :
    u ≤ η / (2 * c) * Real.sinh (h * cutoff (window c η u) h) := by
  have hY : Real.arsinh (2 * c / η * u) ≤ h * cutoff (window c η u) h :=
    (le_max_right (1 : ℝ) _).trans (le_radius (window c η u) hh)
  have hs := Real.sinh_le_sinh.mpr hY
  rw [Real.sinh_arsinh] at hs
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ η / (2 * c) by positivity)
  have he : η / (2 * c) * (2 * c / η * u) = u := by field_simp
  simpa only [he] using! hm

theorem actual_norm_summable (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η h : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (hh : 0 < h) :
    Summable (fun q : ℤ => ‖transformed n b c d T η H L ((h * (q : ℝ) : ℝ) : ℂ)‖) := by
  let N := cutoff (window c η 1) h
  have hs := (actual_tail_erfc n b c d hb hc H L hH hL hT hη hh N
    (rounded_sinh_ge hc hη hh 1)).1
  exact (Finset.Icc (-(N : ℤ)) N).summable_compl_iff.mp hs

theorem mesh_sub_finite_le (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η h : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (hh : 0 < h) (N : ℕ) :
    ‖h • (∑' q : ℤ, transformed n b c d T η H L ((h * (q : ℝ) : ℝ) : ℂ)) -
      finiteIdeal n b c d T η h H L N‖ ≤ latticeTail n b c d T η h H L N := by
  let F : ℤ → Matrix ι ι ℂ := fun q => transformed n b c d T η H L ((h * (q : ℝ) : ℝ) : ℂ)
  let s := Finset.Icc (-(N : ℤ)) N
  have hFn : Summable (fun q => ‖F q‖) := actual_norm_summable n b c d hb hc H L hH hL hT hη hh
  have hF : Summable F := hFn.of_norm
  have he := hF.sum_add_tsum_subtype_compl s
  have hid : (∑' q, F q) - ∑ q ∈ s, F q = ∑' q : {q // q ∉ s}, F q := by
    exact sub_eq_iff_eq_add.mpr (he.symm.trans (add_comm _ _))
  change ‖h • (∑' q, F q) - h • (∑ q ∈ s, F q)‖ ≤ _
  rw [← smul_sub, hid, norm_smul, Real.norm_of_nonneg hh.le]
  exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hFn.subtype _)) hh.le

theorem finite_error_split (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η h : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (hh : 0 < h) (N : ℕ) :
    ‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) - finiteIdeal n b c d T η h H L N‖ ≤
      ‖(∫ x : ℝ, transformed n b c d T η H L (x : ℂ)) -
        h • (∑' q : ℤ, transformed n b c d T η H L ((h * (q : ℝ) : ℝ) : ℂ))‖ +
        latticeTail n b c d T η h H L N := by
  have hi := (actual_integral_change n b c d T hη H L).symm
  calc
    _ = ‖(∫ x : ℝ, transformed n b c d T η H L (x : ℂ)) - finiteIdeal n b c d T η h H L N‖ :=
      congrArg (fun A : Matrix ι ι ℂ => ‖A - finiteIdeal n b c d T η h H L N‖) hi
    _ ≤ _ := by
      let A : Matrix ι ι ℂ := ∫ x : ℝ, transformed n b c d T η H L (x : ℂ)
      let S : Matrix ι ι ℂ := h • (∑' q : ℤ, transformed n b c d T η H L ((h * (q : ℝ) : ℝ) : ℂ))
      let W : Matrix ι ι ℂ := finiteIdeal n b c d T η h H L N
      have htri : ‖A - W‖ ≤ ‖A - S‖ + ‖S - W‖ := norm_sub_le_norm_sub_add_norm_sub A S W
      have htail : ‖S - W‖ ≤ latticeTail n b c d T η h H L N :=
        mesh_sub_finite_le n b c d hb hc H L hH hL hT hη hh N
      have hsum : ‖A - S‖ + ‖S - W‖ ≤ ‖A - S‖ + latticeTail n b c d T η h H L N :=
        _root_.add_le_add (le_refl ‖A - S‖) htail
      exact htri.trans hsum

theorem selected_tail_budget (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T η h ε : ℝ} (hT : 0 ≤ T) (hη : 0 < η) (hh : 0 < h) (hε : 0 < ε) :
    latticeTail n b c d T η h H L
      (cutoff (window c η (Real.sqrt
        (Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailLog
          (Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant n b c d) ε))) h) ≤ ε := by
  let C := Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant n b c d
  let ell := Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailLog C ε
  let Y := window c η (Real.sqrt ell)
  let r := η / (2 * c) * Real.sinh (h * cutoff Y h)
  have hC : 0 < C :=
      Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.tailConstant_pos n b c d hb hc
  have hell : 1 ≤ ell := le_max_left _ _
  have hsqrt : 1 ≤ Real.sqrt ell := by simpa using! Real.sqrt_le_sqrt hell
  have hr : Real.sqrt ell ≤ r := rounded_sinh_ge hc hη hh (Real.sqrt ell)
  have hsq : ell ≤ r ^ 2 := by
    have hs := mul_self_le_mul_self (Real.sqrt_nonneg ell) hr
    nlinarith [Real.sq_sqrt (show 0 ≤ ell by linarith)]
  have ht := actual_tail_bounds n b c d hb hc H L hH hL hT hη hh Y (hsqrt.trans hr)
  have heq : -(η / (2 * c)) ^ 2 * Real.sinh (h * cutoff Y h) ^ 2 = -r ^ 2 := by
    dsimp [r]
    ring
  rw [heq] at ht
  exact (ht.1.trans ht.2).trans ((mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg hsq)) hC.le).trans
      (Qatlib.Papers.CommutLCHS26.QuadratureCmp.TailBudget.exp_tailLog_budget hC hε))

theorem physical_radius_max (η Y h : ℝ) (hη : 0 ≤ η) (hh : 0 ≤ h) :
    IsGreatest {r : ℝ | ∃ q ∈ Finset.Icc (-(cutoff Y h : ℤ)) (cutoff Y h),
      r = |η * Real.sinh (h * (q : ℝ))|} (η * Real.sinh (h * cutoff Y h)) := by
  have hN : 0 ≤ h * (cutoff Y h : ℝ) := mul_nonneg hh (Nat.cast_nonneg _)
  constructor
  · refine ⟨(cutoff Y h : ℤ), by simp, ?_⟩
    simp only [Int.cast_natCast, abs_of_nonneg (mul_nonneg hη (Real.sinh_nonneg_iff.mpr hN))]
  · rintro r ⟨q, hq, rfl⟩
    rw [abs_mul, abs_of_nonneg hη, Real.abs_sinh]
    exact mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr (node_le_radius Y h hh q hq)) hη

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
