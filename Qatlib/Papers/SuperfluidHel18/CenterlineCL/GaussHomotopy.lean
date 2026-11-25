/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussAreaFlux

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Smooth homotopy invariance of the Gauss linking integral

[Kedia2018SuperfluidHelicity], Sec. II and Eq. (6),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
A smooth disjoint family of closed curves determines a smooth map from
the three parameters into the sphere of unit chords. The divergence
theorem cancels the two pairs of periodic faces and equates the Gauss
integrals on the remaining faces. This gives invariance under smooth
disjoint homotopies while retaining the analytic definition of the
linking integral.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open scoped Real

local notation "HomotopyVec" => (Fin 3 → ℝ)
local notation "homotopyBasis" => (fun i : Fin 3 => (Pi.single i (1 : ℝ) : HomotopyVec))

/-- The flux associated to a periodic sphere map has the same period as the map. -/
private theorem areaFlux_period {n : HomotopyVec → HomotopyVec} {d : HomotopyVec}
    (h : ∀ x, n (x + d) = n x) (x : HomotopyVec) : gaussAreaFlux n (x + d) = gaussAreaFlux n x := by
  have heq : (fun y => n (y + d)) = n := funext h
  have hd : fderiv ℝ n (x + d) = fderiv ℝ n x := by
    rw [← fderiv_comp_add_right d, heq]
  have hpartial : gaussMapPartial n (x + d) = gaussMapPartial n x := by
    funext i
    unfold gaussMapPartial
    rw [hd]
  simp only [gaussAreaFlux, hpartial, h x]

/-- The two faces at a Cartesian coordinate differ by a translation. -/
private theorem insertNth_sub_faces (i : Fin 3) (d : ℝ) (q : Fin 2 → ℝ) :
    Fin.insertNth i d q = Fin.insertNth i 0 q + d • homotopyBasis i := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [Fin.insertNth_apply_succAbove, Fin.succAbove_ne]

/-- The oriented spherical area through the face with fixed third coordinate. -/
noncomputable def gaussAreaFace (n : HomotopyVec → HomotopyVec) (u : ℝ) : ℝ :=
  ∫ q in Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 2 * π),
    gaussAreaFlux n (Fin.insertNth 2 u q) 2

/-- The two faces transverse to the third coordinate have equal oriented
areas when a smooth sphere map is periodic in the first two coordinates. -/
theorem gaussAreaFace_eq_of_periodic {n : HomotopyVec → HomotopyVec} (hn : ContDiff ℝ 2 n)
    (hu : ∀ x, dot3 (n x) (n x) = 1)
    (hperiod : ∀ i : Fin 3, i ≠ 2 → ∀ x, n (x + (2 * π) • homotopyBasis i) = n x)
    {a b : ℝ} (hab : a ≤ b) : gaussAreaFace n a = gaussAreaFace n b := by
  let lo : HomotopyVec := ![0, 0, a]
  let hi : HomotopyVec := ![2 * π, 2 * π, b]
  have hle : lo ≤ hi := by
    intro i
    fin_cases i
    · exact Real.two_pi_pos.le
    · exact Real.two_pi_pos.le
    · exact hab
  let f (i : Fin 3) (x : HomotopyVec) := gaussAreaFlux n x i
  let f' (i : Fin 3) (x : HomotopyVec) := fderiv ℝ (f i) x
  have hd (i : Fin 3) : Differentiable ℝ (f i) :=
    (show HomotopyVec →L[ℝ] ℝ from ContinuousLinearMap.proj i).differentiable.comp
      (differentiable_gaussAreaFlux hn)
  have hz : (fun x : HomotopyVec => ∑ i : Fin 3, f' i x (homotopyBasis i)) = fun _ => 0 :=
    funext (gaussAreaFlux_divergence hn hu)
  have hiInt : IntegrableOn (fun x : HomotopyVec => ∑ i : Fin 3, f' i x (homotopyBasis i)) (Set.Icc lo hi) := by
    rw [hz]
    exact integrable_zero _ _ _
  have hFlux := integral_divergence_of_hasFDerivAt_off_countable' lo hi hle
    f f' ∅ Set.countable_empty (fun i => (hd i).continuous.continuousOn)
    (fun x _ i => (hd i x).hasFDerivAt) hiInt
  have hSide (i : Fin 3) (hi2 : i ≠ 2)
      (hlo : lo i = 0) (hhi : hi i = 2 * π) :
      (∫ q in Set.Icc (lo ∘ i.succAbove) (hi ∘ i.succAbove), f i (i.insertNth (hi i) q)) =
        ∫ q in Set.Icc (lo ∘ i.succAbove) (hi ∘ i.succAbove), f i (i.insertNth (lo i) q) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro q _
    change f i (i.insertNth (hi i) q) = f i (i.insertNth (lo i) q)
    rw [hlo, hhi, insertNth_sub_faces]
    exact congrFun (areaFlux_period (hperiod i hi2) _) i
  rw [hz, integral_zero, Fin.sum_univ_three, hSide 0 (by decide) rfl rfl,
    hSide 1 (by decide) rfl rfl, sub_self, sub_self, zero_add, zero_add] at hFlux
  have hlo : lo ∘ (2 : Fin 3).succAbove = (fun _ : Fin 2 => (0 : ℝ)) := by
    funext i
    fin_cases i <;> rfl
  have hhi : hi ∘ (2 : Fin 3).succAbove = (fun _ : Fin 2 => 2 * π) := by
    funext i
    fin_cases i <;> rfl
  rw [hlo, hhi] at hFlux
  exact (sub_eq_zero.mp hFlux.symm).symm

/-- The unit chord of the two curves with third coordinate the homotopy
time and first two coordinates the curve parameters. -/
noncomputable def gaussHomotopyDirection (Γ₁ Γ₂ : ℝ × ℝ → HomotopyVec) (p : HomotopyVec) : HomotopyVec :=
  gaussDirection (fun s => Γ₁ (p 2, s)) (fun t => Γ₂ (p 2, t)) (p 0) (p 1)

/-- The unit-chord map of disjoint twice continuously differentiable
families is itself twice continuously differentiable. -/
private theorem contDiff_gaussHomotopyDirection {Γ₁ Γ₂ : ℝ × ℝ → HomotopyVec}
    (h₁ : ContDiff ℝ 2 Γ₁) (h₂ : ContDiff ℝ 2 Γ₂)
    (hDisj : ∀ u s t, Γ₁ (u, s) ≠ Γ₂ (u, t)) :
    ContDiff ℝ 2 (gaussHomotopyDirection Γ₁ Γ₂) := by
  let chord := fun p : HomotopyVec => Γ₁ (p 2, p 0) - Γ₂ (p 2, p 1)
  have hProj (i : Fin 3) : ContDiff ℝ 2 (fun p : HomotopyVec => p i) :=
    (show HomotopyVec →L[ℝ] ℝ from ContinuousLinearMap.proj i).contDiff
  have hc : ContDiff ℝ 2 chord :=
    (h₁.comp ((hProj 2).prodMk (hProj 0))).sub (h₂.comp ((hProj 2).prodMk (hProj 1)))
  have hLength : ContDiff ℝ 2 (fun p => euclideanLength (chord p)) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    have hOuter : ContDiffAt ℝ 2 euclideanLength (chord p) :=
      contDiffAt_euclideanLength (sub_ne_zero.mpr (hDisj (p 2) (p 0) (p 1)))
    exact (show ContDiffAt ℝ 2 (euclideanLength ∘ chord) p from hOuter.comp p hc.contDiffAt)
  have hNe (p : HomotopyVec) : euclideanLength (chord p) ≠ 0 :=
    ((norm_pos_iff.mpr (sub_ne_zero.mpr (hDisj (p 2) (p 0) (p 1)))).trans_le
      (norm_le_euclideanLength _)).ne'
  exact (hLength.inv hNe).smul hc

/-- The curve-parameter line in the first coordinate has first unit vector as derivative. -/
private theorem derivative_first_section (s t u : ℝ) :
    HasDerivAt (fun v : ℝ => (![v, t, u] : HomotopyVec)) (homotopyBasis 0) s := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · exact hasDerivAt_id s
  · exact hasDerivAt_const s t
  · exact hasDerivAt_const s u

/-- The curve-parameter line in the second coordinate has second unit vector as derivative. -/
private theorem derivative_second_section (s t u : ℝ) :
    HasDerivAt (fun v : ℝ => (![s, v, u] : HomotopyVec)) (homotopyBasis 1) t := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · exact hasDerivAt_const t s
  · exact hasDerivAt_id t
  · exact hasDerivAt_const t u

/-- The density on a time face is exactly the Gauss kernel times its
normalization constant. -/
private theorem gaussHomotopy_face_kernel {Γ₁ Γ₂ : ℝ × ℝ → HomotopyVec}
    (h₁ : ContDiff ℝ 2 Γ₁) (h₂ : ContDiff ℝ 2 Γ₂)
    (hDisj : ∀ u s t, Γ₁ (u, s) ≠ Γ₂ (u, t)) (u s t : ℝ) :
    gaussAreaFlux (gaussHomotopyDirection Γ₁ Γ₂) ![s, t, u] 2 / (4 * π) =
      gaussKernel (fun s => Γ₁ (u, s)) (fun t => Γ₂ (u, t)) s t := by
  let n := gaussHomotopyDirection Γ₁ Γ₂
  have hd : HasFDerivAt n (fderiv ℝ n ![s, t, u]) ![s, t, u] :=
    ((contDiff_gaussHomotopyDirection h₁ h₂ hDisj).differentiable (by norm_num)
      ![s, t, u]).hasFDerivAt
  have h0 := (hd.comp_hasDerivAt s (derivative_first_section s t u)).deriv
  have h1 := (hd.comp_hasDerivAt t (derivative_second_section s t u)).deriv
  change deriv (fun v => gaussDirection (fun w => Γ₁ (u, w)) (fun w => Γ₂ (u, w)) v t) s =
    gaussMapPartial n ![s, t, u] 0 at h0
  change deriv (fun v => gaussDirection (fun w => Γ₁ (u, w)) (fun w => Γ₂ (u, w)) s v) t =
    gaussMapPartial n ![s, t, u] 1 at h1
  change dot3 (cross3 (gaussMapPartial n ![s, t, u] 1) (gaussMapPartial n ![s, t, u] 0))
    (gaussDirection (fun w => Γ₁ (u, w)) (fun w => Γ₂ (u, w)) s t) / (4 * π) = _
  rw [← h0, ← h1]
  have hSec (v : ℝ) : DifferentiableAt ℝ (fun w : ℝ => (u, w)) v := by fun_prop
  exact gaussDirection_area_density _ _ s t
    ((h₁.differentiable (by norm_num)).differentiableAt.comp s (hSec s))
    ((h₂.differentiable (by norm_num)).differentiableAt.comp t (hSec t)) (hDisj u s t)

/-- Inserting the last coordinate produces the ordered tuple of the
two curve parameters and the homotopy time. -/
private theorem insertNth_time (u : ℝ) (q : Fin 2 → ℝ) :
    Fin.insertNth 2 u q = (![q 0, q 1, u] : HomotopyVec) := by
  funext j
  fin_cases j <;> rfl

/-- The Lebesgue area on the time face agrees with the measure used to
define the original Gauss integral. -/
private theorem gaussHomotopyFace_eq {Γ₁ Γ₂ : ℝ × ℝ → HomotopyVec}
    (h₁ : ContDiff ℝ 2 Γ₁) (h₂ : ContDiff ℝ 2 Γ₂)
    (hDisj : ∀ u s t, Γ₁ (u, s) ≠ Γ₂ (u, t)) (u : ℝ) :
    gaussAreaFace (gaussHomotopyDirection Γ₁ Γ₂) u / (4 * π) =
      gaussLinking (fun s => Γ₁ (u, s)) (fun t => Γ₂ (u, t)) := by
  let equivalence : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow
  have hpre : equivalence ⁻¹' gaussDomain =
      Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 2 * π) := by
    ext q
    change ((q 0, q 1) : ℝ × ℝ) ∈ gaussDomain ↔ _
    simp only [gaussDomain, Set.mem_prod, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two]
    tauto
  have hMeasure : gaussMeasure = (volume : Measure (ℝ × ℝ)).restrict gaussDomain := by
    rw [gaussMeasure, Measure.prod_restrict]
    rfl
  unfold gaussAreaFace gaussLinking
  rw [hMeasure, div_eq_mul_inv, ← integral_mul_const, ← hpre]
  have hp := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    equivalence.measurableEmbedding
    (fun p => gaussKernel (fun s => Γ₁ (u, s)) (fun t => Γ₂ (u, t)) p.1 p.2) gaussDomain
  change ∫ q in equivalence ⁻¹' gaussDomain,
    gaussKernel (fun s => Γ₁ (u, s)) (fun t => Γ₂ (u, t)) (q 0) (q 1) =
      ∫ p in gaussDomain, gaussKernel (fun s => Γ₁ (u, s)) (fun t => Γ₂ (u, t)) p.1 p.2 at hp
  rw [← hp]
  apply setIntegral_congr_fun (equivalence.measurable
    (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet gaussDomain))
  intro q _
  change gaussAreaFlux (gaussHomotopyDirection Γ₁ Γ₂) (Fin.insertNth 2 u q) 2 * (4 * π)⁻¹ =
    gaussKernel (fun s => Γ₁ (u, s)) (fun t => Γ₂ (u, t)) (q 0) (q 1)
  rw [← div_eq_mul_inv, insertNth_time, gaussHomotopy_face_kernel h₁ h₂ hDisj]

/-- The actual Gauss linking integral is constant along a smooth family
of disjoint closed curves, using their periodic parameters with period
`2π`. The theorem applies to any two real homotopy times. -/
theorem gaussLinking_eq_of_smooth_homotopy (Γ₁ Γ₂ : ℝ × ℝ → HomotopyVec)
    (h₁ : ContDiff ℝ 2 Γ₁) (h₂ : ContDiff ℝ 2 Γ₂)
    (hDisj : ∀ u s t, Γ₁ (u, s) ≠ Γ₂ (u, t))
    (hP₁ : ∀ u, Function.Periodic (fun s => Γ₁ (u, s)) (2 * π))
    (hP₂ : ∀ u, Function.Periodic (fun t => Γ₂ (u, t)) (2 * π))
    (a b : ℝ) :
    gaussLinking (fun s => Γ₁ (a, s)) (fun t => Γ₂ (a, t)) =
      gaussLinking (fun s => Γ₁ (b, s)) (fun t => Γ₂ (b, t)) := by
  let n := gaussHomotopyDirection Γ₁ Γ₂
  have hn := contDiff_gaussHomotopyDirection h₁ h₂ hDisj
  have hu (p : HomotopyVec) : dot3 (n p) (n p) = 1 :=
    gaussDirection_dot_self _ _ _ _ (hDisj (p 2) (p 0) (p 1))
  have hp (i : Fin 3) (hi : i ≠ 2) (p : HomotopyVec) :
      n (p + (2 * π) • homotopyBasis i) = n p := by
    fin_cases i
    · change gaussDirection (fun s => Γ₁ (p 2 + (2 * π) * 0, s))
        (fun t => Γ₂ (p 2 + (2 * π) * 0, t)) (p 0 + (2 * π) * 1) (p 1 + (2 * π) * 0) = _
      simp only [mul_zero, add_zero, mul_one, gaussDirection, hP₁ (p 2) (p 0), n,
        gaussHomotopyDirection]
    · change gaussDirection (fun s => Γ₁ (p 2 + (2 * π) * 0, s))
        (fun t => Γ₂ (p 2 + (2 * π) * 0, t)) (p 0 + (2 * π) * 0) (p 1 + (2 * π) * 1) = _
      simp only [mul_zero, add_zero, mul_one, gaussDirection, hP₂ (p 2) (p 1), n,
        gaussHomotopyDirection]
    · exact (hi rfl).elim
  have h : gaussAreaFace n a = gaussAreaFace n b := by
    rcases le_total a b with hab | hba
    · exact gaussAreaFace_eq_of_periodic hn hu hp hab
    · exact (gaussAreaFace_eq_of_periodic hn hu hp hba).symm
  rw [← gaussHomotopyFace_eq h₁ h₂ hDisj a, ← gaussHomotopyFace_eq h₁ h₂ hDisj b]
  exact congrArg (· / (4 * π)) h

/-- Smoothness and disjointness suffice on the closed time interval between
the two endpoints. A smooth change of time stays in that interval for
every real parameter and attains both endpoints. -/
theorem gaussLinking_eq_on_interval (Γ₁ Γ₂ : ℝ × ℝ → HomotopyVec) {a b : ℝ} (hab : a ≤ b)
    (h₁ : ContDiffOn ℝ 2 Γ₁ (Set.Icc a b ×ˢ Set.univ))
    (h₂ : ContDiffOn ℝ 2 Γ₂ (Set.Icc a b ×ˢ Set.univ))
    (hDisj : ∀ u ∈ Set.Icc a b, ∀ s t, Γ₁ (u, s) ≠ Γ₂ (u, t))
    (hP₁ : ∀ u ∈ Set.Icc a b, Function.Periodic (fun s => Γ₁ (u, s)) (2 * π))
    (hP₂ : ∀ u ∈ Set.Icc a b, Function.Periodic (fun t => Γ₂ (u, t)) (2 * π)) :
    gaussLinking (fun s => Γ₁ (a, s)) (fun t => Γ₂ (a, t)) =
      gaussLinking (fun s => Γ₁ (b, s)) (fun t => Γ₂ (b, t)) := by
  let time (u : ℝ) := a + (b - a) * ((1 + Real.sin u) / 2)
  let warp (p : ℝ × ℝ) := (time p.1, p.2)
  have hTime (u : ℝ) : time u ∈ Set.Icc a b := by
    have hδ := sub_nonneg.mpr hab
    have hLow : 0 ≤ (1 + Real.sin u) / 2 := by linarith [Real.neg_one_le_sin u]
    have hHigh : 0 ≤ 1 - (1 + Real.sin u) / 2 := by linarith [Real.sin_le_one u]
    exact ⟨by dsimp [time]; linarith [mul_nonneg hδ hLow],
      by dsimp [time]; nlinarith [mul_nonneg hδ hHigh]⟩
  have hm : Set.MapsTo warp Set.univ (Set.Icc a b ×ˢ (Set.univ : Set ℝ)) :=
    fun p _ => ⟨hTime p.1, Set.mem_univ p.2⟩
  have hWarp : ContDiff ℝ 2 warp := by
    dsimp only [warp, time]
    fun_prop
  have h := gaussLinking_eq_of_smooth_homotopy (Γ₁ ∘ warp) (Γ₂ ∘ warp)
    (contDiffOn_univ.mp (h₁.comp hWarp.contDiffOn hm))
    (contDiffOn_univ.mp (h₂.comp hWarp.contDiffOn hm))
    (fun u => hDisj (time u) (hTime u))
    (fun u => hP₁ (time u) (hTime u)) (fun u => hP₂ (time u) (hTime u))
    (-(π / 2)) (π / 2)
  have ha : time (-(π / 2)) = a := by simp [time, Real.sin_neg, Real.sin_pi_div_two]
  have hb : time (π / 2) = b := by simp [time, Real.sin_pi_div_two]
  simpa only [Function.comp_apply, warp, ha, hb] using h

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
