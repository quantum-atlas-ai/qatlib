/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.DysonPiecewise
import Qatlib.Foundations.CbmdAnalysis.Core.DysonUniqueness
import Mathlib.Topology.Piecewise
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# Assembling piecewise matrix evolutions

`assembledField` and `assembledDyson` glue interval fields and their Dyson paths along a finite
partition. The assembled path is continuous and locally Lipschitz, hence absolutely continuous
on every compact interval, and satisfies the assembled differential equation almost everywhere.

The module proves uniqueness for absolutely continuous solutions, identifies the endpoint with
`dysonPiecewise`, and expresses its growth bound using the integral norm of the assembled field.
This supplies piecewise input data for the contour-based matrix decomposition in [WangEtAl2026].

## Main statements

* `assembledDyson_unique_ae`: proves uniqueness for the almost-everywhere evolution equation.
* `assembledDyson_norm_le`: bounds the endpoint by the assembled integral budget.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section
namespace CBMD

open Set MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology Classical NNReal

/-- The field obtained by recursively selecting the interval field after each partition time,
starting from the zero field. -/
def assembledField {E : Type*} [Zero E]
    (F : ℕ → ℝ → E) (τ : ℕ → ℝ) : ℕ → ℝ → E
  | 0, _ => 0
  | n + 1, t => if t < τ n then assembledField F τ n t else F n t

/-- The path obtained by recursively joining the interval Dyson paths, retaining the preceding
path at and before each joining time. -/
def assembledDyson {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) : ℕ → ℂ → ℝ → Matrix I I ℂ
  | 0, _, _ => 1
  | n + 1, z, t => if t ≤ τ n then assembledDyson H L τ n z t
      else dysonPiecewisePath H L τ n z t

/-- At `τ n`, the assembled path equals the product of the first `n` interval propagators for a
strictly increasing partition. -/
theorem assembledDyson_endpoint {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n : ℕ) (z : ℂ) : assembledDyson H L τ n z (τ n) = dysonPiecewise H L τ n z := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [assembledDyson, not_le.mpr (hτ (Nat.lt_succ_self n)), ↓reduceIte,
      dysonPiecewisePath, dysonPiecewise]

/-- For a monotone partition, the assembled path equals the identity at `τ 0`. -/
@[simp] theorem assembledDyson_initial {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (n : ℕ) (z : ℂ) : assembledDyson H L τ n z (τ 0) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [assembledDyson, hτ (Nat.zero_le n), ↓reduceIte, ih]

/-- Inside partition cell `j < n`, the assembled field equals `F j`. -/
theorem assembledField_eq_on_piece {E : Type*} [Zero E]
    (F : ℕ → ℝ → E) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (n j : ℕ) (hj : j < n) {t : ℝ} (ht : t ∈ Ioo (τ j) (τ (j + 1))) :
    assembledField F τ n t = F j t := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hjn : j < n
    · have hlt : t < τ n := ht.2.trans_le (hτ (by omega))
      simp only [assembledField, hlt, ↓reduceIte]
      exact ih hjn
    · have he : j = n := by omega
      subst j
      simp only [assembledField, not_lt.mpr ht.1.le, ↓reduceIte]

/-- On the closed partition cell `j < n`, the assembled path equals `dysonPiecewisePath H L τ j
z` for a strictly increasing partition. -/
theorem assembledDyson_eq_on_piece {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n j : ℕ) (hj : j < n) (z : ℂ) {t : ℝ} (ht : t ∈ Icc (τ j) (τ (j + 1))) :
    assembledDyson H L τ n z t = dysonPiecewisePath H L τ j z t := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hjn : j < n
    · have hle : t ≤ τ n := ht.2.trans (hτ.monotone (by omega))
      simp only [assembledDyson, hle, ↓reduceIte]
      exact ih hjn
    · have he : j = n := by omega
      subst j
      by_cases he : t = τ n
      · subst t
        simp only [assembledDyson, le_refl, ↓reduceIte,
          assembledDyson_endpoint H L τ hτ, dysonPiecewisePath,
          dysonPropagator_self, one_mul]
      · have hlt : τ n < t := lt_of_le_of_ne ht.1 (Ne.symm he)
        simp only [assembledDyson, not_le.mpr hlt, ↓reduceIte]

/-- Continuous interval fields and a strictly increasing partition give a continuous assembled
Dyson path. -/
theorem assembledDyson_continuous {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n : ℕ) (z : ℂ) : Continuous (assembledDyson H L τ n z) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hp : Continuous (dysonPiecewisePath H L τ n z) :=
      continuous_iff_continuousAt.mpr fun t =>
        (dysonPiecewisePath_hasDerivAt H L τ n (hH n) (hL n) z t).continuousAt
    apply Continuous.if _ ih hp
    intro t ht
    have he : t = τ n := by
      change t ∈ frontier (Iic (τ n)) at ht
      simpa only [frontier_Iic, mem_singleton_iff] using ht
    subst t
    simp only [assembledDyson_endpoint H L τ hτ, dysonPiecewisePath,
      dysonPropagator_self, one_mul]

/-- Inside a partition cell with continuous fields, the assembled path satisfies the evolution
equation for the assembled `H` and `L`. -/
theorem assembledDyson_hasDerivAt_piece {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n j : ℕ) (hj : j < n) (hH : Continuous (H j)) (hL : Continuous (L j))
    (z : ℂ) {t : ℝ} (ht : t ∈ Ioo (τ j) (τ (j + 1))) :
    HasDerivAt (assembledDyson H L τ n z)
      (-(Complex.I • (assembledField H τ n t + z • assembledField L τ n t) *
        assembledDyson H L τ n z t)) t := by
  rw [assembledField_eq_on_piece H τ hτ.monotone n j hj ht,
    assembledField_eq_on_piece L τ hτ.monotone n j hj ht,
    assembledDyson_eq_on_piece H L τ hτ n j hj z ⟨ht.1.le, ht.2.le⟩]
  apply (dysonPiecewisePath_hasDerivAt H L τ j hH hL z t).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
  exact assembledDyson_eq_on_piece H L τ hτ n j hj z ⟨hu.1.le, hu.2.le⟩

/-- A point between the first and last partition times that differs from every partition time
lies in an open partition cell. -/
private theorem exists_partition_cell (τ : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Icc (τ 0) (τ n)) (hne : ∀ j ≤ n, t ≠ τ j) :
    ∃ j < n, t ∈ Ioo (τ j) (τ (j + 1)) := by
  induction n with
  | zero => exact False.elim ((hne 0 le_rfl) (le_antisymm ht.2 ht.1))
  | succ n ih =>
    by_cases hn : t < τ n
    · obtain ⟨j, hj, hc⟩ := ih ⟨ht.1, hn.le⟩ (fun j hj => hne j (by omega))
      exact ⟨j, by omega, hc⟩
    · exact ⟨n, Nat.lt_succ_self n, lt_of_le_of_ne (not_lt.mp hn) (Ne.symm (hne n (by omega))),
        lt_of_le_of_ne ht.2 (hne (n + 1) le_rfl)⟩

/-- For continuous interval fields and a strictly increasing partition, the assembled Dyson path
satisfies its matrix evolution equation almost everywhere on the partition interval. -/
theorem assembledDyson_hasDerivAt_ae {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n : ℕ) (z : ℂ) :
    ∀ᵐ t : ℝ, t ∈ Icc (τ 0) (τ n) →
      HasDerivAt (assembledDyson H L τ n z)
        (-(Complex.I • (assembledField H τ n t + z • assembledField L τ n t) *
          assembledDyson H L τ n z t)) t := by
  have hnull := ((Finset.range (n + 1)).image τ).finite_toSet.countable.ae_notMem volume
  filter_upwards [hnull] with t ht hmem
  have hne (j : ℕ) (hj : j ≤ n) : t ≠ τ j := by
    intro he
    apply ht
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨j, by omega, he.symm⟩
  obtain ⟨j, hj, hc⟩ := exists_partition_cell τ n t hmem hne
  exact assembledDyson_hasDerivAt_piece H L τ hτ n j hj (hH j) (hL j) z hc

/-- The assembled field is interval integrable on each partition cell when all interval fields
are continuous and the partition is monotone. -/
theorem assembledField_intervalIntegrable_piece {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℕ → ℝ → E) (hF : ∀ j, Continuous (F j))
    (τ : ℕ → ℝ) (hτ : Monotone τ) (n j : ℕ) (hj : j < n) :
    IntervalIntegrable (assembledField F τ n) volume (τ j) (τ (j + 1)) := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hτ (Nat.le_succ j))]
  have hi := (hF j).intervalIntegrable (μ := volume) (τ j) (τ (j + 1))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (hτ (Nat.le_succ j))] at hi
  exact hi.congr_fun (fun t ht => (assembledField_eq_on_piece F τ hτ n j hj ht).symm)
    measurableSet_Ioo

/-- The integral of an assembled continuous field over a monotone partition equals the sum of
its interval integrals. -/
theorem assembledField_integral_eq_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℕ → ℝ → E) (hF : ∀ j, Continuous (F j))
    (τ : ℕ → ℝ) (hτ : Monotone τ) (n : ℕ) :
    (∫ t in τ 0..τ n, assembledField F τ n t) =
      ∑ j ∈ Finset.range n, ∫ t in τ j..τ (j + 1), F j t := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals
    (fun j hj => assembledField_intervalIntegrable_piece F hF τ hτ n j hj)]
  apply Finset.sum_congr rfl
  intro j hj
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (τ (j + 1))] with t hne ht
  rw [uIoc_of_le (hτ (Nat.le_succ j))] at ht
  exact assembledField_eq_on_piece F τ hτ n j (Finset.mem_range.mp hj)
    ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩

/-- Taking the norm of an assembled field is the same as assembling the norms of its interval
fields. -/
private theorem assembledField_norm {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → ℝ → E) (τ : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    ‖assembledField F τ n t‖ = assembledField (fun j u => ‖F j u‖) τ n t := by
  induction n with
  | zero => exact norm_zero
  | succ n ih =>
    simp only [assembledField]
    split_ifs <;> simp only [ih]

/-- The integral norm of the assembled matrix field equals the piecewise Dyson budget for
continuous fields and a monotone partition. -/
theorem assembledField_norm_integral {I : Type} [Fintype I] [DecidableEq I]
    (L : ℕ → ℝ → Matrix I I ℂ) (hL : ∀ j, Continuous (L j))
    (τ : ℕ → ℝ) (hτ : Monotone τ) (n : ℕ) :
    (∫ t in τ 0..τ n, ‖assembledField L τ n t‖) = dysonPiecewiseBudget L τ n := by
  simp_rw [assembledField_norm]
  exact assembledField_integral_eq_sum (fun j u => ‖L j u‖) (fun j => (hL j).norm) τ hτ n

/-- Two Lipschitz functions that agree at the switching point glue to a Lipschitz function with
the sum of their Lipschitz constants. -/
private theorem lipschitzOn_if_le {E : Type*} [PseudoMetricSpace E]
    {f g : ℝ → E} {a b c : ℝ} {Kf Kg : ℝ≥0}
    (hf : LipschitzOnWith Kf f (Icc a b)) (hg : LipschitzOnWith Kg g (Icc a b))
    (hjoin : f c = g c) :
    LipschitzOnWith (Kf + Kg) (fun t => if t ≤ c then f t else g t) (Icc a b) := by
  let h := fun t => if t ≤ c then f t else g t
  have hfwd (x : ℝ) (hx : x ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      dist (h x) (h y) ≤ (Kf + Kg : ℝ≥0) * dist x y := by
    by_cases hyc : y ≤ c
    · have hxc := hxy.trans hyc
      simp only [h, hxc, hyc, ↓reduceIte]
      exact (hf.dist_le_mul x hx y hy).trans (by
        exact mul_le_mul_of_nonneg_right (by simp) dist_nonneg)
    · by_cases hxc : x ≤ c
      · have hcy : c ≤ y := (lt_of_not_ge hyc).le
        have hc : c ∈ Icc a b := ⟨hx.1.trans hxc, hcy.trans hy.2⟩
        have hdist₁ : dist x c ≤ dist x y := by
          rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxc),
            abs_of_nonpos (sub_nonpos.mpr hxy)]
          linarith
        have hdist₂ : dist c y ≤ dist x y := by
          rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hcy),
            abs_of_nonpos (sub_nonpos.mpr hxy)]
          linarith
        simp only [h, hxc, hyc, ↓reduceIte]
        calc
          _ ≤ dist (f x) (f c) + dist (g c) (g y) := by rw [hjoin]; exact dist_triangle _ _ _
          _ ≤ Kf * dist x c + Kg * dist c y := add_le_add
            (hf.dist_le_mul x hx c hc) (hg.dist_le_mul c hc y hy)
          _ ≤ Kf * dist x y + Kg * dist x y := add_le_add
            (mul_le_mul_of_nonneg_left hdist₁ Kf.coe_nonneg)
            (mul_le_mul_of_nonneg_left hdist₂ Kg.coe_nonneg)
          _ = _ := by simp only [NNReal.coe_add]; ring
      · simp only [h, hxc, hyc, ↓reduceIte]
        exact (hg.dist_le_mul x hx y hy).trans (by
          exact mul_le_mul_of_nonneg_right (by simp) dist_nonneg)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hfwd x hx y hy hxy
  · simpa only [dist_comm] using hfwd y hy x hx hyx

/-- The extended Dyson path is continuously differentiable in time when its interval fields are
continuous. -/
theorem dysonPiecewisePath_contDiff_one {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (τ : ℕ → ℝ) (n : ℕ)
    (hH : Continuous (H n)) (hL : Continuous (L n)) (z : ℂ) :
    ContDiff ℝ 1 (dysonPiecewisePath H L τ n z) := by
  exact (orderedEvolution_contDiff_one
    (fun u => Complex.I • (H n u + z • L n u))
    ((hH.add (hL.const_smul z)).const_smul Complex.I) (τ n)).mul contDiff_const

/-- With continuous interval fields and a strictly increasing partition, the assembled path has
a Lipschitz constant on every compact unordered interval. -/
theorem assembledDyson_exists_lipschitz {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n : ℕ) (z : ℂ) (a b : ℝ) :
    ∃ K, LipschitzOnWith K (assembledDyson H L τ n z) (uIcc a b) := by
  induction n with
  | zero => exact ⟨0, (LipschitzWith.const _).lipschitzOnWith⟩
  | succ n ih =>
    obtain ⟨Kf, hf⟩ := ih
    obtain ⟨Kg, hg⟩ := (dysonPiecewisePath_contDiff_one H L τ n (hH n) (hL n) z).contDiffOn
      |>.exists_lipschitzOnWith (by decide) (convex_Icc (min a b) (max a b)) isCompact_Icc
    refine ⟨Kf + Kg, lipschitzOn_if_le hf hg ?_⟩
    simp only [assembledDyson_endpoint H L τ hτ, dysonPiecewisePath,
      dysonPropagator_self, one_mul]

/-- With continuous interval fields and a strictly increasing partition, the assembled Dyson
path is absolutely continuous on every interval. -/
theorem assembledDyson_absolutelyContinuous {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n : ℕ) (z : ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (assembledDyson H L τ n z) a b := by
  obtain ⟨K, hK⟩ := assembledDyson_exists_lipschitz H L hH hL τ hτ n z a b
  exact hK.absolutelyContinuousOnInterval

/-- An absolutely continuous solution of the assembled evolution equation with identity initial
value agrees with the assembled Dyson path on the partition interval. -/
theorem assembledDyson_unique_ae {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (τ : ℕ → ℝ) (hτ : StrictMono τ)
    (n : ℕ) (z : ℂ) (f : ℝ → Matrix I I ℂ)
    (hf : AbsolutelyContinuousOnInterval f (τ 0) (τ n)) (hinit : f (τ 0) = 1)
    (hode : ∀ᵐ t : ℝ, t ∈ Icc (τ 0) (τ n) → HasDerivAt f
      (-(Complex.I • (assembledField H τ n t + z • assembledField L τ n t) * f t)) t) :
    EqOn f (assembledDyson H L τ n z) (Icc (τ 0) (τ n)) := by
  induction n with
  | zero =>
    intro t ht
    have he : t = τ 0 := le_antisymm ht.2 ht.1
    simpa only [he, assembledDyson] using hinit
  | succ n ih =>
    have h₀n : τ 0 ≤ τ n := hτ.monotone (Nat.zero_le n)
    have hnnext : τ n ≤ τ (n + 1) := hτ.monotone (Nat.le_succ n)
    have h₀next : τ 0 ≤ τ (n + 1) := hτ.monotone (Nat.zero_le _)
    have hfprev : AbsolutelyContinuousOnInterval f (τ 0) (τ n) := by
      apply hf.mono
      rw [uIcc_of_le h₀n, uIcc_of_le h₀next]
      exact Icc_subset_Icc_right hnnext
    have hodeprev : ∀ᵐ t : ℝ, t ∈ Icc (τ 0) (τ n) → HasDerivAt f
        (-(Complex.I • (assembledField H τ n t + z • assembledField L τ n t) * f t)) t := by
      filter_upwards [hode, volume.ae_ne (τ n)] with t ht hne hmem
      have hlt : t < τ n := lt_of_le_of_ne hmem.2 hne
      have hu := ht ⟨hmem.1, hmem.2.trans hnnext⟩
      simpa only [assembledField, hlt, ↓reduceIte] using hu
    have hprev := ih hfprev hodeprev
    have hftail : AbsolutelyContinuousOnInterval f (τ n) (τ (n + 1)) := by
      apply hf.mono
      rw [uIcc_of_le hnnext, uIcc_of_le h₀next]
      exact Icc_subset_Icc_left h₀n
    have hgtail : AbsolutelyContinuousOnInterval (dysonPiecewisePath H L τ n z)
        (τ n) (τ (n + 1)) :=
      (dysonPiecewisePath_contDiff_one H L τ n (hH n) (hL n) z).contDiffOn.absolutelyContinuousOnInterval
    have hitail : f (τ n) = dysonPiecewisePath H L τ n z (τ n) := by
      have he := hprev ⟨h₀n, le_rfl⟩
      simpa only [assembledDyson_endpoint H L τ hτ, dysonPiecewisePath,
        dysonPropagator_self, one_mul] using he
    have hfode : ∀ᵐ t : ℝ, t ∈ uIcc (τ n) (τ (n + 1)) → HasDerivAt f
        (-(Complex.I • (H n t + z • L n t) * f t)) t := by
      filter_upwards [hode, volume.ae_ne (τ n), volume.ae_ne (τ (n + 1))]
        with t ht hne₁ hne₂ hmem
      rw [uIcc_of_le hnnext] at hmem
      have hc : t ∈ Ioo (τ n) (τ (n + 1)) :=
        ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne₁), lt_of_le_of_ne hmem.2 hne₂⟩
      have hu := ht ⟨h₀n.trans hmem.1, hmem.2⟩
      simpa only [assembledField_eq_on_piece H τ hτ.monotone (n + 1) n (Nat.lt_succ_self n) hc,
        assembledField_eq_on_piece L τ hτ.monotone (n + 1) n (Nat.lt_succ_self n) hc] using hu
    have hgode : ∀ᵐ t : ℝ, t ∈ uIcc (τ n) (τ (n + 1)) →
        HasDerivAt (dysonPiecewisePath H L τ n z)
          (-(Complex.I • (H n t + z • L n t) * dysonPiecewisePath H L τ n z t)) t :=
      Eventually.of_forall fun t _ => dysonPiecewisePath_hasDerivAt H L τ n (hH n) (hL n) z t
    have htail := ordered_matrix_ode_unique_ae
      (fun t => Complex.I • (H n t + z • L n t))
      (((hH n).add ((hL n).const_smul z)).const_smul Complex.I)
      f (dysonPiecewisePath H L τ n z) (τ n) (τ (n + 1))
      hftail hgtail hitail hfode hgode
    intro t ht
    by_cases htn : t ≤ τ n
    · simpa only [assembledDyson, htn, ↓reduceIte] using hprev ⟨ht.1, htn⟩
    · have hmem : t ∈ uIcc (τ n) (τ (n + 1)) := by
        rw [uIcc_of_le hnnext]
        exact ⟨(lt_of_not_ge htn).le, ht.2⟩
      simpa only [assembledDyson, htn, ↓reduceIte] using htail hmem

/-- The endpoint of the assembled Dyson path is complex differentiable in the parameter for
continuous interval fields and a strictly increasing partition. -/
theorem assembledDyson_differentiable_parameter {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (τ : ℕ → ℝ) (hτ : StrictMono τ) (n : ℕ) :
    Differentiable ℂ (fun z => assembledDyson H L τ n z (τ n)) := by
  simp_rw [assembledDyson_endpoint H L τ hτ]
  exact dysonPiecewise_differentiable H L hH hL τ n

/-- For continuous Hermitian `H` and positive semidefinite `L`, the assembled endpoint norm is
bounded by the exponential of `max z.im 0` times the assembled integral norm. -/
theorem assembledDyson_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j))
    (hHherm : ∀ j u, (H j u).IsHermitian) (hLpos : ∀ j u, (L j u).PosSemidef)
    (τ : ℕ → ℝ) (hτ : StrictMono τ) (n : ℕ) (z : ℂ) :
    ‖assembledDyson H L τ n z (τ n)‖ ≤
      Real.exp (max z.im 0 * ∫ u in τ 0..τ n, ‖assembledField L τ n u‖) := by
  rw [assembledDyson_endpoint H L τ hτ, assembledField_norm_integral L hL τ hτ.monotone]
  exact dysonPiecewise_norm_le H L hH hL hHherm hLpos τ hτ.monotone n z

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
