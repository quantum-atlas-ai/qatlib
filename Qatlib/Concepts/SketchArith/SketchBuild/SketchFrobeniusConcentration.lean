/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

/-!
# Frobenius concentration for compact sketches

The module expresses compact sketch products as averages of probability-weighted row products
and proves their mean and second-moment identities. Under one-source or joint row-norm
domination, it establishes unbiasedness, Frobenius error bounds, and concentration estimates for
the matrix arithmetic framework of [ChiaEtAl2022].

## Main statements

* `compact_sketch_unbiased_product_and_variances`: Domination of either source gives an unbiased
  compact product and bounds both its expected squared Frobenius error and its expected cached
  row-energy product sum by `φ * sketchSquared X * sketchSquared Y / r`. See [ChiaEtAl2022].
* `compact_sketch_frobenius_norm_bounds_and_tail`: Row-energy domination bounds each sketched
  row and total energy, gives exact total energy for supported samples when `φ = 1`, and
  provides the stated two-sided energy tail bound. See [ChiaEtAl2022].
* `compact_sketch_two_sided_source_frobenius_tail`: Under joint row-norm domination, the
  probability that the Frobenius product error reaches `√(8 * φ² * log (2 / δ) / r) *
  sketchRowProductMass X Y` is at most `δ`. See [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Concepts.SketchArith.SketchBuild
open Matrix
open scoped Classical BigOperators Matrix.Norms.Frobenius

/-- Every squared row norm is nonnegative. -/
theorem sketchRowSquared_nonneg {K C : Type} [Fintype C] (A : Matrix K C ℂ) (i : K) :
    0≤ sketchRowSquared A i := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The squared Frobenius energy `sketchSquared A` is nonnegative. -/
theorem sketchSquared_nonneg {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) :
    0≤ sketchSquared A := Finset.sum_nonneg fun _ _ => sketchRowSquared_nonneg A _

/-- The squared Frobenius norm of `A` equals the sum of its squared row norms. -/
theorem sketch_frobenius_norm_sq {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) :
    ‖A‖^2=sketchSquared A := by
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt]
  · simp only [sketchSquared,sketchRowSquared,Real.rpow_two,Complex.normSq_eq_norm_sq]
  · apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (norm_nonneg _) _

/-- Every entry of a row with zero squared norm is zero. -/
theorem sketchRowSquared_eq_zero_entry {K C : Type} [Fintype C] [DecidableEq C]
    (A : Matrix K C ℂ) (i : K) (h : sketchRowSquared A i=0) (j : C) : A i j=0 := by
  have hh : Complex.normSq (A i j)≤ sketchRowSquared A i :=
    Finset.single_le_sum (fun k _=>Complex.normSq_nonneg (A i k)) (Finset.mem_univ j)
  have hz : Complex.normSq (A i j)=0 :=
      le_antisymm (by simpa [h] using hh) (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp hz

/-- The square of a compact sketch weight is the reciprocal of `r * p.prob (ω t)`. -/
theorem compactSketch_scale_sq {K : Type} [Fintype K] (p : FinDist K) (r : ℕ)
    (ω : Fin r→K) (t : Fin r) :
    ((compactSketchData p r ω t).2)^2=((r : ℝ)*p.prob (ω t))⁻¹ := by
  change ((Real.sqrt ((r : ℝ)*p.prob (ω t)))⁻¹)^2=_
  rw [inv_pow,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg r) (p.nonneg _))]

/-- The energy of sketched row `t` is the source row energy divided by `r * p.prob (ω t)`. -/
theorem compactSketched_row_energy {K C : Type} [Fintype K] [Fintype C]
    (p : FinDist K) (r : ℕ) (ω : Fin r→K) (A : Matrix K C ℂ) (t : Fin r) :
    sketchRowSquared (compactSketched (compactSketchData p r ω) A) t =
      sketchRowSquared A (ω t)/((r : ℝ)*p.prob (ω t)) := by
  let s := (compactSketchData p r ω t).2
  have hs : s^2=((r : ℝ)*p.prob (ω t))⁻¹ := compactSketch_scale_sq p r ω t
  unfold sketchRowSquared compactSketched compactSketchEntry
  simp only [Complex.normSq_mul,Complex.normSq_ofReal,← pow_two]
  change (∑ j,s^2*Complex.normSq (A (ω t) j)) =
    (∑ j,Complex.normSq (A (ω t) j))/((r : ℝ)*p.prob (ω t))
  rw [← Finset.mul_sum,hs]
  ring

/-- The conjugate outer product of source row `k` from `X` and `Y`, scaled by the reciprocal of
its sampling probability. -/
noncomputable def sketchSampleMatrix {K C D : Type} [Fintype K]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (k : K) : Matrix C D ℂ :=
  fun i j => (p.prob k : ℂ)⁻¹ * (star (X k i)*Y k j)

/-- Each sketch-product entry is the average of the corresponding weighted row-product entries. -/
theorem sketchProduct_entry_average {K C D : Type} [Fintype K] (p : FinDist K)
    (r : ℕ) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (ω : Fin r→K) (i : C) (j : D) :
    sketchProduct p r X Y ω i j =
      (r : ℂ)⁻¹ * ∑ t : Fin r,sketchSampleMatrix p X Y (ω t) i j := by
  unfold sketchProduct compactProduct
  rw [compactProductEntry_eq]
  dsimp only [Prod.fst]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  let s := (compactSketchData p r ω t).2
  have hs : (s : ℂ)*(s : ℂ)=((r : ℂ)*(p.prob (ω t) : ℂ))⁻¹ := by
    have hh := congrArg Complex.ofReal (compactSketch_scale_sq p r ω t)
    simpa only [Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_mul,
      Complex.ofReal_natCast,pow_two] using hh
  change star ((s : ℂ)*X (ω t) i)*((s : ℂ)*Y (ω t) j)=_
  have hstar : star (s : ℂ)=(s : ℂ) := by simp only [Complex.star_def,Complex.conj_ofReal]
  rw [star_mul,hstar]
  calc
    _ = ((s : ℂ)*(s : ℂ))*(star (X (ω t) i)*Y (ω t) j) := by ring
    _ = _ := by rw [hs]; simp only [mul_inv,sketchSampleMatrix]; ring

/-- The real and imaginary parts of a sketch-product entry are the sample averages of the
corresponding parts of `sketchSampleMatrix`. -/
theorem sketchProduct_entry_parts {K C D : Type} [Fintype K] (p : FinDist K)
    (r : ℕ) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (ω : Fin r→K) (i : C) (j : D) :
    (sketchProduct p r X Y ω i j).re =
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun k=>(sketchSampleMatrix p X Y k i j).re) ω ∧
    (sketchProduct p r X Y ω i j).im =
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun k=>(sketchSampleMatrix p X Y k i j).im) ω := by
  rw [sketchProduct_entry_average]
  constructor <;> simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg,Complex.mul_re,Complex.mul_im,← Complex.ofReal_natCast] <;> ring

/-- The variance of a real observable is at most its second moment. -/
theorem sketch_variance_le_second {K : Type} [Fintype K] [DecidableEq K]
    (p : FinDist K) (f : K→ℝ) : p.variance f≤ p.expect (fun k=>(f k)^2) := by
  have he (k : K) : p.prob k*(f k)^2 =
      p.prob k*(f k-p.expect f)^2 + 2*p.expect f*(p.prob k*(f k-p.expect f)) +
        (p.expect f)^2*p.prob k := by ring
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    ← Finset.mul_sum,p.sum_sub_mean,p.sum_one]
  change p.variance f≤ p.variance f+2*p.expect f*0+(p.expect f)^2*1
  nlinarith [sq_nonneg (p.expect f)]

/-- The entrywise expectation of the probability-weighted row-product matrix. -/
noncomputable def sketchMeanMatrix {K C D : Type} [Fintype K]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) : Matrix C D ℂ :=
  fun i j => ∑ k,(p.prob k : ℂ)*sketchSampleMatrix p X Y k i j

/-- The real and imaginary parts of `sketchMeanMatrix` equal the expectations of the
corresponding parts of the sample matrix. -/
private theorem sketchMean_parts {K C D : Type} [Fintype K] (p : FinDist K)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (i : C) (j : D) :
    (sketchMeanMatrix p X Y i j).re=p.expect (fun k=>(sketchSampleMatrix p X Y k i j).re) ∧
    (sketchMeanMatrix p X Y i j).im=p.expect (fun k=>(sketchSampleMatrix p X Y k i j).im) := by
  constructor <;> simp [sketchMeanMatrix,Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,Complex.mul_re,Complex.mul_im]

/-- The mean squared error of a sketch-product entry about its mean is at most the sample-entry
second moment divided by the positive sample size. -/
theorem sketchProduct_entry_second_moment {K C D : Type} [Fintype K] [DecidableEq K]
    (p : FinDist K) (r : ℕ) (hr : 0<r) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (i : C) (j : D) :
    (∑ ω : Fin r→K,p.probOf ω*Complex.normSq ((sketchProduct p r X Y ω-sketchMeanMatrix p X Y) i j)) ≤
      (p.expect (fun k=>Complex.normSq (sketchSampleMatrix p X Y k i j)))/(r : ℝ) := by
  have hre (ω : Fin r→K) := (sketchProduct_entry_parts p r X Y ω i j).1
  have him (ω : Fin r→K) := (sketchProduct_entry_parts p r X Y ω i j).2
  have hmr := (sketchMean_parts p X Y i j).1
  have hmi := (sketchMean_parts p X Y i j).2
  have he : (∑ ω : Fin r→K,p.probOf ω*Complex.normSq ((sketchProduct p r X Y ω-sketchMeanMatrix p X Y) i j)) =
      (p.variance (fun k=>(sketchSampleMatrix p X Y k i j).re)+
        p.variance (fun k=>(sketchSampleMatrix p X Y k i j).im))/(r : ℝ) := by
    simp only [Matrix.sub_apply,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      hre,him,hmr,hmi,← pow_two,mul_add,Finset.sum_add_distrib]
    rw [p.expect_avg_sub_sq _ hr,p.expect_avg_sub_sq _ hr,add_div]
  rw [he]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
  have h1 := sketch_variance_le_second p (fun k=>(sketchSampleMatrix p X Y k i j).re)
  have h2 := sketch_variance_le_second p (fun k=>(sketchSampleMatrix p X Y k i j).im)
  have hf : p.expect (fun k=>Complex.normSq (sketchSampleMatrix p X Y k i j)) =
      p.expect (fun k=>((sketchSampleMatrix p X Y k i j).re)^2)+
      p.expect (fun k=>((sketchSampleMatrix p X Y k i j).im)^2) := by
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,Complex.normSq_apply,← pow_two,mul_add,Finset.sum_add_distrib]
  rw [hf]
  exact add_le_add h1 h2

/-- The expected squared Frobenius error about `sketchMeanMatrix` is at most the sample-matrix
second moment divided by the positive sample size. -/
theorem sketchProduct_frobenius_second_moment {K C D : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [Fintype D] (p : FinDist K) (r : ℕ) (hr : 0<r)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) :
    (∑ ω : Fin r→K,p.probOf ω*‖sketchProduct p r X Y ω-sketchMeanMatrix p X Y‖^2) ≤
      (∑ k,p.prob k*‖sketchSampleMatrix p X Y k‖^2)/(r : ℝ) := by
  simp only [sketch_frobenius_norm_sq,sketchSquared,sketchRowSquared,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i,∑ j,∑ ω : Fin r→K,p.probOf ω*Complex.normSq ((sketchProduct p r X Y ω-sketchMeanMatrix p X Y) i j) := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ ≤ ∑ i,∑ j,p.expect (fun k=>Complex.normSq (sketchSampleMatrix p X Y k i j))/(r : ℝ) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact sketchProduct_entry_second_moment p r hr X Y i j
    _ = _ := by
      simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,← Finset.sum_div]
      congr 1
      calc
        _ = ∑ i,∑ k,∑ j,p.prob k*Complex.normSq (sketchSampleMatrix p X Y k i j) := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm

/-- The expected weighted row product equals `Xᴴ * Y` if all row products outside the support of
`p` vanish. -/
theorem sketchMean_eq_product {K C D : Type} [Fintype K]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ)
    (hs : ∀ k,p.prob k=0→∀ i j,star (X k i)*Y k j=0) :
    sketchMeanMatrix p X Y=Xᴴ*Y := by
  ext i j
  simp only [sketchMeanMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hp : p.prob k=0
  · simp only [hp,Complex.ofReal_zero,zero_mul]
    exact (hs k hp i j).symm
  · simp only [sketchSampleMatrix,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hp),one_mul]

/-- The squared Frobenius norm of a sample matrix is the product of source row energies divided
by the squared sampling probability. -/
theorem sketchSample_norm_sq {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (k : K) :
    ‖sketchSampleMatrix p X Y k‖^2 =
      sketchRowSquared X k*sketchRowSquared Y k/(p.prob k)^2 := by
  rw [sketch_frobenius_norm_sq]
  simp only [sketchSquared,sketchRowSquared,sketchSampleMatrix,Complex.normSq_mul,
    Complex.normSq_inv,Complex.star_def,Complex.normSq_conj,Complex.normSq_ofReal]
  simp only [← Finset.mul_sum,← Finset.sum_mul,← pow_two]
  ring

/-- Multiplying the squared sample-matrix norm by its sampling probability gives the row-energy
product divided by that probability. -/
theorem sketchSample_weighted_norm {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (k : K) :
    p.prob k*‖sketchSampleMatrix p X Y k‖^2 =
      sketchRowSquared X k*sketchRowSquared Y k/p.prob k := by
  rw [sketchSample_norm_sq]
  by_cases hp : p.prob k=0
  · simp [hp]
  · field_simp

/-- Under row-energy domination and positive total energy, a row with zero sampling probability
has zero energy. -/
theorem sketch_dominance_zero_row {K C : Type} [Fintype K] [Fintype C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ : ℝ)
    (hφ : 1≤φ) (hA : 0<sketchSquared A)
    (hdom : ∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤ p.prob k)
    (k : K) (hp : p.prob k=0) : sketchRowSquared A k=0 := by
  have hden : 0<φ*sketchSquared A := mul_pos (by linarith) hA
  have hh := (div_le_iff₀ hden).mp (hdom k)
  rw [hp,zero_mul] at hh
  exact le_antisymm hh (sketchRowSquared_nonneg A k)

/-- A domination bound `x / (φ * E) ≤ q` gives `x * y / q ≤ φ * E * y` under the stated sign
conditions. -/
private theorem sketch_ratio_bound (x y E φ q : ℝ)
    (hy : 0≤y) (hE : 0<E) (hφ : 1≤φ) (hq : 0≤q) (hd : x/(φ*E)≤q) :
    x*y/q≤φ*E*y := by
  by_cases hq0 : q=0
  · simp only [hq0,div_zero]
    exact mul_nonneg (mul_nonneg (by linarith) hE.le) hy
  · have hqp : 0<q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hx := (div_le_iff₀ (mul_pos (by linarith) hE)).mp hd
    apply (div_le_iff₀ hqp).mpr
    nlinarith

/-- Domination of either source's normalized row energies bounds the sample-matrix second moment
by `φ * sketchSquared X * sketchSquared Y`. -/
theorem sketch_one_source_second_bound {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (φ : ℝ) (hφ : 1≤φ)
    (hs : ((0<sketchSquared X ∧ ∀ k,sketchRowSquared X k/(φ*sketchSquared X)≤ p.prob k) ∨
      (0<sketchSquared Y ∧ ∀ k,sketchRowSquared Y k/(φ*sketchSquared Y)≤ p.prob k))) :
    (∑ k,p.prob k*‖sketchSampleMatrix p X Y k‖^2) ≤ φ*sketchSquared X*sketchSquared Y := by
  simp only [sketchSample_weighted_norm]
  rcases hs with hX | hY
  · calc
      _ ≤ ∑ k,φ*sketchSquared X*sketchRowSquared Y k := Finset.sum_le_sum fun k _ =>
        sketch_ratio_bound _ _ _ _ _ (sketchRowSquared_nonneg Y k) hX.1 hφ (p.nonneg k) (hX.2 k)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  · calc
      _ ≤ ∑ k,φ*sketchSquared Y*sketchRowSquared X k := by
        apply Finset.sum_le_sum; intro k _
        rw [mul_comm (sketchRowSquared X k) (sketchRowSquared Y k)]
        exact sketch_ratio_bound _ _ _ _ _ (sketchRowSquared_nonneg X k) hY.1 hφ (p.nonneg k)
            (hY.2 k)
      _ = _ := by rw [← Finset.mul_sum]; change φ*sketchSquared Y*sketchSquared X=φ*sketchSquared X*sketchSquared Y; ring

/-- For a positive sample size, the expected sketch-product entry equals the corresponding entry
of `sketchMeanMatrix`. -/
theorem sketchProduct_unbiased_mean {K C D : Type} [Fintype K] [DecidableEq K]
    (p : FinDist K) (r : ℕ) (hr : 0<r) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (i : C) (j : D) :
    (∑ ω : Fin r→K,(p.probOf ω : ℂ)*sketchProduct p r X Y ω i j)=sketchMeanMatrix p X Y i j := by
  apply Complex.ext
  · simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,(sketchMean_parts p X Y i j).1]
    simp_rw [(sketchProduct_entry_parts p r X Y _ i j).1]
    exact p.expect_avg _ hr
  · simp only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero,(sketchMean_parts p X Y i j).2]
    simp_rw [(sketchProduct_entry_parts p r X Y _ i j).2]
    exact p.expect_avg _ hr

/-- The expected sum of products of cached sketched row energies equals the sample-matrix second
moment divided by the positive sample size. -/
theorem sketch_cached_row_products_expectation {K C D : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [Fintype D] (p : FinDist K) (r : ℕ) (hr : 0<r)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) :
    (∑ ω : Fin r→K,p.probOf ω*(∑ t : Fin r,
      sketchRowSquared (compactSketched (compactSketchData p r ω) X) t*
      sketchRowSquared (compactSketched (compactSketchData p r ω) Y) t)) =
      (∑ k,p.prob k*‖sketchSampleMatrix p X Y k‖^2)/(r : ℝ) := by
  have he (ω : Fin r→K) : (∑ t : Fin r,
      sketchRowSquared (compactSketched (compactSketchData p r ω) X) t*
      sketchRowSquared (compactSketched (compactSketchData p r ω) Y) t) =
      (∑ t : Fin r,‖sketchSampleMatrix p X Y (ω t)‖^2)/(r : ℝ)^2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro t _
    rw [compactSketched_row_energy,compactSketched_row_energy,sketchSample_norm_sq]
    simp only [div_eq_mul_inv,mul_inv]
    ring
  simp only [he,← mul_div_assoc,← Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  have hh (t : Fin r) : (∑ ω : Fin r→K,p.probOf ω*‖sketchSampleMatrix p X Y (ω t)‖^2) =
      ∑ k,p.prob k*‖sketchSampleMatrix p X Y k‖^2 :=
    p.expect_coord t (fun k=>‖sketchSampleMatrix p X Y k‖^2)
  simp only [hh,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
  field_simp [Nat.cast_ne_zero.mpr hr.ne']

/-- Domination of either source gives an unbiased compact product and bounds both its expected
squared Frobenius error and its expected cached row-energy product sum by `φ * sketchSquared
X * sketchSquared Y / r`. See [ChiaEtAl2022]. -/
theorem compact_sketch_unbiased_product_and_variances : ∀ (K C D : Type) [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] [Fintype D] [DecidableEq D] (p : FinDist K) (r : ℕ)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (φ : ℝ),
  0< r → 1≤φ →
  ((0< sketchSquared X ∧ ∀ k,sketchRowSquared X k/(φ*sketchSquared X)≤ p.prob k) ∨
    (0< sketchSquared Y ∧ ∀ k,sketchRowSquared Y k/(φ*sketchSquared Y)≤ p.prob k)) →
  (∀ i j,(∑ ω : Fin r→K,(p.probOf ω:ℂ)*(sketchProduct p r X Y ω) i j)=(Xᴴ*Y) i j) ∧
  (∑ ω : Fin r→K,p.probOf ω*‖sketchProduct p r X Y ω-Xᴴ*Y‖^2)≤
    φ*sketchSquared X*sketchSquared Y/(r:ℝ) ∧
  (∑ ω : Fin r→K,p.probOf ω*(∑ t : Fin r,
    sketchRowSquared (compactSketched (compactSketchData p r ω) X) t*
      sketchRowSquared (compactSketched (compactSketchData p r ω) Y) t))≤
    φ*sketchSquared X*sketchSquared Y/(r:ℝ) := by
  intro K C D _ _ _ _ _ _ p r X Y φ hr hφ hs
  have hsupport : ∀ k,p.prob k=0→∀ i j,star (X k i)*Y k j=0 := by
    intro k hp i j
    rcases hs with hX | hY
    · have hz := sketch_dominance_zero_row p X φ hφ hX.1 hX.2 k hp
      rw [sketchRowSquared_eq_zero_entry X k hz i,star_zero,zero_mul]
    · have hz := sketch_dominance_zero_row p Y φ hφ hY.1 hY.2 k hp
      rw [sketchRowSquared_eq_zero_entry Y k hz j,mul_zero]
  have hmean := sketchMean_eq_product p X Y hsupport
  have hb := sketch_one_source_second_bound p X Y φ hφ hs
  have hdiv := div_le_div_of_nonneg_right hb (Nat.cast_nonneg r)
  refine ⟨?_,?_,?_⟩
  · intro i j
    rw [← hmean]
    exact sketchProduct_unbiased_mean p r hr X Y i j
  · rw [← hmean]
    exact (sketchProduct_frobenius_second_moment p r hr X Y).trans hdiv
  · rw [sketch_cached_row_products_expectation p r hr X Y]
    exact hdiv

/-- The energy of a compact sketch is the sample average of source row energy divided by
sampling probability. -/
theorem compactSketched_energy_avg {K C : Type} [Fintype K] [Fintype C]
    (p : FinDist K) (r : ℕ) (ω : Fin r→K) (A : Matrix K C ℂ) :
    sketchSquared (compactSketched (compactSketchData p r ω) A) =
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun k=>sketchRowSquared A k/p.prob k) ω := by
  unfold sketchSquared Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg
  simp only [compactSketched_row_energy,Finset.sum_div]
  apply Finset.sum_congr rfl; intro t _
  simp only [div_eq_mul_inv,mul_inv]
  ring

/-- Row-energy domination with positive total energy makes the probability-weighted row-energy
observable have expectation `sketchSquared A`. -/
theorem sketch_energy_expectation {K C : Type} [Fintype K] [Fintype C]
    (p : FinDist K) (A : Matrix K C ℂ) (φ : ℝ) (hφ : 1≤φ) (hA : 0<sketchSquared A)
    (hdom : ∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤ p.prob k) :
    p.expect (fun k=>sketchRowSquared A k/p.prob k)=sketchSquared A := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect sketchSquared
  apply Finset.sum_congr rfl; intro k _
  by_cases hp : p.prob k=0
  · have hz := sketch_dominance_zero_row p A φ hφ hA hdom k hp
    simp [hp,hz]
  · field_simp

/-- Domination with factor one forces each row energy to equal the total energy multiplied by
its sampling probability. -/
theorem sketch_dominance_one_eq {K C : Type} [Fintype K] [Fintype C]
    (p : FinDist K) (A : Matrix K C ℂ) (hA : 0<sketchSquared A)
    (hdom : ∀ k,sketchRowSquared A k/sketchSquared A≤ p.prob k) :
    ∀ k,sketchRowSquared A k=sketchSquared A*p.prob k := by
  have hn (k : K) : 0≤ sketchSquared A*p.prob k-sketchRowSquared A k := by
    have hh := (div_le_iff₀ hA).mp (hdom k)
    nlinarith
  have hs : (∑ k,(sketchSquared A * p.prob k - sketchRowSquared A k))=0 := by
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,p.sum_one,mul_one]
    change sketchSquared A-sketchSquared A=0
    ring
  intro k
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun k _=>hn k)).mp hs k (Finset.mem_univ k)
  linarith

/-- Row-energy domination bounds each sketched row and total energy, gives exact total energy
for supported samples when `φ = 1`, and provides the stated two-sided energy tail bound. See
[ChiaEtAl2022]. -/
theorem compact_sketch_frobenius_norm_bounds_and_tail : ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (p : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (φ : ℝ),
  0< r → 1≤φ → 0< sketchSquared A →
  (∀ k,sketchRowSquared A k/(φ*sketchSquared A)≤ p.prob k) →
  (∀ (ω : Fin r→K) (t : Fin r),
    sketchRowSquared (compactSketched (compactSketchData p r ω) A) t≤φ*sketchSquared A/(r:ℝ)) ∧
  (∀ ω : Fin r→K,sketchSquared (compactSketched (compactSketchData p r ω) A)≤φ*sketchSquared A) ∧
  (φ=1 → ∀ ω : Fin r→K,(∀ t,0< p.prob (ω t)) →
    sketchSquared (compactSketched (compactSketchData p r ω) A)= sketchSquared A) ∧
  (∀ δ : ℝ,0<δ → δ<1 →p.probEvent (fun ω : Fin r→K=>
      Real.sqrt (φ^2*Real.log (2/δ)/(2*(r:ℝ)))*sketchSquared A≤
      |sketchSquared (compactSketched (compactSketchData p r ω) A)-sketchSquared A|)≤δ) := by
  intro K C _ _ _ _ p r A φ hr hφ hA hdom
  have hrp : 0<(r : ℝ) := Nat.cast_pos.mpr hr
  have hφp : 0<φ := by linarith
  have hB : 0<φ*sketchSquared A := mul_pos hφp hA
  have hZ (k : K) : (sketchRowSquared A k/p.prob k)∈Set.Icc 0 (φ*sketchSquared A) := by
    refine ⟨div_nonneg (sketchRowSquared_nonneg A k) (p.nonneg k),?_⟩
    simpa only [mul_one] using sketch_ratio_bound (sketchRowSquared A k) 1 (sketchSquared A) φ (p.prob k)
      (by norm_num) hA hφ (p.nonneg k) (hdom k)
  have hrow (ω : Fin r→K) (t : Fin r) :
      sketchRowSquared (compactSketched (compactSketchData p r ω) A) t≤φ*sketchSquared A/(r : ℝ) := by
    rw [compactSketched_row_energy]
    have hb := div_le_div_of_nonneg_right (hZ (ω t)).2 hrp.le
    convert! hb using 1 <;> (try simp only [div_eq_mul_inv,mul_inv]) <;> ring
  refine ⟨hrow,?_,?_,?_⟩
  · intro ω
    calc
      _ ≤ ∑ t : Fin r,φ*sketchSquared A/(r : ℝ) := Finset.sum_le_sum fun t _=>hrow ω t
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]; field_simp
  · intro he ω hsupp
    subst φ
    have hm := sketch_dominance_one_eq p A hA (by simpa only [one_mul] using hdom)
    rw [compactSketched_energy_avg]
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg
    have he (t : Fin r) : sketchRowSquared A (ω t)/p.prob (ω t)=sketchSquared A := by
      rw [hm]; exact mul_div_cancel_right₀ _ (hsupp t).ne'
    simp only [he,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
    field_simp
  · intro δ hδ hδ1
    have ht := finite_iid_bounded_average_tail p (fun k=>sketchRowSquared A k/p.prob k)
      r (φ*sketchSquared A) δ hr hB hδ hδ1 hZ
    rw [sketch_energy_expectation p A φ hφ hA hdom] at ht
    have hL : 0<Real.log (2/δ) := Real.log_pos (by apply (lt_div_iff₀ hδ).mpr; linarith)
    have he : Real.sqrt ((φ*sketchSquared A)^2*Real.log (2/δ)/(2*(r : ℝ))) =
        Real.sqrt (φ^2*Real.log (2/δ)/(2*(r : ℝ)))*sketchSquared A := by
      rw [show (φ*sketchSquared A)^2*Real.log (2/δ)/(2*(r : ℝ)) =
        (φ^2*Real.log (2/δ)/(2*(r : ℝ)))*(sketchSquared A)^2 by ring,
        Real.sqrt_mul (by positivity),Real.sqrt_sq hA.le]
    simpa only [he,compactSketched_energy_avg] using ht

/-- The square of the product of two row norms equals the product of their squared row norms. -/
private theorem sketch_sqrt_row_product_sq {K C D : Type} [Fintype C] [Fintype D]
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (k : K) :
    (Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k))^2 =
      sketchRowSquared X k*sketchRowSquared Y k := by
  rw [mul_pow,Real.sq_sqrt (sketchRowSquared_nonneg X k),Real.sq_sqrt (sketchRowSquared_nonneg Y k)]

/-- Joint row-norm domination bounds every sample-matrix Frobenius norm by `φ *
sketchRowProductMass X Y`. -/
theorem sketch_two_source_atom_bound {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (φ : ℝ)
    (hφ : 1≤φ) (hW : 0<sketchRowProductMass X Y)
    (hdom : ∀ k,Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k)/
      (φ*sketchRowProductMass X Y)≤ p.prob k) :
    ∀ k,‖sketchSampleMatrix p X Y k‖≤φ*sketchRowProductMass X Y := by
  intro k
  have hB : 0<φ*sketchRowProductMass X Y := mul_pos (by linarith) hW
  by_cases hp : p.prob k=0
  · have hz : sketchSampleMatrix p X Y k=0 := by ext i j; simp [sketchSampleMatrix,hp]
    rw [hz,norm_zero]
    exact hB.le
  · have hqp : 0<p.prob k := lt_of_le_of_ne (p.nonneg k) (Ne.symm hp)
    have hx := (div_le_iff₀ hB).mp (hdom k)
    have hs := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg hqp.le hB.le)).mpr hx
    rw [sketch_sqrt_row_product_sq,mul_pow] at hs
    apply (sq_le_sq₀ (norm_nonneg _) hB.le).mp
    rw [sketchSample_norm_sq]
    apply (div_le_iff₀ (sq_pos_of_pos hqp)).mpr
    nlinarith

/-- Joint row-norm domination bounds the sample-matrix second moment by `φ *
(sketchRowProductMass X Y)²`. -/
theorem sketch_two_source_second_bound {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (φ : ℝ)
    (hφ : 1≤φ) (hW : 0<sketchRowProductMass X Y)
    (hdom : ∀ k,Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k)/
      (φ*sketchRowProductMass X Y)≤ p.prob k) :
    (∑ k,p.prob k*‖sketchSampleMatrix p X Y k‖^2)≤φ*(sketchRowProductMass X Y)^2 := by
  simp only [sketchSample_weighted_norm]
  calc
    _ ≤ ∑ k,φ*sketchRowProductMass X Y*
        (Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k)) := by
      apply Finset.sum_le_sum; intro k _
      rw [← sketch_sqrt_row_product_sq X Y k,pow_two]
      exact sketch_ratio_bound _ _ _ _ _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        hW hφ (p.nonneg k) (hdom k)
    _ = _ := by rw [← Finset.mul_sum]; change φ*sketchRowProductMass X Y*sketchRowProductMass X Y=_; ring

/-- Under joint row-norm domination, the sample-matrix mean equals `Xᴴ * Y`. -/
theorem sketch_two_source_mean_eq {K C D : Type} [Fintype K] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] (p : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (φ : ℝ)
    (hφ : 1≤φ) (hW : 0<sketchRowProductMass X Y)
    (hdom : ∀ k,Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k)/
      (φ*sketchRowProductMass X Y)≤ p.prob k) : sketchMeanMatrix p X Y=Xᴴ*Y := by
  apply sketchMean_eq_product
  intro k hp i j
  have hh := (div_le_iff₀ (mul_pos (by linarith : 0<φ) hW)).mp (hdom k)
  rw [hp,zero_mul] at hh
  have hz : Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k)=0 :=
    le_antisymm hh (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rcases mul_eq_zero.mp hz with hx | hy
  · have hx0 : sketchRowSquared X k=0 := by
      rw [← Real.sq_sqrt (sketchRowSquared_nonneg X k),hx]; norm_num
    rw [sketchRowSquared_eq_zero_entry X k hx0 i,star_zero,zero_mul]
  · have hy0 : sketchRowSquared Y k=0 := by
      rw [← Real.sq_sqrt (sketchRowSquared_nonneg Y k),hy]; norm_num
    rw [sketchRowSquared_eq_zero_entry Y k hy0 j,mul_zero]

/-- The compact sketch product is the matrix average of its weighted row-product samples. -/
theorem sketchProduct_matrix_average {K C D : Type} [Fintype K]
    (p : FinDist K) (r : ℕ) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (ω : Fin r→K) :
    sketchProduct p r X Y ω=(r : ℂ)⁻¹ • ∑ t : Fin r,sketchSampleMatrix p X Y (ω t) := by
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
  exact sketchProduct_entry_average p r X Y ω i j

/-- The square of an expectation is at most the expectation of the square. -/
theorem sketch_expect_sq_le {K : Type} [Fintype K] [DecidableEq K] (p : FinDist K) (f : K→ℝ) :
    (p.expect f)^2≤ p.expect (fun k=>(f k)^2) := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset K)
    (r:=fun k=>p.prob k*f k) (f:=p.prob) (g:=fun k=>p.prob k*(f k)^2)
    (fun k _=>p.nonneg k) (fun k _=>mul_nonneg (p.nonneg k) (sq_nonneg _))
    (fun k _=>by ring_nf; rfl)
  simpa only [p.sum_one,one_mul,Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect] using
      hh

/-- If sample-matrix norms are bounded by `B`, changing one sample changes the sketch product by
Frobenius norm at most `2 * B / r`. -/
private theorem sketchProduct_coord_difference {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (p : FinDist K) (r : ℕ) (_hr : 0<r) (X : Matrix K C ℂ) (Y : Matrix K D ℂ)
    (B : ℝ) (hB : ∀ k,‖sketchSampleMatrix p X Y k‖≤B)
    (i : Fin r) (ω τ : Fin r→K) (h : ∀ j,j≠i→ω j=τ j) :
    ‖sketchProduct p r X Y ω-sketchProduct p r X Y τ‖≤2*B/(r : ℝ) := by
  have hs : (∑ t : Fin r,sketchSampleMatrix p X Y (ω t))-
      (∑ t : Fin r,sketchSampleMatrix p X Y (τ t)) =
      sketchSampleMatrix p X Y (ω i)-sketchSampleMatrix p X Y (τ i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single i
    · intro j _ hj; rw [h j hj,sub_self]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  rw [sketchProduct_matrix_average,sketchProduct_matrix_average,← smul_sub,hs,norm_smul,norm_inv,
    Complex.norm_natCast]
  have hb := (norm_sub_le _ _).trans (add_le_add (hB (ω i)) (hB (τ i)))
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Nat.cast_nonneg r))
  convert! hh using 1 <;> ring

/-- Under joint row-norm domination, the probability that the Frobenius product error reaches
`√(8 * φ² * log (2 / δ) / r) * sketchRowProductMass X Y` is at most `δ`. See [ChiaEtAl2022]. -/
theorem compact_sketch_two_sided_source_frobenius_tail : ∀ (K C D : Type) [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] [Fintype D] [DecidableEq D] (p : FinDist K) (r : ℕ)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (φ δ : ℝ),
  0< r → 1≤φ → 0< sketchRowProductMass X Y → 0<δ → δ<1 →
  (∀ k,Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k)/
    (φ*sketchRowProductMass X Y)≤ p.prob k) →
  p.probEvent (fun ω : Fin r→K=> Real.sqrt (8*φ^2*Real.log (2/δ)/(r:ℝ))*
    sketchRowProductMass X Y≤‖sketchProduct p r X Y ω-Xᴴ*Y‖)≤δ := by
  intro K C D _ _ _ _ _ _ p r X Y φ δ hr hφ hW hδ hδ1 hdom
  let W := sketchRowProductMass X Y
  let L := Real.log (2/δ)
  let q := independentSampleLaw (fun _ : Fin r=>p)
  let f := fun ω : Fin r→K=>‖sketchProduct p r X Y ω-Xᴴ*Y‖
  let μ := q.expect f
  let u := φ*W*Real.sqrt (2*L/(r : ℝ))
  have hrp : 0<(r : ℝ) := Nat.cast_pos.mpr hr
  have hφp : 0<φ := by linarith
  have hLlo : (1/2 : ℝ)≤L := by
    have htwo : (1/2 : ℝ)≤Real.log 2 := by
      have hh := Real.le_log_one_add_of_nonneg (by norm_num : 0≤(1 : ℝ))
      norm_num at hh
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) ((le_div_iff₀ hδ).mpr (by linarith)))
  have hLp : 0<L := by linarith
  have hu : 0<u := by dsimp [u]; positivity
  have hu2 : u^2*(r : ℝ)=2*φ^2*W^2*L := by
    dsimp [u]
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
    field_simp
  have hsum : (∑ i : Fin r,(2*φ*W/(r : ℝ))^2)=4*φ^2*W^2/(r : ℝ) := by
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
    field_simp
    ring
  have hmoment : q.expect (fun ω=>(f ω)^2)≤φ*W^2/(r : ℝ) := by
    have hmean := sketch_two_source_mean_eq p X Y φ hφ hW hdom
    have hh := sketchProduct_frobenius_second_moment p r hr X Y
    rw [hmean] at hh
    exact hh.trans
        (div_le_div_of_nonneg_right (sketch_two_source_second_bound p X Y φ hφ hW hdom) hrp.le)
  have hμsq : μ^2≤φ*W^2/(r : ℝ) := (sketch_expect_sq_le q f).trans hmoment
  have hμnn : 0≤μ := Finset.sum_nonneg fun ω _=>mul_nonneg (q.nonneg ω) (norm_nonneg _)
  have hμu : μ≤u := by
    have hmul := (le_div_iff₀ hrp).mp hμsq
    have hfactor : φ≤2*φ^2*L := by
      have hs : φ≤φ^2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left (show 1≤2*L by linarith) (sq_nonneg φ)
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hfactor (sq_nonneg W)
    have hsq : μ^2*(r : ℝ)≤u^2*(r : ℝ) := calc
      _ ≤ φ*W^2 := hmul
      _ ≤ 2*φ^2*W^2*L := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
      _ = _ := hu2.symm
    exact (sq_le_sq₀ hμnn hu.le).mp (le_of_mul_le_mul_right hsq hrp)
  have hT : Real.sqrt (8*φ^2*L/(r : ℝ))*W=2*u := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hW.le) (by positivity : 0≤2*u)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),mul_pow]
    change (8*φ^2*L/(r : ℝ))*W^2=2^2*u^2
    field_simp
    nlinarith [hu2]
  have hdiff : ∀ i (ω τ : Fin r→K),(∀ j,j≠i→ω j=τ j)→|f ω-f τ|≤2*φ*W/(r : ℝ) := by
    intro i ω τ h
    have hh := abs_norm_sub_norm_le (sketchProduct p r X Y ω-Xᴴ*Y) (sketchProduct p r X Y τ-Xᴴ*Y)
    have he : (sketchProduct p r X Y ω-Xᴴ*Y)-(sketchProduct p r X Y τ-Xᴴ*Y)=
        sketchProduct p r X Y ω-sketchProduct p r X Y τ := by abel
    rw [he] at hh
    have hb := sketchProduct_coord_difference p r hr X Y (φ*W)
      (sketch_two_source_atom_bound p X Y φ hφ hW hdom) i ω τ h
    exact hh.trans (by simpa only [mul_assoc] using hb)
  have hupper := (finite_product_bounded_differences_tail K r (fun _=>p) f
    (fun _=>2*φ*W/(r : ℝ)) u (fun _=>by positivity) (by rw [hsum]; positivity) hu hdiff).1
  have hprob : p.probEvent (fun ω : Fin r→K=>Real.sqrt (8*φ^2*L/(r : ℝ))*W≤f ω)≤
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin r→K=>μ+u≤f ω),q.prob ω) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ ω,?_⟩
      have hh := (Finset.mem_filter.mp hω).2
      rw [hT] at hh
      linarith
    · intro ω _ _; exact q.nonneg ω
  refine hprob.trans (hupper.trans ?_)
  rw [hsum]
  have he : -2*u^2/(4*φ^2*W^2/(r : ℝ))=-L := by
    apply (div_eq_iff (by positivity : (4*φ^2*W^2/(r : ℝ))≠0)).mpr
    field_simp
    nlinarith [hu2]
  rw [he]
  have he' : Real.exp (-L)=δ/2 := by
    rw [Real.exp_neg]
    dsimp [L]
    rw [Real.exp_log (by positivity : 0<2/δ)]
    field_simp
  rw [he']
  linarith

end Qatlib.Concepts.SketchArith.SketchBuild
