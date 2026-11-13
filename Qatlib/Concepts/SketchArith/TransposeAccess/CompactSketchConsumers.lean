/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.TransposeAccess.SketchTransposeAccess
import Qatlib.Concepts.SketchArith.TransposeAccess.FinDistTransport

/-!
# Mixture sampling consumers for compact sketches

`compactMixtureLaw` combines two finite sampling laws with equal weights, and
`compactMixtureBuild` records its construction costs. The module proves the induced product law,
a matrix-product concentration bound, and an oversampling-overhead event bound for compact
sketches in [ChiaEtAl2022].

## Main statements

* `compactMixtureBuild_eq`: The mixture builder returns the compact data for projected samples
  with counters `(r, 2 * r, r)`.
* `compact_sketch_actual_mixture_product_consumer`: Exact row-energy laws yield a mixture
  distribution with the stated tagged product-law fibers, Frobenius product tail, and exact
  compact construction and query counts. See [ChiaEtAl2022].
* `compact_sketch_actual_sq_overhead_event`: With the stated sample budget and an entrywise
  dominating matrix, the probability of zero sketch energy or oversampling overhead exceeding
  twice its source ratio is at most `δ`. See [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option autoImplicit false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.SketchArith.TransposeAccess
open Matrix
open scoped Classical BigOperators Matrix.Norms.Frobenius

/-- The joint mass obtained by choosing a Boolean branch uniformly and then sampling from `px`
or `py`. -/
noncomputable def sketchMixtureMass {K : Type} [Fintype K] (px py : FinDist K) (z : Bool×K) : ℝ :=
  (1/2:ℝ)*(if z.1 then py.prob z.2 else px.prob z.2)

/-- The equal-weight mixture probability `(px.prob i + py.prob i) / 2`. -/
noncomputable def sketchMixtureProbability {K : Type} [Fintype K] (px py : FinDist K) (i : K) : ℝ :=
  (px.prob i+py.prob i)/2

/-- Builds compact records from Boolean-tagged samples while counting one sample, two
probability reads, and one branch choice per record. -/
noncomputable def compactMixtureBuild {K : Type} [Fintype K] (px py : FinDist K) (r : ℕ)
    (ω : Fin r→Bool×K) : List (K×ℝ)×ℕ×ℕ×ℕ :=
  let a:=(List.ofFn (fun t : Fin r=> t)).foldl (fun a t=>
    (((ω t).2,(Real.sqrt ((r:ℝ)*sketchMixtureProbability px py (ω t).2))⁻¹)::a.1,
      a.2.1+1,a.2.2.1+2,a.2.2.2+1)) ([],0,0,0);
  (a.1.reverse,a.2.1,a.2.2.1,a.2.2.2)

/-- The finite distribution whose probabilities are the equal-weight mixture of `px` and `py`. -/
noncomputable def compactMixtureLaw {K : Type} [Fintype K] (px py : FinDist K) : FinDist K where
  prob := sketchMixtureProbability px py
  nonneg i := div_nonneg (add_nonneg (px.nonneg i) (py.nonneg i)) (by norm_num)
  sum_one := by
    simp only [sketchMixtureProbability,← Finset.sum_div,Finset.sum_add_distrib,px.sum_one,py.sum_one]
    norm_num

/-- The joint finite distribution of a uniform Boolean branch and a sample from the selected
source law. -/
noncomputable def compactMixtureJoint {K : Type} [Fintype K] (px py : FinDist K) : FinDist (Bool×K) where
  prob := sketchMixtureMass px py
  nonneg z := mul_nonneg (by norm_num) (by split_ifs <;> exact (by first | exact px.nonneg _ | exact py.nonneg _))
  sum_one := by
    simp only [sketchMixtureMass,Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,← Finset.mul_sum,
      px.sum_one,py.sum_one]
    norm_num

/-- Summing the tagged joint law over the fiber above `i` gives the mixture probability at `i`. -/
private theorem compact_mixture_fiber {K : Type} [Fintype K] [DecidableEq K]
    (px py : FinDist K) (i : K) :
    (∑ z : Bool×K,if z.2=i then (compactMixtureJoint px py).prob z else 0) =
      (compactMixtureLaw px py).prob i := by
  simp [compactMixtureJoint,compactMixtureLaw,sketchMixtureMass,sketchMixtureProbability,Fintype.sum_prod_type,
    mul_ite]
  ring

/-- Applying a map with the stated one-sample fiber probabilities to independent samples yields
the corresponding product-law fiber probabilities. -/
private theorem compact_fresh_fiber {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K] (q : FinDist X) (p : FinDist K) (f : X→K)
    (hf : ∀ i,(∑ x,if f x=i then q.prob x else 0)=p.prob i)
    (r : ℕ) (v : Fin r→K) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin r→X=>(fun t=>f (ω t))=v),∏ t,q.prob (ω t))=p.probOf v := by
  have hrecord (ω : Fin r→X) :
      (if (fun t=>f (ω t))=v then ∏ t,q.prob (ω t) else 0) =
      q.probOf ω*(∏ t : Fin r,if f (ω t)=v t then (1 : ℝ) else 0) := by
    by_cases h : (fun t=>f (ω t))=v
    · have hh (t : Fin r) : f (ω t)=v t := congrFun h t
      simp [hh,Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
    · obtain ⟨t,ht⟩ := Function.ne_iff.mp h
      have hz : (∏ t : Fin r,if f (ω t)=v t then (1 : ℝ) else 0)=0 :=
        Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
      simp [h,hz]
  simp only [Finset.sum_filter,hrecord]
  rw [q.expect_prod (fun t x=>if f x=v t then 1 else 0)]
  change (∏ t : Fin r,∑ x,q.prob x*(if f x=v t then (1 : ℝ) else 0))=∏ t,p.prob (v t)
  apply Finset.prod_congr rfl; intro t _
  simpa only [mul_ite,mul_one,mul_zero] using hf (v t)

/-- Evaluates the mixture-record fold, increasing its counters by the list length, twice that
length, and that length respectively. -/
private theorem compact_mixture_fold {T K : Type} (xs : List T) (d : T→K×ℝ)
    (a : List (K×ℝ)) (b c e : ℕ) :
    xs.foldl (fun a t=>(d t::a.1,a.2.1+1,a.2.2.1+2,a.2.2.2+1)) (a,b,c,e) =
      ((xs.map d).reverse++a,b+xs.length,c+2*xs.length,e+xs.length) := by
  induction xs generalizing a b c e with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,Nat.mul_add,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- The mixture builder returns the compact data for projected samples with counters `(r, 2 * r,
r)`. -/
theorem compactMixtureBuild_eq {K : Type} [Fintype K] (px py : FinDist K) (r : ℕ)
    (ω : Fin r→Bool×K) :
    compactMixtureBuild px py r ω =
      (List.ofFn (compactSketchData (compactMixtureLaw px py) r (fun t=>(ω t).2)),r,2*r,r) := by
  unfold compactMixtureBuild
  rw [compact_mixture_fold]
  simp only [List.map_ofFn,Function.comp_def,List.length_ofFn,List.append_nil,List.reverse_reverse,
    Nat.zero_add]
  rfl

/-- Entrywise domination of squared entry norms implies domination of squared row norms. -/
theorem sketchRowSquared_mono {K C : Type} [Fintype C] (A B : Matrix K C ℂ)
    (h : ∀ i j,Complex.normSq (A i j)≤Complex.normSq (B i j)) :
    ∀ i,sketchRowSquared A i≤ sketchRowSquared B i := fun i=>Finset.sum_le_sum fun j _=>h i j

/-- Entrywise domination of squared entry norms implies domination of total squared Frobenius
energies. -/
theorem sketchSquared_mono {K C : Type} [Fintype K] [Fintype C] (A B : Matrix K C ℂ)
    (h : ∀ i j,Complex.normSq (A i j)≤Complex.normSq (B i j)) :
    sketchSquared A≤ sketchSquared B := Finset.sum_le_sum fun i _=>sketchRowSquared_mono A B h i

/-- The sum of products of corresponding row norms is nonnegative. -/
theorem sketchRowProductMass_nonneg {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) : 0≤ sketchRowProductMass X Y :=
  Finset.sum_nonneg fun _ _=>mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The sum of products of corresponding row norms is bounded by the product of the Frobenius
norms. -/
theorem sketchRowProductMass_le_norms {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) :
    sketchRowProductMass X Y≤ Real.sqrt (sketchSquared X)*Real.sqrt (sketchSquared Y) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset K)
    (fun k=>Real.sqrt (sketchRowSquared X k)) (fun k=>Real.sqrt (sketchRowSquared Y k))
  have hx (k : K) : (Real.sqrt (sketchRowSquared X k))^2=sketchRowSquared X k :=
    Real.sq_sqrt (sketchRowSquared_nonneg X k)
  have hy (k : K) : (Real.sqrt (sketchRowSquared Y k))^2=sketchRowSquared Y k :=
    Real.sq_sqrt (sketchRowSquared_nonneg Y k)
  simp only [hx,hy] at hc
  apply (sq_le_sq₀ (sketchRowProductMass_nonneg X Y)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (sketchSquared_nonneg X),Real.sq_sqrt (sketchSquared_nonneg Y)]
  exact hc

/-- If the total row-norm product mass is zero, every conjugate product of corresponding
source-row entries vanishes. -/
private theorem sketch_zero_row_products {K C D : Type} [Fintype K] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] (X : Matrix K C ℂ) (Y : Matrix K D ℂ)
    (hW : sketchRowProductMass X Y=0) : ∀ k i j,star (X k i)*Y k j=0 := by
  have hn (k : K) : 0≤ Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  intro k i j
  have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun k _=>hn k)).mp hW k (Finset.mem_univ k)
  rcases mul_eq_zero.mp hh with hx | hy
  · have hz : sketchRowSquared X k=0 := by rw [← Real.sq_sqrt (sketchRowSquared_nonneg X k),hx]; norm_num
    rw [sketchRowSquared_eq_zero_entry X k hz i,star_zero,zero_mul]
  · have hz : sketchRowSquared Y k=0 := by rw [← Real.sq_sqrt (sketchRowSquared_nonneg Y k),hy]; norm_num
    rw [sketchRowSquared_eq_zero_entry Y k hz j,mul_zero]

/-- The equal mixture of exact row-energy laws dominates each normalized product of source row
norms. -/
private theorem compact_mixture_row_dominance {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (px py : FinDist K) (X : Matrix K C ℂ) (Y : Matrix K D ℂ)
    (hX : 0<sketchSquared X) (hY : 0<sketchSquared Y)
    (hpx : ∀ i,px.prob i=sketchRowSquared X i/sketchSquared X)
    (hpy : ∀ i,py.prob i=sketchRowSquared Y i/sketchSquared Y) :
    ∀ i,Real.sqrt (sketchRowSquared X i)*Real.sqrt (sketchRowSquared Y i)/
      (Real.sqrt (sketchSquared X)*Real.sqrt (sketchSquared Y))≤(compactMixtureLaw px py).prob i := by
  intro i
  let N := Real.sqrt (sketchSquared X)*Real.sqrt (sketchSquared Y)
  have hN : 0<N := mul_pos (Real.sqrt_pos.mpr hX) (Real.sqrt_pos.mpr hY)
  have hN2 : N^2=sketchSquared X*sketchSquared Y := by
    rw [mul_pow,Real.sq_sqrt hX.le,Real.sq_sqrt hY.le]
  have hx : sketchRowSquared X i=sketchSquared X*px.prob i := by rw [hpx]; field_simp
  have hy : sketchRowSquared Y i=sketchSquared Y*py.prob i := by rw [hpy]; field_simp
  have he : (Real.sqrt (sketchRowSquared X i)*Real.sqrt (sketchRowSquared Y i)/N)^2=px.prob i*py.prob i := by
    rw [div_pow,mul_pow,Real.sq_sqrt (sketchRowSquared_nonneg X i),Real.sq_sqrt (sketchRowSquared_nonneg Y i),hN2,hx,hy]
    field_simp
  apply (sq_le_sq₀ (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hN.le)
    ((compactMixtureLaw px py).nonneg i)).mp
  rw [he]
  change px.prob i*py.prob i≤((px.prob i+py.prob i)/2)^2
  nlinarith [sq_nonneg (px.prob i-py.prob i)]

/-- Exact row-energy laws yield a mixture distribution with the stated tagged product-law
fibers, Frobenius product tail, and exact compact construction and query counts. See
[ChiaEtAl2022]. -/
theorem compact_sketch_actual_mixture_product_consumer : ∀ (K C D : Type) [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] [Fintype D] [DecidableEq D] (px py : FinDist K) (r : ℕ)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (δ : ℝ),
  0< r → 0< sketchSquared X → 0< sketchSquared Y → 0<δ → δ<1 →
  (∀ i,px.prob i= sketchRowSquared X i/sketchSquared X) →
  (∀ i,py.prob i= sketchRowSquared Y i/sketchSquared Y) →
  ∃ p : FinDist K,(∀ i,p.prob i= sketchMixtureProbability px py i) ∧
    (∀ i,sketchMixtureMass px py (false,i)+sketchMixtureMass px py (true,i)= p.prob i) ∧
    (∀ v : Fin r→K,
      (∑ ω∈Finset.univ.filter (fun ω : Fin r→Bool×K=>(fun t=>(ω t).2)= v),
        ∏ t,sketchMixtureMass px py (ω t))= p.probOf v) ∧
    p.probEvent (fun ω : Fin r→K=> Real.sqrt (8*Real.log (2/δ)/(r:ℝ))*
      Real.sqrt (sketchSquared X)*Real.sqrt (sketchSquared Y)≤
      ‖sketchProduct p r X Y ω-Xᴴ*Y‖)≤δ ∧
    (∀ ω : Fin r→K,(compactSketchBuild p r ω).2=(r,r) ∧
      ∀ i j,(compactProductEntry (compactSketchData p r ω) X Y i j).2=2*r) ∧
    (∀ ω : Fin r→Bool×K,
      (compactMixtureBuild px py r ω).1= List.ofFn (compactSketchData p r (fun t=>(ω t).2)) ∧
      (compactMixtureBuild px py r ω).2=(r,2*r,r)) := by
  intro K C D _ _ _ _ _ _ px py r X Y δ hr hX hY hδ hδ1 hpx hpy
  let p := compactMixtureLaw px py
  let N := Real.sqrt (sketchSquared X)*Real.sqrt (sketchSquared Y)
  let W := sketchRowProductMass X Y
  have hN : 0<N := mul_pos (Real.sqrt_pos.mpr hX) (Real.sqrt_pos.mpr hY)
  have hrp : 0<(r : ℝ) := Nat.cast_pos.mpr hr
  have hLp : 0<Real.log (2/δ) := Real.log_pos (by apply (lt_div_iff₀ hδ).mpr; linarith)
  refine ⟨p,(fun _=>rfl),?_,?_,?_,?_,?_⟩
  · intro i
    simp [p,compactMixtureLaw,sketchMixtureMass,sketchMixtureProbability]
    ring
  · intro v
    exact compact_fresh_fiber (compactMixtureJoint px py) p Prod.snd
      (compact_mixture_fiber px py) r v
  · by_cases hW : W=0
    · have hz := sketch_zero_row_products X Y hW
      have ha (k : K) : sketchSampleMatrix p X Y k=0 := by
        ext i j; simp only [sketchSampleMatrix,hz k i j,mul_zero,Matrix.zero_apply]
      have hprod (ω : Fin r→K) : sketchProduct p r X Y ω=0 := by
        rw [sketchProduct_matrix_average]
        simp only [ha,Finset.sum_const_zero,smul_zero]
      have htarget : Xᴴ*Y=0 := by
        ext i j
        simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.zero_apply]
        exact Finset.sum_eq_zero fun k _=>hz k i j
      have hT : 0<Real.sqrt (8*Real.log (2/δ)/(r : ℝ))*N :=
          mul_pos (Real.sqrt_pos.mpr (by positivity)) hN
      simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent,hprod,htarget,sub_zero,norm_zero]
      have he : (Finset.univ.filter (fun _ : Fin r→K=>Real.sqrt (8*Real.log (2/δ)/(r : ℝ))*N≤0))=∅ := by
        apply Finset.filter_eq_empty_iff.mpr; intro ω _; exact not_le_of_gt hT
      simp only [mul_assoc]
      change (∑ ω ∈ Finset.univ.filter (fun _ : Fin r→K=>Real.sqrt (8*Real.log (2/δ)/(r : ℝ))*N≤0),p.probOf ω)≤δ
      rw [he,Finset.sum_empty]
      exact hδ.le
    · have hWp : 0<W := lt_of_le_of_ne (sketchRowProductMass_nonneg X Y) (Ne.symm hW)
      let φ := N/W
      have hφ : 1≤φ := (le_div_iff₀ hWp).mpr (by simpa using sketchRowProductMass_le_norms X Y)
      have hφW : φ*W=N := div_mul_cancel₀ N hWp.ne'
      have hdom : ∀ k,Real.sqrt (sketchRowSquared X k)*Real.sqrt (sketchRowSquared Y k)/(φ*W)≤p.prob k := by
        rw [hφW]
        exact compact_mixture_row_dominance px py X Y hX hY hpx hpy
      have ht :=
          compact_sketch_two_sided_source_frobenius_tail K C D p r X Y φ δ hr hφ hWp hδ hδ1 hdom
      have hth : Real.sqrt (8*φ^2*Real.log (2/δ)/(r : ℝ))*W=
          Real.sqrt (8*Real.log (2/δ)/(r : ℝ))*N := by
        apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hWp.le)
          (mul_nonneg (Real.sqrt_nonneg _) hN.le)).mp
        rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
        rw [← hφW]
        ring
      have hth' : Real.sqrt (8*φ^2*Real.log (2/δ)/(r : ℝ))*sketchRowProductMass X Y=
          Real.sqrt (8*Real.log (2/δ)/(r : ℝ))*Real.sqrt (sketchSquared X)*Real.sqrt (sketchSquared Y) := by
        simpa only [N,W,mul_assoc] using hth
      rw [hth'] at ht
      exact ht
  · intro ω
    rw [compactSketchBuild_eq]
    refine ⟨rfl,?_⟩
    intro i j
    rw [compactProductEntry_eq]
  · intro ω
    rw [compactMixtureBuild_eq]
    exact ⟨rfl,rfl⟩

/-- With the stated sample budget and an entrywise dominating matrix, the probability of zero
sketch energy or oversampling overhead exceeding twice its source ratio is at most `δ`. See
[ChiaEtAl2022]. -/
theorem compact_sketch_actual_sq_overhead_event : ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (p : FinDist K) (r : ℕ) (A Ah : Matrix K C ℂ) (δ : ℝ),
  0< sketchSquared A → (∀ i j,Complex.normSq (A i j)≤ Complex.normSq (Ah i j)) →
  (∀ i,p.prob i= sketchRowSquared Ah i/sketchSquared Ah) → 0< r → 0<δ → δ<1 →
  2*(sketchSquared Ah/sketchSquared A)^2*Real.log (2/δ)≤(r:ℝ) →
  p.probEvent (fun ω : Fin r→K=>
    sketchSquared (compactSketched (compactSketchData p r ω) A)=0 ∨
    2*(sketchSquared Ah/sketchSquared A)<
      sketchSquared Ah/sketchSquared (compactSketched (compactSketchData p r ω) A))≤δ := by
  intro K C _ _ _ _ p r A Ah δ hA hdom hp hr hδ hδ1 hbudget
  have henergy := sketchSquared_mono A Ah hdom
  have hhat : 0<sketchSquared Ah := hA.trans_le henergy
  let φ := sketchSquared Ah/sketchSquared A
  have hφ : 1≤φ := (le_div_iff₀ hA).mpr (by simpa using henergy)
  have hφp : 0<φ := by linarith
  have hφA : φ*sketchSquared A=sketchSquared Ah := div_mul_cancel₀ _ hA.ne'
  have hprop : ∀ i,sketchRowSquared A i/(φ*sketchSquared A)≤ p.prob i := by
    intro i
    rw [hφA,hp]
    exact div_le_div_of_nonneg_right (sketchRowSquared_mono A Ah hdom i) hhat.le
  have ht :=
      (compact_sketch_frobenius_norm_bounds_and_tail K C p r A φ hr hφ hA hprop).2.2.2 δ hδ hδ1
  have hrp : 0<(r : ℝ) := Nat.cast_pos.mpr hr
  have hL : 0<Real.log (2/δ) := Real.log_pos (by apply (lt_div_iff₀ hδ).mpr; linarith)
  have hsqrt : Real.sqrt (φ^2*Real.log (2/δ)/(2*(r : ℝ)))≤(1/2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    apply (div_le_iff₀ (by positivity : 0<2*(r : ℝ))).mpr
    dsimp [φ]
    nlinarith
  have hth : Real.sqrt (φ^2*Real.log (2/δ)/(2*(r : ℝ)))*sketchSquared A≤ sketchSquared A/2 := by
    have hh := mul_le_mul_of_nonneg_right hsqrt hA.le
    nlinarith
  refine (show p.probEvent (fun ω : Fin r→K=>
      sketchSquared (compactSketched (compactSketchData p r ω) A)=0 ∨
      2*(sketchSquared Ah/sketchSquared A)<
        sketchSquared Ah/sketchSquared (compactSketched (compactSketchData p r ω) A))≤
    p.probEvent (fun ω : Fin r→K=>Real.sqrt (φ^2*Real.log (2/δ)/(2*(r : ℝ)))*sketchSquared A≤
      |sketchSquared (compactSketched (compactSketchData p r ω) A)-sketchSquared A|) from ?_).trans ht
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ ω,?_⟩
    rcases (Finset.mem_filter.mp hω).2 with hz | hb
    · rw [hz,zero_sub,abs_neg,abs_of_pos hA]
      linarith
    · have hZ := sketchSquared_nonneg (compactSketched (compactSketchData p r ω) A)
      by_cases hz : sketchSquared (compactSketched (compactSketchData p r ω) A)=0
      · rw [hz,zero_sub,abs_neg,abs_of_pos hA]; linarith
      · have hZp : 0<sketchSquared (compactSketched (compactSketchData p r ω) A) := lt_of_le_of_ne hZ (Ne.symm hz)
        have hh := (lt_div_iff₀ hZp).mp hb
        change 2*φ*sketchSquared
            (compactSketched (compactSketchData p r ω) A)<sketchSquared Ah at hh
        rw [← hφA] at hh
        have hf : sketchSquared (compactSketched (compactSketchData p r ω) A)<sketchSquared A/2 :=
            by nlinarith
        rw [abs_of_neg (by linarith)]
        linarith
  · intro ω _ _
    exact Finset.prod_nonneg fun i _=>p.nonneg _

end Qatlib.Concepts.SketchArith.TransposeAccess
