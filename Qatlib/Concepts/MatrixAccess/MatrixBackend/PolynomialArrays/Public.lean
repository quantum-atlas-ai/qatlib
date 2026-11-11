/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Fuel

set_option backward.isDefEq.respectTransparency false

/-! Public exact-array algorithms and generated-domain correctness contracts. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open RootYunInternal.ActualYunRationalArray RootYunInternal.ActualYunPrimitive
open RootYunInternal.ActualYunPrimitiveContent RootYunInternal.ActualYunContentSupply
open RootYunInternal.ActualYunArrayLoop RootYunInternal.ActualYunContentGuard
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

open RootYunInternal.ActualYunRationalCanonical

/-- A nonzero rational array with its exact degree-length shape is canonical. -/
theorem canonical_of_degree_length (a : List ℚ) (ha : poly a≠0)
    (hlen : a.length=(poly a).natDegree+1) : Canonical a := by
  have hidx : a.length-1=(poly a).natDegree := by omega
  have hlast : a.getD (a.length-1) 0≠0 := by
    rw [← RootYunInternal.ActualYunRationalArray.coeff,hidx]
    exact Polynomial.leadingCoeff_ne_zero.mpr ha
  induction a using List.reverseRecOn with
  | nil => exact (ha poly_nil).elim
  | append_singleton a x ih =>
    have hx : x≠0 := by
      have he : (a++[x]).getD ((a++[x]).length-1) 0=x := by
        simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel,
          List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
      rw [he] at hlast
      exact hlast
    change trim (a++[x])=a++[x]
    simp [trim,hx]

/-- Literal exact-value model of source squarefree_factors, including its
array gcd, exact division, primitive integers and after-step exponent guard.
The derived finite fuel cannot exhaust on the stated nonconstant domain. -/
def rootYunSquarefreeFactors (a : List ℚ) : Option (List (List ℤ×ℕ)) := squarefreeArrays a

/-- Source ordered rational multiplication of every stored factor, repeated
by its own exponent, starting from the actual one-cell array [1]. -/
def rootYunFactorProduct (out : List (List ℤ×ℕ)) : List ℚ :=
  RootYunInternal.ActualYunProductArrays.factorsProduct out [1]

/-- Mathematical integer polynomial of the same actual stored factors. -/
def rootYunIntegerProduct (out : List (List ℤ×ℕ)) : ℤ[X] :=
  (out.map (fun f => (⟨⟨f.1.toFinsupp⟩⟩ : ℤ[X])^f.2)).prod

/-- Construction for Root Yun Factor Good in the public model. -/
def RootYunFactorGood (f : List ℤ×ℕ) : Prop :=
  (rootIntegerListPolynomial f.1).Separable ∧
    0<(rootIntegerListPolynomial f.1).natDegree ∧
    f.1.length=(rootIntegerListPolynomial f.1).natDegree+1 ∧
    f.1.getD (f.1.length-1) 0≠0 ∧ 0<f.2

/-- No factor, gcd, quotient, separability or successful-run answer is input.
The product here deliberately normalizes each stored integer factor. -/
theorem rootYun_generated_factors (a : List ℚ) (ha : (⟨⟨a.toFinsupp⟩⟩ : ℚ[X])≠0)
    (hd : 0<(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree) :
    ∃ out,rootYunSquarefreeFactors a=some out ∧
      normalize (⟨⟨a.toFinsupp⟩⟩ : ℚ[X])=
        (out.map (fun f => normalize ((⟨⟨f.1.toFinsupp⟩⟩ : ℤ[X]).map (Int.castRingHom ℚ))^f.2)).prod ∧
      ∀ f∈out,RootYunFactorGood f ∧ f.2≤(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree :=
  generated_integer_factors a ha hd

/-- Actual primitive integer outputs recover the original raw integer target
with a derived nonzero integer content. No content answer is supplied. -/
theorem rootYun_generated_integer_product (a : List ℤ) (ha : (⟨⟨a.toFinsupp⟩⟩ : ℤ[X])≠0)
    (hd : 0<(⟨⟨a.toFinsupp⟩⟩ : ℤ[X]).natDegree) :
    ∃ (out : List (List ℤ×ℕ)) (c : ℤ),
      rootYunSquarefreeFactors (a.map (fun z : ℤ => (z : ℚ)))=some out ∧
      (c : ℚ)=((⟨⟨a.toFinsupp⟩⟩ : ℤ[X]).map (Int.castRingHom ℚ)).leadingCoeff/
        ((rootYunIntegerProduct out).map (Int.castRingHom ℚ)).leadingCoeff ∧
      c≠0 ∧ (⟨⟨a.toFinsupp⟩⟩ : ℤ[X])=C c*rootYunIntegerProduct out ∧
      ∀ f∈out,RootYunFactorGood f ∧ f.2≤(⟨⟨a.toFinsupp⟩⟩ : ℤ[X]).natDegree ∧
        (⟨⟨f.1.toFinsupp⟩⟩ : ℤ[X]).IsPrimitive :=
  generated_content a ha hd

/-- Actual signed primitive remainder chain for source real_intervals.
The nonconstant-domain success theorem computes it from the input array. -/
def rootSturmChain (a : List ℚ) : Option (List (List ℤ)) :=
  RootYunInternal.ActualSturmChain.sourceChain a

/-- Source zero-skipping integer signs followed by the literal zip sum. -/
def rootSturmVariation (chain : List (List ℤ)) (x : ℚ) : ℕ :=
  RootYunInternal.ActualSturmVariationLoop.literalSourceVariation chain x

/-- Original distinct real roots; multiplicities are deliberately discarded. -/
noncomputable def rootSturmRealRoots (a : List ℚ) : Finset ℝ :=
  ((⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).map (Rat.castHom ℝ)).roots.toFinset

/-- The exact-value isolation run. Fuel bounds finite evaluation of the
source while loop; it is not an extra source acceptance condition. Sorting
has the canonical lexicographic sorted-permutation value specification. -/
def rootSturmIntervals (a : List ℚ) (bits fuel : ℕ) : Option (List (ℚ×ℚ)) :=
  RootYunInternal.ActualSturmComputedIsolation.intervals a bits fuel

/-- Construction for Root Sturm Good Interval in the public model. -/
def RootSturmGoodInterval (a : List ℚ) (bits : ℕ) (p : ℚ×ℚ) : Prop :=
  p.1<p.2 ∧ (p.1 : ℝ)∉rootSturmRealRoots a ∧ (p.2 : ℝ)∉rootSturmRealRoots a ∧
    ((rootSturmRealRoots a).filter (fun x => (p.1 : ℝ)<x ∧ x<(p.2 : ℝ))).card=1 ∧
    p.2-p.1≤1/(2 : ℚ)^bits

/-- Number of output open intervals containing this point. -/
noncomputable def rootSturmHits (ps : List (ℚ×ℚ)) (x : ℝ) : ℕ := by
  classical
  exact (ps.map (fun p => if (p.1 : ℝ)<x ∧ x<(p.2 : ℝ) then 1 else 0)).sum

/-- Construction for Root Sturm Apart in the public model. -/
def RootSturmApart (p q : ℚ×ℚ) : Prop := p.2≤q.1 ∨ q.2≤p.1
/-- Construction for Root Sturm Lex LE in the public model. -/
def RootSturmLexLE (p q : ℚ×ℚ) : Prop := p.1<q.1 ∨ p.1=q.1 ∧ p.2≤q.2

/-- The same computed chain counts original distinct real roots in every
open rational interval with a nonroot right endpoint. Left roots are
allowed: zero skipping makes the variation right continuous. -/
theorem rootSturm_generated_counts (a : List ℚ) (ha : (⟨⟨a.toFinsupp⟩⟩ : ℚ[X])≠0)
    (hd : 0<(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree)
    (hlen : a.length=(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree+1) :
    ∃ chain,rootSturmChain a=some chain ∧
      ∀ left right : ℚ,left≤right → (⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).eval right≠0 →
        rootSturmVariation chain left=rootSturmVariation chain right+
          ((rootSturmRealRoots a).filter (fun x => (left : ℝ)<x ∧ x<(right : ℝ))).card := by
  have hcan := canonical_of_degree_length a ha hlen
  exact RootYunInternal.ActualSturmVariationLoop.computed_literal_counts a hcan ha hd

/-- All chain/count/Cauchy/cut/queue/width/coverage facts are derived from
this same nonconstant canonical array. No interval, root, separation gap,
count or successful-run answer is supplied. The ghost termination rank
proves finite fuel existence, not a polynomial bit-cost bound. -/
theorem rootSturm_generated_intervals (a : List ℚ) (ha : (⟨⟨a.toFinsupp⟩⟩ : ℚ[X])≠0)
    (hd : 0<(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree)
    (hlen : a.length=(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree+1) (bits : ℕ) :
    ∃ fuel result,rootSturmIntervals a bits fuel=some result ∧
      (∀ p∈result,RootSturmGoodInterval a bits p) ∧
      (∀ x∈rootSturmRealRoots a,rootSturmHits result x=1) ∧
      result.Pairwise RootSturmApart ∧ result.Pairwise RootSturmLexLE := by
  have hcan := canonical_of_degree_length a ha hlen
  exact RootYunInternal.ActualSturmComputedIsolation.computed_isolation a hcan ha hd bits

/-- Exact-value model of source determinant on its decoded rational square
matrix domain. The body performs the full array pivot/swap/cell loops. -/
def rootProjectionGaussian (N : ℕ) (A : Matrix (Fin N) (Fin N) ℚ) : ℚ :=
  RootYunInternal.ActualProjectionGaussianLoop.determinant N A

/-- Literal source padding, descending coefficient rows and Gaussian loop;
m/n are the fixed symbolic sizes, even if specialization drops degree. -/
def rootProjectionFixedResultant (a b : List ℚ) (m n : ℕ) : ℚ :=
  RootYunInternal.ActualProjectionResultantSamples.fixedResultant a b m n

/-- Literal forward-difference values/basis/out array loop. Finite fuel is
the initial values length; success is derived for every rational list. -/
def rootProjectionInterpolate (values : List ℚ) : Option (List ℚ) :=
  RootYunInternal.ActualProjectionInterpolationLoop.interpolate values

/-- Actual samples and interpolation for already specified integer
bivariate source inputs. This does not construct the sparse source U/V. -/
def rootProjectionBivariateValues (F G : ℤ[X][X]) (m n D : ℕ) : Option (List ℚ) :=
  RootYunInternal.ActualProjectionComputedResultant.compute
    (RootYunInternal.ActualProjectionComputedResultant.castBivariate F)
    (RootYunInternal.ActualProjectionComputedResultant.castBivariate G) m n D

/-- Same computed arrays followed by source empty/denominator checks and
map(int,out). Symbolic nonzero still has to be proved for actual source U/V. -/
def rootProjectionFromBivariate (F G : ℤ[X][X]) (m n D : ℕ) : Option (List ℤ) :=
  RootYunInternal.ActualProjectionIntegerGuard.project F G m n D

/-- The finite construction in `Public` satisfies `rootProjection_gaussian_value` under the displayed hypotheses. -/
theorem rootProjection_gaussian_value (N : ℕ) (A : Matrix (Fin N) (Fin N) ℚ) :
    rootProjectionGaussian N A=A.det :=
  RootYunInternal.ActualProjectionGaussianLoop.source_determinant_eq N A

/-- The finite construction in `Public` satisfies `rootProjection_fixed_resultant_value` under the displayed hypotheses. -/
theorem rootProjection_fixed_resultant_value (a b : List ℚ) (m n : ℕ)
    (ha : a.length ≤ m+1) (hb : b.length ≤ n+1) :
    rootProjectionFixedResultant a b m n=(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).resultant (⟨⟨b.toFinsupp⟩⟩ : ℚ[X]) m n :=
  RootYunInternal.ActualProjectionResultantSamples.fixedResultant_eq a b m n ha hb

/-- No interpolation answer is input: the actual difference/basis/out loop
recovers P from its supplied sample values and the strict sample-count bound. -/
theorem rootProjection_interpolate_exact (P : ℚ[X]) (values : List ℚ)
    (hd : P.natDegree < values.length)
    (hv : ∀ i : Fin values.length,values.getD i.val 0=P.eval (i.val : ℚ)) :
    ∃ result,rootProjectionInterpolate values=some result ∧ (⟨⟨result.toFinsupp⟩⟩ : ℚ[X])=P :=
  RootYunInternal.ActualProjectionInterpolationLoop.interpolate_recovers P values hd hv

/-- This consumer generates the samples itself, using the same source
Gaussian loop at exactly 2*D*D+1 points. Integer inputs supply all output
denominators without an integrality answer. Source U/V size and degree
facts are still explicit until their sparse construction is connected. -/
theorem rootProjection_generated_integral_values (F G : ℤ[X][X]) (m n D : ℕ)
    (hFm : F.natDegree ≤ m) (hGn : G.natDegree ≤ n) (hm : m ≤ D) (hn : n ≤ D)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D) :
    ∃ result,rootProjectionBivariateValues F G m n D=some result ∧
      (⟨⟨result.toFinsupp⟩⟩ : ℚ[X])=(F.resultant G m n).map (Int.castRingHom ℚ) ∧
      ∀ j : ℕ,(result.getD j 0).den=1 :=
  RootYunInternal.ActualProjectionComputedResultant.integral_computed_resultant F G m n D hFm hGn hm hn hF hG

/-- The nonempty guard remains explicitly conditional on the symbolic
resultant being nonzero. It is not a proof of original-factor projections
or complete complex root-certificate production. -/
theorem rootProjection_generated_integer_resultant (F G : ℤ[X][X]) (m n D : ℕ)
    (hFm : F.natDegree ≤ m) (hGn : G.natDegree ≤ n) (hm : m ≤ D) (hn : n ≤ D)
    (hF : ∀ k,(F.coeff k).natDegree ≤ D) (hG : ∀ k,(G.coeff k).natDegree ≤ D)
    (hres : F.resultant G m n ≠ 0) :
    ∃ result,rootProjectionFromBivariate F G m n D=some result ∧
      (⟨⟨result.toFinsupp⟩⟩ : ℤ[X])=F.resultant G m n :=
  RootYunInternal.ActualProjectionIntegerGuard.source_integer_guard F G m n D hFm hGn hm hn hF hG hres

/-- Source sparse binomial U/V construction followed by its actual max,
fixed-size specialization/Gaussian samples, interpolation and integer guard.
No symbolic F/G, sizes, resultant or projection answer is a program input. -/
def rootProjectionFromIntegerList (cs : List ℤ) : Option (List ℤ) × Option (List ℤ) :=
  RootYunInternal.ActualProjectionGeneratedAxes.projections cs

/-- Derived array shape and single-coordinate coverage. This allows extra
projection roots and does not identify arbitrary coordinate pairs as roots. -/
def RootProjectionArrayGood (cs out : List ℤ) (coord : ℂ → ℝ) : Prop :=
  out.length=(⟨⟨(out.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X]).natDegree+1 ∧
    (⟨⟨(out.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X]) ≠ 0 ∧
    0 < (⟨⟨(out.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X]).natDegree ∧
    ∀ z : ℂ,(rootIntegerListPolynomial cs).eval z=0 →
      (rootIntegerListPolynomial out).eval (coord z : ℂ)=0

/-- The finite construction in `Public` satisfies `projection_output_public` under the displayed hypotheses. -/
private theorem projection_output_public (cs out : List ℤ)
    (axis : RootYunInternal.ActualProjectionEntryDegrees.Axis)
    (h : RootYunInternal.ActualProjectionProducedArrays.OutputProperties cs axis out) :
    RootProjectionArrayGood cs out (RootYunInternal.ActualProjectionProducedArrays.coordinate axis) := by
  obtain ⟨hcan,hn,hd,hcoord⟩ := h
  have hlen := RootYunInternal.ActualYunRationalCanonical.canonical_length _ hcan
    ((RootYunInternal.ActualYunRationalCanonical.canonical_nonzero _ hcan).mpr hn)
  exact ⟨by simpa only [RootYunInternal.ActualSturmArrayTools.lift, RootYunInternal.ActualYunRationalArray.poly, List.length_map] using hlen,hn,hd,hcoord⟩

/-- The actual nonconstant highest-nonzero integer input supplies all
source U/V/max/degree, nonzero/integer/canonical and coordinate facts.
Repeated roots are allowed; no hres or separability answer is an input. -/
theorem rootProjection_generated_arrays (cs : List ℤ) (D : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0 ≠ 0) :
    ∃ rx ry,rootProjectionFromIntegerList cs=(some rx,some ry) ∧
      RootProjectionArrayGood cs rx Complex.re ∧ RootProjectionArrayGood cs ry Complex.im := by
  obtain ⟨rx,ry,hr,hx,hy⟩ := RootYunInternal.ActualProjectionProducedArrays.actual_projection_pair cs D hlen hD hlead
  exact ⟨rx,ry,hr,projection_output_public cs rx _ hx,projection_output_public cs ry _ hy⟩

/-- Same generated arrays and two exact Sturm runs. Ghost fuel witnesses
finite evaluation, without claiming an explicit polynomial fee. -/
def rootProjectionAxesIntervals (cs : List ℤ) (bits fuelX fuelY : ℕ) :
    Option (List (ℚ×ℚ) × List (ℚ×ℚ)) :=
  RootYunInternal.ActualProjectionSturmAxes.isolateAxes cs bits fuelX fuelY

/-- Literal nested midpoint loops of the two actual interval lists. -/
def rootProjectionCartesianCenters (ix iy : List (ℚ×ℚ)) : List (ℚ×ℚ) :=
  RootYunInternal.ActualProjectionCartesian.centers ix iy

/-- Number of produced open Cartesian rectangles containing this point. -/
noncomputable def rootProjectionCartesianHits (ix iy : List (ℚ×ℚ)) (z : ℂ) : ℕ :=
  RootYunInternal.ActualProjectionCartesian.rectangleHits
    (RootYunInternal.ActualProjectionCartesian.rectangles ix iy) z

/-- Both interval families are generated from the same raw cs. Their
root/count/separation and interval answers are derived internally. -/
theorem rootProjection_generated_axes (cs : List ℤ) (D bits : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0 ≠ 0) :
    ∃ fuelX fuelY rx ry ix iy,rootProjectionFromIntegerList cs=(some rx,some ry) ∧
      rootProjectionAxesIntervals cs bits fuelX fuelY=some (ix,iy) ∧
      (∀ p∈ix,RootSturmGoodInterval (rx.map (fun z : ℤ => (z : ℚ))) bits p) ∧
      (∀ p∈iy,RootSturmGoodInterval (ry.map (fun z : ℤ => (z : ℚ))) bits p) ∧
      (∀ x∈rootSturmRealRoots (rx.map (fun z : ℤ => (z : ℚ))),rootSturmHits ix x=1) ∧
      (∀ y∈rootSturmRealRoots (ry.map (fun z : ℤ => (z : ℚ))),rootSturmHits iy y=1) ∧
      ix.Pairwise RootSturmApart ∧ iy.Pairwise RootSturmApart ∧
      ix.Pairwise RootSturmLexLE ∧ iy.Pairwise RootSturmLexLE ∧
      ∀ z : ℂ,(rootIntegerListPolynomial cs).eval z=0 → rootSturmHits ix z.re=1 ∧ rootSturmHits iy z.im=1 := by
  obtain ⟨fx,fy,rx,ry,ix,iy,hpr,hr,_,_,hx,hy⟩ :=
    RootYunInternal.ActualProjectionSturmAxes.computed_axes cs D bits hlen hD hlead
  exact ⟨fx,fy,rx,ry,ix,iy,hpr,hr,hx.1,hy.1,hx.2.1,hy.2.1,hx.2.2.1,hy.2.2.1,
    hx.2.2.2.1,hy.2.2.2.1,fun z hz => ⟨hx.2.2.2.2 z hz,hy.2.2.2.2 z hz⟩⟩

/-- Every original complex root lies in exactly one produced rectangle,
with an actual nested-loop midpoint at most 2^-bits away. Additional
candidates may remain; filtering, accepted certificates and fees are open. -/
theorem rootProjection_generated_cartesian (cs : List ℤ) (D bits : ℕ) (hlen : cs.length=D+1)
    (hD : 0 < D) (hlead : cs.getD D 0 ≠ 0) :
    ∃ fuelX fuelY ix iy,rootProjectionAxesIntervals cs bits fuelX fuelY=some (ix,iy) ∧
      ∀ z : ℂ,(rootIntegerListPolynomial cs).eval z=0 → rootProjectionCartesianHits ix iy z=1 ∧
        ∃ c∈rootProjectionCartesianCenters ix iy,‖rootRationalCoordinate c-z‖ ≤ ((1/(2 : ℚ)^bits : ℚ) : ℝ) :=
  RootYunInternal.ActualProjectionCartesian.computed_cartesian cs D bits hlen hD hlead

/-- Explicit numerical fuel for an integer projection array. Degree and
coefficient height are values of the complete stored array, not their
encoding lengths. This bounds queue fuel, not total bit/physical cost. -/
def rootSturmNumericFuel (a : List ℤ) (bits : ℕ) : ℕ :=
  RootYunInternal.ActualSturmNumericalFuel.fuelBudget a bits

/-- Actual first successful fuel, computed by testing literal Option trials.
Legal-input proofs are erased; no successful fuel/root/gap is an input. -/
def rootSturmSearchedFuel (a : List ℚ) (ha : (⟨⟨a.toFinsupp⟩⟩ : ℚ[X])≠0)
    (hd : 0<(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree)
    (hlen : a.length=(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree+1) (bits : ℕ) : ℕ :=
  RootYunInternal.ActualFiniteFuelSearch.fuel
    (RootYunInternal.ActualSturmComputedIsolation.intervals a bits)
    (RootYunInternal.ActualSturmFuelSearch.exists_success a
      (canonical_of_degree_length a ha hlen) ha hd bits)

/-- Full ordered list returned by the actual least-fuel search. -/
def rootSturmSearchedIntervals (a : List ℚ) (ha : (⟨⟨a.toFinsupp⟩⟩ : ℚ[X])≠0)
    (hd : 0<(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree)
    (hlen : a.length=(⟨⟨a.toFinsupp⟩⟩ : ℚ[X]).natDegree+1) (bits : ℕ) : List (ℚ×ℚ) :=
  RootYunInternal.ActualSturmFuelSearch.searched a
    (canonical_of_degree_length a ha hlen) ha hd bits

/-- On the same legal integer projection, the fully numerical fuel succeeds
with precisely the actual searched list, whose least successful fuel is
bounded by it. All original coverage/width/order guarantees are retained.
No root set, interval, first factor, separation or run answer is supplied. -/
theorem rootSturm_integer_numeric_search (a : List ℤ)
    (ha : (⟨⟨(a.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X])≠0)
    (hd : 0<(⟨⟨(a.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X]).natDegree)
    (hlen : (a.map (fun z : ℤ => (z : ℚ))).length=
      (⟨⟨(a.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X]).natDegree+1) (bits : ℕ) :
    let A := a.map (fun z : ℤ => (z : ℚ))
    let result := rootSturmSearchedIntervals A ha hd hlen bits
    rootSturmSearchedFuel A ha hd hlen bits≤rootSturmNumericFuel a bits ∧
      rootSturmIntervals A bits (rootSturmNumericFuel a bits)=some result ∧
      (∀ p∈result,RootSturmGoodInterval A bits p) ∧
      (∀ x∈rootSturmRealRoots A,rootSturmHits result x=1) ∧
      result.Pairwise RootSturmApart ∧ result.Pairwise RootSturmLexLE := by
  have hcan := canonical_of_degree_length (a.map (fun z : ℤ => (z : ℚ))) ha hlen
  obtain ⟨hf,he⟩ := RootYunInternal.ActualSturmNumericalFuel.original_search_numerical a hcan ha hd bits
  have hgood := RootYunInternal.ActualSturmFuelSearch.searched_correct
    (a.map (fun z : ℤ => (z : ℚ))) hcan ha hd bits
  exact ⟨hf,he,hgood⟩

/-- Complete numeric expression in the stored array's degree, coefficient
bit height and requested precision VALUE. This is not a total bit fee. -/
theorem rootSturm_numeric_fuel_formula (a : List ℤ) (bits : ℕ) :
    let D := a.length-1
    let H := (a.map (fun z => z.natAbs.size)).foldl max 0
    rootSturmNumericFuel a bits=8*D*(H+D*(H+2)+3+
      max bits (D*D*(H+D*(H+2)+2)+1))+1 := by
  exact RootYunInternal.ActualSturmNumericalFuel.fuelBudget_formula a bits

/-- Both actual generated projection arrays now use their own explicit
coefficient-derived numeric fuel; original complex-root coordinates and
full interval guarantees come from the same produced lists. -/
theorem rootProjection_generated_numeric_axes (cs : List ℤ) (D bits : ℕ)
    (hlen : cs.length=D+1) (hD : 0<D) (hlead : cs.getD D 0≠0) :
    ∃ rx ry ix iy,rootProjectionFromIntegerList cs=(some rx,some ry) ∧
      rootProjectionAxesIntervals cs bits (rootSturmNumericFuel rx bits)
        (rootSturmNumericFuel ry bits)=some (ix,iy) ∧
      (∀ p∈ix,RootSturmGoodInterval (rx.map (fun z : ℤ => (z : ℚ))) bits p) ∧
      (∀ p∈iy,RootSturmGoodInterval (ry.map (fun z : ℤ => (z : ℚ))) bits p) ∧
      (∀ x∈rootSturmRealRoots (rx.map (fun z : ℤ => (z : ℚ))),rootSturmHits ix x=1) ∧
      (∀ y∈rootSturmRealRoots (ry.map (fun z : ℤ => (z : ℚ))),rootSturmHits iy y=1) ∧
      ix.Pairwise RootSturmApart ∧ iy.Pairwise RootSturmApart ∧
      ix.Pairwise RootSturmLexLE ∧ iy.Pairwise RootSturmLexLE ∧
      ∀ z : ℂ,(rootIntegerListPolynomial cs).eval z=0 →
        rootSturmHits ix z.re=1 ∧ rootSturmHits iy z.im=1 := by
  obtain ⟨rx,ry,hproj,hx,hy⟩ := rootProjection_generated_arrays cs D hlen hD hlead
  have hxl : (rx.map (fun z : ℤ => (z : ℚ))).length=
      (⟨⟨(rx.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X]).natDegree+1 := by
    simpa only [List.length_map] using hx.1
  have hyl : (ry.map (fun z : ℤ => (z : ℚ))).length=
      (⟨⟨(ry.map (fun z : ℤ => (z : ℚ))).toFinsupp⟩⟩ : ℚ[X]).natDegree+1 := by
    simpa only [List.length_map] using hy.1
  obtain ⟨_,hrx,hgoodx,hcoverx,hapartx,hsortx⟩ :=
    rootSturm_integer_numeric_search rx hx.2.1 hx.2.2.1 hxl bits
  obtain ⟨_,hry,hgoody,hcovery,haparty,hsorty⟩ :=
    rootSturm_integer_numeric_search ry hy.2.1 hy.2.2.1 hyl bits
  refine ⟨rx,ry,_,_,hproj,?_,hgoodx,hgoody,hcoverx,hcovery,hapartx,haparty,hsortx,hsorty,?_⟩
  · change RootYunInternal.ActualProjectionGeneratedAxes.projections cs=(some rx,some ry) at hproj
    change RootYunInternal.ActualSturmComputedIsolation.intervals _ _ _=some _ at hrx hry
    simp only [rootProjectionAxesIntervals,RootYunInternal.ActualProjectionSturmAxes.isolateAxes,
      hproj,RootYunInternal.ActualSturmArrayTools.lift,hrx,hry,Option.bind_some,Option.map_some]
  · intro z hz
    exact ⟨hcoverx _ (RootYunInternal.ActualProjectionSturmAxes.real_root_member rx hx.2.1 z.re (hx.2.2.2 z hz)),
      hcovery _ (RootYunInternal.ActualProjectionSturmAxes.real_root_member ry hy.2.1 z.im (hy.2.2.2 z hz))⟩


end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
