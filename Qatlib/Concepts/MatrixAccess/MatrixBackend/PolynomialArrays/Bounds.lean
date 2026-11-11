/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Find
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.Nodup
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.List.Sort
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Data.List.Induction
import Mathlib.Data.List.ToFinsupp
import Mathlib.RingTheory.Polynomial.GaussLemma
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Projection

set_option backward.isDefEq.respectTransparency false

/-! Exact polynomial-array algorithms: Bounds.
Ported from OQ #132 at c0d79a391c008771dd64bd305ec2133c1b32c2d6,
retaining program bodies, guards, hypotheses and finite-fuel semantics. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
namespace RootYunInternal

namespace ActualRootProjectionCap
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Abbreviation for Context in the bounds model. -/
abbrev Context := RootProjectionContext

/-- Construction for list Max in the bounds model. -/
def listMax (xs : List ℕ) : ℕ := xs.foldl max 0
/-- Construction for degree in the bounds model. -/
def degree (f : List ℤ) : ℕ := f.length-1
/-- Construction for height in the bounds model. -/
def height (f : List ℤ) : ℕ := listMax (f.map (fun a => a.natAbs.size))
/-- Construction for a Exponent in the bounds model. -/
def aExponent (c : Context) : ℕ :=
  degree c.factor * degree c.factor * (height c.factor+2) * (degree c.factor-1)
/-- Construction for m Exponent in the bounds model. -/
def mExponent (c : Context) : ℕ :=
  3*sourceCeilLog2 (degree c.factor)+height c.factor+
    degree c.factor*(height c.factor+2)
/-- Construction for separation Exponent in the bounds model. -/
def separationExponent (f : List ℤ) : ℕ :=
  degree f * degree f * (height f+degree f*(height f+2)+2)
/-- Construction for context Terms in the bounds model. -/
def contextTerms (c : Context) : List ℕ :=
  [aExponent c+mExponent c+sourceCeilLog2 (8*degree c.factor)+4,
   separationExponent c.xProjection+5, separationExponent c.yProjection+5]
/-- Construction for terms in the bounds model. -/
def terms (contexts : List Context) (bits : ℕ) (gap : ℚ) : List ℕ :=
  [bits+4,sourceCeilLog2 (1/gap)+4] ++ contexts.flatMap contextTerms
/-- Construction for cap in the bounds model. -/
def cap (contexts : List Context) (bits : ℕ) (gap : ℚ) : ℕ :=
  max (2*bits+16) (2*(listMax (terms contexts bits gap)+2))
/-- Construction for half in the bounds model. -/
def half (contexts : List Context) (bits : ℕ) (gap : ℚ) : ℕ := cap contexts bits gap/2
/-- Construction for radius in the bounds model. -/
def radius (contexts : List Context) (bits : ℕ) (gap : ℚ) : ℚ :=
  1/(2 : ℚ)^half contexts bits gap
/-- Construction for midpoint Error in the bounds model. -/
def midpointError (contexts : List Context) (bits : ℕ) (gap : ℚ) : ℚ :=
  1/(2 : ℚ)^cap contexts bits gap

/-- The finite construction in `Bounds` satisfies `fold_max_initial` under the displayed hypotheses. -/
theorem fold_max_initial (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))
/-- The finite construction in `Bounds` satisfies `fold_max_member` under the displayed hypotheses. -/
theorem fold_max_member (xs : List ℕ) (a x : ℕ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst y
      exact (le_max_right a x).trans (fold_max_initial ys (max a x))
    · exact ih (max a y) h

/-- The finite construction in `Bounds` satisfies `half_ge_term` under the displayed hypotheses. -/
theorem half_ge_term (contexts : List Context) (bits t : ℕ) (gap : ℚ)
    (ht : t ∈ terms contexts bits gap) : t+2 ≤ half contexts bits gap := by
  have hm := fold_max_member (terms contexts bits gap) 0 t ht
  have hc := le_max_right (2*bits+16) (2*(listMax (terms contexts bits gap)+2))
  change t+2 ≤ cap contexts bits gap/2
  unfold cap
  change t ≤ listMax (terms contexts bits gap) at hm
  omega

/-- The finite construction in `Bounds` satisfies `cap_even` under the displayed hypotheses. -/
theorem cap_even (contexts : List Context) (bits : ℕ) (gap : ℚ) :
    cap contexts bits gap = 2*half contexts bits gap := by
  unfold cap half cap
  omega

/-- The finite construction in `Bounds` satisfies `half_ge_bits` under the displayed hypotheses. -/
theorem half_ge_bits (contexts : List Context) (bits : ℕ) (gap : ℚ) :
    bits+8 ≤ half contexts bits gap := by
  have hc := le_max_left (2*bits+16) (2*(listMax (terms contexts bits gap)+2))
  change bits+8 ≤ cap contexts bits gap/2
  unfold cap
  omega

/-- The finite construction in `Bounds` satisfies `midpoint_square` under the displayed hypotheses. -/
theorem midpoint_square (contexts : List Context) (bits : ℕ) (gap : ℚ) :
    midpointError contexts bits gap = radius contexts bits gap ^ 2 := by
  unfold midpointError radius
  rw [cap_even, Nat.mul_comm 2 (half contexts bits gap), pow_mul]
  simp only [one_div, inv_pow]

/-- The finite construction in `Bounds` satisfies `cap_radius_budgets` under the displayed hypotheses. -/
theorem cap_radius_budgets (contexts : List Context) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) :
    0 < radius contexts bits gap ∧ radius contexts bits gap ≤ 1 ∧
      radius contexts bits gap ≤ (1/(2 : ℚ)^bits)/256 ∧
      radius contexts bits gap ≤ gap/64 := by
  have hb := half_ge_bits contexts bits gap
  have hp : (2 : ℚ)^(bits+8) ≤ 2^half contexts bits gap :=
    pow_le_pow_right₀ (by norm_num) hb
  have he := sourceCeilLog2_envelope (1/gap) (by positivity)
  have ht : sourceCeilLog2 (1/gap)+4 ∈ terms contexts bits gap := by
    simp [terms]
  have hs := half_ge_term contexts bits _ gap ht
  have hgp : (2 : ℚ)^(sourceCeilLog2 (1/gap)+6) ≤ 2^half contexts bits gap :=
    pow_le_pow_right₀ (by norm_num) hs
  have hbig : 64/gap ≤ (2 : ℚ)^half contexts bits gap := by
    calc
      _ = 64*(1/gap) := by ring
      _ ≤ 64*(2 : ℚ)^sourceCeilLog2 (1/gap) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = (2 : ℚ)^(sourceCeilLog2 (1/gap)+6) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := hgp
  have hrb : radius contexts bits gap ≤ (1/(2 : ℚ)^bits)/256 := by
    unfold radius
    calc
      _ ≤ 1/(2 : ℚ)^(bits+8) := one_div_le_one_div_of_le (by positivity) hp
      _ = _ := by rw [pow_add]; norm_num; ring
  have hrg : radius contexts bits gap ≤ gap/64 := by
    unfold radius
    apply (div_le_iff₀ (by positivity)).mpr
    have hx := (div_le_iff₀ hg).mp hbig
    nlinarith only [hx]
  refine ⟨by unfold radius; positivity, ?_, hrb, hrg⟩
  unfold radius
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))


end ActualRootProjectionCap


namespace ActualRootResultantDerivative
open Polynomial

/-- The estimate `norm_product_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem norm_product_bound (s : Multiset ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ x ∈ s, ‖x‖ ≤ M) : ‖s.prod‖ ≤ M^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x xs ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ]
    have hx := hs x (Multiset.mem_cons_self x xs)
    have hr := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    nlinarith [mul_le_mul hx hr (norm_nonneg xs.prod) hM]

/-- The finite construction in `Bounds` satisfies `integer_resultant_derivative_lower` under the displayed hypotheses. -/
theorem integer_resultant_derivative_lower (p : ℤ[X]) (hp : 0 < p.natDegree)
    (hres : p.resultant p.derivative p.natDegree (p.natDegree-1) ≠ 0)
    (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hlead : ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ ≤ B)
    (hupper : ∀ w ∈ (p.map (Int.castRingHom ℂ)).roots,
      ‖(p.map (Int.castRingHom ℂ)).derivative.eval w‖ ≤ M)
    (z : ℂ) (hz : (p.map (Int.castRingHom ℂ)).eval z = 0) :
    1 ≤ B^(p.natDegree-1)*M^(p.natDegree-1)*
      ‖(p.map (Int.castRingHom ℂ)).derivative.eval z‖ := by
  classical
  let f := p.map (Int.castRingHom ℂ)
  let R := p.resultant p.derivative p.natDegree (p.natDegree-1)
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hd : f.natDegree = p.natDegree := Polynomial.natDegree_map_eq_of_injective hinj p
  have hf0 : f ≠ 0 := by intro h; simp [h] at hd; omega
  have hf : f.Splits := IsAlgClosed.splits f
  have hcard : f.roots.card = p.natDegree := hf.natDegree_eq_card_roots.symm.trans hd
  have hmem : z ∈ f.roots := (Polynomial.mem_roots hf0).mpr hz
  have herase : (f.roots.erase z).card = p.natDegree-1 := by
    rw [Multiset.card_erase_of_mem hmem,hcard]
    exact Nat.pred_eq_sub_one
  have hresmap : f.resultant f.derivative p.natDegree (p.natDegree-1) = (R : ℂ) := by
    dsimp only [f,R]
    rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
    rfl
  have hfac : (R : ℂ) = f.leadingCoeff^(p.natDegree-1) *
      (f.roots.map f.derivative.eval).prod := by
    rw [← hresmap, ← hd]
    exact Polynomial.resultant_eq_prod_eval f f.derivative (f.natDegree-1)
      (Polynomial.natDegree_derivative_le f) hf
  have hint : (1 : ℝ) ≤ ‖(R : ℂ)‖ := by
    have hr : (1 : ℝ) ≤ |(R : ℝ)| := by exact_mod_cast Int.one_le_abs hres
    simpa only [Complex.norm_intCast, Int.norm_eq_abs, Int.cast_abs] using hr
  have htail : ‖((f.roots.erase z).map f.derivative.eval).prod‖ ≤ M^(p.natDegree-1) := by
    have h := norm_product_bound ((f.roots.erase z).map f.derivative.eval) M hM ?_
    · simpa only [Multiset.card_map,herase] using h
    · intro w hw
      obtain ⟨u,hu,rfl⟩ := Multiset.mem_map.mp hw
      exact hupper u (Multiset.mem_of_mem_erase hu)
  have hnorm : ‖(R : ℂ)‖ = ‖f.leadingCoeff‖^(p.natDegree-1) *
      ‖f.derivative.eval z‖ * ‖((f.roots.erase z).map f.derivative.eval).prod‖ := by
    conv_lhs => rw [hfac, ← Multiset.cons_erase hmem, Multiset.map_cons, Multiset.prod_cons]
    simp only [norm_mul,norm_pow]
    ring
  calc
    1 ≤ ‖(R : ℂ)‖ := hint
    _ = _ := hnorm
    _ ≤ B^(p.natDegree-1) * ‖f.derivative.eval z‖ * M^(p.natDegree-1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hlead _) (norm_nonneg _)
      · exact htail
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

end ActualRootResultantDerivative


namespace ActualRootHeightEnvelope
open Polynomial
open scoped BigOperators
open ActualRootProjectionCap
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

/-- The estimate `eval_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem eval_bound (p : ℂ[X]) (m : ℕ) (C R : ℝ) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hd : p.natDegree < m) (hcoeff : ∀ i < m, ‖p.coeff i‖ ≤ C)
    (w : ℂ) (hw : ‖w‖ ≤ R) : ‖p.eval w‖ ≤ (m : ℝ)*C*R^m := by
  rw [Polynomial.eval_eq_sum_range' hd]
  calc
    _ ≤ ∑ i ∈ Finset.range m, ‖p.coeff i*w^i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, C*R^m := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      rw [norm_mul,norm_pow]
      apply mul_le_mul (hcoeff i him)
      · exact (pow_le_pow_left₀ (norm_nonneg _) hw i).trans
          (pow_le_pow_right₀ hR him.le)
      · positivity
      · exact hC
    _ = _ := by simp; ring

/-- The finite construction in `Bounds` satisfies `derivatives_from_coefficients` under the displayed hypotheses. -/
theorem derivatives_from_coefficients (p : ℂ[X]) (m : ℕ) (hm : 0 < m)
    (hd : p.natDegree = m) (B R : ℝ) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hcoeff : ∀ i, ‖p.coeff i‖ ≤ B) (w : ℂ) (hw : ‖w‖ ≤ R) :
    ‖p.derivative.eval w‖ ≤ (m : ℝ)^3*B*R^m ∧
      ‖p.derivative.derivative.eval w‖ ≤ (m : ℝ)^3*B*R^m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdeg : p.derivative.natDegree < m := by
    simpa only [hd] using Polynomial.natDegree_derivative_lt (p := p) (by omega)
  have hdeg2 : p.derivative.derivative.natDegree < m :=
    (Polynomial.natDegree_derivative_le p.derivative).trans_lt (by omega)
  have hfirst : ∀ i < m, ‖p.derivative.coeff i‖ ≤ (m : ℝ)*B := by
    intro i hi
    rw [Polynomial.coeff_derivative,norm_mul]
    have hii : ((i+1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hi
    have hn : ‖((i+1 : ℕ) : ℂ)‖ = ((i+1 : ℕ) : ℝ) := Complex.norm_natCast (i+1)
    rw [← Nat.cast_add_one, hn]
    have hh := mul_le_mul (hcoeff (i+1)) hii (by positivity) hB
    nlinarith only [hh]
  have hsecond : ∀ i < m, ‖p.derivative.derivative.coeff i‖ ≤ (m : ℝ)^2*B := by
    intro i _hi
    rw [Polynomial.coeff_derivative,Polynomial.coeff_derivative]
    by_cases hi : i+2 ≤ m
    · have h1 : ((i+1 : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : i+1 ≤ m)
      have h2 : ((i+2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hi
      simp only [norm_mul, ← Nat.cast_add_one, Complex.norm_natCast]
      have hh := mul_le_mul (hcoeff (i+2)) h2 (by positivity) hB
      have hh' := mul_le_mul hh h1 (by positivity) (by positivity : (0 : ℝ) ≤ B*m)
      nlinarith only [hh']
    · have hz : p.coeff (i+1+1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz,zero_mul,zero_mul,norm_zero]
      positivity
  have hf := eval_bound p.derivative m ((m : ℝ)*B) R (by positivity) hR hdeg hfirst w hw
  have hs := eval_bound p.derivative.derivative m ((m : ℝ)^2*B) R
    (by positivity) hR hdeg2 hsecond w hw
  refine ⟨?_, by nlinarith only [hs]⟩
  have hmp : (m : ℝ)^2 ≤ (m : ℝ)^3 := by nlinarith [sq_nonneg ((m : ℝ)-1)]
  have hmul := mul_le_mul_of_nonneg_right hmp (by positivity : (0 : ℝ) ≤ B*R^m)
  nlinarith only [hf,hmul]

/-- The finite construction in `Bounds` satisfies `fold_max_member` under the displayed hypotheses. -/
theorem fold_max_member (xs : List ℕ) (a x : ℕ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  have init : ∀ (ys : List ℕ) (b : ℕ), b ≤ ys.foldl max b := by
    intro ys
    induction ys with
    | nil => intro b; rfl
    | cons y ys ih => intro b; exact (le_max_left b y).trans (ih (max b y))
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst y; exact (le_max_right a x).trans (init ys (max a x))
    · exact ih (max a y) h

/-- The finite construction in `Bounds` satisfies `coefficient_from_height` under the displayed hypotheses. -/
theorem coefficient_from_height (cs : List ℤ) (k : ℕ) :
    ‖(rootIntegerListPolynomial cs).coeff k‖ ≤ (2 : ℝ)^height cs := by
  have hsize : (cs.getD k 0).natAbs.size ≤ height cs := by
    by_cases hk : k < cs.length
    · have hm : cs.getD k 0 ∈ cs := by
        simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using
          List.getElem_mem hk
      exact fold_max_member _ 0 _ (List.mem_map.mpr ⟨_,hm,rfl⟩)
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : cs.length ≤ k),
        Option.getD_none,Int.natAbs_zero,Nat.size_zero]
      exact Nat.zero_le _
  have hn : (cs.getD k 0).natAbs ≤ 2^height cs :=
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hsize)
  rw [rootIntegerListPolynomial_coeff,Complex.norm_intCast]
  simpa only [Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat] using
    (show ((cs.getD k 0).natAbs : ℝ) ≤ (2 : ℝ)^height cs by exact_mod_cast hn)


end ActualRootHeightEnvelope


namespace ActualRootAnalyticSupply
open ActualRootProjectionCap
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
/-- The finite construction in `Bounds` satisfies `cap_horner_without_analytic_answers` under the displayed hypotheses. -/
theorem cap_horner_without_analytic_answers (contexts : List Context) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) (ctx : Context) (hctx : ctx ∈ contexts)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1)) ≠ 0)
    (hfactor : ctx.factor = List.ofFn a) (hsep : (rootIntegerPolynomial a).Separable)
    (z : ℂ) (hz : (rootIntegerPolynomial a).eval z = 0) (c : ℚ×ℚ)
    (hc : ‖rootRationalCoordinate c-z‖ ≤ (midpointError contexts bits gap : ℝ)) :
    rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))) (radius contexts bits gap) ∧
    0 < max
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.1|
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.2| :=
  rootProjectionCap_near_horner contexts bits gap hg ctx hctx n a ha hfactor hsep z hz c hc
end ActualRootAnalyticSupply


namespace ActualProjectionSourceDerivative
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for derivative Raw in the bounds model. -/
def derivativeRaw (cs : List ℤ) : List ℤ := List.ofFn
  (fun i : Fin (cs.length-1) => ((i.val+1 : ℕ) : ℤ)*cs.getD (i.val+1) 0)

/-- Construction for derivative in the bounds model. -/
def derivative (cs : List ℤ) : List ℤ := rootCanonicalCoefficients (derivativeRaw cs)

/-- The finite construction in `Bounds` satisfies `canonical_ofFn` under the displayed hypotheses. -/
theorem canonical_ofFn (d : ℕ) (a : Fin (d+1) → ℤ) (ha : a (Fin.last d)≠0) :
    rootCanonicalCoefficients (List.ofFn a)=List.ofFn a := by
  have he : List.ofFn a=List.ofFn (fun i : Fin d => a i.castSucc)++[a (Fin.last d)] := by simpa only [List.concat_eq_append] using List.ofFn_succ' a
  rw [he]
  simp [rootCanonicalCoefficients,ha]

/-- The finite construction in `Bounds` satisfies `raw_ofFn` under the displayed hypotheses. -/
theorem raw_ofFn (n : ℕ) (a : Fin (n+2) → ℤ) :
    derivativeRaw (List.ofFn a)=List.ofFn (rootIntegerDerivative n a) := by
  unfold derivativeRaw
  simp only [List.length_ofFn,show n+2-1=n+1 by omega]
  apply congrArg List.ofFn
  funext i
  change ((i.val+1 : ℕ) : ℤ)*(List.ofFn a).getD (i.val+1) 0=rootIntegerDerivative n a i
  have hi : i.val+1 < n+2 := by omega
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hi,Option.getD_some]
  rfl

/-- The finite construction in `Bounds` satisfies `derivative_ofFn` under the displayed hypotheses. -/
theorem derivative_ofFn (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0) :
    derivative (List.ofFn a)=List.ofFn (rootIntegerDerivative n a) := by
  rw [derivative,raw_ofFn]
  apply canonical_ofFn
  change ((n+1 : ℕ) : ℤ)*a (Fin.last (n+1))≠0
  exact mul_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n)) ha

/-- The same emitted instruction list satisfies `derivative_length` with the displayed gate and query accounting. -/
theorem derivative_length (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0) :
    (derivative (List.ofFn a)).length=n+1 := by rw [derivative_ofFn n a ha,List.length_ofFn]



end ActualProjectionSourceDerivative


namespace ActualProjectionSourcePasses
open ActualProjectionSourceDerivative
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian

/-- Construction for horner in the bounds model. -/
def horner (cs : List ℤ) (c : ℚ×ℚ) : GaussianIntegerFraction :=
  rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) cs

/-- Construction for source Passes in the bounds model. -/
def sourcePasses (cs : List ℤ) (c : ℚ×ℚ) (r : ℚ) : Bool :=
  let v := horner cs c
  if v.numerator=(0,0) then true else
  let w := horner (derivative cs) c
  let upper := |v.numerator.1|+|v.numerator.2|
  let lower := max |w.numerator.1| |w.numerator.2|
  decide (0 < lower ∧ ((cs.length-1 : ℕ) : ℤ)*upper*(w.denominator : ℤ)*(r.den : ℤ) ≤
    r.num*lower*(v.denominator : ℤ))

/-- The finite construction in `Bounds` satisfies `passes_exact` under the displayed hypotheses. -/
theorem passes_exact (cs : List ℤ) (c : ℚ×ℚ) (r : ℚ) :
    sourcePasses cs c r=true ↔ (horner cs c).numerator=(0,0) ∨
      (0 < max |(horner (derivative cs) c).numerator.1| |(horner (derivative cs) c).numerator.2| ∧
        rootIntegerCoordinateBound (cs.length-1) (horner cs c) (horner (derivative cs) c) r) := by
  by_cases hz : (horner cs c).numerator=(0,0)
  · simp [sourcePasses,hz]
  · simp [sourcePasses,hz,rootIntegerCoordinateBound]

/-- The estimate `passes_of_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem passes_of_bound (cs : List ℤ) (c : ℚ×ℚ) (r : ℚ)
    (hb : rootIntegerCoordinateBound (cs.length-1) (horner cs c) (horner (derivative cs) c) r)
    (hl : 0 < max |(horner (derivative cs) c).numerator.1| |(horner (derivative cs) c).numerator.2|) :
    sourcePasses cs c r=true := (passes_exact cs c r).mpr (Or.inr ⟨hl,hb⟩)

/-- The estimate `passes_of_ofFn_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem passes_of_ofFn_bound (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0)
    (c : ℚ×ℚ) (r : ℚ)
    (hb : rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))) r)
    (hl : 0 < max
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.1|
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.2|) :
    sourcePasses (List.ofFn a) c r=true := by
  apply passes_of_bound
  · simpa only [horner,derivative_ofFn n a ha,List.length_ofFn,
      show n+2-1=n+1 by omega] using hb
  · simpa only [horner,derivative_ofFn n a ha] using hl



end ActualProjectionSourcePasses


namespace ActualProjectionCapRetention
open ActualProjectionSourcePasses ActualProjectionSturmAxes ActualProjectionCartesian
open ActualProjectionBinomialEval ActualSturmComputedIsolation
open ActualRootProjectionCap ActualRootAnalyticSupply
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for retained in the bounds model. -/
def retained (cs : List ℤ) (r : ℚ) (ix iy : List (ℚ×ℚ)) : List (ℚ×ℚ) :=
  (centers ix iy).filter (fun c => sourcePasses cs c r)

/-- The finite construction in `Bounds` satisfies `retained_mem` under the displayed hypotheses. -/
theorem retained_mem (cs : List ℤ) (r : ℚ) (ix iy : List (ℚ×ℚ)) (c : ℚ×ℚ) :
    c∈retained cs r ix iy ↔ c∈centers ix iy ∧ sourcePasses cs c r=true :=
  List.mem_filter

/-- The finite construction in `Bounds` satisfies `actual_cap_retention` under the displayed hypotheses. -/
theorem actual_cap_retention (contexts : List Context) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) (ctx : Context) (hctx : ctx∈contexts)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0)
    (hfactor : ctx.factor=List.ofFn a) (hsep : (rootIntegerPolynomial a).Separable) :
    ∃ fuelX fuelY ix iy,isolateAxes (List.ofFn a) (cap contexts bits gap) fuelX fuelY=some (ix,iy) ∧
      ∀ z : ℂ,(rootIntegerPolynomial a).eval z=0 →
        ∃ c∈retained (List.ofFn a) (radius contexts bits gap) ix iy,
          ‖rootRationalCoordinate c-z‖ ≤ (midpointError contexts bits gap : ℝ) := by
  have htop : (List.ofFn a).getD (n+1) 0≠0 := by
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,
      dite_eq_left (by omega : n+1 < n+2),Option.getD_some,Fin.last] using ha
  obtain ⟨fx,fy,ix,iy,hr,hcover⟩ := computed_cartesian (List.ofFn a) (n+1) (cap contexts bits gap)
    (by simp only [List.length_ofFn]) (by omega) htop
  refine ⟨fx,fy,ix,iy,hr,?_⟩
  intro z hz
  have hz' : (inputPoly (List.ofFn a)).eval z=0 := by
    change (rootIntegerListPolynomial (List.ofFn a)).eval z=0
    rw [rootIntegerListPolynomial_ofFn]
    exact hz
  obtain ⟨c,hc,hnear⟩ := (hcover z hz').2
  have hnear' : ‖rootRationalCoordinate c-z‖ ≤ (midpointError contexts bits gap : ℝ) := hnear
  obtain ⟨hb,hl⟩ := cap_horner_without_analytic_answers contexts bits gap hg ctx hctx n a ha hfactor hsep z hz c hnear'
  exact ⟨c,(retained_mem _ _ _ _ _).mpr ⟨hc,passes_of_ofFn_bound n a ha c _ hb hl⟩,hnear'⟩

end ActualProjectionCapRetention


namespace ActualProjectionContexts
open ActualProjectionProducedArrays ActualProjectionGeneratedAxes ActualProjectionEntryDegrees
open ActualYunArrayStep ActualRootProjectionCap

/-- Construction for build in the bounds model. -/
def build : List (List ℤ×ℕ) → Option (List Context)
  | [] => some []
  | (f,e)::fs => match projections f with
    | (some rx,some ry) => (build fs).map (fun tail => ⟨f,e,rx,ry⟩::tail)
    | _ => none

/-- Construction for Context Good in the bounds model. -/
def ContextGood (ctx : Context) : Prop :=
  FactorGood (ctx.factor,ctx.exponent) ∧
    projections ctx.factor=(some ctx.xProjection,some ctx.yProjection) ∧
    OutputProperties ctx.factor Axis.real ctx.xProjection ∧
    OutputProperties ctx.factor Axis.imag ctx.yProjection

/-- The finite construction in `Bounds` satisfies `factor_projections` under the displayed hypotheses. -/
theorem factor_projections (f : List ℤ×ℕ) (hf : FactorGood f) :
    ∃ rx ry,projections f.1=(some rx,some ry) ∧
      OutputProperties f.1 Axis.real rx ∧ OutputProperties f.1 Axis.imag ry := by
  obtain ⟨_,hd,hlen,htop,_⟩ := hf
  let D := (Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.rootIntegerListPolynomial f.1).natDegree
  exact actual_projection_pair f.1 D hlen hd (by simpa only [hlen,Nat.add_sub_cancel] using htop)

/-- The finite construction in `Bounds` satisfies `build_success` under the displayed hypotheses. -/
theorem build_success (fs : List (List ℤ×ℕ)) (hgood : ∀ f∈fs,FactorGood f) :
    ∃ contexts,build fs=some contexts ∧ contexts.map (fun ctx => (ctx.factor,ctx.exponent))=fs ∧
      ∀ ctx∈contexts,ContextGood ctx := by
  induction fs with
  | nil => exact ⟨[],rfl,rfl,by intro ctx h; cases h⟩
  | cons f fs ih =>
    have hf : FactorGood f := hgood f (by simp)
    obtain ⟨rx,ry,hpr,hx,hy⟩ := factor_projections f hf
    obtain ⟨tail,ht,hmap,hg⟩ := ih (fun g hgf => hgood g (by simp only [List.mem_cons]; exact Or.inr hgf))
    let ctx : Context := ⟨f.1,f.2,rx,ry⟩
    refine ⟨ctx::tail,?_,?_,?_⟩
    · simp only [build,hpr,ht,Option.map_some,ctx]
    · change (f.1,f.2)::tail.map (fun c => (c.factor,c.exponent))=f::fs
      rw [hmap,Prod.eta]
    · intro c hc
      rcases List.mem_cons.mp hc with he|he
      · subst c
        exact ⟨hf,hpr,hx,hy⟩
      · exact hg c he

end ActualProjectionContexts


namespace ActualProjectionAcceptedDisks
open ActualProjectionSourceDerivative ActualProjectionSourcePasses ActualProjectionCapRetention
open ActualRootProjectionCap ActualProjectionSturmAxes
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- The finite construction in `Bounds` satisfies `source_passes_disk` under the displayed hypotheses. -/
theorem source_passes_disk (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0)
    (c : ℚ×ℚ) (r : ℚ) (hr : 0 < r) (hp : sourcePasses (List.ofFn a) c r=true) :
    ∃ z : ℂ,(rootIntegerPolynomial a).eval z=0 ∧ ‖z-rootRationalCoordinate c‖ ≤ (r : ℝ) := by
  rcases (passes_exact _ _ _).mp hp with hz|⟨_,hb⟩
  · exact rootIntegerArray_zero_disk a c r hr.le hz
  · apply rootIntegerArray_disk n a ha c r hr
    simpa only [horner,derivative_ofFn n a ha,List.length_ofFn,
      show n+2-1=n+1 by omega] using hb

/-- The finite construction in `Bounds` satisfies `retained_disks_sound` under the displayed hypotheses. -/
theorem retained_disks_sound (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0)
    (r : ℚ) (hr : 0 < r) (ix iy : List (ℚ×ℚ)) :
    ∀ c∈retained (List.ofFn a) r ix iy,
      ∃ z : ℂ,(rootIntegerPolynomial a).eval z=0 ∧ ‖z-rootRationalCoordinate c‖ ≤ (r : ℝ) := by
  intro c hc
  exact source_passes_disk n a ha c r hr ((retained_mem _ _ _ _ _).mp hc).2

/-- The finite construction in `Bounds` satisfies `cap_midpoint_le_radius` under the displayed hypotheses. -/
theorem cap_midpoint_le_radius (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0 < gap) :
    midpointError contexts bits gap ≤ radius contexts bits gap := by
  have hr := cap_radius_budgets contexts bits gap hg
  rw [midpoint_square]
  nlinarith [hr.1,hr.2.1]

/-- The finite construction in `Bounds` satisfies `actual_cap_disks` under the displayed hypotheses. -/
theorem actual_cap_disks (contexts : List Context) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) (ctx : Context) (hctx : ctx∈contexts)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1))≠0)
    (hfactor : ctx.factor=List.ofFn a) (hsep : (rootIntegerPolynomial a).Separable) :
    ∃ fuelX fuelY ix iy,isolateAxes (List.ofFn a) (cap contexts bits gap) fuelX fuelY=some (ix,iy) ∧
      (∀ z : ℂ,(rootIntegerPolynomial a).eval z=0 →
        ∃ c∈retained (List.ofFn a) (radius contexts bits gap) ix iy,
          ‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ)) ∧
      (∀ c∈retained (List.ofFn a) (radius contexts bits gap) ix iy,
        ∃ z : ℂ,(rootIntegerPolynomial a).eval z=0 ∧
          ‖z-rootRationalCoordinate c‖ ≤ (radius contexts bits gap : ℝ)) := by
  obtain ⟨fx,fy,ix,iy,hr,hcover⟩ := actual_cap_retention contexts bits gap hg ctx hctx n a ha hfactor hsep
  refine ⟨fx,fy,ix,iy,hr,?_,retained_disks_sound n a ha _ (cap_radius_budgets contexts bits gap hg).1 ix iy⟩
  intro z hz
  obtain ⟨c,hc,hnear⟩ := hcover z hz
  refine ⟨c,hc,?_⟩
  rw [norm_sub_rev]
  have he : (midpointError contexts bits gap : ℝ) ≤ (radius contexts bits gap : ℝ) := by
    exact_mod_cast cap_midpoint_le_radius contexts bits gap hg
  exact hnear.trans he

end ActualProjectionAcceptedDisks


namespace ActualProjectionDivisorHeight
open Polynomial
open scoped BigOperators

/-- Construction for complex Poly in the bounds model. -/
def complexPoly (p : ℤ[X]) : ℂ[X] := p.map (Int.castRingHom ℂ)

/-- The finite construction in `Bounds` satisfies `integer_mahler_one` under the displayed hypotheses. -/
theorem integer_mahler_one (p : ℤ[X]) (hp : p≠0) : 1 ≤ (complexPoly p).mahlerMeasure := by
  apply Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  rw [complexPoly,Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
  change (1 : ℝ) ≤ ‖(p.leadingCoeff : ℂ)‖
  have hh : (1 : ℝ) ≤ |(p.leadingCoeff : ℝ)| := by
    exact_mod_cast Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hp)
  simpa only [Complex.norm_intCast,Int.norm_eq_abs,Int.cast_abs] using hh

/-- The estimate `degree_card_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem degree_card_bound (D : ℕ) : D+1 ≤ 2^D := by
  induction D with
  | zero => norm_num
  | succ D ih =>
    calc
      D+1+1 ≤ 2*(D+1) := by omega
      _ ≤ 2*2^D := Nat.mul_le_mul_left 2 ih
      _ = 2^(D+1) := by rw [pow_succ]; omega

/-- The estimate `mahler_coefficient_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem mahler_coefficient_bound (p : ℂ[X]) (D H : ℕ)
    (hd : p.natDegree ≤ D) (hc : ∀ k,‖p.coeff k‖ ≤ (2 : ℝ)^H) :
    p.mahlerMeasure ≤ ((D+1 : ℕ) : ℝ)*(2 : ℝ)^H := by
  apply p.mahlerMeasure_le_sum_norm_coeff.trans
  rw [Polynomial.sum_over_range' p (fun _ => norm_zero) (D+1) (by omega)]
  calc
    _ ≤ ∑ _k∈Finset.range (D+1),(2 : ℝ)^H := Finset.sum_le_sum (fun k _ => hc k)
    _ = _ := by simp

/-- The finite construction in `Bounds` satisfies `divisor_coefficients` under the displayed hypotheses. -/
theorem divisor_coefficients (p g h : ℤ[X]) (hp : p≠0) (hprod : p=g*h)
    (D H : ℕ) (hd : p.natDegree ≤ D)
    (hc : ∀ k,‖(complexPoly p).coeff k‖ ≤ (2 : ℝ)^H) (k : ℕ) :
    ‖(complexPoly g).coeff k‖ ≤ (2 : ℝ)^(H+D*(H+2)) := by
  have hh : h≠0 := by intro hz; rw [hz,mul_zero] at hprod; exact hp hprod
  have hgd : (complexPoly g).natDegree ≤ D := by
    have hg : g∣p := ⟨h,hprod⟩
    exact Polynomial.natDegree_map_le.trans ((Polynomial.natDegree_le_of_dvd hg hp).trans hd)
  have hpd : (complexPoly p).natDegree ≤ D := Polynomial.natDegree_map_le.trans hd
  have hchoose : (((complexPoly g).natDegree.choose k : ℕ) : ℝ) ≤ (2 : ℝ)^D := by
    have hnat := (Nat.choose_le_two_pow (complexPoly g).natDegree k).trans
      (Nat.pow_le_pow_right (by decide) hgd)
    exact_mod_cast hnat
  have hm : (complexPoly p).mahlerMeasure ≤ ((D+1 : ℕ) : ℝ)*(2 : ℝ)^H :=
    mahler_coefficient_bound _ D H hpd hc
  have hfactor : complexPoly g*complexPoly h=complexPoly p := by simp only [complexPoly,hprod,Polynomial.map_mul]
  have hmg := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure k
    (complexPoly g) (complexPoly h) (integer_mahler_one h hh)
  rw [hfactor] at hmg
  have hcard : ((D+1 : ℕ) : ℝ) ≤ (2 : ℝ)^D := by exact_mod_cast degree_card_bound D
  calc
    _ ≤ (((complexPoly g).natDegree.choose k : ℕ) : ℝ)*(complexPoly p).mahlerMeasure := hmg
    _ ≤ (2 : ℝ)^D*(((D+1 : ℕ) : ℝ)*(2 : ℝ)^H) :=
      mul_le_mul hchoose hm (Polynomial.mahlerMeasure_nonneg _) (by positivity)
    _ ≤ (2 : ℝ)^D*((2 : ℝ)^D*(2 : ℝ)^H) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (by positivity)) (by positivity)
    _ = (2 : ℝ)^(H+2*D) := by rw [← pow_add,← pow_add]; congr 1; omega
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (D*H)])

end ActualProjectionDivisorHeight


namespace ActualProjectionPrimitiveDivisor
open Polynomial ActualYunRationalArray ActualYunRationalCanonical
open ActualYunGcd ActualYunArrayInitialization ActualYunPrimitive ActualYunPrimitiveContent
open ActualSturmArrayTools ActualSturmInitialization

/-- The finite construction in `Bounds` satisfies `primitive_dvd_integral` under the displayed hypotheses. -/
theorem primitive_dvd_integral (p q : ℤ[X]) (hp : p.IsPrimitive) (hq : q≠0)
    (hdvd : p.map (Int.castRingHom ℚ)∣q.map (Int.castRingHom ℚ)) : p∣q := by
  have hc : q.content≠0 := fun hz => hq (Polynomial.content_eq_zero_iff.mp hz)
  have hcq : (q.content : ℚ)≠0 := by exact_mod_cast hc
  have hqm : q.map (Int.castRingHom ℚ)=C (q.content : ℚ)*q.primPart.map (Int.castRingHom ℚ) := by
    conv_lhs => rw [q.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul,Polynomial.map_C]
    rfl
  have he : q.primPart.map (Int.castRingHom ℚ)=C (q.content : ℚ)⁻¹*q.map (Int.castRingHom ℚ) := by
    rw [hqm,← mul_assoc,← Polynomial.C_mul,inv_mul_cancel₀ hcq,Polynomial.C_1,one_mul]
  have hprim : p.map (Int.castRingHom ℚ)∣q.primPart.map (Int.castRingHom ℚ) := by
    obtain ⟨a,ha⟩ := hdvd
    refine ⟨a*C (q.content : ℚ)⁻¹,?_⟩
    rw [he,ha]
    ring
  exact ((Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast p q.primPart hp).mpr hprim).trans q.primPart_dvd

/-- The finite construction in `Bounds` satisfies `initialized_rational_divisor` under the displayed hypotheses. -/
theorem initialized_rational_divisor (a : List ℚ) (hcan : Canonical a) (ha : poly a≠0)
    (f g : List ℤ) (hinit : initialChain a=some [f,g]) :
    (integerPoly f).IsPrimitive ∧ integerPolyQ f∣poly a := by
  obtain ⟨c,hc,hC,hCpoly⟩ := polyGcd_success a (derivative a) hcan (trim_canonical _)
  rw [derivative_poly] at hCpoly
  have hcn : poly c≠0 := by rw [hCpoly,ActualYunStep.gcdQ_eq_gcd]; exact gcd_ne_zero_of_left ha
  have hcd : poly c∣poly a := by rw [hCpoly,ActualYunStep.gcdQ_eq_gcd]; exact gcd_dvd_left _ _
  obtain ⟨q,hq,_,hQpoly⟩ := exactDiv_success a c hcn hcd
  have hprod : poly c*poly q=poly a := by rw [hQpoly]; exact EuclideanDomain.mul_div_cancel' hcn hcd
  have hqn : poly q≠0 := by intro hz; rw [hz,mul_zero] at hprod; exact ha hprod.symm
  simp only [initialChain,hc,hq] at hinit
  split_ifs at hinit
  · have hh := Option.some.inj hinit
    cases hh
  · have hhead := congrArg (fun l : List (List ℤ) => l.head?) (Option.some.inj hinit)
    simp only [List.head?_cons,Option.some.injEq] at hhead
    rw [← hhead]
    refine ⟨primitive_isPrimitive q hqn,?_⟩
    rw [primitive_polynomialQ q hqn]
    have hs : primitiveScale q≠0 := (primitiveScale_pos q hqn).ne'
    refine ⟨C (primitiveScale q)⁻¹*poly c,?_⟩
    calc
      poly a=(C (primitiveScale q)*C (primitiveScale q)⁻¹)*(poly c*poly q) := by
        rw [← Polynomial.C_mul,mul_inv_cancel₀ hs,Polynomial.C_1,one_mul,hprod]
      _=(C (primitiveScale q)*poly q)*(C (primitiveScale q)⁻¹*poly c) := by ring

/-- The finite construction in `Bounds` satisfies `initialized_integer_divisor` under the displayed hypotheses. -/
theorem initialized_integer_divisor (a : List ℤ) (hcan : Canonical (lift a)) (ha : integerPoly a≠0)
    (f g : List ℤ) (hinit : initialChain (lift a)=some [f,g]) :
    (integerPoly f).IsPrimitive ∧ integerPoly f∣integerPoly a := by
  have haq : poly (lift a)≠0 := by
    rw [lift_poly]
    intro hz
    apply ha
    apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    simpa only [integerPolyQ,integerPoly,Polynomial.map_zero] using hz
  obtain ⟨hprim,hdiv⟩ := initialized_rational_divisor (lift a) hcan haq f g hinit
  rw [lift_poly] at hdiv
  exact ⟨hprim,primitive_dvd_integral (integerPoly f) (integerPoly a) hprim ha hdiv⟩

end ActualProjectionPrimitiveDivisor


namespace ActualProjectionPairProduct
open Polynomial

/-- The estimate `product_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem product_bound (s : Multiset ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ x∈s,‖x‖ ≤ M) : ‖s.prod‖ ≤ M^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x xs ih =>
    rw [Multiset.prod_cons,Multiset.card_cons,norm_mul,pow_succ]
    have hx := hs x (Multiset.mem_cons_self x xs)
    have hr := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    nlinarith [mul_le_mul hx hr (norm_nonneg xs.prod) hM]

/-- The finite construction in `Bounds` satisfies `derivative_root_product` under the displayed hypotheses. -/
theorem derivative_root_product (f : ℂ[X]) (z : ℂ) (hz : z∈f.roots) :
    f.derivative.eval z=f.leadingCoeff*((f.roots.erase z).map (fun w => z-w)).prod := by
  have hsplit := IsAlgClosed.splits f
  conv_lhs => rw [hsplit.eq_prod_roots]
  rw [Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,zero_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_multiset_prod_X_sub_C_derivative hz]

/-- The estimate `pair_derivative_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem pair_derivative_bound (f : ℂ[X]) (hf : f≠0) (z w : ℂ)
    (hz : f.eval z=0) (hw : f.eval w=0) (hne : z≠w)
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hroots : ∀ t∈f.roots,‖t‖ ≤ R) (hlead : ‖f.leadingCoeff‖ ≤ B) :
    ‖f.derivative.eval z‖ ≤ B*‖z-w‖*(2*R)^(f.natDegree-2) := by
  classical
  have hzm : z∈f.roots := (Polynomial.mem_roots hf).mpr hz
  have hwm : w∈f.roots := (Polynomial.mem_roots hf).mpr hw
  have hwe : w∈f.roots.erase z := (Multiset.mem_erase_of_ne (Ne.symm hne)).mpr hwm
  let rest := (f.roots.erase z).erase w
  have hcard : rest.card=f.natDegree-2 := by
    dsimp only [rest]
    rw [Multiset.card_erase_of_mem hwe,Multiset.card_erase_of_mem hzm,
      ← (IsAlgClosed.splits f).natDegree_eq_card_roots]
    simp only [Nat.pred_eq_sub_one]
    omega
  have htail : ‖(rest.map (fun t => z-t)).prod‖ ≤ (2*R)^(f.natDegree-2) := by
    have hh := product_bound (rest.map (fun t => z-t)) (2*R) (by positivity) ?_
    · simpa only [Multiset.card_map,hcard] using hh
    · intro u hu
      obtain ⟨t,ht,rfl⟩ := Multiset.mem_map.mp hu
      have htm : t∈f.roots := Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ht)
      have hn := norm_sub_le z t
      linarith [hroots z hzm,hroots t htm]
  have he : ‖f.derivative.eval z‖=‖f.leadingCoeff‖*‖z-w‖*‖(rest.map (fun t => z-t)).prod‖ := by
    rw [derivative_root_product f z hzm,← Multiset.cons_erase hwe,Multiset.map_cons,Multiset.prod_cons,
      norm_mul,norm_mul]
    ring
  rw [he]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hlead (norm_nonneg _)) htail
    (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))

end ActualProjectionPairProduct


namespace ActualProjectionSquarefreeHeight
open Polynomial ActualProjectionPrimitiveDivisor ActualProjectionDivisorHeight
open ActualRootProjectionCap ActualRootHeightEnvelope
open ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive ActualYunPrimitiveContent
open ActualSturmArrayTools ActualSturmInitialization
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- The finite construction in `Bounds` satisfies `integer_leading_one` under the displayed hypotheses. -/
theorem integer_leading_one (p : ℤ[X]) (hp : p≠0) : 1 ≤ ‖(complexPoly p).leadingCoeff‖ := by
  rw [complexPoly,Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
  change (1 : ℝ) ≤ ‖(p.leadingCoeff : ℂ)‖
  have hh : (1 : ℝ) ≤ |(p.leadingCoeff : ℝ)| := by exact_mod_cast Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hp)
  simpa only [Complex.norm_intCast,Int.norm_eq_abs,Int.cast_abs] using hh

/-- The finite construction in `Bounds` satisfies `cauchy_radius` under the displayed hypotheses. -/
theorem cauchy_radius (p : ℂ[X]) (hp : p≠0) (B : ℝ) (hB : 1 ≤ B)
    (hc : ∀ k,‖p.coeff k‖ ≤ B) (hl : 1 ≤ ‖p.leadingCoeff‖) (z : ℂ) (hz : p.eval z=0) : ‖z‖ ≤ 2*B := by
  let b : NNReal := ⟨B,by linarith⟩
  have hs : (Finset.range p.natDegree).sup (fun k => ‖p.coeff k‖₊) ≤ b := by
    apply Finset.sup_le
    intro k _
    exact_mod_cast hc k
  have hl' : (1 : NNReal) ≤ ‖p.leadingCoeff‖₊ := by exact_mod_cast hl
  have hlp : (0 : NNReal) < ‖p.leadingCoeff‖₊ := lt_of_lt_of_le zero_lt_one hl'
  have hq : (Finset.range p.natDegree).sup (fun k => ‖p.coeff k‖₊)/‖p.leadingCoeff‖₊ ≤ b := by
    apply (div_le_iff₀ hlp).mpr
    exact hs.trans (by simpa using mul_le_mul_of_nonneg_left hl' (zero_le : (0 : NNReal) ≤ b))
  have hcb : p.cauchyBound ≤ b+1 := by
    dsimp only [Polynomial.cauchyBound]
    exact add_le_add hq (le_refl 1)
  have hr := (Polynomial.IsRoot.norm_lt_cauchyBound hp hz).trans_le hcb
  have hrR : ‖z‖ < B+1 := by exact_mod_cast hr
  linarith

/-- The finite construction in `Bounds` satisfies `integer_root_radius` under the displayed hypotheses. -/
theorem integer_root_radius (p : ℤ[X]) (hp : p≠0) (H : ℕ)
    (hc : ∀ k,‖(complexPoly p).coeff k‖ ≤ (2 : ℝ)^H) (z : ℂ) (hz : (complexPoly p).eval z=0) :
    ‖z‖ ≤ (2 : ℝ)^(H+1) := by
  have hpc : complexPoly p≠0 := by
    intro hzero
    apply hp
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa only [complexPoly,Polynomial.map_zero] using hzero
  have hh := cauchy_radius (complexPoly p) hpc (2^H) (one_le_pow₀ (by norm_num)) hc (integer_leading_one p hp) z hz
  simpa only [pow_succ,mul_comm] using hh

/-- The estimate `initialized_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem initialized_bounds (a : List ℤ) (hcan : Canonical (lift a)) (ha : integerPoly a≠0)
    (hd : 0 < (integerPoly a).natDegree) :
    ∃ f g,initialChain (lift a)=some [f,g] ∧
      (integerPoly f).IsPrimitive ∧ integerPoly f∣integerPoly a ∧
      (rootIntegerListPolynomial f).Separable ∧ 0 < (integerPoly f).natDegree ∧
      (integerPoly f).natDegree ≤ degree a ∧
      (∀ k,‖(rootIntegerListPolynomial f).coeff k‖ ≤ (2 : ℝ)^(height a+degree a*(height a+2))) ∧
      (∀ z : ℂ,(rootIntegerListPolynomial f).eval z=0 → ‖z‖ ≤ (2 : ℝ)^(height a+1)) := by
  have haq : poly (lift a)≠0 := by
    rw [lift_poly]
    intro hzero
    apply ha
    apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    simpa only [integerPolyQ,integerPoly,Polynomial.map_zero] using hzero
  have hqdeg : (poly (lift a)).natDegree=(integerPoly a).natDegree := by
    rw [lift_poly]
    exact Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective _
  have hlen := canonical_length (lift a) hcan ((canonical_nonzero _ hcan).mpr haq)
  have hD : degree a=(integerPoly a).natDegree := by
    rw [hqdeg] at hlen
    simp only [lift,List.length_map] at hlen
    dsimp only [ActualRootProjectionCap.degree]
    omega
  obtain ⟨f,g,hinit,_,_,hsep,hfd,hfdle,_,_,_⟩ := initialization_success (lift a) hcan haq (by rw [hqdeg]; exact hd)
  obtain ⟨hprim,hdiv⟩ := initialized_integer_divisor a hcan ha f g hinit
  obtain ⟨h,hprod⟩ := hdiv
  have hfdeg : (integerPolyQ f).natDegree=(integerPoly f).natDegree :=
    Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective _
  have hsc : (rootIntegerListPolynomial f).Separable := by
    rw [← integerPolyQ_map]
    exact (Polynomial.separable_map (Rat.castHom ℂ)).mpr hsep
  refine ⟨f,g,hinit,hprim,⟨h,hprod⟩,hsc,by omega,by omega,?_,?_⟩
  · intro k
    exact divisor_coefficients (integerPoly a) (integerPoly f) h ha hprod (degree a) (height a)
      (by omega) (coefficient_from_height a) k
  · intro z hz
    have hpz : (complexPoly (integerPoly a)).eval z=0 := by
      change ((integerPoly a).map (Int.castRingHom ℂ)).eval z=0
      rw [hprod,Polynomial.map_mul,Polynomial.eval_mul]
      change (rootIntegerListPolynomial f).eval z*_=0
      rw [hz,zero_mul]
    exact integer_root_radius (integerPoly a) ha (height a) (coefficient_from_height a) z hpz

end ActualProjectionSquarefreeHeight


namespace ActualProjectionSeparationBudget
open Polynomial ActualProjectionDivisorHeight ActualRootHeightEnvelope

/-- Construction for squarefree Height in the bounds model. -/
def squarefreeHeight (D H : ℕ) : ℕ := H+D*(H+2)
/-- Construction for derivative Exponent in the bounds model. -/
def derivativeExponent (D H : ℕ) : ℕ := squarefreeHeight D H+D*(H+4)
/-- Construction for pair Exponent in the bounds model. -/
def pairExponent (s D H : ℕ) : ℕ :=
  (s-1)*(squarefreeHeight D H+derivativeExponent D H)+squarefreeHeight D H+(s-2)*(H+2)
/-- Construction for source Exponent in the bounds model. -/
def sourceExponent (D H : ℕ) : ℕ := D*D*(squarefreeHeight D H+2)

/-- The estimate `derivative_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem derivative_bound (f : ℂ[X]) (s D H : ℕ) (hs : 0 < s) (hdeg : f.natDegree=s) (hD : s ≤ D)
    (hc : ∀ k,‖f.coeff k‖ ≤ (2 : ℝ)^squarefreeHeight D H) (w : ℂ)
    (hw : ‖w‖ ≤ (2 : ℝ)^(H+1)) : ‖f.derivative.eval w‖ ≤ (2 : ℝ)^derivativeExponent D H := by
  have hb := (derivatives_from_coefficients f s hs hdeg (2^squarefreeHeight D H) (2^(H+1))
    (by positivity) (one_le_pow₀ (by norm_num)) hc w hw).1
  have hsR : (s : ℝ) ≤ (2 : ℝ)^D := by
    exact_mod_cast hD.trans ((Nat.le_succ D).trans (degree_card_bound D))
  have hcub : (s : ℝ)^3 ≤ ((2 : ℝ)^D)^3 := pow_le_pow_left₀ (by positivity) hsR 3
  have hpower : ((2 : ℝ)^(H+1))^s ≤ ((2 : ℝ)^(H+1))^D :=
    pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hD
  calc
    _ ≤ (s : ℝ)^3*(2 : ℝ)^squarefreeHeight D H*((2 : ℝ)^(H+1))^s := hb
    _ ≤ ((2 : ℝ)^D)^3*(2 : ℝ)^squarefreeHeight D H*((2 : ℝ)^(H+1))^D :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcub (by positivity)) hpower (by positivity) (by positivity)
    _ = _ := by
      rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
      congr 1
      unfold derivativeExponent
      ring

/-- The estimate `exponent_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem exponent_bound (s D H : ℕ) (hs : 2 ≤ s) (hD : s ≤ D) : pairExponent s D H ≤ sourceExponent D H := by
  have h1 : (s-1)*(squarefreeHeight D H+derivativeExponent D H) ≤
      (D-1)*(squarefreeHeight D H+derivativeExponent D H) :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hD 1)
  have h2 : (s-2)*(H+2) ≤ (D-2)*(H+2) := Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hD 2)
  have hmid : pairExponent s D H ≤ pairExponent D D H := by unfold pairExponent; omega
  apply hmid.trans
  obtain ⟨k,hk⟩ : ∃ k,D=k+2 := ⟨D-2,by omega⟩
  subst D
  have he : sourceExponent (k+2) H=pairExponent (k+2) (k+2) H+
      ((k^3+4*k^2+3*k+1)*H+(2*k^3+6*k^2+4*k+4)) := by
    unfold sourceExponent pairExponent derivativeExponent squarefreeHeight
    rw [show k+2-1=k+1 by omega,show k+2-2=k by omega]
    ring
  omega

end ActualProjectionSeparationBudget


namespace ActualProjectionPairSeparation
open Polynomial ActualProjectionDivisorHeight ActualProjectionPairProduct ActualProjectionSeparationBudget
open ActualRootResultantDerivative

/-- The finite construction in `Bounds` satisfies `integer_derivative_resultant_nonzero` under the displayed hypotheses. -/
theorem integer_derivative_resultant_nonzero (p : ℤ[X]) (hd : 0 < p.natDegree)
    (hs : (complexPoly p).Separable) : p.resultant p.derivative p.natDegree (p.natDegree-1)≠0 := by
  let f := complexPoly p
  have hnd : f.natDegree=p.natDegree := Polynomial.natDegree_map_eq_of_injective Int.cast_injective p
  have hfd : 0 < f.natDegree := by rw [hnd]; exact hd
  have hder : f.derivative.natDegree=f.natDegree-1 :=
    Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_derivative hfd.ne')
  have hres : f.resultant f.derivative≠0 := Polynomial.resultant_ne_zero f f.derivative hs
  intro hz
  apply hres
  rw [hder,hnd]
  dsimp only [f,complexPoly]
  rw [Polynomial.derivative_map,Polynomial.resultant_map_map]
  change (p.resultant p.derivative p.natDegree (p.natDegree-1) : ℂ)=0
  rw [hz,Int.cast_zero]

/-- The finite construction in `Bounds` satisfies `separated` under the displayed hypotheses. -/
theorem separated (p : ℤ[X]) (hp : p≠0) (D H : ℕ) (hD : p.natDegree ≤ D)
    (hs : (complexPoly p).Separable)
    (hc : ∀ k,‖(complexPoly p).coeff k‖ ≤ (2 : ℝ)^squarefreeHeight D H)
    (hroots : ∀ z : ℂ,(complexPoly p).eval z=0 → ‖z‖ ≤ (2 : ℝ)^(H+1))
    (z w : ℂ) (hz : (complexPoly p).eval z=0) (hw : (complexPoly p).eval w=0) (hne : z≠w) :
    1/(2 : ℝ)^sourceExponent D H ≤ ‖z-w‖ := by
  classical
  let f := complexPoly p
  let s := p.natDegree
  have hfd : f.natDegree=s := Polynomial.natDegree_map_eq_of_injective Int.cast_injective p
  have hfn : f≠0 := by
    intro hf
    apply hp
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa only [f,complexPoly,Polynomial.map_zero] using hf
  have hzm : z∈f.roots := (Polynomial.mem_roots hfn).mpr hz
  have hwm : w∈f.roots := (Polynomial.mem_roots hfn).mpr hw
  have hwe : w∈f.roots.erase z := (Multiset.mem_erase_of_ne (Ne.symm hne)).mpr hwm
  have hpos : 0 < (f.roots.erase z).card := Multiset.card_pos_iff_exists_mem.mpr ⟨w,hwe⟩
  have hs2 : 2 ≤ s := by
    rw [Multiset.card_erase_of_mem hzm,← (IsAlgClosed.splits f).natDegree_eq_card_roots,hfd] at hpos
    simp only [Nat.pred_eq_sub_one] at hpos
    omega
  have hlead : ‖f.leadingCoeff‖ ≤ (2 : ℝ)^squarefreeHeight D H := by
    rw [← Polynomial.coeff_natDegree]
    exact hc _
  have hupper : ∀ v∈f.roots,‖f.derivative.eval v‖ ≤ (2 : ℝ)^derivativeExponent D H := by
    intro v hv
    exact derivative_bound f s D H (by omega) hfd hD hc v (hroots v ((Polynomial.mem_roots hfn).mp hv))
  have hlow := integer_resultant_derivative_lower p (by omega)
    (integer_derivative_resultant_nonzero p (by omega) hs)
    ((2 : ℝ)^squarefreeHeight D H) ((2 : ℝ)^derivativeExponent D H)
    (by positivity) (by positivity) hlead hupper z hz
  have hpair := pair_derivative_bound f hfn z w hz hw hne ((2 : ℝ)^(H+1))
    ((2 : ℝ)^squarefreeHeight D H) (by positivity) (by positivity)
    (fun v hv => hroots v ((Polynomial.mem_roots hfn).mp hv)) hlead
  have hR : 2*(2 : ℝ)^(H+1)=(2 : ℝ)^(H+2) := by
    rw [show H+2=(H+1)+1 by omega,pow_succ]
    ring
  rw [hR,hfd] at hpair
  have hmul := mul_le_mul_of_nonneg_left hpair
    (by positivity : (0 : ℝ) ≤ ((2 : ℝ)^squarefreeHeight D H)^(s-1)*((2 : ℝ)^derivativeExponent D H)^(s-1))
  have hvalue : 1 ≤ (2 : ℝ)^pairExponent s D H*‖z-w‖ := by
    calc
      1 ≤ ((2 : ℝ)^squarefreeHeight D H)^(s-1)*((2 : ℝ)^derivativeExponent D H)^(s-1)*
          (((2 : ℝ)^squarefreeHeight D H)*‖z-w‖*((2 : ℝ)^(H+2))^(s-2)) := hlow.trans hmul
      _ = ((((2 : ℝ)^squarefreeHeight D H)^(s-1)*((2 : ℝ)^derivativeExponent D H)^(s-1))*
          ((2 : ℝ)^squarefreeHeight D H)*((2 : ℝ)^(H+2))^(s-2))*‖z-w‖ := by ring
      _ = _ := by
        rw [← pow_mul,← pow_mul,← pow_mul,← pow_add,← pow_add,← pow_add]
        congr 2
        unfold pairExponent
        ring
  have hpowers : (2 : ℝ)^pairExponent s D H ≤ (2 : ℝ)^sourceExponent D H :=
    pow_le_pow_right₀ (by norm_num) (exponent_bound s D H hs2 hD)
  have hfinal : 1 ≤ (2 : ℝ)^sourceExponent D H*‖z-w‖ :=
    hvalue.trans (mul_le_mul_of_nonneg_right hpowers (norm_nonneg _))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^sourceExponent D H)).mpr
  simpa only [mul_comm] using hfinal

end ActualProjectionPairSeparation


namespace ActualProjectionRealSeparation
open Polynomial ActualProjectionPairSeparation ActualProjectionSquarefreeHeight
open ActualProjectionSeparationBudget ActualRootProjectionCap
open ActualYunRationalArray ActualYunRationalCanonical ActualYunPrimitive ActualYunPrimitiveContent
open ActualSturmArrayTools ActualSturmRootset ActualSturmSourceCount
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- The finite construction in `Bounds` satisfies `real_eval_zero` under the displayed hypotheses. -/
theorem real_eval_zero (a : List ℤ) (x : ℝ) :
    (rootIntegerListPolynomial a).eval (x : ℂ)=0 ↔ (integerPolyQ a).eval₂ (Rat.castHom ℝ) x=0 := by
  let P := (integerPolyQ a).map (Rat.castHom ℝ)
  have hhom : Complex.ofRealHom.comp (Rat.castHom ℝ)=Rat.castHom ℂ := Subsingleton.elim _ _
  have hm : P.map Complex.ofRealHom=rootIntegerListPolynomial a := by
    dsimp only [P]
    rw [Polynomial.map_map,hhom,integerPolyQ_map]
  have hh := Polynomial.eval_map_apply (f:=Complex.ofRealHom) (p:=P) x
  rw [hm] at hh
  change (rootIntegerListPolynomial a).eval (x : ℂ)=((P.eval x : ℝ) : ℂ) at hh
  rw [hh]
  simp only [P,Polynomial.eval_map]
  exact Complex.ofReal_eq_zero

/-- The finite construction in `Bounds` satisfies `member_zero_iff` under the displayed hypotheses. -/
theorem member_zero_iff (a : List ℤ) (hn : poly (lift a)≠0) (x : ℝ) :
    x∈inputRoots (lift a) ↔ (rootIntegerListPolynomial a).eval (x : ℂ)=0 := by
  rw [inputRoots,Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero hn)]
  change ((poly (lift a)).map (Rat.castHom ℝ)).eval x=0 ↔ (rootIntegerListPolynomial a).eval (x : ℂ)=0
  rw [Polynomial.eval_map,lift_poly]
  exact (real_eval_zero a x).symm

/-- The finite construction in `Bounds` satisfies `original_real_separated` under the displayed hypotheses. -/
theorem original_real_separated (a : List ℤ) (hcan : Canonical (lift a)) (ha : integerPoly a≠0)
    (hd : 0 < (integerPoly a).natDegree) (x y : ℝ)
    (hx : (rootIntegerListPolynomial a).eval (x : ℂ)=0)
    (hy : (rootIntegerListPolynomial a).eval (y : ℂ)=0) (hne : x≠y) :
    1/(2 : ℝ)^separationExponent a ≤ |x-y| := by
  obtain ⟨f,g,hinit,_,_,hs,hfd,hfD,hcoeff,hroots⟩ := initialized_bounds a hcan ha hd
  have haq : poly (lift a)≠0 := by
    rw [lift_poly]
    intro hzero
    apply ha
    apply Polynomial.map_injective (Int.castRingHom ℚ) Rat.intCast_injective
    simpa only [integerPolyQ,integerPoly,Polynomial.map_zero] using hzero
  have hqdeg : (poly (lift a)).natDegree=(integerPoly a).natDegree := by
    rw [lift_poly]
    exact Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective _
  have heq := initialized_real_roots (lift a) hcan haq (by rw [hqdeg]; exact hd) f g hinit
  simp only [lift_poly] at heq
  have hfx : (rootIntegerListPolynomial f).eval (x : ℂ)=0 :=
    (real_eval_zero f x).mpr ((heq x).mpr ((real_eval_zero a x).mp hx))
  have hfy : (rootIntegerListPolynomial f).eval (y : ℂ)=0 :=
    (real_eval_zero f y).mpr ((heq y).mpr ((real_eval_zero a y).mp hy))
  have hfn : integerPoly f≠0 := by intro hf; rw [hf,Polynomial.natDegree_zero] at hfd; omega
  have hxy : (x : ℂ)≠(y : ℂ) := fun h => hne (Complex.ofReal_inj.mp h)
  have hh := separated (integerPoly f) hfn (degree a) (height a) hfD hs hcoeff hroots
    (x : ℂ) (y : ℂ) hfx hfy hxy
  simpa only [sourceExponent,squarefreeHeight,separationExponent,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hh

/-- The finite construction in `Bounds` satisfies `lifted_real_separated` under the displayed hypotheses. -/
theorem lifted_real_separated (a : List ℤ) (hcan : Canonical (lift a)) (hn : poly (lift a)≠0)
    (hd : 0 < (poly (lift a)).natDegree) (x y : ℝ)
    (hx : (rootIntegerListPolynomial a).eval (x : ℂ)=0)
    (hy : (rootIntegerListPolynomial a).eval (y : ℂ)=0) (hne : x≠y) :
    1/(2 : ℝ)^separationExponent a ≤ |x-y| := by
  have ha : integerPoly a≠0 := by
    intro hz
    apply hn
    rw [lift_poly]
    change (integerPoly a).map (Int.castRingHom ℚ)=0
    rw [hz,Polynomial.map_zero]
  have hdeg : (poly (lift a)).natDegree=(integerPoly a).natDegree := by
    rw [lift_poly]
    exact Polynomial.natDegree_map_eq_of_injective Rat.intCast_injective _
  exact original_real_separated a hcan ha (by rw [← hdeg]; exact hd) x y hx hy hne

end ActualProjectionRealSeparation


namespace ActualProjectionCapSeparationScale
open ActualRootProjectionCap ActualProjectionAcceptedDisks

/-- The finite construction in `Bounds` satisfies `radius_projection_small` under the displayed hypotheses. -/
theorem radius_projection_small (contexts : List Context) (bits : ℕ) (gap : ℚ)
    (ctx : Context) (hctx : ctx∈contexts) (projection : List ℤ)
    (hp : projection=ctx.xProjection ∨ projection=ctx.yProjection) :
    radius contexts bits gap ≤ (1/(2 : ℚ)^separationExponent projection)/128 := by
  have ht : separationExponent projection+5∈terms contexts bits gap := by
    unfold terms
    apply List.mem_append.mpr
    right
    apply List.mem_flatMap.mpr
    refine ⟨ctx,hctx,?_⟩
    rcases hp with rfl|rfl <;> simp [contextTerms]
  have hhalf := half_ge_term contexts bits (separationExponent projection+5) gap ht
  have hP : (2 : ℚ)^(separationExponent projection+7) ≤ 2^half contexts bits gap :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow : (2 : ℚ)^separationExponent projection*128 ≤ 2^half contexts bits gap := by
    simpa only [pow_add,show (2 : ℚ)^7=128 by norm_num] using hP
  rw [ActualRootProjectionCap.radius,div_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

/-- The estimate `radius_error_small` retains the actual parameter, input-error and normalization budgets. -/
theorem radius_error_small (contexts : List Context) (bits : ℕ) (gap : ℚ) (hg : 0 < gap)
    (ctx : Context) (hctx : ctx∈contexts) (projection : List ℤ)
    (hp : projection=ctx.xProjection ∨ projection=ctx.yProjection) :
    (radius contexts bits gap : ℝ)+(midpointError contexts bits gap : ℝ) <
      1/(2 : ℝ)^separationExponent projection := by
  have hs := radius_projection_small contexts bits gap ctx hctx projection hp
  have he := cap_midpoint_le_radius contexts bits gap hg
  have hpos : (0 : ℚ) < 1/(2 : ℚ)^separationExponent projection := by positivity
  have hQ : radius contexts bits gap+midpointError contexts bits gap <
      1/(2 : ℚ)^separationExponent projection := by nlinarith
  have hR : ((radius contexts bits gap+midpointError contexts bits gap : ℚ) : ℝ) <
      ((1/(2 : ℚ)^separationExponent projection : ℚ) : ℝ) := (Rat.cast_lt (K:=ℝ)).mpr hQ
  simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using hR

end ActualProjectionCapSeparationScale


end RootYunInternal
end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
