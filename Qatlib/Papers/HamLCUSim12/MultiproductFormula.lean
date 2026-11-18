/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder
public import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiConsumers
public import Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal
public import Qatlib.Papers.HamLCUSim12.Multiproduct.Definition1Formula.Definition1
public import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma12IntegerNodesAuxiliary
public import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma12IntegerNodesCorrectedHami
public import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma5CoeffBound.Lemma5

@[expose] public section

/-!
# Definition 1 — the actual Suzuki multi-product operator and its composite identity

Fixed source: Childs and Wiebe, arXiv:1202.5822v1, Definition 1, Eqs. (15)-(17), with the
Suzuki recursion of Section III: the multi-product
`M_{k,chi}(lam) = sum_{q=1}^{k+1} C_q S(lam / ell_q)^{ell_q}` combines node words — powers
of a symmetric Suzuki product operator at step counts `ell_q` — into one linear combination.

This module is the first executable slice of the Lemma 8 and Lemma 10 approximation chain:
the multi-product is defined at the operator level from the actual Suzuki composition, and
the composite identity is proved — the defined multi-product equals the stated nested
product (the public `recursiveSuzukiWord` flattened exponential word, the explicit Strang
expansion at level zero, and the public Definition-1 linear-combination shape with the
actual Suzuki node words as terms). The coefficients and the alternating schedule are the
public recursive Suzuki ones: the five-block split `u, u, 1 - 4u, u, u` with the concrete
scale `u = (4 - 4^(1/(2k+3)))^{-1}`. The symmetry of the schedule gives the negative-time
inverse identities, the operator-side prerequisite of the `E_k(-lam) E_k(lam)` analysis.

The Taylor-remainder defect analysis is reused, not re-proved: the final theorem forwards
`Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder.multiproduct_order_at` to the concrete Suzuki node words. The
derived-defect section below derives the defect expansion from the actual generator structure:
the node word is a single exponential word over the scaled concatenated generator list,
its series coefficients match the exponential through the Suzuki order (the public
`recursive_suzuki_all_even_order_coefficients`), its first defect coefficient is the
single-step defect scaled by `n ^ (-2 chi)`, and the product-exponential tail control
(the Lemma-9 estimate, in the `suzukiSeries` form) bounds the remainder. The resulting
multiproduct boost is proved with the explicit tail constant. The full defect family then reuses the public
`BCHFormal` odd-logarithm layer to derive the complete defect family and its full multiproduct
order boost, and proves the Lemma-12 `integerNode` rounding bridge. The corrected-exponent analysis derives the
remaining numerical conditions of the printed Lemma-8 chain — the `hγ`/`hcond`/`hlarge`
hypotheses at `correctedGamma` — from the public Lemma-12 bundle over the η window and a
concrete size threshold `k ≤ 91`, and assembles the conditional final multiproduct bound with
every hypothesis side derived. The Lemma 10 normalization
composite transform remains outside the scope of this module.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal
open Qatlib.Papers.CommutLCHS26.MainResults.FormalPowers
open Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
open Qatlib.Papers.HamLCUSim12.Multiproduct
open Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.HamLCUSim12.MultiproductFormula

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable section

local instance : NormedAlgebra ℝ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _

local instance : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _

local instance : IsScalarTower ℝ ℂ (Matrix I I ℂ) :=
  IsScalarTower.restrictScalars ℝ ℂ _

/-! ## The actual Suzuki multi-product operator -/

/-- The single-step Suzuki product operator at recursion level `s` (the paper's `S_{2s+2}`):
the ordered exponential word of the public recursive Suzuki generator list, i.e. the finite
alternating product with the concrete split coefficients `u, u, 1-4u, u, u` of
`recursiveSuzukiScale` applied to the Hamiltonian factors `hs`. -/
def suzukiStep (hs : List (Matrix I I ℂ)) (s : ℕ) (t : ℝ) : Matrix I I ℂ :=
  suzukiExponentialWord (recursiveSuzukiGenerators hs s) t

/-- The node word of Definition 1: the `n`-fold nested operator composition (matrix power)
of the single-step Suzuki product at step size `lam / n`, as an operator-valued function of
the factors `hs`, the recursion level `s`, and the integer step count `n`. -/
def suzukiNode (hs : List (Matrix I I ℂ)) (s : ℕ) (n : ℕ) (lam : ℝ) : Matrix I I ℂ :=
  suzukiStep hs s (lam / (n : ℝ)) ^ n

/-- The actual multi-product operator of Definition 1, Eq. (15): the linear combination
`sum_q C_q • S(lam / r_q)^{r_q}` of Suzuki node words over integer step counts `r q`,
general over the coefficient family `C` (the paper's `C_q` are the public `mCoeff`). -/
def multiproductOp (hs : List (Matrix I I ℂ)) (s : ℕ) {k : ℕ}
    (C : Fin (k + 1) → ℝ) (r : Fin (k + 1) → ℕ) (lam : ℝ) : Matrix I I ℂ :=
  ∑ q, C q • suzukiNode hs s (r q) lam

/-! ## Word calculus for the exponential word -/

/-- An exponential word over a concatenation is the product of the two exponential words. -/
private theorem suzukiExponentialWord_append (ls ms : List (Matrix I I ℂ)) (τ : ℝ) :
    suzukiExponentialWord (ls ++ ms) τ =
      suzukiExponentialWord ls τ * suzukiExponentialWord ms τ := by
  simp [suzukiExponentialWord, List.map_append, List.prod_append]

/-- An exponential word over a singleton list is the single exponential times the empty
word. -/
private theorem suzukiExponentialWord_cons (K : Matrix I I ℂ) (ks : List (Matrix I I ℂ))
    (τ : ℝ) : suzukiExponentialWord (K :: ks) τ =
      suzukiExponentialWord [K] τ * suzukiExponentialWord ks τ := by
  simp [suzukiExponentialWord]

/-- Scaling every generator by `c` rescales the time of the exponential word by `c`. -/
private theorem suzukiExponentialWord_map_scale (c τ : ℝ) :
    ∀ L : List (Matrix I I ℂ),
      suzukiExponentialWord (L.map fun X => c • X) τ = suzukiExponentialWord L (τ * c) := by
  intro L
  induction L with
  | nil => simp [suzukiExponentialWord]
  | cons X L ih =>
    have hhead : suzukiExponentialWord [c • X] τ = suzukiExponentialWord [X] (τ * c) := by
      simp only [suzukiExponentialWord, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      congr 1
      rw [smul_smul]
    rw [List.map_cons, suzukiExponentialWord_cons, hhead, ih]
    simp [suzukiExponentialWord]

/-- A one-generator word at negative time is a left inverse of the same word at positive
time. -/
private theorem suzukiExponentialWord_pair (t : ℝ) (K : Matrix I I ℂ) :
    suzukiExponentialWord [K] (-t) * suzukiExponentialWord [K] t = 1 := by
  simp only [suzukiExponentialWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  have hcomm : Commute ((-t) • K) (t • K) := by
    show (-t) • K * (t • K) = t • K * (-t) • K
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      neg_mul, mul_neg]
  have hsum : (-t) • K + t • K = 0 := by rw [neg_smul, neg_add_cancel]
  rw [← NormedSpace.exp_add_of_commute hcomm, hsum, NormedSpace.exp_zero]

/-! ## Definitional correctness: the composite identity -/

/-- At level zero the single-step Suzuki product is the explicit Strang alternating product
of Eq. (11): the forward half-step word over the factors followed by the backward half-step
word over the reversed factors. -/
theorem suzukiStep_zero_eq_strang (hs : List (Matrix I I ℂ)) (t : ℝ) :
    suzukiStep hs 0 t =
      suzukiExponentialWord hs (t / 2) * suzukiExponentialWord hs.reverse (t / 2) := by
  simp only [suzukiStep, recursiveSuzukiGenerators]
  rw [suzukiExponentialWord_append, suzukiExponentialWord_map_scale,
    suzukiExponentialWord_map_scale, mul_one_div]

/-- Composite identity for one node: the defined `n`-fold operator composition of the
single-step Suzuki product equals the stated nested product — the public `recursiveSuzukiWord`
flattened word of `n` repetitions of the level-`s` exponential word at step size `lam / n`. -/
theorem suzukiNode_eq_word_prod (hs : List (Matrix I I ℂ)) (s n : ℕ) (lam : ℝ) :
    suzukiNode hs s n lam = (recursiveSuzukiWord hs s lam n).prod := by
  simp only [suzukiNode, suzukiStep, recursiveSuzukiWord, suzukiExponentialWord,
    List.prod_flatten, List.map_replicate, List.prod_replicate]

/-- Composite identity for the full construction: the defined multi-product operator equals
the linear combination of the stated nested products, one flattened exponential word per
node. -/
theorem multiproductOp_eq_word_prod (hs : List (Matrix I I ℂ)) (s : ℕ) {k : ℕ}
    (C : Fin (k + 1) → ℝ) (r : Fin (k + 1) → ℕ) (lam : ℝ) :
    multiproductOp hs s C r lam =
      ∑ q, C q • (recursiveSuzukiWord hs s lam (r q)).prod := by
  simp [multiproductOp, suzukiNode_eq_word_prod]

/-- The defined multi-product operator with the paper's coefficients is exactly the public
Definition-1 linear combination `sum_q (mCoeff k N q : ℂ) • S q` of Eq. (15) with the actual
Suzuki node words as its terms. -/
theorem multiproductOp_eq_def1 (hs : List (Matrix I I ℂ)) (s k : ℕ) (N : ℝ)
    (r : Fin (k + 1) → ℕ) (lam : ℝ) :
    multiproductOp hs s (mCoeff k N) r lam =
      Definition1Formula.multiproductFormula k N (fun q => suzukiNode hs s (r q) lam) := by
  rw [multiproductOp, Definition1Formula.multiproductFormula]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Complex.coe_algebraMap]
  exact (IsScalarTower.algebraMap_smul (A := ℂ) (mCoeff k N q)
    (suzukiNode hs s (r q) lam)).symm

/-! ## Symmetry of the alternating schedule -/

/-- Reversal inversion for exponential words: the word of a reversed generator list at
negative time is a left inverse of the word at positive time. -/
private theorem suzukiExponentialWord_reverse_neg (t : ℝ) :
    ∀ L : List (Matrix I I ℂ),
      suzukiExponentialWord L.reverse (-t) * suzukiExponentialWord L t = 1 := by
  intro L
  induction L with
  | nil => simp [suzukiExponentialWord]
  | cons X L ih =>
    have hsecond : suzukiExponentialWord (X :: L) t =
        suzukiExponentialWord [X] t * suzukiExponentialWord L t :=
      suzukiExponentialWord_cons X L t
    have hre : ∀ p q : Matrix I I ℂ,
        (p * suzukiExponentialWord [X] (-t)) * (suzukiExponentialWord [X] t * q) =
          (p * (suzukiExponentialWord [X] (-t) * suzukiExponentialWord [X] t)) * q := by
      intro p q; noncomm_ring
    rw [List.reverse_cons, suzukiExponentialWord_append, hsecond, hre,
      suzukiExponentialWord_pair, mul_one]
    exact ih

/-- Negative time inverts the single-step Suzuki product: the palindromic generator
schedule of the public recursion makes the word at `-t` a left inverse of the word at `t`. -/
theorem suzukiStep_neg_time (hs : List (Matrix I I ℂ)) (s : ℕ) (t : ℝ) :
    suzukiStep hs s (-t) * suzukiStep hs s t = 1 := by
  have h := suzukiExponentialWord_reverse_neg t (recursiveSuzukiGenerators hs s)
  rw [recursiveSuzukiGenerators_reverse hs s] at h
  simpa [suzukiStep, suzukiExponentialWord] using h

/-- Negative time inverts a node word: the `n`-fold composition at `-lam` is a left inverse
of the `n`-fold composition at `lam`; this is the operator-side prerequisite of the
`E_k(-lam) E_k(lam)` estimate of Lemma 10. -/
theorem suzukiNode_neg_time (hs : List (Matrix I I ℂ)) (s n : ℕ) (lam : ℝ) :
    suzukiNode hs s n (-lam) * suzukiNode hs s n lam = 1 := by
  have hstep : suzukiStep hs s (-lam / (n : ℝ)) * suzukiStep hs s (lam / (n : ℝ)) = 1 := by
    rw [neg_div]
    exact suzukiStep_neg_time hs s (lam / (n : ℝ))
  exact pow_mul_pow_eq_one n hstep

/-! ## The defect-order hook (reused, not re-proved) -/

/-- The multiproduct defect-order boost of the AdiabaticEvol00 line
(`Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder.multiproduct_order_at`), forwarded to the actual Suzuki node
words: with the moment system over the integer step counts and the node-uniform defect
expansion of the Suzuki node words (the interface hypothesis of the reused analysis), the
multi-product operator obeys the order-`2 (chi + k) + 1` defect bound. The defect expansion
itself is derived independently in the derived first-row theorem and in the full odd-logarithm family
theorem below. -/
theorem suzuki_multiproduct_defect_order (k χ : ℕ) (hs : List (Matrix I I ℂ)) (s : ℕ)
    (C : Fin (k + 1) → ℝ) (r : Fin (k + 1) → ℕ)
    (hmom₁ : ∑ q, C q = 1)
    (hmom : ∀ j : ℕ, j < k → (∑ q, C q / ((r q : ℝ)) ^ (2 * χ + 2 * j)) = 0)
    (U : ℝ → Matrix I I ℂ) (D : ℕ → Matrix I I ℂ) (B lam : ℝ)
    (hd : ∀ q : Fin (k + 1),
      ‖suzukiNode hs s (r q) lam - U lam - ∑ j : Fin k, ((lam ^ (2 * χ + 1 + 2 * (j : ℕ))) /
          ((r q : ℝ) ^ (2 * χ + 2 * (j : ℕ)))) • (D (j : ℕ))‖ ≤
        B * lam ^ (2 * (χ + k) + 1)) :
    ‖(∑ q, C q • suzukiNode hs s (r q) lam) - U lam‖ ≤
      (∑ q, |C q|) * B * lam ^ (2 * (χ + k) + 1) :=
  multiproduct_order_at k χ C (fun q => ((r q : ℕ) : ℝ)) hmom₁ hmom U
    (fun q _ => suzukiNode hs s (r q) lam) D B lam hd

/-! ## Derived defects: the derived defect expansion of the Suzuki node words

The conditional theorem `suzuki_multiproduct_defect_order` takes the node-uniform defect
expansion as an interface hypothesis. This section derives the defect expansion from
the actual generator structure, in three steps.

First, the node word `suzukiNode hs s n lam` is a single exponential word over the
scaled concatenated generator list `nodeGenerators`, so the public `suzukiSeries`
machinery (HasSum representation, coefficient norm bounds) applies to it directly.
Second, the public `recursive_suzuki_all_even_order_coefficients` gives exact
coefficients: through the Suzuki order the node coefficients equal the exponential
coefficients, and at the first defect degree `2 χ + 1` the node coefficient is the
exponential coefficient plus the single-step defect scaled by `n ^ (-2 χ)`. Third,
the product-exponential tail control (the Lemma-9 estimate `x^(m+1)/(m+1)! * exp x`,
proved here for the `suzukiSeries` representation at any truncation order) bounds
the remainder with an explicit constant.

The combined statement `suzuki_multiproduct_first_defect_boost` discharges the defect
input of the multiproduct order boost at the first Richardson row: with `sum C = 1`
and `sum_q C q / (r q)^(2 χ) = 0`, the multiproduct over the actual Suzuki node words
obeys the order-`2 χ + 2` bound with the explicit tail constant, improving on the
single-node order `2 χ + 1`.

A structural remark on the interface: the literal conditional hypothesis `hd` (only
odd-degree defect terms) is not the right per-node form for the actual Suzuki nodes.
Beyond the first defect degree, the node word also has even-degree defect terms whose
node scalings are even powers of `1 / n` in the same moment-exponent family (they come
from exponentiating the odd-only defect of the logarithm of a symmetric word). The
correct general interface is therefore the family form `multiproduct_order_family`
below, whose defect curves are arbitrary node-independent curves scaled by the moment
exponents; the derivation above supplies its first defect term, and the full odd-logarithm family below derives the
full family from the odd-logarithm structure of symmetric words. -/

/-- The generator list of a node word as a single exponential word: the `n`-fold
concatenation of the single-step generator list, with every generator scaled by
`1 / n`, so that the exponential word at time `lam` is the node word. -/
def nodeGenerators (gs : List (Matrix I I ℂ)) (n : ℕ) : List (Matrix I I ℂ) :=
  ((List.replicate n gs).flatten).map (fun X => ((n : ℝ)⁻¹) • X)

/-- The degree-`m` defect of the exponential word of `gs` against the exponential of
`H`: the series coefficient minus the exponential coefficient `H^m / m!`. -/
def stepDefect (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (m : ℕ) : Matrix I I ℂ :=
  suzukiSeries gs m - ((m.factorial : ℝ)⁻¹) • H ^ m

/-! ### Series convolution and scaling -/

/-- The cons recursion of `suzukiSeries` as a sum over `range (m + 1)`. -/
private theorem suzukiSeries_cons_range (X : Matrix I I ℂ) (L : List (Matrix I I ℂ))
    (m : ℕ) : suzukiSeries (X :: L) m =
      ∑ a ∈ Finset.range (m + 1), (((a.factorial : ℝ)⁻¹) • X ^ a) * suzukiSeries L (m - a) := by
  rw [suzukiSeries, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Triangular sum swap: summing `F a b` over `a + b ≤ m` row-by-row equals summing it
diagonal-by-diagonal. -/
private theorem sum_triangle_swap {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → ℕ → M) :
    (∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m - a + 1), F a b) =
      ∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (c + 1), F a (c - a) := by
  rw [Finset.sum_sigma' (Finset.range (m + 1)) (fun a => Finset.range (m - a + 1)) F,
    Finset.sum_sigma' (Finset.range (m + 1)) (fun c => Finset.range (c + 1))
      (fun c a => F a (c - a))]
  refine Finset.sum_nbij' (fun x => ⟨x.1 + x.2, x.1⟩) (fun x => ⟨x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    cases x with
    | mk a b =>
      have hb : a + b - a = b := by omega
      simp [hb]
  · intro x hx
    cases x with
    | mk a b =>
      rw [Finset.mem_sigma] at hx
      have ha1 : a < m + 1 := Finset.mem_range.mp hx.1
      have hb1 : b < a + 1 := Finset.mem_range.mp hx.2
      have hc : b + (a - b) = a := by omega
      simp [hc]
  · intro x hx
    cases x with
    | mk a b =>
      have hb : a + b - a = b := by omega
      simp [hb]

/-- The coefficient of an exponential word over a concatenation is the convolution of
the coefficients of the two parts. -/
private theorem suzukiSeries_append_range : ∀ (L M : List (Matrix I I ℂ)) (m : ℕ),
    suzukiSeries (L ++ M) m =
      ∑ a ∈ Finset.range (m + 1), suzukiSeries L a * suzukiSeries M (m - a) := by
  intro L
  induction L with
  | nil =>
    intro M m
    simp only [List.nil_append]
    rw [Finset.sum_eq_single 0]
    · simp [suzukiSeries]
    · intro b _ hb
      cases b with
      | zero => exact absurd rfl hb
      | succ b => simp [suzukiSeries]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
  | cons X L ih =>
    intro M m
    have hL : suzukiSeries (X :: (L ++ M)) m =
        ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m - a + 1),
          (((a.factorial : ℝ)⁻¹) • X ^ a) *
            (suzukiSeries L b * suzukiSeries M (m - a - b)) := by
      rw [suzukiSeries_cons_range]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ih M (m - a), Finset.mul_sum]
    have hR : (∑ c ∈ Finset.range (m + 1), suzukiSeries (X :: L) c * suzukiSeries M (m - c)) =
        ∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (c + 1),
          ((((a.factorial : ℝ)⁻¹) • X ^ a) * suzukiSeries L (c - a)) * suzukiSeries M (m - c) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [suzukiSeries_cons_range, Finset.sum_mul]
    rw [List.cons_append, hL, hR,
      sum_triangle_swap m
        (fun a b => (((a.factorial : ℝ)⁻¹) • X ^ a) *
          (suzukiSeries L b * suzukiSeries M (m - a - b)))]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_range] at hc ha
    have hsub : m - a - (c - a) = m - c := by omega
    rw [hsub, mul_assoc]

/-- Scaling every generator by `c` scales the degree-`m` coefficient by `c ^ m`. -/
private theorem suzukiSeries_map_smul (c : ℝ) : ∀ (L : List (Matrix I I ℂ)) (m : ℕ),
    suzukiSeries (L.map (fun X => c • X)) m = c ^ m • suzukiSeries L m := by
  intro L
  induction L with
  | nil => intro m; cases m <;> simp [suzukiSeries]
  | cons X L ih =>
    intro m
    rw [List.map_cons, suzukiSeries_cons_range, suzukiSeries_cons_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_range] at ha
    rw [smul_pow, ih]
    have e1 : (((a.factorial : ℝ)⁻¹) • (c ^ a • X ^ a)) * (c ^ (m - a) • suzukiSeries L (m - a)) =
        ((a.factorial : ℝ)⁻¹ * (c ^ (m - a) * c ^ a)) • (X ^ a * suzukiSeries L (m - a)) := by
      simp only [smul_smul, Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      ring
    have e2 : c ^ m • (((a.factorial : ℝ)⁻¹ • X ^ a) * suzukiSeries L (m - a)) =
        (c ^ m * (a.factorial : ℝ)⁻¹) • (X ^ a * suzukiSeries L (m - a)) := by
      simp only [Matrix.smul_mul, smul_smul]
    rw [e1, e2, ← pow_add]
    have hm : m - a + a = m := by omega
    rw [hm]
    congr 1
    ring

/-! ### Exact node coefficients from the even-order cancellation -/

/-- Binomial sum in factorial form: the interior diagonal of `(ℓ + 1)^(N+1)` scaled by
`1 / (N+1)!`. -/
private theorem sum_choose_scaled (ℓ : ℝ) (N : ℕ) :
    (∑ a ∈ Finset.range N, (ℓ ^ (a + 1) : ℝ) *
        (((a + 1).factorial : ℝ) * ((N - a).factorial : ℝ))⁻¹) =
      ((ℓ + 1) ^ (N + 1) - 1 - ℓ ^ (N + 1)) / ((N + 1).factorial : ℝ) := by
  have hterm : ∀ a ∈ Finset.range N, (ℓ ^ (a + 1) : ℝ) *
      (((a + 1).factorial : ℝ) * ((N - a).factorial : ℝ))⁻¹ =
        (ℓ ^ (a + 1) * ((N + 1).choose (a + 1) : ℝ)) / ((N + 1).factorial : ℝ) := by
    intro a ha
    simp only [Finset.mem_range] at ha
    have hsum : (a + 1) + (N - a) = N + 1 := by omega
    have hchoose : (((N + 1).choose (a + 1) : ℕ) : ℝ) =
        ((N + 1).factorial : ℝ) / (((a + 1).factorial : ℝ) * ((N - a).factorial : ℝ)) := by
      rw [← hsum, Nat.cast_add_choose]
    rw [hchoose]
    field_simp [Nat.factorial_ne_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  congr 1
  have hpow := add_pow (ℓ : ℝ) 1 (N + 1)
  rw [Finset.sum_range_succ'] at hpow
  rw [Finset.sum_range_succ] at hpow
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, Nat.choose_zero_right,
    pow_zero] at hpow
  have hrew : (∑ a ∈ Finset.range N, ℓ ^ (a + 1) * ((N + 1).choose (a + 1) : ℝ)) =
      (∑ a ∈ Finset.range N, ℓ ^ (a + 1) * 1 ^ (N + 1 - (a + 1)) *
        ((N + 1).choose (a + 1) : ℝ)) := by simp
  rw [hrew, hpow]
  ring

/-- The coefficients of the concatenated word match the exponential through the
matched order: `u_m(ℓ) = ℓ^m • H^m / m!`. -/
private theorem suzukiSeries_replicate_matched (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p : ℕ) (hc : ∀ j ≤ p, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j) :
    ∀ (ℓ m : ℕ), m ≤ p → suzukiSeries ((List.replicate ℓ gs).flatten) m =
      (ℓ : ℝ) ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro m hm
    simp only [List.replicate_zero, List.flatten_nil, Nat.cast_zero]
    cases m <;> simp [suzukiSeries]
  | succ ℓ ih =>
    intro m hm
    have hrep : (List.replicate (ℓ + 1) gs).flatten = (List.replicate ℓ gs).flatten ++ gs := by
      rw [List.replicate_add]
      simp [List.flatten_append]
    rw [hrep, suzukiSeries_append_range]
    have hterm : ∀ a ∈ Finset.range (m + 1),
        suzukiSeries ((List.replicate ℓ gs).flatten) a * suzukiSeries gs (m - a) =
          ((ℓ : ℝ) ^ a * (((a.factorial : ℝ) * ((m - a).factorial : ℝ))⁻¹)) • H ^ m := by
      intro a ha
      simp only [Finset.mem_range] at ha
      have hmul : (((a.factorial : ℝ)⁻¹) • H ^ a) * (((m - a).factorial : ℝ)⁻¹) • H ^ (m - a) =
          (((a.factorial : ℝ) * ((m - a).factorial : ℝ))⁻¹) • H ^ m := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
        have hm' : a + (m - a) = m := by omega
        rw [hm', mul_inv]
      rw [ih a (by omega), hc (m - a) (by omega), Matrix.smul_mul, hmul, smul_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, smul_smul]
    congr 1
    have hsc : ∀ a ∈ Finset.range (m + 1),
        (ℓ : ℝ) ^ a * (((a.factorial : ℝ) * ((m - a).factorial : ℝ))⁻¹) =
          ((ℓ : ℝ) ^ a * (m.choose a : ℝ)) * ((m.factorial : ℝ)⁻¹) := by
      intro a ha
      simp only [Finset.mem_range] at ha
      have hsum : a + (m - a) = m := by omega
      have hchoose : ((m.choose a : ℕ) : ℝ) =
          (m.factorial : ℝ) / ((a.factorial : ℝ) * ((m - a).factorial : ℝ)) := by
        rw [← hsum, Nat.cast_add_choose]
        simp only [Nat.add_sub_cancel_left]
      rw [hchoose]
      field_simp [Nat.factorial_ne_zero]
    rw [Finset.sum_congr rfl hsc, ← Finset.sum_mul]
    congr 1
    have hpow := add_pow (ℓ : ℝ) 1 m
    simpa using hpow.symm

/-- The first defect coefficient of the concatenated word: at degree `2 χ + 1` it is
the exponential coefficient plus `ℓ` times the single-step defect. -/
private theorem suzukiSeries_replicate_first_defect (gs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (χ : ℕ)
    (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j) :
    ∀ ℓ : ℕ, suzukiSeries ((List.replicate ℓ gs).flatten) (2 * χ + 1) =
      (ℓ : ℝ) ^ (2 * χ + 1) • (((2 * χ + 1).factorial : ℝ)⁻¹) • H ^ (2 * χ + 1) +
        (ℓ : ℝ) • stepDefect gs H (2 * χ + 1) := by
  have hmatch := suzukiSeries_replicate_matched gs H (2 * χ) hc
  have hc1 : suzukiSeries gs (2 * χ + 1) =
      ((2 * χ + 1).factorial : ℝ)⁻¹ • H ^ (2 * χ + 1) + stepDefect gs H (2 * χ + 1) := by
    rw [stepDefect]; abel
  intro ℓ
  induction ℓ with
  | zero =>
    have hpos : 2 * χ + 1 ≠ 0 := by omega
    simp [zero_pow hpos]
  | succ ℓ ih =>
    have hrep : (List.replicate (ℓ + 1) gs).flatten = (List.replicate ℓ gs).flatten ++ gs := by
      rw [List.replicate_add]
      simp [List.flatten_append]
    rw [hrep, suzukiSeries_append_range, Finset.sum_range_succ]
    have hlast : suzukiSeries ((List.replicate ℓ gs).flatten) (2 * χ + 1) *
        suzukiSeries gs (2 * χ + 1 - (2 * χ + 1)) =
          (ℓ : ℝ) ^ (2 * χ + 1) • (((2 * χ + 1).factorial : ℝ)⁻¹) • H ^ (2 * χ + 1) +
            (ℓ : ℝ) • stepDefect gs H (2 * χ + 1) := by
      simp [suzukiSeries_zero, ih]
    rw [hlast, Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    have hfirst : suzukiSeries ((List.replicate ℓ gs).flatten) 0 * suzukiSeries gs (2 * χ + 1) =
        ((2 * χ + 1).factorial : ℝ)⁻¹ • H ^ (2 * χ + 1) + stepDefect gs H (2 * χ + 1) := by
      rw [suzukiSeries_zero, hc1, one_mul]
    rw [hfirst]
    have hmid : (∑ a ∈ Finset.range (2 * χ),
        suzukiSeries ((List.replicate ℓ gs).flatten) (a + 1) *
          suzukiSeries gs (2 * χ + 1 - (a + 1))) =
        (∑ a ∈ Finset.range (2 * χ), (ℓ : ℝ) ^ (a + 1) *
          (((a + 1).factorial : ℝ) * ((2 * χ - a).factorial : ℝ))⁻¹) • H ^ (2 * χ + 1) := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun a ha => ?_
      simp only [Finset.mem_range] at ha
      have hsub : 2 * χ + 1 - (a + 1) = 2 * χ - a := by omega
      rw [hsub]
      have hmul : (((a + 1).factorial : ℝ)⁻¹) • H ^ (a + 1) *
          (((2 * χ - a).factorial : ℝ)⁻¹) • H ^ (2 * χ - a) =
          (((a + 1).factorial : ℝ) * ((2 * χ - a).factorial : ℝ))⁻¹ • H ^ (2 * χ + 1) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
        have hm' : (a + 1) + (2 * χ - a) = 2 * χ + 1 := by omega
        rw [hm', mul_inv]
      rw [hmatch ℓ (a + 1) (by omega), hc (2 * χ - a) (by omega), Matrix.smul_mul, hmul,
        smul_smul]
    rw [hmid, sum_choose_scaled]
    push_cast
    module

/-! ### Product-exponential tail control (Lemma 9 form) -/

/-- The norm of the degree-`n` series term at real time `t` is at most
`(|t| * suzukiMass xs)^n / n!`. -/
private theorem suzukiSeries_term_norm' (xs : List (Matrix I I ℂ)) (t : ℝ) (n : ℕ) :
    ‖t ^ n • suzukiSeries xs n‖ ≤ (|t| * suzukiMass xs) ^ n / (n.factorial : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc
    _ ≤ |t| ^ n * (suzukiMass xs ^ n / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (suzukiSeries_norm_le xs n) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The norms of the time-scaled exponential-word coefficients form a summable series. -/
private theorem suzukiSeries_norm_summable' (xs : List (Matrix I I ℂ)) (t : ℝ) :
    Summable (fun n => ‖t ^ n • suzukiSeries xs n‖) := by
  have h : Summable (fun n => (|t| * suzukiMass xs) ^ n / (n.factorial : ℝ)) := by
    simpa only [smul_eq_mul, inv_mul_eq_div] using!
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (|t| * suzukiMass xs)).summable
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (suzukiSeries_term_norm' xs t)

/-- The real exponential `Real.exp a` is the sum of the series with terms `a^n / n!`. -/
private theorem suzuki_real_exp_hasSum' (a : ℝ) :
    HasSum (fun n : ℕ => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
  simpa only [smul_eq_mul, inv_mul_eq_div, ← Real.exp_eq_exp_ℝ] using!
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a

/-- For nonnegative `a`, the exponential-series tail starting at degree `m` is summable
and bounded by `a^m / m! * Real.exp a`. -/
private theorem suzuki_scalar_tail' (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    Summable (fun n : ℕ => a ^ (n + m) / ((n + m).factorial : ℝ)) ∧
      (∑' n : ℕ, a ^ (n + m) / ((n + m).factorial : ℝ)) ≤
        a ^ m / (m.factorial : ℝ) * Real.exp a := by
  have hterm (n : ℕ) : a ^ (n + m) / ((n + m).factorial : ℝ) ≤
      (a ^ m / (m.factorial : ℝ)) * (a ^ n / (n.factorial : ℝ)) := by
    have hfac : (n.factorial : ℝ) * (m.factorial : ℝ) ≤ ((n + m).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add n m)
    calc
      _ ≤ a ^ (n + m) / ((n.factorial : ℝ) * (m.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
      _ = _ := by rw [pow_add]; ring
  have hg := (suzuki_real_exp_hasSum' a).mul_left (a ^ m / (m.factorial : ℝ))
  have hs : Summable (fun n : ℕ => a ^ (n + m) / ((n + m).factorial : ℝ)) :=
    hg.summable.of_nonneg_of_le (fun _ => by positivity) hterm
  exact ⟨hs, (hs.tsum_le_tsum hterm hg.summable).trans_eq hg.tsum_eq⟩

/-- Lemma 9 (product-exponential tail control) for the `suzukiSeries` representation at
any truncation order: the exponential word minus its Taylor polynomial of degree `M` is
bounded by `exp(|t| * mass) * (|t| * mass)^(M+1) / (M+1)!`. -/
private theorem suzukiExponentialWord_trunc_bound (xs : List (Matrix I I ℂ)) (t : ℝ) (M : ℕ) :
    ‖suzukiExponentialWord xs t - ∑ n ∈ Finset.range (M + 1), t ^ n • suzukiSeries xs n‖ ≤
      Real.exp (|t| * suzukiMass xs) * (|t| * suzukiMass xs) ^ (M + 1) /
        ((M + 1).factorial : ℝ) := by
  let f := fun n : ℕ => t ^ n • suzukiSeries xs n
  let a := |t| * suzukiMass xs
  have hmass : 0 ≤ suzukiMass xs := by
    unfold suzukiMass
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg Y)
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg _) hmass
  have hs := suzukiSeries_norm_summable' xs t
  have hn : Summable (fun n => ‖f (n + (M + 1))‖) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have he : suzukiExponentialWord xs t - ∑ n ∈ Finset.range (M + 1), f n =
      ∑' n, f (n + (M + 1)) := by
    have h : (∑ n ∈ Finset.range (M + 1), f n) + (∑' n, f (n + (M + 1))) =
        suzukiExponentialWord xs t :=
      (hs.of_norm.sum_add_tsum_nat_add (M + 1)).trans (suzukiSeries_hasSum xs t).tsum_eq
    calc
      _ = ((∑ n ∈ Finset.range (M + 1), f n) + (∑' n, f (n + (M + 1)))) -
          (∑ n ∈ Finset.range (M + 1), f n) := by rw [h]
      _ = _ := by abel
  rw [he]
  obtain ⟨hscalar, hb⟩ := suzuki_scalar_tail' a ha (M + 1)
  calc
    _ ≤ ∑' n, ‖f (n + (M + 1))‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, a ^ (n + (M + 1)) / ((n + (M + 1)).factorial : ℝ) :=
      hn.tsum_le_tsum (fun n => suzukiSeries_term_norm' xs t (n + (M + 1))) hscalar
    _ ≤ a ^ (M + 1) / ((M + 1).factorial : ℝ) * Real.exp a := hb
    _ = _ := by ring

/-! ### The node word as a single exponential word -/

/-- The mass of the concatenated word is `ℓ` times the single-step mass. -/
private theorem suzukiMass_flatten_replicate (gs : List (Matrix I I ℂ)) :
    ∀ ℓ : ℕ, suzukiMass ((List.replicate ℓ gs).flatten) = (ℓ : ℝ) * suzukiMass gs := by
  have happ : ∀ A B : List (Matrix I I ℂ), suzukiMass (A ++ B) = suzukiMass A + suzukiMass B := by
    intro A B; simp [suzukiMass, List.map_append, List.sum_append]
  intro ℓ
  induction ℓ with
  | zero => simp [suzukiMass]
  | succ ℓ ih =>
    have hrep : (List.replicate (ℓ + 1) gs).flatten = (List.replicate ℓ gs).flatten ++ gs := by
      rw [List.replicate_add]
      simp [List.flatten_append]
    rw [hrep, happ, ih]
    push_cast
    ring

/-- Scaling every generator by `c` scales the mass by `|c|`. -/
private theorem suzukiMass_map_smul (c : ℝ) (xs : List (Matrix I I ℂ)) :
    suzukiMass (xs.map (fun X => c • X)) = |c| * suzukiMass xs := by
  induction xs with
  | nil => simp [suzukiMass]
  | cons X xs ih => simpa [suzukiMass, norm_smul, Real.norm_eq_abs, mul_add] using! ih

/-- The node word is the exponential word of `nodeGenerators` at time `lam`. -/
theorem suzukiNode_eq_scaled_word (hs : List (Matrix I I ℂ)) (s n : ℕ) (lam : ℝ) :
    suzukiNode hs s n lam =
      suzukiExponentialWord (nodeGenerators (recursiveSuzukiGenerators hs s) n) lam := by
  rw [nodeGenerators, suzukiExponentialWord_map_scale]
  simp only [suzukiNode, suzukiStep, suzukiExponentialWord, List.map_flatten,
    List.map_replicate, List.prod_flatten, List.prod_replicate, div_eq_mul_inv]

/-- The mass of the scaled node generator list equals the single-step mass. -/
private theorem suzukiMass_nodeGenerators (gs : List (Matrix I I ℂ)) (n : ℕ) (hn : 0 < n) :
    suzukiMass (nodeGenerators gs n) = suzukiMass gs := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [nodeGenerators, suzukiMass_map_smul, suzukiMass_flatten_replicate,
    abs_of_pos (inv_pos.mpr hn'), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn'), one_mul]

/-- Exact node coefficients through the matched order: with `gs` matching the
exponential of `H` through degree `2 χ`, the scaled node generator list matches the
exponential through degree `2 χ` as well. -/
theorem nodeGenerators_series_coeff_matched (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ : ℕ) (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (n m : ℕ) (hm : m ≤ 2 * χ) (hn : 0 < n) :
    suzukiSeries (nodeGenerators gs n) m = ((m.factorial : ℝ)⁻¹) • H ^ m := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [nodeGenerators, suzukiSeries_map_smul,
    suzukiSeries_replicate_matched _ _ (2 * χ) hc n m hm, smul_smul]
  have hsc : ((n : ℝ)⁻¹) ^ m * (n : ℝ) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hn'), one_pow]
  rw [hsc, one_smul]

/-- Exact first defect coefficient of the scaled node generator list: at degree
`2 χ + 1` the coefficient is the exponential coefficient plus the single-step defect
scaled by `n ^ (-2 χ)`. -/
theorem nodeGenerators_series_coeff_first_defect (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ : ℕ) (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (n : ℕ) (hn : 0 < n) :
    suzukiSeries (nodeGenerators gs n) (2 * χ + 1) =
      ((2 * χ + 1).factorial : ℝ)⁻¹ • H ^ (2 * χ + 1) +
        (((n : ℝ)⁻¹) ^ (2 * χ)) • stepDefect gs H (2 * χ + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [nodeGenerators, suzukiSeries_map_smul,
    suzukiSeries_replicate_first_defect _ _ χ hc n]
  simp only [smul_add, smul_smul]
  have hsc1 : ((n : ℝ)⁻¹) ^ (2 * χ + 1) * (n : ℝ) ^ (2 * χ + 1) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hn'), one_pow]
  have hsc2 : ((n : ℝ)⁻¹) ^ (2 * χ + 1) * (n : ℝ) = ((n : ℝ)⁻¹) ^ (2 * χ) := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ (ne_of_gt hn'), mul_one]
  rw [← mul_assoc, hsc1, hsc2, one_mul]

/-- The explicit tail constant of the derived defect expansion: the Lemma-9
product-exponential tail at truncation order `2 χ + 1`, of order `lam ^ (2 χ + 2)` as
`lam → 0`, summed over the node word and the exact exponential. -/
def defectTail (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (χ : ℕ) (lam : ℝ) : ℝ :=
  Real.exp (|lam| * suzukiMass gs) * (|lam| * suzukiMass gs) ^ (2 * χ + 2) /
      ((2 * χ + 2).factorial : ℝ) +
    Real.exp (|lam| * ‖H‖) * (|lam| * ‖H‖) ^ (2 * χ + 2) / ((2 * χ + 2).factorial : ℝ)

/-- The tail constant is nonnegative. -/
theorem defectTail_nonneg (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (χ : ℕ) (lam : ℝ) :
    0 ≤ defectTail gs H χ lam := by
  have hfac : (0 : ℝ) < ((2 * χ + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * χ + 2)
  have hmass : 0 ≤ suzukiMass gs := by
    unfold suzukiMass
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg Y)
  exact add_nonneg
    (div_nonneg (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (mul_nonneg (abs_nonneg _) hmass) _)) hfac.le)
    (div_nonneg (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg H)) _)) hfac.le)

/-- The first-order defect expansion of the scaled node word, derived from the
even-order coefficient cancellation and the product-exponential tail control: the node
word equals `exp(lam • H)` plus the single-step defect at degree `2 χ + 1` scaled by
`lam^(2χ+1) / n^(2χ)`, up to the explicit tail constant of order `lam^(2χ+2)`. -/
theorem nodeGenerators_first_defect_expansion (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ : ℕ) (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (n : ℕ) (hn : 0 < n) (lam : ℝ) :
    ‖suzukiExponentialWord (nodeGenerators gs n) lam - NormedSpace.exp (lam • H) -
        ((lam ^ (2 * χ + 1)) / ((n : ℝ) ^ (2 * χ))) • stepDefect gs H (2 * χ + 1)‖ ≤
      defectTail gs H χ lam := by
  have htrunc : (∑ m ∈ Finset.range (2 * χ + 2), lam ^ m •
      suzukiSeries (nodeGenerators gs n) m) =
      (∑ m ∈ Finset.range (2 * χ + 2), lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m)) +
        ((lam ^ (2 * χ + 1)) / ((n : ℝ) ^ (2 * χ))) • stepDefect gs H (2 * χ + 1) := by
    rw [Finset.sum_range_succ (fun m => lam ^ m • suzukiSeries (nodeGenerators gs n) m),
      Finset.sum_range_succ (fun m => lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m))]
    have hlow : (∑ m ∈ Finset.range (2 * χ + 1), lam ^ m •
        suzukiSeries (nodeGenerators gs n) m) =
        ∑ m ∈ Finset.range (2 * χ + 1), lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Finset.mem_range] at hm
      rw [nodeGenerators_series_coeff_matched gs H χ hc n m (by omega) hn]
    rw [hlow, nodeGenerators_series_coeff_first_defect gs H χ hc n hn, smul_add]
    have hsc : lam ^ (2 * χ + 1) • (((n : ℝ)⁻¹) ^ (2 * χ) • stepDefect gs H (2 * χ + 1)) =
        ((lam ^ (2 * χ + 1)) / ((n : ℝ) ^ (2 * χ))) • stepDefect gs H (2 * χ + 1) := by
      rw [smul_smul, inv_pow, div_eq_mul_inv]
    rw [hsc]
    abel
  have hE : NormedSpace.exp (lam • H) = suzukiExponentialWord [H] lam := by
    simp [suzukiExponentialWord]
  have hN := suzukiExponentialWord_trunc_bound (nodeGenerators gs n) lam (2 * χ + 1)
  have hE2 := suzukiExponentialWord_trunc_bound [H] lam (2 * χ + 1)
  rw [suzukiMass_nodeGenerators gs n hn] at hN
  have hmass : suzukiMass [H] = ‖H‖ := by simp [suzukiMass]
  rw [hmass] at hE2
  have hsing : (∑ m ∈ Finset.range (2 * χ + 2), lam ^ m • suzukiSeries [H] m) =
      ∑ m ∈ Finset.range (2 * χ + 2), lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [suzukiSeries_singleton]
  rw [hsing] at hE2
  have hdecomp : suzukiExponentialWord (nodeGenerators gs n) lam - NormedSpace.exp (lam • H) -
      ((lam ^ (2 * χ + 1)) / ((n : ℝ) ^ (2 * χ))) • stepDefect gs H (2 * χ + 1) =
      (suzukiExponentialWord (nodeGenerators gs n) lam -
        (∑ m ∈ Finset.range (2 * χ + 2), lam ^ m • suzukiSeries (nodeGenerators gs n) m)) -
      (suzukiExponentialWord [H] lam -
        (∑ m ∈ Finset.range (2 * χ + 2), lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m))) := by
    rw [hE, htrunc]
    abel
  rw [hdecomp]
  exact (norm_sub_le _ _).trans (add_le_add hN hE2)

/-- The first-order defect expansion of the actual Suzuki node word, derived from the
public even-order cancellation `recursive_suzuki_all_even_order_coefficients` and the
product-exponential tail control. -/
theorem suzukiNode_first_defect_expansion (hs : List (Matrix I I ℂ)) (s χ n : ℕ)
    (hχ : χ ≤ s + 1) (hn : 0 < n) (lam : ℝ) :
    ‖suzukiNode hs s n lam - NormedSpace.exp (lam • hs.sum) -
        ((lam ^ (2 * χ + 1)) / ((n : ℝ) ^ (2 * χ))) •
          stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1)‖ ≤
      defectTail (recursiveSuzukiGenerators hs s) hs.sum χ lam := by
  rw [suzukiNode_eq_scaled_word hs s n lam]
  exact nodeGenerators_first_defect_expansion (recursiveSuzukiGenerators hs s) hs.sum χ
    (fun j hj => recursive_suzuki_all_even_order_coefficients I hs s j (by omega)) n hn lam

/-- The derived multiproduct boost at the first Richardson row: with `sum C = 1` and
the first moment row `sum_q C q / (r q)^(2 χ) = 0`, the multiproduct over the actual
Suzuki node words obeys the order-`2 χ + 2` bound with the explicit tail constant,
improving on the single-node order `2 χ + 1`. The defect expansion input is derived,
not assumed. -/
theorem suzuki_multiproduct_first_defect_boost (hs : List (Matrix I I ℂ)) (s χ k : ℕ)
    (hχ : χ ≤ s + 1) (C : Fin (k + 1) → ℝ) (r : Fin (k + 1) → ℕ) (hr : ∀ q, 0 < r q)
    (hmom₁ : ∑ q, C q = 1) (hmom : ∑ q, C q / ((r q : ℝ) ^ (2 * χ)) = 0) (lam : ℝ) :
    ‖(∑ q, C q • suzukiNode hs s (r q) lam) - NormedSpace.exp (lam • hs.sum)‖ ≤
      (∑ q, |C q|) * defectTail (recursiveSuzukiGenerators hs s) hs.sum χ lam := by
  have hsplit : (∑ q, C q • suzukiNode hs s (r q) lam) - NormedSpace.exp (lam • hs.sum) =
      ∑ q, C q • (suzukiNode hs s (r q) lam - NormedSpace.exp (lam • hs.sum)) := by
    have hU : NormedSpace.exp (lam • hs.sum) = ∑ q, C q • NormedSpace.exp (lam • hs.sum) := by
      rw [← Finset.sum_smul, hmom₁, one_smul]
    conv_lhs => rw [hU]
    rw [← Finset.sum_sub_distrib]
    simp only [smul_sub]
  have hdef : ∀ q : Fin (k + 1),
      C q • (suzukiNode hs s (r q) lam - NormedSpace.exp (lam • hs.sum)) =
      C q • (suzukiNode hs s (r q) lam - NormedSpace.exp (lam • hs.sum) -
          ((lam ^ (2 * χ + 1)) / ((r q : ℝ) ^ (2 * χ))) •
            stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1)) +
        C q • (((lam ^ (2 * χ + 1)) / ((r q : ℝ) ^ (2 * χ))) •
          stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1)) := by
    intro q
    rw [← smul_add, sub_add_cancel]
  rw [hsplit, Finset.sum_congr rfl (fun q _ => hdef q), Finset.sum_add_distrib]
  have hzero : (∑ q, C q • (((lam ^ (2 * χ + 1)) / ((r q : ℝ) ^ (2 * χ))) •
      stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1))) = 0 := by
    have hterm : ∀ q : Fin (k + 1),
        C q • (((lam ^ (2 * χ + 1)) / ((r q : ℝ) ^ (2 * χ))) •
          stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1)) =
        ((C q / ((r q : ℝ) ^ (2 * χ))) * lam ^ (2 * χ + 1)) •
          stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1) := by
      intro q
      rw [smul_smul]
      congr 1
      rw [← mul_div_assoc, div_mul_eq_mul_div]
    rw [Finset.sum_congr rfl (fun q _ => hterm q), ← Finset.sum_smul, ← Finset.sum_mul, hmom,
      zero_mul, zero_smul]
  rw [hzero, add_zero]
  calc ‖∑ q, C q • (suzukiNode hs s (r q) lam - NormedSpace.exp (lam • hs.sum) -
        ((lam ^ (2 * χ + 1)) / ((r q : ℝ) ^ (2 * χ))) •
          stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1))‖
      ≤ ∑ q, ‖C q • (suzukiNode hs s (r q) lam - NormedSpace.exp (lam • hs.sum) -
          ((lam ^ (2 * χ + 1)) / ((r q : ℝ) ^ (2 * χ))) •
            stepDefect (recursiveSuzukiGenerators hs s) hs.sum (2 * χ + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ q, |C q| * defectTail (recursiveSuzukiGenerators hs s) hs.sum χ lam := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (suzukiNode_first_defect_expansion hs s χ (r q) hχ (hr q) lam) (abs_nonneg (C q))
    _ = (∑ q, |C q|) * defectTail (recursiveSuzukiGenerators hs s) hs.sum χ lam :=
        (Finset.sum_mul _ _ _).symm

section FamilyInterface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The general defect-family form of the multiproduct order boost: with the moment
system over the nodes and node-uniform defect curves `P j` (arbitrary node-independent
curves, scaled by the moment exponents `ℓ q ^ (2 χ + 2 j)`), the multiproduct obeys the
order-`2 (χ + k) + 1` bound. Specializing `P j lam := lam^(2χ+1+2j) • D j` recovers the
shape of `Qatlib.Papers.HamLCUSim12.TaylorBounds.DefectOrder.multiproduct_order_at`; the actual Suzuki nodes
require the general form because even-degree defect terms carry the same moment
exponents. -/
theorem multiproduct_order_family (k χ : ℕ) (C : Fin (k + 1) → ℝ) (ℓ : Fin (k + 1) → ℝ)
    (hmom₁ : ∑ q, C q = 1)
    (hmom : ∀ j : ℕ, j < k → (∑ q, C q / ℓ q ^ (2 * χ + 2 * j)) = 0)
    (U : ℝ → E) (W : Fin (k + 1) → ℝ → E) (P : Fin k → ℝ → E) (B lam : ℝ)
    (hd : ∀ q : Fin (k + 1),
      ‖W q lam - U lam - ∑ j : Fin k, ((ℓ q ^ (2 * χ + 2 * (j : ℕ)))⁻¹) • (P j lam)‖ ≤
        B * lam ^ (2 * (χ + k) + 1)) :
    ‖(∑ q, C q • W q lam) - U lam‖ ≤ (∑ q, |C q|) * B * lam ^ (2 * (χ + k) + 1) := by
  have hU : U lam = ∑ q, C q • U lam := by rw [← Finset.sum_smul, hmom₁, one_smul]
  have hsplit : (∑ q, C q • W q lam) - U lam = ∑ q, C q • (W q lam - U lam) := by
    conv_lhs => rw [hU]
    rw [← Finset.sum_sub_distrib]
    simp only [smul_sub]
  have hzero : (∑ q, C q • ∑ j : Fin k, ((ℓ q ^ (2 * χ + 2 * (j : ℕ)))⁻¹) • (P j lam)) = 0 := by
    have hterm : ∀ q : Fin (k + 1),
        C q • ∑ j : Fin k, ((ℓ q ^ (2 * χ + 2 * (j : ℕ)))⁻¹) • (P j lam) =
        ∑ j : Fin k, (C q / ℓ q ^ (2 * χ + 2 * (j : ℕ))) • (P j lam) := by
      intro q
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
    rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul, hmom (j : ℕ) j.isLt, zero_smul]
  rw [hsplit]
  have hdecomp : ∀ q : Fin (k + 1), C q • (W q lam - U lam) =
      C q • (W q lam - U lam - ∑ j : Fin k, ((ℓ q ^ (2 * χ + 2 * (j : ℕ)))⁻¹) • (P j lam)) +
        C q • ∑ j : Fin k, ((ℓ q ^ (2 * χ + 2 * (j : ℕ)))⁻¹) • (P j lam) := by
    intro q
    rw [← smul_add, sub_add_cancel]
  rw [Finset.sum_congr rfl (fun q _ => hdecomp q), Finset.sum_add_distrib, hzero, add_zero]
  calc ‖∑ q, C q • (W q lam - U lam - ∑ j : Fin k, ((ℓ q ^ (2 * χ + 2 * (j : ℕ)))⁻¹) • (P j lam))‖
      ≤ ∑ q, ‖C q • (W q lam - U lam - ∑ j : Fin k, ((ℓ q ^ (2 * χ + 2 * (j : ℕ)))⁻¹) • (P j lam))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q, |C q| * (B * lam ^ (2 * (χ + k) + 1)) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hd q) (abs_nonneg (C q))
    _ = (∑ q, |C q|) * (B * lam ^ (2 * (χ + k) + 1)) := (Finset.sum_mul _ _ _).symm
    _ = (∑ q, |C q|) * B * lam ^ (2 * (χ + k) + 1) := (mul_assoc _ _ _).symm

end FamilyInterface

/-! ### The Lemma-5 coefficient mass and the actual Definition-1 multiproduct -/

/-- Under the Lemma-5 small-time condition, the terminal node `N = exp(γ(k+1))`
dominates `k`, so it differs from every initial node. -/
private theorem mNode_gt_of_cond (k : ℕ) (hk : 1 ≤ k) (γ : ℝ)
    (hcond : 2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ))) :
    (k : ℝ) < Real.exp (γ * ((k + 1 : ℕ) : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hNpos : (0 : ℝ) < Real.exp (γ * ((k + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hN2 : (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) ^ 2 =
      Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    push_cast
    ring
  by_contra hle
  have hle' : Real.exp (γ * ((k + 1 : ℕ) : ℝ)) ≤ (k : ℝ) := not_lt.mp hle
  have hsq : (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) ^ 2 ≤ (k : ℝ) ^ 2 :=
    pow_le_pow_left₀ hNpos.le hle' 2
  nlinarith [hcond, hN2, hsq, hkpos]

/-- The terminal node differs from every initial node under the Lemma-5 condition. -/
private theorem nodesDistinct_of_cond (k : ℕ) (hk : 1 ≤ k) (γ : ℝ)
    (hcond : 2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ))) :
    NodesDistinct k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) := by
  intro j hj
  have hNk := mNode_gt_of_cond k hk γ hcond
  have hle : ((j : ℕ) + 1 : ℝ) ≤ (k : ℝ) := by
    have hjk : (j : ℕ) + 1 ≤ k := by omega
    exact_mod_cast hjk
  exact ne_of_gt (lt_of_le_of_lt hle hNk)

/-- Lemma 5's exponential coefficient bound driven to the constant `2`: with the
Lemma-5 small-time condition and the explicit size condition
`(5/2) log k + (1/2) log 2 ≤ 2k(γ - (1 + log(312/1000)/2))`, every Definition-1
coefficient satisfies `|mCoeff| ≤ 2`. The first `k` coefficients are bounded by
`1 / k` each from `lemma5_coeff_bound`; the terminal coefficient is bounded through
`sum C = 1`. This is the `|C_q| ≤ 2` input of the printed Lemma 8 bound. -/
theorem mCoeff_abs_le_two (k : ℕ) (hk : 1 ≤ k) (γ : ℝ) (hγ : 0 < γ)
    (hcond : 2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)))
    (hlarge : (5 / 2 : ℝ) * Real.log (k : ℝ) + (1 / 2 : ℝ) * Real.log 2 ≤
      2 * (k : ℝ) * (γ - (1 + Real.log (312 / 1000) / 2))) :
    ∀ q : Fin (k + 1), |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q| ≤ 2 := by
  obtain ⟨η, hηlo, hηhi, hb⟩ := Lemma5CoeffBound.lemma5_coeff_bound
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hNpos : (0 : ℝ) < Real.exp (γ * ((k + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hdistinct := nodesDistinct_of_cond k hk γ hcond
  have hmoms := Definition1Formula.definition1_moments k (Real.exp (γ * ((k + 1 : ℕ) : ℝ)))
    hNpos hdistinct
  have hper : ∀ q : Fin k, |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q)| ≤
      1 / (k : ℝ) := by
    intro q
    have hq : ((Fin.castSucc q : Fin (k + 1)) : ℕ) < k := q.isLt
    have h1 := hb k hk γ hγ hcond (Fin.castSucc q) hq
    have hlog : Real.log η < Real.log (312 / 1000) :=
      Real.log_lt_log (by linarith [hηlo] : (0 : ℝ) < η) hηhi
    have hexp : Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - γ)) ≤
        (Real.sqrt 2 * (k : ℝ) ^ ((5 : ℝ) / 2))⁻¹ := by
      have harg : 2 * (k : ℝ) * (1 + Real.log η / 2 - γ) ≤
          -((5 / 2 : ℝ) * Real.log (k : ℝ) + (1 / 2 : ℝ) * Real.log 2) := by
        have hmul : 2 * (k : ℝ) * (1 + Real.log η / 2 - γ) ≤
            2 * (k : ℝ) * (1 + Real.log (312 / 1000) / 2 - γ) :=
          mul_le_mul_of_nonneg_left (by linarith [hlog]) (by positivity)
        nlinarith [hmul, hlarge]
      have hE1 : Real.exp (-((5 / 2 : ℝ) * Real.log (k : ℝ) + (1 / 2 : ℝ) * Real.log 2)) =
          (Real.sqrt 2 * (k : ℝ) ^ ((5 : ℝ) / 2))⁻¹ := by
        rw [neg_add, Real.exp_add]
        have hk5 : Real.exp (-((5 / 2 : ℝ) * Real.log (k : ℝ))) =
            ((k : ℝ) ^ ((5 : ℝ) / 2))⁻¹ := by
          rw [Real.rpow_def_of_pos hkpos, ← Real.exp_neg]
          congr 1
          ring
        have hs2 : Real.exp (-((1 / 2 : ℝ) * Real.log 2)) = (Real.sqrt 2)⁻¹ := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
            ← Real.exp_neg]
          congr 1
          ring
        rw [hk5, hs2, mul_inv]
        ring
      exact (Real.exp_le_exp.mpr harg).trans_eq hE1
    have hC : Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2) *
        (Real.sqrt 2 * (k : ℝ) ^ ((5 : ℝ) / 2))⁻¹ = 1 / (k : ℝ) := by
      have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hkk : (k : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ ((5 : ℝ) / 2) = (k : ℝ)⁻¹ := by
        rw [← Real.rpow_sub hkpos, show (3 : ℝ) / 2 - 5 / 2 = -1 from by norm_num,
          Real.rpow_neg_one]
      calc Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2) *
          (Real.sqrt 2 * (k : ℝ) ^ ((5 : ℝ) / 2))⁻¹
          = (Real.sqrt 2 * (Real.sqrt 2)⁻¹) *
            ((k : ℝ) ^ ((3 : ℝ) / 2) / (k : ℝ) ^ ((5 : ℝ) / 2)) := by
            rw [mul_inv]; ring
        _ = 1 * (k : ℝ)⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt hs2), hkk]
        _ = 1 / (k : ℝ) := by rw [one_div, one_mul]
    exact h1.trans ((mul_le_mul_of_nonneg_left hexp
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) :
        (0 : ℝ) ≤ Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2))).trans_eq hC)
  have hsum : (∑ q : Fin k, |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q)|) ≤
      1 := by
    have hle : (∑ q : Fin k, |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q)|) ≤
        ∑ q : Fin k, (1 / (k : ℝ)) := Finset.sum_le_sum (fun q _ => hper q)
    have hconst : (∑ q : Fin k, (1 / (k : ℝ))) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_div,
        mul_inv_cancel₀ (ne_of_gt hkpos)]
    exact hle.trans_eq hconst
  have hmain := hmoms.1
  rw [Fin.sum_univ_castSucc] at hmain
  intro q
  induction q using Fin.lastCases with
  | last =>
    have hlast : mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.last k) =
        1 - ∑ q : Fin k, mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q) := by
      linarith [hmain]
    rw [hlast]
    calc |1 - ∑ q : Fin k, mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q)|
        ≤ |1| + |∑ q : Fin k, mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q)| :=
          abs_sub _ _
      _ ≤ 1 + ∑ q : Fin k, |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q)| := by
          rw [abs_one]
          have habs : |∑ q : Fin k, mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ)))
              (Fin.castSucc q)| ≤
              ∑ q : Fin k, |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q)| := by
            simpa only [Real.norm_eq_abs] using
              norm_sum_le Finset.univ (fun q : Fin k =>
                mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (Fin.castSucc q))
          linarith [habs]
      _ ≤ 2 := by linarith [hsum]  | cast q =>
    have h1 := hper q
    have hk1 : (1 : ℝ) / (k : ℝ) ≤ 1 := (div_le_one hkpos).mpr (by exact_mod_cast hk)
    linarith [h1, hk1]

/-- The actual Definition-1 multiproduct over the Suzuki node words, with the derived
defect expansion and the Lemma-5 coefficient mass: under the Lemma-5 small-time
condition, the explicit size condition, and integrality of the terminal node, the
multiproduct obeys the order-`2 (s+1) + 2` bound with constant `2 (k+1)` times the
explicit tail. The first moment row at `m = s + 1` comes from the public
`definition1_moments`. -/
theorem suzuki_multiproduct_mCoeff_boost (hs : List (Matrix I I ℂ)) (s k : ℕ)
    (hk : 1 ≤ k) (hsk : s + 1 ≤ k) (γ : ℝ) (hγ : 0 < γ)
    (hcond : 2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)))
    (hlarge : (5 / 2 : ℝ) * Real.log (k : ℝ) + (1 / 2 : ℝ) * Real.log 2 ≤
      2 * (k : ℝ) * (γ - (1 + Real.log (312 / 1000) / 2)))
    (n : ℕ) (hn : 0 < n) (hnN : (n : ℝ) = Real.exp (γ * ((k + 1 : ℕ) : ℝ))) (lam : ℝ) :
    let r : Fin (k + 1) → ℕ := fun q => if (q : ℕ) < k then (q : ℕ) + 1 else n
    ‖(∑ q, mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q • suzukiNode hs s (r q) lam) -
        NormedSpace.exp (lam • hs.sum)‖ ≤
      (2 * ((k : ℝ) + 1)) * defectTail (recursiveSuzukiGenerators hs s) hs.sum (s + 1) lam := by
  intro r
  have hNpos : (0 : ℝ) < Real.exp (γ * ((k + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hdistinct := nodesDistinct_of_cond k hk γ hcond
  have hmoms := Definition1Formula.definition1_moments k (Real.exp (γ * ((k + 1 : ℕ) : ℝ)))
    hNpos hdistinct
  have hr : ∀ q : Fin (k + 1), 0 < r q := by
    intro q
    dsimp only [r]
    split_ifs with hq
    · omega
    · exact hn
  have hrN : ∀ q : Fin (k + 1), ((r q : ℕ) : ℝ) =
      mNode k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q := by
    intro q
    by_cases hq : (q : ℕ) < k
    · dsimp only [r]
      rw [ite_eq_left hq]
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((Definition1Formula.definition1_nodes k _).1 q hq).symm
    · have hql : q = Fin.last k := by
        have hval : (q : ℕ) = k := by omega
        exact Fin.ext (by simpa using hval)
      dsimp only [r]
      rw [ite_eq_right hq, hql, hnN]
      exact (Definition1Formula.definition1_nodes k _).2.symm
  have hrow : (∑ q, mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q /
      ((r q : ℝ) ^ (2 * (s + 1)))) = 0 := by
    rw [Finset.sum_congr rfl (fun q _ => by rw [hrN q])]
    exact hmoms.2 (s + 1) (by omega) hsk
  have hB := suzuki_multiproduct_first_defect_boost hs s (s + 1) k (le_refl _)
    (mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ)))) r hr hmoms.1 hrow lam
  have hmass : (∑ q, |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q|) ≤ 2 * ((k : ℝ) + 1) := by
    have hle : (∑ q : Fin (k + 1), |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q|) ≤
        ∑ q : Fin (k + 1), (2 : ℝ) :=
      Finset.sum_le_sum (fun q _ => mCoeff_abs_le_two k hk γ hγ hcond hlarge q)
    have hconst : (∑ q : Fin (k + 1), (2 : ℝ)) = 2 * ((k : ℝ) + 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    exact hle.trans_eq hconst
  exact hB.trans (mul_le_mul_of_nonneg_right hmass (defectTail_nonneg _ _ _ _))

/-! ## Full defect family: formal odd logarithms and the full defect family

The public `BCHFormal` development supplies the missing noncommutative algebraic layer: a
formal logarithm for a normalized matrix power series, reconstruction of the original series
from that logarithm, scaling under repetition, and vanishing of every even logarithm
coefficient for a palindromic word. No analytic logarithm or convergence hypothesis is needed.
This section combines those coefficient identities with the matched-order calculation
to construct the defect curves for every Richardson row and to derive the complete input of
`multiproduct_order_family`. -/

/-- Two complex polynomials that agree at every natural number are equal. -/
private theorem polynomial_eq_of_nat_eval' (p q : Polynomial ℂ)
    (h : ∀ n : ℕ, p.eval (n : ℂ) = q.eval (n : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℂ)))).mono
  rintro _ ⟨n, rfl⟩
  exact h n

/-- The degree-one coefficient of an exponential word is the sum of its generators. -/
private theorem suzukiSeries_one' : ∀ gs : List (Matrix I I ℂ), suzukiSeries gs 1 = gs.sum := by
  intro gs
  induction gs with
  | nil => rfl
  | cons X gs ih => simp [ih, add_comm]

/-- Matching through order `2 χ` determines the exponent-interpolation polynomial at every
degree in that range: it is the exponential coefficient times the monomial of the same degree. -/
private theorem powerPolynomial_eq_matched (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ m : ℕ) (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (hm : m ≤ 2 * χ) (i j : I) :
    Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.powerPolynomial
        (Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries gs) m i j =
      Polynomial.C ((((m.factorial : ℝ)⁻¹) • H ^ m) i j) * Polynomial.X ^ m := by
  apply polynomial_eq_of_nat_eval'
  intro q
  rw [Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.powerPolynomial_eval _
    (by simp [Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries])]
  have hcoeff : PowerSeries.coeff m
      (Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries gs ^ q) =
        (q : ℝ) ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m) := by
    rw [← Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries_replicate]
    simpa only [Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries,
      PowerSeries.coeff_mk] using suzukiSeries_replicate_matched gs H (2 * χ) hc q m hm
  rw [hcoeff]
  simp [Matrix.smul_apply, Complex.real_smul, mul_comm]

/-- The formal logarithm of a word matching `exp H` through order `2 χ` has the same low-order
coefficients: only the linear coefficient `H` survives through that order. -/
private theorem logCoefficient_matched (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ : ℕ) (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (m : ℕ) (hm : m ≤ 2 * χ) :
    Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal.logCoefficient
      (Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries gs) m =
        if m = 1 then H else 0 := by
  by_cases hm1 : m = 1
  · subst m
    rw [Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal.logCoefficient_one, ite_eq_left rfl]
    simpa [Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries] using
      hc 1 (by omega)
  · rw [ite_eq_right hm1]
    by_cases hm0 : m = 0
    · subst m
      exact Qatlib.Papers.CommutLCHS26.MainResults.BCHFormal.logCoefficient_zero _
    · have hm2 : 2 ≤ m := by omega
      ext i j
      change (Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.powerPolynomial
        (Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial.wordSeries gs) m i j).coeff 1 = 0
      rw [powerPolynomial_eq_matched gs H χ m hc hm, Polynomial.coeff_C_mul_X_pow,
        ite_eq_right (by omega)]

/-- If a normalized logarithm series has linear coefficient `H` and no other coefficients
through degree `2 χ`, then below the first possible defect its powers are concentrated on the
diagonal: the degree-`r` coefficient of the `r`th power is `H ^ r`, and all earlier coefficients
up to the defect margin vanish. -/
private theorem coeff_log_pow_below_defect (L : PowerSeries (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ : ℕ) (hzero : PowerSeries.coeff 0 L = 0) (hone : PowerSeries.coeff 1 L = H)
    (hlow : ∀ b : ℕ, 2 ≤ b → b ≤ 2 * χ → PowerSeries.coeff b L = 0) :
    ∀ r m : ℕ, m < r + 2 * χ →
      PowerSeries.coeff m (L ^ r) = if m = r then H ^ r else 0 := by
  have hc0 : L.constantCoeff = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hzero
  intro r
  induction r with
  | zero =>
    intro m hm
    by_cases hm0 : m = 0 <;> simp [hm0]
  | succ r ih =>
    intro m hm
    have hother : ∀ p : ℕ × ℕ, p ∈ Finset.HasAntidiagonal.antidiagonal m → p.2 ≠ 1 →
        PowerSeries.coeff p.1 (L ^ r) * PowerSeries.coeff p.2 L = 0 := by
      intro p hp hp1
      have hsum : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases hp0 : p.2 = 0
      · rw [hp0, hzero, mul_zero]
      · have hp2 : 2 ≤ p.2 := by omega
        by_cases hple : p.2 ≤ 2 * χ
        · rw [hlow p.2 hp2 hple, mul_zero]
        · have hlt : p.1 < r := by omega
          rw [power_coeff_vanish L hc0 p.1 r hlt, zero_mul]
    rw [pow_succ, PowerSeries.coeff_mul]
    by_cases hmr : m = r + 1
    · rw [ite_eq_left hmr]
      rw [Finset.sum_eq_single (r, 1)]
      · rw [ih r (by omega), ite_eq_left rfl, hone, pow_succ]
      · intro p hp hne
        by_cases hp1 : p.2 = 1
        · have hsum : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hpair : p = (r, 1) := by
            apply Prod.ext <;> dsimp <;> omega
          exact (hne hpair).elim
        · exact hother p hp hp1
      · intro hnot
        exact (hnot (by simp [hmr])).elim
    · rw [ite_eq_right hmr]
      apply Finset.sum_eq_zero
      intro p hp
      by_cases hp1 : p.2 = 1
      · have hsum : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have hlt : p.1 < r + 2 * χ := by omega
        have hne : p.1 ≠ r := by omega
        rw [hp1, hone, ih p.1 hlt, ite_eq_right hne, zero_mul]
      · exact hother p hp hp1

/-- If every even coefficient of a series vanishes, then the degree and power of every nonzero
coefficient of a natural power have the same parity. -/
private theorem coeff_log_pow_odd (L : PowerSeries (Matrix I I ℂ))
    (heven : ∀ n : ℕ, Even n → PowerSeries.coeff n L = 0) :
    ∀ r m : ℕ, Odd (m + r) → PowerSeries.coeff m (L ^ r) = 0 := by
  intro r
  induction r with
  | zero =>
    intro m hm
    have hm0 : m ≠ 0 := by
      rcases hm with ⟨u, hu⟩
      omega
    simp [hm0]
  | succ r ih =>
    intro m hmr
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hsum : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rcases Nat.even_or_odd p.2 with he | ho
    · rw [heven p.2 he, mul_zero]
    · have hodd : Odd (p.1 + r) := by
        rcases hmr with ⟨u, hu⟩
        rcases ho with ⟨v, hv⟩
        exact ⟨u - v - 1, by omega⟩
      rw [ih p.1 hodd, zero_mul]

/-- The matrix coefficient of `n ^ (-e)` in the degree-`m` coefficient of an `n`-fold
subdivided word. It is the reflected exponent-interpolation coefficient, extended by zero when
`e > m`. -/
def subdivisionCoefficient (gs : List (Matrix I I ℂ)) (m e : ℕ) : Matrix I I ℂ :=
  if e ≤ m then fun i j => (powerPolynomial (wordSeries gs) m i j).coeff (m - e) else 0

/-- A subdivision coefficient is the corresponding coefficient of a power of the formal
logarithm, divided by the factorial of the logarithm-power exponent. -/
private theorem subdivisionCoefficient_eq_log_pow (gs : List (Matrix I I ℂ)) (m e : ℕ)
    (he : e ≤ m) : subdivisionCoefficient gs m e =
      ((m - e).factorial : ℂ)⁻¹ •
        PowerSeries.coeff m (logSeries (wordSeries gs) ^ (m - e)) := by
  simp only [subdivisionCoefficient, he, ↓reduceIte]
  ext i j
  have h := congrArg (fun F : PowerSeries (Matrix I I ℂ) =>
    (PowerSeries.coeff m F : Matrix I I ℂ) i j)
    (exponentCoefficient_eq (wordSeries gs) (by simp [wordSeries]) (m - e))
  rw [exponentCoefficient, PowerSeries.coeff_mk] at h
  simpa only [PowerSeries.coeff_smul, Matrix.smul_apply, smul_eq_mul] using! h

/-- The zeroth subdivision coefficient is always the exact exponential coefficient. -/
theorem subdivisionCoefficient_zero (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (hH : suzukiSeries gs 1 = H) (m : ℕ) :
    subdivisionCoefficient gs m 0 = ((m.factorial : ℝ)⁻¹) • H ^ m := by
  simp only [subdivisionCoefficient, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  have h1 : PowerSeries.coeff 1 (wordSeries gs) = H := by
    simpa only [wordSeries, PowerSeries.coeff_mk] using hH
  ext i j
  rw [powerPolynomial_leading _ (by simp [wordSeries]), h1]
  simp [Matrix.smul_apply, Complex.real_smul, mul_comm]

/-- Positive subdivision exponents below `2 χ` vanish when the word matches the exponential
through order `2 χ`. -/
private theorem subdivisionCoefficient_eq_zero_of_low (gs : List (Matrix I I ℂ))
    (H : Matrix I I ℂ) (χ : ℕ)
    (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (hH : suzukiSeries gs 1 = H) (m e : ℕ) (he : e ≤ m) (he0 : 0 < e) (hel : e < 2 * χ) :
    subdivisionCoefficient gs m e = 0 := by
  have hzero : PowerSeries.coeff 0 (logSeries (wordSeries gs)) = 0 := by
    simpa only [logSeries, PowerSeries.coeff_mk] using logCoefficient_zero (wordSeries gs)
  have hone : PowerSeries.coeff 1 (logSeries (wordSeries gs)) = H := by
    rw [logSeries, PowerSeries.coeff_mk, logCoefficient_one]
    simpa only [wordSeries, PowerSeries.coeff_mk] using hH
  have hlow : ∀ b : ℕ, 2 ≤ b → b ≤ 2 * χ →
      PowerSeries.coeff b (logSeries (wordSeries gs)) = 0 := by
    intro b hb2 hbχ
    have hb1 : b ≠ 1 := by omega
    simpa only [logSeries, PowerSeries.coeff_mk, ite_eq_right hb1] using
      logCoefficient_matched gs H χ hc b hbχ
  rw [subdivisionCoefficient_eq_log_pow gs m e he]
  have hne : m ≠ m - e := by omega
  rw [coeff_log_pow_below_defect (logSeries (wordSeries gs)) H χ hzero hone hlow
    (m - e) m (by omega), ite_eq_right hne, smul_zero]

/-- Palindrome symmetry makes every odd subdivision exponent vanish. -/
private theorem subdivisionCoefficient_eq_zero_of_odd (gs : List (Matrix I I ℂ))
    (hgs : gs.reverse = gs) (m e : ℕ) (he : e ≤ m) (hodd : Odd e) :
    subdivisionCoefficient gs m e = 0 := by
  have heven : ∀ b : ℕ, Even b → PowerSeries.coeff b (logSeries (wordSeries gs)) = 0 := by
    intro b hb
    simpa only [logSeries, PowerSeries.coeff_mk] using symmetric_logCoefficient_even gs hgs b hb
  rw [subdivisionCoefficient_eq_log_pow gs m e he]
  have hpa : Odd (m + (m - e)) := by
    rcases hodd with ⟨u, hu⟩
    exact ⟨m - u - 1, by omega⟩
  rw [coeff_log_pow_odd (logSeries (wordSeries gs)) heven (m - e) m hpa, smul_zero]

/-- Below the target degree `2 (χ + k) + 1`, subdivision exponents at or beyond
`2 χ + 2 k` vanish: only the constant exponent-polynomial coefficient could remain there, and
that coefficient is zero at positive degree. -/
private theorem subdivisionCoefficient_eq_zero_of_top (gs : List (Matrix I I ℂ)) (χ k m e : ℕ)
    (hχ : 0 < χ) (hm : m < 2 * (χ + k) + 1) (he : e ≤ m) (hetop : 2 * χ + 2 * k ≤ e) :
    subdivisionCoefficient gs m e = 0 := by
  simp only [subdivisionCoefficient, he, ↓reduceIte]
  have hr : m - e = 0 := by omega
  ext i j
  change (powerPolynomial (wordSeries gs) m i j).coeff (m - e) = 0
  rw [hr]
  exact powerPolynomial_zero _ (by simp [wordSeries]) m (by omega) i j

/-- The degree-`m` coefficient of a positive subdivided node is the finite sum of its
subdivision coefficients, weighted by the corresponding inverse node powers. -/
theorem nodeGenerators_series_coeff_eq_subdivision_sum (gs : List (Matrix I I ℂ))
    (n m : ℕ) (hn : 0 < n) : suzukiSeries (nodeGenerators gs n) m =
      ∑ e ∈ Finset.range (m + 1), ((n : ℝ)⁻¹) ^ e • subdivisionCoefficient gs m e := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  let : Invertible (n : ℂ) := invertibleOfNonzero hnC
  have hcoeff : suzukiSeries (nodeGenerators gs n) m =
      ((n : ℝ)⁻¹) ^ m • PowerSeries.coeff m (wordSeries gs ^ n) := by
    rw [nodeGenerators, suzukiSeries_map_smul, ← wordSeries_replicate]
    simp only [wordSeries, PowerSeries.coeff_mk]
  ext i j
  rw [hcoeff]
  let p := powerPolynomial (wordSeries gs) m i j
  have hp := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (n : ℂ) m p
    (powerPolynomial_degree _ _ _ _)
  simp only [Polynomial.eval₂_id, invOf_eq_inv] at hp
  have heval : ((((n : ℝ)⁻¹) ^ m • PowerSeries.coeff m (wordSeries gs ^ n)) i j) =
      (p.reflect m).eval ((n : ℂ)⁻¹) := by
    rw [Matrix.smul_apply, Complex.real_smul]
    simp only [Complex.ofReal_pow, Complex.ofReal_inv]
    change ((n : ℂ)⁻¹) ^ m * (PowerSeries.coeff m (wordSeries gs ^ n)) i j = _
    rw [← powerPolynomial_eval _ (by simp [wordSeries])]
    change ((n : ℂ)⁻¹) ^ m * p.eval (n : ℂ) = _
    rw [← hp]
    calc
      _ = (p.reflect m).eval ((n : ℂ)⁻¹) * (((n : ℂ)⁻¹ * (n : ℂ)) ^ m) := by
        rw [mul_pow]
        ring
      _ = _ := by rw [inv_mul_cancel₀ hnC, one_pow, mul_one]
  rw [heval]
  have hdeg : (p.reflect m).natDegree < m + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_reflect_le.trans
      (max_le le_rfl (powerPolynomial_degree _ _ _ _)))
  rw [Polynomial.eval_eq_sum_range' hdeg]
  dsimp only [p]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro e he
  have hem : e ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using he
  simp only [subdivisionCoefficient, hem, ↓reduceIte, Polynomial.coeff_reflect,
    Polynomial.revAt_le hem, Complex.ofReal_inv, Complex.ofReal_pow]
  push_cast
  ring

/-- A finite sum supported on zero and the even moment exponents `2 χ + 2 j` can be
reindexed as its constant term plus the sum over the Richardson rows. -/
private theorem sum_range_moment_support {M : Type*} [AddCommMonoid M] (F : ℕ → M)
    (χ k m : ℕ) (hχ : 0 < χ) (hm : m < 2 * (χ + k) + 1)
    (hout : ∀ e : ℕ, m < e → F e = 0)
    (hodd : ∀ e : ℕ, e ≤ m → Odd e → F e = 0)
    (hlow : ∀ e : ℕ, e ≤ m → 0 < e → e < 2 * χ → F e = 0)
    (htop : ∀ e : ℕ, e ≤ m → 2 * χ + 2 * k ≤ e → F e = 0) :
    (∑ e ∈ Finset.range (m + 1), F e) =
      F 0 + ∑ j : Fin k, F (2 * χ + 2 * (j : ℕ)) := by
  have hext : (∑ e ∈ Finset.range (m + 1), F e) =
      ∑ e ∈ Finset.range (2 * (χ + k) + 1), F e := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro e _ henot
    apply hout
    simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using henot
  have hsub : insert 0 (Finset.univ.image (fun j : Fin k => 2 * χ + 2 * (j : ℕ))) ⊆
      Finset.range (2 * (χ + k) + 1) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with rfl | ⟨j, rfl⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by have := j.isLt; omega)
  have hsupp : (∑ e ∈ Finset.range (2 * (χ + k) + 1), F e) =
      ∑ e ∈ insert 0 (Finset.univ.image (fun j : Fin k => 2 * χ + 2 * (j : ℕ))), F e := by
    symm
    apply Finset.sum_subset hsub
    intro e _ heT
    by_cases hem : m < e
    · exact hout e hem
    · have hele : e ≤ m := by omega
      by_cases he0 : e = 0
      · subst e
        exact (heT (Finset.mem_insert_self 0 _)).elim
      by_cases hel : e < 2 * χ
      · exact hlow e hele (by omega) hel
      by_cases het : 2 * χ + 2 * k ≤ e
      · exact htop e hele het
      rcases Nat.even_or_odd e with heven | ho
      · exfalso
        apply heT
        apply Finset.mem_insert_of_mem
        rcases heven with ⟨a, ha⟩
        apply Finset.mem_image.mpr
        refine ⟨⟨a - χ, by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp
        omega
      · exact hodd e hele ho
  have hzero : 0 ∉ Finset.univ.image (fun j : Fin k => 2 * χ + 2 * (j : ℕ)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    omega
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin k)), ∀ b ∈ (Finset.univ : Finset (Fin k)),
      2 * χ + 2 * (a : ℕ) = 2 * χ + 2 * (b : ℕ) → a = b := by
    intro a _ b _ hab
    apply Fin.ext
    omega
  rw [hext, hsupp, Finset.sum_insert hzero, Finset.sum_image hinj]

/-- The node-independent defect curve attached to Richardson row `j`: at each Taylor degree
below `2 (χ + k) + 1`, it collects the subdivision coefficient of exponent `2 χ + 2 j`. -/
def subdivisionDefectCurve (gs : List (Matrix I I ℂ)) (χ k : ℕ) (j : Fin k) (lam : ℝ) :
    Matrix I I ℂ :=
  ∑ m ∈ Finset.range (2 * (χ + k) + 1),
    lam ^ m • subdivisionCoefficient gs m (2 * χ + 2 * (j : ℕ))

/-- Exact truncated Taylor expansion of a symmetric subdivided word. Below the target degree,
the coefficient of every inverse-node power is collected into the exponential polynomial or one
of the `k` node-independent defect curves. -/
theorem nodeGenerators_taylor_defect_family (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ k : ℕ) (hχ : 0 < χ) (hgs : gs.reverse = gs)
    (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (hH : suzukiSeries gs 1 = H) (n : ℕ) (hn : 0 < n) (lam : ℝ) :
    (∑ m ∈ Finset.range (2 * (χ + k) + 1),
        lam ^ m • suzukiSeries (nodeGenerators gs n) m) =
      (∑ m ∈ Finset.range (2 * (χ + k) + 1),
        lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m)) +
        ∑ j : Fin k, (((n : ℝ) ^ (2 * χ + 2 * (j : ℕ)))⁻¹) •
          subdivisionDefectCurve gs χ k j lam := by
  calc
    _ = ∑ m ∈ Finset.range (2 * (χ + k) + 1), lam ^ m •
        (∑ e ∈ Finset.range (m + 1),
          ((n : ℝ)⁻¹) ^ e • subdivisionCoefficient gs m e) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [nodeGenerators_series_coeff_eq_subdivision_sum gs n m hn]
    _ = ∑ m ∈ Finset.range (2 * (χ + k) + 1),
        (lam ^ m • subdivisionCoefficient gs m 0 +
          ∑ j : Fin k, lam ^ m • (((n : ℝ)⁻¹) ^ (2 * χ + 2 * (j : ℕ)) •
            subdivisionCoefficient gs m (2 * χ + 2 * (j : ℕ)))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.smul_sum]
      have hmem : m < 2 * (χ + k) + 1 := Finset.mem_range.mp hm
      have hs := sum_range_moment_support
        (F := fun e => lam ^ m • (((n : ℝ)⁻¹) ^ e • subdivisionCoefficient gs m e))
        χ k m hχ hmem (by
          intro e he
          have hnm : ¬e ≤ m := by omega
          simp only [subdivisionCoefficient, hnm, ↓reduceIte, smul_zero]) (by
          intro e he ho
          rw [subdivisionCoefficient_eq_zero_of_odd gs hgs m e he ho, smul_zero, smul_zero]) (by
          intro e he he0 hel
          rw [subdivisionCoefficient_eq_zero_of_low gs H χ hc hH m e he he0 hel,
            smul_zero, smul_zero]) (by
          intro e he het
          rw [subdivisionCoefficient_eq_zero_of_top gs χ k m e hχ hmem he het,
            smul_zero, smul_zero])
      simpa only [pow_zero, one_smul] using hs
    _ = (∑ m ∈ Finset.range (2 * (χ + k) + 1),
        lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m)) +
        ∑ m ∈ Finset.range (2 * (χ + k) + 1), ∑ j : Fin k,
          lam ^ m • (((n : ℝ)⁻¹) ^ (2 * χ + 2 * (j : ℕ)) •
            subdivisionCoefficient gs m (2 * χ + 2 * (j : ℕ))) := by
      simp only [subdivisionCoefficient_zero gs H hH]
      rw [Finset.sum_add_distrib]
    _ = (∑ m ∈ Finset.range (2 * (χ + k) + 1),
        lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m)) +
        ∑ j : Fin k, ∑ m ∈ Finset.range (2 * (χ + k) + 1),
          lam ^ m • (((n : ℝ)⁻¹) ^ (2 * χ + 2 * (j : ℕ)) •
            subdivisionCoefficient gs m (2 * χ + 2 * (j : ℕ))) := by
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [subdivisionDefectCurve, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [smul_smul, smul_smul, inv_pow]
      congr 1
      ring

/-- The explicit product-exponential tail at order `2 (χ + k) + 1`, summing the tails of the
subdivided word and of the exact exponential. -/
def subdivisionTail (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (χ k : ℕ) (lam : ℝ) : ℝ :=
  Real.exp (|lam| * suzukiMass gs) * (|lam| * suzukiMass gs) ^ (2 * (χ + k) + 1) /
      ((2 * (χ + k) + 1).factorial : ℝ) +
    Real.exp (|lam| * ‖H‖) * (|lam| * ‖H‖) ^ (2 * (χ + k) + 1) /
      ((2 * (χ + k) + 1).factorial : ℝ)

/-- The coefficient of `|lam| ^ (2 (χ + k) + 1)` in `subdivisionTail`. -/
def subdivisionTailScale (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ) (χ k : ℕ) (lam : ℝ) : ℝ :=
  Real.exp (|lam| * suzukiMass gs) * suzukiMass gs ^ (2 * (χ + k) + 1) /
      ((2 * (χ + k) + 1).factorial : ℝ) +
    Real.exp (|lam| * ‖H‖) * ‖H‖ ^ (2 * (χ + k) + 1) /
      ((2 * (χ + k) + 1).factorial : ℝ)

/-- The full tail factors as its scale times the absolute value of the target odd power. -/
theorem subdivisionTail_eq_scale (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ k : ℕ) (lam : ℝ) : subdivisionTail gs H χ k lam =
      subdivisionTailScale gs H χ k lam * |lam| ^ (2 * (χ + k) + 1) := by
  rw [subdivisionTail, subdivisionTailScale, mul_pow, mul_pow]
  ring

/-- The tail scale is nonnegative. -/
theorem subdivisionTailScale_nonneg (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ k : ℕ) (lam : ℝ) : 0 ≤ subdivisionTailScale gs H χ k lam := by
  have hmass : 0 ≤ suzukiMass gs := by
    unfold suzukiMass
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg Y)
  unfold subdivisionTailScale
  positivity

/-- The complete defect-family expansion of a symmetric subdivided word, with the explicit
product-exponential tail at order `2 (χ + k) + 1`. -/
theorem nodeGenerators_defect_family_expansion (gs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (χ k : ℕ) (hχ : 0 < χ) (hgs : gs.reverse = gs)
    (hc : ∀ j ≤ 2 * χ, suzukiSeries gs j = ((j.factorial : ℝ)⁻¹) • H ^ j)
    (hH : suzukiSeries gs 1 = H) (n : ℕ) (hn : 0 < n) (lam : ℝ) :
    ‖suzukiExponentialWord (nodeGenerators gs n) lam - NormedSpace.exp (lam • H) -
        ∑ j : Fin k, (((n : ℝ) ^ (2 * χ + 2 * (j : ℕ)))⁻¹) •
          subdivisionDefectCurve gs χ k j lam‖ ≤
      subdivisionTail gs H χ k lam := by
  have htrunc := nodeGenerators_taylor_defect_family gs H χ k hχ hgs hc hH n hn lam
  have hE : NormedSpace.exp (lam • H) = suzukiExponentialWord [H] lam := by
    simp [suzukiExponentialWord]
  have hN := suzukiExponentialWord_trunc_bound (nodeGenerators gs n) lam (2 * (χ + k))
  have hE2 := suzukiExponentialWord_trunc_bound [H] lam (2 * (χ + k))
  rw [suzukiMass_nodeGenerators gs n hn] at hN
  have hmass : suzukiMass [H] = ‖H‖ := by simp [suzukiMass]
  rw [hmass] at hE2
  have hsing : (∑ m ∈ Finset.range (2 * (χ + k) + 1), lam ^ m • suzukiSeries [H] m) =
      ∑ m ∈ Finset.range (2 * (χ + k) + 1), lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [suzukiSeries_singleton]
  rw [hsing] at hE2
  have hdecomp : suzukiExponentialWord (nodeGenerators gs n) lam - NormedSpace.exp (lam • H) -
      (∑ j : Fin k, (((n : ℝ) ^ (2 * χ + 2 * (j : ℕ)))⁻¹) •
        subdivisionDefectCurve gs χ k j lam) =
      (suzukiExponentialWord (nodeGenerators gs n) lam -
        (∑ m ∈ Finset.range (2 * (χ + k) + 1),
          lam ^ m • suzukiSeries (nodeGenerators gs n) m)) -
      (suzukiExponentialWord [H] lam -
        (∑ m ∈ Finset.range (2 * (χ + k) + 1),
          lam ^ m • (((m.factorial : ℝ)⁻¹) • H ^ m))) := by
    rw [hE, htrunc]
    abel
  rw [hdecomp, subdivisionTail]
  exact (norm_sub_le _ _).trans (add_le_add hN hE2)

/-- The complete defect-family expansion of the actual level-`s` Suzuki node, with
`χ = s + 1` and all `k` Richardson rows derived from the palindromic formal logarithm. -/
theorem suzukiNode_defect_family_expansion (hs : List (Matrix I I ℂ)) (s k n : ℕ)
    (hn : 0 < n) (lam : ℝ) :
    ‖suzukiNode hs s n lam - NormedSpace.exp (lam • hs.sum) -
        ∑ j : Fin k, (((n : ℝ) ^ (2 * (s + 1) + 2 * (j : ℕ)))⁻¹) •
          subdivisionDefectCurve (recursiveSuzukiGenerators hs s) (s + 1) k j lam‖ ≤
      subdivisionTail (recursiveSuzukiGenerators hs s) hs.sum (s + 1) k lam := by
  rw [suzukiNode_eq_scaled_word hs s n lam]
  exact nodeGenerators_defect_family_expansion (recursiveSuzukiGenerators hs s) hs.sum
    (s + 1) k (by omega) (recursiveSuzukiGenerators_reverse hs s)
    (fun j hj => recursive_suzuki_all_even_order_coefficients I hs s j (by omega))
    (by
      have h := recursive_suzuki_all_even_order_coefficients I hs s 1 (by omega)
      simpa using h) n hn lam

/-- The full multiproduct order boost for the actual Suzuki nodes: the odd-log defect curves
are derived, not assumed, and are supplied to `multiproduct_order_family`. With `χ = s + 1`,
the explicit tail has order `2 (χ + k) + 1`. -/
theorem suzuki_multiproduct_full_defect_order (hs : List (Matrix I I ℂ)) (s k : ℕ)
    (C : Fin (k + 1) → ℝ) (r : Fin (k + 1) → ℕ) (hr : ∀ q, 0 < r q)
    (hmom₁ : ∑ q, C q = 1)
    (hmom : ∀ j : ℕ, j < k → (∑ q, C q / ((r q : ℝ)) ^ (2 * (s + 1) + 2 * j)) = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ‖(∑ q, C q • suzukiNode hs s (r q) lam) - NormedSpace.exp (lam • hs.sum)‖ ≤
      (∑ q, |C q|) * subdivisionTail (recursiveSuzukiGenerators hs s) hs.sum (s + 1) k lam := by
  have hd : ∀ q : Fin (k + 1),
      ‖suzukiNode hs s (r q) lam - NormedSpace.exp (lam • hs.sum) -
          ∑ j : Fin k, (((r q : ℝ) ^ (2 * (s + 1) + 2 * (j : ℕ)))⁻¹) •
            subdivisionDefectCurve (recursiveSuzukiGenerators hs s) (s + 1) k j lam‖ ≤
        subdivisionTailScale (recursiveSuzukiGenerators hs s) hs.sum (s + 1) k lam *
          lam ^ (2 * ((s + 1) + k) + 1) := by
    intro q
    have h := suzukiNode_defect_family_expansion hs s k (r q) (hr q) lam
    rw [subdivisionTail_eq_scale, abs_of_nonneg hlam] at h
    exact h
  have hmain := multiproduct_order_family k (s + 1) C (fun q => (r q : ℝ)) hmom₁ hmom
    (fun t => NormedSpace.exp (t • hs.sum)) (fun q t => suzukiNode hs s (r q) t)
    (fun j => subdivisionDefectCurve (recursiveSuzukiGenerators hs s) (s + 1) k j)
    (subdivisionTailScale (recursiveSuzukiGenerators hs s) hs.sum (s + 1) k lam) lam hd
  calc
    _ ≤ (∑ q, |C q|) *
        subdivisionTailScale (recursiveSuzukiGenerators hs s) hs.sum (s + 1) k lam *
          lam ^ (2 * ((s + 1) + k) + 1) := hmain
    _ = (∑ q, |C q|) *
        subdivisionTail (recursiveSuzukiGenerators hs s) hs.sum (s + 1) k lam := by
      rw [subdivisionTail_eq_scale, abs_of_nonneg hlam]
      ring

/-! ### The Lemma-12 rounded terminal node -/

/-- The Lemma-12 rounding bridge: the ceiling node is a positive natural step count after
`Int.toNat`, and exponentiating `(k + 1) • correctedGamma` recovers both that natural step count
and the original real integer node. -/
theorem integerNode_rounding_bridge (η : ℝ) (k : ℕ) :
    0 < (integerNode η k).toNat ∧
      (((integerNode η k).toNat : ℝ) =
        Real.exp (correctedGamma η k * ((k + 1 : ℕ) : ℝ))) ∧
      Real.exp (correctedGamma η k * ((k + 1 : ℕ) : ℝ)) = ((integerNode η k : ℤ) : ℝ) := by
  have hpos : (0 : ℝ) < ((integerNode η k : ℤ) : ℝ) := by
    rw [integerNode]
    exact (Real.exp_pos _).trans_le (Int.le_ceil _)
  have hZ : 0 < integerNode η k := by exact_mod_cast hpos
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hExp : Real.exp (correctedGamma η k * ((k + 1 : ℕ) : ℝ)) =
      ((integerNode η k : ℤ) : ℝ) := by
    rw [correctedGamma, div_mul_cancel₀ _ hk1, Real.exp_log hpos]
  have hcastZ : (((integerNode η k).toNat : ℤ) = integerNode η k) :=
    Int.toNat_of_nonneg hZ.le
  have hcast : (((integerNode η k).toNat : ℝ) = ((integerNode η k : ℤ) : ℝ)) := by
    exact_mod_cast hcastZ
  exact ⟨by omega, hcast.trans hExp.symm, hExp⟩

/-- The `mCoeff` boost with its terminal integrality hypothesis discharged by the actual
Lemma-12 `integerNode`. The remaining hypotheses are exactly the Lemma-5 conditions expressed
at `correctedGamma η k`. -/
theorem suzuki_multiproduct_mCoeff_integerNode_boost (hs : List (Matrix I I ℂ)) (s k : ℕ)
    (hk : 1 ≤ k) (hsk : s + 1 ≤ k) (η : ℝ) (hγ : 0 < correctedGamma η k)
    (hcond : 2 * (k : ℝ) ^ 2 ≤
      Real.exp (2 * correctedGamma η k * ((k + 1 : ℕ) : ℝ)))
    (hlarge : (5 / 2 : ℝ) * Real.log (k : ℝ) + (1 / 2 : ℝ) * Real.log 2 ≤
      2 * (k : ℝ) * (correctedGamma η k - (1 + Real.log (312 / 1000) / 2))) (lam : ℝ) :
    let n := (integerNode η k).toNat
    let r : Fin (k + 1) → ℕ := fun q => if (q : ℕ) < k then (q : ℕ) + 1 else n
    ‖(∑ q, mCoeff k ((integerNode η k : ℤ) : ℝ) q • suzukiNode hs s (r q) lam) -
        NormedSpace.exp (lam • hs.sum)‖ ≤
      (2 * ((k : ℝ) + 1)) *
        defectTail (recursiveSuzukiGenerators hs s) hs.sum (s + 1) lam := by
  intro n r
  obtain ⟨hn, hnN, hExp⟩ := integerNode_rounding_bridge η k
  have hmain := suzuki_multiproduct_mCoeff_boost hs s k hk hsk (correctedGamma η k) hγ
    hcond hlarge n hn hnN lam
  rw [hExp] at hmain
  exact hmain

/-! ## Corrected exponent: the Lemma-12 numerical conditions at `correctedGamma`

The integer-node theorem `suzuki_multiproduct_mCoeff_integerNode_boost` still takes the three
numerical conditions of the Lemma-5 chain — the positivity `hγ`, the separation
`hcond : 2 k^2 ≤ exp (2 γ (k + 1))`, and the explicit size condition
`hlarge : (5/2) log k + (1/2) log 2 ≤ 2k (γ − (1 + log (312/1000)/2))` — as hypotheses at
`γ = correctedGamma η k`. This wave derives them from the paper's Lemma-12 hypotheses: the
η window `305/1000 < η < 312/1000` and an explicit size threshold on `k`.

The public Lemma-12 bundle `lemma12IntegerNodesCorrected` supplies the rounded-node facts
(exponentiating the corrected exponent recovers the rounded node, the corrected exponent
dominates the threshold exponent `gammaReq η k`, and the rounded node's square dominates
`2 k^2`); the first two numerical conditions follow directly, and the third reduces to the
explicit log-ratio bound `k * log (312/1000 / η) ≤ 3 * log 2`, which the concrete threshold
`k ≤ 91` implies uniformly over the η window (the exact integer inequality
`(312/305)^(91:ℕ) ≤ 2^(3:ℕ)`). The final theorem assembles the conditional multiproduct
bound with every hypothesis side now derived: the terminal-node rounding (integer-node construction), the
derived defect expansion (derived defect expansion), and the η conditions at `correctedGamma` (corrected-exponent analysis). -/

/-- The three rounded-node facts of the public Lemma-12 bundle that drive the numerical
conditions: exponentiating `correctedGamma η k` over `k + 1` recovers the rounded integer
node, the corrected exponent dominates the threshold exponent `gammaReq η k`, and the
rounded node's square dominates `2 k^2`. The bundle's simulation and coefficient hypotheses
are discharged with dummy parameters and the point mass at the terminal index. -/
theorem correctedGamma_node_facts (η : ℝ) (hηlo : 305 / 1000 < η) (hηhi : η < 312 / 1000)
    (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (correctedGamma η k * ((k + 1 : ℕ) : ℝ)) = ((integerNode η k : ℤ) : ℝ) ∧
      gammaReq η k ≤ correctedGamma η k ∧
      2 * (k : ℝ) ^ 2 ≤ ((integerNode η k : ℤ) : ℝ) ^ 2 := by
  have hCsum : (∑ q ∈ Finset.Icc 1 (k + 1), (if q = k + 1 then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_eq_single (k + 1)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hmem
      exact absurd (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩) hmem
  have hCbd : ∀ q ∈ Finset.Icc 1 k,
      |(if q = k + 1 then (1 : ℝ) else 0)| ≤
        2 ^ (1 / 2 : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) *
          Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - correctedGamma η k)) := by
    intro q hq
    have hne : q ≠ k + 1 := by
      simp only [Finset.mem_Icc] at hq
      omega
    have h0 : (if q = k + 1 then (1 : ℝ) else 0) = 0 := by simp [hne]
    rw [h0, abs_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.exp_pos _).le
  obtain ⟨_, _, h3, h4, _, _, h7, _⟩ :=
    lemma12IntegerNodesCorrected η hηlo hηhi k hk 1 1 1 1 (1 / 2) le_rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun q => if q = k + 1 then 1 else 0) hCsum hCbd
  exact ⟨h3, h4, h7⟩

/-- The Lemma-5 separation condition at the corrected exponent (the `hcond` input):
the rounded node's square, re-exponentiated, dominates `2 k^2`. -/
theorem correctedGamma_cond (η : ℝ) (hηlo : 305 / 1000 < η) (hηhi : η < 312 / 1000)
    (k : ℕ) (hk : 1 ≤ k) :
    2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * correctedGamma η k * ((k + 1 : ℕ) : ℝ)) := by
  obtain ⟨h3, _, h7⟩ := correctedGamma_node_facts η hηlo hηhi k hk
  have hsq : ((integerNode η k : ℤ) : ℝ) ^ 2 =
      Real.exp (2 * correctedGamma η k * ((k + 1 : ℕ) : ℝ)) := by
    rw [pow_two, ← h3, ← Real.exp_add]
    congr 1
    ring
  rwa [hsq] at h7

/-- The corrected exponent is positive (the `hγ` input): the separation condition
already forces a positive exponent, since a nonpositive exponent would cap its exponential
at `exp 0 = 1 < 2 ≤ 2 k^2`. -/
theorem correctedGamma_pos (η : ℝ) (hηlo : 305 / 1000 < η) (hηhi : η < 312 / 1000)
    (k : ℕ) (hk : 1 ≤ k) : 0 < correctedGamma η k := by
  have hcond := correctedGamma_cond η hηlo hηhi k hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkp1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    have hn : (0 : ℕ) < k + 1 := Nat.succ_pos k
    exact_mod_cast hn
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hk1]
  by_contra hle
  push Not at hle
  have hexp : Real.exp (2 * correctedGamma η k * ((k + 1 : ℕ) : ℝ)) ≤ 1 := by
    have h2γ : 2 * correctedGamma η k ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hle
    have hnonpos : 2 * correctedGamma η k * ((k + 1 : ℕ) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h2γ hkp1.le
    have := Real.exp_le_exp.mpr hnonpos
    rwa [Real.exp_zero] at this
  linarith

/-- The explicit size condition at the corrected exponent (the `hlarge` input): with
`gammaReq η k ≤ correctedGamma η k` and the log-ratio numeric hypothesis
`k * log (312/1000 / η) ≤ 3 * log 2`, the size condition holds. The numeric hypothesis is
exactly the slack of the threshold exponent against the `1 / k` coefficient decay demanded
by Lemma 5 at the printed constant `312/1000`. -/
theorem correctedGamma_large (η : ℝ) (hηlo : 305 / 1000 < η) (hηhi : η < 312 / 1000)
    (k : ℕ) (hk : 1 ≤ k)
    (hnum : (k : ℝ) * Real.log (312 / 1000 / η) ≤ 3 * Real.log 2) :
    (5 / 2 : ℝ) * Real.log (k : ℝ) + (1 / 2 : ℝ) * Real.log 2 ≤
      2 * (k : ℝ) * (correctedGamma η k - (1 + Real.log (312 / 1000) / 2)) := by
  obtain ⟨_, h4, _⟩ := correctedGamma_node_facts η hηlo hηhi k hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have hn : (0 : ℕ) < k := by omega
    exact_mod_cast hn
  have hkne : ((k : ℝ)) ≠ 0 := ne_of_gt hk0
  have hL : Real.log (2 * ((2 * (k : ℝ)) : ℝ) ^ (5 / 2 : ℝ)) =
      (7 / 2 : ℝ) * Real.log 2 + (5 / 2 : ℝ) * Real.log (k : ℝ) := by
    rw [Real.log_mul (by norm_num : ((2 : ℝ)) ≠ 0) (by positivity),
      Real.log_rpow (by nlinarith : (0 : ℝ) < 2 * (k : ℝ)),
      Real.log_mul (by norm_num) (ne_of_gt hk0)]
    ring
  have hsplit : 2 * (k : ℝ) * gammaReq η k =
      2 * (k : ℝ) + (k : ℝ) * Real.log η + (7 / 2 : ℝ) * Real.log 2 +
        (5 / 2 : ℝ) * Real.log (k : ℝ) := by
    unfold gammaReq
    rw [hL]
    field_simp
    ring
  have hratio : (k : ℝ) * Real.log η - (k : ℝ) * Real.log (312 / 1000) =
      -((k : ℝ) * Real.log (312 / 1000 / η)) := by
    have hd : Real.log (312 / 1000 / η) = Real.log (312 / 1000) - Real.log η :=
      Real.log_div (by positivity) (by positivity)
    rw [hd]
    ring
  have hmono : 2 * (k : ℝ) * gammaReq η k ≤ 2 * (k : ℝ) * correctedGamma η k :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [show 2 * (k : ℝ) * (correctedGamma η k - (1 + Real.log (312 / 1000) / 2)) =
      2 * (k : ℝ) * correctedGamma η k - 2 * (k : ℝ) - (k : ℝ) * Real.log (312 / 1000)
      from by ring]
  linarith [hmono, hsplit, hratio, hnum]

/-- The concrete `k ≤ 91` threshold: uniformly over the η window, the log-ratio hypothesis
of `correctedGamma_large` holds for every `k ≤ 91`. The proof compares
`log (312/1000 / η) ≤ log (312/305)` (from `305/1000 < η`) against the exact integer
inequality `(312/305)^(91:ℕ) ≤ 2^(3:ℕ)`, i.e. `91 * log (312/305) ≤ 3 * log 2`. -/
theorem correctedGamma_large_of_k_le_91 (η : ℝ) (hηlo : 305 / 1000 < η)
    (hηhi : η < 312 / 1000) (k : ℕ) (hk91 : k ≤ 91) :
    (k : ℝ) * Real.log (312 / 1000 / η) ≤ 3 * Real.log 2 := by
  have hηpos : (0 : ℝ) < η := by positivity
  have hone : (1 : ℝ) ≤ 312 / 1000 / η := by
    rw [le_div_iff₀ hηpos]
    simpa using hηhi.le
  have hnn : (0 : ℝ) ≤ Real.log (312 / 1000 / η) := Real.log_nonneg hone
  have hmonoη : Real.log (312 / 1000 / η) ≤ Real.log (312 / 305) := by
    have hle : 312 / 1000 / η ≤ 312 / 305 := by
      rw [div_le_div_iff₀ hηpos (by norm_num : (0 : ℝ) < 305)]
      have hstep : (312 / 1000) * (305 : ℝ) = (305 / 1000) * 312 := by norm_num
      have hη312 := mul_le_mul_of_nonneg_right hηlo.le (by norm_num : (0 : ℝ) ≤ 312)
      linarith
    exact Real.log_le_log (div_pos (by norm_num : (0 : ℝ) < 312 / 1000) hηpos) hle
  have h91 : (91 : ℝ) * Real.log (312 / 305) ≤ 3 * Real.log 2 := by
    have hkey : Real.log ((312 / 305 : ℝ) ^ (91 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (3 : ℕ)) := by
      refine Real.log_le_log (by positivity) ?_
      have hnat : (312 : ℕ) ^ 91 ≤ 2 ^ 3 * (305 : ℕ) ^ 91 := by decide
      have hle : (312 : ℝ) ^ (91 : ℕ) ≤ (2 : ℝ) ^ (3 : ℕ) * (305 : ℝ) ^ (91 : ℕ) := by
        exact_mod_cast hnat
      rw [div_pow, div_le_iff₀ (show (0 : ℝ) < (305 : ℝ) ^ (91 : ℕ) by positivity)]
      exact hle
    rw [Real.log_pow, Real.log_pow] at hkey
    simpa using hkey
  have hk91' : (k : ℝ) ≤ 91 := by exact_mod_cast hk91
  calc (k : ℝ) * Real.log (312 / 1000 / η)
      ≤ (91 : ℝ) * Real.log (312 / 1000 / η) :=
        mul_le_mul_of_nonneg_right hk91' hnn
    _ ≤ (91 : ℝ) * Real.log (312 / 305) :=
        mul_le_mul_of_nonneg_left hmonoη (by norm_num)
    _ ≤ 3 * Real.log 2 := h91

/-- The Lemma-8 coefficient input at the rounded node: within the η window and under the
concrete size threshold `k ≤ 91`, every Definition-1 coefficient of the rounded-node
multiproduct is bounded by `2` — the `hC : |C_q| ≤ 2` hypothesis of
`Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma8Bound.lemma8_multiproduct_bound`, with `C := mCoeff` at the rounded
terminal node. -/
theorem mCoeff_abs_le_two_of_lemma12 (k : ℕ) (hk : 1 ≤ k) (η : ℝ)
    (hηlo : 305 / 1000 < η) (hηhi : η < 312 / 1000) (hk91 : k ≤ 91) :
    ∀ q : Fin (k + 1), |mCoeff k ((integerNode η k : ℤ) : ℝ) q| ≤ 2 := by
  have hmain := mCoeff_abs_le_two k hk (correctedGamma η k)
    (correctedGamma_pos η hηlo hηhi k hk)
    (correctedGamma_cond η hηlo hηhi k hk)
    (correctedGamma_large η hηlo hηhi k hk
      (correctedGamma_large_of_k_le_91 η hηlo hηhi k hk91))
  have h3 := (correctedGamma_node_facts η hηlo hηhi k hk).1
  rwa [h3] at hmain

/-- The conditional final multiproduct bound with every hypothesis side derived: under the
Lemma-12 η window and the concrete size threshold `k ≤ 91` (with `s + 1 ≤ k`), the
Definition-1 multiproduct over the actual Suzuki node words with the rounded terminal node
obeys the first-Richardson-row bound with constant `2 (k + 1)` and the explicit derived
tail. The terminal-node rounding is the `integerNode` bridge, the defect expansion
is the derived derived first-row expansion, and the `hγ`/`hcond`/`hlarge` conditions at
`correctedGamma` are the numerical implications above. -/
theorem suzuki_multiproduct_lemma12_boost (hs : List (Matrix I I ℂ)) (s k : ℕ)
    (hk : 1 ≤ k) (hsk : s + 1 ≤ k) (η : ℝ) (hηlo : 305 / 1000 < η) (hηhi : η < 312 / 1000)
    (hk91 : k ≤ 91) (lam : ℝ) :
    let n := (integerNode η k).toNat
    let r : Fin (k + 1) → ℕ := fun q => if (q : ℕ) < k then (q : ℕ) + 1 else n
    ‖(∑ q, mCoeff k ((integerNode η k : ℤ) : ℝ) q • suzukiNode hs s (r q) lam) -
        NormedSpace.exp (lam • hs.sum)‖ ≤
      (2 * ((k : ℝ) + 1)) *
        defectTail (recursiveSuzukiGenerators hs s) hs.sum (s + 1) lam :=
  suzuki_multiproduct_mCoeff_integerNode_boost hs s k hk hsk η
    (correctedGamma_pos η hηlo hηhi k hk)
    (correctedGamma_cond η hηlo hηhi k hk)
    (correctedGamma_large η hηlo hηhi k hk
      (correctedGamma_large_of_k_le_91 η hηlo hηhi k hk91)) lam

end

end Qatlib.Papers.HamLCUSim12.MultiproductFormula
