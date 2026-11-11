/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticTraceDistance

set_option backward.isDefEq.respectTransparency false

/-!
# StateHSP24 — Schmidt coefficients, product-state overlap and purity

Bouland–Giurgica-Tiron–Wright, fixed arXiv:2410.12706v1, Section 2.

* **Proposition 1**: the maximum squared overlap of a bipartite pure state with a
  product state equals its largest squared Schmidt coefficient `λ₁`.
* **Corollary 2**: if the state is `ε`-far (in trace distance) from every product
  state then `λ₁ ≤ 1 - ε²`.
* **Proposition 2**: under the same promise the purity of the reduced state is at
  most `1 - ε²`.

The representation bridge uses the actual coefficient matrix
`bipartiteMatrix ψ` and the Gram matrix `gramMatrix ψ = M Mᴴ` of the frozen
`Foundations-ENTANGLEMENT` development, whose eigenvalues `schmidtΛ ψ j` are the
squared Schmidt coefficients.  The trace-distance promise is stated through the
standard pure-state identity `D(ψ, φ)² = 1 - |⟨φ|ψ⟩|²`, formalised as the
definition `pureTraceDistance`; no fidelity theorem is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000

noncomputable section

namespace Qatlib.Papers.StateHSP24.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators ComplexOrder

variable {D E : ℕ}

/-! ## Basic vocabulary -/

/-- Complex conjugation of a pure state. -/
noncomputable def conjState {I : Type*} (ψ : QState I) : QState I := fun i => star (ψ i)

/-- The squared overlap of a (normalized) product state with a bipartite pure state. -/
def productOverlapSq (ψ : QState (Fin D × Fin E)) (a : QState (Fin D))
    (b : QState (Fin E)) : ℝ :=
  ‖Inner (TensorState a b) ψ‖ ^ 2

/-- The largest squared Schmidt coefficient `λ₁` of a bipartite pure state, read
from the Gram spectrum (Mathlib eigenvalues are not ordered, hence the supremum). -/
def schmidtCoeffMax (ψ : QState (Fin D × Fin E)) : ℝ :=
  ⨆ j, schmidtΛ ψ j

/-- The purity `Tr(ρ²)` of a finite matrix, as a real number. -/
def purity {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (ρ * ρ)).re

/-- The actual trace distance between normalized pure states, in terms of the
overlap: `D(ψ, φ) = sqrt (1 - |⟨φ|ψ⟩|²)`.  This is the paper's equation (4). -/
def pureTraceDistance {I : Type*} [Fintype I] (φ ψ : QState I) : ℝ :=
  Real.sqrt (1 - ‖Inner φ ψ‖ ^ 2)

/-- The paper's `ε`-far promise, expressed through the actual pure-state trace
distance to every normalized product state. -/
def FarFromProduct (ψ : QState (Fin D × Fin E)) (ε : ℝ) : Prop :=
  ∀ a b, Normalized a → Normalized b → ε ≤ pureTraceDistance (TensorState a b) ψ

/-! ## Inner products against coefficient matrices -/

/-- Overlap of a product state with a bipartite state, through the coefficient
matrix: `⟨a⊗b|ψ⟩ = ⟨a| M (conj b)⟩`. -/
theorem inner_tensorState_eq (a : QState (Fin D)) (b : QState (Fin E))
    (ψ : QState (Fin D × Fin E)) :
    Inner (TensorState a b) ψ = Inner a (bipartiteMatrix ψ *ᵥ conjState b) := by
  change (∑ p, star ((TensorState a b) p) * ψ p) =
    ∑ i, star (a i) * (∑ j, (bipartiteMatrix ψ) i j * conjState b j)
  simp only [TensorState, bipartiteMatrix, Matrix.of_apply, conjState, star_mul,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Adjoint identity for the coefficient matrix: `⟨Mᴴx|y⟩ = ⟨x|My⟩`. -/
theorem inner_conjTranspose_mulVec_left (M : Matrix (Fin D) (Fin E) ℂ)
    (x : QState (Fin D)) (y : QState (Fin E)) :
    Inner ((Mᴴ) *ᵥ x) y = Inner x (M *ᵥ y) := by
  change (∑ i, star (∑ j, (Mᴴ) i j * x j) * y i) =
    ∑ i, star (x i) * (∑ j, M i j * y j)
  simp only [Matrix.conjTranspose_apply, star_sum, star_mul, star_star]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The inner product against the zero state vanishes. -/
theorem inner_zero_right {I : Type*} [Fintype I] (x : QState I) :
    Inner x (0 : QState I) = 0 := by
  change (∑ i, star (x i) * (0 : ℂ)) = 0
  simp

/-- The inner product is additive in its second argument over a finite sum. -/
theorem inner_finset_sum_right {I ι : Type*} [Fintype I] (x : QState I)
    (s : Finset ι) (f : ι → QState I) :
    Inner x (∑ i ∈ s, f i) = ∑ i ∈ s, Inner x (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · exact inner_zero_right x
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Qatlib.Concepts.FiniteLocc.LOCCProgram.inner_add_right, ih]

/-- The inner product is additive in its second argument over `Finset.univ`. -/
theorem inner_sum_right {I ι : Type*} [Fintype I] [Fintype ι] (x : QState I)
    (f : ι → QState I) :
    Inner x (∑ i, f i) = ∑ i, Inner x (f i) := by
  simpa using inner_finset_sum_right x (Finset.univ : Finset ι) f

/-- The quadratic form of an outer product is the squared overlap. -/
theorem inner_outerProduct_mulVec_self {d : ℕ} (u x : QState (Fin d)) :
    Inner x ((outerProduct u) *ᵥ x) = ((‖Inner u x‖ ^ 2 : ℝ) : ℂ) := by
  rw [outerProduct_mulVec,
    Qatlib.Concepts.FiniteLocc.LOCCProgram.inner_smul_right,
    ← star_inner u x, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ## Cauchy–Schwarz for the finite inner product -/

/-- Cauchy–Schwarz for the concrete finite-dimensional inner product. -/
theorem inner_normSq_le {I : Type*} [Fintype I] (x y : QState I) :
    ‖Inner x y‖ ^ 2 ≤ (∑ i, ‖x i‖ ^ 2) * (∑ i, ‖y i‖ ^ 2) := by
  have htri : ‖Inner x y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    change ‖∑ i, star (x i) * y i‖ ≤ ∑ i, ‖x i‖ * ‖y i‖
    calc ‖∑ i, star (x i) * y i‖ ≤ ∑ i, ‖star (x i) * y i‖ := norm_sum_le _ _
      _ = ∑ i, ‖x i‖ * ‖y i‖ := by simp
  have hcs : ∑ i, ‖x i‖ * ‖y i‖ ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
    simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖x i‖) (fun i => ‖y i‖)
  have hle : ‖Inner x y‖ ≤
      Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ i, ‖y i‖ ^ 2) := le_trans htri hcs
  have hA : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : 0 ≤ ∑ i, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc ‖Inner x y‖ ^ 2
      ≤ (Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ i, ‖y i‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = (∑ i, ‖x i‖ ^ 2) * (∑ i, ‖y i‖ ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- Normalized vectors have squared overlap at most one. -/
theorem inner_normSq_le_one {I : Type*} [Fintype I] (x y : QState I)
    (hx : Normalized x) (hy : Normalized y) :
    ‖Inner x y‖ ^ 2 ≤ 1 := by
  have h := inner_normSq_le x y
  rw [hx, hy, mul_one] at h
  exact h

/-! ## The Gram quadratic form -/

/-- The real quadratic form `Re ⟨x|Gx⟩` of a Gram matrix. -/
def quadForm (G : Matrix (Fin D) (Fin D) ℂ) (x : QState (Fin D)) : ℝ :=
  (Inner x (G *ᵥ x)).re

/-- Expansion of the Gram quadratic form in the Gram eigenbasis. -/
theorem quadForm_gramMatrix (ψ : QState (Fin D × Fin E)) (x : QState (Fin D)) :
    quadForm (gramMatrix ψ) x =
      ∑ j, schmidtΛ ψ j * ‖Inner (schmidtU ψ j) x‖ ^ 2 := by
  rw [quadForm, gramMatrix_eq_sum]
  rw [Qatlib.Concepts.FiniteLocc.LOCCProgram.sum_mulVec]
  rw [inner_sum_right]
  simp_rw [Matrix.smul_mulVec,
    Qatlib.Concepts.FiniteLocc.LOCCProgram.inner_smul_right]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_outerProduct_mulVec_self, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Parseval in the Gram eigenbasis: the squared overlaps with a full orthonormal
Gram eigenbasis sum to the squared norm of the vector. -/
theorem sum_sq_inner_schmidtU (ψ : QState (Fin D × Fin E)) (x : QState (Fin D)) :
    ∑ j, ‖Inner (schmidtU ψ j) x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have hcomplex : (∑ j, ((‖Inner (schmidtU ψ j) x‖ ^ 2 : ℝ) : ℂ)) = Inner x x := by
    rw [show (∑ j, ((‖Inner (schmidtU ψ j) x‖ ^ 2 : ℝ) : ℂ)) =
        ∑ j, Inner x ((outerProduct (schmidtU ψ j)) *ᵥ x) from
      Finset.sum_congr rfl fun j _ =>
        (inner_outerProduct_mulVec_self (schmidtU ψ j) x).symm]
    rw [← inner_sum_right,
      ← Qatlib.Concepts.FiniteLocc.LOCCProgram.sum_mulVec,
      sum_outerProduct_schmidtU, Matrix.one_mulVec]
  rw [inner_self] at hcomplex
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum] at hcomplex
  exact Complex.ofReal_inj.mp hcomplex

/-- Quadratic-form bound by the largest squared Schmidt coefficient. -/
theorem quadForm_gramMatrix_le (ψ : QState (Fin D × Fin E)) (x : QState (Fin D)) :
    quadForm (gramMatrix ψ) x ≤ schmidtCoeffMax ψ * ∑ i, ‖x i‖ ^ 2 := by
  rw [quadForm_gramMatrix]
  have hterm : ∀ j, schmidtΛ ψ j * ‖Inner (schmidtU ψ j) x‖ ^ 2 ≤
      schmidtCoeffMax ψ * ‖Inner (schmidtU ψ j) x‖ ^ 2 := by
    intro j
    exact mul_le_mul_of_nonneg_right
      (le_ciSup (Finite.bddAbove_range _) j) (sq_nonneg _)
  calc ∑ j, schmidtΛ ψ j * ‖Inner (schmidtU ψ j) x‖ ^ 2
      ≤ ∑ j, schmidtCoeffMax ψ * ‖Inner (schmidtU ψ j) x‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = schmidtCoeffMax ψ * ∑ j, ‖Inner (schmidtU ψ j) x‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = schmidtCoeffMax ψ * ∑ i, ‖x i‖ ^ 2 := by rw [sum_sq_inner_schmidtU]

/-! ## Proposition 1: maximum product-state overlap -/

/-- **Proposition 1, upper bound**: every product state has squared overlap at
most `λ₁`. -/
theorem proposition1_product_overlap_le (ψ : QState (Fin D × Fin E))
    (a : QState (Fin D)) (b : QState (Fin E))
    (ha : Normalized a) (hb : Normalized b) :
    productOverlapSq ψ a b ≤ schmidtCoeffMax ψ := by
  have hmass : (∑ i, ‖conjState b i‖ ^ 2) = 1 := by
    simpa [conjState, Normalized] using hb
  have hfirst : (∑ i, ‖(((bipartiteMatrix ψ)ᴴ) *ᵥ a) i‖ ^ 2) =
      quadForm (gramMatrix ψ) a := by
    have hself := inner_self (((bipartiteMatrix ψ)ᴴ) *ᵥ a)
    have hquad : Inner (((bipartiteMatrix ψ)ᴴ) *ᵥ a) (((bipartiteMatrix ψ)ᴴ) *ᵥ a)
        = Inner a (gramMatrix ψ *ᵥ a) := by
      simpa [gramMatrix] using inner_conjTranspose_mulVec (bipartiteMatrix ψ) a a
    have hre : (Inner (((bipartiteMatrix ψ)ᴴ) *ᵥ a) (((bipartiteMatrix ψ)ᴴ) *ᵥ a)).re =
        quadForm (gramMatrix ψ) a := by
      rw [hquad]
      rfl
    have hsumC : ((∑ i, ‖(((bipartiteMatrix ψ)ᴴ) *ᵥ a) i‖ ^ 2 : ℝ) : ℂ) =
        Inner (((bipartiteMatrix ψ)ᴴ) *ᵥ a) (((bipartiteMatrix ψ)ᴴ) *ᵥ a) := by
      rw [Complex.ofReal_sum]
      exact hself.symm
    have hsum : (∑ i, ‖(((bipartiteMatrix ψ)ᴴ) *ᵥ a) i‖ ^ 2) =
        (Inner (((bipartiteMatrix ψ)ᴴ) *ᵥ a) (((bipartiteMatrix ψ)ᴴ) *ᵥ a)).re := by
      rw [← hsumC, Complex.ofReal_re]
    rw [hsum, hre]
  have hcs := inner_normSq_le (((bipartiteMatrix ψ)ᴴ) *ᵥ a) (conjState b)
  have hoverlap : Inner (TensorState a b) ψ =
      Inner (((bipartiteMatrix ψ)ᴴ) *ᵥ a) (conjState b) := by
    rw [inner_tensorState_eq]
    exact (inner_conjTranspose_mulVec_left (bipartiteMatrix ψ) a (conjState b)).symm
  have hstep : productOverlapSq ψ a b ≤ quadForm (gramMatrix ψ) a := by
    rw [productOverlapSq, hoverlap]
    calc ‖Inner (((bipartiteMatrix ψ)ᴴ) *ᵥ a) (conjState b)‖ ^ 2
        ≤ (∑ i, ‖(((bipartiteMatrix ψ)ᴴ) *ᵥ a) i‖ ^ 2) *
            (∑ i, ‖conjState b i‖ ^ 2) := hcs
      _ = quadForm (gramMatrix ψ) a := by rw [hfirst, hmass, mul_one]
  have hquad := quadForm_gramMatrix_le ψ a
  have hamass : (∑ i, ‖a i‖ ^ 2) = 1 := ha
  rw [hamass, mul_one] at hquad
  exact le_trans hstep hquad

/-! ## Attainment of the maximum -/

/-- The maximum is attained by a product state built from a top Gram eigenvector. -/
theorem proposition1_product_overlap_attained (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) :
    ∃ a b, Normalized a ∧ Normalized b ∧
      productOverlapSq ψ a b = schmidtCoeffMax ψ := by
  classical
  haveI : Nonempty (Fin D) := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI := h
    have h0 : (∑ i : Fin D × Fin E, ‖ψ i‖ ^ 2) = 0 := by simp
    change (∑ i : Fin D × Fin E, ‖ψ i‖ ^ 2) = 1 at hψ
    rw [h0] at hψ
    exact zero_ne_one hψ
  -- a top eigenvector exists
  obtain ⟨j0, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun j => schmidtΛ ψ j) Finset.univ_nonempty
  have hsup : schmidtCoeffMax ψ = schmidtΛ ψ j0 := by
    refine le_antisymm ?_ (le_ciSup (Finite.bddAbove_range _) j0)
    exact ciSup_le (fun j => hmax j (Finset.mem_univ j))
  -- the top squared weight is positive
  have htr : Matrix.trace (gramMatrix ψ) = 1 := by
    rw [trace_gramMatrix]
    exact_mod_cast hψ
  have hsum : ∑ j, schmidtΛ ψ j = 1 :=
    sum_eigenvalues_eq_one (gramMatrix ψ) (gramMatrix_posSemidef ψ) htr
  have hpos : 0 < schmidtΛ ψ j0 := by
    have hnonneg : ∀ j, 0 ≤ schmidtΛ ψ j := schmidtΛ_nonneg ψ
    by_contra hle
    have hle' : schmidtΛ ψ j0 ≤ 0 := le_of_not_gt hle
    have hzero : ∀ j, schmidtΛ ψ j = 0 := fun j =>
      le_antisymm (le_trans (hmax j (Finset.mem_univ j)) hle') (hnonneg j)
    have hz : (∑ j, schmidtΛ ψ j) = 0 := by simp [hzero]
    rw [hsum] at hz
    exact zero_ne_one hz.symm
  set s : ℝ := Real.sqrt (schmidtΛ ψ j0) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hpos
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hss : ((s : ℝ) : ℂ) * ((s : ℝ) : ℂ) = ((schmidtΛ ψ j0 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hpos)]
  -- the candidate second factor
  set b : QState (Fin E) := fun j => star (schmidtW ψ j0 j / (s : ℂ)) with hbdef
  have hb : Normalized b := by
    show ∑ j, ‖star (schmidtW ψ j0 j / (s : ℂ))‖ ^ 2 = 1
    have hw : (∑ j, ‖schmidtW ψ j0 j‖ ^ 2) = schmidtΛ ψ j0 := by
      have hinner : ((∑ j, ‖schmidtW ψ j0 j‖ ^ 2 : ℝ) : ℂ) =
          ((schmidtΛ ψ j0 : ℝ) : ℂ) := by
        have hself := inner_self (schmidtW ψ j0)
        rw [Complex.ofReal_sum, ← hself, schmidtW_inner, if_pos rfl]
      exact Complex.ofReal_inj.mp hinner
    calc ∑ j, ‖star (schmidtW ψ j0 j / (s : ℂ))‖ ^ 2
        = ∑ j, ‖schmidtW ψ j0 j‖ ^ 2 / s ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_star, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (le_of_lt hs), div_pow]
      _ = (∑ j, ‖schmidtW ψ j0 j‖ ^ 2) / s ^ 2 := by rw [Finset.sum_div]
      _ = 1 := by
          rw [hw, hsdef, Real.sq_sqrt (le_of_lt hpos), div_self (ne_of_gt hpos)]
  refine ⟨schmidtU ψ j0, b, ?_, hb, ?_⟩
  · have h := schmidtU_inner ψ j0 j0
    rw [if_pos rfl] at h
    have h' : ((∑ i, ‖schmidtU ψ j0 i‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      have hself := inner_self (schmidtU ψ j0)
      rw [Complex.ofReal_sum, ← hself, h]
      norm_num
    exact Complex.ofReal_inj.mp h'
  · -- the overlap is `sqrt λ₁`, whose square is `λ₁`
    have hinner : Inner (TensorState (schmidtU ψ j0) b) ψ = ((s : ℝ) : ℂ) := by
      rw [inner_tensorState_eq]
      have hcb : conjState b = fun j => schmidtW ψ j0 j / (s : ℂ) := by
        funext j
        simp [conjState, b]
      rw [hcb]
      have hsplit : (fun j => schmidtW ψ j0 j / (s : ℂ)) =
          ((s : ℂ)⁻¹) • (schmidtW ψ j0) := by
        funext j
        simp [div_eq_mul_inv, mul_comm]
      rw [hsplit, Matrix.mulVec_smul, schmidtW, Matrix.mulVec_mulVec, ← gramMatrix,
        schmidtU_mulVec, smul_smul,
        Qatlib.Concepts.FiniteLocc.LOCCProgram.inner_smul_right,
        schmidtU_inner, if_pos rfl, mul_one]
      rw [← hss, ← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
    rw [productOverlapSq, hinner, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hs), hsdef, Real.sq_sqrt (le_of_lt hpos), hsup]

/-! ## Corollary 2 -/

/-- The `ε`-far promise, in the overlap form used by the paper (equation (4)). -/
theorem farFromProduct_iff_overlap (ψ : QState (Fin D × Fin E)) (ε : ℝ)
    (hψ : Normalized ψ) (hε : 0 ≤ ε) :
    FarFromProduct ψ ε ↔
      ∀ a b, Normalized a → Normalized b →
        ‖Inner (TensorState a b) ψ‖ ^ 2 ≤ 1 - ε ^ 2 := by
  constructor
  · intro hfar a b ha hb
    have hd := hfar a b ha hb
    have h1 : 0 ≤ 1 - ‖Inner (TensorState a b) ψ‖ ^ 2 :=
      sub_nonneg.mpr (inner_normSq_le_one (TensorState a b) ψ
        (normalized_tensorState ha hb) hψ)
    have hd' : ε ≤ Real.sqrt (1 - ‖Inner (TensorState a b) ψ‖ ^ 2) := hd
    have := (Real.le_sqrt hε h1).mp hd'
    linarith
  · intro hoverlap a b ha hb
    have h1 : 0 ≤ 1 - ‖Inner (TensorState a b) ψ‖ ^ 2 :=
      sub_nonneg.mpr (inner_normSq_le_one (TensorState a b) ψ
        (normalized_tensorState ha hb) hψ)
    show ε ≤ Real.sqrt (1 - ‖Inner (TensorState a b) ψ‖ ^ 2)
    exact (Real.le_sqrt hε h1).mpr (by linarith [hoverlap a b ha hb])

/-- **Corollary 2**: a state `ε`-far from every product state has largest squared
Schmidt coefficient at most `1 - ε²`. -/
theorem corollary2_schmidtCoeffMax_le (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (ε : ℝ) (hε : 0 ≤ ε) (hfar : FarFromProduct ψ ε) :
    schmidtCoeffMax ψ ≤ 1 - ε ^ 2 := by
  obtain ⟨a, b, ha, hb, hmax⟩ := proposition1_product_overlap_attained ψ hψ
  rw [← hmax]
  exact (farFromProduct_iff_overlap ψ ε hψ hε).mp hfar a b ha hb

/-! ## Proposition 2: purity of the reduced state -/

/-- The reduced state of a bipartite pure state is its Gram matrix. -/
theorem partialTrace_outerProduct_eq_gramMatrix (ψ : QState (Fin D × Fin E)) :
    PartialTrace (outerProduct ψ) = gramMatrix ψ := by
  ext i j
  simp only [PartialTrace, gramMatrix, bipartiteMatrix, outerProduct, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply]

/-- The purity of a spectral combination of orthonormal rank-one projections. -/
theorem trace_sq_spectral {r : ℕ} (a : Fin r → ℝ) (u : Fin r → QState (Fin D))
    (hu : ∀ i j, Inner (u i) (u j) = if i = j then 1 else 0) :
    (Matrix.trace ((∑ i, (a i : ℂ) • outerProduct (u i)) *
      (∑ j, (a j : ℂ) • outerProduct (u j)))).re = ∑ i, a i ^ 2 := by
  have hmul : (∑ i, (a i : ℂ) • outerProduct (u i)) *
      (∑ j, (a j : ℂ) • outerProduct (u j)) =
      ∑ i, ∑ j, ((a i * a j : ℝ) : ℂ) •
        (outerProduct (u i) * outerProduct (u j)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul, ← Complex.ofReal_mul]
  have htrace : ∀ i j : Fin r,
      Matrix.trace (outerProduct (u i) * outerProduct (u j)) =
        if i = j then (1 : ℂ) else 0 := by
    intro i j
    rw [trace_outerProduct_mul_eq_quadratic, outerProduct_mulVec, dotProduct_smul,
      smul_eq_mul]
    have h1 : star (u i) ⬝ᵥ u j = Inner (u i) (u j) := rfl
    rw [h1, hu i j]
    by_cases h : i = j
    · rw [if_pos h, hu j i, if_pos h.symm, one_mul]
    · rw [if_neg h]
      simp
  rw [hmul, Matrix.trace_sum]
  simp only [Matrix.trace_sum, Matrix.trace_smul, htrace]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum, Finset.sum_eq_single i]
  · simp [pow_two]
  · intro j _ hj
    rw [if_neg (Ne.symm hj)]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Proposition 2**: if a bipartite pure state is `ε`-far from every product
state, the purity of its reduced state is at most `1 - ε²`. -/
theorem proposition2_purity_bound (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ)
    (ε : ℝ) (hε : 0 ≤ ε) (hfar : FarFromProduct ψ ε) :
    purity (PartialTrace (outerProduct ψ)) ≤ 1 - ε ^ 2 := by
  have hsum : ∑ j, schmidtΛ ψ j = 1 := by
    have htr : Matrix.trace (gramMatrix ψ) = 1 := by
      rw [trace_gramMatrix]
      exact_mod_cast hψ
    exact sum_eigenvalues_eq_one (gramMatrix ψ) (gramMatrix_posSemidef ψ) htr
  have hp : purity (PartialTrace (outerProduct ψ)) = ∑ j, schmidtΛ ψ j ^ 2 := by
    rw [purity, partialTrace_outerProduct_eq_gramMatrix, gramMatrix_eq_sum]
    exact trace_sq_spectral (fun j => schmidtΛ ψ j) (schmidtU ψ) (schmidtU_inner ψ)
  have hmax := corollary2_schmidtCoeffMax_le ψ hψ ε hε hfar
  rw [hp]
  calc ∑ j, schmidtΛ ψ j ^ 2
      ≤ ∑ j, schmidtCoeffMax ψ * schmidtΛ ψ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hle : schmidtΛ ψ j ≤ schmidtCoeffMax ψ :=
          le_ciSup (Finite.bddAbove_range (fun k : Fin D => schmidtΛ ψ k)) j
        have hnn := schmidtΛ_nonneg ψ j
        nlinarith
    _ = schmidtCoeffMax ψ * ∑ j, schmidtΛ ψ j := by rw [Finset.mul_sum]
    _ = schmidtCoeffMax ψ := by rw [hsum, mul_one]
    _ ≤ 1 - ε ^ 2 := hmax

end Qatlib.Papers.StateHSP24.MainResults
