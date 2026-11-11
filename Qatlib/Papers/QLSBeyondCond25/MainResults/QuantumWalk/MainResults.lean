/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper layer for *A New Quantum Algorithm for Linear Systems beyond the Condition Number*
(QLSBeyondCond25), fixed source version arXiv:2510.05588v3.

Section 3 of the paper builds a quantum walk `U_AB = (2Π_A - I)(2Π_B - I)` from two families
of star states and proves the three hypotheses of the phase-estimation Lemma 3.4:

* Lemma 3.6 (page 16, initial state decomposition):
  `|Φ_b⟩ = (1/√(1+pᵀb))|θ*⟩ - (I-Π_A)|p_B⟩`.
* Lemma 3.7 (page 17, fixed-point condition): `U_AB |θ*⟩ = |θ*⟩`.
* Lemma 3.8 (page 18, projection property): `Π_B |p_B⟩ = |p_B⟩`.

We formalise the *abstract* algebraic content of these three lemmas: an inner product space
`E` carrying orthonormal families `Ψ : M → E`, `Φ : N → E` and a unit vector `Φ_b`, together
with the cross inner products `⟨Ψ_i, Φ_j⟩ = A_ij/σ_i` and `⟨Ψ_i, Φ_b⟩ = -b_i/σ_i` that the
paper derives from Definitions 3.2/3.3 (there `σ_i = √d_{u_i}`).  The graph-level derivation
of these cross inner products is Definitions 3.2/3.3 themselves; the three lemmas only use
the resulting inner products.

All declarations below are proved outright; no trusted assumptions are added.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace

namespace Qatlib.Papers.QLSBeyondCond25.MainResults.QuantumWalk

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

/-! ## The two reflection unitaries of Eq. (8) -/

/-- Paper Eq. (7): the projector `Π_B = Σ_i |Ψ_i⟩⟨Ψ_i|` onto the row-star subspace `B`. -/
def projB (Ψ : M → E) (w : E) : E := ∑ i, ⟪Ψ i, w⟫_ℝ • Ψ i

/-- The complement projector `I - Π_A = Σ_j |Φ_j⟩⟨Φ_j| + |Φ_b⟩⟨Φ_b|` (paper Eq. (6)). -/
def projKC (Φ : N → E) (Φb : E) (w : E) : E :=
  (∑ j, ⟪Φ j, w⟫_ℝ • Φ j) + ⟪Φb, w⟫_ℝ • Φb

/-- Paper Eq. (6): the projector `Π_A = I - Σ_j |Φ_j⟩⟨Φ_j| - |Φ_b⟩⟨Φ_b|`. -/
def projA (Φ : N → E) (Φb : E) (w : E) : E := w - projKC Φ Φb w

/-- The reflection `2Π_B - I` appearing in Eq. (8). -/
def reflB (Ψ : M → E) (w : E) : E := (2 : ℝ) • projB Ψ w - w

/-- The reflection `2Π_A - I` appearing in Eq. (8). -/
def reflA (Φ : N → E) (Φb : E) (w : E) : E := (2 : ℝ) • projA Φ Φb w - w

/-- Paper Eq. (8): `U_AB = (2Π_A - I)(2Π_B - I)`. -/
def UAB (Φ : N → E) (Φb : E) (Ψ : M → E) (w : E) : E :=
  reflA Φ Φb (reflB Ψ w)

/-- Paper Eq. (10): `|θ*⟩ = (1/√(1+pᵀb))(Σ_j y_j |Φ_j⟩ + |Φ_b⟩)`. -/
def thetaStar (Φ : N → E) (Φb : E) (y : N → ℝ) (pb : ℝ) : E :=
  (Real.sqrt (1 + pb))⁻¹ • ((∑ j, y j • Φ j) + Φb)

/-- Paper Eq. (11): `|p_B⟩ = (1+pᵀb)⁻¹ Σ_i p_i √d_{u_i} |Ψ_i⟩` with `σ_i = √d_{u_i}`. -/
def pBVector (Ψ : M → E) (σ p : M → ℝ) (pb : ℝ) : E :=
  (1 / (1 + pb)) • ∑ i, (p i * σ i) • Ψ i

/-- Summation helper: `∑ x, f x * (if a = x then 1 else 0) = f a`. -/
theorem sum_mul_ite_eq' {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (a : α) :
    (∑ x, f x * (if a = x then (1 : ℝ) else 0)) = f a := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [show a ≠ b from fun h => hb h.symm]
  · intro ha
    simp at ha

/-! ## Orthogonal projection lemmas -/

/-- An orthonormal family defines an idempotent projection (used for `Π_B`). -/
theorem projB_idem {Ψ : M → E}
    (hΨ : ∀ i i', ⟪Ψ i, Ψ i'⟫_ℝ = if i = i' then (1 : ℝ) else 0) (w : E) :
    projB Ψ (projB Ψ w) = projB Ψ w := by
  simp only [projB, inner_sum, inner_smul_right, hΨ]
  exact Finset.sum_congr rfl fun x _ => by rw [sum_mul_ite_eq']

/-- An orthonormal family together with a unit vector orthogonal to it defines an idempotent
projection (used for `I - Π_A`, paper Eq. (6)). -/
theorem projKC_idem {Φ : N → E} {Φb : E}
    (hΦ : ∀ j j', ⟪Φ j, Φ j'⟫_ℝ = if j = j' then (1 : ℝ) else 0)
    (hΦb : ⟪Φb, Φb⟫_ℝ = 1)
    (hb : ∀ j, ⟪Φ j, Φb⟫_ℝ = 0) (w : E) :
    projKC Φ Φb (projKC Φ Φb w) = projKC Φ Φb w := by
  have hb' : ∀ j, ⟪Φb, Φ j⟫_ℝ = 0 := by
    intro j
    rw [real_inner_comm, hb j]
  have hnorm : ‖Φb‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hΦb
  have h1 : ∀ j, ⟪Φ j, (∑ j', ⟪Φ j', w⟫_ℝ • Φ j') + ⟪Φb, w⟫_ℝ • Φb⟫_ℝ
      = ⟪Φ j, w⟫_ℝ := by
    intro j
    simp only [inner_add_right, inner_sum, inner_smul_right, hΦ, hb]
    rw [sum_mul_ite_eq']
    simp
  have h2 : ⟪Φb, (∑ j', ⟪Φ j', w⟫_ℝ • Φ j') + ⟪Φb, w⟫_ℝ • Φb⟫_ℝ
      = ⟪Φb, w⟫_ℝ := by
    simp [inner_add_right, inner_sum, inner_smul_right, hb', hΦb, hnorm]
  simp only [projKC, h1, h2]

/-- `Π_B` fixes every vector of the star-state subspace `B` (used in Lemma 3.8). -/
theorem projB_sum {Ψ : M → E}
    (hΨ : ∀ i i', ⟪Ψ i, Ψ i'⟫_ℝ = if i = i' then (1 : ℝ) else 0)
    (a : M → ℝ) :
    projB Ψ (∑ i, a i • Ψ i) = ∑ i, a i • Ψ i := by
  have h : ∀ i, ⟪Ψ i, ∑ i', a i' • Ψ i'⟫_ℝ = a i := by
    intro i
    simp only [inner_sum, inner_smul_right, hΨ]
    exact sum_mul_ite_eq' a i
  simp only [projB, h]

/-! ## Lemma 3.8: projection property -/

/-- Lemma 3.8 (paper page 18): `Π_B |p_B⟩ = |p_B⟩`.  `|p_B⟩` is by construction a linear
combination of the row star states spanning `B` (Eq. (11)), so the orthogonal projector `Π_B`
fixes it. -/
theorem lemma38_projection_property {Ψ : M → E}
    (hΨ : ∀ i i', ⟪Ψ i, Ψ i'⟫_ℝ = if i = i' then (1 : ℝ) else 0)
    (p σ : M → ℝ) (pb : ℝ) :
    projB Ψ (pBVector Ψ σ p pb) = pBVector Ψ σ p pb := by
  unfold pBVector
  rw [show (1 / (1 + pb)) • ∑ i, (p i * σ i) • Ψ i
      = ∑ i, ((1 / (1 + pb)) * (p i * σ i)) • Ψ i from by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]]
  exact projB_sum hΨ _

/-! ## Lemma 3.6: initial state decomposition -/

/-- Scalar identity used in the proof of Lemma 3.6: `(√x)⁻¹ · (√x)⁻¹ = x⁻¹`. -/
theorem inv_sqrt_mul_inv_sqrt {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = x⁻¹ := by
  rw [← _root_.mul_inv_rev, Real.mul_self_sqrt (le_of_lt hx)]

/-- Lemma 3.6 (paper page 16, initial state decomposition):
`|Φ_b⟩ = (1/√(1+pᵀb))|θ*⟩ - (I-Π_A)|p_B⟩`.

The proof follows the paper: expanding `(I-Π_A)|p_B⟩` in the column star basis gives
`⟨Φ_j, p_B⟩ = y_j/(1+pᵀb)` and `⟨Φ_b, p_B⟩ = -(pᵀb)/(1+pᵀb)` (here `pᵀb = ‖y‖₂²` follows from
`Aᵀp = y` and `Ay = b`), and the two appearances of `Σ_j y_j|Φ_j⟩` cancel. -/
theorem lemma36_initial_state_decomposition
    {Φ : N → E} {Φb : E} {Ψ : M → E} {A : Matrix M N ℝ} {b : M → ℝ} {y : N → ℝ}
    {p σ : M → ℝ}
    (hΦ : ∀ j j', ⟪Φ j, Φ j'⟫_ℝ = if j = j' then (1 : ℝ) else 0)
    (hΦb : ⟪Φb, Φb⟫_ℝ = 1)
    (hb : ∀ j, ⟪Φ j, Φb⟫_ℝ = 0)
    (hcross : ∀ i j, ⟪Φ j, Ψ i⟫_ℝ = A i j / σ i)
    (hcrossb : ∀ i, ⟪Φb, Ψ i⟫_ℝ = -b i / σ i)
    (hσ : ∀ i, σ i ≠ 0) (hy : A *ᵥ y = b) (hp : Aᵀ *ᵥ p = y) :
    Φb = (Real.sqrt (1 + p ⬝ᵥ b))⁻¹ • thetaStar Φ Φb y (p ⬝ᵥ b)
      - projKC Φ Φb (pBVector Ψ σ p (p ⬝ᵥ b)) := by
  -- `p ⬝ᵥ b = y ⬝ᵥ y ≥ 0`
  have hpb_eq : p ⬝ᵥ b = y ⬝ᵥ y := by
    calc p ⬝ᵥ b = p ⬝ᵥ (A *ᵥ y) := by rw [hy]
      _ = (p ᵥ* A) ⬝ᵥ y := dotProduct_mulVec p A y
      _ = (Aᵀ *ᵥ p) ⬝ᵥ y := by
        rw [show p ᵥ* A = Aᵀ *ᵥ p from by
          funext j
          simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]]
      _ = y ⬝ᵥ y := by rw [hp]
  have hpb_nonneg : 0 ≤ p ⬝ᵥ b := by
    rw [hpb_eq]
    simpa using dotProduct_star_self_nonneg (v := y)
  have hpos : 0 < 1 + p ⬝ᵥ b := by linarith
  have hd : (1 : ℝ) / (1 + p ⬝ᵥ b) * (1 + p ⬝ᵥ b) = 1 :=
    div_mul_cancel₀ 1 (ne_of_gt hpos)
  -- `Σ_i (p_i σ_i) * (A_ij/σ_i) = (Aᵀ p)_j = y_j`
  have hsumj : ∀ j, (∑ i, (p i * σ i) * (A i j / σ i)) = y j := by
    intro j
    have hcongr : (∑ i, (p i * σ i) * (A i j / σ i)) = ∑ i, A i j * p i := by
      exact Finset.sum_congr rfl fun i _ => by
        have hne : σ i ≠ 0 := hσ i
        field_simp
    rw [hcongr]
    have := congrFun hp j
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
  -- inner product `⟨Φ_j, p_B⟩ = y_j/(1+pᵀb)`
  have hpB_j : ∀ j, ⟪Φ j, pBVector Ψ σ p (p ⬝ᵥ b)⟫_ℝ = y j / (1 + p ⬝ᵥ b) := by
    intro j
    simp only [pBVector, inner_smul_right, inner_sum, inner_smul_right, hcross, hsumj]
    ring
  -- inner product `⟨Φ_b, p_B⟩ = -(pᵀb)/(1+pᵀb)`
  have hpB_b : ⟪Φb, pBVector Ψ σ p (p ⬝ᵥ b)⟫_ℝ
      = -(p ⬝ᵥ b) / (1 + p ⬝ᵥ b) := by
    have hb0 : (∑ i, (p i * σ i) * (-b i / σ i)) = -(p ⬝ᵥ b) := by
      have hcongr : (∑ i, (p i * σ i) * (-b i / σ i)) = ∑ i, (-b i) * p i := by
        exact Finset.sum_congr rfl fun i _ => by
          have hne : σ i ≠ 0 := hσ i
          field_simp
      rw [hcongr]
      rw [show p ⬝ᵥ b = ∑ i, p i * b i from rfl]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [pBVector, inner_smul_right, inner_sum, inner_smul_right, hcrossb, hb0]
    ring
  -- evaluate `(I - Π_A)|p_B⟩`
  have hproj : projKC Φ Φb (pBVector Ψ σ p (p ⬝ᵥ b))
      = (1 / (1 + p ⬝ᵥ b)) • (∑ j, y j • Φ j) - ((p ⬝ᵥ b) / (1 + p ⬝ᵥ b)) • Φb := by
    have hS : (∑ j, (y j / (1 + p ⬝ᵥ b)) • Φ j)
        = (1 / (1 + p ⬝ᵥ b)) • (∑ j, y j • Φ j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      ring
    have hB : (-(p ⬝ᵥ b) / (1 + p ⬝ᵥ b)) • Φb
        = -((p ⬝ᵥ b) / (1 + p ⬝ᵥ b)) • Φb := by
      rw [neg_div, neg_smul]
    simp only [projKC, hpB_j, hpB_b, hS, hB]
    rw [sub_eq_add_neg, neg_smul]
  rw [hproj]
  -- combine the two `Φ_b` coefficients: `1/(1+pᵀb) + pᵀb/(1+pᵀb) = 1`
  have hcoef : (1 / (1 + p ⬝ᵥ b)) + (p ⬝ᵥ b) / (1 + p ⬝ᵥ b) = 1 := by
    have hne : (1 + p ⬝ᵥ b) ≠ 0 := ne_of_gt hpos
    rw [← add_div, div_self hne]
  have hc2 : (Real.sqrt (1 + p ⬝ᵥ b))⁻¹ * (Real.sqrt (1 + p ⬝ᵥ b))⁻¹
      = 1 / (1 + p ⬝ᵥ b) := by
    rw [inv_sqrt_mul_inv_sqrt hpos, one_div]
  have hTT : ∀ X : E, (Real.sqrt (1 + p ⬝ᵥ b))⁻¹ •
      ((Real.sqrt (1 + p ⬝ᵥ b))⁻¹ • X) = (1 / (1 + p ⬝ᵥ b)) • X := by
    intro X
    rw [smul_smul, hc2]
  rw [thetaStar, hTT]
  have hstep : (1 / (1 + p ⬝ᵥ b)) • ((∑ j, y j • Φ j) + Φb)
        - ((1 / (1 + p ⬝ᵥ b)) • (∑ j, y j • Φ j) - ((p ⬝ᵥ b) / (1 + p ⬝ᵥ b)) • Φb)
      = ((1 / (1 + p ⬝ᵥ b)) + (p ⬝ᵥ b) / (1 + p ⬝ᵥ b)) • Φb := by
    module
  rw [hstep, hcoef, one_smul]

/-! ## Lemma 3.7: fixed-point condition -/

/-- `Π_A |θ*⟩ = 0`, i.e. `(I - Π_A)|θ*⟩ = |θ*⟩`: the state `|θ*⟩` lies in the span of the
column star states (paper page 17, first step of the proof of Lemma 3.7). -/
theorem projKC_thetaStar {Φ : N → E} {Φb : E} {y : N → ℝ} {pb : ℝ}
    (hΦ : ∀ j j', ⟪Φ j, Φ j'⟫_ℝ = if j = j' then (1 : ℝ) else 0)
    (hΦb : ⟪Φb, Φb⟫_ℝ = 1)
    (hb : ∀ j, ⟪Φ j, Φb⟫_ℝ = 0) :
    projKC Φ Φb (thetaStar Φ Φb y pb) = thetaStar Φ Φb y pb := by
  have hb' : ∀ j, ⟪Φb, Φ j⟫_ℝ = 0 := by
    intro j
    rw [real_inner_comm, hb j]
  have h1 : ∀ j, ⟪Φ j, thetaStar Φ Φb y pb⟫_ℝ
      = (Real.sqrt (1 + pb))⁻¹ * y j := by
    intro j
    have hsum : (∑ j', y j' * (if j = j' then (1 : ℝ) else 0)) = y j :=
      sum_mul_ite_eq' y j
    simp only [thetaStar, inner_smul_right, inner_add_right, inner_sum, inner_smul_right,
      hΦ, hb]
    rw [hsum]
    ring
  have h2 : ⟪Φb, thetaStar Φ Φb y pb⟫_ℝ = (Real.sqrt (1 + pb))⁻¹ := by
    simp only [thetaStar, inner_smul_right, inner_add_right, inner_sum, inner_smul_right,
      hb', hΦb]
    simp
  simp only [projKC, h1, h2]
  rw [thetaStar, smul_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]

/-- `Π_B |θ*⟩ = 0`: this is the paper's computation on page 17, using
`⟨Ψ_i, Φ_j⟩ = A_ij/σ_i`, `⟨Ψ_i, Φ_b⟩ = -b_i/σ_i` and `A y = b`. -/
theorem projB_thetaStar {Φ : N → E} {Φb : E} {Ψ : M → E} {A : Matrix M N ℝ}
    {b : M → ℝ} {y : N → ℝ} {p σ : M → ℝ}
    (hcross : ∀ i j, ⟪Ψ i, Φ j⟫_ℝ = A i j / σ i)
    (hcrossb : ∀ i, ⟪Ψ i, Φb⟫_ℝ = -b i / σ i)
    (hσ : ∀ i, σ i ≠ 0) (hy : A *ᵥ y = b) :
    projB Ψ (thetaStar Φ Φb y (p ⬝ᵥ b)) = 0 := by
  have hzero : ∀ i, ⟪Ψ i, thetaStar Φ Φb y (p ⬝ᵥ b)⟫_ℝ = 0 := by
    intro i
    have hAy : (∑ j, y j * A i j) = b i := by
      have h := congrFun hy i
      rw [Matrix.mulVec, dotProduct] at h
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => mul_comm (y j) (A i j)
    have hsum : (∑ j, y j * (A i j / σ i)) = b i / σ i := by
      rw [← hAy, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
    simp only [thetaStar, inner_smul_right, inner_add_right, inner_sum, inner_smul_right,
      hcross, hcrossb]
    rw [hsum, show (-b i / σ i) = -(b i / σ i) from by rw [neg_div]]
    rw [add_neg_cancel, mul_zero]
  simp only [projB, hzero, zero_smul, Finset.sum_const_zero]

/-- Lemma 3.7 (paper page 17, fixed-point condition): `U_AB |θ*⟩ = |θ*⟩`.

The proof follows the paper: `Π_B|θ*⟩ = 0` (computed above from `Ay = b`) and
`Π_A|θ*⟩ = 0` (because `|θ*⟩` lies in the span of the column star states), hence
`U_AB|θ*⟩ = (2Π_A - I)(2Π_B - I)|θ*⟩ = (-I)(-I)|θ*⟩ = |θ*⟩`. -/
theorem lemma37_fixed_point {Φ : N → E} {Φb : E} {Ψ : M → E} {A : Matrix M N ℝ}
    {b : M → ℝ} {y : N → ℝ} {p σ : M → ℝ}
    (hΦ : ∀ j j', ⟪Φ j, Φ j'⟫_ℝ = if j = j' then (1 : ℝ) else 0)
    (hΦb : ⟪Φb, Φb⟫_ℝ = 1)
    (hb : ∀ j, ⟪Φ j, Φb⟫_ℝ = 0)
    (hcross : ∀ i j, ⟪Ψ i, Φ j⟫_ℝ = A i j / σ i)
    (hcrossb : ∀ i, ⟪Ψ i, Φb⟫_ℝ = -b i / σ i)
    (hσ : ∀ i, σ i ≠ 0) (hy : A *ᵥ y = b) :
    UAB Φ Φb Ψ (thetaStar Φ Φb y (p ⬝ᵥ b)) = thetaStar Φ Φb y (p ⬝ᵥ b) := by
  set ψ := thetaStar Φ Φb y (p ⬝ᵥ b) with hψ
  have hB : projB Ψ ψ = 0 := projB_thetaStar hcross hcrossb hσ hy
  have hA : projA Φ Φb ψ = 0 := by
    rw [projA, projKC_thetaStar hΦ hΦb hb, sub_self]
  have hB' : (2 : ℝ) • projB Ψ ψ - ψ = -ψ := by rw [hB]; simp
  have hneg : projA Φ Φb (-ψ) = -projA Φ Φb ψ := by
    simp only [projA, projKC, inner_neg_right, neg_smul, Finset.sum_neg_distrib]
    abel
  have hA' : projA Φ Φb (-ψ) = 0 := by rw [hneg, hA, neg_zero]
  unfold UAB reflA reflB
  rw [hB', hA']
  simp only [smul_zero, zero_sub, neg_neg]

end Qatlib.Papers.QLSBeyondCond25.MainResults.QuantumWalk
