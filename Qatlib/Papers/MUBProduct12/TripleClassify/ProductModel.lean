/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — product model for `C² ⊗ C³`

Reusable model for McNulty–Weigert, "On the Impossibility to Extend Triples of
Mutually Unbiased Product Bases in Dimension Six", fixed arXiv:1203.6887v2.

The bipartite space `C² ⊗ C³` is represented on the product index type
`Fin 2 × Fin 3`, using the shared tensor-state interface
`QuantumAlgorithm.Concepts.MbqcFlow.FlowDecision.TensorState`.  A *product state*
is `TensorState φ Φ`, with amplitude `(φ ⊗ Φ)(i,j) = φ i * Φ j`; the inner product
is the shared `Inner` from `FlowDecision.Qubit`.

This file supplies only the algebraic backbone used by Lemmas 1–4: the tensor
factorization of overlaps, the Parseval identity associated with an orthonormal
product basis (completeness), and an elementary real pinning lemma.  No paper
claim is stated here.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

open Qatlib.Foundations.PureStateMath

/-- Qubit factor `C²` of the bipartite model. -/
abbrev C2State := QState (Fin 2)

/-- Qutrit factor `C³` of the bipartite model. -/
abbrev C3State := QState (Fin 3)

/-- The six product vectors `ψ k ⊗ Ψ k` form an orthonormal product basis of
`C² ⊗ C³`: each factor is normalized and the family is complete, encoded by the
resolution of identity `Inner u v = ∑ k, ⟨u|b_k⟩⟨b_k|v⟩`.

This is the exact content of "product basis" in Lemma 4 (arXiv:1203.6887v2, p. 8):
six unit product vectors whose span is the whole six-dimensional space. -/
def IsProductBasis (ψ : Fin 6 → C2State) (Ψ : Fin 6 → C3State) : Prop :=
  (∀ k, Normalized (ψ k)) ∧
  (∀ k, Normalized (Ψ k)) ∧
  (∀ u v : QState (Fin 2 × Fin 3),
    Inner u v = ∑ k, Inner u (TensorState (ψ k) (Ψ k)) *
      Inner (TensorState (ψ k) (Ψ k)) v)

/-- The paper's `|j_a⟩ ∈ C²` and `|J_A⟩ ∈ C³` product vector `|j_a, J_A⟩`. -/
abbrev productKet (j : Fin 2) (J : Fin 3) : QState (Fin 2 × Fin 3) :=
  TensorState (Ket j) (Ket J)

/-- A computational basis bra extracts the corresponding amplitude
(`⟨i|ψ⟩ = ψ i`), for any finite index type. -/
theorem inner_ket_eq {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (ψ : QState I) : Inner (Ket i) ψ = ψ i := by
  rw [inner_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ket, hj]
  · simp

/-- **Tensor factorization of overlaps** (arXiv:1203.6887v2, Lemma 4, p. 8):
`⟨φ ⊗ Φ | ψ ⊗ Ψ⟩ = ⟨φ|ψ⟩ · ⟨Φ|Ψ⟩`. -/
theorem inner_tensorState (φ ψ : C2State) (Φ Ψ : C3State) :
    Inner (TensorState φ Φ) (TensorState ψ Ψ) = Inner φ ψ * Inner Φ Ψ := by
  rw [inner_apply, inner_apply, inner_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [TensorState, map_mul]
  ring

/-- Norm-squared of a product overlap factors as the product of norm-squared
local overlaps. -/
theorem normSq_inner_tensorState (φ ψ : C2State) (Φ Ψ : C3State) :
    Complex.normSq (Inner (TensorState φ Φ) (TensorState ψ Ψ)) =
      Complex.normSq (Inner φ ψ) * Complex.normSq (Inner Φ Ψ) := by
  rw [inner_tensorState, Complex.normSq_mul]

/-- `⟨φ|ψ⟩` is the conjugate of `⟨ψ|φ⟩`. -/
theorem inner_conj_symm (φ ψ : C2State) :
    Inner φ ψ = (starRingEnd ℂ) (Inner ψ φ) := by
  rw [inner_apply, inner_apply, map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [map_mul, Complex.conj_conj]
  ring

/-- `⟨φ|ψ⟩` is the conjugate of `⟨ψ|φ⟩` (qutrit version). -/
theorem inner_conj_symm_3 (Φ Ψ : C3State) :
    Inner Φ Ψ = (starRingEnd ℂ) (Inner Ψ Φ) := by
  rw [inner_apply, inner_apply, map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [map_mul, Complex.conj_conj]
  ring

/-- **Parseval / completeness**: for a complete product family `b`, the squared
overlaps of any `u` with the `b k` sum to `‖u‖²`. -/
theorem parseval {b : Fin 6 → QState (Fin 2 × Fin 3)}
    (hb : ∀ u v : QState (Fin 2 × Fin 3),
      Inner u v = ∑ k, Inner u (b k) * Inner (b k) v)
    (u : QState (Fin 2 × Fin 3)) :
    ∑ k, Complex.normSq (Inner u (b k)) = ∑ p, Complex.normSq (u p) := by
  have hsu : Inner u u = ((∑ p, Complex.normSq (u p) : ℝ) : ℂ) := by
    rw [inner_self, Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Complex.normSq_eq_norm_sq]
  have hk : Inner u u = ((∑ k, Complex.normSq (Inner u (b k)) : ℝ) : ℂ) := by
    rw [hb u u, Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [show Inner (b k) u = (starRingEnd ℂ) (Inner u (b k)) from by
      rw [inner_apply, inner_apply, map_sum]
      apply Finset.sum_congr rfl; intro p _
      rw [map_mul, Complex.conj_conj]; ring]
    rw [Complex.mul_conj]
  exact Complex.ofReal_inj.mp (by rw [← hk, hsu])

/-- Parseval for a normalized state: the squared overlaps with a complete
product family sum to `1`. -/
theorem parseval_normalized {b : Fin 6 → QState (Fin 2 × Fin 3)}
    (hb : ∀ u v : QState (Fin 2 × Fin 3),
      Inner u v = ∑ k, Inner u (b k) * Inner (b k) v)
    {u : QState (Fin 2 × Fin 3)} (hu : Normalized u) :
    ∑ k, Complex.normSq (Inner u (b k)) = 1 := by
  rw [parseval hb u]
  rw [← hu]
  apply Finset.sum_congr rfl; intro p _
  rw [Complex.normSq_eq_norm_sq]

/-- **Elementary pinning lemma.**  Six nonnegative real numbers `a k` and `b k`
with `a k * b k = 1/6`, `∑ a = 3`, `∑ b = 2` are forced to be `a k = 1/2` and
`b k = 1/3`.

Used at the end of the proof of Lemma 4: the completeness identities give the sum
constraints, and the nonnegativity of `(a k − 1/2)² / a k` upgrades the marginal
information to the pointwise values. -/
theorem six_term_pin (a b : Fin 6 → ℝ)
    (ha : ∀ k, 0 < a k)
    (hprod : ∀ k, a k * b k = 1 / 6)
    (hsa : ∑ k, a k = 3) (hsb : ∑ k, b k = 2) :
    (∀ k, a k = 1 / 2) ∧ (∀ k, b k = 1 / 3) := by
  have hb_eq : ∀ k, b k = (1 / 6) / a k := by
    intro k
    rw [eq_div_iff (ne_of_gt (ha k)), mul_comm, hprod k]
  have hsum_inv : ∑ k, (1 / a k) = 12 := by
    have heq : ∑ k, b k = ∑ k, (1 / 6 : ℝ) * (1 / a k) := by
      apply Finset.sum_congr rfl; intro k _
      rw [hb_eq k]; ring
    rw [heq, ← Finset.mul_sum] at hsb
    linarith
  have hterm : ∀ k, (a k - 1 / 2) ^ 2 / a k = a k - 1 + (1 / 4) * (1 / a k) := by
    intro k
    field_simp [ne_of_gt (ha k)]
    ring
  have hsix : ∑ k : Fin 6, (1 : ℝ) = 6 := by simp [Fintype.card_fin]
  have hzero : ∑ k, (a k - 1 / 2) ^ 2 / a k = 0 := by
    calc
      ∑ k, (a k - 1 / 2) ^ 2 / a k
          = ∑ k, (a k - 1 + (1 / 4) * (1 / a k)) :=
            Finset.sum_congr rfl (fun k _ => hterm k)
      _ = (∑ k, a k) - (∑ k, (1 : ℝ)) + (1 / 4) * (∑ k, (1 / a k)) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 3 - 6 + (1 / 4) * 12 := by rw [hsa, hsix, hsum_inv]
      _ = 0 := by norm_num
  have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin 6)),
      0 ≤ (a k - 1 / 2) ^ 2 / a k := by
    intro k _
    exact div_nonneg (sq_nonneg _) (le_of_lt (ha k))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
  have ha_half : ∀ k, a k = 1 / 2 := by
    intro k
    have hk := hall k (Finset.mem_univ k)
    rw [div_eq_zero_iff] at hk
    rcases hk with h | h
    · nlinarith [sq_nonneg (a k - 1 / 2)]
    · exact absurd h (ne_of_gt (ha k))
  refine ⟨ha_half, fun k => ?_⟩
  rw [hb_eq k, ha_half k]
  norm_num

end Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

/-! ## Claim-level predicates (paper notation) -/

namespace Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

open Qatlib.Foundations.PureStateMath

/-- A vector of `C² ⊗ C³` is a product state when it is `φ ⊗ Φ`. -/
def IsProductState (v : QState (Fin 2 × Fin 3)) : Prop :=
  ∃ φ : C2State, ∃ Φ : C3State, v = TensorState φ Φ

/-- Six unit vectors forming an orthonormal family (`⟨B k|B l⟩ = δ k l`). -/
def OrthonormalFamily (B : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  ∀ k l, Inner (B k) (B l) = if k = l then 1 else 0

/-- A triple of MU bases (no product assumption): three orthonormal bases with all
cross overlaps of squared modulus `1/6`. -/
def IsMuTriple (T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  (∀ r, OrthonormalFamily (T r)) ∧
  ∀ r s, r ≠ s → ∀ i j, Complex.normSq (Inner (T r i) (T s j)) = 1 / 6

/-- A triple of MU *product* bases: every state is a product state and the triple is MU. -/
def IsMuProductTriple (T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  (∀ r k, IsProductState (T r k)) ∧ IsMuTriple T

/-- A basis is a **direct product basis** when it is `{|i_a⟩ ⊗ |J_A⟩}` for a qubit basis
`{|i_a⟩}` and a qutrit basis `{|J_A⟩}`, i.e. the three T0 rows of Eq. (1). -/
def IsDirectProductBasis (B : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  ∃ (a : Fin 2 → C2State) (f : Fin 3 → C3State) (e : Fin 6 ≃ Fin 2 × Fin 3),
    (∀ i, Normalized (a i)) ∧ (∀ J, Normalized (f J)) ∧
    ∀ k, B k = TensorState (a (e k).1) (f (e k).2)

/-- An **indirect product basis** as in the third row of T1: a qubit basis `{|i_y⟩}` whose
`|0_y⟩` sector uses the qutrit basis `{|J_y⟩}` and whose `|1_y⟩` sector uses `{|J_w⟩}`. -/
def IsIndirectBasis (B : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  ∃ (a : Fin 2 → C2State) (f g : Fin 3 → C3State) (e : Fin 6 ≃ Fin 2 × Fin 3),
    (∀ i, Normalized (a i)) ∧ (∀ J, Normalized (f J)) ∧ (∀ J, Normalized (g J)) ∧
    ∀ k, B k = TensorState (a (e k).1) ((if (e k).1 = 0 then f else g) (e k).2)

/-- Equivalence of triples under the paper's transformations that preserve the product
structure and the moduli of overlaps: one common product unitary `U₂ ⊗ U₃`, an arbitrary
reordering `σ` of the three bases, a per-basis permutation `τ`, and unit phases `ph`.
(Anti-unitary global conjugation is omitted from this witness relation.) -/
def ProductEquiv (T T' : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  ∃ (U2 : Matrix (Fin 2) (Fin 2) ℂ) (U3 : Matrix (Fin 3) (Fin 3) ℂ),
  ∃ (_ : U2 ∈ Matrix.unitaryGroup (Fin 2) ℂ) (_ : U3 ∈ Matrix.unitaryGroup (Fin 3) ℂ),
  ∃ (σ : Fin 3 ≃ Fin 3) (τ : Fin 3 → Fin 6 ≃ Fin 6) (ph : Fin 3 → Fin 6 → ℂ),
    (∀ r k, ‖ph r k‖ = 1) ∧
    ∀ r k, T' r k = fun p =>
      ph r k * ApplyGate (TensorGate U2 U3) (T (σ r) ((τ r).symm k)) p

/-- Equivalence of pairs of bases under the same product-preserving transformations. -/
def ProductEquivPair (A B A' B' : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  ∃ (U2 : Matrix (Fin 2) (Fin 2) ℂ) (U3 : Matrix (Fin 3) (Fin 3) ℂ),
  ∃ (_ : U2 ∈ Matrix.unitaryGroup (Fin 2) ℂ) (_ : U3 ∈ Matrix.unitaryGroup (Fin 3) ℂ),
  ∃ (τA τB : Fin 6 ≃ Fin 6) (phA phB : Fin 6 → ℂ),
    (∀ k, ‖phA k‖ = 1) ∧ (∀ k, ‖phB k‖ = 1) ∧
    (∀ k, A' k = fun p => phA k * ApplyGate (TensorGate U2 U3) (A ((τA).symm k)) p) ∧
    (∀ k, B' k = fun p => phB k * ApplyGate (TensorGate U2 U3) (B ((τB).symm k)) p)

end Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel
