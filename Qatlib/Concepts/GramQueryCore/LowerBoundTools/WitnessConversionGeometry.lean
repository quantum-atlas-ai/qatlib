/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.WitnessConversionDefs
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Boolean witness conversion geometry

Constructs root states, forbidden vectors, and fixed vectors from a Boolean filtered Gram
factorization. Their orthogonality yields a common orthogonal projector and a product of
reflections with controlled action, following the state conversion geometry of [LeeEtAl2011].

The module handles zero-budget and zero-address cases by a single known unitary gate, and proves
quantitative witness distance and size bounds for the nonzero construction.

## Main statements

* `conversion_zero_corner_word`: gives an exact zero-query circuit in the degenerate cases.
* `conversion_witness_orthogonality`: derives orthogonality from a filtered Gram factorization.
* `conversion_witness_public_walk`: constructs a unitary reflection walk with prescribed witness
  action.
* `conversion_fixed_gap_bound`, `conversion_forbidden_size_bound`: control witness distance and
  size.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators

/-- A matrix possessing a filtered Gram certificate with budget zero is the zero matrix. -/
theorem conversion_cert_zero_matrix {X : Type} {n : ℕ} (A : Matrix X X ℂ)
    (Z : Fin n → Matrix X X ℂ) (h : gramFilteredCert A Z 0) : A = 0 := by
  obtain ⟨Q, hQ, u, v, hu, _, huv⟩ := h
  letI := hQ
  have hz (j : Fin n) (x : X) (q : Q) : u j x q = 0 := by
    have hj : (∑ q, Complex.normSq (u j x q)) ≤ 0 :=
      (Finset.single_le_sum (fun k _ =>
        Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg (u k x a)))
        (Finset.mem_univ j)).trans (hu x)
    have hq : Complex.normSq (u j x q) ≤ 0 :=
      (Finset.single_le_sum (fun a _ => Complex.normSq_nonneg (u j x a))
        (Finset.mem_univ q)).trans hj
    exact Complex.normSq_eq_zero.mp (le_antisymm hq (Complex.normSq_nonneg _))
  ext x y
  rw [huv]
  simp [dotProduct, hz]

/-- A matrix possessing a filtered Gram certificate with no filter addresses is the zero matrix. -/
theorem conversion_cert_no_addresses {X : Type} (A : Matrix X X ℂ)
    (Z : Fin 0 → Matrix X X ℂ) (W : ℝ) (h : gramFilteredCert A Z W) : A = 0 := by
  obtain ⟨Q, hQ, u, v, _, _, huv⟩ := h
  letI := hQ
  ext x y
  simpa using huv x y

/-- The inner product of two tensor product states is the product of their component inner
products. -/
private theorem conversion_inner_tensor {I J : Type} [Fintype I] [Fintype J]
    (a b : QState I) (c d : QState J) :
    Qatlib.Foundations.PureStateMath.Inner (TensorState a c) (TensorState b d) = Qatlib.Foundations.PureStateMath.Inner a b * Qatlib.Foundations.PureStateMath.Inner c d := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, TensorState, dotProduct, Fintype.sum_prod_type,
    Pi.star_apply, star_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The inner product of clean embeddings is the payload inner product when their Boolean tags
agree and zero otherwise. -/
theorem conversion_clean_inner {H : Type} [Fintype H] [DecidableEq H]
    (n r : ℕ) (hr : 0 < r) (b c : Bool) (ψ φ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (conversionCleanEmbed n r hr b ψ) (conversionCleanEmbed n r hr c φ) =
      (if b = c then 1 else 0) * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp [conversionCleanEmbed, conversion_inner_tensor, inner_ket_ket]

/-- State families with equal Gram matrices have an exact clean tagged conversion using a
unitary circuit with zero queries and one gate. -/
theorem conversion_equal_gram_clean_word
    (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (n : ℕ) (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (hGram : gramStateMatrix ρ = gramStateMatrix σ) :
    ∃ C : Circuit ((Fin (n+1) × Bool) × ((Bool × H) × Fin 1)),
      IsUnitaryCircuit C ∧ QueryCount C = 0 ∧ GateCount C = 1 ∧
      ∀ x, Run (workspaceBitOracle (W := (Bool × H) × Fin 1)
        (conversionPaddedInput input x)) C (conversionCleanEmbed n 1 (by omega) false (ρ x)) =
        conversionCleanEmbed n 1 (by omega) true (σ x) := by
  let K := (Fin (n+1) × Bool) × ((Bool × H) × Fin 1)
  let V : Matrix K X ℂ := fun i x => conversionCleanEmbed n 1 (by omega) false (ρ x) i
  let S : Matrix K X ℂ := fun i x => conversionCleanEmbed n 1 (by omega) true (σ x) i
  have hVS : Vᴴ * V = Sᴴ * S := by
    ext x y
    change Qatlib.Foundations.PureStateMath.Inner (conversionCleanEmbed n 1 (by omega) false (ρ x))
      (conversionCleanEmbed n 1 (by omega) false (ρ y)) =
      Qatlib.Foundations.PureStateMath.Inner (conversionCleanEmbed n 1 (by omega) true (σ x))
      (conversionCleanEmbed n 1 (by omega) true (σ y))
    simp only [conversion_clean_inner, if_true, one_mul]
    exact congrFun (congrFun hGram x) y
  obtain ⟨U, hU, hUV⟩ := gram_equal_actual_unitary_transport K X V S hVS
  refine ⟨[.gate U], ?_, rfl, rfl, ?_⟩
  · simpa [IsUnitaryCircuit] using hU
  · intro x
    change ApplyGate U (fun i => V i x) = fun i => S i x
    funext i
    exact congrFun (congrFun hUV i) x

/-- A filtered Gram certificate with zero budget or no input addresses yields an exact clean
tagged conversion using zero queries and one unitary gate. -/
theorem conversion_zero_corner_word
    (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (n : ℕ) (input : X → Fin n → Bool) (ρ σ : X → QState H) (W : ℝ)
    (hCert : gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (gramFilterDelta input) W) (hZero : W = 0 ∨ n = 0) :
    ∃ C : Circuit ((Fin (n+1) × Bool) × ((Bool × H) × Fin 1)),
      IsUnitaryCircuit C ∧ QueryCount C = 0 ∧ GateCount C = 1 ∧
      ∀ x, Run (workspaceBitOracle (W := (Bool × H) × Fin 1)
        (conversionPaddedInput input x)) C (conversionCleanEmbed n 1 (by omega) false (ρ x)) =
        conversionCleanEmbed n 1 (by omega) true (σ x) := by
  apply conversion_equal_gram_clean_word X H n input ρ σ
  apply sub_eq_zero.mp
  rcases hZero with hW | hn
  · subst W
    exact conversion_cert_zero_matrix _ _ hCert
  · subst n
    exact conversion_cert_no_addresses _ _ W hCert

/-- The equally weighted direct sum of the input and output states on two copies of the state
space. -/
def conversionRootPlus {H : Type} (ρ σ : QState H) : QState (H ⊕ H) :=
  Sum.elim (((Real.sqrt 2)⁻¹ : ℂ) • ρ) (((Real.sqrt 2)⁻¹ : ℂ) • σ)

/-- The equally weighted direct sum of the input state and the negative output state. -/
def conversionRootMinus {H : Type} (ρ σ : QState H) : QState (H ⊕ H) :=
  Sum.elim (((Real.sqrt 2)⁻¹ : ℂ) • ρ) (-((Real.sqrt 2)⁻¹ : ℂ) • σ)

/-- The inner product of two direct sum states is the sum of their component inner products. -/
private theorem conversion_inner_sum {H K : Type} [Fintype H] [Fintype K]
    (a b : QState H) (c d : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (Sum.elim a c) (Sum.elim b d) = Qatlib.Foundations.PureStateMath.Inner a b + Qatlib.Foundations.PureStateMath.Inner c d := by
  simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Fintype.sum_sum_type]

/-- Scaling the first and second states by `c` and `d` multiplies their inner product by `star c
* d`. -/
private theorem conversion_inner_smul {H : Type} [Fintype H]
    (a b : QState H) (c d : ℂ) : Qatlib.Foundations.PureStateMath.Inner (c • a) (d • b) = star c * d * Qatlib.Foundations.PureStateMath.Inner a b := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Pi.smul_apply,
      smul_eq_mul, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The squared complex norm factor associated with the reciprocal of `Real.sqrt 2` equals
`1/2`. -/
private theorem conversion_root_scale :
    star (((Real.sqrt 2)⁻¹ : ℂ)) * (((Real.sqrt 2)⁻¹ : ℂ)) = 1/2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hc : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by exact_mod_cast hs
  simp only [map_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, hc]
  norm_num

/-- The inner product of a minus root and a plus root is one half of the difference of the input
and output inner products. -/
theorem conversion_root_cross {H : Type} [Fintype H] (ρ σ ρ' σ' : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (conversionRootMinus ρ σ) (conversionRootPlus ρ' σ') =
      (1/2 : ℂ) * (Qatlib.Foundations.PureStateMath.Inner ρ ρ' - Qatlib.Foundations.PureStateMath.Inner σ σ') := by
  rw [conversionRootMinus, conversionRootPlus, conversion_inner_sum,
    conversion_inner_smul, conversion_inner_smul, star_neg]
  rw [neg_mul, conversion_root_scale]
  ring

/-- The plus root of two normalized states is normalized. -/
theorem conversion_root_plus_normalized {H : Type} [Fintype H]
    (ρ σ : QState H) (hρ : Normalized ρ) (hσ : Normalized σ) :
    Normalized (conversionRootPlus ρ σ) := by
  apply (normalized_iff_inner_self _).mpr
  rw [conversionRootPlus, conversion_inner_sum, conversion_inner_smul,
    conversion_inner_smul, conversion_root_scale,
    (normalized_iff_inner_self _).mp hρ, (normalized_iff_inner_self _).mp hσ]
  norm_num

/-- The forbidden vector with root component `2*α` times the minus root and negative
first-witness amplitudes on input-matching query sectors. -/
def conversionForbidden {X H Q : Type} {n : ℕ} (input : X → Fin n → Bool)
    (ρ σ : X → QState H) (u : Fin n → X → Q → ℂ) (α : ℝ) (x : X) :
    QState ((H ⊕ H) ⊕ (Fin n × Bool × Q)) :=
  Sum.elim (((2 * α : ℝ) : ℂ) • conversionRootMinus (ρ x) (σ x))
    (fun p => if p.2.1 = input x p.1 then -u p.1 x p.2.2 else 0)

/-- The fixed-vector candidate with the plus root and second-witness amplitudes scaled by `α` on
input-mismatching query sectors. -/
def conversionFixedWitness {X H Q : Type} {n : ℕ} (input : X → Fin n → Bool)
    (ρ σ : X → QState H) (v : Fin n → X → Q → ℂ) (α : ℝ) (x : X) :
    QState ((H ⊕ H) ⊕ (Fin n × Bool × Q)) :=
  Sum.elim (conversionRootPlus (ρ x) (σ x))
    (fun p => if p.2.1 = !(input x p.1) then (α : ℂ) * v p.1 x p.2.2 else 0)

/-- The filtered Gram factorization identity makes each forbidden vector orthogonal to every
fixed witness vector. -/
theorem conversion_witness_orthogonality
    {X H Q : Type} [Fintype H] [Fintype Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u v : Fin n → X → Q → ℂ) (α : ℝ)
    (hEq : ∀ y x, (gramStateMatrix ρ - gramStateMatrix σ) y x =
      ∑ j, gramFilterDelta input j y x * (star (u j y) ⬝ᵥ v j x)) (x y : X) :
    Qatlib.Foundations.PureStateMath.Inner (conversionForbidden input ρ σ u α y)
      (conversionFixedWitness input ρ σ v α x) = 0 := by
  rw [conversionForbidden, conversionFixedWitness, conversion_inner_sum]
  have hrow : Qatlib.Foundations.PureStateMath.Inner (((2 * α : ℝ) : ℂ) • conversionRootMinus (ρ y) (σ y))
      (conversionRootPlus (ρ x) (σ x)) =
      (α : ℂ) * (gramStateMatrix ρ - gramStateMatrix σ) y x := by
    rw [← one_smul ℂ (conversionRootPlus (ρ x) (σ x)), conversion_inner_smul,
      mul_one, conversion_root_cross]
    simp only [map_mul, map_ofNat, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Matrix.sub_apply, gramStateMatrix]
    ring
  rw [hrow, hEq]
  have hcol : Qatlib.Foundations.PureStateMath.Inner
      (fun p : Fin n × Bool × Q => if p.2.1 = input y p.1 then -u p.1 y p.2.2 else 0)
      (fun p => if p.2.1 = !(input x p.1) then (α : ℂ) * v p.1 x p.2.2 else 0) =
      -(α : ℂ) * ∑ j, gramFilterDelta input j y x * (star (u j y) ⬝ᵥ v j x) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Fintype.sum_prod_type,
        Pi.star_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [gramFilterDelta]
    cases input y j <;> cases input x j <;> simp <;>
      rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [hcol]
  ring

/-- The diagonal mask preserving the root sector and the input-mismatching query sectors. -/
def conversionLogicalKeep {X H Q : Type} {n : ℕ} (input : X → Fin n → Bool)
    (x : X) : ((H ⊕ H) ⊕ (Fin n × Bool × Q)) → ℂ :=
  Sum.elim (fun _ => 1) (fun p => if p.2.1 = input x p.1 then 0 else 1)

/-- The diagonal matrix formed from the logical keep mask. -/
def conversionLogicalProjector {X H Q : Type} [DecidableEq H] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (x : X) :
    Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ :=
  Matrix.diagonal (conversionLogicalKeep input x)

/-- The logical keep matrix is an orthogonal projector. -/
theorem conversionLogicalProjector_orthogonal
    {X H Q : Type} [Fintype H] [DecidableEq H] [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (x : X) :
    IsOrthogonalProjector (conversionLogicalProjector (H := H) (Q := Q) input x) := by
  have hi : (fun p => conversionLogicalKeep (H := H) (Q := Q) input x p *
      conversionLogicalKeep input x p) = conversionLogicalKeep input x := by
    funext p
    cases p with
    | inl a => simp [conversionLogicalKeep]
    | inr p => dsimp [conversionLogicalKeep]; split_ifs <;> norm_num
  have hs : star (conversionLogicalKeep (H := H) (Q := Q) input x) =
      conversionLogicalKeep input x := by
    funext p
    cases p with
    | inl a => simp [conversionLogicalKeep]
    | inr p => dsimp [conversionLogicalKeep]; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · change conversionLogicalProjector input x * conversionLogicalProjector input x =
      conversionLogicalProjector input x
    simp only [conversionLogicalProjector, Matrix.diagonal_mul_diagonal, hi]
  · change star (conversionLogicalProjector input x) = conversionLogicalProjector input x
    simp only [conversionLogicalProjector, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, hs]

/-- The logical projector fixes the constructed fixed witness vector. -/
theorem conversionLogicalProjector_fixedWitness
    {X H Q : Type} [Fintype H] [DecidableEq H] [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (v : Fin n → X → Q → ℂ) (α : ℝ) (x : X) :
    ApplyGate (conversionLogicalProjector input x) (conversionFixedWitness input ρ σ v α x) =
      conversionFixedWitness input ρ σ v α x := by
  funext p
  change (Matrix.diagonal (conversionLogicalKeep input x) *ᵥ _) p = _
  rw [Matrix.mulVec_diagonal]
  cases p with
  | inl a => simp [conversionLogicalKeep, conversionFixedWitness]
  | inr p => cases p with | mk j p => cases p with | mk b q =>
      cases h : input x j <;> cases b <;> simp [conversionLogicalKeep, conversionFixedWitness, h]

/-- The logical projector removes the query sector of a forbidden vector, leaving its scaled
minus root. -/
theorem conversionLogicalProjector_forbidden
    {X H Q : Type} [Fintype H] [DecidableEq H] [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u : Fin n → X → Q → ℂ) (α : ℝ) (x : X) :
    ApplyGate (conversionLogicalProjector input x) (conversionForbidden input ρ σ u α x) =
      Sum.elim (((2 * α : ℝ) : ℂ) • conversionRootMinus (ρ x) (σ x)) (fun _ => 0) := by
  funext p
  change (Matrix.diagonal (conversionLogicalKeep input x) *ᵥ _) p = _
  rw [Matrix.mulVec_diagonal]
  cases p with
  | inl a => simp [conversionLogicalKeep, conversionForbidden]
  | inr p => dsimp [conversionLogicalKeep, conversionForbidden]; split_ifs <;> norm_num

/-- Two mutually orthogonal vector families possess an orthogonal projector annihilating the
first family and fixing the second. -/
theorem conversion_public_complement_projection
    (I X : Type) [Fintype I] [DecidableEq I]
    (forbidden fixed : X → QState I)
    (hCross : ∀ x y, Qatlib.Foundations.PureStateMath.Inner (forbidden x) (fixed y) = 0) :
    ∃ Λ : Matrix I I ℂ, IsOrthogonalProjector Λ ∧
      (∀ x, ApplyGate Λ (forbidden x) = 0) ∧
      (∀ y, ApplyGate Λ (fixed y) = fixed y) := by
  let F := fun x => toEuclidean_fromVec (forbidden x)
  let S := fun x => toEuclidean_fromVec (fixed x)
  let K := Submodule.span ℂ (Set.range F)
  let T := Kᗮ
  let e := Matrix.toLinAlgEquiv (EuclideanSpace.basisFun I ℂ).toBasis
  let Λ : Matrix I I ℂ := e.symm T.starProjection.toLinearMap
  have he : Matrix.toEuclideanLin Λ = T.starProjection.toLinearMap := e.apply_symm_apply _
  have hi : Λ * Λ = Λ := by
    apply e.injective
    rw [map_mul, show e Λ = T.starProjection.toLinearMap from e.apply_symm_apply _]
    exact congrArg ContinuousLinearMap.toLinearMap T.isIdempotentElem_starProjection
  have hs : Λᴴ = Λ := by
    apply Matrix.IsHermitian.eq
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [he]
    exact T.starProjection_isSymmetric
  refine ⟨Λ, ⟨hi, hs⟩, ?_, ?_⟩
  · intro x
    have hx : F x ∈ K := Submodule.subset_span (Set.mem_range_self x)
    have hz : T.starProjection (F x) = 0 :=
      T.starProjection_apply_eq_zero_iff.mpr (Submodule.le_orthogonal_orthogonal K hx)
    have h := congrArg (fun f : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I => f (F x)) he
    change toEuclidean_fromVec (ApplyGate Λ (forbidden x)) = T.starProjection (F x) at h
    rw [hz] at h
    exact congrArg WithLp.ofLp h
  · intro y
    have hy : S y ∈ T := by
      apply (K.mem_orthogonal _).mpr
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨x, rfl⟩ := hz
          exact (inner_euclidean_fromVec _ _).trans (hCross x y)
      | zero => simp
      | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
      | smul a z _ hz => simp [inner_smul_left, hz]
    have hfix : T.starProjection (S y) = S y := T.starProjection_eq_self_iff.mpr hy
    have h := congrArg (fun f : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I => f (S y)) he
    change toEuclidean_fromVec (ApplyGate Λ (fixed y)) = T.starProjection (S y) at h
    rw [hfix] at h
    exact congrArg WithLp.ofLp h

/-- A filtered Gram factorization yields an orthogonal projector annihilating all forbidden
vectors and fixing all fixed witness vectors. -/
theorem conversion_witness_public_projection
    {X H Q : Type} [Fintype H] [DecidableEq H] [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u v : Fin n → X → Q → ℂ) (α : ℝ)
    (hEq : ∀ y x, (gramStateMatrix ρ - gramStateMatrix σ) y x =
      ∑ j, gramFilterDelta input j y x * (star (u j y) ⬝ᵥ v j x)) :
    ∃ Λ : Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ,
      IsOrthogonalProjector Λ ∧
      (∀ x, ApplyGate Λ (conversionForbidden input ρ σ u α x) = 0) ∧
      (∀ x, ApplyGate Λ (conversionFixedWitness input ρ σ v α x) =
        conversionFixedWitness input ρ σ v α x) := by
  apply conversion_public_complement_projection _ X
  intro x y
  exact conversion_witness_orthogonality input ρ σ u v α hEq y x

/-- If `Λ` annihilates `ψ`, then the product of reflections about `P` and `Λ` sends `ψ` to `ψ -
2 • ApplyGate P ψ`. -/
theorem conversion_walk_forbidden_identity
    {I : Type} [Fintype I] [DecidableEq I]
    (P Λ : Matrix I I ℂ) (ψ : QState I) (hΛ : ApplyGate Λ ψ = 0) :
    ApplyGate (ReflectionAbout P * ReflectionAbout Λ) ψ = ψ - (2 : ℂ) • ApplyGate P ψ := by
  rw [applyGate_mul, applyGate_reflectionAbout_of_zero hΛ, applyGate_reflectionAbout]
  simp only [ApplyGate, Matrix.mulVec_neg]
  module

/-- The sum of squared amplitudes of a direct sum state is the sum of the corresponding
component sums. -/
private theorem conversion_sum_norm_sq {I J : Type} [Fintype I] [Fintype J]
    (a : QState I) (b : QState J) :
    (∑ p : I ⊕ J, ‖Sum.elim a b p‖ ^ 2) = (∑ i, ‖a i‖ ^ 2) + ∑ j, ‖b j‖ ^ 2 := by
  rw [Fintype.sum_sum_type]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => rfl)

/-- The minus root of two normalized states is normalized. -/
theorem conversion_root_minus_normalized {H : Type} [Fintype H] (ρ σ : QState H)
    (hρ : Normalized ρ) (hσ : Normalized σ) :
    Normalized (conversionRootMinus ρ σ) := by
  apply (normalized_iff_inner_self _).mpr
  rw [conversionRootMinus, conversion_inner_sum, conversion_inner_smul,
    conversion_inner_smul, star_neg, neg_mul_neg, conversion_root_scale,
    (normalized_iff_inner_self _).mp hρ, (normalized_iff_inner_self _).mp hσ]
  norm_num

/-- Embeds a state into the first root summand, with zero amplitudes in the second root and
query sectors. -/
def conversionSourceRoot {H Q : Type} {n : ℕ} (ψ : QState H) :
    QState ((H ⊕ H) ⊕ (Fin n × Bool × Q)) :=
  Sum.elim (Sum.elim ψ 0) 0

/-- Embeds a state into the second root summand, with zero amplitudes in the first root and
query sectors. -/
def conversionTargetRoot {H Q : Type} {n : ℕ} (ψ : QState H) :
    QState ((H ⊕ H) ⊕ (Fin n × Bool × Q)) :=
  Sum.elim (Sum.elim 0 ψ) 0

/-- Embeds the plus root in the full witness space with zero query-sector amplitudes. -/
def conversionPlusRoot {H Q : Type} {n : ℕ} (ρ σ : QState H) :
    QState ((H ⊕ H) ⊕ (Fin n × Bool × Q)) :=
  Sum.elim (conversionRootPlus ρ σ) 0

/-- Embeds the minus root in the full witness space with zero query-sector amplitudes. -/
def conversionMinusRoot {H Q : Type} {n : ℕ} (ρ σ : QState H) :
    QState ((H ⊕ H) ⊕ (Fin n × Bool × Q)) :=
  Sum.elim (conversionRootMinus ρ σ) 0

/-- The square of the complex embedding of the reciprocal of `Real.sqrt 2` equals `1/2`. -/
private theorem conversion_root_inv_two :
    ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) * ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) = 1 / 2 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num)
  have hinv : ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) * ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) =
      (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    rw [← _root_.mul_inv_rev]
  rw [hinv, hs]
  norm_num

/-- If `a*a = 1/2`, then `a * (a*b + a*b) = b`. -/
private theorem conversion_root_double {a b : ℂ} (hc : a * a = 1 / 2) :
    a * (a * b + a * b) = b := by
  linear_combination (2 * b) * hc

/-- If `a*a = 1/2`, then `a * (a*b - -a*b) = b`. -/
private theorem conversion_root_double' {a b : ℂ} (hc : a * a = 1 / 2) :
    a * (a * b - -a * b) = b := by
  linear_combination (2 * b) * hc

/-- The source root is the sum of the plus and minus roots scaled by the reciprocal of
`Real.sqrt 2`. -/
theorem conversion_source_root_split {H Q : Type} {n : ℕ} (ρ σ : QState H) :
    (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) • (conversionPlusRoot (Q := Q) (n := n) ρ σ +
        conversionMinusRoot (Q := Q) (n := n) ρ σ) =
      conversionSourceRoot (Q := Q) (n := n) ρ := by
  have hc := conversion_root_inv_two
  funext g
  rcases g with r | p
  · rcases r with h | h
    · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, conversionSourceRoot,
        conversionPlusRoot, conversionMinusRoot, conversionRootPlus,
        conversionRootMinus, Sum.elim_inl]
      exact conversion_root_double hc
    · simp only [Pi.smul_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, conversionSourceRoot, conversionPlusRoot,
        conversionMinusRoot, conversionRootPlus, conversionRootMinus,
        Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
      ring
  · simp [conversionSourceRoot, conversionPlusRoot, conversionMinusRoot]

/-- The target root is the difference of the plus and minus roots scaled by the reciprocal of
`Real.sqrt 2`. -/
theorem conversion_target_root_split {H Q : Type} {n : ℕ} (ρ σ : QState H) :
    (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) • (conversionPlusRoot (Q := Q) (n := n) ρ σ -
        conversionMinusRoot (Q := Q) (n := n) ρ σ) =
      conversionTargetRoot (Q := Q) (n := n) σ := by
  have hc := conversion_root_inv_two
  funext g
  rcases g with r | p
  · rcases r with h | h
    · simp only [Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        conversionTargetRoot, conversionPlusRoot, conversionMinusRoot,
        conversionRootPlus, conversionRootMinus, Sum.elim_inl,
        Pi.zero_apply]
      ring
    · simp only [Pi.smul_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, conversionTargetRoot, conversionPlusRoot,
        conversionMinusRoot, conversionRootMinus, conversionRootPlus,
        Sum.elim_inl, Sum.elim_inr]
      exact conversion_root_double' hc
  · simp [conversionTargetRoot, conversionPlusRoot, conversionMinusRoot]

/-- The source root embedding preserves inner products. -/
theorem conversion_source_root_inner {H Q : Type} [Fintype H] [Fintype Q] {n : ℕ}
    (ρ ρ' : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (conversionSourceRoot (Q := Q) (n := n) ρ)
        (conversionSourceRoot (Q := Q) (n := n) ρ') = Qatlib.Foundations.PureStateMath.Inner ρ ρ' := by
  simp [conversionSourceRoot, Qatlib.Foundations.PureStateMath.Inner, dotProduct]

/-- The target root embedding preserves inner products. -/
theorem conversion_target_root_inner {H Q : Type} [Fintype H] [Fintype Q] {n : ℕ}
    (σ σ' : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (conversionTargetRoot (Q := Q) (n := n) σ)
        (conversionTargetRoot (Q := Q) (n := n) σ') = Qatlib.Foundations.PureStateMath.Inner σ σ' := by
  simp [conversionTargetRoot, Qatlib.Foundations.PureStateMath.Inner, dotProduct]

/-- Placing each witness column in one selected Boolean sector preserves its total squared
amplitude. -/
theorem conversion_column_mass_eq {n : ℕ} {Q : Type} [Fintype Q]
    (f : Fin n → Bool) (a : Fin n → Q → ℂ) :
    (∑ p : Fin n × Bool × Q, ‖(if p.2.1 = f p.1 then a p.1 p.2.2 else 0 : ℂ)‖ ^ 2) =
      ∑ j, ∑ q, ‖a j q‖ ^ 2 := by
  have h1 : (∑ p : Fin n × Bool × Q,
      ‖(if p.2.1 = f p.1 then a p.1 p.2.2 else 0 : ℂ)‖ ^ 2) =
      ∑ j : Fin n, ∑ s : Bool × Q, ‖(if s.1 = f j then a j s.2 else 0 : ℂ)‖ ^ 2 :=
    Fintype.sum_prod_type _
  have h2 : ∀ j : Fin n, (∑ s : Bool × Q, ‖(if s.1 = f j then a j s.2 else 0 : ℂ)‖ ^ 2) =
      ∑ q : Q, ‖a j q‖ ^ 2 := by
    intro j
    have hs := Fintype.sum_prod_type
      (f := fun s : Bool × Q => ‖(if s.1 = f j then a j s.2 else 0 : ℂ)‖ ^ 2)
    rw [hs]
    cases f j <;> simp
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => h2 j

/-- The fixed witness vector's squared Euclidean distance from the plus root is `α^2` times the
second-witness squared amplitude sum. -/
theorem conversion_fixed_minus_plus_norm_sq {X H Q : Type} [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (v : Fin n → X → Q → ℂ) (α : ℝ) (x : X) :
    ‖toEuclidean_fromVec (conversionFixedWitness input ρ σ v α x -
        conversionPlusRoot (Q := Q) (n := n) (ρ x) (σ x))‖ ^ 2 =
      α ^ 2 * ∑ j, ∑ q, ‖v j x q‖ ^ 2 := by
  rw [norm_toEuclidean_fromVec_sq, Fintype.sum_sum_type]
  have hrow : (∑ r : H ⊕ H,
      ‖(conversionFixedWitness input ρ σ v α x -
          conversionPlusRoot (Q := Q) (n := n) (ρ x) (σ x)) (Sum.inl r)‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    rcases r with h | h <;> simp [conversionFixedWitness, conversionPlusRoot]
  have hcol : (∑ p : Fin n × Bool × Q,
      ‖(conversionFixedWitness input ρ σ v α x -
          conversionPlusRoot (Q := Q) (n := n) (ρ x) (σ x)) (Sum.inr p)‖ ^ 2) =
      ∑ p : Fin n × Bool × Q,
        ‖((α : ℝ) : ℂ) * (if p.2.1 = !(input x p.1) then v p.1 x p.2.2 else 0)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.2.1 = !(input x p.1) <;>
      simp [conversionFixedWitness, conversionPlusRoot, hp]
  have hnm : ∀ z : ℂ, ‖((α : ℝ) : ℂ) * z‖ ^ 2 = α ^ 2 * ‖z‖ ^ 2 := by
    intro z
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hrow, zero_add, hcol]
  simp only [hnm, ← Finset.mul_sum]
  rw [conversion_column_mass_eq (f := fun j => !(input x j))
    (a := fun j q => v j x q)]

/-- For positive `α` and normalized root states, a first-witness squared amplitude budget `B`
bounds the squared norm of the forbidden vector scaled by `(2*α)⁻¹` by `1 + ‖(2*α : ℂ)⁻¹‖^2
* B`. -/
theorem conversion_forbidden_scaled_norm {X H Q : Type} [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u : Fin n → X → Q → ℂ) (α : ℝ) (hα : 0 < α) (x : X)
    (hρ : Normalized (ρ x)) (hσ : Normalized (σ x)) (B : ℝ)
    (hB : (∑ j, ∑ q, ‖u j x q‖ ^ 2) ≤ B) :
    ‖toEuclidean_fromVec (((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x)‖ ^ 2 ≤
      1 + ‖(((2 * α : ℝ) : ℂ)⁻¹)‖ ^ 2 * B := by
  have hc : (((2 * α : ℝ) : ℂ)⁻¹) * ((2 * α : ℝ) : ℂ) = 1 := by
    refine inv_mul_cancel₀ ?_
    simp only [ne_eq]
    exact_mod_cast (by linarith : (2 * α : ℝ) ≠ 0)
  rw [norm_toEuclidean_fromVec_sq, Fintype.sum_sum_type]
  have hrow : (∑ r : H ⊕ H,
      ‖(((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) (Sum.inl r)‖ ^ 2) =
      ∑ r : H ⊕ H, ‖conversionRootMinus (ρ x) (σ x) r‖ ^ 2 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show (((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) (Sum.inl r) =
        (((2 * α : ℝ) : ℂ)⁻¹) *
          (((2 * α : ℝ) : ℂ) * conversionRootMinus (ρ x) (σ x) r) from rfl,
      ← mul_assoc, hc, one_mul]
  have hrownorm : (∑ r : H ⊕ H, ‖conversionRootMinus (ρ x) (σ x) r‖ ^ 2) = 1 :=
    conversion_root_minus_normalized (ρ x) (σ x) hρ hσ
  have hcol : (∑ p : Fin n × Bool × Q,
      ‖(((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) (Sum.inr p)‖ ^ 2) =
      ‖(((2 * α : ℝ) : ℂ)⁻¹)‖ ^ 2 * ∑ j, ∑ q, ‖u j x q‖ ^ 2 := by
    have hpt : ∀ p : Fin n × Bool × Q,
        (((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) (Sum.inr p) =
        (((2 * α : ℝ) : ℂ)⁻¹) *
          (if p.2.1 = input x p.1 then -u p.1 x p.2.2 else 0) := by
      intro p; rfl
    simp only [hpt, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [conversion_column_mass_eq (f := fun j => input x j)
      (a := fun j q => -(u j x q))]
    simp
  rw [hrow, hrownorm, hcol]
  exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hB (sq_nonneg _))

/-- For positive `α`, the logical projector sends the forbidden vector scaled by `(2*α)⁻¹` to
the minus root. -/
theorem conversion_forbidden_scaled_projector {X H Q : Type} [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u : Fin n → X → Q → ℂ) (α : ℝ) (hα : 0 < α) (x : X) :
    ApplyGate (conversionLogicalProjector input x)
        (((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) =
      conversionMinusRoot (Q := Q) (n := n) (ρ x) (σ x) := by
  have hc : (((2 * α : ℝ) : ℂ)⁻¹) * ((2 * α : ℝ) : ℂ) = 1 := by
    refine inv_mul_cancel₀ ?_
    simp only [ne_eq]
    exact_mod_cast (by linarith : (2 * α : ℝ) ≠ 0)
  have hsmul : ∀ (c : ℂ) (a : QState (H ⊕ H)) (b : QState (Fin n × Bool × Q)),
      c • Sum.elim a b = Sum.elim (c • a) (c • b) := by
    intro c a b
    funext p
    rcases p with i | j <;> simp [Sum.elim]
  have hstep : ApplyGate (conversionLogicalProjector input x)
      (((2 * α : ℝ) : ℂ)⁻¹ • conversionForbidden input ρ σ u α x) =
      (((2 * α : ℝ) : ℂ)⁻¹) •
        ApplyGate (conversionLogicalProjector input x)
          (conversionForbidden input ρ σ u α x) := by
    simp only [ApplyGate, Matrix.mulVec_smul]
  have hz : (((2 * α : ℝ) : ℂ)⁻¹ • (fun _ => (0 : ℂ)) :
      QState (Fin n × Bool × Q)) = 0 := by
    funext p; simp
  rw [hstep, conversionLogicalProjector_forbidden, hsmul, smul_smul, hc, one_smul,
    hz]
  rfl

/-- For positive `B` and nonnegative `η`, a second-witness budget of at most `B` gives distance
at most `η/2` from the fixed vector at scale `η/(2*Real.sqrt B)` to the plus root. -/
theorem conversion_fixed_gap_bound {X H Q : Type} [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (v : Fin n → X → Q → ℂ) (B η : ℝ) (hB : 0 < B) (hη : 0 ≤ η) (x : X)
    (hv : (∑ j, ∑ q, ‖v j x q‖ ^ 2) ≤ B) :
    ‖toEuclidean_fromVec (conversionFixedWitness input ρ σ v (η / (2 * Real.sqrt B)) x -
      conversionPlusRoot (Q := Q) (n := n) (ρ x) (σ x))‖ ≤ η / 2 := by
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hs2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  have hα : (η / (2 * Real.sqrt B)) ^ 2 * B = (η / 2) ^ 2 := by
    field_simp
    nlinarith [hs2]
  have hsq := conversion_fixed_minus_plus_norm_sq input ρ σ v (η / (2 * Real.sqrt B)) x
  have hb := mul_le_mul_of_nonneg_left hv (sq_nonneg (η / (2 * Real.sqrt B)))
  rw [hα, ← hsq] at hb
  nlinarith [norm_nonneg (toEuclidean_fromVec (conversionFixedWitness input ρ σ v
    (η / (2 * Real.sqrt B)) x - conversionPlusRoot (Q := Q) (n := n) (ρ x) (σ x)))]

/-- For `B ≥ 1`, `0 < η ≤ 1`, normalized states, and first-witness budget at most `B`, the
scaled forbidden vector has norm at most `2*B/η`. -/
theorem conversion_forbidden_size_bound {X H Q : Type} [Fintype H] [DecidableEq H]
    [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u : Fin n → X → Q → ℂ) (B η : ℝ) (hB : 1 ≤ B) (hη : 0 < η) (hη1 : η ≤ 1)
    (x : X) (hρ : Normalized (ρ x)) (hσ : Normalized (σ x))
    (hu : (∑ j, ∑ q, ‖u j x q‖ ^ 2) ≤ B) :
    ‖toEuclidean_fromVec (((2 * (η / (2 * Real.sqrt B)) : ℝ) : ℂ)⁻¹ •
      conversionForbidden input ρ σ u (η / (2 * Real.sqrt B)) x)‖ ≤ 2 * B / η := by
  have hBp : 0 < B := by linarith
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  have hα : 0 < η / (2 * Real.sqrt B) := by positivity
  have hinv : (2 * (η / (2 * Real.sqrt B)))⁻¹ = Real.sqrt B / η := by
    field_simp
  have hnorm : ‖(((2 * (η / (2 * Real.sqrt B)) : ℝ) : ℂ)⁻¹)‖ ^ 2 * B =
      (B / η) ^ 2 := by
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs, hinv,
      div_pow, Real.sq_sqrt hBp.le]
    ring
  have hb := conversion_forbidden_scaled_norm input ρ σ u (η / (2 * Real.sqrt B))
    hα x hρ hσ B hu
  rw [hnorm] at hb
  have hc : 1 ≤ B / η := (one_le_div hη).mpr (hη1.trans hB)
  have hd : 2 * B / η = 2 * (B / η) := by ring
  rw [hd]
  nlinarith [norm_nonneg (toEuclidean_fromVec
    (((2 * (η / (2 * Real.sqrt B)) : ℝ) : ℂ)⁻¹ •
      conversionForbidden input ρ σ u (η / (2 * Real.sqrt B)) x))]

/-- A filtered Gram factorization yields a common orthogonal projector whose reflection walk is
unitary, fixes the fixed witnesses, and changes forbidden vectors by twice their projected
root component. -/
theorem conversion_witness_public_walk
    {X H Q : Type} [Fintype H] [DecidableEq H] [Fintype Q] [DecidableEq Q] {n : ℕ}
    (input : X → Fin n → Bool) (ρ σ : X → QState H)
    (u v : Fin n → X → Q → ℂ) (α : ℝ)
    (hEq : ∀ y x, (gramStateMatrix ρ - gramStateMatrix σ) y x =
      ∑ j, gramFilterDelta input j y x * (star (u j y) ⬝ᵥ v j x)) :
    ∃ Λ : Matrix ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ((H ⊕ H) ⊕ (Fin n × Bool × Q)) ℂ,
      IsOrthogonalProjector Λ ∧
      ∀ x,
      let U :=
          ReflectionAbout (conversionLogicalProjector (H := H) (Q := Q) input x) * ReflectionAbout Λ
      U ∈ Matrix.unitaryGroup _ ℂ ∧
      ApplyGate U (conversionFixedWitness input ρ σ v α x) = conversionFixedWitness input ρ σ v α x ∧
      ApplyGate U (conversionForbidden input ρ σ u α x) =
        conversionForbidden input ρ σ u α x - (2 : ℂ) •
          Sum.elim (((2 * α : ℝ) : ℂ) • conversionRootMinus (ρ x) (σ x)) (fun _ => 0) := by
  obtain ⟨Λ, hΛ, hForbidden, hFixed⟩ := conversion_witness_public_projection input ρ σ u v α hEq
  refine ⟨Λ, hΛ, ?_⟩
  intro x
  (try dsimp only)
  refine ⟨(Matrix.unitaryGroup _ ℂ).mul_mem
    (reflectionAbout_unitary (conversionLogicalProjector_orthogonal input x))
    (reflectionAbout_unitary hΛ), ?_, ?_⟩
  · rw [applyGate_mul, applyGate_reflectionAbout_of_fixed (hFixed x),
      applyGate_reflectionAbout_of_fixed (conversionLogicalProjector_fixedWitness input ρ σ v α x)]
  · rw [conversion_walk_forbidden_identity _ _ _ (hForbidden x),
      conversionLogicalProjector_forbidden input ρ σ u α x]

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
