/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Bridges between vectors, Euclidean states, and operators

This module relates function-valued `QState` vectors to `EuclideanSpace`, proving compatibility
of inner products, normalization, matrix action, and basis relabeling. Tensor associativity and
swaps are expressed by explicit index equivalences, while outer products connect normalized
vectors to density operators and partial traces [Watrous2018].

The norm comparisons distinguish the function-space supremum norm from the Euclidean state norm,
and identify `SchattenTwo` with the Frobenius norm while comparing it with
`OperatorSpectralNorm` [Bhatia1997].

## Main statements

* `normalized_iff_norm_toEuclidean_fromVec`: State normalization is equivalent to unit Euclidean
  norm.
* `bornDistribution_relabelState`: Relabeling a state pushes forward its Born distribution.
* `partialTrace_outerProduct_tensorState`: Tracing out a normalized tensor factor recovers the
  other outer product.
* `schattenTwo_le_operatorSpectralNorm`: The Schatten 2-norm is at most √D times the spectral
  norm.

## References

* [Watrous, 2018][Watrous2018]
* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.BornBridge

open Matrix

set_option linter.unusedSectionVars false

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- View a function-valued finite state as a vector in complex Euclidean space using the ℓ²
wrapper. -/
def toEuclidean_fromVec (v : QState I) : EuclideanSpace ℂ I := WithLp.toLp 2 v

/-- Recover the function-valued state underlying a complex Euclidean vector. -/
def toVec_fromEuclidean (x : EuclideanSpace ℂ I) : QState I := WithLp.ofLp x

/-- Conversion from a state to Euclidean space preserves each coordinate. -/
@[simp] theorem toEuclidean_fromVec_apply (v : QState I) (i : I) :
    toEuclidean_fromVec v i = v i := rfl

/-- Conversion from Euclidean space to a state preserves each coordinate. -/
@[simp] theorem toVec_fromEuclidean_apply (x : EuclideanSpace ℂ I) (i : I) :
    toVec_fromEuclidean x i = x i := rfl

/-- Converting a state to Euclidean space and back yields the original state. -/
theorem toVec_fromEuclidean_toEuclidean_fromVec (v : QState I) :
    toVec_fromEuclidean (toEuclidean_fromVec v) = v := rfl

/-- Converting a Euclidean vector to a state and back yields the original vector. -/
theorem toEuclidean_fromVec_toVec_fromEuclidean (x : EuclideanSpace ℂ I) :
    toEuclidean_fromVec (toVec_fromEuclidean x) = x := rfl

/-- The Euclidean inner product of converted states equals their Qatlib inner product `Inner`. -/
theorem inner_euclidean_fromVec (ψ φ : QState I) :
    inner ℂ (toEuclidean_fromVec ψ) (toEuclidean_fromVec φ) = Inner ψ φ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The squared Euclidean norm of a converted state is the sum of the squared norms of its
amplitudes. -/
theorem norm_toEuclidean_fromVec_sq (v : QState I) :
    ‖toEuclidean_fromVec v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The squared Euclidean norm of a converted state equals the real part of its self-inner
product. -/
theorem norm_toEuclidean_sq_eq_re_inner (v : QState I) :
    ‖toEuclidean_fromVec v‖ ^ 2 = (Inner v v).re := by
  rw [norm_toEuclidean_fromVec_sq, inner_self, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- A state is normalized exactly when its Euclidean representation has norm one. -/
theorem normalized_iff_norm_toEuclidean_fromVec (v : QState I) :
    Normalized v ↔ ‖toEuclidean_fromVec v‖ = 1 := by
  constructor
  · intro hψ
    have hs : ∑ i, ‖v i‖ ^ 2 = 1 := hψ
    have h2 : ‖toEuclidean_fromVec v‖ ^ 2 = 1 := by rw [norm_toEuclidean_fromVec_sq, hs]
    rcases _root_.sq_eq_one_iff (a := ‖toEuclidean_fromVec v‖) |>.mp h2 with h | h
    · exact h
    · exact absurd h (by have := norm_nonneg (toEuclidean_fromVec v); linarith)
  · intro h
    show ∑ i, ‖v i‖ ^ 2 = 1
    rw [← norm_toEuclidean_fromVec_sq, h, one_pow]

/-- The continuous linear map associated with a matrix acts on Euclidean state representations
exactly as `ApplyGate` acts on the original states. -/
theorem toEuclideanCLM_applyGate (U : Matrix I I ℂ) (ψ : QState I) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U (toEuclidean_fromVec ψ)
      = toEuclidean_fromVec (ApplyGate U ψ) := by
  have h : WithLp.ofLp ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U (toEuclidean_fromVec ψ))
      = WithLp.ofLp (toEuclidean_fromVec (ApplyGate U ψ)) := by
    rw [Matrix.ofLp_toEuclideanCLM]
    rfl
  exact WithLp.ofLp_injective 2 h

/-- The continuous linear map associated with a unitary matrix preserves the Euclidean norm of
every vector. -/
theorem norm_toEuclideanCLM_of_mem_unitaryGroup {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (x : EuclideanSpace ℂ I) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U x‖ = ‖x‖ := by
  have hinner : inner ℂ ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U x)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U x) = inner ℂ x x := by
    have hx : x = toEuclidean_fromVec (WithLp.ofLp x) := rfl
    rw [hx, toEuclideanCLM_applyGate, inner_euclidean_fromVec, inner_applyGate hU,
      ← inner_euclidean_fromVec, ← hx]
  have h1 := norm_sq_eq_re_inner (𝕜 := ℂ)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U x)
  have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) x
  have hsq : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [h1, h2, hinner]
  calc ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U x‖
      = Real.sqrt (‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix I I ℂ ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) U x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- The inner product of `u` with the matrix action on `v` is the double sum of conjugated
coordinates of `u` times the matrix entries and coordinates of `v`. -/
theorem inner_toEuclideanLin (M : Matrix I I ℂ) (u v : EuclideanSpace ℂ I) :
    inner ℂ u (Matrix.toEuclideanLin M v) = ∑ x, ∑ y, (starRingEnd ℂ) (u x) * (M x y * v y) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hmul : (Matrix.toEuclideanLin M v) x = ∑ y, M x y * v y := rfl
  rw [hmul, inner_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [RCLike.inner_apply]; ring

/-- The function-space supremum norm of the two-coordinate state `(1, 1)` equals one. -/
theorem piSupNorm_two_dim : ‖(![1, 1] : QState (Fin 2))‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    fin_cases i <;> norm_num
  · have h := norm_le_pi_norm (![1, 1] : QState (Fin 2)) 0
    simpa using h

/-- The Euclidean ℓ² norm of the two-coordinate state `(1, 1)` equals √2. -/
theorem euclideanL2Norm_two_dim :
    ‖toEuclidean_fromVec (![1, 1] : QState (Fin 2))‖ = Real.sqrt 2 := by
  have h : ∀ i : Fin 2, ‖(![1, 1] : QState (Fin 2)) i‖ ^ 2 = 1 := by
    intro i; fin_cases i <;> norm_num
  have hsq : ‖toEuclidean_fromVec (![1, 1] : QState (Fin 2))‖ ^ 2 = 2 := by
    rw [norm_toEuclidean_fromVec_sq, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    norm_num
  calc ‖toEuclidean_fromVec (![1, 1] : QState (Fin 2))‖
      = Real.sqrt (‖toEuclidean_fromVec (![1, 1] : QState (Fin 2))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 2 := by rw [hsq]

/-- The two-coordinate state `(1, 1)` has different function-space supremum and Euclidean ℓ²
norms. -/
theorem piSupNorm_ne_euclideanL2Norm :
    ‖(![1, 1] : QState (Fin 2))‖ ≠ ‖toEuclidean_fromVec (![1, 1] : QState (Fin 2))‖ := by
  rw [piSupNorm_two_dim, euclideanL2Norm_two_dim]
  intro h
  have hsq : ((1 : ℝ) ^ 2) = (Real.sqrt 2) ^ 2 := congrArg (fun x : ℝ => x ^ 2) h
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
  norm_num at hsq

/-- For the state `(1, 1)`, the squared function-space supremum norm differs from the real part
of its Qatlib self-inner product. -/
theorem piSupNorm_sq_ne_re_inner :
    ‖(![1, 1] : QState (Fin 2))‖ ^ 2 ≠ (Inner (![1, 1] : QState (Fin 2)) (![1, 1])).re := by
  rw [piSupNorm_two_dim, ← norm_toEuclidean_sq_eq_re_inner, euclideanL2Norm_two_dim]
  norm_num

/-- Relabel a state's basis along an equivalence by precomposing its amplitudes with the inverse
equivalence. -/
def relabelState (e : I ≃ J) (v : QState I) : QState J := v ∘ e.symm

/-- Relabel both row and column indices of a matrix along the same equivalence. -/
def relabelGate (e : I ≃ J) (U : Matrix I I ℂ) : Matrix J J ℂ := Matrix.reindex e e U

/-- The amplitude of a relabeled state at `j` is the original amplitude at `e.symm j`. -/
theorem relabelState_apply (e : I ≃ J) (v : QState I) (j : J) :
    relabelState e v j = v (e.symm j) := rfl

/-- Relabeling a state by an equivalence and then its inverse recovers the state. -/
theorem relabelState_relabelState (e : I ≃ J) (v : QState I) :
    relabelState e.symm (relabelState e v) = v := by
  funext i
  show v (e.symm (e.symm.symm i)) = v i
  rw [Equiv.symm_symm, Equiv.symm_apply_apply]

/-- Relabeling a matrix by an equivalence and then its inverse recovers the matrix. -/
theorem relabelGate_relabelGate (e : I ≃ J) (U : Matrix I I ℂ) :
    relabelGate e.symm (relabelGate e U) = U := by
  ext i j
  show (U.submatrix e.symm e.symm).submatrix e.symm.symm e.symm.symm i j = U i j
  rw [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id]

/-- Applying a relabeled gate to a relabeled state equals relabeling the original gate action. -/
theorem applyGate_relabelGate (e : I ≃ J) (U : Matrix I I ℂ) (v : QState I) :
    ApplyGate (relabelGate e U) (relabelState e v) = relabelState e (ApplyGate U v) := by
  funext i
  simp only [ApplyGate, relabelGate, relabelState, Matrix.reindex_apply, Matrix.mulVec,
    dotProduct]
  exact e.symm.sum_comp fun k => U (e.symm i) k * v k

/-- Relabeling both states by the same basis equivalence preserves their Qatlib inner product. -/
theorem inner_relabelState (e : I ≃ J) (v w : QState I) :
    Inner (relabelState e v) (relabelState e w) = Inner v w := by
  rw [inner_apply, inner_apply]
  exact e.symm.sum_comp fun k => (starRingEnd ℂ) (v k) * w k

/-- The Qatlib inner product is conjugate symmetric. -/
theorem inner_conj_symm (ψ φ : QState I) :
    Inner ψ φ = (starRingEnd ℂ) (Inner φ ψ) := by
  rw [inner_apply, inner_apply,
    show (∑ i, (starRingEnd ℂ) (ψ i) * φ i)
      = (starRingEnd ℂ) (∑ i, (starRingEnd ℂ) (φ i) * ψ i) from by
      rw [map_sum (starRingEnd ℂ) (fun i => (starRingEnd ℂ) (φ i) * ψ i) Finset.univ]
      exact Finset.sum_congr rfl fun i _ => by
        have h : (starRingEnd ℂ) ((starRingEnd ℂ) (φ i)) = φ i := star_star (φ i)
        rw [map_mul, h]
        ring]

/-- Relabeling the basis of a normalized state preserves normalization. -/
theorem normalized_relabelState (e : I ≃ J) {v : QState I} (h : Normalized v) :
    Normalized (relabelState e v) := by
  rw [normalized_iff_inner_self, inner_relabelState]
  exact (normalized_iff_inner_self v).1 h

/-- The Born probability at a relabeled basis index equals the original probability at the
inverse image of that index. -/
@[simp] theorem bornProb_relabelState (e : I ≃ J) (v : QState I) (j : J) :
    BornProb (relabelState e v) j = BornProb v (e.symm j) := rfl

/-- Relabeling a state and its finite measurement event by the same equivalence preserves the
event probability. -/
theorem measureProb_relabelState (e : I ≃ J) (v : QState I) (S : Finset I) :
    MeasureProb (relabelState e v) (S.map e) = MeasureProb v S := by
  unfold MeasureProb
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  show BornProb v (e.symm (e i)) = BornProb v i
  rw [Equiv.symm_apply_apply]

/-- The Born distribution of a relabeled normalized state is the pushforward of the original
Born distribution along the basis equivalence. -/
theorem bornDistribution_relabelState (e : I ≃ J) (ψ : QState I) (hψ : Normalized ψ) :
    bornDistribution (relabelState e ψ) (normalized_relabelState e hψ)
      = PMF.map e (bornDistribution ψ hψ) := by
  ext b
  rw [PMF.map_apply, bornDistribution_apply, tsum_eq_single (e.symm b)]
  · rw [if_pos (Equiv.apply_symm_apply e b).symm, bornDistribution_apply]
    rfl
  · intro a ha
    refine if_neg ?_
    intro hba
    exact ha (by rw [hba, Equiv.symm_apply_apply])

/-- Relabeling a tensor state by a product equivalence is the tensor product of the separately
relabeled states. -/
theorem relabelState_prodCongr {I' J' : Type*} [Fintype I'] [DecidableEq I'] [Fintype J']
    [DecidableEq J'] (e : I ≃ I') (f : J ≃ J') (u : QState I) (v : QState J) :
    relabelState (Equiv.prodCongr e f) (TensorState u v)
      = TensorState (relabelState e u) (relabelState f v) := by
  funext p
  simp only [relabelState, Equiv.prodCongr_symm, Equiv.prodCongr_apply, TensorState]
  rfl

/-- Relabeling a tensor gate by a product equivalence is the tensor product of the separately
relabeled gates. -/
theorem relabelGate_prodCongr {I' J' : Type*} [Fintype I'] [DecidableEq I'] [Fintype J']
    [DecidableEq J'] (e : I ≃ I') (f : J ≃ J') (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    relabelGate (Equiv.prodCongr e f) (TensorGate U V)
      = TensorGate (relabelGate e U) (relabelGate f V) := by
  ext ⟨i', j'⟩ ⟨k', l'⟩
  simp only [relabelGate, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, TensorGate, Matrix.kronecker_apply]
  rfl

/-- Reassociating the product index of a three-factor tensor state gives the corresponding
right-associated tensor state. -/
theorem relabelState_prodAssoc (u : QState I) (v : QState J) (w : QState K) :
    relabelState (Equiv.prodAssoc I J K) (TensorState (TensorState u v) w)
      = TensorState u (TensorState v w) := by
  funext p
  show (TensorState (TensorState u v) w) ((Equiv.prodAssoc I J K).symm p)
      = u p.1 * (v p.2.1 * w p.2.2)
  have hp : (Equiv.prodAssoc I J K).symm p = ((p.1, p.2.1), p.2.2) := rfl
  rw [hp]
  simp only [TensorState]
  ring

/-- Reassociating the product index of a three-factor tensor gate gives the corresponding
right-associated tensor gate. -/
theorem relabelGate_prodAssoc (U : Matrix I I ℂ) (V : Matrix J J ℂ) (W : Matrix K K ℂ) :
    relabelGate (Equiv.prodAssoc I J K) (TensorGate (TensorGate U V) W)
      = TensorGate U (TensorGate V W) := by
  ext p q
  obtain ⟨i, ⟨j, k⟩⟩ := p
  obtain ⟨i', ⟨j', k'⟩⟩ := q
  have hp : (Equiv.prodAssoc I J K).symm (i, (j, k)) = ((i, j), k) := rfl
  have hp' : (Equiv.prodAssoc I J K).symm (i', (j', k')) = ((i', j'), k') := rfl
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, hp, hp', TensorGate,
    Matrix.kronecker_apply]
  ring

/-- Swapping the product indices of a tensor state interchanges its two tensor factors. -/
theorem relabelState_prodComm (u : QState I) (v : QState J) :
    relabelState (Equiv.prodComm I J) (TensorState u v) = TensorState v u := by
  funext p
  have hp : (Equiv.prodComm I J).symm p = (p.2, p.1) := rfl
  show (TensorState u v) ((Equiv.prodComm I J).symm p) = v p.1 * u p.2
  rw [hp]
  simp only [TensorState]
  ring

/-- Swapping the product indices of a tensor gate interchanges its two tensor factors. -/
theorem relabelGate_prodComm (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    relabelGate (Equiv.prodComm I J) (TensorGate U V) = TensorGate V U := by
  ext ⟨j, i⟩ ⟨l, k⟩
  have h1 : (Equiv.prodComm J I) (j, i) = (i, j) := rfl
  have h2 : (Equiv.prodComm J I) (l, k) = (k, l) := rfl
  simp only [relabelGate, Equiv.prodComm_symm, Matrix.reindex_apply, Matrix.submatrix_apply,
    h1, h2, TensorGate, Matrix.kronecker_apply]
  ring

/-- After reassociating indices, applying three tensor-product gates to three tensor-product
states equals the tensor product of the three separate gate actions. -/
theorem applyGate_tensorGate_prodAssoc (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (W : Matrix K K ℂ) (u : QState I) (v : QState J) (w : QState K) :
    relabelState (Equiv.prodAssoc I J K)
        (ApplyGate (TensorGate (TensorGate U V) W) (TensorState (TensorState u v) w))
      = TensorState (ApplyGate U u) (TensorState (ApplyGate V v) (ApplyGate W w)) := by
  rw [applyGate_tensorGate, applyGate_tensorGate, relabelState_prodAssoc]

/-- After swapping indices, applying a two-factor tensor gate to a tensor state equals the
tensor product of the two separate gate actions in reversed order. -/
theorem applyGate_tensorGate_prodComm (U : Matrix I I ℂ) (V : Matrix J J ℂ)
    (u : QState I) (v : QState J) :
    relabelState (Equiv.prodComm I J) (ApplyGate (TensorGate U V) (TensorState u v))
      = TensorState (ApplyGate V v) (ApplyGate U u) := by
  rw [applyGate_tensorGate, relabelState_prodComm]

/-- The outer product of any finite state vector is Hermitian. -/
theorem outerProduct_isHermitian (ψ : QState I) : (outerProduct ψ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, outerProduct, Matrix.of_apply, RCLike.star_def,
    map_mul]
  have h : (starRingEnd ℂ) ((starRingEnd ℂ) (ψ i)) = ψ i := star_star (ψ i)
  rw [h]
  ring

open scoped ComplexOrder in

/-- The outer product of any finite state vector is positive semidefinite. -/
theorem outerProduct_posSemidef (ψ : QState I) : (outerProduct ψ).PosSemidef := by
  refine ⟨outerProduct_isHermitian ψ, ?_⟩
  intro x
  have hz : ∀ i : I,
      (x.sum fun j xj => star ((0 : ℂ)) * outerProduct ψ i j * xj) = 0 := by
    intro i
    show (∑ j ∈ x.support, star ((0 : ℂ)) * outerProduct ψ i j * x j) = 0
    exact Finset.sum_eq_zero fun j _ => by simp
  have hout : (x.sum fun i xi => x.sum fun j xj => star xi * outerProduct ψ i j * xj)
      = ∑ i : I, ∑ j : I, star (x i) * (ψ i * star (ψ j)) * x j := by
    have h1 : ∀ i : I,
        (x.sum fun j xj => star (x i) * outerProduct ψ i j * xj)
          = ∑ j : I, star (x i) * (ψ i * star (ψ j)) * x j := by
      intro i
      rw [Finsupp.sum_fintype x
        (fun j xj => star (x i) * outerProduct ψ i j * xj) (fun _ => by simp)]
      exact Finset.sum_congr rfl fun j _ => by rw [outerProduct_apply]; rfl
    rw [Finsupp.sum_fintype x
      (fun i xi => x.sum fun j xj => star xi * outerProduct ψ i j * xj) hz]
    exact Finset.sum_congr rfl fun i _ => h1 i
  rw [hout]
  have hreg : ∑ i : I, ∑ j : I, star (x i) * (ψ i * star (ψ j)) * x j
      = ∑ i : I, ∑ j : I, (star (x i) * ψ i) * (star (ψ j) * x j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hreg, ← Finset.sum_mul_sum]
  have hfirst : (∑ i : I, star (x i) * ψ i)
      = (starRingEnd ℂ) (∑ j : I, star (ψ j) * x j) := by
    rw [map_sum (starRingEnd ℂ) (fun j => star (ψ j) * x j) Finset.univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    show star (x i) * ψ i = (starRingEnd ℂ) (star (ψ i) * x i)
    rw [map_mul]
    have h : (starRingEnd ℂ) (star (ψ i)) = ψ i := star_star (ψ i)
    rw [h]
    show star (x i) * ψ i = ψ i * star (x i)
    ring
  rw [hfirst]
  have hval : (starRingEnd ℂ) (∑ j : I, star (ψ j) * x j) * (∑ j : I, star (ψ j) * x j)
      = ((Complex.normSq (∑ j : I, star (ψ j) * x j) : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  rw [hval, Complex.nonneg_iff]
  exact ⟨Complex.normSq_nonneg _, rfl⟩

/-- The trace of a state's outer product is the sum of its squared amplitude norms, embedded in
the complex numbers. -/
theorem trace_outerProduct (ψ : QState I) :
    Matrix.trace (outerProduct ψ) = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ i : I, ψ i * (starRingEnd ℂ) (ψ i) = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ψ i * (starRingEnd ℂ) (ψ i) = ((‖ψ i‖ ^ 2 : ℝ) : ℂ)
  exact hterm i

open scoped ComplexOrder in

/-- The outer product of a normalized state is positive semidefinite and has trace one. -/
theorem outerProduct_density {ψ : QState I} (hψ : Normalized ψ) :
    (outerProduct ψ).PosSemidef ∧ Matrix.trace (outerProduct ψ) = 1 :=
  ⟨outerProduct_posSemidef ψ, by rw [trace_outerProduct]; exact_mod_cast hψ⟩

variable {D E : ℕ}

/-- The outer product of a normalized finite-dimensional state satisfies `IsDensityOperator`. -/
theorem isDensityOperator_outerProduct {ψ : QState (Fin D)} (hψ : Normalized ψ) :
    IsDensityOperator (outerProduct ψ) :=
  ⟨(outerProduct_density hψ).1, (outerProduct_density hψ).2⟩

/-- The outer product of a tensor state equals the tensor product of the two outer products. -/
theorem outerProduct_tensorState (ψ : QState I) (φ : QState J) :
    outerProduct (TensorState ψ φ) = TensorGate (outerProduct ψ) (outerProduct φ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [outerProduct_apply, TensorState, TensorGate, Matrix.kronecker_apply, map_mul]
  ring

/-- Summing over the second subsystem of a tensor state's outer product gives the first outer
product multiplied by the squared Euclidean norm of the second state. -/
theorem sum_outerProduct_tensorState (ψ : QState I) (φ : QState J) (i j : I) :
    ∑ a : J, outerProduct (TensorState ψ φ) (i, a) (j, a)
      = outerProduct ψ i j * ((∑ a, ‖φ a‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ a : J, outerProduct (TensorState ψ φ) (i, a) (j, a)
      = (ψ i * (starRingEnd ℂ) (ψ j)) * (φ a * (starRingEnd ℂ) (φ a)) := by
    intro a
    show ψ i * φ a * (starRingEnd ℂ) (ψ j * φ a)
        = ψ i * (starRingEnd ℂ) (ψ j) * (φ a * (starRingEnd ℂ) (φ a))
    rw [map_mul]
    ring
  have hterm2 : ∀ a : J, φ a * (starRingEnd ℂ) (φ a) = ((‖φ a‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum]
  have h1 : ψ i * (starRingEnd ℂ) (ψ j) = outerProduct ψ i j := rfl
  have h2 : (∑ a : J, φ a * (starRingEnd ℂ) (φ a))
      = ((∑ a : J, ‖φ a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun a _ => hterm2 a
  rw [h1, h2]

/-- Tracing out the second factor of a matrix tensor product gives the first factor scaled by
the trace of the second. -/
theorem partialTrace_tensorGate (ρ : Operator D) (σ : Matrix (Fin E) (Fin E) ℂ) :
    PartialTrace (TensorGate ρ σ) = (Matrix.trace σ) • ρ := by
  ext i j
  have hentry : ∀ a : Fin E, TensorGate ρ σ (i, a) (j, a) = ρ i j * σ a a := fun a => rfl
  show (∑ a : Fin E, ρ i j * σ a a) = (Matrix.trace σ) * ρ i j
  rw [← Finset.mul_sum, mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply]

/-- Tracing out a tensor factor that is an outer product scales the first matrix by the sum of
the second state's squared amplitude norms. -/
theorem partialTrace_tensorGate_outerProduct (ρ : Operator D) (φ : QState (Fin E)) :
    PartialTrace (TensorGate ρ (outerProduct φ)) = ((∑ a, ‖φ a‖ ^ 2 : ℝ) : ℂ) • ρ := by
  rw [partialTrace_tensorGate, trace_outerProduct]

/-- If the second tensor-state factor is normalized, tracing it out of the tensor state's outer
product gives the first state's outer product. -/
theorem partialTrace_outerProduct_tensorState (ψ : QState (Fin D)) {φ : QState (Fin E)}
    (hφ : Normalized φ) :
    PartialTrace (outerProduct (TensorState ψ φ)) = outerProduct ψ := by
  rw [outerProduct_tensorState, partialTrace_tensorGate_outerProduct, hφ]
  have h1 : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [h1, one_smul]

/-- Tensoring a matrix with a normalized state's outer product and tracing out that state
recovers the matrix. -/
theorem partialTrace_tensorGate_outerProduct_normalized (ρ : Operator D) {φ : QState (Fin E)}
    (hφ : Normalized φ) :
    PartialTrace (TensorGate ρ (outerProduct φ)) = ρ := by
  rw [partialTrace_tensorGate_outerProduct, hφ]
  have h1 : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [h1, one_smul]

/-- The Schatten 2-norm of a finite operator is the square root of the sum of squared entry
norms. -/
theorem schattenTwo_eq (A : Operator D) :
    SchattenTwo A = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  have hterm : ∀ i : Fin D, (A.conjTranspose * A) i i = ((∑ j, ‖A j i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have h : ∀ j : Fin D, (starRingEnd ℂ) (A j i) * A j i = ((‖A j i‖ ^ 2 : ℝ) : ℂ) := by
      intro j
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    calc (A.conjTranspose * A) i i = ∑ j, (starRingEnd ℂ) (A j i) * A j i := by
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      _ = ((∑ j, ‖A j i‖ ^ 2 : ℝ) : ℂ) := by
          rw [show (∑ j, (starRingEnd ℂ) (A j i) * A j i)
              = ∑ j, ((‖A j i‖ ^ 2 : ℝ) : ℂ) from
              Finset.sum_congr rfl (fun j _ => h j), ← Complex.ofReal_sum]
  have hre : (Matrix.trace (A.conjTranspose * A)).re = ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, hterm, Complex.ofReal_sum, Complex.re_sum,
      Complex.ofReal_re]
  rw [SchattenTwo, hre]
  have hcomm : (∑ i, ∑ j : Fin D, ‖A j i‖ ^ 2) = (∑ i, ∑ j : Fin D, ‖A i j‖ ^ 2) := by
    rw [← Fintype.sum_prod_type' (fun (i j : Fin D) => ‖A j i‖ ^ 2),
      ← Fintype.sum_prod_type' (fun (i j : Fin D) => ‖A i j‖ ^ 2)]
    exact Equiv.sum_comp (Equiv.prodComm (Fin D) (Fin D))
      (fun p : Fin D × Fin D => ‖A p.1 p.2‖ ^ 2)
  exact congrArg Real.sqrt hcomm

open scoped Matrix.Norms.Frobenius in

/-- The Schatten 2-norm equals the matrix Frobenius norm under the Frobenius norm scope. -/
theorem schattenTwo_eq_frobeniusNorm (A : Operator D) : SchattenTwo A = ‖A‖ := by
  rw [schattenTwo_eq, Matrix.frobenius_norm_def A]
  refine (Real.sqrt_eq_rpow _).trans ?_
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    (Real.rpow_natCast (‖A i j‖) 2).symm

open scoped Matrix.Norms.L2Operator in

/-- The induced ℓ² matrix operator norm equals `OperatorSpectralNorm`. -/
theorem l2OpNorm_eq_operatorSpectralNorm (A : Operator D) :
    (‖A‖ : ℝ) = OperatorSpectralNorm A := by
  rw [Matrix.l2_opNorm_def]
  rfl

/-- The Schatten 2-norm of a dimension-`D` operator is at most √D times its spectral norm. -/
theorem schattenTwo_le_operatorSpectralNorm (A : Operator D) :
    SchattenTwo A
      ≤ Real.sqrt (Fintype.card (Fin D)) * OperatorSpectralNorm A := by
  have hop := operatorSpectralNorm_nonneg A
  have hcol : ∀ j : Fin D, ∑ i, ‖A i j‖ ^ 2 ≤ OperatorSpectralNorm A ^ 2 := by
    intro j
    have hact : ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin D) (Fin D) ℂ ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) A)
        (PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) : EuclideanSpace ℂ (Fin D))
        = (WithLp.toLp 2 (A *ᵥ Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin D)) :=
      Matrix.toEuclideanCLM_toLp A (Pi.single j (1 : ℂ))
    have hnormx : ‖(PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) :
        EuclideanSpace ℂ (Fin D))‖ = 1 := by
      rw [PiLp.norm_single 2 (fun _ : Fin D => ℂ) j (1 : ℂ)]
      norm_num
    have hle : ‖((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin D) (Fin D) ℂ ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) A)
        (PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) : EuclideanSpace ℂ (Fin D))‖
        ≤ OperatorSpectralNorm A
          * ‖(PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) :
              EuclideanSpace ℂ (Fin D))‖ :=
      ContinuousLinearMap.le_opNorm
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin D) (Fin D) ℂ ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) A)
        (PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) : EuclideanSpace ℂ (Fin D))
    have hentries : ∀ i : Fin D, (A *ᵥ Pi.single j (1 : ℂ)) i = A i j := by
      intro i
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    have hsq : ‖((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin D) (Fin D) ℂ ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) A)
        (PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) : EuclideanSpace ℂ (Fin D))‖ ^ 2
        = ∑ i, ‖A i j‖ ^ 2 := by
      rw [hact, EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => by rw [PiLp.toLp_apply, hentries i]
    calc ∑ i, ‖A i j‖ ^ 2
        = ‖((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin D) (Fin D) ℂ ≃⋆ₐ[ℂ]
            (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) A)
            (PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) :
              EuclideanSpace ℂ (Fin D))‖ ^ 2 := hsq.symm
      _ ≤ (OperatorSpectralNorm A
            * ‖(PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) :
                EuclideanSpace ℂ (Fin D))‖) ^ 2 := by
          have h1 := norm_nonneg (((Matrix.toEuclideanCLM (𝕜 := ℂ) :
              Matrix (Fin D) (Fin D) ℂ ≃⋆ₐ[ℂ]
              (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) A)
            (PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) :
              EuclideanSpace ℂ (Fin D)))
          have h2 : 0 ≤ OperatorSpectralNorm A
              * ‖(PiLp.single 2 (β := fun _ : Fin D => ℂ) j (1 : ℂ) :
                  EuclideanSpace ℂ (Fin D))‖ := mul_nonneg hop (norm_nonneg _)
          nlinarith [hle, h1, h2]
      _ = OperatorSpectralNorm A ^ 2 := by rw [hnormx, mul_one]
  have htotal : (∑ j, ∑ i, ‖A i j‖ ^ 2)
      ≤ Fintype.card (Fin D) * OperatorSpectralNorm A ^ 2 := by
    calc ∑ j, ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _j : Fin D, OperatorSpectralNorm A ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = Fintype.card (Fin D) * OperatorSpectralNorm A ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc SchattenTwo A = Real.sqrt (∑ j, ∑ i, ‖A i j‖ ^ 2) := by
        rw [schattenTwo_eq, Finset.sum_comm]
    _ ≤ Real.sqrt (Fintype.card (Fin D) * OperatorSpectralNorm A ^ 2) :=
        Real.sqrt_le_sqrt htotal
    _ = Real.sqrt (Fintype.card (Fin D)) * OperatorSpectralNorm A := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hop]

/-- The Schatten 2-norm of the two-dimensional identity is √2. -/
theorem schattenTwo_one_two : SchattenTwo (1 : Operator 2) = Real.sqrt 2 := by
  rw [schattenTwo_eq]
  have h00 : ‖((1 : Operator 2) (0 : Fin 2) (0 : Fin 2))‖ ^ 2 = 1 := by
    rw [Matrix.one_apply_eq]; norm_num
  have h11 : ‖((1 : Operator 2) (1 : Fin 2) (1 : Fin 2))‖ ^ 2 = 1 := by
    rw [Matrix.one_apply_eq]; norm_num
  have h01 : ‖((1 : Operator 2) (0 : Fin 2) (1 : Fin 2))‖ ^ 2 = 0 := by
    rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]; norm_num
  have h10 : ‖((1 : Operator 2) (1 : Fin 2) (0 : Fin 2))‖ ^ 2 = 0 := by
    rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]; norm_num
  simp only [Fin.sum_univ_two, h00, h01, h10, h11]
  norm_num

open scoped Matrix.Norms.L2Operator in

/-- In nonzero dimension, the spectral norm of the identity is one. -/
theorem operatorSpectralNorm_one [Nonempty (Fin D)] :
    OperatorSpectralNorm (1 : Operator D) = 1 := by
  have h1 : (1 : Operator D) = Matrix.diagonal (fun _ => (1 : ℂ)) := by
    rw [Matrix.diagonal_one]
  rw [← l2OpNorm_eq_operatorSpectralNorm, h1, Matrix.l2_opNorm_diagonal]
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    simp
  · obtain ⟨i⟩ := ‹Nonempty (Fin D)›
    simp

/-- The two-dimensional identity has distinct Schatten 2-norm and spectral norm. -/
theorem schattenTwo_ne_operatorSpectralNorm :
    SchattenTwo (1 : Operator 2) ≠ OperatorSpectralNorm (1 : Operator 2) := by
  rw [schattenTwo_one_two, operatorSpectralNorm_one]
  intro h
  rw [Real.sqrt_eq_one] at h
  norm_num at h

end Qatlib.Foundations.PureStateMath.BornBridge
