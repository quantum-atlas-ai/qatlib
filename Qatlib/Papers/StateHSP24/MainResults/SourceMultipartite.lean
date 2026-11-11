/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateHSP24.MainResults.SourceSwapTest
import Qatlib.Papers.StateHSP24.MainResults.SourceSchmidtPurity

set_option backward.isDefEq.respectTransparency false

/-!
# StateHSP24 — purity across cuts and multi-copy SWAP testing

Bouland–Giurgica-Tiron–Wright, fixed arXiv:2410.12706v1, Section 2.4.

* **Proposition 5**: if `|ψ⟩ = |a⟩_C ⊗ |b⟩_{C̄}` and both factors are `ε`-far from
  product, then for any subset `S` the reduced state on `S` has purity `1` when
  `S = C` or `S = C̄`, and purity at most `1 - ε²` otherwise.
* **Corollary 4**: consequently the SWAP test on the qubits of `S` accepts with
  probability at most `1 - ε²/2` when `S ≠ C, C̄`.
* **Proposition 6**: repeating the test on `m` pairs amplifies the rejection to
  `exp(-ε² m / 2)`.

The four register types model the four pieces `X = C ∩ S`, `Y = C ∖ S`,
`Z = C̄ ∩ S` and `W = C̄ ∖ S`; the reduced state on `S = X ∪ Z` is obtained by
tracing out `Y` and `W`, and is shown to equal the tensor product of the two
partial traces `ψ_X` and `ψ_Z`.  The purity bounds then follow from the
`Fin`-level Proposition 2 of `SourceSchmidtPurity.lean`.

Everything is stated for actual finite matrices; `purityGen` is the real part of
`Tr(ρ²)` and the general SWAP operator is the honest permutation operator
`SWAP |i⟩|j⟩ = |j⟩|i⟩` on an arbitrary finite register.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Qatlib.Papers.StateHSP24.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators ComplexOrder

variable {x y z w : ℕ}

/-! ## Generic partial trace and purity -/

/-- The partial trace over the second factor of a bipartite matrix on `I × J`. -/
noncomputable def partialTraceGen {I J : Type*} [Fintype J]
    (A : Matrix (I × J) (I × J) ℂ) : Matrix I I ℂ :=
  fun i j => ∑ a : J, A (i, a) (j, a)

/-- On `Fin`-indexed bipartite matrices the generic partial trace is the frozen
`PartialTrace`. -/
theorem partialTraceGen_eq_partialTrace {D E : ℕ}
    (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    partialTraceGen A = PartialTrace A := rfl

/-- Partial trace preserves the scalar trace. -/
theorem trace_partialTraceGen {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (I × J) (I × J) ℂ) : (partialTraceGen A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceGen, Fintype.sum_prod_type]

/-- The generic purity `Tr(ρ²)` on an arbitrary finite index type. -/
noncomputable def purityGen {I : Type*} [Fintype I] (ρ : Matrix I I ℂ) : ℝ :=
  (Matrix.trace (ρ * ρ)).re

/-- The `Fin`-indexed `purity` is the generic purity. -/
theorem purity_eq_purityGen {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    purity ρ = purityGen ρ := rfl

/-- The trace of the outer product is the squared norm of the state. -/
theorem trace_outerProductGen {I : Type*} [Fintype I] (ψ : QState I) :
    (outerProduct ψ).trace = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ψ i * (starRingEnd ℂ) (ψ i) = ((‖ψ i‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The outer product of a state with itself is Hermitian. -/
theorem outerProduct_conjTranspose {I : Type*} [Fintype I] (ψ : QState I) :
    (outerProduct ψ)ᴴ = outerProduct ψ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, outerProduct_apply, RCLike.star_def, map_mul,
    starRingEnd_self_apply]
  ring

/-- Partial trace preserves Hermiticity. -/
theorem partialTraceGen_conjTranspose {I J : Type*} [Fintype J]
    (A : Matrix (I × J) (I × J) ℂ) (h : Aᴴ = A) :
    (partialTraceGen A)ᴴ = partialTraceGen A := by
  ext i j
  simp only [partialTraceGen, Matrix.conjTranspose_apply]
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hh := congrFun (congrFun h (i, a)) (j, a)
  simpa only [Matrix.conjTranspose_apply] using hh

/-- For a Hermitian matrix the trace of the square is the sum of the squared
norms of the entries. -/
theorem trace_mul_self_of_isHermitian {I : Type*} [Fintype I] (ρ : Matrix I I ℂ)
    (h : ρᴴ = ρ) :
    Matrix.trace (ρ * ρ) = ((∑ i, ∑ j, ‖ρ i j‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hji : ∀ i j : I, ρ j i = (starRingEnd ℂ) (ρ i j) := by
    intro i j
    have hh : starRingEnd ℂ (ρ j i) = ρ i j := by
      change star (ρ j i) = ρ i j
      exact congrFun (congrFun h i) j
    rw [← hh, starRingEnd_self_apply]
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrow : (ρ * ρ) i i = ∑ j, ((‖ρ i j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hji i j, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simpa only [Matrix.diag_apply, Complex.ofReal_sum] using hrow

/-- Purity of a Hermitian matrix as the sum of the squared norms of its entries. -/
theorem purityGen_eq_sum_normSq {I : Type*} [Fintype I] (ρ : Matrix I I ℂ)
    (h : ρᴴ = ρ) : purityGen ρ = ∑ i, ∑ j, ‖ρ i j‖ ^ 2 := by
  rw [purityGen, trace_mul_self_of_isHermitian ρ h, Complex.ofReal_re]

/-! ## The four-register model of a state separated by a cut -/

/-- The register permutation `(X × Y) × (Z × W) ≃ (X × Z) × (Y × W)` which moves
the two "inside the subset" factors `X` and `Z` to the front. -/
def middleSwap (x y z w : ℕ) :
    ((Fin x × Fin y) × (Fin z × Fin w)) ≃ ((Fin x × Fin z) × (Fin y × Fin w)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv p := by obtain ⟨⟨i, k⟩, ⟨l, m⟩⟩ := p; rfl
  right_inv q := by obtain ⟨⟨i, l⟩, ⟨k, m⟩⟩ := q; rfl

/-- Action of the inverse permutation, in coordinates. -/
theorem middleSwap_symm_apply (p : (Fin x × Fin z) × (Fin y × Fin w)) :
    (middleSwap x y z w).symm p = ((p.1.1, p.2.1), (p.1.2, p.2.2)) := rfl

/-- The joint density matrix of `|a⟩_{XY} ⊗ |b⟩_{ZW}`. -/
noncomputable def jointDensity (a : QState (Fin x × Fin y)) (b : QState (Fin z × Fin w)) :
    Matrix ((Fin x × Fin y) × (Fin z × Fin w)) ((Fin x × Fin y) × (Fin z × Fin w)) ℂ :=
  outerProduct (TensorState a b)

/-- The reduced state on the union `S = X ∪ Z`, obtained by tracing out `Y` and `W`. -/
noncomputable def cutReduced (a : QState (Fin x × Fin y)) (b : QState (Fin z × Fin w)) :
    Matrix (Fin x × Fin z) (Fin x × Fin z) ℂ :=
  partialTraceGen
    ((jointDensity a b).submatrix (middleSwap x y z w).symm (middleSwap x y z w).symm)

/-- The reduced state on `X ∪ Z` is the tensor product of the two partial traces
`ψ_X` and `ψ_Z`. -/
theorem cutReduced_eq_tensorGate (a : QState (Fin x × Fin y)) (b : QState (Fin z × Fin w)) :
    cutReduced a b = TensorGate (partialTraceGen (outerProduct a))
      (partialTraceGen (outerProduct b)) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [cutReduced, jointDensity, partialTraceGen, Matrix.submatrix_apply,
    outerProduct_apply, TensorState, tensorGate_apply, middleSwap_symm_apply,
    Fintype.sum_prod_type, star_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun yy _ => Finset.sum_congr rfl fun ww _ => ?_
  rw [map_mul]
  ring

/-- The trace of a Kronecker product factors over arbitrary finite indices. -/
theorem trace_tensorGate_gen {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    (TensorGate A B).trace = A.trace * B.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, tensorGate_apply]
  rw [Finset.sum_mul_sum]

/-- Purity multiplies over Kronecker products of Hermitian matrices. -/
theorem purityGen_tensorGate {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (P : Matrix I I ℂ) (Q : Matrix J J ℂ)
    (hP : Pᴴ = P) (hQ : Qᴴ = Q) :
    purityGen (TensorGate P Q) = purityGen P * purityGen Q := by
  rw [purityGen_eq_sum_normSq P hP, purityGen_eq_sum_normSq Q hQ, purityGen,
    tensorGate_mul, trace_tensorGate_gen,
    trace_mul_self_of_isHermitian P hP, trace_mul_self_of_isHermitian Q hQ,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The reduced density matrix of a normalized pure state has trace one. -/
theorem trace_cutReduced (a : QState (Fin x × Fin y)) (b : QState (Fin z × Fin w))
    (ha : Normalized a) (hb : Normalized b) : (cutReduced a b).trace = 1 := by
  have ha' : (∑ i, ‖a i‖ ^ 2) = 1 := ha
  have hb' : (∑ i, ‖b i‖ ^ 2) = 1 := hb
  rw [cutReduced_eq_tensorGate, trace_tensorGate_gen, trace_partialTraceGen,
    trace_partialTraceGen, trace_outerProductGen, trace_outerProductGen, ha', hb']
  norm_num

/-! ## Purity bounds (Proposition 5) -/

/-- The purity of the reduced state of a normalized bipartite pure state is at
most one. -/
theorem sum_schmidtLambda_sq_le_one (a : QState (Fin x × Fin y)) (ha : Normalized a) :
    ∑ j, schmidtΛ a j ^ 2 ≤ 1 := by
  have hsum : ∑ j, schmidtΛ a j = 1 := by
    have htr : Matrix.trace (gramMatrix a) = 1 := by
      rw [trace_gramMatrix]
      exact_mod_cast ha
    exact sum_eigenvalues_eq_one (gramMatrix a) (gramMatrix_posSemidef a) htr
  have hnn : ∀ j, 0 ≤ schmidtΛ a j := schmidtΛ_nonneg a
  calc ∑ j, schmidtΛ a j ^ 2 ≤ ∑ j, schmidtΛ a j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hle1 : schmidtΛ a j ≤ 1 := by
          rw [← hsum]
          exact Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ j)
        nlinarith [hnn j]
    _ = 1 := hsum

/-- The purity of the reduced state `ψ_X` computed from the Gram spectrum. -/
theorem purity_partialTrace_outerProduct (a : QState (Fin x × Fin y)) :
    purityGen (partialTraceGen (outerProduct a)) = ∑ j, schmidtΛ a j ^ 2 := by
  have h : partialTraceGen (outerProduct a) = PartialTrace (outerProduct a) := rfl
  rw [h, ← purity_eq_purityGen, purity, partialTrace_outerProduct_eq_gramMatrix,
    gramMatrix_eq_sum]
  exact trace_sq_spectral (fun j => schmidtΛ a j) (schmidtU a) (schmidtU_inner a)

/-- The reduced state of a normalized bipartite pure state has purity at most one. -/
theorem purity_partialTrace_le_one (a : QState (Fin x × Fin y)) (ha : Normalized a) :
    purityGen (partialTraceGen (outerProduct a)) ≤ 1 := by
  rw [purity_partialTrace_outerProduct]
  exact sum_schmidtLambda_sq_le_one a ha

/-- Reduced purities are nonnegative. -/
theorem purity_partialTrace_nonneg (a : QState (Fin x × Fin y)) :
    0 ≤ purityGen (partialTraceGen (outerProduct a)) := by
  rw [purity_partialTrace_outerProduct]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The purity of a pure normalized state is one (the `S = C` and `S = C̄` case
of Proposition 5). -/
theorem purity_outerProduct_of_normalized {I : Type*} [Fintype I] (ψ : QState I)
    (hψ : Normalized ψ) : purityGen (outerProduct ψ) = 1 := by
  rw [purityGen_eq_sum_normSq (outerProduct ψ) (outerProduct_conjTranspose ψ)]
  have hterm : ∀ i j : I, ‖(outerProduct ψ) i j‖ ^ 2 = ‖ψ i‖ ^ 2 * ‖ψ j‖ ^ 2 := by
    intro i j
    show ‖ψ i * (starRingEnd ℂ) (ψ j)‖ ^ 2 = ‖ψ i‖ ^ 2 * ‖ψ j‖ ^ 2
    rw [norm_mul, mul_pow, starRingEnd_apply, norm_star]
  simp only [hterm]
  have h : (∑ i, ‖ψ i‖ ^ 2) = 1 := hψ
  rw [← Finset.sum_mul_sum, h]
  norm_num

/-- **Proposition 5** (purity across different cuts), mixed case: if `|a⟩_{XY}` is
`ε`-far from every product state, then the reduced state of `|a⟩_{XY} ⊗ |b⟩_{ZW}`
on `X ∪ Z` has purity at most `1 - ε²`. -/
theorem proposition5_purity_le (a : QState (Fin x × Fin y))
    (b : QState (Fin z × Fin w)) (ha : Normalized a) (hb : Normalized b)
    (ε : ℝ) (hε : 0 ≤ ε) (hfar : FarFromProduct a ε) :
    purityGen (cutReduced a b) ≤ 1 - ε ^ 2 := by
  have hPA : partialTraceGen (outerProduct a) = PartialTrace (outerProduct a) := rfl
  have hPB : partialTraceGen (outerProduct b) = PartialTrace (outerProduct b) := rfl
  have hhermA : (PartialTrace (outerProduct a))ᴴ = PartialTrace (outerProduct a) :=
    partialTraceGen_conjTranspose _ (outerProduct_conjTranspose a)
  have hhermB : (PartialTrace (outerProduct b))ᴴ = PartialTrace (outerProduct b) :=
    partialTraceGen_conjTranspose _ (outerProduct_conjTranspose b)
  rw [cutReduced_eq_tensorGate, hPA, hPB]
  rw [purityGen_tensorGate _ _ hhermA hhermB]
  have hA : purityGen (PartialTrace (outerProduct a)) ≤ 1 - ε ^ 2 := by
    rw [← purity_eq_purityGen]
    exact proposition2_purity_bound a ha ε hε hfar
  have hA0 : 0 ≤ purityGen (PartialTrace (outerProduct a)) := purity_partialTrace_nonneg a
  have hB : purityGen (PartialTrace (outerProduct b)) ≤ 1 :=
    purity_partialTrace_le_one b hb
  calc purityGen (PartialTrace (outerProduct a)) * purityGen (PartialTrace (outerProduct b))
      ≤ purityGen (PartialTrace (outerProduct a)) :=
        mul_le_of_le_one_right hA0 hB
    _ ≤ 1 - ε ^ 2 := hA

/-! ## The SWAP test on an arbitrary finite register -/

/-- The SWAP operator `SWAP |i⟩|j⟩ = |j⟩|i⟩` on an arbitrary finite register. -/
def swapOpGen (I : Type*) [DecidableEq I] : Matrix (I × I) (I × I) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- `SWAP` is an involution. -/
theorem swapOpGen_mul_self {I : Type*} [Fintype I] [DecidableEq I] :
    swapOpGen I * swapOpGen I = 1 := by
  classical
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp only [swapOpGen, Matrix.one_apply, Prod.mk.injEq]
      by_cases h : i = k ∧ j = l
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · have h' : ¬(j = l ∧ i = k) := fun hh => h ⟨hh.2, hh.1⟩
        rw [if_neg h', if_neg h]
        simp
    · intro yy _ hy
      by_cases h : i = yy
      · exact absurd h.symm hy
      · simp [swapOpGen, h]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro xx _ hx
    by_cases h : j = xx
    · exact absurd h.symm hx
    · simp [swapOpGen, h]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `SWAP` is self-adjoint. -/
theorem swapOpGen_conjTranspose {I : Type*} [Fintype I] [DecidableEq I] :
    (swapOpGen I)ᴴ = swapOpGen I := by
  classical
  ext p q
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [Matrix.conjTranspose_apply, swapOpGen]
  by_cases h : k = j ∧ l = i
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, if_true, star_one]
  · have h' : ¬(i = l ∧ j = k) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨rfl, rfl⟩
    rw [if_neg h, if_neg h', star_zero]

/-- The projector `Π_SWAP = ½ (I + SWAP)` onto the symmetric subspace. -/
def swapProjectorGen (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix (I × I) (I × I) ℂ :=
  (1 / 2 : ℂ) • (1 + swapOpGen I)

/-- `Π_SWAP` is idempotent. -/
theorem swapProjectorGen_mul_self {I : Type*} [Fintype I] [DecidableEq I] :
    swapProjectorGen I * swapProjectorGen I = swapProjectorGen I := by
  have h : (1 + swapOpGen I) * (1 + swapOpGen I) = (2 : ℂ) • (1 + swapOpGen I) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, swapOpGen_mul_self]
    module
  rw [swapProjectorGen, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, smul_smul]
  norm_num

/-- `Π_SWAP` is self-adjoint, hence an orthogonal projector. -/
theorem swapProjectorGen_conjTranspose {I : Type*} [Fintype I] [DecidableEq I] :
    (swapProjectorGen I)ᴴ = swapProjectorGen I := by
  rw [swapProjectorGen, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, swapOpGen_conjTranspose]
  norm_num

/-- **Proposition 4**, general register: `Tr(SWAP · (A ⊗ B)) = Tr(A B)`. -/
theorem trace_swapOpGen_tensorGate {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) : (swapOpGen I * TensorGate A B).trace = (A * B).trace := by
  classical
  rw [Matrix.trace, Fintype.sum_prod_type]
  have hleft : ∀ i j : I, (swapOpGen I * TensorGate A B) (i, j) (i, j) = A j i * B i j := by
    intro i j
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single i]
      · simp only [swapOpGen, tensorGate_apply]
        simp
      · intro yy _ hy
        by_cases h : i = yy
        · exact absurd h.symm hy
        · simp [swapOpGen, h]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · intro xx _ hx
      by_cases h : j = xx
      · exact absurd h.symm hx
      · simp [swapOpGen, h]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [Matrix.diag_apply, hleft]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

/-- The swap-test acceptance trace `Tr(Π_SWAP · ρ^{⊗2})` on a general register. -/
def swapTestTraceGen (I : Type*) [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) : ℂ :=
  (swapProjectorGen I * TensorGate ρ ρ).trace

/-- **Corollary 3**, general register: for a density matrix the swap-test
acceptance trace is `½ + ½ Tr(ρ²)`. -/
theorem swapTestTraceGen_eq {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Matrix I I ℂ) (htr : ρ.trace = 1) :
    swapTestTraceGen I ρ = (1 / 2 : ℂ) + (1 / 2 : ℂ) * (ρ * ρ).trace := by
  rw [swapTestTraceGen, swapProjectorGen, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
    Matrix.trace_smul, Matrix.trace_add, trace_tensorGate_gen,
    trace_swapOpGen_tensorGate, htr]
  ring

/-- The acceptance probability of the swap test on a general register, as the real
part of the acceptance trace. -/
def swapAcceptProbGen (I : Type*) [Fintype I] [DecidableEq I]
    (ρ : Matrix I I ℂ) : ℝ := (swapTestTraceGen I ρ).re

/-- The acceptance probability is `½ + ½ Tr(ρ²)`. -/
theorem swapAcceptProbGen_eq {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Matrix I I ℂ) (htr : ρ.trace = 1) :
    swapAcceptProbGen I ρ = 1 / 2 + 1 / 2 * purityGen ρ := by
  unfold swapAcceptProbGen purityGen
  rw [swapTestTraceGen_eq ρ htr]
  have h : ((1 / 2 : ℂ) + (1 / 2 : ℂ) * (ρ * ρ).trace)
      = ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * (ρ * ρ).trace := by
    push_cast
    ring
  rw [h]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Corollary 4**: the SWAP test on the qubits of `S` accepts with probability
at most `1 - ε²/2` when `S ≠ C, C̄`. -/
theorem corollary4_acceptance_le (a : QState (Fin x × Fin y))
    (b : QState (Fin z × Fin w)) (ha : Normalized a) (hb : Normalized b)
    (ε : ℝ) (hε : 0 ≤ ε) (hfar : FarFromProduct a ε) :
    swapAcceptProbGen (Fin x × Fin z) (cutReduced a b) ≤ 1 - ε ^ 2 / 2 := by
  rw [swapAcceptProbGen_eq _ (trace_cutReduced a b ha hb)]
  have hp := proposition5_purity_le a b ha hb ε hε hfar
  linarith

/-! ## Multi-copy amplification (Proposition 6) -/

/-- **Proposition 6** (quantitative core): if each pair accepts with probability at
most `1 - ε²/2`, then `m` independent pairs accept with probability at most
`exp(-ε² m / 2)`. -/
theorem proposition6_mfold_acceptance_le (p ε : ℝ) (hε : 0 ≤ ε) (hp0 : 0 ≤ p)
    (hp : p ≤ 1 - ε ^ 2 / 2) (m : ℕ) :
    p ^ m ≤ Real.exp (-(ε ^ 2 * m / 2)) := by
  have hbase : 0 ≤ 1 - ε ^ 2 / 2 := le_trans hp0 hp
  have h1 : p ^ m ≤ (1 - ε ^ 2 / 2) ^ m := pow_le_pow_left₀ hp0 hp m
  have h2 : (1 - ε ^ 2 / 2) ^ m ≤ Real.exp (-(ε ^ 2 / 2)) ^ m :=
    pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (ε ^ 2 / 2)) m
  have h3 : Real.exp (-(ε ^ 2 / 2)) ^ m = Real.exp (-(ε ^ 2 * m / 2)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [h3] at h2
  exact le_trans h1 h2

end Qatlib.Papers.StateHSP24.MainResults
