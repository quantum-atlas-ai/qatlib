/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatrixProd07.MainResults.Defs
import Qatlib.Papers.MatrixProd07.MainResults.Appendix
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork
import Mathlib.Topology.Order.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Translation invariant canonical forms and block algebra

The module defines cyclic symmetry predicates and propositions describing site independent
representations, canonical reductions, periodic decompositions, and uniqueness. These
propositions are accompanied by concrete matrix lemmas for word products, cut matrix
factorizations, and block decompositions.

`proposition1_cutRank` proves the cut rank formula under spanning and normalization hypotheses,
while `atMostOneNonzeroBlock_of_C1` shows that a spanning tensor family has at most one nonzero
block. For the matrix product state setting, see [PerezGarciaEtAl2007].

## Main statements

* `cutMatrix_eq_mul`: factors a cut matrix using word product matrices.
* `proposition1_cutRank_canonical`: cut rank equals `D ^ 2` under the stated canonical
  hypotheses.
* `atMostOneNonzeroBlock_of_C1`: uniqueness of a nonzero block under word spanning.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatrixProd07.MainResults.TICanonical

open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork
open Qatlib.Papers.MatrixProd07.MainResults
open Qatlib.Papers.MatrixProd07.MainResults.Appendix
  (wordSpan wordProd_zero wordProd_snoc map_mulLeft_le_wordSpan_succ)
open Matrix Filter
open scoped BigOperators ComplexConjugate Topology

/-- Rotates a configuration by `s` cyclic predecessor steps, using `s % n`. -/
def rotateBy {d : ℕ} (n : ℕ) [NeZero n] (s : ℕ) (x : Fin n → Fin d) : Fin n → Fin d :=
  fun i => x ⟨(i.val + n - s % n) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- The condition that an amplitude function is invariant under rotation by `p` sites. -/
def IsPPeriodic {n d : ℕ} [NeZero n] (p : ℕ) (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ x, ψ (rotateBy n p x) = ψ x

/-- The cyclic predecessor of an index in `Fin p`. -/
def cycPred {p : ℕ} (k : Fin p) : Fin p :=
  ⟨(k.val + p - 1) % p, Nat.mod_lt _ k.pos⟩

/-- The condition that a positive number `p` of pairwise annihilating idempotents sums to the
identity and each `A i` moves a block to its cyclic predecessor. -/
def HasCyclicUnitSpectrum {d D : ℕ} (A : Fin d → BM D) (p : ℕ) : Prop :=
  0 < p ∧ ∃ P : Fin p → BM D,
    (∀ k, P k * P k = P k) ∧ (∀ k l, k ≠ l → P k * P l = 0) ∧ (∑ k, P k = 1) ∧
      (∀ (k : Fin p) (i : Fin d), A i * P k = P (cycPred k) * A i)

/-- The condition that any two left canonical bond dimension `D` representations of `ψ` are
related at every site by one common unitary conjugation. -/
def OBCUnique {n d D : ℕ} [NeZero D] (ψ : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ A₁ A₂ : Fin n → Fin d → BM D,
    IsMpsRepresentation A₁ ψ → IsMpsRepresentation A₂ ψ →
      LeftCanonical A₁ → LeftCanonical A₂ →
        ∃ U : BM D, IsUnitary U ∧ ∀ (i : Fin n) (x : Fin d), A₁ i x = U * A₂ i x * Uᴴ

/-- The tail sum of the squared products `v i * v j`, using the flattened pair indices at least
`k`. -/
def pairTail {D : ℕ} (v : Fin D → ℝ) (k : ℕ) : ℝ :=
  ∑ t : Fin (D * D),
    if k ≤ t.val then
      (v ((finProdFinEquiv (m := D) (n := D)).symm t).1 * v ((finProdFinEquiv (m := D) (n := D)).symm t).2) ^ 2
    else 0

/-- The proposition that a cyclically invariant amplitude function has a site independent
periodic matrix product representation with some nonzero bond dimension. -/
def theorem3_site_independent  {n d : ℕ} [NeZero n] (ψ : (Fin n → Fin d) → ℂ)
    (_hTI : IsTICyclic ψ) : Prop :=
  ∃ (D : ℕ) (hD : NeZero D) (A : Fin d → BM D),
      ∀ x, @tiAmplitude n d D _ hD A x = ψ x

/-- The proposition that `ψ` has a site independent periodic representation of bond dimension at
most `n * D₀`, parameterized by a given bond dimension `D₀` representation. -/
def theorem3_bond_increase  {n d D₀ : ℕ} [NeZero n] (ψ : (Fin n → Fin d) → ℂ)
    (hD₀ : 0 < D₀) (A₀ : Fin n → Fin d → Matrix (Fin D₀) (Fin D₀) ℂ)
    (_hrep : ∀ x, @mpsAmplitude n d D₀ ⟨Nat.pos_iff_ne_zero.mp hD₀⟩ A₀ x = ψ x) : Prop :=
  ∃ (D : ℕ) (hD : NeZero D) (A : Fin d → BM D),
      D ≤ n * D₀ ∧ ∀ x, @tiAmplitude n d D _ hD A x = ψ x

/-- The proposition that a periodic representation can be replaced by one satisfying
`TICanonicalForm` without increasing its bond dimension. -/
def theorem4_TI_canonical  {n d D : ℕ} [NeZero n] [NeZero D] (ψ : (Fin n → Fin d) → ℂ)
    (A : Fin d → BM D) (_hrep : ∀ x, tiAmplitude A x = ψ x) : Prop :=
  ∃ (D' : ℕ) (hD' : NeZero D') (A' : Fin d → BM D'),
      TICanonicalForm A' ∧ (∀ x, @tiAmplitude n d D' _ hD' A' x = ψ x) ∧ D' ≤ D

/-- The proposition that divisibility `p ∣ n` permits a sum of `p` periodic tensor amplitudes
whose length `p` amplitudes satisfy `IsPPeriodic p`, while failure of divisibility forces
`ψ` to vanish. -/
def theorem5_periodic_decomposition  {n d D p : ℕ} [NeZero n] [NeZero D] [NeZero p]
    (A : Fin d → BM D) (ψ : (Fin n → Fin d) → ℂ)
    (_hcanon : TICanonicalFormWithBlocks 1 A)
    (_hrep : ∀ x, tiAmplitude A x = ψ x)
    (_hp : HasCyclicUnitSpectrum A p) : Prop :=
  ((p ∣ n) → ∃ B : Fin p → Fin d → BM D,
        (∀ x, ψ x = ∑ k, tiAmplitude (B k) x) ∧
          (∀ k : Fin p, IsPPeriodic p (fun (x : Fin p → Fin d) => tiAmplitude (B k) x)))
      ∧ ((¬ p ∣ n) → ∀ x, ψ x = 0)

/-- The proposition combining a single-block canonical representation of `ψ` with cut rank `D ^
2` whenever both sides of the cut have length at least a spanning length. -/
def proposition1_single_block  {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin d → BM D) (ψ : (Fin n → Fin d) → ℂ)
    (_hrep : ∀ x, tiAmplitude A x = ψ x)
    (_hcanon : TICanonicalForm A)
    (_hC1 : ∃ L0, L0 < n ∧ C1At A L0) : Prop :=
  (∃ A' : Fin d → BM D,
        TICanonicalFormWithBlocks 1 A' ∧ ∀ x, tiAmplitude A' x = ψ x)
      ∧ (∀ (L0 R : ℕ), L0 < n → C1At A L0 → L0 ≤ R → L0 ≤ n - R →
            cutRank n d ψ R = D ^ 2)

/-- The proposition that, for every `k`, the half-chain squared Schmidt tail converges to
`pairTail v k` as the chain length tends to infinity. -/
def theorem6_lambda_interpretation  {d D : ℕ} (v : Fin D → ℝ)
    (ψ : (N : ℕ) → (Fin N → Fin d) → ℂ)
    (_hNorm : ∀ N, ∑ x, Complex.normSq (ψ N x) = 1) : Prop :=
  ∀ k : ℕ, Tendsto (fun N => schmidtTailSq N d (ψ N) (N / 2) k) atTop
      (𝓝 (pairTail v k))

/-- The proposition that the two supplied single-block canonical tensor families are related by
one unitary conjugation under the stated representation, spanning, uniqueness, and length
hypotheses. -/
def theorem7_TI_uniqueness  {n d D : ℕ} [NeZero n] [NeZero D]
    (B C : Fin d → BM D) (ψ : (Fin n → Fin d) → ℂ)
    (_hBrep : ∀ x, tiAmplitude B x = ψ x)
    (_hCrep : ∀ x, tiAmplitude C x = ψ x)
    (_hBcanon : TICanonicalFormWithBlocks 1 B)
    (_hCcanon : TICanonicalFormWithBlocks 1 C)
    (_hC1 : ∃ L0, L0 < n ∧ C1At B L0)
    (_hOBC : OBCUnique (D := D) ψ)
    (_hN : ∀ L0, L0 < n → C1At B L0 → 2 * L0 + D ^ 4 < n) : Prop :=
  ∃ U : BM D, IsUnitary U ∧ ∀ i, B i = U * C i * Uᴴ

/-- The matrix `B ⊗ 1` with pair indices encoded in `Fin (D * D)`. -/
def kronRightOne {D : ℕ} (B : BM D) : BM (D * D) :=
  Matrix.of fun i j =>
    if ((finProdFinEquiv (m := D) (n := D)).symm i).2 =
        ((finProdFinEquiv (m := D) (n := D)).symm j).2 then
      B ((finProdFinEquiv (m := D) (n := D)).symm i).1
        ((finProdFinEquiv (m := D) (n := D)).symm j).1
    else 0

/-- The condition that invertible gauge pairs relate the selected interior open boundary tensors
to `B ⊗ 1`, and `B` satisfies `∑ i, B i * (B i)ᴴ = 1`. -/
def SatisfiesSystemS {n d D L0 : ℕ} (Aoc : (m : Fin n) → Fin d → BM (D * D))
    (B : Fin d → BM D) : Prop :=
  ∃ Y Z : (j : Fin (n + 1)) → BM (D * D),
    (∀ j, Y j * Z j = 1) ∧
      (∀ (j : Fin n) (i : Fin d), L0 + 1 ≤ j.val → j.val ≤ L0 + D ^ 4 →
          kronRightOne (B i) = Y ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ * Aoc j i *
            Z ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ∧
      (∑ i, B i * (B i)ᴴ = 1)

/-- The proposition combining existence of a solution to `SatisfiesSystemS` from a spanning
periodic representation with unitary equivalence of each solution to `Ac`, under the
supplied rank, canonical, and length data. -/
def theorem8_obtain_canonical  {n d D L0 : ℕ} [NeZero n] [NeZero D]
    (ψ : (Fin n → Fin d) → ℂ) (Aoc : (m : Fin n) → Fin d → BM (D * D)) (Ac : Fin d → BM D)
    (_hOBC : OBCUnique (D := D) ψ)
    (_hRank : ∀ m : Fin n, cutRank n d ψ m.val ≤ D ^ 2)
    (_hAc : TICanonicalFormWithBlocks 1 Ac)
    (_hbound : L0 + D ^ 4 < n) : Prop :=
  ((∃ Bc : Fin d → BM D, C1 Bc ∧ ∀ x, tiAmplitude Bc x = ψ x) →
        ∃ B : Fin d → BM D, SatisfiesSystemS (L0 := L0) Aoc B)
      ∧ (∀ B : Fin d → BM D, SatisfiesSystemS (L0 := L0) Aoc B →
          ∃ U : BM D, IsUnitary U ∧ ∀ i, Ac i = U * B i * Uᴴ)

/-- The trace of a matrix product equals the double sum of `P a b * Q b a`. -/
lemma trace_mul_sum {D : ℕ} (P Q : BM D) :
    (P * Q).trace = ∑ a, ∑ b, P a b * Q b a := by
  simp [Matrix.trace, Matrix.mul_apply]

/-- The recursive chain product of a sequence of selected generators equals its finite word
product. -/
lemma chainProd_eq_wordProd {d D : ℕ} (A : Fin d → BM D) :
    ∀ (m : ℕ) (w : ℕ → Fin d),
      chainProd (fun k => A (w k)) m = wordProd A m (fun i : Fin m => w i) := by
  intro m
  induction m with
  | zero =>
      intro w
      rw [wordProd_zero]
      rfl
  | succ m ih =>
      intro w
      have hw : (fun i : Fin (m + 1) => w i) =
          Fin.snoc (fun i : Fin m => w i) (w m) := by
        funext j
        cases j using Fin.lastCases with
        | last => simp
        | cast i => simp
      rw [chainProd_succ, ih w, hw, wordProd_snoc]

/-- Splits a chain product of length `r + s` into the first `r` factors and the next `s`
factors. -/
lemma chainProd_split {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℕ → Matrix ι ι ℂ) :
    ∀ r s : ℕ, chainProd M (r + s) = chainProd M r * chainProd (fun k => M (r + k)) s := by
  intro r s
  induction s with
  | zero =>
      rw [Nat.add_zero]
      simp [chainProd]
  | succ s ih =>
      rw [Nat.add_succ, chainProd_succ, ih]
      rw [chainProd_succ]
      rw [Matrix.mul_assoc]

/-- Expresses the periodic amplitude of a joined configuration as the trace contraction of the
word products on the two sides. -/
lemma tiAmplitude_splitJoin {n d D : ℕ} [NeZero n] [NeZero D] (A : Fin d → BM D)
    {R : ℕ} (hR : R ≤ n) (u : Fin R → Fin d) (v : Fin (n - R) → Fin d) :
    tiAmplitude A (splitJoin n R d u v) =
      ∑ a, ∑ b, (wordProd A R u) a b * (wordProd A (n - R) v) b a := by
  classical
  set x := splitJoin n R d u v with hx
  set xs : ℕ → Fin d := fun k => x ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩ with hxs
  have ht : tiAmplitude A x = (perTransferProd (fun _ : Fin n => A) x).trace := by
    simp only [tiAmplitude]
    exact periodicMpsAmplitude_eq_trace (fun _ : Fin n => A) x
  have hp : perTransferProd (fun _ : Fin n => A) x = chainProd (fun k => A (xs k)) n := rfl
  rw [ht, hp]
  have hn : n = R + (n - R) := (Nat.add_sub_cancel' hR).symm
  conv_lhs => rw [hn]
  rw [chainProd_split, chainProd_eq_wordProd, chainProd_eq_wordProd, trace_mul_sum]
  have hu : (fun i : Fin R => xs i) = u := by
    funext i
    have hin : (i : ℕ) < n := lt_of_lt_of_le i.isLt hR
    have hmod : (i : ℕ) % n = (i : ℕ) := Nat.mod_eq_of_lt hin
    simp only [hxs, hx, splitJoin]
    rw [dif_pos (by rw [hmod]; exact i.isLt)]
    congr 1
    exact Fin.ext (by simp [hmod])
  have hv : (fun i : Fin (n - R) => xs (R + i)) = v := by
    funext i
    have hi : R + (i : ℕ) < n := by have := i.isLt; omega
    have hmod : (R + (i : ℕ)) % n = R + (i : ℕ) := Nat.mod_eq_of_lt hi
    simp only [hxs, hx, splitJoin]
    rw [dif_neg (by rw [hmod]; omega)]
    congr 1
    exact Fin.ext (by simp [hmod])
  rw [hu, hv]

/-- The complex linear map sending a matrix to its function of ordered index pairs. -/
def matFunLin (D : ℕ) : BM D →ₗ[ℂ] (Fin D × Fin D → ℂ) where
  toFun M := fun p => M p.1 p.2
  map_add' M N := by funext p; rcases p with ⟨a, b⟩; rfl
  map_smul' c M := by funext p; rcases p with ⟨a, b⟩; rfl

/-- The complex linear map sending a matrix to its entries with the two indices exchanged. -/
def matFunLinT (D : ℕ) : BM D →ₗ[ℂ] (Fin D × Fin D → ℂ) where
  toFun M := fun p => M p.2 p.1
  map_add' M N := by funext p; rcases p with ⟨a, b⟩; rfl
  map_smul' c M := by funext p; rcases p with ⟨a, b⟩; rfl

/-- Every complex function on pairs of bond indices is the entry function of a matrix. -/
lemma matFunLin_surj (D : ℕ) : Function.Surjective (matFunLin D) := by
  intro f
  exact ⟨Matrix.of fun a b => f (a, b), by funext p; rcases p with ⟨a, b⟩; rfl⟩

/-- Every complex function on pairs of bond indices is the transposed entry function of a
matrix. -/
lemma matFunLinT_surj (D : ℕ) : Function.Surjective (matFunLinT D) := by
  intro f
  exact ⟨Matrix.of fun a b => f (b, a), by funext p; rcases p with ⟨a, b⟩; rfl⟩

/-- The matrix whose columns are the vectorized word products of length `R`, using the finite
word encoding. -/
def Fmat {d D : ℕ} (A : Fin d → BM D) (R : ℕ) :
    Matrix (Fin D × Fin D) (Fin (d ^ R)) ℂ :=
  fun p i => wordProd A R ((finPowEnc d R).symm i) p.1 p.2

/-- The matrix whose columns are the transposed entry functions of word products of length `m`. -/
def Gmat {d D : ℕ} (A : Fin d → BM D) (m : ℕ) :
    Matrix (Fin D × Fin D) (Fin (d ^ m)) ℂ :=
  fun p j => wordProd A m ((finPowEnc d m).symm j) p.2 p.1

/-- If length `R` word products span all bond matrices, then `Fmat A R` has rank `D * D`. -/
lemma rank_Fmat {d D : ℕ} (A : Fin d → BM D) {R : ℕ} (hC1 : C1At A R) :
    (Fmat A R).rank = D * D := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hrange : Set.range (Fmat A R).col = matFunLin D '' Set.range (wordProd A R) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨wordProd A R ((finPowEnc d R).symm i), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨M, ⟨w, rfl⟩, rfl⟩
      exact ⟨finPowEnc d R w, by
        funext p
        rcases p with ⟨a, b⟩
        simp [Fmat, matFunLin, Matrix.col]⟩
  have hspan : Submodule.span ℂ (Set.range (wordProd A R)) = ⊤ := hC1
  rw [hrange, ← Submodule.map_span (matFunLin D), hspan,
    Submodule.map_top (matFunLin D),
    LinearMap.range_eq_top.mpr (matFunLin_surj D), finrank_top, Module.finrank_pi]
  simp [Fintype.card_prod]

/-- If length `m` word products span all bond matrices, then `Gmat A m` has rank `D * D`. -/
lemma rank_Gmat {d D : ℕ} (A : Fin d → BM D) {m : ℕ} (hC1 : C1At A m) :
    (Gmat A m).rank = D * D := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hrange : Set.range (Gmat A m).col = matFunLinT D '' Set.range (wordProd A m) := by
    ext f
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨wordProd A m ((finPowEnc d m).symm j), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨M, ⟨w, rfl⟩, rfl⟩
      exact ⟨finPowEnc d m w, by
        funext p
        rcases p with ⟨a, b⟩
        simp [Gmat, matFunLinT, Matrix.col]⟩
  have hspan : Submodule.span ℂ (Set.range (wordProd A m)) = ⊤ := hC1
  rw [hrange, ← Submodule.map_span (matFunLinT D), hspan,
    Submodule.map_top (matFunLinT D),
    LinearMap.range_eq_top.mpr (matFunLinT_surj D), finrank_top, Module.finrank_pi]
  simp [Fintype.card_prod]

/-- If length `m` word products span all bond matrices, then multiplication by `Gmat A m` is
surjective. -/
lemma range_mulVecLin_Gmat {d D : ℕ} (A : Fin d → BM D) {m : ℕ} (hC1 : C1At A m) :
    LinearMap.range (Gmat A m).mulVecLin = ⊤ := by
  have hrank : (Gmat A m).rank = D * D := rank_Gmat A hC1
  rw [Matrix.rank] at hrank
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hrank, Module.finrank_pi]
  simp [Fintype.card_prod]

/-- The cut matrix of a represented periodic state factors as `(Fmat A R)ᵀ * Gmat A (n - R)`.
See [PerezGarciaEtAl2007]. -/
lemma cutMatrix_eq_mul {n d D : ℕ} [NeZero n] [NeZero D] (A : Fin d → BM D)
    (ψ : (Fin n → Fin d) → ℂ) (hrep : ∀ x, tiAmplitude A x = ψ x) {R : ℕ} (hR : R ≤ n) :
    cutMatrix n d ψ R = (Fmat A R)ᵀ * Gmat A (n - R) := by
  classical
  ext i j
  simp only [cutMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Fmat, Gmat]
  rw [← hrep (splitJoin n R d ((finPowEnc d R).symm i) ((finPowEnc d (n - R)).symm j))]
  rw [tiAmplitude_splitJoin A hR]
  rw [Fintype.sum_prod_type]

/-- A single-block canonical family satisfies `∑ i, A i * (A i)ᴴ = c • 1` for some nonzero
complex scalar `c`. See [PerezGarciaEtAl2007]. -/
lemma hsum_of_single_block {d D : ℕ} (A : Fin d → BM D)
    (h : TICanonicalFormWithBlocks 1 A) :
    ∃ c : ℂ, c ≠ 0 ∧ ∑ i, A i * (A i)ᴴ = c • 1 := by
  obtain ⟨-, P, lam, Ablk, hdec, hblk, hnorm, -, -⟩ := h
  have hP0 : P 0 = 1 := by
    simpa using! hdec.2.2.1
  have hlam0 : 0 < lam 0 := hdec.2.2.2.2.1 0
  have hAi : ∀ i, A i = ((lam 0 : ℝ) : ℂ) • Ablk 0 i := by
    intro i
    have h1 := hblk 0 i
    rw [hP0] at h1
    simpa using! h1
  refine ⟨((lam 0 : ℝ) : ℂ) ^ 2, ?_, ?_⟩
  · exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0))
  · calc ∑ i, A i * (A i)ᴴ
        = ∑ i, (((lam 0 : ℝ) : ℂ) ^ 2) • (Ablk 0 i * (Ablk 0 i)ᴴ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hAi i, Matrix.conjTranspose_smul]
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
            congr 1
            rw [pow_two]
            simp
      _ = (((lam 0 : ℝ) : ℂ) ^ 2) • ∑ i, Ablk 0 i * (Ablk 0 i)ᴴ := by
            rw [Finset.smul_sum]
      _ = (((lam 0 : ℝ) : ℂ) ^ 2) • P 0 := by rw [hnorm 0]
      _ = (((lam 0 : ℝ) : ℂ) ^ 2) • 1 := by rw [hP0]

/-- If the normalization sum is a nonzero scalar multiple of the identity, spanning at length
`L` implies spanning at length `L + 1`. -/
lemma C1At_succ {d D : ℕ} (A : Fin d → BM D) {c : ℂ} (hc : c ≠ 0)
    (hsum : ∑ i, A i * (A i)ᴴ = c • 1) {L : ℕ} (h : C1At A L) : C1At A (L + 1) := by
  show wordSpan A (L + 1) = ⊤
  rw [eq_top_iff]
  intro X _
  have hX : X = c⁻¹ • ∑ i, A i * ((A i)ᴴ * X) := by
    have hc1 : ((c⁻¹ : ℂ) • (∑ i, A i * (A i)ᴴ) : BM D) = 1 := by
      rw [hsum, smul_smul, inv_mul_cancel₀ hc, one_smul]
    calc X = (1 : BM D) * X := (Matrix.one_mul X).symm
      _ = ((c⁻¹ : ℂ) • (∑ i, A i * (A i)ᴴ)) * X := by rw [hc1]
      _ = (c⁻¹ : ℂ) • ((∑ i, A i * (A i)ᴴ) * X) := Matrix.smul_mul _ _ _
      _ = (c⁻¹ : ℂ) • ∑ i, (A i * (A i)ᴴ) * X := by rw [Matrix.sum_mul]
      _ = (c⁻¹ : ℂ) • ∑ i, A i * ((A i)ᴴ * X) := by
            congr 1
            exact Finset.sum_congr rfl fun i _ => Matrix.mul_assoc (A i) ((A i)ᴴ) X
  rw [hX]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
  have hmem : (A i)ᴴ * X ∈ wordSpan A L := by
    rw [show wordSpan A L = ⊤ from h]
    exact Submodule.mem_top
  exact map_mulLeft_le_wordSpan_succ A L i (Submodule.mem_map.mpr ⟨(A i)ᴴ * X, hmem, rfl⟩)

/-- If the normalization sum is a nonzero scalar multiple of the identity, spanning at length
`L` implies spanning at every length `L' ≥ L`. -/
lemma C1At_mono {d D : ℕ} (A : Fin d → BM D) {c : ℂ} (hc : c ≠ 0)
    (hsum : ∑ i, A i * (A i)ᴴ = c • 1) {L L' : ℕ} (h : C1At A L) (hLL : L ≤ L') :
    C1At A L' :=
  Nat.le_induction (P := fun k _ => C1At A k) h
    (fun _ _ ih => C1At_succ A hc hsum ih) L' hLL

/-- If length `L0 > 0` word products span all matrices and the normalization sum is a nonzero
scalar multiple of the identity, every cut with both sides at least `L0` has rank `D ^ 2`.
See [PerezGarciaEtAl2007]. -/
theorem proposition1_cutRank {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin d → BM D) (ψ : (Fin n → Fin d) → ℂ)
    (hrep : ∀ x, tiAmplitude A x = ψ x)
    {c : ℂ} (hc : c ≠ 0) (hsum : ∑ i, A i * (A i)ᴴ = c • 1)
    {L0 R : ℕ} (hL0pos : 0 < L0) (_hL0 : L0 < n) (hC1 : C1At A L0)
    (hR1 : L0 ≤ R) (hR2 : L0 ≤ n - R) :
    cutRank n d ψ R = D ^ 2 := by
  have hRn : R ≤ n := by omega
  have hC1R : C1At A R := C1At_mono A hc hsum hC1 hR1
  have hC1m : C1At A (n - R) := C1At_mono A hc hsum hC1 hR2
  rw [cutRank, cutMatrix_eq_mul A ψ hrep hRn]
  change ((Fmat A R)ᵀ * Gmat A (n - R)).rank = D ^ 2
  rw [Matrix.rank, Matrix.mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top ((Fmat A R)ᵀ).mulVecLin (range_mulVecLin_Gmat A hC1m)]
  change ((Fmat A R)ᵀ).rank = D ^ 2
  rw [Matrix.rank_transpose, rank_Fmat A hC1R, Nat.pow_two]

/-- For a single-block canonical representation spanning at length `L0 > 0`, every cut with both
sides at least `L0` has rank `D ^ 2`. See [PerezGarciaEtAl2007]. -/
theorem proposition1_cutRank_canonical {n d D : ℕ} [NeZero n] [NeZero D]
    (A : Fin d → BM D) (ψ : (Fin n → Fin d) → ℂ)
    (hrep : ∀ x, tiAmplitude A x = ψ x)
    (hcanon : TICanonicalFormWithBlocks 1 A)
    {L0 R : ℕ} (hL0pos : 0 < L0) (hL0 : L0 < n) (hC1 : C1At A L0)
    (hR1 : L0 ≤ R) (hR2 : L0 ≤ n - R) :
    cutRank n d ψ R = D ^ 2 := by
  obtain ⟨c, hc, hsum⟩ := hsum_of_single_block A hcanon
  exact proposition1_cutRank A ψ hrep hc hsum hL0pos hL0 hC1 hR1 hR2

/-- Left multiplication by an idempotent twice equals left multiplication by it once. -/
lemma mul_idem_assoc {D : ℕ} {p : BM D} (hp : p * p = p) (z : BM D) :
    p * (p * z) = p * z := by
  rw [← Matrix.mul_assoc, hp]

/-- If `p * q = 0`, then `p * (q * z) = 0`. -/
lemma mul_of_mul_eq_zero {D : ℕ} {p q : BM D} (h : p * q = 0) (z : BM D) :
    p * (q * z) = 0 := by
  rw [← Matrix.mul_assoc, h, Matrix.zero_mul]

/-- The product of two block diagonal sums over pairwise annihilating idempotents is the sum of
their products within each block. -/
lemma blockDiag_mul_form {D b : ℕ} (P : Fin b → BM D)
    (hPid : ∀ j, P j * P j = P j) (hPorth : ∀ j k, j ≠ k → P j * P k = 0)
    (X Y : BM D) :
    (∑ j, P j * X * P j) * (∑ j, P j * Y * P j)
      = ∑ j, P j * X * P j * Y * P j := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.mul_assoc]
    rw [mul_idem_assoc (hPid j)]
  · intro k _ hkj
    simp only [Matrix.mul_assoc]
    rw [mul_of_mul_eq_zero (hPorth j k (Ne.symm hkj))]
    simp
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Compressing the product of two block diagonal sums to block `j` gives `P j * X * P j * Y * P
j`. -/
lemma block_proj_mul {D b : ℕ} (P : Fin b → BM D)
    (hPid : ∀ j, P j * P j = P j) (hPorth : ∀ j k, j ≠ k → P j * P k = 0)
    (X Y : BM D) (j : Fin b) :
    P j * ((∑ i, P i * X * P i) * (∑ i, P i * Y * P i)) * P j
      = P j * X * P j * Y * P j := by
  rw [blockDiag_mul_form P hPid hPorth]
  rw [Matrix.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.mul_assoc]
    rw [mul_idem_assoc (hPid j), hPid j]
  · intro i _ hij
    simp only [Matrix.mul_assoc]
    rw [mul_of_mul_eq_zero (hPorth j i (Ne.symm hij))]
  · intro hi
    exact absurd (Finset.mem_univ j) hi

/-- If `Y` is block diagonal, compressing `X * Y` to block `j` inserts `P j` between `X` and
`Y`. -/
lemma block_proj_mul_right {D b : ℕ} (P : Fin b → BM D)
    (hPid : ∀ j, P j * P j = P j) (hPorth : ∀ j k, j ≠ k → P j * P k = 0)
    (X Y : BM D) (hY : Y = ∑ k, P k * Y * P k) (j : Fin b) :
    P j * (X * Y) * P j = P j * X * P j * Y * P j := by
  conv_lhs => rw [hY]
  rw [Matrix.mul_sum]
  rw [Matrix.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.mul_assoc]
    rw [hPid j]
  · intro k _ hkj
    simp only [Matrix.mul_assoc]
    rw [hPorth k j hkj]
    simp
  · intro hk
    exact absurd (Finset.mem_univ j) hk

/-- If all generators are block diagonal with respect to idempotents summing to one, every word
product is block diagonal with respect to the same idempotents. -/
lemma wordProd_blockDiag {d D b : ℕ} (P : Fin b → BM D) (A : Fin d → BM D)
    (hPid : ∀ j, P j * P j = P j) (hPorth : ∀ j k, j ≠ k → P j * P k = 0)
    (hPsum : ∑ j, P j = 1) (hA : ∀ i, A i = ∑ j, P j * A i * P j) :
    ∀ (m : ℕ) (w : Fin m → Fin d),
      wordProd A m w = ∑ j, P j * wordProd A m w * P j := by
  intro m
  induction m with
  | zero =>
      intro w
      rw [wordProd_zero]
      rw [show (∑ j, P j * (1 : BM D) * P j) = ∑ j, P j from
        Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_one, hPid j]]
      exact hPsum.symm
  | succ m ih =>
      intro w
      have hsplit : wordProd A (m + 1) w
          = wordProd A m (Fin.init w) * A (w (Fin.last m)) := by
        conv_lhs => rw [← Fin.snoc_init_self (q := w)]
        exact wordProd_snoc A m (Fin.init w) (w (Fin.last m))
      rw [hsplit]
      have hW : wordProd A m (Fin.init w) = ∑ i, P i * wordProd A m (Fin.init w) * P i :=
        ih (Fin.init w)
      have hAe : A (w (Fin.last m)) = ∑ i, P i * A (w (Fin.last m)) * P i :=
        hA (w (Fin.last m))
      calc wordProd A m (Fin.init w) * A (w (Fin.last m))
          = (∑ i, P i * wordProd A m (Fin.init w) * P i)
              * (∑ i, P i * A (w (Fin.last m)) * P i) := by
              conv_lhs => rw [hW, hAe]
        _ = ∑ j, P j * wordProd A m (Fin.init w) * P j
              * A (w (Fin.last m)) * P j :=
              blockDiag_mul_form P hPid hPorth _ _
        _ = ∑ j, P j * (wordProd A m (Fin.init w) * A (w (Fin.last m))) * P j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              exact (block_proj_mul_right P hPid hPorth (wordProd A m (Fin.init w))
                (A (w (Fin.last m))) hAe j).symm

/-- The trace pairing of an off-diagonal block with any word product of block diagonal
generators is zero. -/
lemma trace_offdiag_wordProd {d D b : ℕ} (P : Fin b → BM D) (A : Fin d → BM D)
    (hPid : ∀ j, P j * P j = P j) (hPorth : ∀ j k, j ≠ k → P j * P k = 0)
    (hPsum : ∑ j, P j = 1) (hA : ∀ i, A i = ∑ j, P j * A i * P j)
    {a b' : Fin b} (hab : a ≠ b') (M : BM D) (m : ℕ) (w : Fin m → Fin d) :
    ((P a * M * P b') * wordProd A m w).trace = 0 := by
  have hexp : wordProd A m w = ∑ j, P j * wordProd A m w * P j :=
    wordProd_blockDiag P A hPid hPorth hPsum hA m w
  calc ((P a * M * P b') * wordProd A m w).trace
      = ((P a * M * P b') * ∑ j, P j * wordProd A m w * P j).trace := by
          conv_lhs => rw [hexp]
    _ = (∑ j, (P a * M * P b') * (P j * wordProd A m w * P j)).trace := by
          rw [Matrix.mul_sum]
    _ = ∑ j, ((P a * M * P b') * (P j * wordProd A m w * P j)).trace := by
          rw [Matrix.trace_sum]
    _ = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          by_cases hjb : j = b'
          · rw [hjb]
            rw [Matrix.trace_mul_comm]
            have hz : (P b' * wordProd A m w * P b') * (P a * M * P b') = 0 := by
              simp only [Matrix.mul_assoc]
              rw [mul_of_mul_eq_zero (hPorth b' a (Ne.symm hab))]
              simp
            rw [hz, Matrix.trace_zero]
          · have hz : (P a * M * P b') * (P j * wordProd A m w * P j) = 0 := by
              simp only [Matrix.mul_assoc]
              rw [mul_of_mul_eq_zero (hPorth b' j (Ne.symm hjb))]
              simp
            rw [hz, Matrix.trace_zero]

/-- If length `L` word products span all matrices and `X` has zero trace pairing with each such
product, then `X = 0`. -/
lemma eq_zero_of_trace_wordProd {d D : ℕ} (A : Fin d → BM D) {L : ℕ} (hC1 : C1At A L)
    (X : BM D) (hX : ∀ w : Fin L → Fin d, (X * wordProd A L w).trace = 0) : X = 0 := by
  classical
  let phi : BM D →ₗ[ℂ] ℂ :=
    { toFun := fun W => (X * W).trace
      map_add' := fun W₁ W₂ => by simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun r W => by simp [Matrix.trace_smul] }
  have hker : LinearMap.ker phi = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = Submodule.span ℂ (Set.range (wordProd A L)) := hC1.symm
      _ ≤ LinearMap.ker phi := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨w, rfl⟩
          show phi (wordProd A L w) = 0
          exact hX w
  rw [Matrix.ext_iff_trace_mul_right]
  intro W
  have hW : W ∈ LinearMap.ker phi := by rw [hker]; exact Submodule.mem_top
  have h0 : phi W = 0 := hW
  simpa using! h0

/-- If a block diagonal family spans all matrices at some word length, every off-diagonal block
`P a * M * P b'` with `a ≠ b'` vanishes. See [PerezGarciaEtAl2007]. -/
theorem offdiag_block_eq_zero_of_C1 {d D b : ℕ} (P : Fin b → BM D) (A : Fin d → BM D)
    (lam : Fin b → ℝ) (hdec : IsBlockDiagonalDecomp P A lam) {L0 : ℕ} (hC1 : C1At A L0)
    {a b' : Fin b} (hab : a ≠ b') (M : BM D) : P a * M * P b' = 0 := by
  obtain ⟨hPid, hPorth, hPsum, hA, -, -⟩ := hdec
  exact eq_zero_of_trace_wordProd A hC1 (P a * M * P b')
    (fun w => trace_offdiag_wordProd P A hPid hPorth hPsum hA hab M L0 w)

/-- The `(i, j)` entry of `X * Matrix.single k l 1 * Y` equals `X i k * Y l j`. -/
lemma mul_single_mul_apply {D : ℕ} (X Y : BM D) (k l : Fin D) (i j : Fin D) :
    (X * Matrix.single k l (1 : ℂ) * Y) i j = X i k * Y l j := by
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro y _ hy
      rw [if_neg (by intro h; exact hy h.1.symm)]
      simp
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · intro x _ hxl
    have hzero : (∑ y, X i y * (if k = y ∧ l = x then (1 : ℂ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg (by intro h; exact hxl h.2.symm)]
      simp
    rw [hzero, zero_mul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- For nonzero square matrices `X` and `Y`, some matrix `M` satisfies `X * M * Y ≠ 0`. -/
lemma exists_mul_ne_zero {D : ℕ} {X Y : BM D} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ∃ M : BM D, X * M * Y ≠ 0 := by
  have hXe : ∃ i k, X i k ≠ 0 := by
    by_contra h
    exact hX (by
      ext i j
      by_contra hij
      exact h ⟨i, j, hij⟩)
  obtain ⟨i, k, hik⟩ := hXe
  have hYe : ∃ l j, Y l j ≠ 0 := by
    by_contra h
    exact hY (by
      ext i j
      by_contra hij
      exact h ⟨i, j, hij⟩)
  obtain ⟨l, j, hlj⟩ := hYe
  refine ⟨Matrix.single k l (1 : ℂ), ?_⟩
  intro hzero
  have hval : (X * Matrix.single k l (1 : ℂ) * Y) i j = 0 := by
    rw [hzero, Matrix.zero_apply]
  rw [mul_single_mul_apply] at hval
  exact mul_ne_zero hik hlj hval

/-- If a block diagonal tensor family has word products spanning all matrices, any two nonzero
block idempotents have the same index. See [PerezGarciaEtAl2007]. -/
theorem atMostOneNonzeroBlock_of_C1 {d D b : ℕ} (P : Fin b → BM D) (A : Fin d → BM D)
    (lam : Fin b → ℝ) (hdec : IsBlockDiagonalDecomp P A lam) {L0 : ℕ} (hC1 : C1At A L0) :
    ∀ a b' : Fin b, P a ≠ 0 → P b' ≠ 0 → a = b' := by
  intro a b' ha hb'
  by_contra hab
  obtain ⟨M, hM⟩ := exists_mul_ne_zero ha hb'
  exact hM (offdiag_block_eq_zero_of_C1 P A lam hdec hC1 hab M)

end Qatlib.Papers.MatrixProd07.MainResults.TICanonical
