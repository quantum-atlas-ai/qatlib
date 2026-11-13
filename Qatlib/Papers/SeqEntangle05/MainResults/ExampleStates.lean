/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SeqEntangle05.MainResults.SequentialGeneration

/-!
# Matrix-product representations of GHZ, W, and cluster amplitudes

This module gives explicit bond-dimension-two representations of the example states discussed in
[SchoenEtAl2005]. The families `ghzBlock`, `wBlock`, and `clBlock`, with their boundary vectors,
reproduce `ghzState`, `wState`, and `clState` through `mpsAmplitude`.

The GHZ and W amplitudes have coefficient one on their supported bit strings, while `clState`
includes the factor `invSqrt2 ^ n` and the phase determined by `adjCount`. The
sequential-generation conclusions use the boundary-contraction predicate `SeqGenerable`; the GHZ
results require a nonempty chain.

## Main statements

* `ghzState_isMPS` and `ghzState_seqGenerable` give the GHZ representation for `1 ≤ n`.
* `wState_isMPS` and `wState_seqGenerable` give the single-excitation representation for every
  `n`.
* `clChain` computes both ancillary coordinates of the cluster block product.
* `clState_isMPS` and `clState_seqGenerable` give the linear cluster amplitude representation.

## References

* [Schoen et al., 2005][SchoenEtAl2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SeqEntangle05.MainResults.ExampleStates

open Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs
open Qatlib.Papers.SeqEntangle05.MainResults.SequentialGeneration

/-- The diagonal projector onto ancillary coordinate `i`, with diagonal entry one at `i` and
zero at every other coordinate. -/
def maskBlock (D : ℕ) [DecidableEq (Fin D)] (i : Fin D) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal (fun s => if s = i then (1 : ℂ) else 0)

/-- The two GHZ blocks, obtained by projecting onto coordinate zero or coordinate one according
to the physical bit. -/
def ghzBlock : Block 2 := fun i => maskBlock 2 i

/-- The amplitude equal to one on the all-zero and all-one bit strings and zero elsewhere. For a
nonempty chain this is the unnormalized GHZ amplitude; for an empty chain its sole value is
one. -/
def ghzState (n : ℕ) (bits : Fin n → Fin 2) : ℂ :=
  if (∀ k, bits k = 0) ∨ (∀ k, bits k = 1) then 1 else 0

/-- For a bit list of length `n`, the product of `n` GHZ blocks is diagonal, with coordinate `s`
equal to the product of indicators that every listed bit equals `s`. -/
theorem prodBlocks_replicate_ghzBlock (n : ℕ) (is : List (Fin 2)) (h : is.length = n) :
    prodBlocks (List.replicate n ghzBlock) is =
      Matrix.diagonal (fun s : Fin 2 =>
        (is.map (fun i => if s = i then (1 : ℂ) else 0)).prod) := by
  induction is generalizing n with
  | nil =>
      have hn : n = 0 := by simpa using h.symm
      subst hn
      simp
  | cons i is' ih =>
      have hn : n = is'.length + 1 := by simpa using h.symm
      subst hn
      rw [List.replicate_succ, prodBlocks_cons, ih is'.length rfl]
      show Matrix.diagonal (fun s : Fin 2 => if s = i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun s : Fin 2 => (is'.map (fun i => if s = i then (1 : ℂ) else 0)).prod) =
        Matrix.diagonal (fun s : Fin 2 => ((i :: is').map (fun i => if s = i then (1 : ℂ) else 0)).prod)
      simp only [List.map_cons, List.prod_cons]
      rw [Matrix.diagonal_mul_diagonal]

/-- Multiplying a diagonal matrix by the all-ones vector returns its diagonal vector. -/
theorem diagonal_mulVec_one {D : ℕ} [DecidableEq (Fin D)] (d : Fin D → ℂ) :
    Matrix.diagonal d *ᵥ (fun _ => (1 : ℂ)) = d := by
  funext s
  rw [mulVec_diagonal]
  simp

/-- The product of the indicators that each bit in `l` equals `i` is the indicator that all bits
in `l` equal `i`. This includes the empty list, whose product and universal condition both
give one. -/
theorem prod_indicator (l : List (Fin 2)) (i : Fin 2) :
    (l.map (fun b => if i = b then (1 : ℂ) else 0)).prod =
      if (∀ b ∈ l, i = b) then 1 else 0 := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      rw [List.map_cons, List.prod_cons]
      by_cases hb : i = b
      · rw [if_pos hb, one_mul, ih]
        have hiff : (∀ x ∈ bs, i = x) ↔ (∀ x ∈ b :: bs, i = x) := by
          constructor
          · intro h x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hb
            · exact h x hx'
          · intro h x hx
            exact h x (List.mem_cons_of_mem b hx)
        simp only [hiff]
      · have hneg : ¬ (∀ b_1 ∈ b :: bs, i = b_1) := by
          intro hc
          exact hb (hc b (by simp))
        rw [if_neg hb, zero_mul, if_neg hneg]

/-- Every entry of `List.ofFn bits` equals `i` if and only if `bits k = i` at every finite index
`k`. -/
theorem forall_mem_ofFn {n : ℕ} (bits : Fin n → Fin 2) (i : Fin 2) :
    (∀ x ∈ List.ofFn bits, i = x) ↔ ∀ k, bits k = i := by
  constructor
  · intro h k
    exact (h (bits k) (List.mem_ofFn.mpr ⟨k, rfl⟩)).symm
  · intro h x hx
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hx
    rw [← hk]
    exact (h k).symm

/-- The amplitude of the constant GHZ block family with all-ones boundary vectors is the sum of
the all-zero and all-one indicator products. The identity also holds for `n = 0`, when both
products equal one. -/
theorem mpsAmplitude_ghz (n : ℕ) (bits : Fin n → Fin 2) :
    mpsAmplitude (fun _ => ghzBlock) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) bits =
      ((List.ofFn bits).map (fun b => if (0 : Fin 2) = b then (1 : ℂ) else 0)).prod +
      ((List.ofFn bits).map (fun b => if (1 : Fin 2) = b then (1 : ℂ) else 0)).prod := by
  unfold mpsAmplitude blockProd
  have hA : List.ofFn (fun _ : Fin n => ghzBlock) = List.replicate n ghzBlock := by simp
  rw [hA]
  have hlen : (List.ofFn bits).length = n := by simp
  rw [prodBlocks_replicate_ghzBlock n (List.ofFn bits) hlen]
  simp only [mulVec_diagonal, mul_one, one_mul, star_one]
  rw [Fin.sum_univ_two]

/-- On a nonempty bit string, the all-zero and all-one conditions are disjoint, so the sum of
their complex indicators equals the indicator of their disjunction. -/
theorem ghz_cond_add {n : ℕ} (hn : 1 ≤ n) (bits : Fin n → Fin 2) :
    (if (∀ k, bits k = 0) then (1 : ℂ) else 0) +
        (if (∀ k, bits k = 1) then (1 : ℂ) else 0) =
      if ((∀ k, bits k = 0) ∨ (∀ k, bits k = 1)) then 1 else 0 := by
  by_cases h0 : ∀ k, bits k = 0
  · by_cases h1 : ∀ k, bits k = 1
    · exfalso
      have hk0 := h0 (⟨0, by omega⟩ : Fin n)
      have hk1 := h1 (⟨0, by omega⟩ : Fin n)
      rw [hk0] at hk1
      exact absurd hk1 (by decide)
    · rw [if_pos h0, if_neg h1, if_pos (Or.inl h0)]; simp
  · rw [if_neg h0]
    by_cases h1 : ∀ k, bits k = 1
    · rw [if_pos h1, if_pos (Or.inr h1)]; simp
    · rw [if_neg h1, if_neg (by rintro (h | h); exact h0 h; exact h1 h)]; simp

/-- For `1 ≤ n`, the unnormalized GHZ amplitude has a bond-dimension-two matrix-product
representation using `ghzBlock` and all-ones boundary vectors [SchoenEtAl2005]. -/
theorem ghzState_isMPS {n : ℕ} (hn : 1 ≤ n) : IsMPS 2 n (ghzState n) := by
  refine ⟨fun _ => ghzBlock, fun _ => (1 : ℂ), fun _ => (1 : ℂ), ?_⟩
  intro bits
  rw [mpsAmplitude_ghz, prod_indicator, prod_indicator]
  simp only [forall_mem_ofFn]
  unfold ghzState
  exact (ghz_cond_add hn bits).symm

/-- The two-by-two matrix unit with its only nonzero entry, equal to one, in row zero and column
one. -/
def wE : Matrix (Fin 2) (Fin 2) ℂ := fun a b => if a = 0 ∧ b = 1 then (1 : ℂ) else 0

/-- The W block family assigns the identity matrix to physical bit zero and the nilpotent matrix
`wE` to physical bit one. -/
def wBlock : Block 2 := fun i => if i = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) else wE

/-- The initial ancillary boundary vector for the W representation, equal to the coordinate-one
basis vector. -/
def wPhiI : Fin 2 → ℂ := fun s => if s = 1 then 1 else 0

/-- The final ancillary boundary vector for the W representation, equal to the coordinate-zero
basis vector. -/
def wPhiF : Fin 2 → ℂ := fun s => if s = 0 then 1 else 0

/-- Counts the entries equal to one in a list of binary labels, adding one for each nonzero
entry. -/
def onesCount : List (Fin 2) → ℕ
  | [] => 0
  | i :: is => onesCount is + (if i = 0 then 0 else 1)

/-- The matrix `wE` is nilpotent of square zero. -/
theorem wE_sq_zero : wE ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, Matrix.zero_apply]
  fin_cases a <;> fin_cases b <;> simp [wE, Fin.sum_univ_two]

/-- The row-zero, column-one entry of `wE ^ m` equals one precisely when `m = 1`, and equals
zero otherwise. -/
theorem wE_pow_zero_one (m : ℕ) : (wE ^ m) 0 1 = if m = 1 then (1 : ℂ) else 0 := by
  by_cases h0 : m = 0
  · subst h0; simp [wE]
  by_cases h1 : m = 1
  · subst h1; simp [wE]
  · have h2 : 2 ≤ m := by omega
    have hm : wE ^ m = wE ^ 2 * wE ^ (m - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hm, wE_sq_zero, Matrix.zero_mul, if_neg h1]
    simp

/-- For a bit list of length `n`, the product of `n` W blocks is `wE` raised to the number of
ones in the list. -/
theorem prodBlocks_replicate_wBlock (n : ℕ) (is : List (Fin 2)) (h : is.length = n) :
    prodBlocks (List.replicate n wBlock) is = wE ^ onesCount is := by
  induction is generalizing n with
  | nil =>
      have hn : n = 0 := by simpa using h.symm
      subst hn
      simp [onesCount]
  | cons i is' ih =>
      have hn : n = is'.length + 1 := by simpa using h.symm
      subst hn
      rw [List.replicate_succ, prodBlocks_cons, ih is'.length rfl]
      by_cases hi : i = 0
      · subst hi
        simp [wBlock, onesCount]
      · have hwb : wBlock i = wE := by simp [wBlock, hi]
        rw [hwb]
        show wE * wE ^ onesCount is' = wE ^ (onesCount is' + (if i = 0 then 0 else 1))
        rw [if_neg hi, pow_succ']

/-- The amplitude of the W block family with boundaries `wPhiI` and `wPhiF` is the row-zero,
column-one entry of `wE` raised to the bit string's number of ones. -/
theorem mpsAmplitude_w (n : ℕ) (bits : Fin n → Fin 2) :
    mpsAmplitude (fun _ => wBlock) wPhiI wPhiF bits =
      (wE ^ onesCount (List.ofFn bits)) 0 1 := by
  unfold mpsAmplitude blockProd
  have hA : List.ofFn (fun _ : Fin n => wBlock) = List.replicate n wBlock := by simp
  rw [hA]
  have hlen : (List.ofFn bits).length = n := by simp
  rw [prodBlocks_replicate_wBlock n (List.ofFn bits) hlen]
  simp [wPhiF, wPhiI, Matrix.mulVec, Fin.sum_univ_two]

/-- The unnormalized single-excitation amplitude, equal to one exactly on bit strings containing
one occurrence of one and zero on all other strings. -/
def wState (n : ℕ) (bits : Fin n → Fin 2) : ℂ :=
  if onesCount (List.ofFn bits) = 1 then 1 else 0

/-- For every chain length, `wState n` has a bond-dimension-two matrix-product representation
using `wBlock`, `wPhiI`, and `wPhiF` [SchoenEtAl2005]. -/
theorem wState_isMPS (n : ℕ) : IsMPS 2 n (wState n) := by
  refine ⟨fun _ => wBlock, wPhiI, wPhiF, ?_⟩
  intro bits
  rw [mpsAmplitude_w, wE_pow_zero_one]
  unfold wState
  rfl

/-- The complex scalar obtained by embedding the positive real square root of two and taking its
inverse. -/
def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The cluster block for bit zero has column zero equal to `invSqrt2` times `(1, 1)` and its
other column zero. The block for bit one has column one equal to `invSqrt2` times `(1, -1)`
and its other column zero. -/
def clBlock : Block 2 := fun i => fun a b =>
  invSqrt2 * (if b = i then (if a = 0 then (1 : ℂ) else (if i = 0 then 1 else -1)) else 0)

/-- The all-ones initial ancillary boundary vector for the cluster representation. -/
def clPhiI : Fin 2 → ℂ := fun _ => 1

/-- The final ancillary boundary vector for the cluster representation, equal to the
coordinate-zero basis vector. -/
def clPhiF : Fin 2 → ℂ := fun s => if s = 0 then 1 else 0

/-- Counts adjacent pairs of ones in a binary list, including overlapping pairs and assigning
zero to lists of length at most one. -/
def adjCount : List (Fin 2) → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (if x = 1 ∧ y = 1 then 1 else 0) + adjCount (y :: rest)

/-- The linear cluster amplitude `invSqrt2 ^ n` multiplied by a sign that is negative once for
each adjacent pair of ones in the bit string. -/
def clState (n : ℕ) (bits : Fin n → Fin 2) : ℂ :=
  invSqrt2 ^ n * (-1 : ℂ) ^ (adjCount (List.ofFn bits))

/-- The sign determined by the first bit: one for an empty list or a leading zero, and negative
one for a leading one. -/
def headSign : List (Fin 2) → ℂ
  | [] => 1
  | i :: _ => if i = 0 then 1 else -1

/-- Prepending bit `i` changes the cluster phase by `headSign js` when `i = 1` and by one when
`i = 0`. -/
theorem adj_step (i : Fin 2) (js : List (Fin 2)) :
    (-1 : ℂ) ^ (adjCount js) * (if i = 0 then 1 else headSign js)
      = (-1 : ℂ) ^ (adjCount (i :: js)) := by
  cases js with
  | nil => simp [adjCount, headSign]
  | cons j ks =>
      fin_cases i <;> fin_cases j <;>
        simp [adjCount, headSign, pow_succ, pow_add]

/-- Applying `clBlock i` selects coordinate `i` of the input vector, multiplies it by
`invSqrt2`, and inserts the cluster sign in output coordinate one. -/
theorem clBlock_mulVec (i : Fin 2) (w : Fin 2 → ℂ) (a : Fin 2) :
    (clBlock i *ᵥ w) a
      = invSqrt2 * (if a = 0 then 1 else (if i = 0 then 1 else -1)) * w i := by
  fin_cases i <;> fin_cases a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, clBlock]

/-- Computes both coordinates of the cluster block product applied to `clPhiI`: coordinate zero
is `invSqrt2 ^ l.length` times the adjacent-pair phase, and coordinate one has the
additional factor `headSign l`. -/
theorem clChain (l : List (Fin 2)) :
    (prodBlocks (List.replicate l.length clBlock) l *ᵥ clPhiI) 0
      = invSqrt2 ^ l.length * (-1 : ℂ) ^ (adjCount l) ∧
    (prodBlocks (List.replicate l.length clBlock) l *ᵥ clPhiI) 1
      = invSqrt2 ^ l.length * (-1 : ℂ) ^ (adjCount l) * headSign l := by
  induction l with
  | nil => simp [clPhiI, adjCount, headSign]
  | cons i js ih =>
      rw [List.length_cons, List.replicate_succ, prodBlocks_cons, ← Matrix.mulVec_mulVec]
      obtain ⟨h0, h1⟩ := ih
      have hw : ∀ a : Fin 2,
          (prodBlocks (List.replicate js.length clBlock) js *ᵥ clPhiI) a
            = invSqrt2 ^ js.length * (-1 : ℂ) ^ (adjCount js)
              * (if a = 0 then 1 else headSign js) := by
        intro a
        fin_cases a
        · simpa using h0
        · simpa using h1
      constructor
      · rw [clBlock_mulVec, if_pos rfl, hw, ← adj_step i js]
        simp only [List.length_cons, pow_succ]
        ring
      · rw [clBlock_mulVec, hw, ← adj_step i js]
        simp only [List.length_cons, pow_succ, headSign,
          if_neg (show ¬((1 : Fin 2) = 0) by decide)]
        ring

/-- For every chain length, the linear cluster amplitude has a bond-dimension-two matrix-product
representation using `clBlock`, `clPhiI`, and `clPhiF` [SchoenEtAl2005]. -/
theorem clState_isMPS (n : ℕ) : IsMPS 2 n (clState n) := by
  refine ⟨fun _ => clBlock, clPhiI, clPhiF, ?_⟩
  intro bits
  unfold clState mpsAmplitude blockProd
  have hA : List.ofFn (fun _ : Fin n => clBlock) = List.replicate n clBlock := by simp
  rw [hA]
  have hlen : (List.ofFn bits).length = n := by simp
  have h := (clChain (List.ofFn bits)).1
  rw [hlen] at h
  simp only [Fin.sum_univ_two, clPhiF, star_one, star_zero]
  simpa using h.symm

/-- For a nonempty chain, the unnormalized GHZ amplitude satisfies the sequential-isometry
boundary-contraction predicate with ancillary dimension two [SchoenEtAl2005]. -/
theorem ghzState_seqGenerable {n : ℕ} (hn : 1 ≤ n) :
    SeqGenerable 2 n (ghzState n) :=
  isMPS_seqGenerable_uncond (ghzState_isMPS hn)

/-- For every chain length, the unnormalized single-excitation amplitude satisfies the
sequential-isometry boundary-contraction predicate with ancillary dimension two
[SchoenEtAl2005]. -/
theorem wState_seqGenerable (n : ℕ) : SeqGenerable 2 n (wState n) :=
  isMPS_seqGenerable_uncond (wState_isMPS n)

/-- For every chain length, the linear cluster amplitude satisfies the sequential-isometry
boundary-contraction predicate with ancillary dimension two [SchoenEtAl2005]. -/
theorem clState_seqGenerable (n : ℕ) : SeqGenerable 2 n (clState n) :=
  isMPS_seqGenerable_uncond (clState_isMPS n)

end Qatlib.Papers.SeqEntangle05.MainResults.ExampleStates
