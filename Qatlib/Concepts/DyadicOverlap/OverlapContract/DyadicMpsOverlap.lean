/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicOverlap.OverlapContract.DyadicMpsOverlapDefs

/-!
# Dyadic MPS overlap correctness and arithmetic logs

This module proves that the Gaussian integer double-layer contraction decodes to the complex MPS
amplitude inner product. `g1` establishes `clause1Statement`, and `g2` establishes the
self-overlap properties and six examples in `clause2Statement`. The transfer-matrix
interpretation follows the MPS framework reviewed in [Schollwock2011].

The event-log results give exact construction and contraction lengths and prove every recorded
integer operation correct. `clause3_logWF_and_counts` collects those guarantees and boundary
identities. The proposed additional magnitude envelope fails: `clause3Statement_false` provides
a concrete counterexample to the full `clause3Statement`.

## Main statements

* `transfer_prod_eq_sum`: the double-layer matrix product equals the amplitude-product sum.
* `mpsAmplitude_eq_prodAt`: the open-boundary amplitude is a matrix-product entry.
* `g1` and `g2`: decoded overlap correctness and self-overlap properties.
* `clause3_logWF_and_counts`: valid arithmetic logs and polynomial event bounds.
* `clause3Statement_false`: failure of the proposed combined magnitude bound.

## References

* [Schollwöck, 2011][Schollwock2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.TensorNetwork.GaugeInvariance

set_option autoImplicit false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.DyadicProgram.DyadicContract

open Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Concepts.DyadicOverlap.OverlapContract

open Matrix
open scoped BigOperators ComplexConjugate
open Qatlib.Concepts.DyadicProgram.DyadicContract (GI add mul decode scalar run initial dot row)
open Qatlib.Concepts.MpsAdaptation.MpsTransfer (mpsAmplitude)

/-- The complex encoding of the componentwise sum is the sum of the two complex encodings. -/
private theorem enc_add (x y : GI) :
    ((x.1 + y.1 : ℤ) : ℂ) + ((x.2 + y.2 : ℤ) : ℂ) * Complex.I
      = ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) + ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) := by
  push_cast
  ring

/-- The complex encoding of Gaussian integer multiplication is the product of the two complex
encodings. -/
private theorem enc_mul (x y : GI) :
    ((x.1 * y.1 - x.2 * y.2 : ℤ) : ℂ) + ((x.1 * y.2 + x.2 * y.1 : ℤ) : ℂ) * Complex.I
      = ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) * ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) := by
  push_cast
  linear_combination -((x.2 : ℂ) * (y.2 : ℂ)) * Complex.I_sq

/-- Negating the imaginary component of an integer pair conjugates its complex encoding. -/
private theorem enc_conj (z : GI) :
    ((z.1 : ℂ) + ((-z.2 : ℤ) : ℂ) * Complex.I)
      = conj ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) := by
  rw [map_add, map_mul, Complex.conj_I]
  simp only [map_intCast, Int.cast_neg]
  ring

/-- Complex conjugation fixes every natural power of two. -/
private theorem conj_two_pow (p : ℕ) : conj ((2 : ℂ) ^ p) = (2 : ℂ) ^ p := by
  rw [map_pow, Complex.conj_ofNat]

/-- Decoding at a common dyadic precision preserves Gaussian integer addition. -/
theorem decode_add (p : ℕ) (x y : GI) :
    decode p (add x y) = decode p x + decode p y := by
  show (((x.1 + y.1 : ℤ) : ℂ) + ((x.2 + y.2 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ p
    = ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) / (2 : ℂ) ^ p
        + ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) / (2 : ℂ) ^ p
  rw [enc_add]
  exact add_div _ _ _

/-- A Gaussian integer product decoded at precision `p + q` equals the product of the factors
decoded at precisions `p` and `q`. -/
theorem decode_mul (p q : ℕ) (x y : GI) :
    decode (p + q) (mul x y) = decode p x * decode q y := by
  show (((x.1 * y.1 - x.2 * y.2 : ℤ) : ℂ)
      + ((x.1 * y.2 + x.2 * y.1 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ (p + q)
    = (((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) / (2 : ℂ) ^ p)
        * (((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) / (2 : ℂ) ^ q)
  rw [enc_mul, pow_add, div_mul_div_comm]

/-- Dyadic decoding commutes with Gaussian integer conjugation. -/
theorem decode_conjGI (p : ℕ) (z : GI) :
    decode p (conjGI z) = conj (decode p z) := by
  show (((z.1 : ℂ) + ((-z.2 : ℤ) : ℂ) * Complex.I)) / (2 : ℂ) ^ p
    = conj (((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / (2 : ℂ) ^ p)
  rw [map_div₀, enc_conj, conj_two_pow]

/-- The zero Gaussian integer decodes to zero at every precision. -/
theorem decode_zero (p : ℕ) : decode p ((0, 0) : GI) = 0 := by
  show (((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ p = 0
  rw [Int.cast_zero, zero_mul, add_zero, zero_div]

/-- The Gaussian integer `(1, 0)` decodes to `1 / 2 ^ p`. -/
theorem decode_one_zero (p : ℕ) : decode p ((1, 0) : GI) = (1 : ℂ) / (2 : ℂ) ^ p := by
  show (((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ p = (1 : ℂ) / (2 : ℂ) ^ p
  rw [Int.cast_one, Int.cast_zero, zero_mul, add_zero]

/-- Flattening the pair of zero bond indices gives zero. -/
theorem toIdx_zero_zero {Da Db : ℕ} [NeZero Da] [NeZero Db] :
    toIdx (Da := Da) (Db := Db) 0 0 = 0 := by
  show finProdFinEquiv ((0 : Fin Da), (0 : Fin Db)) = 0
  simp [finProdFinEquiv]

/-- Decoding the zero flattened index gives the pair of zero bond indices. -/
theorem ofIdx_zero {Da Db : ℕ} [NeZero Da] [NeZero Db] :
    ofIdx (Da := Da) (Db := Db) 0 = (0, 0) := by
  have h : (0 : Fin (Da * Db)) = toIdx (0 : Fin Da) (0 : Fin Db) :=
    (toIdx_zero_zero (Da := Da) (Db := Db)).symm
  show finProdFinEquiv.symm 0 = (0, 0)
  rw [h, toIdx]
  exact finProdFinEquiv.symm_apply_apply (0, 0)

/-- Flattening a decoded bond index recovers the original index. -/
theorem toIdx_ofIdx {Da Db : ℕ} (i : Fin (Da * Db)) : toIdx (ofIdx i).1 (ofIdx i).2 = i := by
  show finProdFinEquiv (finProdFinEquiv.symm i) = i
  exact finProdFinEquiv.apply_symm_apply i

/-- Decoding a flattened pair of bond indices recovers the original pair. -/
theorem ofIdx_toIdx {Da Db : ℕ} (a : Fin Da) (b : Fin Db) :
    ofIdx (toIdx a b) = (a, b) := by
  show finProdFinEquiv.symm (finProdFinEquiv (a, b)) = (a, b)
  exact finProdFinEquiv.symm_apply_apply (a, b)

/-- Equality of flattened bond indices implies equality of both components. -/
theorem toIdx_injective {Da Db : ℕ} {a a' : Fin Da} {b b' : Fin Db}
    (h : toIdx a b = toIdx a' b') : a = a' ∧ b = b' := by
  have := congrArg ofIdx h
  simp only [ofIdx_toIdx] at this
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- A flattened bond index is zero exactly when both components are zero. -/
theorem toIdx_eq_zero_iff {Da Db : ℕ} [NeZero Da] [NeZero Db] {a : Fin Da} {b : Fin Db} :
    toIdx a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact toIdx_injective (by rw [h, toIdx_zero_zero])
  · rintro ⟨rfl, rfl⟩
    exact toIdx_zero_zero

/-- Two flattened bond indices are equal exactly when their respective components are equal. -/
theorem toIdx_eq_iff {Da Db : ℕ} {a a' : Fin Da} {b b' : Fin Db} :
    toIdx a b = toIdx a' b' ↔ a = a' ∧ b = b' :=
  ⟨toIdx_injective, by rintro ⟨rfl, rfl⟩; rfl⟩

/-- For a positive paired bond dimension, the overlap program is the scalar contraction of the
transfer list. -/
theorem overlapProgram_of_pos {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI)
    (h : 0 < Da * Db) :
    overlapProgram A B = scalar h (transferList A B) := by
  show (if h' : 0 < Da * Db then scalar h' (transferList A B) else ((1, 0) : GI)) = _
  simp [h]

/-- An empty-chain overlap program with positive paired bond dimension returns `(1, 0)`. -/
theorem overlapProgram_empty_chain {d Da Db : ℕ}
    (A : Fin 0 → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin 0 → Fin d → Matrix (Fin Db) (Fin Db) GI)
    (h : 0 < Da * Db) :
    overlapProgram A B = ((1, 0) : GI) := by
  rw [overlapProgram_of_pos _ _ h, transferList]
  show scalar h ([] : List (Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI)) = ((1, 0) : GI)
  exact (Qatlib.Concepts.DyadicProgram.DyadicContract.decode_standard_scalar (Da * Db) 0 h []).2

/-- The complex transfer matrix obtained by decoding the Gaussian integer transfer matrix at
precision `2 * p`. -/
noncomputable def transferC {d Da Db : ℕ} (p : ℕ)
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI) :
    Matrix (Fin (Da * Db)) (Fin (Da * Db)) ℂ :=
  fun i j => decode (2 * p) (transferMat A B i j)

/-- The complex double-layer transfer matrix formed by summing conjugated `Abar` entries times
`Bbar` entries over the physical index. -/
noncomputable def transferCc {d Da Db : ℕ}
    (Abar : Fin d → Matrix (Fin Da) (Fin Da) ℂ)
    (Bbar : Fin d → Matrix (Fin Db) (Fin Db) ℂ) :
    Matrix (Fin (Da * Db)) (Fin (Da * Db)) ℂ :=
  fun i j => ∑ s : Fin d,
    conj (Abar s (ofIdx i).1 (ofIdx j).1) * Bbar s (ofIdx i).2 (ofIdx j).2

/-- The ordered matrix product selected by a physical configuration. -/
noncomputable def prodAt {n d D : ℕ} (M : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i => M i (x i)).prod

/-- Split a physical configuration of length `n + 1` into its initial `n` symbols and its final
symbol. -/
def snocEquiv (n d : ℕ) : (Fin (n + 1) → Fin d) ≃ (Fin n → Fin d) × Fin d where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun p := @Fin.snoc n (fun _ => Fin d) p.1 p.2
  left_inv x := @Fin.snoc_init_self n (fun _ => Fin d) x
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      exact @Fin.snoc_castSucc n (fun _ => Fin d) p.2 p.1 i
    · exact @Fin.snoc_last n (fun _ => Fin d) p.2 p.1

/-- The inverse of `snocEquiv` appends the final symbol using `Fin.snoc`. -/
theorem snocEquiv_symm_apply (n d : ℕ) (x : Fin n → Fin d) (s : Fin d) :
    (snocEquiv n d).symm (x, s) = @Fin.snoc n (fun _ => Fin d) x s :=
  rfl

/-- The selected matrix product for an appended configuration factors into the prefix product
and the last selected matrix. -/
theorem prodAt_snoc {n d D : ℕ} (M : Fin (n + 1) → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) (s : Fin d) :
    prodAt M (@Fin.snoc n (fun _ => Fin d) x s)
      = prodAt (fun i => M i.castSucc) x * M (Fin.last n) s := by
  show (List.ofFn fun i : Fin (n + 1) =>
      M i ((@Fin.snoc n (fun _ => Fin d) x s) i)).prod
    = (List.ofFn fun i : Fin n => M i.castSucc (x i)).prod * M (Fin.last n) s
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]
  simp only [@Fin.snoc_castSucc n (fun _ => Fin d) s x,
    @Fin.snoc_last n (fun _ => Fin d) s x]

/-- Decoding a folded Gaussian integer sum gives the decoded initial value plus the sum of the
decoded entries. -/
private theorem decode_foldl_add (p : ℕ) (xs : List GI) (z : GI) :
    decode p (xs.foldl add z) = decode p z + (xs.map (decode p)).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih (add z x), decode_add, List.map_cons, List.sum_cons]
    ring

/-- A transfer entry decoded at precision `2 * p` equals the physical-index sum of products of
the decoded site entries, conjugating the first tensor. -/
theorem decode_transferEntry {d Da Db : ℕ} (p : ℕ)
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI)
    (a a' : Fin Da) (b b' : Fin Db) :
    decode (2 * p) (transferEntry A B a a' b b')
      = ∑ s : Fin d, conj (decode p (A s a a')) * decode p (B s b b') := by
  have hfold :
      transferEntry A B a a' b b'
        = (List.ofFn fun s : Fin d => mul (conjGI (A s a a')) (B s b b')).foldl add ((0, 0) : GI) :=
    rfl
  have h := decode_foldl_add (2 * p)
    (List.ofFn fun s : Fin d => mul (conjGI (A s a a')) (B s b b')) ((0, 0) : GI)
  rw [decode_zero, zero_add] at h
  rw [hfold, h, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  show (∑ s : Fin d, decode (2 * p) (mul (conjGI (A s a a')) (B s b b')))
    = ∑ s : Fin d, conj (decode p (A s a a')) * decode p (B s b b')
  apply Finset.sum_congr rfl
  intro s _
  have hp : (2 * p : ℕ) = p + p := by ring
  rw [hp, decode_mul, decode_conjGI]

/-- Decoding the Gaussian integer transfer matrix agrees with constructing the complex transfer
matrix from decoded tensors. -/
theorem transferC_eq_transferCc {d Da Db : ℕ} (p : ℕ)
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI) :
    transferC p A B = transferCc (fun s a a' => decode p (A s a a'))
      (fun s b b' => decode p (B s b b')) := by
  funext i j
  show decode (2 * p) (transferMat A B i j) = _
  rw [show transferMat A B i j
        = transferEntry A B (ofIdx i).1 (ofIdx j).1 (ofIdx i).2 (ofIdx j).2 from rfl,
    decode_transferEntry]
  rfl

/-- The complex transfer entry at flattened bond pairs is the physical-index sum of conjugated
first-tensor entries times second-tensor entries. -/
theorem transferCc_pair {d Da Db : ℕ} (Abar : Fin d → Matrix (Fin Da) (Fin Da) ℂ)
    (Bbar : Fin d → Matrix (Fin Db) (Fin Db) ℂ) (a a' : Fin Da) (b b' : Fin Db) :
    transferCc Abar Bbar (toIdx a b) (toIdx a' b')
      = ∑ s : Fin d, conj (Abar s a a') * Bbar s b b' := by
  show (∑ s : Fin d,
      conj (Abar s (ofIdx (toIdx a b)).1 (ofIdx (toIdx a' b')).1)
        * Bbar s (ofIdx (toIdx a b)).2 (ofIdx (toIdx a' b')).2) = _
  simp only [ofIdx_toIdx]

/-- The product of a finite sequence factors into the product of its initial segment and its
final element. -/
private theorem listProd_ofFn_succ' {α : Type*} [Monoid α] {n : ℕ} (f : Fin (n + 1) → α) :
    (List.ofFn f).prod = (List.ofFn fun i : Fin n => f i.castSucc).prod * f (Fin.last n) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one]

/-- The product of two complex conjugates is the conjugate of their product. -/
private theorem conj_mul_eq (x y : ℂ) : conj x * conj y = conj (x * y) :=
  (map_mul (starRingEnd ℂ) x y).symm

/-- A finite sum of complex conjugates is the conjugate of the finite sum. -/
private theorem conj_sum_eq {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (∑ i : ι, conj (g i)) = conj (∑ i : ι, g i) :=
  (map_sum (starRingEnd ℂ) g Finset.univ).symm

/-- Interchange the first pair and the second pair of indices in a fourfold finite sum. -/
private theorem sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    {M : Type*} [AddCommMonoid M] (f : α → β → γ → δ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d)
      = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d :=
  have h1 : (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d)
      = ∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2 :=
    Eq.trans
      ((Fintype.sum_prod_type
        (fun p : α × β => ∑ c : γ, ∑ d : δ, f p.1 p.2 c d)).symm)
      (Finset.sum_congr rfl fun p _ =>
        (Fintype.sum_prod_type (fun q : γ × δ => f p.1 p.2 q.1 q.2)).symm)
  have h2 : (∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2)
      = ∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2 :=
    Finset.sum_comm
  have h3 : (∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2)
      = ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d :=
    Eq.trans
      (Finset.sum_congr rfl fun q _ =>
        Fintype.sum_prod_type (fun p : α × β => f p.1 p.2 q.1 q.2))
      (Fintype.sum_prod_type (fun q : γ × δ => ∑ a : α, ∑ b : β, f a b q.1 q.2))
  h1.trans (h2.trans h3)

/-- An entry of the product of double-layer transfer matrices equals the physical-configuration
sum of a conjugated first matrix-product entry times a second matrix-product entry. -/
theorem transfer_prod_eq_sum {d Da Db : ℕ} :
    ∀ (n : ℕ) (Abar : Fin n → Fin d → Matrix (Fin Da) (Fin Da) ℂ)
      (Bbar : Fin n → Fin d → Matrix (Fin Db) (Fin Db) ℂ)
      (a0 a1 : Fin Da) (b0 b1 : Fin Db),
      (List.ofFn fun j : Fin n => transferCc (Abar j) (Bbar j)).prod
          (toIdx a0 b0) (toIdx a1 b1)
        = ∑ x : Fin n → Fin d, conj (prodAt Abar x a0 a1) * prodAt Bbar x b0 b1 := by
  intro n
  induction n with
  | zero =>
    intro Abar Bbar a0 a1 b0 b1
    have hprodA : ∀ (x : Fin 0 → Fin d),
        prodAt Abar x = (1 : Matrix (Fin Da) (Fin Da) ℂ) := by
      intro x
      show (List.ofFn fun i : Fin 0 => Abar i (x i)).prod = 1
      rw [List.ofFn_zero, List.prod_nil]
    have hprodB : ∀ (x : Fin 0 → Fin d),
        prodAt Bbar x = (1 : Matrix (Fin Db) (Fin Db) ℂ) := by
      intro x
      show (List.ofFn fun i : Fin 0 => Bbar i (x i)).prod = 1
      rw [List.ofFn_zero, List.prod_nil]
    have hsum : (∑ x : Fin 0 → Fin d, conj (prodAt Abar x a0 a1) * prodAt Bbar x b0 b1)
        = conj ((1 : Matrix (Fin Da) (Fin Da) ℂ) a0 a1)
            * ((1 : Matrix (Fin Db) (Fin Db) ℂ) b0 b1) := by
      refine (Fintype.sum_eq_single (fun i : Fin 0 => Fin.elim0 i) ?_).trans ?_
      · intro x hx
        exact absurd (funext (fun i => Fin.elim0 i) : x = fun i => Fin.elim0 i) hx
      · simp only [hprodA, hprodB]
    rw [hsum, List.ofFn_zero, List.prod_nil, Matrix.one_apply, Matrix.one_apply,
      Matrix.one_apply]
    by_cases ha : a0 = a1
    · obtain rfl := ha
      by_cases hb : b0 = b1
      · obtain rfl := hb
        rw [if_pos rfl, if_pos rfl, if_pos rfl]
        simp
      · rw [if_neg (fun h => hb (toIdx_eq_iff.mp h).2), if_pos rfl, if_neg hb]
        simp
    · by_cases hb : b0 = b1
      · obtain rfl := hb
        rw [if_neg (fun h => ha (toIdx_eq_iff.mp h).1), if_neg ha, if_pos rfl]
        simp
      · rw [if_neg (fun h => ha (toIdx_eq_iff.mp h).1), if_neg ha, if_neg hb]
        simp
  | succ n ih =>
    intro Abar Bbar a0 a1 b0 b1
    have hsnoc : (∑ x : Fin n → Fin d, ∑ s : Fin d,
          conj (prodAt Abar (@Fin.snoc n (fun _ => Fin d) x s) a0 a1)
            * prodAt Bbar (@Fin.snoc n (fun _ => Fin d) x s) b0 b1)
        = ∑ y : Fin (n + 1) → Fin d, conj (prodAt Abar y a0 a1) * prodAt Bbar y b0 b1 :=
      Eq.trans
        ((Fintype.sum_prod_type
          (fun q : (Fin n → Fin d) × Fin d =>
            conj (prodAt Abar (@Fin.snoc n (fun _ => Fin d) q.1 q.2) a0 a1)
              * prodAt Bbar (@Fin.snoc n (fun _ => Fin d) q.1 q.2) b0 b1)).symm)
        (Equiv.sum_comp ((snocEquiv n d).symm)
          (fun y : Fin (n + 1) → Fin d => conj (prodAt Abar y a0 a1) * prodAt Bbar y b0 b1))
    calc (List.ofFn fun j : Fin (n + 1) => transferCc (Abar j) (Bbar j)).prod
            (toIdx a0 b0) (toIdx a1 b1)
        = ((List.ofFn fun j : Fin n => transferCc (Abar j.castSucc) (Bbar j.castSucc)).prod
            * transferCc (Abar (Fin.last n)) (Bbar (Fin.last n))) (toIdx a0 b0) (toIdx a1 b1) :=
          congrArg (fun P : Matrix (Fin (Da * Db)) (Fin (Da * Db)) ℂ =>
            P (toIdx a0 b0) (toIdx a1 b1))
            (listProd_ofFn_succ' (fun j : Fin (n + 1) => transferCc (Abar j) (Bbar j)))
      _ = ∑ k : Fin (Da * Db),
            (List.ofFn fun j : Fin n => transferCc (Abar j.castSucc) (Bbar j.castSucc)).prod
                (toIdx a0 b0) k
              * transferCc (Abar (Fin.last n)) (Bbar (Fin.last n)) k (toIdx a1 b1) := by
          rw [Matrix.mul_apply]
      _ = ∑ p : Fin Da × Fin Db,
            (List.ofFn fun j : Fin n => transferCc (Abar j.castSucc) (Bbar j.castSucc)).prod
                (toIdx a0 b0) (toIdx p.1 p.2)
              * transferCc (Abar (Fin.last n)) (Bbar (Fin.last n)) (toIdx p.1 p.2)
                  (toIdx a1 b1) :=
          (Equiv.sum_comp (finProdFinEquiv (m := Da) (n := Db)) _).symm
      _ = ∑ p : Fin Da × Fin Db,
            (∑ x : Fin n → Fin d, conj (prodAt (fun i => Abar i.castSucc) x a0 p.1)
                * prodAt (fun i => Bbar i.castSucc) x b0 p.2)
              * (∑ s : Fin d, conj (Abar (Fin.last n) s p.1 a1)
                * Bbar (Fin.last n) s p.2 b1) := by
          apply Finset.sum_congr rfl
          intro p _
          exact congrArg₂ (· * ·)
            (ih (fun i => Abar i.castSucc) (fun i => Bbar i.castSucc) a0 p.1 b0 p.2)
            (transferCc_pair (Abar (Fin.last n)) (Bbar (Fin.last n)) p.1 a1 p.2 b1)
      _ = ∑ a' : Fin Da, ∑ b' : Fin Db,
            (∑ x : Fin n → Fin d, conj (prodAt (fun i => Abar i.castSucc) x a0 a')
                * prodAt (fun i => Bbar i.castSucc) x b0 b')
              * (∑ s : Fin d, conj (Abar (Fin.last n) s a' a1)
                * Bbar (Fin.last n) s b' b1) :=
          Fintype.sum_prod_type _
      _ = ∑ a' : Fin Da, ∑ b' : Fin Db, ∑ x : Fin n → Fin d, ∑ s : Fin d,
            (conj (prodAt (fun i => Abar i.castSucc) x a0 a')
                * prodAt (fun i => Bbar i.castSucc) x b0 b')
              * (conj (Abar (Fin.last n) s a' a1)
                * Bbar (Fin.last n) s b' b1) := by
          apply Finset.sum_congr rfl
          intro a' _
          apply Finset.sum_congr rfl
          intro b' _
          exact Fintype.sum_mul_sum _ _
      _ = ∑ x : Fin n → Fin d, ∑ s : Fin d, ∑ a' : Fin Da, ∑ b' : Fin Db,
            (conj (prodAt (fun i => Abar i.castSucc) x a0 a')
                * prodAt (fun i => Bbar i.castSucc) x b0 b')
              * (conj (Abar (Fin.last n) s a' a1)
                * Bbar (Fin.last n) s b' b1) :=
          sum4_comm _
      _ = ∑ x : Fin n → Fin d, ∑ s : Fin d, ∑ a' : Fin Da, ∑ b' : Fin Db,
            conj (prodAt (fun i => Abar i.castSucc) x a0 a' * Abar (Fin.last n) s a' a1)
              * (prodAt (fun i => Bbar i.castSucc) x b0 b' * Bbar (Fin.last n) s b' b1) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro a' _
          apply Finset.sum_congr rfl
          intro b' _
          rw [mul_mul_mul_comm, conj_mul_eq]
      _ = ∑ x : Fin n → Fin d, ∑ s : Fin d,
            (∑ a' : Fin Da, conj (prodAt (fun i => Abar i.castSucc) x a0 a'
                * Abar (Fin.last n) s a' a1))
              * (∑ b' : Fin Db, prodAt (fun i => Bbar i.castSucc) x b0 b'
                * Bbar (Fin.last n) s b' b1) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro s _
          exact (Fintype.sum_mul_sum _ _).symm
      _ = ∑ x : Fin n → Fin d, ∑ s : Fin d,
            conj (∑ a' : Fin Da, prodAt (fun i => Abar i.castSucc) x a0 a'
                * Abar (Fin.last n) s a' a1)
              * (∑ b' : Fin Db, prodAt (fun i => Bbar i.castSucc) x b0 b'
                * Bbar (Fin.last n) s b' b1) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro s _
          rw [conj_sum_eq]
      _ = ∑ x : Fin n → Fin d, ∑ s : Fin d,
            conj ((prodAt (fun i => Abar i.castSucc) x * Abar (Fin.last n) s) a0 a1)
              * ((prodAt (fun i => Bbar i.castSucc) x * Bbar (Fin.last n) s) b0 b1) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro s _
          rw [← Matrix.mul_apply, ← Matrix.mul_apply]
      _ = ∑ x : Fin n → Fin d, ∑ s : Fin d,
            conj (prodAt Abar (@Fin.snoc n (fun _ => Fin d) x s) a0 a1)
              * prodAt Bbar (@Fin.snoc n (fun _ => Fin d) x s) b0 b1 := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro s _
          rw [← prodAt_snoc, ← prodAt_snoc]
      _ = ∑ y : Fin (n + 1) → Fin d, conj (prodAt Abar y a0 a1) * prodAt Bbar y b0 b1 :=
          hsnoc

/-- The left virtual index at a site, taking the boundary value `a` at the first site. -/
private def bondLeftIdx {n D : ℕ} (a : Fin D) (α : Fin (n - 1) → Fin D) (i : Fin n) : Fin D :=
  if (i : ℕ) = 0 then a
  else if h2 : (i : ℕ) - 1 < n - 1 then α ⟨(i : ℕ) - 1, h2⟩ else a

/-- The right virtual index at a site, taking the boundary value `b` at the final site. -/
private def bondRightIdx {n D : ℕ} (b : Fin D) (α : Fin (n - 1) → Fin D) (i : Fin n) : Fin D :=
  if h : (i : ℕ) < n - 1 then α ⟨(i : ℕ), h⟩ else b

/-- The internal-bond sum for an MPS with arbitrary endpoints, using the identity-matrix entry
for an empty chain. -/
noncomputable def bondAmp {n d D : ℕ}
    (M : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
    (a b : Fin D) : ℂ :=
  if n = 0 then (if a = b then 1 else 0)
  else ∑ α : Fin (n - 1) → Fin D,
    ∏ i : Fin n, M i (x i) (bondLeftIdx a α i) (bondRightIdx b α i)

/-- An appended finite function agrees with its original prefix at an index strictly before the
final position. -/
private theorem snoc_of_lt {m D : ℕ} {β : Fin m → Fin D} {k : Fin D}
    {j : Fin (m + 1)} (hj : (j : ℕ) < m) :
    @Fin.snoc m (fun _ => Fin D) β k j = β ⟨(j : ℕ), hj⟩ := by
  show @Fin.snoc m (fun _ => Fin D) β k (Fin.castSucc ⟨(j : ℕ), hj⟩) = β ⟨(j : ℕ), hj⟩
  exact Fin.snoc_castSucc _ _ _

/-- An appended finite function takes the appended value at its final position. -/
private theorem snoc_of_last {m D : ℕ} {β : Fin m → Fin D} {k : Fin D}
    {j : Fin (m + 1)} (hj : (j : ℕ) = m) :
    @Fin.snoc m (fun _ => Fin D) β k j = k := by
  have hj' : j = Fin.last m := by
    apply Fin.ext
    rw [Fin.val_last m]
    exact hj
  rw [hj']
  exact Fin.snoc_last _ _

/-- Appending an internal bond leaves the left indices of the initial sites unchanged. -/
private theorem bondLeftIdx_snoc {m D : ℕ} (a k : Fin D) (β : Fin m → Fin D)
    (i : Fin (m + 1)) :
    bondLeftIdx a (@Fin.snoc m (fun _ => Fin D) β k) i.castSucc = bondLeftIdx a β i := by
  unfold bondLeftIdx
  rw [Fin.val_castSucc]
  by_cases hi : (i : ℕ) = 0
  · rw [hi, if_pos rfl, if_pos rfl]
  · rw [if_neg hi, if_neg hi]
    have h1 : (i : ℕ) - 1 < (m + 1 + 1) - 1 := by have := i.isLt; omega
    have h2 : (i : ℕ) - 1 < (m + 1) - 1 := by have := i.isLt; omega
    rw [dif_pos h1, dif_pos h2]
    exact snoc_of_lt _

/-- For the initial sites, appending the bond `k` makes their right-index formula agree with a
prefix chain whose right boundary is `k`. -/
private theorem bondRightIdx_snoc {m D : ℕ} (b k : Fin D) (β : Fin m → Fin D)
    (i : Fin (m + 1)) :
    bondRightIdx b (@Fin.snoc m (fun _ => Fin D) β k) i.castSucc = bondRightIdx k β i := by
  unfold bondRightIdx
  rw [Fin.val_castSucc]
  by_cases hi : (i : ℕ) < m
  · have h1 : (i : ℕ) < (m + 1 + 1) - 1 := by have := i.isLt; omega
    have h2 : (i : ℕ) < (m + 1) - 1 := by omega
    rw [dif_pos h1, dif_pos h2]
    exact snoc_of_lt hi
  · have h1 : (i : ℕ) = m := by have := i.isLt; omega
    have h2 : ¬(i : ℕ) < (m + 1) - 1 := by omega
    have h3 : (i : ℕ) < (m + 1 + 1) - 1 := by have := i.isLt; omega
    rw [dif_pos h3, dif_neg h2]
    exact snoc_of_last h1

/-- The left virtual index at the last site is the appended internal bond `k`. -/
private theorem bondLeftIdx_last {m D : ℕ} (a k : Fin D) (β : Fin m → Fin D) :
    bondLeftIdx a (@Fin.snoc m (fun _ => Fin D) β k) (Fin.last (m + 1)) = k := by
  unfold bondLeftIdx
  have h0 : ¬((Fin.last (m + 1) : ℕ) = 0) := by rw [Fin.val_last]; omega
  have h1 : ((Fin.last (m + 1) : ℕ)) - 1 < (m + 1 + 1) - 1 := by rw [Fin.val_last]; omega
  rw [if_neg h0, dif_pos h1]
  exact snoc_of_last (by
    show (Fin.last (m + 1) : ℕ) - 1 = m
    have := Fin.val_last (m + 1)
    omega)

/-- The right virtual index at the last site is the boundary value `b`. -/
private theorem bondRightIdx_last {m D : ℕ} (b k : Fin D) (β : Fin m → Fin D) :
    bondRightIdx b (@Fin.snoc m (fun _ => Fin D) β k) (Fin.last (m + 1)) = b := by
  unfold bondRightIdx
  have h1 : ¬((Fin.last (m + 1) : ℕ) < (m + 1 + 1) - 1) := by rw [Fin.val_last]; omega
  rw [dif_neg h1]

/-- A configuration's matrix product factors into the initial-site product and the final
selected matrix. -/
private theorem prodAt_castSucc {n d D : ℕ}
    (M : Fin (n + 1) → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin (n + 1) → Fin d) :
    prodAt M x = prodAt (fun i => M i.castSucc) (fun i => x i.castSucc)
      * M (Fin.last n) (x (Fin.last n)) :=
  listProd_ofFn_succ' _

/-- The explicit internal-bond amplitude with arbitrary endpoints equals the corresponding entry
of the ordered matrix product. -/
theorem bondAmp_eq_prodAt {d D : ℕ} :
    ∀ (n : ℕ) (M : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d)
      (a b : Fin D), bondAmp M x a b = prodAt M x a b := by
  intro n
  induction n with
  | zero =>
    intro M x a b
    show (if a = b then (1 : ℂ) else 0) = _
    rw [show (prodAt M x : Matrix (Fin D) (Fin D) ℂ) = 1 from by
      show (List.ofFn fun i : Fin 0 => M i (x i)).prod = 1
      rw [List.ofFn_zero, List.prod_nil]]
    rw [Matrix.one_apply]
  | succ n ih =>
    intro M x a b
    cases n with
    | zero =>
      have hL : ∀ α : Fin (1 - 1) → Fin D,
          (∏ i : Fin 1, M i (x i) (bondLeftIdx a α i) (bondRightIdx b α i))
            = M 0 (x 0) a b := by
        intro α
        rw [Fin.prod_univ_one]
        have hl : bondLeftIdx a α (0 : Fin 1) = a := by
          unfold bondLeftIdx
          exact if_pos rfl
        have hr : bondRightIdx b α (0 : Fin 1) = b := by
          unfold bondRightIdx
          rw [dif_neg (by omega : ¬((0 : Fin 1) : ℕ) < 1 - 1)]
        rw [hl, hr]
      show (∑ α : Fin (1 - 1) → Fin D,
          ∏ i : Fin 1, M i (x i) (bondLeftIdx a α i) (bondRightIdx b α i))
        = prodAt M x a b
      rw [Finset.sum_congr rfl fun α _ => hL α]
      have hsum : (∑ α : Fin (1 - 1) → Fin D, (M 0 (x 0) a b : ℂ)) = M 0 (x 0) a b := by
        refine (Fintype.sum_eq_single (fun i : Fin 0 => i.elim0) ?_).trans ?_
        · intro α hne
          exact absurd (funext (fun i => i.elim0) : α = fun i => i.elim0) hne
        · rfl
      rw [hsum]
      rw [show (prodAt M x : Matrix (Fin D) (Fin D) ℂ) = M 0 (x 0) from by
        show (List.ofFn fun i : Fin 1 => M i (x i)).prod = _
        rw [listProd_ofFn_succ' (fun i : Fin 1 => M i (x i)),
          List.ofFn_zero, List.prod_nil, one_mul]
        rfl]
    | succ m =>
      have hprod : ∀ α : Fin ((m + 2) - 1) → Fin D,
          (∏ i : Fin (m + 2), M i (x i) (bondLeftIdx a α i) (bondRightIdx b α i))
            = (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                (bondLeftIdx a α i.castSucc) (bondRightIdx b α i.castSucc))
              * M (Fin.last (m + 1)) (x (Fin.last (m + 1)))
                (bondLeftIdx a α (Fin.last (m + 1)))
                (bondRightIdx b α (Fin.last (m + 1))) :=
        fun α => Fin.prod_univ_castSucc _
      have hre : (∑ α : Fin ((m + 2) - 1) → Fin D,
            (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                (bondLeftIdx a α i.castSucc) (bondRightIdx b α i.castSucc))
              * M (Fin.last (m + 1)) (x (Fin.last (m + 1)))
                (bondLeftIdx a α (Fin.last (m + 1)))
                (bondRightIdx b α (Fin.last (m + 1))))
          = ∑ β : Fin ((m + 1) - 1) → Fin D, ∑ k : Fin D,
            (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                (bondLeftIdx a β i) (bondRightIdx k β i))
              * M (Fin.last (m + 1)) (x (Fin.last (m + 1))) k b := by
        have hE : (∑ α : Fin ((m + 2) - 1) → Fin D,
              (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                  (bondLeftIdx a α i.castSucc) (bondRightIdx b α i.castSucc))
                * M (Fin.last (m + 1)) (x (Fin.last (m + 1)))
                  (bondLeftIdx a α (Fin.last (m + 1)))
                  (bondRightIdx b α (Fin.last (m + 1))))
            = ∑ p : (Fin m → Fin D) × Fin D,
              (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                  (bondLeftIdx a (@Fin.snoc m (fun _ => Fin D) p.1 p.2) i.castSucc)
                  (bondRightIdx b (@Fin.snoc m (fun _ => Fin D) p.1 p.2) i.castSucc))
                * M (Fin.last (m + 1)) (x (Fin.last (m + 1)))
                  (bondLeftIdx a (@Fin.snoc m (fun _ => Fin D) p.1 p.2) (Fin.last (m + 1)))
                  (bondRightIdx b (@Fin.snoc m (fun _ => Fin D) p.1 p.2) (Fin.last (m + 1))) :=
          (Equiv.sum_comp ((snocEquiv m D).symm) fun α : Fin ((m + 2) - 1) → Fin D =>
            (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                (bondLeftIdx a α i.castSucc) (bondRightIdx b α i.castSucc))
              * M (Fin.last (m + 1)) (x (Fin.last (m + 1)))
                (bondLeftIdx a α (Fin.last (m + 1)))
                (bondRightIdx b α (Fin.last (m + 1)))).symm
        rw [hE, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro β _
        apply Finset.sum_congr rfl
        intro k _
        simp only [bondLeftIdx_snoc, bondRightIdx_snoc, bondLeftIdx_last, bondRightIdx_last]
      have hk : ∀ k : Fin D,
          (∑ β : Fin ((m + 1) - 1) → Fin D,
            ∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
              (bondLeftIdx a β i) (bondRightIdx k β i))
          = prodAt (fun i => M i.castSucc) (fun i => x i.castSucc) a k := by
        intro k
        rw [← ih (fun i => M i.castSucc) (fun i => x i.castSucc) a k]
        have hb : bondAmp (fun i => M i.castSucc) (fun i => x i.castSucc) a k
            = (∑ β : Fin ((m + 1) - 1) → Fin D,
              ∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                (bondLeftIdx a β i) (bondRightIdx k β i)) := by
          show (if m + 1 = 0 then (if a = k then (1 : ℂ) else 0)
              else ∑ β : Fin ((m + 1) - 1) → Fin D,
                ∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                  (bondLeftIdx a β i) (bondRightIdx k β i)) = _
          rw [if_neg (by omega)]
        rw [hb]
      have hswap : (∑ β : Fin ((m + 1) - 1) → Fin D, ∑ k : Fin D,
            (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                (bondLeftIdx a β i) (bondRightIdx k β i))
              * M (Fin.last (m + 1)) (x (Fin.last (m + 1))) k b)
          = ∑ k : Fin D, prodAt (fun i => M i.castSucc) (fun i => x i.castSucc) a k
              * M (Fin.last (m + 1)) (x (Fin.last (m + 1))) k b := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.sum_mul, hk k]
      calc bondAmp M x a b
          = ∑ α : Fin ((m + 2) - 1) → Fin D,
              ∏ i : Fin (m + 2), M i (x i) (bondLeftIdx a α i) (bondRightIdx b α i) := by
              show (if m + 2 = 0 then (if a = b then (1 : ℂ) else 0)
                  else ∑ α : Fin ((m + 2) - 1) → Fin D,
                    ∏ i : Fin (m + 2), M i (x i) (bondLeftIdx a α i) (bondRightIdx b α i)) = _
              rw [if_neg (by omega)]
        _ = ∑ α : Fin ((m + 2) - 1) → Fin D,
              (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                  (bondLeftIdx a α i.castSucc) (bondRightIdx b α i.castSucc))
                * M (Fin.last (m + 1)) (x (Fin.last (m + 1)))
                  (bondLeftIdx a α (Fin.last (m + 1)))
                  (bondRightIdx b α (Fin.last (m + 1))) :=
            Finset.sum_congr rfl fun α _ => hprod α
        _ = ∑ β : Fin ((m + 1) - 1) → Fin D, ∑ k : Fin D,
              (∏ i : Fin (m + 1), M i.castSucc (x i.castSucc)
                  (bondLeftIdx a β i) (bondRightIdx k β i))
                * M (Fin.last (m + 1)) (x (Fin.last (m + 1))) k b :=
            hre
        _ = ∑ k : Fin D,
              prodAt (fun i => M i.castSucc) (fun i => x i.castSucc) a k
                * M (Fin.last (m + 1)) (x (Fin.last (m + 1))) k b :=
            hswap
        _ = prodAt M x a b := by
            rw [show prodAt M x
                  = prodAt (fun i => M i.castSucc) (fun i => x i.castSucc)
                      * M (Fin.last (m + 1)) (x (Fin.last (m + 1))) from
                prodAt_castSucc M x]
            rw [Matrix.mul_apply]

/-- The standard open-boundary MPS amplitude equals `bondAmp` with both endpoints zero. -/
private theorem mpsAmplitude_eq_bondAmp {n d D : ℕ} [NeZero D]
    (M : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    mpsAmplitude M x = bondAmp M x 0 0 := by
  cases n with
  | zero =>
    show (∑ α : Fin (0 - 1) → Fin D,
        ∏ i : Fin 0, M i (x i) (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsLeftIdx α i)
          (Qatlib.Concepts.MpsAdaptation.MpsTransfer.mpsRightIdx α i))
      = if (0 : Fin D) = 0 then (1 : ℂ) else 0
    rw [if_pos rfl]
    refine (Fintype.sum_eq_single (fun i : Fin 0 => i.elim0) ?_).trans ?_
    · intro α hne
      exact absurd (funext (fun i => i.elim0) : α = fun i => i.elim0) hne
    · rw [Fin.prod_univ_zero]
  | succ n =>
    rfl

/-- The standard open-boundary MPS amplitude is the `(0, 0)` entry of the selected matrix
product. -/
theorem mpsAmplitude_eq_prodAt {n d D : ℕ} [NeZero D]
    (M : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    mpsAmplitude M x = prodAt M x 0 0 :=
  (mpsAmplitude_eq_bondAmp M x).trans (bondAmp_eq_prodAt n M x 0 0)

/-- Adding the zero Gaussian integer on the right leaves a Gaussian integer unchanged. -/
private theorem add_zero_right (x : GI) : add x ((0, 0) : GI) = x := by
  show (x.1 + 0, x.2 + 0) = x
  rw [Int.add_zero, Int.add_zero]

/-- Multiplication by the zero Gaussian integer on the right gives zero. -/
private theorem mul_zero_right (x : GI) : mul x ((0, 0) : GI) = ((0, 0) : GI) := by
  show (x.1 * 0 - x.2 * 0, x.1 * 0 + x.2 * 0) = ((0, 0) : ℤ × ℤ)
  simp only [Int.mul_zero]
  rfl

/-- A left-folded sum of zero Gaussian integers starting at zero is zero. -/
private theorem foldl_add_zeros (xs : List GI) (hz : ∀ z ∈ xs, z = ((0, 0) : GI)) :
    xs.foldl add ((0, 0) : GI) = ((0, 0) : GI) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, hz x List.mem_cons_self, add_zero_right]
    exact ih (fun z hz' => hz z (List.mem_cons_of_mem x hz'))

/-- A dot product against a zero Gaussian integer matrix is zero. -/
private theorem dot_zero {D : ℕ} (v : Fin D → GI) (j : Fin D) :
    dot v ((0 : Matrix (Fin D) (Fin D) GI)) j = ((0, 0) : GI) := by
  show (List.ofFn fun i : Fin D =>
      mul (v i) ((0 : Matrix (Fin D) (Fin D) GI) i j)).foldl add ((0, 0) : GI) = ((0, 0) : GI)
  have h : ∀ i : Fin D,
      mul (v i) ((0 : Matrix (Fin D) (Fin D) GI) i j) = ((0, 0) : GI) := by
    intro i
    rw [Matrix.zero_apply]
    exact mul_zero_right (v i)
  rw [show (List.ofFn fun i : Fin D =>
        mul (v i) ((0 : Matrix (Fin D) (Fin D) GI) i j))
      = List.ofFn fun _ : Fin D => ((0, 0) : GI) from
      congrArg List.ofFn (funext fun i => h i),
    List.ofFn_const D ((0, 0) : GI)]
  exact foldl_add_zeros _ (fun z hz => by
    rw [List.mem_replicate] at hz
    exact hz.2)

/-- A row update through a zero Gaussian integer matrix produces the zero vector. -/
private theorem row_zero {D : ℕ} (v : Fin D → GI) :
    row v ((0 : Matrix (Fin D) (Fin D) GI)) = fun _ => ((0, 0) : GI) := by
  funext j
  exact dot_zero v j

/-- A fold through zero matrices starting from the zero vector remains zero. -/
private theorem foldl_row_zero {D : ℕ} :
    ∀ (As : List (Matrix (Fin D) (Fin D) GI)),
      (∀ A ∈ As, A = (0 : Matrix (Fin D) (Fin D) GI)) →
      As.foldl row (fun _ => ((0, 0) : GI)) = fun _ => ((0, 0) : GI)
  | [], _ => rfl
  | A :: As, h => by
    rw [List.foldl_cons, h A List.mem_cons_self, row_zero]
    exact foldl_row_zero As (fun A' hA' => h A' (List.mem_cons_of_mem A hA'))

/-- A zero first matrix followed by zero matrices gives zero at the zero output index. -/
private theorem run_cons_zero {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI))
    (hz : ∀ A ∈ As, A = (0 : Matrix (Fin D) (Fin D) GI)) (hD : 0 < D) :
    run ((0 : Matrix (Fin D) (Fin D) GI) :: As) ⟨0, hD⟩ = ((0, 0) : GI) := by
  show As.foldl row (row (initial D) ((0 : Matrix (Fin D) (Fin D) GI))) ⟨0, hD⟩ = ((0, 0) : GI)
  rw [row_zero]
  show As.foldl row (fun _ => ((0, 0) : GI)) ⟨0, hD⟩ = ((0, 0) : GI)
  rw [foldl_row_zero As hz]

/-- A nonempty chain of zero matrices gives zero at the zero output index. -/
private theorem run_ofFn_zero {D n : ℕ} (hn : n ≠ 0) (hD : 0 < D) :
    run (List.ofFn fun _ : Fin n => (0 : Matrix (Fin D) (Fin D) GI)) ⟨0, hD⟩
      = ((0, 0) : GI) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m =>
    rw [List.ofFn_succ]
    exact run_cons_zero _ (fun A hA => by
      rw [List.mem_ofFn] at hA
      obtain ⟨i, hi⟩ := hA
      exact hi.symm) hD

/-- The dyadic overlap program decodes to the conjugate amplitude inner product and has the
empty-chain and empty-physical-space values specified by `clause1Statement`. -/
theorem g1 : clause1Statement := by
  intro n d Da Db p _ _ A B
  have hK : 0 < Da * Db := Nat.mul_pos (NeZero.pos Da) (NeZero.pos Db)
  have hlen : (transferList A B).length = n := List.length_ofFn
  have hword : Qatlib.Concepts.DyadicProgram.DyadicContract.standardMatrixWord (2 * p) (transferList A B)
      = (List.ofFn fun j : Fin n => transferCc (decodeTensor p A j) (decodeTensor p B j)).prod := by
    unfold Qatlib.Concepts.DyadicProgram.DyadicContract.standardMatrixWord
    rw [show transferList A B = List.ofFn fun j : Fin n => transferMat (A j) (B j) from rfl,
      List.map_ofFn]
    congr 1
    congr 1
    funext j
    show transferC p (A j) (B j) = transferCc (decodeTensor p A j) (decodeTensor p B j)
    rw [transferC_eq_transferCc]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have hscalar : overlapProgram A B = scalar hK (transferList A B) :=
      overlapProgram_of_pos A B hK
    have hdec := (Qatlib.Concepts.DyadicProgram.DyadicContract.decode_standard_scalar
      (Da * Db) (2 * p) hK (transferList A B)).1
    rw [hlen] at hdec
    rw [hscalar, hdec, hword]
    have hi : (⟨0, hK⟩ : Fin (Da * Db)) = toIdx (Da := Da) (Db := Db) (0 : Fin Da) (0 : Fin Db) :=
      (toIdx_zero_zero (Da := Da) (Db := Db)).symm
    rw [hi]
    rw [show (∑ x : Fin n → Fin d,
          conj (mpsAmplitude (decodeTensor p A) x) * mpsAmplitude (decodeTensor p B) x)
        = (∑ x : Fin n → Fin d,
          conj (prodAt (decodeTensor p A) x 0 0) * prodAt (decodeTensor p B) x 0 0) from
        Finset.sum_congr rfl fun x _ => by
          rw [mpsAmplitude_eq_prodAt, mpsAmplitude_eq_prodAt]]
    exact transfer_prod_eq_sum n (decodeTensor p A) (decodeTensor p B) 0 0 0 0
  · intro hn
    subst hn
    exact overlapProgram_empty_chain A B hK
  · intro hd hn0
    subst hd
    have hz : ∀ j : Fin n,
        transferMat (A j) (B j) = (0 : Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI) := by
      intro j
      funext i i'
      rfl
    rw [overlapProgram_of_pos A B hK]
    show run (transferList A B) ⟨0, hK⟩ = ((0, 0) : GI)
    rw [show transferList A B
        = List.ofFn fun j : Fin n => (0 : Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI) from
        congrArg List.ofFn (funext fun j => hz j)]
    exact run_ofFn_zero hn0 hK

/-- The product of a complex number with its conjugate is its squared norm, embedded in the
complex numbers. -/
theorem conj_mul_self (z : ℂ) : conj z * z = (Complex.normSq z : ℂ) :=
  (@Complex.normSq_eq_conj_mul_self z).symm

/-- The real part of an integer cast to the complex numbers is its real cast. -/
private theorem intCast_re (n : ℤ) : ((n : ℂ)).re = (n : ℝ) := by
  rw [← Complex.ofReal_intCast, Complex.ofReal_re]

/-- The imaginary part of an integer cast to the complex numbers is zero. -/
private theorem intCast_im (n : ℤ) : ((n : ℂ)).im = 0 := by
  rw [← Complex.ofReal_intCast, Complex.ofReal_im]

/-- Embedding a finite real sum of squared complex norms into the complex numbers commutes with
the sum. -/
private theorem sum_normSq_ofReal {ι : Type} [Fintype ι] (f : ι → ℂ) :
    ((∑ i : ι, Complex.normSq (f i) : ℝ) : ℂ) = ∑ i : ι, (Complex.normSq (f i) : ℂ) :=
  map_sum Complex.ofRealHom (fun i : ι => Complex.normSq (f i)) Finset.univ

/-- A decoded Gaussian integer equal to a real scalar has zero imaginary part. -/
private theorem decode_ofReal_im {q : ℕ} {z : GI} {S : ℝ}
    (h : decode q z = ((S : ℝ) : ℂ)) : (decode q z).im = 0 := by
  rw [h, Complex.ofReal_im]

/-- A decoded Gaussian integer equal to a real scalar has that scalar as its real part. -/
private theorem decode_ofReal_re {q : ℕ} {z : GI} {S : ℝ}
    (h : decode q z = ((S : ℝ) : ℂ)) : (decode q z).re = S := by
  rw [h, Complex.ofReal_re]

/-- The real part of the complex encoding of an integer pair is its first component. -/
private theorem add_mul_I_re (x y : ℤ) :
    (((x : ℂ) + (y : ℂ) * Complex.I)).re = (x : ℝ) := by
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, intCast_re, intCast_im]
  ring

/-- The imaginary part of the complex encoding of an integer pair is its second component. -/
private theorem add_mul_I_im (x y : ℤ) :
    (((x : ℂ) + (y : ℂ) * Complex.I)).im = (y : ℝ) := by
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, intCast_re, intCast_im]
  ring

/-- If a decoded Gaussian integer is a nonnegative real scalar, its imaginary integer component
is zero and its real integer component is nonnegative. -/
private theorem gi_of_decode_real {q : ℕ} {z : GI} {S : ℝ} (hS : 0 ≤ S)
    (h : decode q z = ((S : ℝ) : ℂ)) : z.2 = 0 ∧ 0 ≤ z.1 := by
  have hne : ((2 : ℂ) ^ q) ≠ 0 := pow_ne_zero q (by norm_num)
  have hnum : ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) = ((S : ℝ) : ℂ) * (2 : ℂ) ^ q := by
    have hdecode : ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / (2 : ℂ) ^ q = ((S : ℝ) : ℂ) := h
    exact (div_eq_iff hne).mp hdecode
  have hden : ((2 : ℂ) ^ q) = (((2 : ℝ) ^ q : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [hden, ← Complex.ofReal_mul] at hnum
  have him := congrArg Complex.im hnum
  have hre := congrArg Complex.re hnum
  rw [add_mul_I_im, Complex.ofReal_im] at him
  rw [add_mul_I_re, Complex.ofReal_re] at hre
  refine ⟨Int.cast_eq_zero.mp him, ?_⟩
  have hz1 : (0 : ℝ) ≤ (z.1 : ℝ) := by
    rw [hre]
    exact mul_nonneg hS (pow_nonneg (by norm_num) q)
  exact Int.cast_le.mp (by simpa using! hz1)

/-- The amplitude self-inner-product sum equals the sum of squared amplitude norms. -/
private theorem sum_conj_mul_eq_normSq {n d D : ℕ} [NeZero D] (p : ℕ)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) GI) :
    (∑ x : Fin n → Fin d,
        conj (mpsAmplitude (decodeTensor p A) x) * mpsAmplitude (decodeTensor p A) x)
      = ∑ x : Fin n → Fin d, (Complex.normSq (mpsAmplitude (decodeTensor p A) x) : ℂ) :=
  Finset.sum_congr rfl fun x _ => conj_mul_self (mpsAmplitude (decodeTensor p A) x)

/-- The physical amplitude inner product equals the overlap program decoded at precision `2 * p
* n`. -/
private theorem sum_conj_eq_decode {n d Da Db : ℕ} [NeZero Da] [NeZero Db] (p : ℕ)
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (∑ x : Fin n → Fin d,
        conj (mpsAmplitude (decodeTensor p A) x) * mpsAmplitude (decodeTensor p B) x)
      = decode (2 * p * n) (overlapProgram A B) :=
  (g1 n d Da Db p A B).1.symm

/-- The sum of squared decoded MPS amplitude norms equals the decoded self-overlap program. -/
private theorem sum_normSq_eq_decode {n d D : ℕ} [NeZero D] (p : ℕ)
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) GI) :
    (∑ x : Fin n → Fin d, (Complex.normSq (mpsAmplitude (decodeTensor p A) x) : ℂ))
      = decode (2 * p * n) (overlapProgram A A) :=
  (sum_conj_mul_eq_normSq p A).symm.trans (sum_conj_eq_decode p A A)

/-- The self-overlap is real and nonnegative, equals the sum of squared physical amplitude
norms, and satisfies the stated integer-component and degenerate-case identities. -/
theorem clause2_general {n d D p : ℕ} [NeZero D]
    (A : Fin n → Fin d → Matrix (Fin D) (Fin D) GI) :
    (decode (2 * p * n) (overlapProgram A A)).im = 0
    ∧ 0 ≤ (decode (2 * p * n) (overlapProgram A A)).re
    ∧ decode (2 * p * n) (overlapProgram A A)
        = ∑ x : Fin n → Fin d, (Complex.normSq (mpsAmplitude (decodeTensor p A) x) : ℂ)
    ∧ (overlapProgram A A).2 = 0
    ∧ 0 ≤ (overlapProgram A A).1
    ∧ (n = 0 → overlapProgram A A = ((1, 0) : GI))
    ∧ (d = 0 → n ≠ 0 → overlapProgram A A = ((0, 0) : GI)) := by
  obtain ⟨_, hn0, hd0⟩ := g1 n d D D p A A
  have hEq : decode (2 * p * n) (overlapProgram A A)
      = ∑ x : Fin n → Fin d, (Complex.normSq (mpsAmplitude (decodeTensor p A) x) : ℂ) :=
    (sum_normSq_eq_decode p A).symm
  have hreal : decode (2 * p * n) (overlapProgram A A)
      = ((∑ x : Fin n → Fin d, Complex.normSq (mpsAmplitude (decodeTensor p A) x) : ℝ) : ℂ) :=
    hEq.trans (sum_normSq_ofReal _).symm
  have hS : (0 : ℝ) ≤ ∑ x : Fin n → Fin d, Complex.normSq (mpsAmplitude (decodeTensor p A) x) :=
    Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _
  refine ⟨?_, ?_, hEq, ?_, ?_, hn0, hd0⟩
  · exact decode_ofReal_im hreal
  · rw [decode_ofReal_re hreal]; exact hS
  · exact (gi_of_decode_real hS hreal).1
  · exact (gi_of_decode_real hS hreal).2

/-- The product-state example has Gaussian integer self-overlap `(4, 0)` and decoded squared
norm four. -/
theorem productI_consumer : consumerProductI := by
  have hprog : overlapProgram prodITensors prodITensors = ((4, 0) : GI) := rfl
  have hdec : decode (2 * 0 * 2) (overlapProgram prodITensors prodITensors) = (4 : ℂ) := by
    rw [hprog]
    show (((4 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ (2 * 0 * 2) = (4 : ℂ)
    norm_num
  exact ⟨hprog, hdec, (sum_normSq_eq_decode 0 prodITensors).trans hdec⟩

/-- The zero-input example has Gaussian integer self-overlap `(0, 0)` and decoded squared norm
zero. -/
theorem zeroInput_consumer : consumerZeroInput := by
  have hprog : overlapProgram zeroTensors zeroTensors = ((0, 0) : GI) := rfl
  have hdec : decode (2 * 0 * 2) (overlapProgram zeroTensors zeroTensors) = (0 : ℂ) := by
    rw [hprog]
    show (((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ (2 * 0 * 2) = (0 : ℂ)
    norm_num
  exact ⟨hprog, hdec, (sum_normSq_eq_decode 0 zeroTensors).trans hdec⟩

/-- The unnormalized Bell example has Gaussian integer self-overlap `(2, 0)` and decoded squared
norm two. -/
theorem bell_consumer : consumerBell := by
  have hprog : overlapProgram bellTensors bellTensors = ((2, 0) : GI) := rfl
  have hdec : decode (2 * 0 * 2) (overlapProgram bellTensors bellTensors) = (2 : ℂ) := by
    rw [hprog]
    show (((2 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ (2 * 0 * 2) = (2 : ℂ)
    norm_num
  exact ⟨hprog, hdec, (sum_normSq_eq_decode 0 bellTensors).trans hdec⟩

/-- The orthogonal one-site examples have zero Gaussian integer overlap and zero decoded
amplitude inner product. -/
theorem orthogonal_consumer : consumerOrthogonal := by
  have hprog : overlapProgram orthoA orthoB = ((0, 0) : GI) := rfl
  have hdec : decode (2 * 0 * 1) (overlapProgram orthoA orthoB) = (0 : ℂ) := by
    rw [hprog]
    show (((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ (2 * 0 * 1) = (0 : ℂ)
    norm_num
  exact ⟨hprog, hdec, (sum_conj_eq_decode 0 orthoA orthoB).trans hdec⟩

/-- The empty-chain example has Gaussian integer self-overlap `(1, 0)` and decoded squared norm
one. -/
theorem emptyChain_consumer : consumerEmptyChain := by
  have hprog : overlapProgram emptyTensors emptyTensors = ((1, 0) : GI) := rfl
  have hdec : decode (2 * 0 * 0) (overlapProgram emptyTensors emptyTensors) = (1 : ℂ) := by
    rw [hprog]
    show (((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ (2 * 0 * 0) = (1 : ℂ)
    norm_num
  exact ⟨hprog, hdec, (sum_normSq_eq_decode 0 emptyTensors).trans hdec⟩

/-- The example with an empty physical index type has zero Gaussian integer self-overlap and
decoded squared norm. -/
theorem zeroPhysical_consumer : consumerZeroPhysical := by
  have hprog : overlapProgram zeroPhysicalTensors zeroPhysicalTensors = ((0, 0) : GI) := rfl
  have hdec : decode (2 * 0 * 1) (overlapProgram zeroPhysicalTensors zeroPhysicalTensors)
      = (0 : ℂ) := by
    rw [hprog]
    show (((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ (2 * 0 * 1) = (0 : ℂ)
    norm_num
  exact ⟨hprog, hdec, (sum_normSq_eq_decode 0 zeroPhysicalTensors).trans hdec⟩

/-- The self-overlap properties and six explicit example propositions collected in
`clause2Statement` hold. -/
theorem g2 : clause2Statement := by
  refine ⟨?_, productI_consumer, zeroInput_consumer, bell_consumer,
    orthogonal_consumer, emptyChain_consumer, zeroPhysical_consumer⟩
  intro n d D p instD A
  exact clause2_general A

/-- The constant seven-site tensor family with physical and bond dimensions six and Gaussian
integer entry `(1, -1)`. -/
private def g3cA : Fin 7 → Fin 6 → Matrix (Fin 6) (Fin 6) GI :=
  fun _ _ _ _ => ((1, -1) : GI)

/-- The second constant seven-site tensor family with Gaussian integer entry `(1, -1)` used in
the magnitude-bound counterexample. -/
private def g3cB : Fin 7 → Fin 6 → Matrix (Fin 6) (Fin 6) GI :=
  fun _ _ _ _ => ((1, -1) : GI)

/-- The constant `36` by `36` Gaussian integer matrix with entry `(12, 0)`. -/
private def g3cT : Matrix (Fin 36) (Fin 36) GI := fun _ _ => ((12, 0) : GI)

/-- Every double-layer transfer entry of the counterexample tensor families equals `(12, 0)`. -/
private theorem g3c_entry : ∀ (j : Fin 7) (a a' b b' : Fin 6),
    transferEntry (g3cA j) (g3cB j) a a' b b' = ((12, 0) : GI) := by
  intro j a a' b b'
  rfl

/-- Each site transfer matrix in the counterexample is `g3cT`. -/
private theorem g3c_mat : ∀ (j : Fin 7), transferMat (g3cA j) (g3cB j) = g3cT := by
  intro j
  funext i i'
  rfl

/-- The counterexample transfer list consists of seven copies of `g3cT`. -/
private theorem g3c_list : transferList g3cA g3cB = List.replicate 7 g3cT := by
  show (List.ofFn fun j : Fin 7 => transferMat (g3cA j) (g3cB j)) = List.replicate 7 g3cT
  rw [show (List.ofFn fun j : Fin 7 => transferMat (g3cA j) (g3cB j))
        = List.ofFn fun _ : Fin 7 => g3cT from
      congrArg List.ofFn (funext fun j => g3c_mat j),
    List.ofFn_const]

/-- Multiplication by `(12, 0)` scales both Gaussian integer components by twelve. -/
private theorem g3c_mul120 (x : GI) :
    mul x ((12, 0) : GI) = ((12 : ℤ) * x.1, (12 : ℤ) * x.2) := by
  show (x.1 * 12 - x.2 * 0, x.1 * 0 + x.2 * 12) = (12 * x.1, 12 * x.2)
  rw [Prod.mk.injEq]
  constructor <;> ring

/-- Summing `n` copies of a Gaussian integer adds `n` times each component to the initial pair. -/
private theorem g3c_foldlAdd : ∀ (n : ℕ) (y z : GI),
    (List.replicate n y).foldl add z = ((z.1 + (n : ℤ) * y.1, z.2 + (n : ℤ) * y.2) : GI) := by
  intro n
  induction n with
  | zero =>
    intro y z
    rw [List.replicate_zero, List.foldl_nil]
    simp only [Int.natCast_zero, Int.zero_mul, Int.add_zero]
  | succ n ih =>
    intro y z
    rw [List.replicate_succ, List.foldl_cons, ih]
    show ((z.1 + y.1 + (n : ℤ) * y.1, z.2 + y.2 + (n : ℤ) * y.2) : GI)
      = (z.1 + ((n + 1 : ℕ) : ℤ) * y.1, z.2 + ((n + 1 : ℕ) : ℤ) * y.2)
    rw [Prod.mk.injEq]
    constructor <;> push_cast <;> ring

/-- Updating the initial row through `g3cT` gives the constant row `(12, 0)`. -/
private theorem g3c_rowInit : row (initial 36) g3cT = fun _ => ((12, 0) : GI) := by
  funext j
  show dot (initial 36) g3cT j = _
  rfl

/-- Updating a constant row through `g3cT` scales both components by `432`. -/
private theorem g3c_rowConst (x : GI) :
    row (fun _ => x) g3cT = fun _ => ((432 * x.1, 432 * x.2) : GI) := by
  funext j
  show dot (fun _ => x) g3cT j = _
  show (List.ofFn fun i : Fin 36 => mul x ((12, 0) : GI)).foldl add ((0, 0) : GI) = _
  rw [List.ofFn_const 36 (mul x ((12, 0) : GI)), g3c_foldlAdd, g3c_mul120]
  show ((0 + (36 : ℤ) * (12 * x.1), 0 + (36 : ℤ) * (12 * x.2)) : GI) = (432 * x.1, 432 * x.2)
  rw [Prod.mk.injEq]
  constructor <;> ring

/-- Folding through `k` copies of `g3cT` scales a constant row's components by `432 ^ k`. -/
private theorem g3c_foldlRow : ∀ (k : ℕ) (x : GI),
    (List.replicate k g3cT).foldl row (fun _ => x)
      = fun _ => ((x.1 * 432 ^ k, x.2 * 432 ^ k) : GI) := by
  intro k
  induction k with
  | zero =>
    intro x
    rw [List.replicate_zero, List.foldl_nil]
    funext i
    show x = (x.1 * 432 ^ 0, x.2 * 432 ^ 0)
    rw [pow_zero, Int.mul_one, Int.mul_one]
  | succ k ih =>
    intro x
    rw [List.replicate_succ, List.foldl_cons]
    have hrow : row (fun _ => x) g3cT = fun _ => ((x.1 * 432, x.2 * 432) : GI) := by
      rw [g3c_rowConst x]
      funext i
      show ((432 * x.1, 432 * x.2) : GI) = (x.1 * 432, x.2 * 432)
      rw [Prod.mk.injEq]
      constructor <;> ring
    rw [hrow, ih (x.1 * 432, x.2 * 432)]
    funext i
    show (((x.1 * 432) * 432 ^ k, (x.2 * 432) * 432 ^ k) : GI)
      = (x.1 * 432 ^ (k + 1), x.2 * 432 ^ (k + 1))
    rw [Prod.mk.injEq, pow_succ (432:ℤ)]
    constructor <;> ring

/-- The counterexample contraction produces the constant row `(77998046721343488, 0)`. -/
private theorem g3c_run :
    run (transferList g3cA g3cB) = fun _ => ((77998046721343488, 0) : GI) := by
  rw [g3c_list]
  show (List.replicate 7 g3cT).foldl row (initial 36) = _
  rw [List.replicate_succ, List.foldl_cons, g3c_rowInit]
  rw [g3c_foldlRow 6 ((12, 0) : GI)]
  funext i
  show (((12 : ℤ) * 432 ^ 6, (0 : ℤ) * 432 ^ 6) : GI) = (77998046721343488, 0)
  rw [Prod.mk.injEq, Int.zero_mul]
  constructor
  · norm_num
  · rfl

/-- Both integer components of every entry of `g3cA` have natural absolute value at most `2 ^
0`. -/
private theorem g3c_hA : ∀ (i : Fin 7) (s : Fin 6) (a a' : Fin 6),
    (g3cA i s a a').1.natAbs ≤ 2 ^ 0 ∧ (g3cA i s a a').2.natAbs ≤ 2 ^ 0 := by
  intro i s a a'
  show ((1, -1) : GI).1.natAbs ≤ 2 ^ 0 ∧ ((1, -1) : GI).2.natAbs ≤ 2 ^ 0
  decide

/-- Both integer components of every entry of `g3cB` have natural absolute value at most `2 ^
0`. -/
private theorem g3c_hB : ∀ (i : Fin 7) (s : Fin 6) (b b' : Fin 6),
    (g3cB i s b b').1.natAbs ≤ 2 ^ 0 ∧ (g3cB i s b b').2.natAbs ≤ 2 ^ 0 := by
  intro i s b b'
  show ((1, -1) : GI).1.natAbs ≤ 2 ^ 0 ∧ ((1, -1) : GI).2.natAbs ≤ 2 ^ 0
  decide

/-- The explicit counterexample output exceeds `magnitudeBound 7 6 6 0`. -/
private theorem g3c_out :
    ¬ BoundedGI (magnitudeBound 7 6 6 0) ((77998046721343488, 0) : GI) := by
  intro h
  have h1 : (77998046721343488 : ℕ) ≤ magnitudeBound 7 6 6 0 := h.1
  have hm : magnitudeBound 7 6 6 0 = 72057594037927936 := by decide
  rw [hm] at h1
  omega

/-- The combined magnitude-bound proposition `clause3Statement` is false. -/
theorem clause3Statement_false : ¬ clause3Statement := by
  intro h
  have h3 := h 7 6 6 6 0 g3cA g3cB g3c_hA g3c_hB
  obtain ⟨_, _, _, _, _, _, hEnv, _, _⟩ := h3
  have hD := hEnv 6 (le_refl 6) (le_refl 6)
  obtain ⟨_, _, hRun, _⟩ := hD
  have h0 := hRun 0
  rw [g3c_run] at h0
  exact g3c_out h0

/-- If each fold step increases a paired log length by `k`, folding over `xs` increases its
length by `k * xs.length`. -/
private theorem foldl_pair_log_length {α σ : Type*}
    (f : σ × List Ev → α → σ × List Ev) :
    ∀ (s : σ × List Ev) (xs : List α) (k : ℕ),
      (∀ acc x, (f acc x).2.length = acc.2.length + k) →
      (List.foldl f s xs).2.length = s.2.length + k * xs.length := by
  intro s xs
  induction xs generalizing s with
  | nil =>
    intro k hf
    simp
  | cons x xs ih =>
    intro k hf
    rw [List.foldl_cons, ih (f s x) k hf, hf s x, List.length_cons]
    ring

/-- A fold preserves log well-formedness when its initial log is well formed and every step
preserves that property. -/
private theorem foldl_pair_logWF {α σ : Type*}
    (f : σ × List Ev → α → σ × List Ev) :
    ∀ (s : σ × List Ev) (xs : List α),
      logWF s.2 → (∀ acc x, logWF acc.2 → logWF (f acc x).2) →
      logWF (List.foldl f s xs).2 := by
  intro s xs
  induction xs generalizing s with
  | nil =>
    intro hs hf
    exact hs
  | cons x xs ih =>
    intro hs hf
    exact ih (f s x) (hf s x hs) hf

/-- The length of a flattened finite family of lists equals the sum of their lengths. -/
private theorem length_flatten_ofFn {m : ℕ} {α : Type*} (f : Fin m → List α) :
    (List.ofFn f).flatten.length = ∑ i : Fin m, (f i).length := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The sum of a constant natural number over `Fin m` is `m * c`. -/
private theorem sum_const_fin {m : ℕ} (c : ℕ) : (∑ _i : Fin m, c) = m * c := by
  simp [Finset.sum_const]

/-- The empty arithmetic event log is well formed. -/
private theorem logWF_nil : logWF ([] : List Ev) := by
  intro e he
  exact absurd he List.not_mem_nil

/-- A Gaussian integer multiplication log has six events. -/
theorem mulEv_length (x y : GI) : (mulEv x y).length = 6 := rfl

/-- A Gaussian integer addition log has two events. -/
theorem addEv_length (x y : GI) : (addEv x y).length = 2 := rfl

/-- A Gaussian integer conjugation log has two events. -/
theorem negEv_length (x : GI) : (negEv x).length = 2 := rfl

/-- Constructing a transfer entry records exactly `10 * d` integer events. -/
theorem transferEntryEv_length {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI)
    (a a' : Fin Da) (b b' : Fin Db) :
    (transferEntryEv A B a a' b b').2.length = 10 * d := by
  have hstep : ∀ (acc : GI × List Ev) (pair : GI × GI),
      ((fun (acc : GI × List Ev) (pair : GI × GI) =>
          let ca := conjGI pair.1
          let m := mul ca pair.2
          (add acc.1 m, acc.2 ++ negEv pair.1 ++ mulEv ca pair.2 ++ addEv acc.1 m))
        acc pair).2.length = acc.2.length + 10 := by
    intro acc pair
    simp only [List.length_append, negEv_length, mulEv_length, addEv_length]
  show ((List.ofFn fun s : Fin d => (A s a a', B s b b')).foldl
      (fun (acc : GI × List Ev) (pair : GI × GI) =>
        let ca := conjGI pair.1
        let m := mul ca pair.2
        (add acc.1 m, acc.2 ++ negEv pair.1 ++ mulEv ca pair.2 ++ addEv acc.1 m))
      (((0, 0) : GI), [])).2.length = 10 * d
  rw [foldl_pair_log_length _ _ _ 10 hstep]
  show (([] : List Ev).length + 10 * (List.ofFn fun s : Fin d => (A s a a', B s b b')).length)
    = 10 * d
  rw [List.length_nil, List.length_ofFn, Nat.zero_add]

/-- Constructing a site transfer matrix records exactly `10 * d * (Da * Db) ^ 2` integer events. -/
theorem transferMatEv_length {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (transferMatEv A B).length = 10 * d * (Da * Db) ^ 2 := by
  have hinner : ∀ i : Fin (Da * Db),
      ((List.ofFn fun j : Fin (Da * Db) =>
          (transferEntryEv A B (ofIdx i).1 (ofIdx j).1 (ofIdx i).2 (ofIdx j).2).2).flatten).length
        = (Da * Db) * (10 * d) := by
    intro i
    rw [length_flatten_ofFn]
    simp only [transferEntryEv_length, sum_const_fin]
  show ((List.ofFn fun i : Fin (Da * Db) =>
      (List.ofFn fun j : Fin (Da * Db) =>
        (transferEntryEv A B (ofIdx i).1 (ofIdx j).1 (ofIdx i).2 (ofIdx j).2).2).flatten).flatten).length
    = 10 * d * (Da * Db) ^ 2
  rw [length_flatten_ofFn]
  simp only [hinner, sum_const_fin]
  ring

/-- Constructing all transfer matrices records exactly `10 * n * d * (Da * Db) ^ 2` integer
events. -/
theorem constructionEv_length {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (constructionEv A B).length = 10 * n * d * (Da * Db) ^ 2 := by
  show ((List.ofFn fun j : Fin n => transferMatEv (A j) (B j)).flatten).length
    = 10 * n * d * (Da * Db) ^ 2
  rw [length_flatten_ofFn]
  simp only [transferMatEv_length, sum_const_fin]
  ring

/-- A logged dot product records exactly `8 * D` integer events. -/
theorem dotEv_length {D : ℕ} (v : Fin D → GI) (T : Matrix (Fin D) (Fin D) GI) (j : Fin D) :
    (dotEv v T j).2.length = 8 * D := by
  have hstep : ∀ (acc : GI × List Ev) (pair : GI × GI),
      ((fun (acc : GI × List Ev) (pair : GI × GI) =>
          let m := mul pair.1 pair.2
          (add acc.1 m, acc.2 ++ mulEv pair.1 pair.2 ++ addEv acc.1 m))
        acc pair).2.length = acc.2.length + 8 := by
    intro acc pair
    simp only [List.length_append, mulEv_length, addEv_length]
  show ((List.ofFn fun i : Fin D => (v i, T i j)).foldl
      (fun (acc : GI × List Ev) (pair : GI × GI) =>
        let m := mul pair.1 pair.2
        (add acc.1 m, acc.2 ++ mulEv pair.1 pair.2 ++ addEv acc.1 m))
      (((0, 0) : GI), [])).2.length = 8 * D
  rw [foldl_pair_log_length _ _ _ 8 hstep]
  show (([] : List Ev).length + 8 * (List.ofFn fun i : Fin D => (v i, T i j)).length) = 8 * D
  rw [List.length_nil, List.length_ofFn, Nat.zero_add]

/-- A logged row update records exactly `8 * D ^ 2` integer events. -/
theorem rowEv_length {D : ℕ} (v : Fin D → GI) (T : Matrix (Fin D) (Fin D) GI) :
    (rowEv v T).length = 8 * D ^ 2 := by
  show ((List.ofFn fun j : Fin D => (dotEv v T j).2).flatten).length = 8 * D ^ 2
  rw [length_flatten_ofFn]
  simp only [dotEv_length, sum_const_fin]
  ring

/-- The contraction log of a matrix list has length `8 * D ^ 2 * As.length`. -/
private theorem runEv_gen_length {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI)) :
    (runEv As).length = 8 * D ^ 2 * As.length := by
  have hstep : ∀ (acc : (Fin D → GI) × List Ev) (T : Matrix (Fin D) (Fin D) GI),
      ((fun (acc : (Fin D → GI) × List Ev) (A : Matrix (Fin D) (Fin D) GI) =>
          (row acc.1 A, acc.2 ++ rowEv acc.1 A)) acc T).2.length
        = acc.2.length + 8 * D ^ 2 := by
    intro acc T
    simp only [List.length_append, rowEv_length]
  show ((As.foldl
      (fun (acc : (Fin D → GI) × List Ev) (A : Matrix (Fin D) (Fin D) GI) =>
        (row acc.1 A, acc.2 ++ rowEv acc.1 A))
      (initial D, [])).2).length = 8 * D ^ 2 * As.length
  rw [foldl_pair_log_length _ _ _ (8 * D ^ 2) hstep]
  show (([] : List Ev).length + 8 * D ^ 2 * As.length) = 8 * D ^ 2 * As.length
  rw [List.length_nil, Nat.zero_add]

/-- Contracting the overlap transfer list records exactly `8 * n * (Da * Db) ^ 2` integer
events. -/
theorem runEv_length {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (runEv (transferList A B)).length = 8 * n * (Da * Db) ^ 2 := by
  rw [runEv_gen_length]
  show 8 * (Da * Db) ^ 2 * (List.ofFn fun j : Fin n => transferMat (A j) (B j)).length
    = 8 * n * (Da * Db) ^ 2
  rw [List.length_ofFn]
  ring

/-- The overlap log contains `10 * n * d * (Da * Db) ^ 2` construction events plus `8 * n * (Da
* Db) ^ 2` contraction events. -/
theorem overlapLog_length {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (overlapLog A B).length
      = 10 * n * d * (Da * Db) ^ 2 + 8 * n * (Da * Db) ^ 2 := by
  show (constructionEv A B ++ runEv (transferList A B)).length = _
  rw [List.length_append, constructionEv_length, runEv_length]

/-- The construction, contraction, and total overlap log lengths satisfy their respective
declared event bounds. -/
theorem clause3_counts {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (constructionEv A B).length ≤ constructionBound n d Da Db
    ∧ (runEv (transferList A B)).length ≤ rowBound n Da Db
    ∧ (overlapTrace A B).2.length ≤ eventBound n d Da Db := by
  have ha : 10 * n * d * (Da * Db) ^ 2 ≤ 12 * n * d * (Da * Db) ^ 2 := by
    calc 10 * n * d * (Da * Db) ^ 2 = 10 * (n * d * (Da * Db) ^ 2) := by ring
      _ ≤ 12 * (n * d * (Da * Db) ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 12 * n * d * (Da * Db) ^ 2 := by ring
  have hb : 8 * n * (Da * Db) ^ 2 ≤ 12 * n * (Da * Db) ^ 2 := by
    calc 8 * n * (Da * Db) ^ 2 = 8 * (n * (Da * Db) ^ 2) := by ring
      _ ≤ 12 * (n * (Da * Db) ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 12 * n * (Da * Db) ^ 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [constructionEv_length, constructionBound]
    exact ha
  · rw [runEv_length, rowBound]
    exact hb
  · show (overlapLog A B).length ≤ eventBound n d Da Db
    rw [overlapLog_length, eventBound]
    calc 10 * n * d * (Da * Db) ^ 2 + 8 * n * (Da * Db) ^ 2
        ≤ 12 * n * d * (Da * Db) ^ 2 + 12 * n * (Da * Db) ^ 2 :=
          Nat.add_le_add ha hb
      _ = 12 * n * (d + 1) * (Da * Db) ^ 2 := by ring

/-- If both bond dimensions are at most `D`, construction and contraction log lengths are
bounded by `12 * n * d * D ^ 4` and `12 * n * D ^ 4`, respectively. -/
theorem clause3_counts_pow4 {n d Da Db D : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI)
    (hDa : Da ≤ D) (hDb : Db ≤ D) :
    (constructionEv A B).length ≤ 12 * n * d * D ^ 4
    ∧ (runEv (transferList A B)).length ≤ 12 * n * D ^ 4 := by
  have hK : (Da * Db) ^ 2 ≤ D ^ 4 := by
    have h : Da * Db ≤ D ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hDa hDb
    have h2 : (Da * Db) ^ 2 ≤ (D ^ 2) ^ 2 := Nat.pow_le_pow_left h 2
    rwa [show (D ^ 2) ^ 2 = D ^ 4 by ring] at h2
  refine ⟨?_, ?_⟩
  · rw [constructionEv_length]
    calc 10 * n * d * (Da * Db) ^ 2 = 10 * (n * d * (Da * Db) ^ 2) := by ring
      _ ≤ 12 * (n * d * (Da * Db) ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 12 * (n * d * D ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hK)
      _ = 12 * n * d * D ^ 4 := by ring
  · rw [runEv_length]
    calc 8 * n * (Da * Db) ^ 2 = 8 * (n * (Da * Db) ^ 2) := by ring
      _ ≤ 12 * (n * (Da * Db) ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 12 * (n * D ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hK)
      _ = 12 * n * D ^ 4 := by ring

/-- Every event in the Gaussian integer multiplication log satisfies its tagged integer
operation. -/
theorem mulEv_wf (x y : GI) : ∀ e ∈ mulEv x y, Ev.wf e := by
  intro e he
  simp only [mulEv, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Every event in the Gaussian integer addition log satisfies its tagged integer operation. -/
theorem addEv_wf (x y : GI) : ∀ e ∈ addEv x y, Ev.wf e := by
  intro e he
  simp only [addEv, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · rfl
  · rfl

/-- Every event in the Gaussian integer conjugation log satisfies its tagged integer operation. -/
theorem negEv_wf (x : GI) : ∀ e ∈ negEv x, Ev.wf e := by
  intro e he
  simp only [negEv, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · rfl
  · rfl

/-- A concatenated arithmetic log is well formed exactly when both constituent logs are well
formed. -/
theorem logWF_append {L L' : List Ev} : logWF (L ++ L') ↔ logWF L ∧ logWF L' := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append.mpr (Or.inl he)),
      fun e he => h e (List.mem_append.mpr (Or.inr he))⟩
  · intro h e he
    rcases List.mem_append.mp he with h1 | h2
    · exact h.1 e h1
    · exact h.2 e h2

/-- Flattening a list of well-formed arithmetic logs gives a well-formed log. -/
theorem logWF_flatten {Ls : List (List Ev)} (h : ∀ L ∈ Ls, logWF L) : logWF Ls.flatten := by
  intro e he
  obtain ⟨L, hL, heL⟩ := List.mem_flatten.mp he
  exact h L hL e heL

/-- The arithmetic log for constructing a transfer entry is well formed. -/
theorem logWF_transferEntryEv {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI)
    (a a' : Fin Da) (b b' : Fin Db) : logWF (transferEntryEv A B a a' b b').2 := by
  show logWF ((List.ofFn fun s : Fin d => (A s a a', B s b b')).foldl
      (fun (acc : GI × List Ev) (pair : GI × GI) =>
        let ca := conjGI pair.1
        let m := mul ca pair.2
        (add acc.1 m, acc.2 ++ negEv pair.1 ++ mulEv ca pair.2 ++ addEv acc.1 m))
      (((0, 0) : GI), [])).2
  apply foldl_pair_logWF _ _ _
  · exact logWF_nil
  · intro acc pair hacc
    show logWF (acc.2 ++ negEv pair.1 ++ mulEv (conjGI pair.1) pair.2
      ++ addEv acc.1 (mul (conjGI pair.1) pair.2))
    exact logWF_append.mpr
      ⟨logWF_append.mpr
        ⟨logWF_append.mpr ⟨hacc, negEv_wf pair.1⟩,
          mulEv_wf (conjGI pair.1) pair.2⟩,
        addEv_wf acc.1 (mul (conjGI pair.1) pair.2)⟩

/-- The arithmetic log for constructing a transfer matrix is well formed. -/
theorem logWF_transferMatEv {d Da Db : ℕ}
    (A : Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin d → Matrix (Fin Db) (Fin Db) GI) : logWF (transferMatEv A B) := by
  show logWF ((List.ofFn fun i : Fin (Da * Db) =>
    (List.ofFn fun j : Fin (Da * Db) =>
      (transferEntryEv A B (ofIdx i).1 (ofIdx j).1 (ofIdx i).2 (ofIdx j).2).2).flatten).flatten)
  apply logWF_flatten
  intro L1 hL1
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL1
  apply logWF_flatten
  intro L2 hL2
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL2
  exact logWF_transferEntryEv A B _ _ _ _

/-- The arithmetic log for constructing the full transfer list is well formed. -/
theorem logWF_constructionEv {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) : logWF (constructionEv A B) := by
  show logWF ((List.ofFn fun j : Fin n => transferMatEv (A j) (B j)).flatten)
  apply logWF_flatten
  intro L hL
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
  exact logWF_transferMatEv (A j) (B j)

/-- The arithmetic log for a Gaussian integer dot product is well formed. -/
theorem logWF_dotEv {D : ℕ} (v : Fin D → GI) (T : Matrix (Fin D) (Fin D) GI) (j : Fin D) :
    logWF (dotEv v T j).2 := by
  show logWF ((List.ofFn fun i : Fin D => (v i, T i j)).foldl
      (fun (acc : GI × List Ev) (pair : GI × GI) =>
        let m := mul pair.1 pair.2
        (add acc.1 m, acc.2 ++ mulEv pair.1 pair.2 ++ addEv acc.1 m))
      (((0, 0) : GI), [])).2
  apply foldl_pair_logWF _ _ _
  · exact logWF_nil
  · intro acc pair hacc
    show logWF (acc.2 ++ mulEv pair.1 pair.2 ++ addEv acc.1 (mul pair.1 pair.2))
    exact logWF_append.mpr
      ⟨logWF_append.mpr ⟨hacc, mulEv_wf pair.1 pair.2⟩,
        addEv_wf acc.1 (mul pair.1 pair.2)⟩

/-- The arithmetic log for a Gaussian integer row update is well formed. -/
theorem logWF_rowEv {D : ℕ} (v : Fin D → GI) (T : Matrix (Fin D) (Fin D) GI) :
    logWF (rowEv v T) := by
  show logWF ((List.ofFn fun j : Fin D => (dotEv v T j).2).flatten)
  apply logWF_flatten
  intro L hL
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hL
  exact logWF_dotEv v T j

/-- The arithmetic log for successive Gaussian integer row updates is well formed. -/
theorem logWF_runEv {D : ℕ} (As : List (Matrix (Fin D) (Fin D) GI)) : logWF (runEv As) := by
  show logWF ((As.foldl
      (fun (acc : (Fin D → GI) × List Ev) (A : Matrix (Fin D) (Fin D) GI) =>
        (row acc.1 A, acc.2 ++ rowEv acc.1 A))
      (initial D, [])).2)
  apply foldl_pair_logWF _ _ _
  · exact logWF_nil
  · intro acc T hacc
    show logWF (acc.2 ++ rowEv acc.1 T)
    exact logWF_append.mpr ⟨hacc, logWF_rowEv acc.1 T⟩

/-- The event log returned by the overlap trace is well formed. -/
theorem clause3_logWF {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    logWF (overlapTrace A B).2 := by
  show logWF (constructionEv A B ++ runEv (transferList A B))
  exact logWF_append.mpr
    ⟨logWF_constructionEv A B, logWF_runEv (transferList A B)⟩

/-- The value component of the overlap trace is exactly the overlap program output. -/
theorem clause3_erasure {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (overlapTrace A B).1 = overlapProgram A B := rfl

/-- An empty-chain overlap trace consists of the unit Gaussian integer and an empty event log. -/
theorem clause3_boundary_empty {n d Da Db : ℕ}
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    n = 0 → overlapTrace A B = (((1, 0) : GI), []) := by
  intro hn
  subst hn
  have hval : overlapProgram A B = ((1, 0) : GI) := by
    by_cases h : 0 < Da * Db
    · exact overlapProgram_empty_chain A B h
    · show (if h' : 0 < Da * Db then scalar h' (transferList A B) else ((1, 0) : GI)) = _
      simp [h]
  have hlog : overlapLog A B = ([] : List Ev) := by
    have hc : constructionEv A B = ([] : List Ev) := by
      show (List.ofFn fun j : Fin 0 => transferMatEv (A j) (B j)).flatten = []
      rw [List.ofFn_zero]
      rfl
    have hr : runEv (transferList A B) = ([] : List Ev) := by
      have htl : transferList A B
          = ([] : List (Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI)) := by
        show (List.ofFn fun j : Fin 0 => transferMat (A j) (B j)) = []
        exact List.ofFn_zero
      rw [htl]
      rfl
    show constructionEv A B ++ runEv (transferList A B) = []
    rw [hc, hr]
    rfl
  show (overlapProgram A B, overlapLog A B) = (((1, 0) : GI), [])
  rw [hval, hlog]

/-- For nonzero bond dimensions and a nonempty chain with no physical symbols, the overlap
program returns zero. -/
theorem clause3_boundary_zeroPhysical {n d Da Db : ℕ} [NeZero Da] [NeZero Db]
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    d = 0 → n ≠ 0 → overlapProgram A B = ((0, 0) : GI) := by
  intro hd hn0
  subst hd
  have hK : 0 < Da * Db := Nat.mul_pos (NeZero.pos Da) (NeZero.pos Db)
  have hz : ∀ j : Fin n,
      transferMat (A j) (B j) = (0 : Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI) := by
    intro j
    funext i i'
    rfl
  rw [overlapProgram_of_pos A B hK]
  show run (transferList A B) ⟨0, hK⟩ = ((0, 0) : GI)
  rw [show transferList A B
      = List.ofFn fun j : Fin n => (0 : Matrix (Fin (Da * Db)) (Fin (Da * Db)) GI) from
      congrArg List.ofFn (funext fun j => hz j)]
  exact run_ofFn_zero hn0 hK

/-- The overlap trace has the program output, a well-formed log, the stated event-count bounds,
and the empty-chain and empty-physical-space identities. -/
theorem clause3_logWF_and_counts {n d Da Db : ℕ} [NeZero Da] [NeZero Db]
    (A : Fin n → Fin d → Matrix (Fin Da) (Fin Da) GI)
    (B : Fin n → Fin d → Matrix (Fin Db) (Fin Db) GI) :
    (overlapTrace A B).1 = overlapProgram A B
    ∧ logWF (overlapTrace A B).2
    ∧ (constructionEv A B).length ≤ constructionBound n d Da Db
    ∧ (runEv (transferList A B)).length ≤ rowBound n Da Db
    ∧ (overlapTrace A B).2.length ≤ eventBound n d Da Db
    ∧ (∀ D : ℕ, Da ≤ D → Db ≤ D →
        (constructionEv A B).length ≤ 12 * n * d * D ^ 4
        ∧ (runEv (transferList A B)).length ≤ 12 * n * D ^ 4)
    ∧ (n = 0 → overlapTrace A B = (((1, 0) : GI), []))
    ∧ (d = 0 → n ≠ 0 → overlapProgram A B = ((0, 0) : GI)) := by
  refine ⟨clause3_erasure A B, clause3_logWF A B,
    (clause3_counts A B).1, (clause3_counts A B).2.1, (clause3_counts A B).2.2, ?_,
    clause3_boundary_empty A B, clause3_boundary_zeroPhysical A B⟩
  intro D hDa hDb
  exact clause3_counts_pow4 A B hDa hDb

end Qatlib.Concepts.DyadicOverlap.OverlapContract
