/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option backward.isDefEq.respectTransparency false

/-!
# Model — shared semantics for QInspired25

Fixed source: Mande–Shao, "Lower bounds for quantum-inspired classical algorithms via
communication complexity", arXiv:2402.15686v3 (Quantum 9, 1593 (2025)).

This file fixes the objects that every claim of the paper speaks about:

* `logBits` — the number of bits needed to specify an integer, the unit of all
  communication-cost statements (Theorem 10, p. 6, and Theorem 28, p. 16--17);
* `frobSqVec` / `frobSqMat` — squared Euclidean / Frobenius norms, so that the paper's
  `‖·‖_F²` never needs a square root (`κ_F²`, `‖A‖_F²`, `‖b‖²` are all used squared);
* `leastSquares_unique` — the normal-equation characterisation of `arg min ‖Ax-b‖`
  used in the row-sparse reduction (Proposition 12, p. 7--9);
* the `SQ` access model of Definitions 1--3 (p. 4) together with a query-counted
  quantum-inspired classical algorithm;
* the coordinator communication model of Section 2.2 (p. 4) and the three hard
  communication problems that the paper cites (Proposition 5 p. 5, Proposition 7
  p. 5, Proposition 9 p. 5).

Everything below is a definition or a theorem about these definitions; the
*external* hardness of Set-Disjointness / Gap-Hamming / Distributed Fourier
Sampling is *not* reproved here and appears as the named hypotheses
`SetDisjointnessHardness`, `GapHammingHardness`, `DistributedFourierSamplingHardness`.
The paper itself cites these as Propositions 5, 7 and 9 of the source.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace Qatlib.Papers.QInspired25.MainResults.Model

/-! ## §1. Bit length -/

/-- The number of bits needed to write an integer in `[0, n]`: `⌊log₂ n⌋ + 1`. -/
def logBits (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- `logBits n` is large enough that `n < 2 ^ logBits n`. -/
theorem lt_two_pow_logBits {n : ℕ} (hn : n ≠ 0) : n < 2 ^ logBits n := by
  unfold logBits
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  simpa [Nat.succ_eq_add_one] using this

/-- A positive input gives a positive bit count. -/
theorem logBits_pos {n : ℕ} (hn : 0 < n) : 0 < logBits n := by
  unfold logBits
  omega

/-- `logBits` is monotone. -/
theorem logBits_mono {a b : ℕ} (h : a ≤ b) : logBits a ≤ logBits b := by
  unfold logBits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

/-- `A + B ≤ A * B` when both are at least `2`. -/
theorem two_le_add_mul {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) : A + B ≤ A * B := by
  have hAB : (0 : ℤ) ≤ ((A : ℤ) - 1) * ((B : ℤ) - 1) :=
    Int.mul_nonneg (by omega) (by omega)
  have : ((A : ℤ) + B) ≤ ((A : ℤ) * B) := by nlinarith [hAB]
  exact_mod_cast this

/-- The product of two `ℕ`-inequalities with positive left sides. -/
theorem mul_lt_mul_nat {a b A B : ℕ} (ha : a < A) (hb : b < B) (ha0 : 0 < a) (hb0 : 0 < b) :
    a * b < A * B := by
  have h1 : (0 : ℤ) < (A : ℤ) - a := by omega
  have h2 : (0 : ℤ) < (B : ℤ) - b := by omega
  have hprod := mul_pos h1 h2
  have : ((a * b : ℕ) : ℤ) < ((A * B : ℕ) : ℤ) := by push_cast; nlinarith [hprod]
  exact_mod_cast this

/-- `logBits` of a product is at most the sum of the `logBits`. -/
theorem logBits_mul_le (a b : ℕ) : logBits (a * b) ≤ logBits a + logBits b := by
  rcases Nat.eq_zero_or_pos a with ha | ha <;> rcases Nat.eq_zero_or_pos b with hb | hb
  · simp [logBits, ha, hb]
  · simp [logBits, ha]
  · simp [logBits, hb]
  · unfold logBits
    have ha' : a < 2 ^ (Nat.log 2 a + 1) := by
      simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a
    have hb' : b < 2 ^ (Nat.log 2 b + 1) := by
      simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) b
    have hlt : a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
      mul_lt_mul_nat ha' hb' ha hb
    have hlt' : a * b < 2 ^ (Nat.log 2 a + 1 + (Nat.log 2 b + 1)) := by
      rw [pow_add]; exact hlt
    have hlog : Nat.log 2 (a * b) < Nat.log 2 a + 1 + (Nat.log 2 b + 1) :=
      Nat.log_lt_of_lt_pow (Nat.mul_pos ha hb).ne' hlt'
    exact Nat.succ_le_of_lt hlog

/-- `logBits` of a sum is at most the sum of the `logBits`. -/
theorem logBits_add_le (a b : ℕ) : logBits (a + b) ≤ logBits a + logBits b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [logBits]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [logBits]
  unfold logBits
  have ha2 : 2 ≤ 2 ^ (Nat.log 2 a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.log 2 a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb2 : 2 ≤ 2 ^ (Nat.log 2 b + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.log 2 b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ha' : a < 2 ^ (Nat.log 2 a + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a
  have hb' : b < 2 ^ (Nat.log 2 b + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) b
  have hsum : a + b < 2 ^ (Nat.log 2 a + 1) + 2 ^ (Nat.log 2 b + 1) := by omega
  have hle : 2 ^ (Nat.log 2 a + 1) + 2 ^ (Nat.log 2 b + 1)
      ≤ 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
    two_le_add_mul ha2 hb2
  have hlt : a + b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) := by omega
  have hlt' : a + b < 2 ^ (Nat.log 2 a + 1 + (Nat.log 2 b + 1)) := by
    rw [pow_add]; exact hlt
  have hlog : Nat.log 2 (a + b) < Nat.log 2 a + 1 + (Nat.log 2 b + 1) :=
    Nat.log_lt_of_lt_pow (Nat.add_pos_left ha b).ne' hlt'
  exact Nat.succ_le_of_lt hlog

/-! ## §2. Squared norms and inner products -/

/-- Squared Euclidean norm of a real vector. -/
def frobSqVec {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Inner product of two real vectors. -/
def innerVec {n : ℕ} (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i

/-- Squared Frobenius norm of a real matrix. -/
def frobSqMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- Squared Frobenius norm of a block matrix indexed by `Fin k × Fin n`. -/
def frobSqBlock {k n : ℕ} (A : Fin k → Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- The squared Frobenius norm of the zero vector is zero. -/
@[simp] theorem frobSqVec_zero {n : ℕ} : frobSqVec (fun _ : Fin n => (0 : ℝ)) = 0 := by
  simp [frobSqVec]

/-- The squared Frobenius norm is nonnegative. -/
theorem frobSqVec_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ frobSqVec v := by
  unfold frobSqVec
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The real inner product is symmetric. -/
theorem innerVec_comm {n : ℕ} (v w : Fin n → ℝ) : innerVec v w = innerVec w v := by
  unfold innerVec
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Pythagoras for the squared Euclidean norm. -/
theorem frobSqVec_add_eq {m : ℕ} (u v : Fin m → ℝ) (h : innerVec u v = 0) :
    frobSqVec (u + v) = frobSqVec u + frobSqVec v := by
  have hpt : ∑ i : Fin m, (u i + v i) ^ 2 =
      ∑ i : Fin m, (u i ^ 2 + v i ^ 2 + 2 * (u i * v i)) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i : Fin m, 2 * (u i * v i) = 0 := by
    rw [← Finset.mul_sum]
    unfold innerVec at h
    rw [h, mul_zero]
  unfold frobSqVec
  simp only [Pi.add_apply]
  rw [hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, h2, add_zero]

/-- The normal equations give the unique least-squares minimiser. -/
theorem frobSqVec_leastSquares {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {x : Fin n → ℝ}
    (h : Aᵀ *ᵥ (A *ᵥ x - b) = 0) (y : Fin n → ℝ) :
    frobSqVec (A *ᵥ y - b) = frobSqVec (A *ᵥ x - b) + frobSqVec (A *ᵥ (y - x)) := by
  have hdecomp : A *ᵥ y - b = (A *ᵥ x - b) + (A *ᵥ (y - x)) := by
    rw [Matrix.mulVec_sub]
    abel
  have hcross : innerVec (A *ᵥ x - b) (A *ᵥ (y - x)) = 0 := by
    have h1 : innerVec (A *ᵥ x - b) (A *ᵥ (y - x)) =
        innerVec ((A *ᵥ x - b) ᵥ* A) (y - x) := dotProduct_mulVec _ A _
    rw [h1, ← mulVec_transpose, h]
    simp [innerVec]
  rw [hdecomp, frobSqVec_add_eq _ _ hcross]

/-! ## §2b. Squared norms over an arbitrary finite index type

The row-sparse construction of Proposition 12 (p. 7--9) indexes rows by `Fin k × Fin n`
rather than by `Fin m`, so we need the same two facts for an arbitrary `Fintype`. -/

/-- Squared Euclidean norm of a real vector over an arbitrary finite index type. -/
def frobSqFun {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Inner product of two real vectors over an arbitrary finite index type. -/
def innerFun {ι : Type*} [Fintype ι] (v w : ι → ℝ) : ℝ := ∑ i, v i * w i

/-- Pythagoras for `frobSqFun`. -/
theorem frobSqFun_add_eq {ι : Type*} [Fintype ι] (u v : ι → ℝ) (h : innerFun u v = 0) :
    frobSqFun (u + v) = frobSqFun u + frobSqFun v := by
  have hpt : ∑ i : ι, (u i + v i) ^ 2 =
      ∑ i : ι, (u i ^ 2 + v i ^ 2 + 2 * (u i * v i)) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i : ι, 2 * (u i * v i) = 0 := by
    rw [← Finset.mul_sum]
    unfold innerFun at h
    rw [h, mul_zero]
  unfold frobSqFun
  simp only [Pi.add_apply]
  rw [hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, h2, add_zero]

/-- The normal equations give the least-squares property for an arbitrary row type. -/
theorem frobSqFun_leastSquares {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (b : ι → ℝ) {x : κ → ℝ}
    (h : Aᵀ *ᵥ (A *ᵥ x - b) = 0) (y : κ → ℝ) :
    frobSqFun (A *ᵥ y - b) = frobSqFun (A *ᵥ x - b) + frobSqFun (A *ᵥ (y - x)) := by
  have hdecomp : A *ᵥ y - b = (A *ᵥ x - b) + (A *ᵥ (y - x)) := by
    rw [Matrix.mulVec_sub]
    abel
  have hcross : innerFun (A *ᵥ x - b) (A *ᵥ (y - x)) = 0 := by
    have h1 : innerFun (A *ᵥ x - b) (A *ᵥ (y - x)) = innerFun ((A *ᵥ x - b) ᵥ* A) (y - x) :=
      dotProduct_mulVec _ A _
    rw [h1, ← mulVec_transpose, h]
    simp [innerFun]
  rw [hdecomp, frobSqFun_add_eq _ _ hcross]

/-! ## §3. The `SQ` access model (Definitions 1--3, p. 4) -/

/-- Sampling-and-query access to a real vector, `SQ(v)` of Definition 2 (p. 4):
entry queries, the squared norm, and the exact sampling law `|v_i|²/‖v‖²`. -/
structure SqVec (n : ℕ) where
  val : Fin n → ℝ
  normSq : ℝ
  normSq_eq : normSq = frobSqVec val
  prob : Fin n → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum : ∑ i, prob i = 1
  prob_eq : ∀ i, prob i = val i ^ 2 / normSq

/-- Sampling-and-query access to a real matrix, `SQ(A)` of Definition 3 (p. 4):
entry queries, the squared Frobenius norm, the sampling law `|A_ij|²/‖A‖_F²`, and the
row data `SQ(A_{i*})` for every row together with `SQ(a)` for `a = (‖A_{1*}‖, ...)`. -/
structure SqMat (m n : ℕ) where
  val : Fin m → Fin n → ℝ
  normSqF : ℝ
  normSqF_eq : normSqF = frobSqBlock val
  prob : Fin m → Fin n → ℝ
  prob_nonneg : ∀ i j, 0 ≤ prob i j
  prob_sum : ∑ i, ∑ j, prob i j = 1
  prob_eq : ∀ i j, prob i j = val i j ^ 2 / normSqF
  rowNormSq : Fin m → ℝ
  rowNormSq_eq : ∀ i, rowNormSq i = ∑ j, val i j ^ 2

/-- A query to a pair `(A, b)` of an SQ matrix and an SQ vector. -/
inductive PairQuery (m n : ℕ) where
  | matEntry (i : Fin m) (j : Fin n)
  | matNorm
  | matSample
  | matRowNorm (i : Fin m)
  | vecEntry (i : Fin n)
  | vecNorm
  | vecSample
  deriving DecidableEq

/-- All the answers an SQ oracle to `(A, b)` can give, indexed by the protocol's coin. -/
structure PairAnswerTuple (m n : ℕ) (Coin : Type) where
  matEntry : Coin → Fin m → Fin n → ℝ
  matNorm : Coin → ℝ
  matSample : Coin → Fin m × Fin n
  matRowNorm : Coin → Fin m → ℝ
  vecEntry : Coin → Fin n → ℝ
  vecNorm : Coin → ℝ
  vecSample : Coin → Fin n

/-- The canonical answers produced by an `SQ` oracle. -/
def PairAnswerTuple.ofSq {m n : ℕ} [NeZero m] [NeZero n] (A : SqMat m n) (b : SqVec n)
    (Coin : Type) : PairAnswerTuple m n Coin where
  matEntry := fun _ i j => A.val i j
  matNorm := fun _ => A.normSqF
  matSample := fun _ => (0, 0)
  matRowNorm := fun _ i => A.rowNormSq i
  vecEntry := fun _ i => b.val i
  vecNorm := fun _ => b.normSq
  vecSample := fun _ => 0

/-- Two answer families agree on a list of queries. -/
def PairAnswerTuple.agreeOn {m n : ℕ} {Coin : Type} (qs : List (PairQuery m n))
    (a a' : PairAnswerTuple m n Coin) : Prop :=
  (∀ (i : Fin m) (j : Fin n), PairQuery.matEntry i j ∈ qs → ∀ c, a.matEntry c i j = a'.matEntry c i j) ∧
  (∀ (i : Fin m), PairQuery.matRowNorm i ∈ qs → ∀ c, a.matRowNorm c i = a'.matRowNorm c i) ∧
  (∀ (i : Fin n), PairQuery.vecEntry i ∈ qs → ∀ c, a.vecEntry c i = a'.vecEntry c i) ∧
  (∀ c, PairQuery.matNorm ∈ qs → a.matNorm c = a'.matNorm c) ∧
  (∀ c, PairQuery.vecNorm ∈ qs → a.vecNorm c = a'.vecNorm c) ∧
  (∀ c, PairQuery.matSample ∈ qs → a.matSample c = a'.matSample c) ∧
  (∀ c, PairQuery.vecSample ∈ qs → a.vecSample c = a'.vecSample c)

/-- A quantum-inspired classical algorithm of query complexity `T` (Definition 3, p. 4):
`T` applications of `SQ(A)`, `SQ(b)` followed by an output. `respects` makes the query
count meaningful, i.e. the output only depends on the answers that were actually asked. -/
structure QicAlgorithm (m n : ℕ) (Coin : Type) (Out : Type) where
  queries : List (PairQuery m n)
  out : PairAnswerTuple m n Coin → Out
  respects : ∀ a a' : PairAnswerTuple m n Coin, a.agreeOn queries a' → out a = out a'

/-- The query complexity `T` of an algorithm. -/
def QicAlgorithm.cost {m n : ℕ} {Coin Out : Type} (alg : QicAlgorithm m n Coin Out) : ℕ :=
  alg.queries.length

/-! ## §4. Tasks and the `ε`-approximate sampling notion (Definition 8, p. 5) -/

/-- `ε`-approximate sampling: `‖P̃ - P‖₁ ≤ ε`. -/
def SamplesApprox {n : ℕ} (p q : Fin n → ℝ) (ε : ℝ) : Prop :=
  (∑ i, |p i - q i|) ≤ ε

/-- The sampling law of an explicitly given real vector, `v_i²/‖v‖²`. -/
def vecDist {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => v i ^ 2 / frobSqVec v

/-! ## §5. The coordinator communication model (Section 2.2, p. 4) -/

/-- A randomised coordinator protocol: `Coin` is the protocol's finite randomness, `answer`
its Boolean output and `cost` the total number of bits on the channel. -/
structure RandProtocol (k : ℕ) (Input : Type) where
  Coin : Type
  [instFintype : Fintype Coin]
  [instNonempty : Nonempty Coin]
  answer : Coin → Input → Bool
  cost : Coin → Input → ℕ

attribute [instance] RandProtocol.instFintype RandProtocol.instNonempty

/-- Worst-case bit cost of a protocol over coins and inputs. -/
def RandProtocol.worstCost {k : ℕ} {Input : Type} [Fintype Input]
    (p : RandProtocol k Input) : ℕ :=
  Finset.univ.sup fun c => Finset.univ.sup fun x => p.cost c x

/-- `p` solves `f` with success probability at least `δ` on every input. -/
def RandProtocol.Succeeds {k : ℕ} {Input : Type} (p : RandProtocol k Input)
    (f : Input → Bool) (δ : ℚ) : Prop :=
  ∀ x : Input, δ * (Fintype.card p.Coin : ℚ) ≤
    ((Finset.univ.filter fun c => p.answer c x = f x).card : ℚ)

/-- Inputs of the `k`-player Set-Disjointness problem (Definition 4, p. 5). -/
abbrev SetDJInput (k n : ℕ) : Type := Fin k → Fin n → Bool

/-- The `k`-player Set-Disjointness answer: some coordinate is shared by player 1 and
another player (`T_{1ℓ} = T_{jℓ} = 1`, Definition 4, p. 5). -/
def setDJAnswer {k n : ℕ} (x : SetDJInput k n) : Bool :=
  decide (∃ ℓ : Fin n, ∃ i : Fin k, i.val = 0 ∧ x i ℓ = true ∧
    ∃ j : Fin k, j.val ≠ 0 ∧ x j ℓ = true)

/-- Proposition 5 (p. 5), as a named hypothesis: when `n ≥ 3200 k`, every randomised
classical protocol for `k`-player Set-Disjointness that succeeds with probability
`1 - 1/k³` needs at least `kn / C` bits.  This is the cited external result of
[20, Theorem 3.3] and [23, Theorem 1]; it is not reproved here. -/
def SetDisjointnessHardness (C : ℝ) : Prop :=
  ∀ (k n : ℕ), 3200 * k ≤ n → ∀ p : RandProtocol k (SetDJInput k n),
    p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3) →
    (k : ℝ) * n ≤ C * (p.worstCost : ℝ)

/-- Inputs of the `k`-Gap-Hamming problem (Definition 6, p. 5): `k` players hold
`±1`-strings whose sum is again a `±1`-string; player `k+1` holds the reference string. -/
abbrev GapHammingInput (k d : ℕ) : Type := Fin (k + 1) → Fin d → Bool

/-- The `k`-Gap-Hamming answer of Definition 6 (p. 5): decide whether
`(Σ_{i<k} T_i)·T_{k+1}` is at least `c₁√d` or at most `-c₁√d`. -/
def gapHammingAnswer {k d : ℕ} (x : GapHammingInput k d) : Bool :=
  decide (0 ≤ ∑ j : Fin d, (∑ i : Fin k, (if x (Fin.castSucc i) j then (1 : ℤ) else -1))
    * (if x (Fin.last k) j then (1 : ℤ) else -1))

/-- Proposition 7 (p. 5), as a named hypothesis: any protocol solving the `k`-Gap-Hamming
problem with large constant probability needs `Ω(kd)` bits ([24, Theorem 3.3]). -/
def GapHammingHardness (C : ℝ) : Prop :=
  ∀ (k d : ℕ), 2 ≤ k → 2 ≤ d → ∀ p : RandProtocol (k + 1) (GapHammingInput k d),
    p.Succeeds gapHammingAnswer (2 / 3 : ℚ) →
    (k : ℝ) * d ≤ C * (p.worstCost : ℝ)

/-- Inputs of the Distributed Fourier Sampling problem (Definition 8, p. 5): Alice holds a
function `f : {0,1}^n → {±1}` and Bob a function `g : {0,1}^n → {±1}`. -/
abbrev DFSInput (n : ℕ) : Type := (Fin n → Bool) → Bool

/-- Proposition 9 (p. 5), as a named hypothesis: for a universal constant inaccuracy `ε`
there is `c > 0` such that any 2-way classical protocol for Distributed Fourier Sampling
must communicate at least `c·2ⁿ` bits ([25, Theorem 1]).  We record only the existence of
the constant `c`. -/
def DistributedFourierSamplingHardness (c : ℝ) : Prop :=
  0 < c ∧ ∀ (n : ℕ), 32 ≤ n → ∀ p : RandProtocol 2 (DFSInput n × DFSInput n),
    p.Succeeds (fun _ => false) (2 / 3 : ℚ) →
    c * (2 : ℝ) ^ n ≤ (p.worstCost : ℝ)

/-! ## §6. From communication lower bounds to query lower bounds -/

/-- The simulation step of Theorem 10 in the shape used by every reduction: `T` SQ
queries become a protocol whose worst-case bit cost is at most `C·(T+k)·L`, where `L`
is the bit length of a single transcript (`log(qmn)` in the paper). -/
theorem query_lower_of_protocol_bound
    {k : ℕ} {Input : Type} [Fintype Input]
    (p : RandProtocol k Input) (hard : ℝ)
    (C L : ℝ)
    (hhard : hard ≤ (p.worstCost : ℝ))
    (hcost : (p.worstCost : ℝ) ≤ C * (k : ℝ) * L) :
    hard ≤ C * (k : ℝ) * L :=
  le_trans hhard hcost

end Qatlib.Papers.QInspired25.MainResults.Model
