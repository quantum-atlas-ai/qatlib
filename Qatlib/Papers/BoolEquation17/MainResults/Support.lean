/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Boolean-system arithmetic and sparse-matrix support

Closed source lemmas from arXiv:1712.06239v3. Polynomial systems here remain bookkeeping
records: no correctness or complexity of HHL, Macaulay construction, or cryptographic
reduction follows from the records. The projection result assumes both extension maps.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEquation17.MainResults
open scoped BigOperators
open Classical

/-- The answer of a Boolean-equation-solving algorithm: `none` (a certificate of
unsatisfiability) or a Boolean assignment. -/
abbrev BoolAnswer (n : ℕ) := Option (Fin n → Bool)

/-- The smallest power of two that is at least `m`, i.e. `2 ^ clog 2 m`.
Definition 3.1 of the paper asks for `d̄` minimal with `d̄ + 1 = 2 ^ δ` and
`d̄ ≥ D - min_i d_i`; thus `d̄ + 1 = nextPow2 (D - min_i d_i + 1)`. -/
def nextPow2 (m : ℕ) : ℕ := 2 ^ Nat.clog 2 m

/-- `nextPow2` dominates its argument. -/
theorem le_nextPow2 (m : ℕ) : m ≤ nextPow2 m :=
  Nat.le_pow_clog (by norm_num) m

/-- `nextPow2 m` is a power of two. -/
theorem nextPow2_isPow (m : ℕ) : ∃ k, nextPow2 m = 2 ^ k := ⟨_, rfl⟩

/-- Minimality of `nextPow2` among powers of two dominating `m`. -/
theorem nextPow2_min {m e : ℕ} (he : ∃ k, e = 2 ^ k) (hm : m ≤ e) :
    nextPow2 m ≤ e := by
  obtain ⟨k, rfl⟩ := he
  have hle : Nat.clog 2 m ≤ k := Nat.clog_le_of_le_pow (b := 2) (x := m) (y := k) hm
  exact Nat.pow_le_pow_right (n := 2) (by norm_num) hle

/-- For `m ≥ 1`, `nextPow2 m ≤ 2 * m - 1`.  This is the arithmetic core of Lemma 3.7:
minimality of `nextPow2` forces `nextPow2 m / 2 < m`. -/
theorem nextPow2_le_two_mul_sub_one (m : ℕ) (hm : 1 ≤ m) :
    nextPow2 m ≤ 2 * m - 1 := by
  rcases eq_or_lt_of_le hm with h1 | h2
  · subst h1
    simp [nextPow2]
  · have hlt : 2 ^ (Nat.clog 2 m).pred < m :=
      Nat.pow_pred_clog_lt_self (by norm_num) h2
    have hpred : (Nat.clog 2 m).pred = Nat.clog 2 m - 1 := Nat.pred_eq_sub_one
    rw [hpred] at hlt
    have hpos : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h2
    have hk' : Nat.clog 2 m = (Nat.clog 2 m - 1) + 1 := by omega
    have hval : nextPow2 m = 2 * 2 ^ (Nat.clog 2 m - 1) := by
      unfold nextPow2
      nth_rewrite 1 [hk']
      rw [Nat.pow_succ]
      ring
    rw [hval]
    have hb : 2 ^ (Nat.clog 2 m - 1) ≤ m - 1 := by omega
    omega

/-- `d̄` of Definition 3.1. -/
def dbarOf (D minDi : ℕ) : ℕ := nextPow2 (D - minDi + 1) - 1

/-- `D̄` of Definition 3.1. -/
def DbarOf (D : ℕ) : ℕ := nextPow2 (D + 1) - 1

/-- `d̄ + 1` is the least power of two dominating `D - min_i d_i + 1`. -/
theorem dbarOf_add_one (D minDi : ℕ) : dbarOf D minDi + 1 = nextPow2 (D - minDi + 1) := by
  unfold dbarOf
  have := le_nextPow2 (D - minDi + 1)
  omega

/-- `D̄ + 1` is the least power of two dominating `D + 1`. -/
theorem DbarOf_add_one (D : ℕ) : DbarOf D + 1 = nextPow2 (D + 1) := by
  unfold DbarOf
  have := le_nextPow2 (D + 1)
  omega

/-- `C`-valued Boolean representation of an assignment (`true ↦ 1`, `false ↦ 0`). -/
def toComplex {n : ℕ} (a : Fin n → Bool) : Fin n → ℂ := fun i => if a i then 1 else 0

/-- A point of `ℂ^n` all of whose coordinates are `0` or `1`. -/
def IsBooleanPoint {n : ℕ} (a : Fin n → ℂ) : Prop := ∀ i, a i = 0 ∨ a i = 1

/-- A polynomial system `F = {f_1, …, f_r} ⊂ ℂ[X]` with the data used by the paper:
degrees, sparseness, complex/Boolean zero sets, condition number, and the solving-degree
invariants of Section 3. -/
structure PolySystem (n : ℕ) where
  /-- Number `r` of polynomials. -/
  numPolys : ℕ
  /-- Degree `d_i` of the `i`-th polynomial. -/
  deg : Fin numPolys → ℕ
  /-- Maximal degree `D = max_i d_i`. -/
  maxDeg : ℕ
  /-- Sparseness `#f_i`. -/
  sparseness : Fin numPolys → ℕ
  /-- Complex zero set `V_ℂ(F)`. -/
  zerosC : Set (Fin n → ℂ)
  /-- Boolean zero set `V_B(F)`. -/
  zerosB : Set (Fin n → Bool)
  /-- Condition number `κ` of the associated Macaulay matrix. -/
  cond : ℝ
  cond_pos : 0 < cond
  /-- Solving degree (degree of regularity) of the system. -/
  sdeg : ℕ
  /-- Complete solving degree `CSdeg` of Definition 3.14. -/
  csdeg : ℕ
  /-- The system is zero-dimensional. -/
  isZeroDim : Prop
  /-- The generating ideal is radical. -/
  isRadical : Prop
  /-- The system is in the normal form (9) of Section 4. -/
  inForm9 : Prop

namespace PolySystem

/-- Total sparseness `T_F = ∑_i #f_i`. -/
def totalSparseness {n : ℕ} (S : PolySystem n) : ℕ := ∑ i, S.sparseness i

/-- Sum of the degrees `∑_i d_i`. -/
def degSum {n : ℕ} (S : PolySystem n) : ℕ := ∑ i, S.deg i

/-- Correctness of an algorithm output. -/
def CorrectAnswer {n : ℕ} (S : PolySystem n) : BoolAnswer n → Prop
  | none => S.zerosB = ∅
  | some a => a ∈ S.zerosB

end PolySystem

/-- A Boolean polynomial system `F ⊂ R₂[X]` in `n` variables. -/
structure BoolSystem (n : ℕ) where
  numPolys : ℕ
  sparseness : Fin numPolys → ℕ
  deg : Fin numPolys → ℕ
  zeros : Set (Fin n → Bool)
  cond : ℝ
  cond_pos : 0 < cond

namespace BoolSystem

/-- Total sparseness `T_F = ∑_i #f_i`. -/
def totalSparseness {n : ℕ} (S : BoolSystem n) : ℕ := ∑ i, S.sparseness i

/-- Correctness of an algorithm output for a Boolean system. -/
def CorrectAnswer {n : ℕ} (S : BoolSystem n) : BoolAnswer n → Prop
  | none => S.zeros = ∅
  | some a => a ∈ S.zeros

end BoolSystem

/-- `F` is `s`-sparse as a Boolean system. -/
def IsSSparseSystem {n : ℕ} (F : BoolSystem n) (s : ℕ) : Prop :=
  ∀ i, F.sparseness i ≤ s

/-- A randomized algorithm solving systems of type `Sys`: output is a probability mass
function on `none`/Boolean assignments, plus a gate-complexity account. -/
structure SolverAlgorithm (Sys : Type) (n : ℕ) where
  run : Sys → ℝ → PMF (BoolAnswer n)
  gateCost : Sys → ℝ → ℝ

/-- Probability that the algorithm's output satisfies the correctness predicate. -/
def SolverAlgorithm.successProb {Sys : Type} {n : ℕ} (A : SolverAlgorithm Sys n)
    (S : Sys) (ε : ℝ) (correct : BoolAnswer n → Prop) : ℝ :=
  (∑' o : BoolAnswer n, if correct o then A.run S ε o else 0).toReal

/-- An algorithm returning a *set* of Boolean assignments. -/
structure MultiSolverAlgorithm (Sys : Type) (n : ℕ) where
  run : Sys → ℝ → PMF (Finset (Fin n → Bool))
  gateCost : Sys → ℝ → ℝ

/-- Probability that the returned set satisfies a correctness predicate. -/
def MultiSolverAlgorithm.successProb {Sys : Type} {n : ℕ} (A : MultiSolverAlgorithm Sys n)
    (S : Sys) (ε : ℝ) (correct : Finset (Fin n → Bool) → Prop) : ℝ :=
  (∑' o : Finset (Fin n → Bool), if correct o then A.run S ε o else 0).toReal

/-! ### Complex vectors, norms, linear systems -/

abbrev CVec (N : ℕ) := Fin N → ℂ

/-- Euclidean norm. -/
def l2Norm {N : ℕ} (x : CVec N) : ℝ := Real.sqrt (∑ i, Complex.normSq (x i))

/-- `x` minimises the Euclidean residual of `A x = b`. -/
def IsLeastSquaresSolution {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (b : CVec M)
    (x : CVec N) : Prop :=
  ∀ y : CVec N, l2Norm (A.mulVec x - b) ≤ l2Norm (A.mulVec y - b)

/-- `x` is within `ε` of some least-squares solution of `A x = b` (the paper's notion of an
`ε`-approximation to the solution state). -/
def ApproximatesSolution {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (b : CVec M)
    (x : CVec N) (ε : ℝ) : Prop :=
  ∃ xs : CVec N, IsLeastSquaresSolution A b xs ∧ l2Norm (x - xs) ≤ ε

/-- At most `s` nonzeros per row. -/
def RowSparseBound {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (s : ℕ) : Prop :=
  ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ s

/-- At most `s` nonzeros per column. -/
def ColSparseBound {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (s : ℕ) : Prop :=
  ∀ j, (Finset.univ.filter (fun i => A i j ≠ 0)).card ≤ s

/-- `s`-sparse in both directions. -/
def IsSSparse {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (s : ℕ) : Prop :=
  RowSparseBound A s ∧ ColSparseBound A s

/-- 1-sparse. -/
def IsOneSparse {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) : Prop := IsSSparse A 1

/-- Condition number `‖A‖ · ‖A†‖`, computed as the product of the suprema of the two
operator norms. -/
def conditionNumber {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) : ℝ :=
  sSup { r : ℝ | ∃ x : CVec N, x ≠ 0 ∧ r = l2Norm (A.mulVec x) / l2Norm x } *
    sSup { r : ℝ | ∃ y : CVec M, y ≠ 0 ∧ r = l2Norm (A.conjTranspose.mulVec y) / l2Norm y }

/-- Costed sparse access to a matrix (`O(s)` per query, normalised so the query cost is at
most `s`; this is the paper's Assumption 1 at unit slope). -/
structure SparseAccess (M N : ℕ) where
  A : Matrix (Fin M) (Fin N) ℂ
  s : ℕ
  queryCost : ℝ
  sparse : IsSSparse A s
  query_bound : queryCost ≤ (s : ℝ)

/-- Assumption 1 of Section 2. -/
structure Assumption1 (M N : ℕ) where
  A : Matrix (Fin M) (Fin N) ℂ
  s : ℕ
  gamma : ℝ
  parts : Fin s → Matrix (Fin M) (Fin N) ℂ
  decompose : A = ∑ j, parts j
  part_sparse : ∀ j, IsOneSparse (parts j)
  partQueryCost : Fin s → ℝ
  part_query_bound : ∀ j, partQueryCost j ≤ gamma

/-- Assumption 2 of Section 2. -/
structure Assumption2 (M : ℕ) where
  b : CVec M
  v : ℕ
  r : ℕ
  rho : ℕ
  hM : M = r * 2 ^ v
  hrho : rho ≤ r
  entries : ∀ i, b i = 0 ∨ b i = 1
  pattern : ∀ i : Fin M, b i = 1 ↔ ∃ k : ℕ, k < rho ∧ (i : ℕ) = k * 2 ^ v

/-- A quantum linear-system algorithm. -/
structure LinearSystemAlgorithm where
  output : (M N : ℕ) → Matrix (Fin M) (Fin N) ℂ → CVec M → ℝ → CVec N
  gateCost : (M N : ℕ) → Matrix (Fin M) (Fin N) ℂ → CVec M → ℝ → ℝ

/-! ### Macaulay systems and their index data -/

/-- The modified Macaulay matrix `𝓜_{F,D}` of Definition 3.1.  The index parameters
`δ, ∆` come with their defining equations `d̄ + 1 = 2^δ`, `D̄ + 1 = 2^∆`, and `ρ ≤ r - 1`. -/
structure MacaulaySystem (n : ℕ) where
  r : ℕ
  D : ℕ
  minDi : ℕ
  delta : ℕ
  Delta : ℕ
  matrix : Matrix (Fin (r * (dbarOf D minDi + 1) ^ n))
    (Fin ((DbarOf D + 1) ^ n - 1)) ℂ
  rhs : Fin (r * (dbarOf D minDi + 1) ^ n) → ℂ
  rho : ℕ
  cond : ℝ
  cond_pos : 0 < cond
  hdelta : dbarOf D minDi + 1 = 2 ^ delta
  hDelta : DbarOf D + 1 = 2 ^ Delta
  hrho : rho ≤ r - 1

namespace MacaulaySystem

/-- Number of rows `N = r (d̄+1)^n = r 2^{δn}` (called `N` in Corollary 3.22). -/
def nRows {n : ℕ} (M : MacaulaySystem n) : ℕ := M.r * (dbarOf M.D M.minDi + 1) ^ n

/-- Number of columns `M = (D̄+1)^n - 1 = 2^{∆n} - 1` (called `M` in Corollary 3.22). -/
def nCols {n : ℕ} (M : MacaulaySystem n) : ℕ := (DbarOf M.D + 1) ^ n - 1

end MacaulaySystem

/-- The `i`-th base-`B` digit of `k` (exponent tuple of the monomial `x^k`). -/
def digitOf (B k i : ℕ) : ℕ := (k / B ^ i) % B

/-- Evaluation at `a` of the monomial with base-`B` index `k`. -/
def monomialEval {n : ℕ} (B : ℕ) (a : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∏ i : Fin n, a i ^ digitOf B k (i : ℕ)

/-- Total degree of the monomial with base-`B` index `k`. -/
def digitSum (n B k : ℕ) : ℕ := ∑ i : Fin n, digitOf B k (i : ℕ)

/-- The truncated monomial vector `m̃_D(a)`: entries of total degree `> D` are set to `0`. -/
def truncatedMonomialVec {n : ℕ} (M : MacaulaySystem n) (a : Fin n → ℂ) :
    Fin M.nCols → ℂ :=
  fun k => if digitSum n (DbarOf M.D + 1) (k : ℕ) ≤ M.D
    then monomialEval (DbarOf M.D + 1) a (k : ℕ) else 0

/-- The set of normalised (convex) combinations of truncated monomial vectors. -/
def PseudoSolutionSet {n : ℕ} (M : MacaulaySystem n) (w : ℕ)
    (sols : Fin w → Fin n → ℂ) : Set (Fin M.nCols → ℂ) :=
  { v | ∃ η : Fin w → ℂ, (∑ i, η i = 1) ∧ v = ∑ i, η i • truncatedMonomialVec M (sols i) }

/-- `mvec` solves the Macaulay linear system `𝓜 m = b`. -/
def IsMacaulaySolution {n : ℕ} (M : MacaulaySystem n) (mvec : Fin M.nCols → ℂ) : Prop :=
  M.matrix.mulVec mvec = M.rhs

/-- Solution form (13) of Lemma 3.18: a normalised combination of the truncated monomial
vectors of the solutions, plus an arbitrary vector supported in total degree `> D`. -/
def MacaulaySolutionForm {n : ℕ} (M : MacaulaySystem n) (w : ℕ)
    (sols : Fin w → Fin n → ℂ) (mvec : Fin M.nCols → ℂ) : Prop :=
  ∃ (η : Fin w → ℂ) (μ : Fin M.nCols → ℂ),
    (∑ i, η i = 1) ∧
    mvec = (fun k : Fin M.nCols => ∑ i, η i * truncatedMonomialVec M (sols i) k) +
      (fun k : Fin M.nCols =>
        if M.D < digitSum n (DbarOf M.D + 1) (k : ℕ) then μ k else 0)

/-- The unique-solution form of Corollary 3.19: `|m̃_D(a)⟩` plus a high-degree vector. -/
def MacaulaySolutionFormUnique {n : ℕ} (M : MacaulaySystem n) (a : Fin n → ℂ)
    (mvec : Fin M.nCols → ℂ) : Prop :=
  ∃ μ : Fin M.nCols → ℂ,
    mvec = truncatedMonomialVec M a +
      (fun k : Fin M.nCols =>
        if M.D < digitSum n (DbarOf M.D + 1) (k : ℕ) then μ k else 0)

/-! ### Cost predicates, logarithms, splitting data -/

/-- `cost` is `O(g)`. -/
def IsBigO (cost g : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ cost ≤ C * g

/-- `cost` is `Õ(g)` with the suppressed logarithm made explicit. -/
def IsTildeO (cost g size : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ cost ≤ C * g * Real.log (size + 2)

/-- Base-2 logarithm. -/
def logb2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- `⌈a / b⌉` for natural numbers. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b


/-- **Lemma 3.7** (arXiv:1712.06239v3, Lemma 3.7, p. 13).
With `d̄ + 1 = 2^δ` and `D̄ + 1 = 2^∆` the minimal powers of two, one has
`d̄ + 1 ≤ 2D`, `D̄ + 1 ≤ 2D + 1`, hence `N = r(d̄+1)^n ≤ r(2D)^n` and
`M = (D̄+1)^n - 1 ≤ (2D+1)^n - 1`. -/
theorem lemma_3_7 {n : ℕ} (M : MacaulaySystem n) (hminDi : 1 ≤ M.minDi)
    (hDdi : M.minDi ≤ M.D) :
    dbarOf M.D M.minDi + 1 ≤ 2 * M.D ∧
    DbarOf M.D + 1 ≤ 2 * M.D + 1 ∧
    M.r * (dbarOf M.D M.minDi + 1) ^ n ≤ M.r * (2 * M.D) ^ n ∧
    ((DbarOf M.D + 1) ^ n - 1) ≤ (2 * M.D + 1) ^ n - 1 := by
  have hdbar : dbarOf M.D M.minDi + 1 ≤ 2 * M.D := by
    rw [dbarOf_add_one]
    have h1 : nextPow2 (M.D - M.minDi + 1) ≤ 2 * (M.D - M.minDi + 1) - 1 :=
      nextPow2_le_two_mul_sub_one _ (by omega)
    omega
  have hDbar : DbarOf M.D + 1 ≤ 2 * M.D + 1 := by
    rw [DbarOf_add_one]
    have h1 : nextPow2 (M.D + 1) ≤ 2 * (M.D + 1) - 1 :=
      nextPow2_le_two_mul_sub_one _ (by omega)
    omega
  refine ⟨hdbar, hDbar, ?_, ?_⟩
  · exact Nat.mul_le_mul_left M.r (Nat.pow_le_pow_left hdbar n)
  · exact Nat.sub_le_sub_right (Nat.pow_le_pow_left hDbar n) 1

/-- **Corollary 3.9** (arXiv:1712.06239v3, Corollary 3.9, p. 14).
A sum of `s` 1-sparse matrices is `s`-sparse; in particular the Macaulay matrix has
sparseness `T_F`. -/
theorem corollary_3_9 {M N : ℕ} {ι : Type} [Fintype ι]
    (A : Matrix (Fin M) (Fin N) ℂ) (parts : ι → Matrix (Fin M) (Fin N) ℂ)
    (hsum : A = ∑ k, parts k) (hsp : ∀ k, IsOneSparse (parts k)) :
    IsSSparse A (Fintype.card ι) := by
  have hA : ∀ i j, A i j = ∑ k, parts k i j := by
    intro i j
    rw [hsum]
    simp [Matrix.sum_apply]
  constructor
  · intro i
    have hsub : (Finset.univ.filter (fun j => A i j ≠ 0)) ⊆
        Finset.univ.biUnion (fun k => Finset.univ.filter (fun j => parts k i j ≠ 0)) := by
      intro j hj
      have hj' : A i j ≠ 0 := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hne : ∑ k, parts k i j ≠ 0 := by rw [← hA i j]; exact hj'
      obtain ⟨k, hk⟩ : ∃ k, parts k i j ≠ 0 := by
        by_contra h
        apply hne
        push Not at h
        exact Finset.sum_eq_zero (fun k _ => h k)
      exact Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_univ k, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk⟩
    calc (Finset.univ.filter (fun j => A i j ≠ 0)).card
        ≤ (Finset.univ.biUnion
            (fun k => Finset.univ.filter (fun j => parts k i j ≠ 0))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ k, (Finset.univ.filter (fun j => parts k i j ≠ 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _k : ι, 1 := by
          apply Finset.sum_le_sum
          intro k _
          exact (hsp k).1 i
      _ = Fintype.card ι := by simp
  · intro j
    have hsub : (Finset.univ.filter (fun i => A i j ≠ 0)) ⊆
        Finset.univ.biUnion (fun k => Finset.univ.filter (fun i => parts k i j ≠ 0)) := by
      intro i hi
      have hi' : A i j ≠ 0 := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      have hne : ∑ k, parts k i j ≠ 0 := by rw [← hA i j]; exact hi'
      obtain ⟨k, hk⟩ : ∃ k, parts k i j ≠ 0 := by
        by_contra h
        apply hne
        push Not at h
        exact Finset.sum_eq_zero (fun k _ => h k)
      exact Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_univ k, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hk⟩
    calc (Finset.univ.filter (fun i => A i j ≠ 0)).card
        ≤ (Finset.univ.biUnion
            (fun k => Finset.univ.filter (fun i => parts k i j ≠ 0))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ k, (Finset.univ.filter (fun i => parts k i j ≠ 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _k : ι, 1 := by
          apply Finset.sum_le_sum
          intro k _
          exact (hsp k).2 j
      _ = Fintype.card ι := by simp

/-- **Lemma 4.4** (arXiv:1712.06239v3, Lemma 4.4, p. 18).
If a nonzero monomial of a Boolean solution `a ∈ V_ℂ(F₂)` has been measured, then every
variable appearing in it evaluates to `1` at `a`; hence with probability `> 1 - ε₁/n`
the measurement yields such a coordinate.  (The probability estimate is recorded in the
statement of the surrounding algorithm; the algebraic content proved here is the
deterministic implication.) -/
theorem lemma_4_4 {n : ℕ} (F2 : PolySystem n) (u : ℕ) (idx : Fin u → Fin n)
    (a : Fin n → ℂ) (_ha : a ∈ F2.zerosC) (hbool : IsBooleanPoint a)
    (hmono : (∏ i : Fin u, a (idx i)) ≠ 0) :
    ∀ i, a (idx i) = 1 := by
  intro i
  have hne : a (idx i) ≠ 0 :=
    (Finset.prod_ne_zero_iff).1 hmono i (Finset.mem_univ i)
  rcases hbool (idx i) with h | h
  · exact absurd h hne
  · exact h

/-- **Lemma 4.5** (arXiv:1712.06239v3, Lemma 4.5, p. 18).
The inner loop runs at most `n` times and returns `∅` with probability
`< 1 - (1 - ε₁/n)^n < ε₁`; the arithmetic core is `1 - (1 - ε₁/n)^n ≤ ε₁`. -/
theorem lemma_4_5 (n : ℕ) (ε1 : ℝ) (hn : 0 < n) (_hε1 : 0 ≤ ε1) (hε1n : ε1 ≤ (n : ℝ)) :
    (1 - ε1 / (n : ℝ)) ^ n ≥ 1 - ε1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hle : ε1 / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hnR]
    nlinarith
  have h2 : (-2 : ℝ) ≤ -(ε1 / (n : ℝ)) := by linarith
  have h := one_add_mul_le_pow (a := -(ε1 / (n : ℝ))) h2 n
  have hcalc : (n : ℝ) * (-(ε1 / (n : ℝ))) = -ε1 := by
    field_simp
  have hbase : (1 : ℝ) + -(ε1 / (n : ℝ)) = 1 - ε1 / n := by ring
  rw [hcalc, hbase] at h
  linarith

/-- Agreement of the zero sets of `F` and of `S(F,s)` under projection along the new
variables (the Boolean-ring counterpart of the ideal equality of Lemma 5.4). -/
def BoolIdealAgreement {n extra : ℕ} (F : BoolSystem n) (SF : BoolSystem (n + extra)) : Prop :=
  ∀ x : Fin n → Bool, x ∈ F.zeros ↔ ∃ y ∈ SF.zeros, ∀ i, y (Fin.castAdd extra i) = x i

/-- **Lemma 5.4** (arXiv:1712.06239v3, Lemma 5.4, p. 22).
For the splitting system `S(F,s)`, the restrictions of the ideals agree:
`(S(F,s)) ∩ R₂[X] = (F)`, equivalently `V_{F₂}(F) = Proj_X V_{F₂}(S(F,s))`. -/
theorem lemma_5_4 (n _s : ℕ) (F : BoolSystem n) (extra : ℕ) (SF : BoolSystem (n + extra))
    (hfwd : ∀ y ∈ SF.zeros, (fun i : Fin n => y (Fin.castAdd extra i)) ∈ F.zeros)
    (hbwd : ∀ x ∈ F.zeros, ∃ y ∈ SF.zeros, ∀ i, y (Fin.castAdd extra i) = x i) :
    BoolIdealAgreement F SF := by
  intro x
  constructor
  · intro hx
    exact hbwd x hx
  · rintro ⟨y, hy, hxy⟩
    have hx : x = fun i : Fin n => y (Fin.castAdd extra i) := (funext hxy).symm
    rw [hx]
    exact hfwd y hy

/-- Rounding the logarithmic number of independent rounds bounds the failure probability. -/
theorem lemma_4_6 (ε ε1 : ℝ) (hε : 0 < ε) (_hε1 : 0 < ε1) (hε1' : ε1 < 1) :
    ε1 ^ (Nat.ceil (Real.log ε / Real.log ε1)) ≤ ε := by
  apply (Real.log_le_log_iff (pow_pos _hε1 _) hε).mp
  rw [Real.log_pow]
  have hlog : Real.log ε1 < 0 := Real.log_neg _hε1 hε1'
  have hceil : Real.log ε / Real.log ε1 ≤ (Nat.ceil (Real.log ε / Real.log ε1) : ℝ) :=
    Nat.le_ceil _
  have hmul := mul_le_mul_of_nonpos_right hceil hlog.le
  rw [div_mul_cancel₀ _ (ne_of_lt hlog)] at hmul
  exact hmul

end Qatlib.Papers.BoolEquation17.MainResults
