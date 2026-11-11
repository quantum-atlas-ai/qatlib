/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Core objects of the Carleman embedding paper

Jennings--Korzekwa--Lostaglio--Sornborger--Subasi--Wang,
*Quantum algorithms for general nonlinear dynamics based on the Carleman embedding*,
fixed arXiv:2509.07155v2 (Quantum, accepted 2026-09-29).

This module fixes the paper's vocabulary once, faithfully to the printed objects:

* the quadratic ODE `ẋ = F0 + F1 x + F2 x^{⊗2}` (Eq. (1.1), (3.14), (4.4));
* the `j`-fold tensor power `x^{⊗j}` and the Carleman blocks
  `A_{j,j-1}, A_{j,j}, A_{j,j+1}` of Eqs. (2.7a)–(2.7c), built as the
  Kronecker sums `F0 ⊗ I^{⊗(j-1)} + shifts` etc.;
* the truncated Carleman system of Eq. (2.10)/(2.13) and the error vectors
  `η_j = x^{⊗j} - y^{[j]}` of Eq. (2.15);
* the rescaling `F̄0 = γF0`, `F̄1 = F1`, `F̄2 = F2/γ`, `x̄ = γx` of Eq. (2.3);
* the `P`-inner product, `P`-norm, generalized log-norm `μ_P` and generalized
  R-number `R_P` of Eqs. (3.2)–(3.6);
* the real spectral gap `δ(F1)` of Eq. (4.9), nonresonance, `Δ`-nonresonance and
  the Siegel "type `(Δ,ν)`" gap of Assumption I.2;
* column sparsity `cs(·)`, the entrywise maximum norm, the binary-tree counts of
  Appendix H and the weighted fusion sums `S_k^j` of Eq. (C.16);
* a lightweight interface for block-encodings and oracle decision problems, used
  only to state the algorithmic and complexity claims of Sections 6–7.

Everything is stated over `ℂ` (the paper works over `ℂ` in Sections 5–7 and over
`ℝ` in Sections 3–4; `ℝ` embeds into the same formulas).  Vectors of Carleman
level `j` are indexed by `Fin j → Fin n`, which is canonically isomorphic to
`Fin (n^j)`; this avoids transport boilerplate while keeping the objects exact.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.CarlemanSim26.MainResults

/-! ## Vectors, matrices and tensor powers -/

/-- A complex vector of dimension `n`. -/
abbrev CVec (n : ℕ) : Type := Fin n → ℂ

/-- A complex matrix of shape `m × n`. -/
abbrev CMat (m n : ℕ) : Type := Matrix (Fin m) (Fin n) ℂ

/-- The paper's `F2` is an `N × N²` matrix (Eq. (2.7c)); we index its columns by
the pair `(j, l)` of tensor factors. -/
abbrev F2Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n × Fin n) ℂ

/-- The `j`-fold tensor power `x^{⊗j}` of a vector, indexed by the `j` tensor
factors (source Eq. (2.4)–(2.6)). -/
def tensorPow {n : ℕ} (j : ℕ) (x : CVec n) : (Fin j → Fin n) → ℂ :=
  fun idx => ∏ l : Fin j, x (idx l)

/-- The second tensor power `x^{⊗2}`, indexed by an explicit pair. -/
def tensorPow2 {n : ℕ} (x : CVec n) : Fin n × Fin n → ℂ :=
  fun p => x p.1 * x p.2

/-- The quadratic right-hand side `F0 + F1 x + F2 x^{⊗2}` (Eq. (1.1)). -/
def quadraticField {n : ℕ} (F0 : CVec n) (F1 : CMat n n) (F2 : F2Mat n) (x : CVec n) :
    CVec n :=
  F0 + F1.mulVec x + F2.mulVec (tensorPow2 x)

/-- `x : ℝ → ℂ^N` solves the quadratic ODE `ẋ = F0 + F1 x + F2 x^{⊗2}` globally. -/
def IsQuadraticSolution {n : ℕ} (F0 : CVec n) (F1 : CMat n n) (F2 : F2Mat n)
    (x : ℝ → CVec n) : Prop :=
  ∀ t : ℝ, HasDerivAt x (quadraticField F0 F1 F2 (x t)) t

/-! ## Carleman blocks (Eqs. (2.7a)–(2.7c)) -/

/-- The diagonal Carleman block `A_{j,j} = F1 ⊗ I^{⊗(j-1)} + shifts` of Eq. (2.7b). -/
def carlemanDiag {n : ℕ} (F1 : CMat n n) (j : ℕ) :
    Matrix (Fin j → Fin n) (Fin j → Fin n) ℂ :=
  fun a b =>
    ∑ l : Fin j,
      F1 (a l) (b l) *
        ∏ k : {k : Fin j // k ≠ l}, (if a k.1 = b k.1 then (1 : ℂ) else 0)

/-- Position in `Fin j` obtained from a position `k` of the *contracted* level
`j - 1` by skipping the factor `l` (used by `carlemanDown`). -/
def skipPos {j : ℕ} (l : Fin j) (k : Fin (j - 1)) : Fin j :=
  ⟨if (k : ℕ) < (l : ℕ) then (k : ℕ) else (k : ℕ) + 1, by
    have hk : (k : ℕ) < j - 1 := k.2
    have hl : (l : ℕ) < j := l.2
    have hj : 0 < j := Nat.lt_of_le_of_lt (Nat.zero_le _) hl
    split
    · exact Nat.lt_trans (by assumption) hl
    · exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk) (Nat.sub_lt hj Nat.zero_lt_one)⟩

/-- The upper Carleman block `A_{j,j+1} = F2 ⊗ I^{⊗(j-1)} + shifts` of Eq. (2.7c):
it maps level `j` to level `j+1` by applying `F2` on two adjacent factors. -/
def carlemanUp {n : ℕ} (F2 : F2Mat n) (j : ℕ) :
    Matrix (Fin j → Fin n) (Fin (j + 1) → Fin n) ℂ :=
  fun a b =>
    ∑ l : Fin j,
      F2 (a l) (b (Fin.castSucc l), b (Fin.succ l)) *
        ∏ k : {k : Fin j // k ≠ l},
          (if a k.1 = b (Fin.succAbove (Fin.castSucc l) k.1) then (1 : ℂ) else 0)

/-- The lower Carleman block `A_{j,j-1} = F0 ⊗ I^{⊗(j-1)} + shifts` of Eq. (2.7a):
it maps level `j-1` into level `j` by placing `F0` in one factor.  The index `j`
below is the *target* level. -/
def carlemanDown {n : ℕ} (F0 : CVec n) (j : ℕ) :
    Matrix (Fin j → Fin n) (Fin (j - 1) → Fin n) ℂ :=
  fun a b =>
    ∑ l : Fin j,
      F0 (a l) * ∏ k : Fin (j - 1), (if a (skipPos l k) = b k then (1 : ℂ) else 0)

/-- The right-hand side of the `ℓ`-th block of the truncated Carleman system
(Eq. (2.10)): `A_{ℓ,ℓ-1} z^{[ℓ-1]} + A_{ℓ,ℓ} z^{[ℓ]} + A_{ℓ,ℓ+1} z^{[ℓ+1]}`, with
`A_{k,k+1}` set to zero at truncation level `k`. -/
def carlemanRhs {n : ℕ} (F0 : CVec n) (F1 : CMat n n) (F2 : F2Mat n) (k : ℕ)
    (z : (ℓ : ℕ) → ℝ → (Fin ℓ → Fin n) → ℂ) (ℓ : ℕ) (t : ℝ) : (Fin ℓ → Fin n) → ℂ :=
  (carlemanDiag F1 ℓ).mulVec (z ℓ t) +
    (carlemanDown F0 ℓ).mulVec (z (ℓ - 1) t) +
    (if ℓ < k then (carlemanUp F2 ℓ).mulVec (z (ℓ + 1) t) else 0)

/-- `z` is the level-`j` block `y^{[j]}` of the truncated Carleman solution of
Eq. (2.10)/(2.13), stored level by level (`z ℓ` has tensor order `ℓ`). -/
def IsTruncatedCarlemanSolution {n : ℕ} (F0 : CVec n) (F1 : CMat n n) (F2 : F2Mat n)
    (k : ℕ) (x : ℝ → CVec n) (z : (ℓ : ℕ) → ℝ → (Fin ℓ → Fin n) → ℂ) : Prop :=
  (z 0 = fun _ _ => 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k → z ℓ 0 = tensorPow ℓ (x 0)) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => z ℓ s) (carlemanRhs F0 F1 F2 k z ℓ t) t)

/-- The Carleman error vector `η_j(t) = x(t)^{⊗j} - y^{[j]}(t)` of Eq. (2.15). -/
def eta {n : ℕ} (z : (ℓ : ℕ) → ℝ → (Fin ℓ → Fin n) → ℂ) (x : ℝ → CVec n)
    (j : ℕ) (t : ℝ) : (Fin j → Fin n) → ℂ :=
  tensorPow j (x t) - z j t

/-- The norm `‖η_j(t)‖` of Eq. (2.15). -/
def etaNorm {n : ℕ} (z : (ℓ : ℕ) → ℝ → (Fin ℓ → Fin n) → ℂ) (x : ℝ → CVec n)
    (j : ℕ) (t : ℝ) : ℝ :=
  ‖eta z x j t‖

/-! ## Rescaling (Eq. (2.3)) -/

/-- Rescaled `F0`: `F̄0 = γF0`. -/
def rescaleF0 {n : ℕ} (γ : ℝ) (F0 : CVec n) : CVec n := (γ : ℂ) • F0

/-- Rescaled `F2`: `F̄2 = γ⁻¹F2`. -/
def rescaleF2 {n : ℕ} (γ : ℝ) (F2 : F2Mat n) : F2Mat n :=
  fun i p => (γ : ℂ)⁻¹ * F2 i p

/-! ## `P`-norm, generalized log-norm and R-number (Eqs. (3.2)–(3.6)) -/

/-- The `P`-inner product `⟨x,y⟩_P = x† P y` of Eq. (3.3). -/
def pInner {n : ℕ} (P : CMat n n) (x y : CVec n) : ℂ :=
  ∑ i : Fin n, star (x i) * (P.mulVec y) i

/-- The `P`-norm `‖x‖_P = √(x† P x)` of Section 3.1. -/
def pNorm {n : ℕ} (P : CMat n n) (x : CVec n) : ℝ :=
  Real.sqrt (pInner P x x).re

/-- The `P`-inner product on a matrix with `Fintype` index set, used for tensor
levels. -/
def pInnerT {α : Type} [Fintype α] (M : Matrix α α ℂ) (x y : α → ℂ) : ℂ :=
  ∑ i : α, star (x i) * (M.mulVec y) i

/-- The corresponding `P`-norm on a tensor level. -/
def pNormT {α : Type} [Fintype α] (M : Matrix α α ℂ) (x : α → ℂ) : ℝ :=
  Real.sqrt (pInnerT M x x).re

/-- The Kronecker square `P ⊗ P` used for the two-factor `P`-norm. -/
def kronP2 {n : ℕ} (P : CMat n n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun a b => P a.1 b.1 * P a.2 b.2

/-- `P > 0` as a positive-definite quadratic form (the paper's `P > 0`). -/
def IsPositiveDefinite {n : ℕ} (P : CMat n n) : Prop :=
  ∀ x : CVec n, x ≠ 0 → 0 < (pInner P x x).re ∧ (pInner P x x).im = 0

/-- The Lyapunov inequality `P F1 + F1† P < 0` of Eq. (3.13), expressed through
the `P`-inner product. -/
def IsLyapunovPair {n : ℕ} (P F1 : CMat n n) : Prop :=
  IsPositiveDefinite P ∧ ∀ x : CVec n, x ≠ 0 → (pInner P (F1.mulVec x) x).re < 0

/-- The generalized log-norm `μ_P(F1)` of Eq. (3.2). -/
def generalizedLogNorm {n : ℕ} (P F1 : CMat n n) : ℝ :=
  sSup {r : ℝ | ∃ x : CVec n, x ≠ 0 ∧ r = (pInner P (F1.mulVec x) x).re / (pInner P x x).re}

/-- The operator `P`-norm `‖F0‖_P` (Eq. (3.6)). -/
def f0PNorm {n : ℕ} (P : CMat n n) (F0 : CVec n) : ℝ := pNorm P F0

/-- The operator `P`-norm `‖F2‖_P = ‖P^{1/2} F2 (P^{-1/2} ⊗ P^{-1/2})‖` of
Eq. (3.6), realized as the supremum of the `P`-norm ratio on two-factor tensors. -/
def f2PNorm {n : ℕ} (P : CMat n n) (F2 : F2Mat n) : ℝ :=
  sSup {r : ℝ |
    ∃ v : Fin n × Fin n → ℂ, v ≠ 0 ∧
      r = pNormT P (F2.mulVec v) / pNormT (kronP2 P) v}

/-- The generalized R-number `R_P` of Eq. (3.5). -/
def reNumber {n : ℕ} (P : CMat n n) (F0 : CVec n) (F1 : CMat n n) (F2 : F2Mat n)
    (x0 : CVec n) : ℝ :=
  (1 / (-generalizedLogNorm P F1)) *
    (f2PNorm P F2 * pNorm P x0 + f0PNorm P F0 / pNorm P x0)

/-! ## Spectrum, spectral abscissa, real spectral gap -/

/-- The spectral abscissa `α(F1) = max Re λ(F1)` of Eq. (1.3). -/
def spectralAbscissa {n : ℕ} (F1 : CMat n n) : ℝ :=
  sSup {r : ℝ | ∃ x : CVec n, x ≠ 0 ∧ ∃ lam : ℂ, F1.mulVec x = lam • x ∧ r = lam.re}

/-- `F1 = Q Λ Q⁻¹` with `Λ = diag(λ)` (Eq. (4.7)). -/
def IsDiagonalizedBy {n : ℕ} (F1 Q : CMat n n) (lam : Fin n → ℂ) : Prop :=
  F1 = Q * Matrix.diagonal lam * Q⁻¹

/-- The real spectral gap `δ(F1) = -max_{Re λ ≠ 0} Re λ` of Eq. (4.9). -/
def realSpectralGap {n : ℕ} (F1 : CMat n n) : ℝ :=
  -sSup {r : ℝ |
      ∃ x : CVec n, x ≠ 0 ∧ ∃ lam : ℂ, F1.mulVec x = lam • x ∧ lam.re ≠ 0 ∧ r = lam.re}

/-- The transformed matrix `F̃2 = Q⁻¹ F2 Q^{⊗2}` (Eq. (4.10)). -/
def tildeF2 {n : ℕ} (Q : CMat n n) (F2 : F2Mat n) : F2Mat n :=
  Q⁻¹ * (F2 * kronP2 Q)

/-- The transformed solution `x̃ = Q⁻¹ x` (Eq. (4.10)). -/
def tildeX {n : ℕ} (Q : CMat n n) (x : CVec n) : CVec n := Q⁻¹.mulVec x

/-! ## Nonresonance and Siegel gaps -/

/-- The tuple `λ` is nonresonant: no eigenvalue equals a sum of at least two
eigenvalues (Section 5.4). -/
def IsNonresonant {n : ℕ} (lam : Fin n → ℂ) : Prop :=
  ∀ (i : Fin n) (alpha : Fin n → ℕ), 2 ≤ ∑ j, alpha j →
    lam i ≠ ∑ j, (alpha j : ℂ) * lam j

/-- `λ` is `Δ`-nonresonant (Assumption 5.5, Eq. (5.124)): every resonant
difference is at least `Δ (m-1)` where `m = Σ α`. -/
def IsDeltaNonresonant {n : ℕ} (lam : Fin n → ℂ) (Δ : ℝ) : Prop :=
  ∀ (i : Fin n) (alpha : Fin n → ℕ), 2 ≤ ∑ j, alpha j →
    Δ * (((∑ j, alpha j : ℕ) : ℝ) - 1) ≤
      ‖lam i - ∑ j, (alpha j : ℂ) * lam j‖

/-- `λ` is of type `(Δ, ν)` (Assumption I.2): every resonant difference is at
least `Δ (m-1)^{-ν}`.  With `ν = -1` this is Assumption 5.5. -/
def IsOfType {n : ℕ} (lam : Fin n → ℂ) (Δ ν : ℝ) : Prop :=
  ∀ (i : Fin n) (alpha : Fin n → ℕ), 2 ≤ ∑ j, alpha j →
    Δ * (((∑ j, alpha j : ℕ) : ℝ) - 1) ^ (-ν) ≤
      ‖lam i - ∑ j, (alpha j : ℂ) * lam j‖

/-- The point `0` lies outside the convex hull of `λ` (Poincaré domain).  The
paper only uses this property through Lemma 5.6; we record it as convex-hull
membership of the origin. -/
def InPoincareDomain {n : ℕ} (lam : Fin n → ℂ) : Prop :=
  ∀ w : Fin n → ℝ, (∑ j, w j = 1) → (∀ j, 0 ≤ w j) →
    (∑ j, (w j : ℂ) * lam j) ≠ 0

/-! ## Sparsity and entrywise maximum norm -/

/-- `A` is `s`-column-sparse: each column has at most `s` nonzero entries. -/
def IsColumnSparse {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (s : ℕ) : Prop :=
  ∀ j : Fin n, (Finset.univ.filter (fun i : Fin m => A i j ≠ 0)).card ≤ s

/-- The entrywise maximum norm `‖B‖_max = max_{i,j} |B_{i,j}|`. -/
def maxEntryNorm {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ i : Fin m, ∃ j : Fin n, r = ‖B i j‖}

/-! ## Binary trees, forests and weighted fusion sums (Appendices C and H) -/

/-- `D_n`, the number of planar binary trees with `n` leaves
(Appendix H, Eq. (H.14)): `D_1 = 1` and `D_{n} = Σ_{a=1}^{n-1} D_a D_{n-a}`. -/
def treeCount (n : ℕ) : ℕ :=
  Nat.strongRecOn (motive := fun _ => ℕ) n fun n ih =>
    match n with
    | 0 => 0
    | 1 => 1
    | m + 2 =>
      ((Finset.range (m + 1)).attach).sum fun i =>
        ih (i.1 + 1) (Nat.succ_lt_succ (Finset.mem_range.mp i.2)) *
          ih (m + 1 - i.1) (Nat.lt_succ_of_le (Nat.sub_le (m + 1) i.1))

/-- The number of binary forests with `i` trees and `j` total leaves
(Appendix H, the paragraph after Eq. (H.16)). -/
def forestCount : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | i + 1, j + 1 =>
      ∑ m ∈ Finset.range (j + 1), treeCount (m + 1) * forestCount i (j + 1 - (m + 1))

/-- The `k`-th Catalan number `C_k = (1/(k+1)) binom(2k,k)` (Eq. (C.18)). -/
def catalan (k : ℕ) : ℚ := (Nat.choose (2 * k) k : ℚ) / (k + 1)

/-- One elementary fusion step at position `l` on a list of subsystem-excitation
flags: the two adjacent subsystems are replaced by a single excited one
(Section C.1, the `•`/`x` formalism after Eq. (C.25)). -/
def fuseAt (s : List Bool) (l : ℕ) : List Bool :=
  s.take l ++ [true] ++ s.drop (l + 2)

/-- Run a fusion path, returning the list of states after each step. -/
def runFusion (s : List Bool) : List ℕ → List (List Bool)
  | [] => []
  | l :: ls => let s' := fuseAt s l; s' :: runFusion s' ls

/-- A fusion path from `k+1` subsystems down to `j` subsystems: at step `t`
(level `i = k - t`) the fusion position lies in `{0, …, i-1}`. -/
def FusionPath (k j : ℕ) : Type :=
  { p : Fin (k - j + 1) → Fin k // ∀ t : Fin (k - j + 1), (p t).1 < k - t.1 }

instance fusionPathFintype (k j : ℕ) : Fintype (FusionPath k j) := by
  classical exact Subtype.fintype _

/-- The number `Ξ_i` of excited subsystems after the step at level `i`. -/
def excitedAt (k j : ℕ) (p : FusionPath k j) (i : ℕ) : ℕ :=
  let steps := runFusion (List.replicate (k + 1) false)
    (List.ofFn (fun t : Fin (k - j + 1) => (p.1 t).1))
  (steps.getD (k - i) []).countP (fun b => b)

/-- The weighted fusion sum `S_k^j` of Eq. (C.16). -/
def weightedFusionSum (k j : ℕ) : ℚ :=
  ∑ p : FusionPath k j,
    ∏ i ∈ Finset.Icc j k, ((excitedAt k j p i : ℚ))⁻¹

/-! ## Block encodings and oracle decision problems (Sections 6–7) -/

/-- A `(α, a, 0)`-block-encoding datum: the rescaling factor `α`, the ancilla
count `a`, and the encoded matrix dimensions.  The paper treats the implementing
unitary as a granted primitive (Section 2.4, Section 6.1). -/
structure BlockEncodingData (m n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  ancilla : ℕ

/-- The external guarantee of the linear-ODE solver of Ref. [10], quoted in
Section 2.4 (Eqs. (2.26)–(2.27)): block-encoded `B`, state preparation, and
`Õ(ω Cmax ĝ T log(1/ε))` queries.  Theorems 6.1–6.3 instantiate this guarantee. -/
structure LinearOdeSolverGuarantee where
  queryCost : ℝ → ℝ → ℝ → ℝ → ℝ
  gateCost : ℝ → ℝ → ℝ → ℝ → ℝ
  queryCost_nonneg : ∀ a b c d, 0 ≤ queryCost a b c d
  gateCost_nonneg : ∀ a b c d, 0 ≤ gateCost a b c d

/-- A promise decision problem over oracle-described instances (Definitions 7.1,
7.4, 7.7), with an explicit notion of instance size used by the polynomial
resource bounds. -/
structure PromiseProblem where
  Instance : Type
  size : Instance → ℕ
  yes : Set Instance
  no : Set Instance
  disjoint : ∀ x, x ∈ yes → x ∈ no → False

/-- A polynomial-resource quantum solver for a promise problem, in the uniform
model used in Section 7: an acceptance probability with a constant promise gap,
a query ledger and a gate ledger, both polynomially bounded in the instance
size.  These are exactly the resources that the containment proofs of
Theorems 7.6/7.9 and Appendix M produce. -/
structure BQPSolver (P : PromiseProblem) where
  queries : P.Instance → ℕ
  gates : P.Instance → ℕ
  acceptProb : P.Instance → ℝ
  queryPoly : ∃ c d : ℕ, ∀ x, queries x ≤ c * (P.size x + 1) ^ d
  gatePoly : ∃ c d : ℕ, ∀ x, gates x ≤ c * (P.size x + 1) ^ d
  gap : ∀ x, x ∈ P.yes → 2 / 3 ≤ acceptProb x
  gap_no : ∀ x, x ∈ P.no → acceptProb x ≤ 1 / 3

/-- `P` is in BQP in the paper's uniform oracle model. -/
def InBQP (P : PromiseProblem) : Prop := Nonempty (BQPSolver P)

/-- A polynomial-time many-one reduction between promise problems. -/
structure PolyReduction (P Q : PromiseProblem) where
  map : P.Instance → Q.Instance
  sizePoly : ∃ c d : ℕ, ∀ x, Q.size (map x) ≤ c * (P.size x + 1) ^ d
  preserves_yes : ∀ x, x ∈ P.yes → map x ∈ Q.yes
  preserves_no : ∀ x, x ∈ P.no → map x ∈ Q.no

/-- BQP-completeness of a promise problem (the notion asserted for Poly-CNOP,
Poly-NLSE and the perturbed oscillator problem in Theorems 7.6, 7.9, 7.10). -/
def BQPComplete (P : PromiseProblem) : Prop :=
  InBQP P ∧ ∀ Q : PromiseProblem, InBQP Q → Nonempty (PolyReduction Q P)

end Qatlib.Papers.CarlemanSim26.MainResults
