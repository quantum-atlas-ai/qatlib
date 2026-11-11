/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# CertSepAmb26 — core definitions

Fixed paper: Ambainis–Iraids–Kokainis, *Near-Optimal Separations of
Certificate Complexity from Randomized and Quantum Query Complexity*,
arXiv:2609.11664v2 (17 Sep 2026).

This module fixes the objects used by the paper-layer statements:

* a finite coordinate query model (`CoordModel`, oracle matrices, a
  randomized finite-tree model from the shared `BoolQueryTree`, and the
  bounded-error / exact / zero-error quantum query predicates built from the
  shared `FixedSpaceQueryUpperBound`);
* the complexity measures `C`, `C_0`, `R_1`, `R`, `Q`, `Q_E`, `Q_0` as
  `sInf`/suprema of the corresponding predicates;
* the Section 3 construction: position tables, prefix lengths `m_j(S)`, the
  unambiguous DNF `f`, the partial function `H`, the verification interface,
  the cheat-sheet totalization `F_n`;
* the asymptotic vocabulary `IsBigO`, `IsBigOmega`, `IsTheta`.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ENNReal
open Filter

namespace Qatlib.Papers.CertSepAmb26.MainResults

/-! ## 1. Finite coordinate query model -/

/-- A finite input type `X` together with a finite family `Q` of input
coordinates that separates points.  The number of input bits is `Fintype.card Q`;
a query asks the value of one coordinate. -/
structure CoordModel (X Q : Type*) [Fintype X] [Fintype Q] where
  /-- The value of coordinate `q` on input `x`. -/
  coord : X → Q → Bool
  /-- Coordinates determine the input. -/
  separates : ∀ x y : X, (∀ q, coord x q = coord y q) → x = y

/-- The standard oracle of a coordinate model: on the register `Q × Bool`
it flips the answer bit by the queried coordinate value. -/
def oracleMatrix {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (x : X) : Matrix (Q × Bool) (Q × Bool) ℂ :=
  Matrix.of fun a b => if a = (b.1, b.2 != M.coord x b.1) then 1 else 0

/-- Quantum query model with a three-symbol answer register: a separate
`Bool` flag records the inconclusive outcome `?` (flag `true`).  The oracle
acts on the answer qubit and leaves the flag untouched. -/
def oracleMatrixZero {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (x : X) : Matrix ((Q × Bool) × Bool) ((Q × Bool) × Bool) ℂ :=
  Matrix.of fun a b => if a = ((b.1.1, b.1.2 != M.coord x b.1.1), b.2) then 1 else 0

/-- `Q(f) ≤ T`: one unitary fixed-gate circuit, with a normalized start state
and at most `T` queries, outputs `f x` with probability at least `2/3` for
every input `x` (paper Section 2.1, bounded error `1/3`). -/
def quantumBoundedErrorLe {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (T : ℕ) : Prop :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.FixedSpaceQueryUpperBound
    (fun x => oracleMatrix M x)
    (fun x => Finset.univ.filter (fun s : Q × Bool => s.2 = f x)) (1 / 3) T

/-- `Q_E(f) ≤ T`: one unitary circuit with a fixed query count at most `T`
computes `f` with certainty (paper Section 2.1). -/
def quantumExactLe {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (T : ℕ) : Prop :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.FixedSpaceQueryUpperBound
    (fun x => oracleMatrix M x)
    (fun x => Finset.univ.filter (fun s : Q × Bool => s.2 = f x)) 0 T

/-- `Q_0(f) ≤ T`: a quantum circuit with a ternary answer register, at most
`T` queries, never a wrong answer, and the correct answer or `?` with
probability at least `1/2` on every input. -/
def quantumZeroErrorLe {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (T : ℕ) : Prop :=
  ∃ (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit ((Q × Bool) × Bool))
    (ψ₀ : Qatlib.Foundations.PureStateMath.QState ((Q × Bool) × Bool)),
    Qatlib.Foundations.QueryWordCore.Circuit.IsUnitaryCircuit C ∧
    Qatlib.Foundations.PureStateMath.Normalized ψ₀ ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C ≤ T ∧
    (∀ x,
      Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Foundations.QueryWordCore.Circuit.Run (oracleMatrixZero M x) C ψ₀)
        (Finset.univ.filter (fun s : (Q × Bool) × Bool => s.1.2 = !(f x) ∧ s.2 = false)) = 0) ∧
    (∀ x,
      (1 / 2 : ℝ) ≤
      Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Foundations.QueryWordCore.Circuit.Run (oracleMatrixZero M x) C ψ₀)
        (Finset.univ.filter (fun s : (Q × Bool) × Bool => s.1.2 = f x ∨ s.2 = true)))

/-- `D(f) ≤ T`: an exact deterministic decision tree with syntactic budget
at most `T`. -/
def deterministicLe {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (T : ℕ) : Prop :=
  ∃ t : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree Q Bool,
    (∀ x, (t.Run (M.coord x)).1 = f x) ∧ t.MaxQueries ≤ T

/-- `R(f) ≤ T`: a randomized finite-tree program whose every positive-probability
tree has budget at most `T`, and whose success probability is at least `2/3`
on every input. -/
def randomizedBoundedErrorLe {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (T : ℕ) : Prop :=
  ∃ prog : PMF (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree Q Bool),
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries prog T ∧
    (∀ x, (2 / 3 : ℝ≥0∞) ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog (M.coord x) (fun b => b = f x))

/-- `R_1(f) ≤ T`: one-sided-error randomized query complexity: negative inputs
are rejected with certainty, positive inputs accepted with probability `2/3`. -/
def randomizedOneSidedLe {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (T : ℕ) : Prop :=
  ∃ prog : PMF (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree Q Bool),
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries prog T ∧
    (∀ x, f x = false → Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog (M.coord x) (fun b => b = false) = 1) ∧
    (∀ x, f x = true → (2 / 3 : ℝ≥0∞) ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog (M.coord x) (fun b => b = true))

/-- `R_0(f) ≤ T`: randomized algorithm with a ternary answer (`none` is `?`),
never wrong, correct or inconclusive with probability at least `1/2`. -/
def randomizedZeroErrorLe {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (T : ℕ) : Prop :=
  ∃ prog : PMF (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree Q (Option Bool)),
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries prog T ∧
    (∀ x, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog (M.coord x) (fun o => o = some (f x) ∨ o = none) = 1) ∧
    (∀ x, (1 / 2 : ℝ≥0∞) ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb prog (M.coord x) (fun o => o = some (f x) ∨ o = none))

/-! ## 2. Complexity measures -/

/-- `C_x(f)`: the minimum size of a certificate for `f` at `x`. -/
def isCertificateAt {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (x : X) (S : Finset Q) : Prop :=
  ∀ y : X, (∀ q ∈ S, M.coord y q = M.coord x q) → f y = f x

/-- `C_x(f)` as a natural number. -/
def certificateSizeAt {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) (x : X) : ℕ :=
  sInf ((Finset.univ.filter fun S : Finset Q => isCertificateAt M f x S).image
    Finset.card : Set ℕ)

/-- `C(f)`: the maximum of `C_x(f)` over all inputs. -/
def certificateComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  (Finset.univ.image fun x : X => certificateSizeAt M f x).sup id

/-- `C_0(f, Z_0)`: the minimum size of a partial assignment of coordinates that
is consistent with the all-zero input and forces value `false`. -/
def zeroCertificateSize {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf ({S : Finset Q | ∀ y : X, (∀ q ∈ S, M.coord y q = false) → f y = false}.image
    Finset.card)

/-- `D(f)`. -/
def deterministicComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf {T : ℕ | deterministicLe M f T}

/-- `R(f)`. -/
def randomizedComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf {T : ℕ | randomizedBoundedErrorLe M f T}

/-- `R_1(f)`. -/
def randomizedOneSidedComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf {T : ℕ | randomizedOneSidedLe M f T}

/-- `R_0(f)`. -/
def randomizedZeroErrorComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf {T : ℕ | randomizedZeroErrorLe M f T}

/-- `Q(f)`. -/
def quantumComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf {T : ℕ | quantumBoundedErrorLe M f T}

/-- `Q_E(f)`. -/
def quantumExactComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf {T : ℕ | quantumExactLe M f T}

/-- `Q_0(f)`. -/
def quantumZeroErrorComplexity {X Q : Type*} [Fintype X] [Fintype Q] [DecidableEq Q]
    (M : CoordModel X Q) (f : X → Bool) : ℕ :=
  sInf {T : ℕ | quantumZeroErrorLe M f T}

/-! ## 3. Asymptotic vocabulary -/

/-- `g = O(h)` along `n → ∞`. -/
def IsBigO (g h : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, g n ≤ C * h n

/-- `g = Ω(h)` along `n → ∞`. -/
def IsBigOmega (g h : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, C * h n ≤ g n

/-- `g = Θ(h)` along `n → ∞`. -/
def IsTheta (g h : ℕ → ℝ) : Prop := IsBigO g h ∧ IsBigOmega g h

/-- `n ↦ (f n : ℝ)` for a natural-valued measure `f`. -/
def toReal (f : ℕ → ℕ) : ℕ → ℝ := fun n => (f n : ℝ)

/-! ## 4. The Section 3 construction -/

/-- The number of positions in one block, `n`. -/
abbrev Input (n : ℕ) := Fin n → Fin n → Bool

/-- A pair `(x, y)` of `{0,1}^{n×n}` inputs, the domain of the partial function `H`. -/
abbrev PairInput (n : ℕ) := Input n × Input n

/-- Coordinate model of one `n × n` block-string: coordinate `(i,p)` reads bit `p`
of block `i`. -/
def inputModel (n : ℕ) : CoordModel (Input n) (Fin n × Fin n) where
  coord := fun x q => x q.1 q.2
  separates := by
    intro x y h
    funext i p
    exact h (i, p)

/-- Coordinate model of `(x, y)`: the extra `Bool` selects `x` (`false`) or `y`
(`true`). -/
def pairModel (n : ℕ) : CoordModel (PairInput n) ((Fin n × Fin n) × Bool) where
  coord := fun u q => if q.2 then u.2 q.1.1 q.1.2 else u.1 q.1.1 q.1.2
  separates := by
    intro u v h
    have hx : u.1 = v.1 := by
      funext i p
      have := h ((i, p), false)
      simpa using this
    have hy : u.2 = v.2 := by
      funext i p
      have := h ((i, p), true)
      simpa using this
    exact Prod.ext hx hy

/-- `k = ⌊n/2⌋` (Section 3.1). -/
def half (n : ℕ) : ℕ := n / 2

/-- `⌈n/2⌉`. -/
def ceilHalf (n : ℕ) : ℕ := (n + 1) / 2

/-- `M = 8n`: the length of each random position list. -/
def posLen (n : ℕ) : ℕ := 8 * n

/-- `τ_n = n(⌈n/2⌉ + 1)`. -/
def tauN (n : ℕ) : ℕ := n * (ceilHalf n + 1)

/-- `⌈log₂ m⌉` (with value `0` for `m ≤ 1`). -/
def log2ceil (m : ℕ) : ℕ := if m ≤ 1 then 0 else Nat.log2 (m - 1) + 1

/-- `r = ⌊log₂ τ_n⌋ + 1` (Section 3.2). -/
def rParam (n : ℕ) : ℕ := Nat.log2 (tauN n) + 1

/-- Number of bits in a certificate description `z`, following Appendix D.1:
the fields `i, w_1,…,w_n, j_1,…,j_M, p⋆` each use `⌈log₂(n+1)⌉` bits, and the
`σ_1,…,σ_n` each use `⌈log₂(M+1)⌉` bits. -/
def descLen (n : ℕ) : ℕ :=
  (n + posLen n + 2) * log2ceil (n + 1) + n * log2ceil (posLen n + 1)

/-- A position table: `n` lists, each of length `M = 8n`, of positions in `[n]`. -/
abbrev PosTable (n : ℕ) := Fin n → Fin (posLen n) → Fin n

/-- `m_j(S) = min{a ∈ [M] : P_j(a) ∈ S}`, with value `M+1` when no entry hits `S`
(Section 3.1). -/
def mOf {n : ℕ} (P : PosTable n) (j : Fin n) (S : Finset (Fin n)) : ℕ :=
  if h : (Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).Nonempty then
    ((Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).min' h).val + 1
  else posLen n + 1

/-- `m_j(S) ≤ M+1`. -/
lemma mOf_le {n : ℕ} (P : PosTable n) (j : Fin n) (S : Finset (Fin n)) :
    mOf P j S ≤ posLen n + 1 := by
  unfold mOf
  split_ifs with h
  · have := ((Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).min' h).isLt
    omega
  · exact le_rfl

/-- The good-table property of Lemma 3.1, in the form used downstream: every
`S` of size at least `n/3` is hit by every list, and the prefix lengths sum to
at most `8n`.  The first conjunct is implied by the sum bound (each term is at
least one when the list misses an nonempty `S`), and is recorded explicitly so
that `m_j(S) ≤ M` is available. -/
def GoodTable {n : ℕ} (P : PosTable n) : Prop :=
  (∀ S : Finset (Fin n), n ≤ 3 * S.card →
      ∀ j : Fin n, (Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).Nonempty) ∧
  (∀ S : Finset (Fin n), n ≤ 3 * S.card → (∑ j : Fin n, mOf P j S) ≤ 8 * n)

/-- Under a good table and `|S| ≥ n/3`, the list `P j` hits `S`, so `m_j(S) ≤ M`. -/
lemma goodTable_hit {n : ℕ} {P : PosTable n} (hG : GoodTable P)
    {S : Finset (Fin n)} (hS : n ≤ 3 * S.card) (j : Fin n) :
    (Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).Nonempty :=
  hG.1 S hS j

/-- Under a good table and `|S| ≥ n/3`, `m_j(S) ≤ M`. -/
lemma mOf_le_posLen {n : ℕ} {P : PosTable n} (hG : GoodTable P)
    {S : Finset (Fin n)} (hS : n ≤ 3 * S.card) (j : Fin n) :
    mOf P j S ≤ posLen n := by
  have hne := goodTable_hit hG hS j
  unfold mOf
  rw [dif_pos hne]
  have := ((Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).min' hne).isLt
  omega

/-- Under a good table and `|S| ≥ n/3`, the entry `P_j(m_j(S))` lies in `S`. -/
lemma mOf_pred_mem {n : ℕ} {P : PosTable n} (hG : GoodTable P)
    {S : Finset (Fin n)} (hS : n ≤ 3 * S.card) (j : Fin n) :
    P j ⟨mOf P j S - 1, by
      have hle := mOf_le_posLen hG hS j
      have hne := goodTable_hit hG hS j
      have hpos : 1 ≤ mOf P j S := by
        unfold mOf
        rw [dif_pos hne]
        omega
      omega⟩ ∈ S := by
  have hne := goodTable_hit hG hS j
  have hmem : (Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).min' hne ∈
      Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S) :=
    Finset.min'_mem _ hne
  have hval : mOf P j S =
      ((Finset.univ.filter (fun a : Fin (posLen n) => P j a ∈ S)).min' hne).val + 1 := by
    unfold mOf
    rw [dif_pos hne]
  have hpos : 1 ≤ mOf P j S := by omega
  have hidx : (⟨mOf P j S - 1, by
      have hle := mOf_le_posLen hG hS j
      omega⟩ : Fin (posLen n)) = (Finset.univ.filter
        (fun a : Fin (posLen n) => P j a ∈ S)).min' hne := by
    apply Fin.ext
    simp only
    omega
  rw [hidx]
  exact (Finset.mem_filter.mp hmem).2

/-- The support of block `i` of `x`. -/
def blockSupport {n : ℕ} (x : Input n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => x i p = true)

/-- `A_{ij}(S) = {P_i(a) : 1 ≤ a ≤ m_j(S)}`, the positions required to be zero
in block `j` by the term `T_{i,S}` (Section 3.1). -/
def Aij {n : ℕ} (P : PosTable n) (i j : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ.filter (fun a : Fin (posLen n) => a.val < mOf P j S)).image (P i)

/-- The term `T_{i,S}` is satisfied by `x` (Section 3.1): block `i` has support
exactly `S`, and every position in `A_{ij}(S)` is zero in block `j`. -/
def TermSat {n : ℕ} (P : PosTable n) (x : Input n) (i : Fin n)
    (S : Finset (Fin n)) : Prop :=
  S.card = half n ∧ blockSupport x i = S ∧
    ∀ j : Fin n, j ≠ i → ∀ p ∈ Aij P i j S, x j p = false

/-- The DNF `f(x) = ⋁_{i,S, |S|=k} T_{i,S}` (Section 3.1). -/
def fDNF {n : ℕ} (P : PosTable n) (x : Input n) : Bool :=
  decide (∃ i S, TermSat P x i S)

/-- `⋁_{p ∈ S} y_i(p)`. -/
def blockOr {n : ℕ} (y : Input n) (i : Fin n) (S : Finset (Fin n)) : Bool :=
  decide (∃ p, p ∈ S ∧ y i p = true)

/-- The partial function `H(x,y) = ⋁_{p∈S} y_i(p)` where `(i,S)` is the unique
satisfied term; undefined (`none`) when `f(x) = 0` (Section 3.1, equation (1)). -/
def H {n : ℕ} (P : PosTable n) (x y : Input n) : Option Bool :=
  if h : ∃ i S, TermSat P x i S then
    some (blockOr y h.choose (h.choose_spec).choose)
  else none

/-! ### Verification procedure (Lemma 3.3 / Appendix D.1) -/

/-- Coordinates read by a verification check: an `x` or `y` bit, or a bit of
the description `z`. -/
abbrev VerifyCoord (n : ℕ) := (Fin n × Fin n) × Bool ⊕ Fin (descLen n)

/-- The oracle of a verification check. -/
def verifyOracle {n : ℕ} (x y : Input n) (z : Fin (descLen n) → Bool) :
    VerifyCoord n → Bool
  | Sum.inl ((i, p), false) => x i p
  | Sum.inl ((i, p), true) => y i p
  | Sum.inr t => z t

/-- A verification interface `A(x,y,β,z) = ⋀_{i=1}^m A_i(x,y,β,z)`, each check
given by a deterministic decision tree of bounded query count. -/
structure Verifier (n : ℕ) where
  /-- The number of conjuncts `m`. -/
  m : ℕ
  /-- The `i`-th conjunct, as a decision tree; `β` is a parameter. -/
  tree : Fin m → Bool → Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree
    (VerifyCoord n) Bool

/-- `A(x,y,β,z) = 1` iff every conjunct accepts. -/
def Verifier.accepts {n : ℕ} (V : Verifier n) (x y : Input n) (β : Bool)
    (z : Fin (descLen n) → Bool) : Bool :=
  decide (∀ i : Fin V.m,
    (V.tree i β).Run (verifyOracle x y z) |>.1 = true)

/-- The properties of the verification procedure stated in Lemma 3.3: it is a
conjunction of `O(n)` checks, each evaluable with `O(ln n)` queries, and it
accepts exactly the descriptions certifying the value of `H`. -/
structure VerifierSpec {n : ℕ} (P : PosTable n) (V : Verifier n) : Prop where
  m_bound : ∃ c : ℕ, V.m ≤ c * (n + 1)
  query_bound : ∃ c : ℕ, ∀ (i : Fin V.m) (β : Bool),
    (V.tree i β).MaxQueries ≤ c * (Nat.log2 (n + 1) + 1)
  iff : ∀ (x y : Input n) (β : Bool) (z : Fin (descLen n) → Bool),
    V.accepts x y β z = true ↔ H P x y = some β

/-! ### Cheat-sheet totalization (Section 3.2) -/

/-- Index type of the `2^r` cheat-sheet cells. -/
abbrev Address (n : ℕ) := Fin (Fintype.card (Fin (rParam n) → Bool))

/-- The address of a bit string `β ∈ {0,1}^r`. -/
def addressOf {n : ℕ} (β : Fin (rParam n) → Bool) : Address n :=
  Fintype.equivFin _ β

/-- An input to the totalized function `F_n`: `r` copies of `(x,y)` and `2^r`
cheat sheets, each holding `r` descriptions of length `d`. -/
structure FnInput (n : ℕ) where
  copies : Fin (rParam n) → PairInput n
  sheets : Address n → Fin (rParam n) → Fin (descLen n) → Bool
  deriving Fintype, DecidableEq

/-- The total Boolean function `F_n` (Section 3.2): one if there is an address
`β` such that every copy `(x^(ℓ), y^(ℓ))` evaluates to `β_ℓ` and the addressed
cell contains an accepting description for every copy. -/
def Fn {n : ℕ} (P : PosTable n) (V : Verifier n) (u : FnInput n) : Bool :=
  decide (∃ β : Fin (rParam n) → Bool,
    (∀ l, H P (u.copies l).1 (u.copies l).2 = some (β l)) ∧
    (∀ l, V.accepts (u.copies l).1 (u.copies l).2 (β l)
      (u.sheets (addressOf β) l)))

/-- Natural coordinates of `FnInput`: the bits of the `r` copies, or the bits
of the cheat-sheet array. -/
abbrev QFn (n : ℕ) :=
  (Fin (rParam n) × (Fin n × Fin n) × Bool) ⊕
    (Address n × Fin (rParam n) × Fin (descLen n))

/-- Coordinate reading function for `FnInput`. -/
def fnCoord {n : ℕ} (u : FnInput n) : QFn n → Bool
  | Sum.inl (l, (i, p), false) => (u.copies l).1 i p
  | Sum.inl (l, (i, p), true) => (u.copies l).2 i p
  | Sum.inr (a, l, t) => u.sheets a l t

/-- Coordinate model of the totalized input type. -/
def fnModel (n : ℕ) : CoordModel (FnInput n) (QFn n) where
  coord := fnCoord
  separates := by
    intro u v h
    cases u with
    | mk c1 s1 =>
      cases v with
      | mk c2 s2 =>
        have hc : c1 = c2 := by
          funext l
          apply Prod.ext
          · funext i p
            exact h (Sum.inl (l, (i, p), false))
          · funext i p
            exact h (Sum.inl (l, (i, p), true))
        have hs : s1 = s2 := by
          funext a l t
          exact h (Sum.inr (a, l, t))
        rw [hc, hs]

/-- The all-zero input to `F_n`. -/
def zeroPair (n : ℕ) : PairInput n :=
  (fun _ _ => false, fun _ _ => false)

/-- The all-zero input `Z_0` to `F_n`. -/
def zeroFnInput (n : ℕ) : FnInput n where
  copies := fun _ => zeroPair n
  sheets := fun _ _ _ => false

/-- A fixed choice of the paper's parameters: a position table and a verification
interface for every `n`, good on a tail and satisfying the Lemma 3.3 contract. -/
structure MainConstruction where
  pos : ∀ n, PosTable n
  ver : ∀ n, Verifier n
  good : ∀ᶠ n in atTop, GoodTable (pos n)
  spec : ∀ n, VerifierSpec (pos n) (ver n)

namespace MainConstruction

/-- The total function `F_n` associated with the construction. -/
def F (C : MainConstruction) (n : ℕ) : FnInput n → Bool := Fn (C.pos n) (C.ver n)

/-- Its coordinate model. -/
def model (_C : MainConstruction) (n : ℕ) : CoordModel (FnInput n) (QFn n) := fnModel n

end MainConstruction

/-! ### Partial assignments for Lemma 3.4 -/

/-- A partial assignment of the `2n²` variables of `(x,y)`; `none` means unfixed. -/
structure PartialAssign (n : ℕ) where
  xa : Fin n → Fin n → Option Bool
  ya : Fin n → Fin n → Option Bool

/-- The number of fixed variables. -/
def PartialAssign.size {n : ℕ} (η : PartialAssign n) : ℕ :=
  (Finset.univ.filter (fun q : Fin n × Fin n => (η.xa q.1 q.2).isSome)).card +
  (Finset.univ.filter (fun q : Fin n × Fin n => (η.ya q.1 q.2).isSome)).card

/-- Consistency with the all-zero input: every fixed bit is zero. -/
def PartialAssign.ConsistentZero {n : ℕ} (η : PartialAssign n) : Prop :=
  (∀ i p, η.xa i p = some true → False) ∧ (∀ i p, η.ya i p = some true → False)

/-- A completion of the partial assignment. -/
def PartialAssign.Agrees {n : ℕ} (η : PartialAssign n) (x y : Input n) : Prop :=
  (∀ i p b, η.xa i p = some b → x i p = b) ∧
  (∀ i p b, η.ya i p = some b → y i p = b)

end Qatlib.Papers.CertSepAmb26.MainResults
