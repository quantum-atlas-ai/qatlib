/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureEnsemblePGM
import Qatlib.Concepts.ShadowModels.BooleanCubeFourier
import Qatlib.Concepts.AdaptiveQuery.RawProcess.ObservedCircuitLaws

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

set_option backward.isDefEq.respectTransparency false

/-!
# WildcardSrch12 — source model

Ambainis–Montanaro, "Quantum algorithms for search with wildcards and
combinatorial group testing", fixed arXiv:1210.1148v4 (20 May 2013).

This module fixes the paper's objects:

* Boolean strings, Hamming weight/distance (§1.2);
* the wildcard query `Q_x(S,y)` and the CGT query `Q_x(S)` (§1.2);
* the state `|ψ_x^k⟩ = C(n,k)^{-1/2} Σ_{|S|=k} |S⟩|x_S⟩` (§3);
* the Gram matrix `G_xy = ⟨ψ_x^k|ψ_y^k⟩` as the library's `ensembleGram` of the
  actual column family, and the pretty-good-measurement outcome probability
  `(√G_xy)²` (§3: "the probability that the PGM outputs j on input |φ_i⟩ is
  precisely |√G_ij|²");
* the query register and the unitary wildcard/CGT oracles used by the
  circuit-level statements of Theorems 1–2 and Lemma 4.

Boundary: the algorithm model is the library's counted-query observed-circuit
model with an explicit oracle matrix; no gate synthesis, no efficient
implementation of the PGM, and no input distribution are asserted.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Papers.WildcardSrch12.MainResults

/-- Boolean strings on `n` bits, the paper's `{0,1}^n`. -/
abbrev BitStr (n : ℕ) := Fin n → Bool

/-- Hamming weight `|x|`: the number of `true` entries. -/
def bitWeight {n : ℕ} (x : BitStr n) : ℕ :=
  (Finset.univ.filter (fun i => x i)).card

/-- Hamming distance `d(x,y)`: the number of coordinates where `x` and `y` differ. -/
def hammingDist {n : ℕ} (x y : BitStr n) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- The coordinates on which `x` and `y` agree (the complement of their
difference support). -/
def agreeSet {n : ℕ} (x y : BitStr n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = y i)

/-- Hamming distance is symmetric. -/
theorem hammingDist_comm {n : ℕ} (x y : BitStr n) :
    hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  ext i
  simp [ne_comm]

/-- The Hamming distance of a string from itself vanishes. -/
theorem hammingDist_self {n : ℕ} (x : BitStr n) : hammingDist x x = 0 := by
  simp [hammingDist]

/-- Agreement and disagreement partition the coordinates, so the agreement set has
cardinality `n - d(x,y)`. -/
theorem card_agreeSet {n : ℕ} (x y : BitStr n) :
    (agreeSet x y).card = n - hammingDist x y := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => x i = y i)
  have hd : (Finset.univ.filter fun i => ¬ (x i = y i)) =
      (Finset.univ.filter fun i => x i ≠ y i) := by
    apply Finset.filter_congr
    intro i _
    exact Iff.rfl
  rw [hd, Finset.card_univ, Fintype.card_fin] at h
  unfold agreeSet hammingDist
  omega

/-- The paper's wildcard query `Q_x(S,y)`: it returns true iff `y` matches `x` on
every coordinate of `S` (coordinates outside `S` are ignored, so a full
`BitStr n` is a convenient carrier for the paper's `y ∈ {0,1}^{|S|}`). -/
def wildcardReply {n : ℕ} (x : BitStr n) (S : Finset (Fin n)) (y : BitStr n) : Bool :=
  decide (∀ i ∈ S, y i = x i)

/-- The paper's combinatorial-group-testing query `Q_x(S)`: true iff some
coordinate of `S` is a `1`-index of `x`. -/
def cgtReply {n : ℕ} (x : BitStr n) (S : Finset (Fin n)) : Bool :=
  decide (∃ i ∈ S, x i = true)

/-- The canonical extension of `x|_S` to all of `[n]` by `false` outside `S`. -/
def embedOn {n : ℕ} (x : BitStr n) (S : Finset (Fin n)) : BitStr n :=
  fun i => if i ∈ S then x i else false

/-- The embed On apply mem property in the paper model. -/
@[simp] theorem embedOn_apply_mem {n : ℕ} (x : BitStr n) {S : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ S) : embedOn x S i = x i := by
  simp [embedOn, hi]

/-- The embed On apply not Mem property in the paper model. -/
@[simp] theorem embedOn_apply_notMem {n : ℕ} (x : BitStr n) {S : Finset (Fin n)}
    {i : Fin n} (hi : i ∉ S) : embedOn x S i = false := by
  simp [embedOn, hi]

/-- Two restrictions agree on `S` exactly when `S` is contained in their
agreement set. -/
theorem embedOn_eq_iff {n : ℕ} (x y : BitStr n) (S : Finset (Fin n)) :
    embedOn x S = embedOn y S ↔ S ⊆ agreeSet x y := by
  constructor
  · intro h i hi
    have := congrFun h i
    simp only [embedOn, hi, if_true] at this
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, this⟩
  · intro h
    funext i
    by_cases hi : i ∈ S
    · have hmem := Finset.mem_filter.mp (h hi)
      simp [embedOn, hi, hmem.2]
    · simp [embedOn, hi]

/-- Basis index of `|ψ_x^k⟩`: a subset `S` and the value `y` of the `|x_S⟩`
register.  Only `S` with `S.card = k` and `y = x|_S` padded by `false` carry
nonzero amplitude; the padding is the canonical embedding of `x_S` into
`BitStr n`. -/
abbrev StateIdx (n : ℕ) := Finset (Fin n) × BitStr n

/-- The dimension of the padded Hilbert space carrying the states (the paper's
subspace is spanned by the `(S, x|_S)` with `|S| = k`).  Declared as an `abbrev` so
that sums over `Fin (stateDim n)` reduce to sums over `StateIdx n` in rewriting. -/
abbrev stateDim (n : ℕ) : ℕ := Fintype.card (StateIdx n)

/-- Amplitude of `|ψ_x^k⟩` at the basis vector `(S, y)`: `C(n,k)^{-1/2}` when
`|S| = k` and `y` is the canonical embedding of `x|_S`, and `0` otherwise. -/
noncomputable def psiAmp {n : ℕ} (k : ℕ) (x : BitStr n) (p : StateIdx n) : ℂ :=
  if p.1.card = k ∧ p.2 = embedOn x p.1 then
    ((Real.sqrt ((Nat.choose n k : ℝ)⁻¹) : ℝ) : ℂ)
  else 0

/-- The `x`-column of the state family, indexed by `Fin (stateDim n)`. -/
noncomputable def stateColumn {n : ℕ} (k : ℕ) (x : BitStr n) :
    Fin (stateDim n) → ℂ :=
  fun d => psiAmp k x ((Fintype.equivFin (StateIdx n)).symm d)

/-- The ensemble matrix `W` whose `x`-column is `|ψ_x^k⟩`. -/
noncomputable def psiEnsemble (n k : ℕ) : Matrix (Fin (stateDim n)) (BitStr n) ℂ :=
  fun d x => stateColumn k x d

/-- The Gram matrix `G_xy = ⟨ψ_x^k|ψ_y^k⟩` of the paper's states, realized as the
library's ensemble Gram matrix of the actual column family (so that its square
root is a genuine matrix square root, not a stand-in). -/
noncomputable def gramMat (n k : ℕ) : HermitianMat (BitStr n) ℂ :=
  ensembleGram (psiEnsemble n k)

/-- The pretty-good-measurement outcome probability `(√G_xy)² = |√G_xy|²`: the
probability that the PGM of §3 outputs `y` when the input state is `|ψ_x^k⟩`
(paper: "the probability that the PGM outputs j on input |φ_i⟩ is precisely
|√G_ij|²"). -/
noncomputable def pgmProb (n k : ℕ) (x y : BitStr n) : ℝ :=
  Complex.normSq ((gramMat n k).sqrt.mat y x)

/-- Expected Hamming distance of the PGM output from `x`, the quantity `D_k` of
§3: `Σ_y d(x,y)·(√G_xy)²`. -/
noncomputable def pgmExpectedDistance (n k : ℕ) (x : BitStr n) : ℝ :=
  ∑ y : BitStr n, (hammingDist x y : ℝ) * pgmProb n k x y

/-- The paper's Gram entry `G_xy = C(n-d(x,y), k)/C(n,k)` (§3). -/
noncomputable def gramEntry (n k d : ℕ) : ℝ :=
  (Nat.choose (n - d) k : ℝ) / (Nat.choose n k : ℝ)

/-- Register of a wildcard query: queried subset `S`, claimed assignment `y`, the
one-bit answer, and an `r`-qubit workspace. -/
abbrev WildcardReg (n r : ℕ) := (Finset (Fin n) × BitStr n × Bool) × Fin r

/-- The paper's wildcard oracle, lifted by the identity on the workspace:
`|S⟩|y⟩|z⟩|w⟩ ↦ |S⟩|y⟩|z ⊕ Q_x(S,y)⟩|w⟩` (§1.2). -/
noncomputable def wildcardOracle (n r : ℕ) (x : BitStr n) :
    Matrix (WildcardReg n r) (WildcardReg n r) ℂ :=
  Matrix.of fun p q =>
    if q = ((p.1.1, p.1.2.1, (p.1.2.2 != wildcardReply x p.1.1 p.1.2.1)), p.2)
    then 1 else 0

/-- Register of a CGT query: queried subset `S`, the one-bit answer, and an
`r`-qubit workspace. -/
abbrev CGTReg (n r : ℕ) := (Finset (Fin n) × Bool) × Fin r

/-- The paper's CGT oracle, lifted by the identity on the workspace:
`|S⟩|z⟩|w⟩ ↦ |S⟩|z ⊕ Q_x(S)⟩|w⟩` (§1.2). -/
noncomputable def cgtOracle (n r : ℕ) (x : BitStr n) :
    Matrix (CGTReg n r) (CGTReg n r) ℂ :=
  Matrix.of fun p q =>
    if q = ((p.1.1, (p.1.2 != cgtReply x p.1.1)), p.2) then 1 else 0

end Qatlib.Papers.WildcardSrch12.MainResults
