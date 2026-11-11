/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option backward.isDefEq.respectTransparency false

/-!
# LinkInvQFT12.MainResults — source model (arXiv:1210.1550)

Krovi--Russell, *Quantum Fourier Transforms and the Complexity of Link Invariants
for Quantum Doubles of Finite Groups*, fixed arXiv:1210.1550 (v2 PDF, 24 Jul 2013;
the metadata line numbers refer to the same text of v1).

This file fixes the abstract objects that the paper-layer statements of
`Theorem 2` (c001), `Theorem 3` (c002), `Theorem 4` (c003), `Lemma 5` (c004),
`Lemma 6` (c005) and `Lemma 7` (c006) talk about:

* braid words `b ∈ Bₙ` of size `m`;
* irreps `([g], ρ)` of the quantum double `D(G)`;
* the colored trace and plat closures `τ_Λ`/`Pl_Λ` of a braid (eq. (4.2)–(4.5));
* the semantic contract of an `ε`-additive quantum/classical approximation
  algorithm together with its polynomial runtime ledger;
* the complexity-class completeness assertion of Theorem 4.

The R-matrix of `D(G)` and the actual machine model are *not* formalised here; the
two closure maps and the completeness predicates are the abstract interface of this
layer, exactly as recorded in the claim binding notes (rank D, no Dev/Frozen
declaration of the result).  Consequently the algorithmic statements (c001–c004)
are registered as `Prop`-valued contracts without proof terms, while the
group-theoretic Lemma 6 (c005) and Lemma 7 (c006) are proved outright in their own
files.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinkInvQFT12.MainResults

/-- A braid word on `n` strands with `m` crossings, written in the Artin generators:
`letters i = (j, pos)` is `σⱼ` when `pos = true` and `σⱼ⁻¹` when `pos = false`
(arXiv:1210.1550 §4.2: `b ∈ Bₙ` of size `m`). -/
structure BraidWord (n m : ℕ) where
  letters : Fin m → Fin n × Bool

/-- A chosen irreducible representation `([g], ρ)` of the quantum double `D(G)`
(arXiv:1210.1550 §3.2): `flux` is the representative `g` of a conjugacy class of `G`
(hence the centralizer `Z(g)` is determined), and `chargeDim` is the dimension of the
irrep `ρ` of `Z(g)`; the paper's `([g], ρ)` and the fluxon `([g], id)` (with `ρ` trivial,
encoded by `chargeDim = 1`). -/
structure DGIrrep (G : Type*) [Group G] where
  flux : G
  chargeDim : ℕ
  chargeDim_pos : 0 < chargeDim

/-- The trace and plat closures of `D(G)`-colored braids, as complex-valued invariants.
The paper computes them as `tr τ_Λ(θ)` and `⟨α|τ_Λ(θ)|α⟩` from the R-matrix of `D(G)`
(arXiv:1210.1550 §4.1–4.2, eq. (4.2)–(4.5)).  The R-matrix is not formalised in this
layer, so the two maps are kept as an abstract interface (see the module docstring). -/
structure ClosureInvariants (G : Type*) [Group G] where
  traceClosure : {n m : ℕ} → DGIrrep G → BraidWord n m → ℂ
  platClosure : {n m : ℕ} → DGIrrep G → BraidWord n m → ℂ

/-- The kind of machine that realises an algorithm (the paper's quantum vs. classical
distinction between Theorem 2 and Theorem 3). -/
inductive AlgorithmKind where
  | quantum
  | classical
  deriving DecidableEq, Repr

/-- An `ε`-additive link algorithm for a fixed finite group `G`, its closure invariants
`I`, a `D(G)`-irrep `Λ` and error `ε > 0`.

The fields record exactly the paper's guarantee: on every braid `b ∈ Bₙ` of size `m`
the algorithm outputs values within additive error `ε` of the true trace and plat
closures, and it carries a cost ledger `cost m n L k` where `L = ⌈log₂|G|⌉` and
`k = ⌈1/ε⌉` are the paper's runtime parameters.  The two `…_ok` rows are `Prop` fields,
so an inhabitant certifies the error guarantee; this keeps the algorithmic existence
statements of Theorems 2/3 from being trivially witnessed by a numerical pair. -/
structure LinkAlgorithm (G : Type*) [Group G] (I : ClosureInvariants G)
    (Λ : DGIrrep G) (ε : ℝ) where
  kind : AlgorithmKind
  /-- Runtime ledger in `(m, n, L, k)` with `L = log₂|G|`, `k = 1/ε`. -/
  cost : ℕ → ℕ → ℕ → ℕ → ℝ
  outTrace : {n m : ℕ} → BraidWord n m → ℂ
  outPlat : {n m : ℕ} → BraidWord n m → ℂ
  /-- Additive-error certificate for the trace closure. -/
  trace_ok : ∀ {n m : ℕ} (b : BraidWord n m),
    ‖I.traceClosure Λ b - outTrace b‖ ≤ ε
  /-- Additive-error certificate for the plat closure. -/
  plat_ok : ∀ {n m : ℕ} (b : BraidWord n m),
    ‖I.platClosure Λ b - outPlat b‖ ≤ ε

/-- `PolyCost f` says the runtime ledger `f` is polynomially bounded in
`m, n, log|G|, 1/ε`, i.e. `f ≤ C · (m+n+L+k+1)^d` — the paper's
`O(poly(m,n,log|G|,1/ε))` for Theorems 2, 3, 4 and Lemma 5. -/
def PolyCost (f : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ m n L k : ℕ, f m n L k ≤ C * ((m + n + L + k + 1 : ℕ) : ℝ) ^ d

/-- `⌈log₂ |G|⌉`, the group-size ledger `L` of the paper's runtime. -/
def logCard (G : Type*) [Fintype G] : ℕ := Nat.log 2 (Fintype.card G)

/-- `⌈1/ε⌉`, the precision ledger `k` of the paper's runtime. -/
def invEps (ε : ℝ) : ℕ := Nat.ceil ε⁻¹

/-- A braid instance bundling its numbers of strands and crossings, used to phrase a
"problem" over all braids (Theorem 4). -/
structure BraidInstance where
  n : ℕ
  m : ℕ
  word : BraidWord n m

/-- The three complexity classes named in Theorem 4. -/
inductive ComplexityClass where
  | BPP
  | SBP
  | SharpP
  deriving DecidableEq, Repr

/-- `CompleteFor C f` records the paper's completeness assertion of Theorem 4: the problem
of approximating the invariant `f` (additively for `BPP`, multiplicatively for `SBP`, and
exactly for `SharpP`) is complete for the class `C`.  The standard promise reductions
underlying completeness (arXiv:1210.1550 §5, Definitions 2–4) are part of the source's
complexity-theoretic background and are not formalised in this layer; the predicate is the
abstract interface standing for that conclusion. -/
opaque CompleteFor {ι : Type*} (C : ComplexityClass) (f : ι → ℂ) : Prop

/-- A randomized computation on `n` bits together with the probability `Pₛ` of success
(arXiv:1210.1550 §5, Lemma 5).  Only the success probability is retained, since that is
what the lemma relates to the plat closure. -/
structure RandomizedComputation (n : ℕ) where
  /-- Probability `Pₛ` that the computation accepts. -/
  successProbability : ℝ
  prob_nonneg : 0 ≤ successProbability
  prob_le_one : successProbability ≤ 1

/-- `FourFixedPoints α` says that the permutation `α` fixes at least four points — the
"at least 4 fixed points" condition of `Aₘ` conjugacy classes in Theorem 4, Lemma 5 and
Lemma 6. -/
def FourFixedPoints {m : ℕ} (α : Equiv.Perm (Fin m)) : Prop :=
  4 ≤ (Finset.univ.filter (fun i => α i = i)).card

end Qatlib.Papers.LinkInvQFT12.MainResults
