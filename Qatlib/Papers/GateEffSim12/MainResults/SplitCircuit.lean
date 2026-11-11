/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GateEffSim12.MainResults.CompressedEncoding
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SplitCircuit — Lemma 5.1 of arXiv:1211.4637v2

Fixed paper version: arXiv:1211.4637v2 (5 April 2013), PDF SHA-256
`aef583fed3675ee75a251ed7438ab99cb4c16b34697dd8f4293f3d39d07d471d`.
Lemma 5.1 is stated on p. 15 (Eq. (25)).

The lemma says: for `x = x_1 x_2` with `x ∈ {0,1}^m`, `|x| ≤ k`, `x_1, x_2` the
two halves of `x` (`m` a power of two), there is a quantum circuit of
complexity `O(k log m)` realising the mapping
`C_m^k|x_1 x_2> ↦ C_{m/2}^k|x_1> ⊗ C_{m/2}^k|x_2>`.

Since both sides are computational basis states (`Definition 4.1`), the proof
observes that a reversible *classical* procedure on the `k+1` registers of
size `O(log m)` suffices, and that it can be made coherent.  We model the
procedure as a list of local classical gates on `(k+1)` registers of dimension
`m+1`, together with an output map into the pair of half-encodings.

Model boundary (recorded as the proof gap below): the gate set is a classical
register model (`LocalGate`), not a unitary 1- and 2-qubit gate set; the paper's
statement is dimensionally loose in that the tensor product
`C_{m/2}^k|x_1> ⊗ C_{m/2}^k|x_2>` uses `2(k+1)` registers while the paper
writes both sides in `(ℂ^{m+1})^{⊗(k+1)}`.  We model the target as the pair of
half-encodings, and the output map `SplitCircuit.out` is an explicit field.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Papers.GateEffSim12.MainResults.CompressedEncoding

namespace Qatlib.Papers.GateEffSim12.MainResults.SplitCircuit

/-! ## Halves of a bit string -/

/-- The first half `x_1` of `x = x_1 x_2`, for `x : Fin m → Bool` with
`m = 2 * n`. -/
def halfLeft {m n : ℕ} (hm : m = 2 * n) (x : Fin m → Bool) : Fin n → Bool :=
  fun i => x (Fin.castLE (by omega) i)

/-- The second half `x_2` of `x = x_1 x_2`, for `x : Fin m → Bool` with
`m = 2 * n`. -/
def halfRight {m n : ℕ} (hm : m = 2 * n) (x : Fin m → Bool) : Fin n → Bool :=
  fun i => x ⟨n + i.val, by omega⟩

/-! ## A local classical gate model on the compressed registers -/

/-- Local classical gates on `(k+1)` registers of dimension `m+1`: a
permutation of one register, or a reversible addition of a constant into one
register.  These are the register operations used by the paper's coherent
version of the classical split procedure (Lemma 5.1 proof, p. 15). -/
inductive LocalGate (k m : ℕ) where
  | perm (i : Fin (k + 1)) (σ : Equiv.Perm (Fin (m + 1)))
  | add (i : Fin (k + 1)) (c : Fin (m + 1))

/-- Semantics of a local gate on computational basis states. -/
def LocalGate.eval {k m : ℕ} :
    LocalGate k m → (Fin (k + 1) → Fin (m + 1)) → (Fin (k + 1) → Fin (m + 1))
  | .perm i σ, v => Function.update v i (σ (v i))
  | .add i c, v =>
      Function.update v i
        ⟨((v i).val + c.val) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- Semantics of a list of local gates (a circuit). -/
def evalList {k m : ℕ} (gates : List (LocalGate k m))
    (v : Fin (k + 1) → Fin (m + 1)) : Fin (k + 1) → Fin (m + 1) :=
  gates.foldl (fun v g => g.eval v) v

/-- A split procedure: a circuit of local gates on the `m`-string compressed
registers, followed by the read-out map into the pair of half-encodings. -/
structure SplitCircuit (m n k : ℕ) where
  gates : List (LocalGate k m)
  out : (Fin (k + 1) → Fin (m + 1)) →
    ((Fin (k + 1) → Fin (n + 1)) × (Fin (k + 1) → Fin (n + 1)))

/-! ## Lemma 5.1 (p. 15) -/

/-- **Lemma 5.1, arXiv:1211.4637v2, p. 15 (Eq. (25)).**  Let `m = 2n` with
`n > 0` and let `k` be the compression parameter.  Then there is a split
procedure `S` whose gate count is `O(k log m)` and which, on every `x` of
Hamming weight `≤ k`, maps the compressed encoding `C_m^k|x>` to the pair of
half-encodings `(C_n^k|x_1>, C_n^k|x_2>)`.  The statement is recorded as the
`Prop`-valued definition below; its proof is not formalised.

Proof route (paper, p. 15): both sides are computational basis states, and the
"split" is a reversible classical computation (prefix sums of the gap
registers, Eq. (19) of §4.4) on `O(k)` registers of size `O(log m)`, hence
`O(k log m)` local operations; coherence follows because the classical
procedure is reversible.

Lean gap: the reversible classical prefix-sum procedure is not implemented as
a concrete gate list, and `SplitCircuit.out` is a free field; the paper's
tensor-space bookkeeping is replaced by a pair of half-encodings.  Candidate
dependencies: `CompressedEncoding.cEnc`, `CompressedEncoding.gapList`,
`CompressedEncoding.gapList_entry_le`.  Suggested successor tactics: implement
the prefix-sum circuit explicitly (`List.range` over registers, each step a
`LocalGate.add`), prove `evalList` computes cumulative gaps by induction on the
register list, and bound `gates.length` by `k * Nat.log2 (m+1)` with
`Nat.log2`-arithmetic lemmas. -/
def lemma_5_1 (m n k : ℕ) (hm : m = 2 * n) (hn : 0 < n) : Prop :=
  ∃ (S : SplitCircuit m n k) (c : ℝ), 0 < c ∧
      (S.gates.length : ℝ) ≤ c * (k : ℝ) * Real.log m ∧
      ∀ (x : Fin m → Bool) (_hx : (gapList (word x)).length ≤ k),
        S.out (evalList S.gates (cEnc x)) =
          (cEnc (k := k) (halfLeft hm x), cEnc (k := k) (halfRight hm x))

end Qatlib.Papers.GateEffSim12.MainResults.SplitCircuit
