/-
Copyright (c) 2026 qatlas-lean-lib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.GaussBosonic24.MomentPropagate.SourceModel
public import Qatlib.Papers.GaussBosonic24.GateUniversal.GateModel

@[expose] public section


set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Papers.GaussBosonic24.GateUniversal

open Qatlib.Papers.GaussBosonic24.MomentPropagate

/-- The number of modes for `n` register qubits: `M = 2^n` (Definition 1). -/
abbrev Modes (n : ℕ) : ℕ := 2 ^ n

/-- The first mode (the paper's mode `m = 1`, read out by Problem 1). -/
def firstMode (n : ℕ) : Fin (Modes n) := ⟨0, by simp [Modes]⟩

/-- The `l`-th bit of a mode index (the mode's binary expansion, register-style). -/
def modeBit (n : ℕ) (l : Fin n) (m : Fin (Modes n)) : Bool := (bitVecEquiv n).symm m l

/-- Flip the `l`-th bit of a mode index: the mode paired with `m` by a global
beamsplitter acting on bit `l`. -/
def flipBit (n : ℕ) (l : Fin n) (m : Fin (Modes n)) : Fin (Modes n) :=
  bitVecEquiv n (Function.update ((bitVecEquiv n).symm m) l (!((bitVecEquiv n).symm m l)))

/-- The mode-space matrix unit `|m⟩⟨m'|` on `M` modes. -/
def modeBasis {M : ℕ} (m m' : Fin M) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => if i = m ∧ j = m' then 1 else 0

/-- The phase-space generator of a single beamsplitter between modes `m` and
`m'`, Eq. (B6) of Appendix B (written on the split `Fin M ⊕ Fin M` of
positions and momenta):
`K = 2(|m'⟩⟨m| + |m⟩⟨m'| − |m+M⟩⟨m'| − |m'⟩⟨m+M|)` in the paper's
`2M`-dimensional phase space, i.e. `K = [[0, 2(|m⟩⟨m'| − |m'⟩⟨m|)],
[−2(|m⟩⟨m'| − |m'⟩⟨m|), 0]]` after collecting the quadrature blocks.  This `K`
is real and symmetric, as required of a Gaussian generator (Eq. (A9)). -/
def bsK {M : ℕ} (m m' : Fin M) : Matrix (Fin M ⊕ Fin M) (Fin M ⊕ Fin M) ℂ :=
  fromBlocks 0 (2 • (modeBasis m m' - modeBasis m' m))
    (-(2 • (modeBasis m m' - modeBasis m' m))) 0

/-- A **global beamsplitter** of Definition 1 and Eq. (B23)–(B24): specified by
two mode numbers `k` (the control bit) and `l` (the target bit), `k ≠ l`, plus
the rotation parameter `t` of the physical gate `CTRL(|0⟩⟨0|_k) Ry(4t)_l`
(Eq. (B24)).  Definition 1 names only `k, l`; the angle is part of the gate
instance, as in Eq. (B24). -/
structure GlobalBeamsplitter (n : ℕ) where
  /-- The control bit `k`. -/
  k : Fin n
  /-- The target bit `l`. -/
  l : Fin n
  /-- The paper's requirement `l ≠ k`. -/
  hkl : k ≠ l
  /-- The rotation parameter `t` (the gate is `CTRL(|0⟩⟨0|_k) Ry(4t)_l`). -/
  t : ℝ

/-- The phase-space generator of a global beamsplitter: the sum of the pair
generators `bsK` of Eq. (B6) over one representative `m` of each paired orbit
`m ↔ m ⊕ 2^l`, restricted to modes whose `k`-th bit is `0` (the beamsplitter
acts on the `|0⟩⟨0|` control branch, Eq. (B24)). -/
def globalK {n : ℕ} (g : GlobalBeamsplitter n) :
    Matrix (Fin (Modes n) ⊕ Fin (Modes n)) (Fin (Modes n) ⊕ Fin (Modes n)) ℂ :=
  Finset.sum (Finset.univ.filter fun m : Fin (Modes n) =>
      modeBit n g.k m = false ∧ modeBit n g.l m = false)
    (fun m => bsK m (flipBit n g.l m))

/-- A **bit-structured interferometer** on `2^n` modes (Definition 1): an
ordered list of `L` global beamsplitters. -/
abbrev BitStructuredInterferometer (n : ℕ) := List (GlobalBeamsplitter n)

/-- Phase-space action of an interferometer: the ordered product of the
propagators `e^{t Ω K}` of its global beamsplitters (Eq. (2) with `Ω` of
Eq. (A7)).  The leftmost gate is applied first. -/
def interferometerAction {n : ℕ} : BitStructuredInterferometer n →
    Matrix (Fin (Modes n) ⊕ Fin (Modes n)) (Fin (Modes n) ⊕ Fin (Modes n)) ℂ
  | [] => 1
  | g :: gs => interferometerAction gs *
      NormedSpace.exp ((g.t : ℂ) • (omega (Modes n) * globalK g))

/-- Initial mean vector of Problem 1: the first mode is displaced by `x` in
position, all other means vanish (the encoding Eq. (3) with `⟨q̂₁⟩ = x` and
`⟨p̂₁⟩ = 0`; "the first mode is displaced by `x`", Problem 1). -/
def initialMean {n : ℕ} (x : ℝ) : Fin (Modes n) ⊕ Fin (Modes n) → ℂ :=
  fun i => match i with
    | Sum.inl m => if m = firstMode n then (x : ℂ) else 0
    | Sum.inr _ => 0

/-- The output mean position `⟨q̂₁⟩` of the first mode after the interferometer:
the position component of the evolved mean vector. -/
def outputPosition {n : ℕ} (gates : BitStructuredInterferometer n) (x : ℝ) : ℝ :=
  ((interferometerAction gates).mulVec (initialMean x) (Sum.inl (firstMode n))).re

/-- The empty interferometer acts as the identity. -/
@[simp] theorem interferometerAction_nil {n : ℕ} :
    interferometerAction ([] : BitStructuredInterferometer n) = 1 := rfl

/-- **Definition 1, trivial instance.**  The empty bit-structured interferometer
leaves the first mode's mean position unchanged: `⟨q̂₁⟩ = x`. -/
@[simp] theorem outputPosition_nil {n : ℕ} (x : ℝ) :
    outputPosition ([] : BitStructuredInterferometer n) x = x := by
  simp [outputPosition, initialMean, Matrix.one_mulVec]

/-- An instance of **Problem 1**: a bit-structured interferometer on `2^n`
modes together with the displacement `x > 0` of the first mode.  (The paper's
`L ∈ O(poly(n))` bound on the number of gates is `gates.length`, and the
construction is uniform in `n`.) -/
structure Problem1Instance (n : ℕ) where
  /-- The interferometer's gate list. -/
  gates : BitStructuredInterferometer n
  /-- The displacement `x > 0` of the first mode. -/
  x : ℝ
  /-- Positivity of the displacement. -/
  hx : 0 < x

/-- **Problem 1, YES case**: `⟨q̂₁⟩ > 2x/3` (printed p. 14). -/
def Problem1Yes {n : ℕ} (inst : Problem1Instance n) : Prop :=
  2 * inst.x / 3 < outputPosition inst.gates inst.x

/-- **Problem 1, NO case**: `⟨q̂₁⟩ < x/3` (printed p. 14). -/
def Problem1No {n : ℕ} (inst : Problem1Instance n) : Prop :=
  outputPosition inst.gates inst.x < inst.x / 3

/-- The **promise** of Problem 1: one of the two cases holds (they are
mutually exclusive, see `problem1_promise_exclusive`). -/
def Problem1Promise {n : ℕ} (inst : Problem1Instance n) : Prop :=
  Problem1Yes inst ∨ Problem1No inst

/-- The two cases of Problem 1 are disjoint. -/
theorem problem1_promise_exclusive {n : ℕ} {inst : Problem1Instance n} :
    ¬ (Problem1Yes inst ∧ Problem1No inst) := by
  rintro ⟨h1, h2⟩
  unfold Problem1Yes at h1
  unfold Problem1No at h2
  nlinarith [inst.hx]

/-- The YES case implies the promise. -/
theorem problem1_yes_imp_promise {n : ℕ} {inst : Problem1Instance n}
    (h : Problem1Yes inst) : Problem1Promise inst := Or.inl h

/-- The NO case implies the promise. -/
theorem problem1_no_imp_promise {n : ℕ} {inst : Problem1Instance n}
    (h : Problem1No inst) : Problem1Promise inst := Or.inr h

/-- **Problem 1 on the empty interferometer** is in the YES case: `⟨q̂₁⟩ = x >
2x/3`, matching the paper's reading `⟨q̂₁⟩/x = 1` (Fig. 3 caption). -/
theorem problem1_yes_nil {n : ℕ} (x : ℝ) (hx : 0 < x) :
    Problem1Yes (⟨[], x, hx⟩ : Problem1Instance n) := by
  unfold Problem1Yes
  rw [outputPosition_nil]
  nlinarith

/-- An instance of **Problem 2**: a word of gates from the universal set
`S = {Rz, Ry, CRy}` (Lemma 2) on `n` qubits — the paper's uniform family of
circuits with `J ∈ O(poly(n))` gates, applied to `|0⟩^{⊗n}` (printed p. 14). -/
structure Problem2Instance (n : ℕ) where
  /-- The circuit's gate word. -/
  gs : List (L2Gate n)

/-- The **overlap with `|0⟩^{⊗n}`** of Problem 2: the squared modulus of the
all-zero amplitude `⟨0…0| U |0…0⟩`, i.e. the probability of the all-zero
outcome.  This is the quantity that equals `⟨q̂₁⟩ / x` under the dictionary
(Fig. 3 caption, printed p. 15). -/
def Problem2Overlap {n : ℕ} (inst : Problem2Instance n) : ℝ :=
  ‖(ApplyGate (l2WordMatrix inst.gs) (Ket (ZeroStr n))) (ZeroStr n)‖ ^ 2

/-- **Problem 2, YES case**: the overlap with `|0⟩^{⊗n}` exceeds `2/3`
(printed p. 14). -/
def Problem2Yes {n : ℕ} (inst : Problem2Instance n) : Prop :=
  2 / 3 < Problem2Overlap inst

/-- **Problem 2, NO case**: the overlap with `|0⟩^{⊗n}` is below `1/3`. -/
def Problem2No {n : ℕ} (inst : Problem2Instance n) : Prop :=
  Problem2Overlap inst < 1 / 3

/-- The two cases of Problem 2 are disjoint. -/
theorem problem2_promise_exclusive {n : ℕ} {inst : Problem2Instance n} :
    ¬ (Problem2Yes inst ∧ Problem2No inst) := by
  rintro ⟨h1, h2⟩
  unfold Problem2Yes at h1
  unfold Problem2No at h2
  linarith

/-- The empty circuit has overlap `1` with `|0⟩^{⊗n}`. -/
@[simp] theorem problem2Overlap_nil {n : ℕ} :
    Problem2Overlap (⟨[]⟩ : Problem2Instance n) = 1 := by
  simp [Problem2Overlap, l2WordMatrix]

/-- **Problem 2 on the empty circuit** is in the YES case: overlap `1 > 2/3`. -/
theorem problem2_yes_nil {n : ℕ} : Problem2Yes (⟨[]⟩ : Problem2Instance n) := by
  unfold Problem2Yes
  rw [problem2Overlap_nil]
  norm_num

/-- The empty circuit is not in the NO case. -/
theorem problem2_no_nil_false {n : ℕ} : ¬ Problem2No (⟨[]⟩ : Problem2Instance n) := by
  unfold Problem2No
  rw [problem2Overlap_nil]
  norm_num

/-- **BQP-completeness of Problem 1** as stated in Theorem 1: containment plus
hardness, uniformly in the number `n` of register qubits. -/
def Problem1BQPComplete : Prop :=
  (∀ n : ℕ, ∀ inst : Problem1Instance n, Problem1Promise inst →
    ∃ gs : List (L2Gate n),
      (Problem1Yes inst ↔ Problem2Yes (⟨gs⟩ : Problem2Instance n)) ∧
      (Problem1No inst ↔ Problem2No (⟨gs⟩ : Problem2Instance n))) ∧
  (∀ n : ℕ, ∀ inst : Problem2Instance n, (Problem2Yes inst ∨ Problem2No inst) →
    ∃ i1 : Problem1Instance n,
      Problem1Promise i1 ∧
      (Problem2Yes inst ↔ Problem1Yes i1) ∧
      (Problem2No inst ↔ Problem1No i1))

end Qatlib.Papers.GaussBosonic24.GateUniversal
