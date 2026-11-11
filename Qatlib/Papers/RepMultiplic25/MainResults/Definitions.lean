/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RepMultiplic25 — shared combinatorial vocabulary

Panova, *Polynomial time classical versus quantum algorithms for representation
theoretic multiplicities* (arXiv:2502.20253v2, 18 Oct 2025). Fixed version: v2.

This file records the elementary objects used throughout the paper layer:

* integer partitions (`Partition`), their size, length, first part, `aft` (the
  `aft(λ)` of the paper, p.6: `aft(λ) := n − max{λ₁, ℓ(λ)}`) and Durfee size
  `d(λ)`;
* the hook length of a cell and the hook-length-formula value `f^λ` (HLF, p.4);
* a light-weight cost interface `CostedAlg` / `ComputesWithin` /
  `ComputesInBigO` used to phrase the paper's `O(·)` runtime statements.

Nothing here is specific to one theorem; the per-theorem statements live in the
sibling files `Section3*.lean` … `Section6*.lean`.
-/

namespace Qatlib.Papers.RepMultiplic25.MainResults

set_option autoImplicit false

/-! ## Partitions -/

/-- An integer partition of `n`, stored as the list of its nonzero parts in
weakly decreasing order. `parts` is the sequence `(λ₁, λ₂, …, λ_ℓ)`. -/
structure Partition where
  /-- The nonzero parts, in weakly decreasing order. -/
  parts : List ℕ
  /-- Every part is positive. -/
  pos : ∀ x ∈ parts, 0 < x
  /-- The parts are weakly decreasing (`λ_{i+1} ≤ λ_i`). -/
  antitone : parts.Pairwise (fun a b => b ≤ a)

namespace Partition

/-- `|λ| = n`, the size of the partition. -/
def size (L : Partition) : ℕ := L.parts.sum

/-- `ℓ(λ)`, the number of nonzero parts. -/
def length (L : Partition) : ℕ := L.parts.length

/-- `λ₁`, the first (largest) part; `0` for the empty partition. -/
def firstPart (L : Partition) : ℕ := L.parts.headD 0

/-- `aft(λ) := n − max{λ₁, ℓ(λ)}` (paper p.6). -/
def aft (L : Partition) : ℕ := L.size - max L.firstPart L.length

/-- The number of rows whose length is `> j`, i.e. the `(j+1)`-st column length
`λ'_{j+1}` in zero-based indexing. -/
def colLength (L : Partition) (j : ℕ) : ℕ := (L.parts.filter (fun x => j < x)).length

/-- The Durfee size `d(λ)` (paper p.6), the side of the largest square that fits
inside `λ`. -/
def durfee (L : Partition) : ℕ :=
  ((List.range L.length).filter (fun i => i < L.parts.getD i 0)).length

/-- The cells `(i,j)` (zero-based) of the Young diagram of `λ`. -/
def cells (L : Partition) : List (ℕ × ℕ) :=
  (List.range L.length).flatMap fun i =>
    (List.range (L.parts.getD i 0)).map fun j => (i, j)

/-- Hook length of the cell `(i,j)` (zero-based), `h = λ_{i+1} − i + λ'_{j+1} − j − 1`
(paper p.4, one-based `h_u = λ_i − i + λ'_j − j + 1`). -/
def hook (L : Partition) (i j : ℕ) : ℕ :=
  L.parts.getD i 0 - i + L.colLength j - j - 1

/-- Product of the hook lengths over all cells, the denominator in the
hook-length formula. -/
def hookProduct (L : Partition) : ℕ :=
  (L.cells.map fun p => L.hook p.1 p.2).prod

/-- The dimension `f^λ = n! / ∏ h_u` of the Specht module `S_λ`, computed by the
hook-length formula (HLF, paper p.4). -/
def dimensionNat (L : Partition) : ℕ := Nat.factorial L.size / L.hookProduct

/-- `f^λ` as a real number, for the asymptotic inequalities of Section 3. -/
noncomputable def dimension (L : Partition) : ℝ := (L.dimensionNat : ℝ)

/-- The size of a literal partition is the sum of its parts. -/
@[simp] theorem size_mk (parts : List ℕ) (h₁ h₂) :
    (Partition.mk parts h₁ h₂).size = parts.sum := rfl

/-- The length of a literal partition is the number of its parts. -/
@[simp] theorem length_mk (parts : List ℕ) (h₁ h₂) :
    (Partition.mk parts h₁ h₂).length = parts.length := rfl

/-- The first part of a literal partition is the head of the part list. -/
@[simp] theorem firstPart_mk (parts : List ℕ) (h₁ h₂) :
    (Partition.mk parts h₁ h₂).firstPart = parts.headD 0 := rfl

/-- `aft(λ) = n − max{λ₁, ℓ(λ)}` (definitional unfolding). -/
theorem aft_eq (L : Partition) :
    L.aft = L.size - max L.firstPart L.length := rfl

/-- `aft` never exceeds the size `n`. -/
theorem aft_le_size (L : Partition) : L.aft ≤ L.size := Nat.sub_le _ _

/-- The maximum of the first part and the length is at most the size. -/
theorem max_first_length_le_size (L : Partition) : max L.firstPart L.length ≤ L.size := by
  have h1 : L.firstPart ≤ L.size := by
    unfold firstPart size
    cases h : L.parts with
    | nil => simp
    | cons a t =>
      have : a ≤ a + t.sum := Nat.le_add_right _ _
      simpa [List.headD_cons, List.sum_cons] using this
  have h2 : L.length ≤ L.size := by
    have hb : ∀ x ∈ L.parts, 1 ≤ x := fun x hx => L.pos x hx
    have := List.length_le_sum_of_one_le L.parts hb
    simpa [size, length] using this
  exact max_le h1 h2

/-- `aft(λ) = k` is equivalent to `n = max{λ₁, ℓ(λ)} + k`. -/
theorem aft_eq_iff (L : Partition) (k : ℕ) :
    L.aft = k ↔ L.size = max L.firstPart L.length + k := by
  unfold aft
  have hle := L.max_first_length_le_size
  omega

end Partition

/-! ## Cost interface for the paper's `O(·)` statements

The paper phrases its results as "the quantity can be computed in time `O(g)`".
We record an algorithm together with its intrinsic step count: a `CostedAlg` is
an algorithm in the RAM model whose `run` map is the function it computes and
whose `cost` is its number of elementary steps on each input. Two different
`cost` functions on the same `run` are genuinely different algorithms, so the
existence statements below quantify over algorithms-with-runtime. -/

/-- A classical deterministic algorithm: an output map together with its step
count. -/
structure CostedAlg (I O : Type*) where
  /-- The value produced on each input. -/
  run : I → O
  /-- Number of elementary steps taken on each input. -/
  cost : I → ℕ

namespace CostedAlg

/-- Sequential composition; the step counts add. -/
def seq {I O P : Type*} (A : CostedAlg I O) (B : CostedAlg O P) : CostedAlg I P where
  run := fun i => B.run (A.run i)
  cost := fun i => A.cost i + B.cost (A.run i)

/-- Sequencing runs the second algorithm on the output of the first. -/
@[simp] theorem seq_run {I O P : Type*} (A : CostedAlg I O) (B : CostedAlg O P) (i : I) :
    (A.seq B).run i = B.run (A.run i) := rfl

/-- Sequencing adds the costs of both stages. -/
@[simp] theorem seq_cost {I O P : Type*} (A : CostedAlg I O) (B : CostedAlg O P) (i : I) :
    (A.seq B).cost i = A.cost i + B.cost (A.run i) := rfl

end CostedAlg

/-- `ComputesWithin target bound`: there is an algorithm computing `target` whose
step count is pointwise at most `bound`. -/
def ComputesWithin {I O : Type*} (target : I → O) (bound : I → ℕ) : Prop :=
  ∃ A : CostedAlg I O, (∀ i, A.run i = target i) ∧ ∀ i, A.cost i ≤ bound i

/-- `ComputesInBigO target g`: there is an algorithm computing `target` whose
step count is `O(g)`, i.e. bounded by `C · g` for some positive integer `C`
(paper §2.4: "runs in time `O(f(n))`"). -/
def ComputesInBigO {I O : Type*} (target : I → O) (g : I → ℕ) : Prop :=
  ∃ A : CostedAlg I O, (∀ i, A.run i = target i) ∧
    ∃ C : ℕ, 0 < C ∧ ∀ i, A.cost i ≤ C * g i

/-- `ComputesWithin` yields `ComputesInBigO` with the same bound (constant `1`). -/
theorem computesWithin_to_bigO {I O : Type*} {target : I → O} {bound : I → ℕ}
    (h : ComputesWithin target bound) : ComputesInBigO target bound := by
  obtain ⟨A, hrun, hcost⟩ := h
  exact ⟨A, hrun, 1, Nat.one_pos, fun i => by simpa using hcost i⟩

/-- Pointwise `O`-monotonicity of `ComputesInBigO`: if `g₁ = O(g₂)` pointwise and
`target` is computable in time `O(g₁)`, then it is computable in time `O(g₂)`. -/
theorem computesInBigO_mono {I O : Type*} {target : I → O} {g₁ g₂ : I → ℕ}
    (h : ComputesInBigO target g₁)
    (hmono : ∃ C : ℕ, 0 < C ∧ ∀ i, g₁ i ≤ C * g₂ i) :
    ComputesInBigO target g₂ := by
  obtain ⟨A, hrun, C₁, hC₁, hbound⟩ := h
  obtain ⟨C₂, hC₂, hg⟩ := hmono
  refine ⟨A, hrun, C₂ * C₁, Nat.mul_pos hC₂ hC₁, ?_⟩
  intro i
  calc A.cost i ≤ C₁ * g₁ i := hbound i
    _ ≤ C₁ * (C₂ * g₂ i) := Nat.mul_le_mul_left C₁ (hg i)
    _ = C₂ * C₁ * g₂ i := by ring

end Qatlib.Papers.RepMultiplic25.MainResults
