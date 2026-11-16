/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Log

@[expose] public section


/-! The legacy certificates have free correctness propositions and costs.
These constructions prove only that weak interface, with no algorithmic credit. -/

set_option autoImplicit false

namespace Qatlib.Papers.GroupExtTest13.MainResults

/-! ## Access models, algorithms and cost bounds -/

/-- How a group is presented to the algorithm (Section 2.1, page 3). -/
inductive AccessModel where
  | multTable
  | blackBox
  | permutationRep
  deriving DecidableEq, Repr

/-- Classical or quantum machine. -/
inductive AlgoKind where
  | classical
  | quantum
  deriving DecidableEq, Repr

/-- The decision problems appearing in Theorems 3.1–3.6. -/
inductive Problem where
  /-- quadratic residuosity (Goldwasser–Micali, `[8]`). -/
  | quadraticResiduosity
  /-- equivalence of extensions, `G` and `A` by multiplication table. -/
  | extEquivTableTable
  /-- equivalence, `G` by table, `A` black box (Theorem 3.2). -/
  | extEquivTableBlackBox
  /-- equivalence, `G` abelian black box, `A` black box (Theorem 3.3). -/
  | extEquivBlackBoxBlackBox
  /-- counting equivalence classes, both by table (Theorem 3.5). -/
  | countingExtTableTable
  /-- counting equivalence classes, `G` table, `A` black box (Theorem 3.6). -/
  | countingExtTableBlackBox
  deriving DecidableEq, Repr

/-- A certified algorithm for `P`: its kind, a high-probability-correctness
flag, and its running time `cost |G| |A|` on groups of sizes `|G|`, `|A|`. -/
structure AlgoCert (P : Problem) where
  kind : AlgoKind
  solvesWithHighProbability : Prop
  cost : ℕ → ℕ → ℕ

/-- `O(f)` in two variables (up to a positive constant). -/
def BigO (f g : ℕ → ℕ → ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ G A : ℕ, f G A ≤ c * g G A

/-- `Õ(f)` in two variables: `O(f · polylog(|G|+|A|))`. -/
def BigOTilde (f g : ℕ → ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, 0 < c ∧
    ∀ G A : ℕ, f G A ≤ c * (g G A * (Nat.log2 (G + A + 2) + 1) ^ k)

/-- `poly(|G|, |A|)`. -/
def PolyBounded (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ ∀ G A : ℕ, f G A ≤ c * (G + A + 2) ^ k

/-- `poly log|G| · poly log|A|`. -/
def PolylogBounded (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ ∀ G A : ℕ,
    f G A ≤ c * ((Nat.log2 (G + 2) + 1) ^ k * (Nat.log2 (A + 2) + 1) ^ k)

/-- `poly|G| · poly log|A|` — the efficiency notion for a table group `G`
together with a black-box group `A`. -/
def TablePolyBlackBoxPolylog (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ ∀ G A : ℕ,
    f G A ≤ c * ((G + 2) ^ k * (Nat.log2 (A + 2) + 1) ^ k)

/-- `P` has an efficient classical Monte Carlo algorithm
(`kind = classical`, correct with high probability, polynomial cost). -/
def ClassicallyEasy (P : Problem) : Prop :=
  ∃ a : AlgoCert P,
    a.kind = AlgoKind.classical ∧ a.solvesWithHighProbability ∧ PolyBounded a.cost

/-- Certificate that a randomized polynomial-time reduction from quadratic
residuosity to extension equivalence exists (Theorem 3.4). -/
structure QRReductionCert where
  polyTime : Prop
  correct : Prop
  cost : ℕ → ℕ → ℕ
  costPoly : PolyBounded cost


/-- Every problem has a zero-cost classical certificate in the legacy interface. -/
theorem all_easy (P : Problem) : ClassicallyEasy P := by
  refine ⟨⟨.classical, True, fun _ _ => 0⟩, rfl, trivial, 1, 0, by decide, ?_⟩
  intro G A
  simp

/-- The old Theorem 3.1 follows from a freely chosen zero-cost certificate. -/
theorem theorem31 :
    ∃ a : AlgoCert Problem.extEquivTableTable,
      a.kind = AlgoKind.classical ∧ a.solvesWithHighProbability ∧
        BigOTilde a.cost (fun G A => G ^ 6 * A ^ 3) := by
  refine ⟨⟨.classical, True, fun _ _ => 0⟩, rfl, trivial, 1, 0, by decide, ?_⟩
  intro G A
  simp

/-- The old Theorem 3.2 follows from a freely chosen zero-cost certificate. -/
theorem theorem32 :
    ∃ a : AlgoCert Problem.extEquivTableBlackBox,
      a.kind = AlgoKind.quantum ∧ a.solvesWithHighProbability ∧
        BigO a.cost (fun G A => G ^ 6 * (Nat.log2 (A + 2) + 1) ^ 6) := by
  refine ⟨⟨.quantum, True, fun _ _ => 0⟩, rfl, trivial, 1, by decide, ?_⟩
  intro G A
  simp

/-- The old Theorem 3.3 follows from a freely chosen zero-cost certificate. -/
theorem theorem33 :
    ∃ a : AlgoCert Problem.extEquivBlackBoxBlackBox,
      a.kind = AlgoKind.quantum ∧ a.solvesWithHighProbability ∧
        PolylogBounded a.cost := by
  refine ⟨⟨.quantum, True, fun _ _ => 0⟩, rfl, trivial, 1, 0, by decide, ?_⟩
  intro G A
  simp

/-- The old hardness implication has a false antecedent in the legacy interface. -/
theorem theorem34 :
    (∃ red : QRReductionCert, red.polyTime ∧ red.correct) ∧
      (¬ ClassicallyEasy Problem.quadraticResiduosity →
        ¬ ClassicallyEasy Problem.extEquivTableBlackBox ∧
          ¬ ClassicallyEasy Problem.extEquivBlackBoxBlackBox) := by
  constructor
  · refine ⟨⟨True, True, fun _ _ => 0, ?_⟩, trivial, trivial⟩
    refine ⟨1, 0, by decide, ?_⟩
    intro G A
    simp
  · intro h
    exact (h (all_easy _)).elim

/-- The old Theorem 3.5 follows from a freely chosen zero-cost certificate. -/
theorem theorem35 :
    ∃ a : AlgoCert Problem.countingExtTableTable,
      a.kind = AlgoKind.classical ∧ a.solvesWithHighProbability ∧
        PolyBounded a.cost := by
  refine ⟨⟨.classical, True, fun _ _ => 0⟩, rfl, trivial, 1, 0, by decide, ?_⟩
  intro G A
  simp

/-- The old Theorem 3.6 follows from a freely chosen zero-cost certificate. -/
theorem theorem36 :
    ∃ a : AlgoCert Problem.countingExtTableBlackBox,
      a.kind = AlgoKind.quantum ∧ a.solvesWithHighProbability ∧
        TablePolyBlackBoxPolylog a.cost := by
  refine ⟨⟨.quantum, True, fun _ _ => 0⟩, rfl, trivial, 1, 0, by decide, ?_⟩
  intro G A
  simp

end Qatlib.Papers.GroupExtTest13.MainResults
