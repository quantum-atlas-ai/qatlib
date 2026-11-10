/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults

structure Encoding (G : Type*) where

  Code : Type*
  [fintypeCode : Fintype Code]

  decode : Code → Option G

attribute [instance] Encoding.fintypeCode

namespace Encoding

variable {G : Type*}

def Unique (E : Encoding G) : Prop :=
  ∀ g : G, ∃! c : E.Code, E.decode c = some g

def NonUnique (E : Encoding G) : Prop :=
  ¬ E.Unique

end Encoding

structure BlackBoxGroupData (G : Type*) [Group G] where

  encodingLength : ℕ

  generators : Finset G

  generates : Subgroup.closure (generators : Set G) = ⊤

  nu : ℕ

namespace BlackBoxGroupData

variable {G : Type*} [Group G]

def inputSize (B : BlackBoxGroupData G) : ℕ :=
  B.encodingLength * B.generators.card

noncomputable def groupOrder (B : BlackBoxGroupData G) : ℕ := Nat.card G

end BlackBoxGroupData

structure NuSpec (G : Type*) [Group G] (ν : ℕ) : Prop where

  pos : 1 ≤ ν

  solvable_eq_one : IsSolvable G → ν = 1

structure HiddenSubgroupInstance (G : Type*) [Group G] (X : Type*) where

  H : Subgroup G

  f : G → X

  hides : ∀ a b : G, f a = f b ↔ a⁻¹ * b ∈ H

namespace HiddenSubgroupInstance

variable {G : Type*} [Group G] {X : Type*}

theorem hides_one (I : HiddenSubgroupInstance G X) (a : G) :
    I.f a = I.f 1 ↔ a ∈ I.H := by
  simpa [mul_one, Subgroup.inv_mem_iff] using I.hides a 1

theorem mem_iff_f_eq_one (I : HiddenSubgroupInstance G X) (a : G) :
    a ∈ I.H ↔ I.f a = I.f 1 :=
  (I.hides_one a).symm

end HiddenSubgroupInstance

structure Oracles {G : Type*} [Group G] (B : BlackBoxGroupData G) where

  orderOracle : G → ℕ

  order_spec : ∀ g : G, orderOracle g = orderOf g

  elementaryMembership : ∀ (S : Finset G) (g : G), Bool

  elementaryMembership_spec :
    ∀ (S : Finset G) (g : G),
      (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) →
      (∃ p : ℕ, p.Prime ∧ ∀ a ∈ S, a ^ p = 1) →
      (elementaryMembership S g = true ↔ g ∈ Subgroup.closure (S : Set G))

namespace Oracles

variable {G : Type*} [Group G] {B : BlackBoxGroupData G}

theorem orderOracle_eq_orderOf (Ω : Oracles B) (g : G) :
    Ω.orderOracle g = orderOf g :=
  Ω.order_spec g

end Oracles

structure CostLedger where

  queries : ℕ

  groupOps : ℕ

  gates : ℕ

namespace CostLedger

def total (l : CostLedger) : ℕ :=
  max l.queries (max l.groupOps l.gates)

def zero : CostLedger := ⟨0, 0, 0⟩

@[simp] theorem total_zero : zero.total = 0 := by
  simp [zero, total]

end CostLedger

def PolyBounded {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (l : CostLedger) : Prop :=
  ∃ c k : ℕ, l.total ≤ c * (B.inputSize + B.nu + 1) ^ k

def PolyBoundedIn {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (p : ℕ) (l : CostLedger) : Prop :=
  ∃ c k : ℕ, l.total ≤ c * (B.inputSize + p + 1) ^ k

inductive Task where

  | membershipTest

  | orderAndPresentation

  | center

  | compositionSeries

  | sylow
  deriving DecidableEq, Repr

def NormalIn {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  (K.subgroupOf H).Normal

def IsSimpleFactor {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  K ≤ H ∧ NormalIn K H ∧ K ≠ H ∧
    ∀ M : Subgroup H, K.subgroupOf H ≤ M → M.Normal → M = ⊤ ∨ M = K.subgroupOf H

def HasCompositionSeries (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (C : ℕ → Subgroup G),
    C 0 = ⊤ ∧ C n = ⊥ ∧
    (∀ i < n, C (i + 1) < C i) ∧
    (∀ i < n, IsSimpleFactor (C (i + 1)) (C i))

def HasGeneratorWords {G : Type*} [Group G] (B : BlackBoxGroupData G) : Prop :=
  ∀ g : G, ∃ w : List (G × ℤ), (w.map (fun q => q.1 ^ q.2)).prod = g

def TaskFeasible {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) : Task → Prop
  | .membershipTest => HasGeneratorWords B
  | .orderAndPresentation =>
      ∃ (α : Type) (_ : Fintype α) (rel : Set (FreeGroup α)),
        Nonempty (PresentedGroup rel ≃* G)
  | .center => ∃ S : Finset G, Subgroup.closure (S : Set G) = Subgroup.center G
  | .compositionSeries => HasCompositionSeries G
  | .sylow => ∀ p : ℕ, p.Prime → Nonempty (Sylow p G)

structure TaskSolution {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) where

  task : Task

  cost : CostLedger

  poly : PolyBounded B cost

  feasible : TaskFeasible B Ω task

def PolySolvable {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) (t : Task) : Prop :=
  ∃ s : TaskSolution B Ω, s.task = t

def PolySolvableIn {G : Type*} [Group G] (B : BlackBoxGroupData G)
    (Ω : Oracles B) (p : ℕ) (t : Task) : Prop :=
  ∃ cost : CostLedger, PolyBoundedIn B p cost ∧ TaskFeasible B Ω t

structure HiddenSubgroupSolution {G : Type*} [Group G] {X : Type*}
    (B : BlackBoxGroupData G) (I : HiddenSubgroupInstance G X) where

  generators : Finset G

  generates : Subgroup.closure (generators : Set G) = I.H

  cost : CostLedger

def allTasks : List Task :=
  [.membershipTest, .orderAndPresentation, .center, .compositionSeries, .sylow]

noncomputable def quotientData {G : Type*} [Group G]
    (B : BlackBoxGroupData G) (N : Subgroup G) [N.Normal] (νq : ℕ)
    (gens : Finset (G ⧸ N))
    (hgens : Subgroup.closure (gens : Set (G ⧸ N)) = ⊤) :
    BlackBoxGroupData (G ⧸ N) where
  encodingLength := B.encodingLength
  generators := gens
  generates := hgens
  nu := νq

end Qatlib.Papers.NonAbelianHSP01.MainResults
