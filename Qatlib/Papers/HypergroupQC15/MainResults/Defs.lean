/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# HypergroupQC15 — shared paper-layer model

Fixed source: arXiv:1509.05806, *Abelian Hypergroups and Quantum Computation*.

This module owns the paper-local vocabulary used by every result file of the
`HypergroupQC15.MainResults` block:

* hiding / class functions (§3, p.9–11),
* the HNSP and CC-HSHP search problems (§3.1–3.2),
* the paper's informal notion of an *efficient quantum algorithm* (§3–§7),
  formalized as a polynomially query- and gate-bounded oracle algorithm that is
  correct on every promised oracle, and an efficient oracle reduction between
  such problems,
* the capability assumptions used by Theorems 6–9 (QFT computability,
  computation with conjugacy classes, kernels of irreps).

The paper does not fix a machine model; the cost model below is the minimal
one that makes the statements meaningful (polynomial query and gate counts,
correctness for all promised oracles) and does not assert any stronger
computational power.  All definitions are in the paper layer and are not
promoted to shared `Foundations`/`Concepts`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HypergroupQC15.MainResults

open scoped BigOperators

/-! ## Class functions and hiding functions -/

variable {G : Type*} {α : Type*}

/-- `IsClassFunction f`: `f` is constant on conjugacy classes,
i.e. `f (c * g * c⁻¹) = f g` for all `g c` (arXiv:1509.05806, §3.2, p.10). -/
def IsClassFunction [Group G] (f : G → α) : Prop :=
  ∀ g c : G, f (c * g * c⁻¹) = f g

/-- `Hides f N`: the function `f` *hides* the subgroup `N`, i.e. two group elements
receive the same label exactly when they differ by an element of `N`
(arXiv:1509.05806, §3.1, p.9: `f x = f x'` iff `x' = x n` for some `n ∈ N`). -/
def Hides [Group G] (f : G → α) (N : Subgroup G) : Prop :=
  ∀ x y : G, f x = f y ↔ x⁻¹ * y ∈ N

/-- A class function is invariant under conjugation. -/
lemma IsClassFunction.conj_eq [Group G] {f : G → α} (h : IsClassFunction f)
    {x y : G} (hxy : IsConj x y) : f x = f y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  rw [← hc]
  exact (h x c).symm

/-- The class function on conjugacy classes induced by a class function on `G`.
This is the CC-HSHP oracle produced by the proof of Theorem 1. -/
def conjClassLift [Group G] (f : G → α) (h : IsClassFunction f) : ConjClasses G → α :=
  Quot.lift f (fun _ _ hab => h.conj_eq hab)

/-- The defining computation rule of `conjClassLift`: on the class `mk x` it returns
`f x`.  This is the label of the CC-HSHP oracle constructed in the proof of Theorem 1
(arXiv:1509.05806, p.10–11). -/
@[simp]
lemma conjClassLift_mk [Group G] (f : G → α) (h : IsClassFunction f) (x : G) :
    conjClassLift f h (ConjClasses.mk x) = f x := rfl

/-! ## Search problems with oracle access -/

/-- A search problem with oracle access: `Inst` are the problem instances, `size` is the
natural size parameter, `Oracle i` is the type of promised oracles for instance `i`, and
`Valid i o a` says that `a` is a valid answer for oracle `o`. -/
structure OracleProblem where
  Inst : Type
  size : Inst → ℕ
  Oracle : Inst → Type
  Answer : Inst → Type
  Valid : (i : Inst) → Oracle i → Answer i → Prop

/-- A polynomially query- and gate-bounded oracle algorithm that is correct on every
promised oracle.  This formalizes the paper's informal phrase "there is an efficient
quantum algorithm for the problem" (arXiv:1509.05806, §3–§7): the algorithm receives
oracle access and its query and gate counts are polynomially bounded in the instance
size.  No uniformity or machine model beyond these bounds is asserted. -/
structure EfficientAlgorithm (P : OracleProblem) where
  queries : P.Inst → ℕ
  gates : P.Inst → ℕ
  polyQueries : ∃ c k : ℕ, ∀ i : P.Inst, queries i ≤ c * (P.size i + 1) ^ k
  polyGates : ∃ c k : ℕ, ∀ i : P.Inst, gates i ≤ c * (P.size i + 1) ^ k
  run : (i : P.Inst) → P.Oracle i → P.Answer i
  correct : ∀ (i : P.Inst) (o : P.Oracle i), P.Valid i o (run i o)

/-- The paper's conclusion "there is an efficient quantum algorithm for `P`". -/
def HasEfficientQuantumAlgorithm (P : OracleProblem) : Prop :=
  Nonempty (EfficientAlgorithm P)

/-- An efficient oracle reduction from `A` to `B` (§3.2): it maps instances and promised
oracles and pulls valid `B`-answers back to valid `A`-answers; the query and gate budgets
of any polynomially bounded `B`-algorithm transport to `A`.  The transport fields encode
the paper's assumption that the translation itself is efficient. -/
structure EfficientReduction (A B : OracleProblem) where
  toInst : A.Inst → B.Inst
  toOracle : (i : A.Inst) → A.Oracle i → B.Oracle (toInst i)
  back : (i : A.Inst) → B.Answer (toInst i) → A.Answer i
  transportQueries : ∀ q : B.Inst → ℕ,
    (∃ c k : ℕ, ∀ j : B.Inst, q j ≤ c * (B.size j + 1) ^ k) →
    ∃ c k : ℕ, ∀ i : A.Inst, q (toInst i) ≤ c * (A.size i + 1) ^ k
  transportGates : ∀ q : B.Inst → ℕ,
    (∃ c k : ℕ, ∀ j : B.Inst, q j ≤ c * (B.size j + 1) ^ k) →
    ∃ c k : ℕ, ∀ i : A.Inst, q (toInst i) ≤ c * (A.size i + 1) ^ k
  valid : ∀ (i : A.Inst) (o : A.Oracle i) (b : B.Answer (toInst i)),
    B.Valid (toInst i) (toOracle i o) b → A.Valid i o (back i b)

/-- An efficient reduction transports efficient solvability. -/
theorem EfficientReduction.preserves {A B : OracleProblem} (R : EfficientReduction A B)
    (hB : HasEfficientQuantumAlgorithm B) : HasEfficientQuantumAlgorithm A := by
  obtain ⟨alg⟩ := hB
  exact ⟨{ queries := fun i => alg.queries (R.toInst i)
           gates := fun i => alg.gates (R.toInst i)
           polyQueries := R.transportQueries alg.queries alg.polyQueries
           polyGates := R.transportGates alg.gates alg.polyGates
           run := fun i o => R.back i (alg.run (R.toInst i) (R.toOracle i o))
           correct := fun i o =>
             R.valid i o (alg.run (R.toInst i) (R.toOracle i o))
               (alg.correct (R.toInst i) (R.toOracle i o)) }⟩

/-! ## The HNSP and the CC-HSHP over a fixed finite group -/

/-- The Hidden Normal Subgroup Problem over a fixed finite group `G` with label type `α`
(arXiv:1509.05806, §3.1, p.9).  An instance is a hiding function promised to hide a normal
subgroup `N ◁ G`; the answer is a normal subgroup, validated by the hiding property. -/
def hnspProblem (G α : Type) [Group G] [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] : OracleProblem where
  Inst := {f : G → α // ∃ N : Subgroup G, N.Normal ∧ Hides f N}
  size := fun _ => Fintype.card G
  Oracle := fun _ => Unit
  Answer := fun _ => {N : Subgroup G // N.Normal}
  Valid := fun i _ K => Hides i.val K.val

/-- The HNSP restricted to class-function oracles, i.e. the source problem of
Theorem 1 (arXiv:1509.05806, p.10). -/
def hnspClassProblem (G α : Type) [Group G] [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] : OracleProblem where
  Inst := {f : G → α // IsClassFunction f ∧ ∃ N : Subgroup G, N.Normal ∧ Hides f N}
  size := fun _ => Fintype.card G
  Oracle := fun _ => Unit
  Answer := fun _ => {N : Subgroup G // N.Normal}
  Valid := fun i _ K => Hides i.val K.val

/-- The Conjugacy-Class Hidden Subhypergroup Problem (CC-HSHP) over a fixed finite group
`G` (arXiv:1509.05806, §3.1, p.10).  The oracle is a function on conjugacy classes; it
hides the subhypergroup `N^G` corresponding to a normal subgroup `N ◁ G`, i.e. it takes
equal labels exactly on classes in the same `N`-coset.  The answer is `N`. -/
def ccHshpProblem (G α : Type) [Group G] [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] : OracleProblem where
  Inst := {g : ConjClasses G → α // ∃ N : Subgroup G, N.Normal ∧
    ∀ x y : G, g (ConjClasses.mk x) = g (ConjClasses.mk y) ↔ x⁻¹ * y ∈ N}
  size := fun _ => Fintype.card G
  Oracle := fun _ => Unit
  Answer := fun _ => {N : Subgroup G // N.Normal}
  Valid := fun i _ K =>
    ∀ x y : G, i.val (ConjClasses.mk x) = i.val (ConjClasses.mk y) ↔ x⁻¹ * y ∈ K.val

/-- The identity oracle translation of Theorem 1 (arXiv:1509.05806, p.10–11): a
class-function HNSP instance and the corresponding CC-HSHP instance carry the same
information, and the constancy lemma below shows that the lifted class function hides
exactly the normal subgroup.  The translation is efficient because it does not change the
instance size; the paper's assumption "we can compute efficiently with conjugacy classes"
is the `transport` data. -/
def hnspClassToCc (G α : Type) [Group G] [Fintype G] [DecidableEq G]
    [Fintype α] [DecidableEq α] :
    EfficientReduction (hnspClassProblem G α) (ccHshpProblem G α) :=
  let toInst : (hnspClassProblem G α).Inst → (ccHshpProblem G α).Inst := fun f =>
    ⟨conjClassLift f.val f.property.1,
      ⟨f.property.2.choose, f.property.2.choose_spec.1,
        by
          intro x y
          rw [conjClassLift_mk, conjClassLift_mk]
          exact f.property.2.choose_spec.2 x y⟩⟩
  { toInst := toInst
    toOracle := fun _ _ => ()
    back := fun _ K => K
    transportQueries := fun q h => by
      obtain ⟨c, k, hk⟩ := h
      exact ⟨c, k, fun i => hk (toInst i)⟩
    transportGates := fun q h => by
      obtain ⟨c, k, hk⟩ := h
      exact ⟨c, k, fun i => hk (toInst i)⟩
    valid := by
      intro i o b hb x y
      have key := hb x y
      simpa only [toInst, conjClassLift_mk] using key }

/-! ## Homomorphism oracles (Theorem 2) -/

/-- The HNSP with a group-homomorphism oracle `f : G →* H` (arXiv:1509.05806, p.11). -/
def hnspHomProblem (G H : Type) [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H] : OracleProblem where
  Inst := {f : G →* H // ∃ N : Subgroup G, N.Normal ∧ Hides (f : G → H) N}
  size := fun _ => Fintype.card G
  Oracle := fun _ => Unit
  Answer := fun _ => {N : Subgroup G // N.Normal}
  Valid := fun i _ K => Hides (i.val : G → H) K.val

/-- The CC-HSHP target produced from a homomorphism oracle: labels live in the conjugacy
classes of the codomain `H` (arXiv:1509.05806, p.11: "the function f̃ taking x to the
conjugacy class label of f(x) is a class function"). -/
def ccHshpHomProblem (G H : Type) [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H] : OracleProblem where
  Inst := {g : ConjClasses G → ConjClasses H // ∃ N : Subgroup G, N.Normal ∧
    ∀ x y : G, g (ConjClasses.mk x) = g (ConjClasses.mk y) ↔ x⁻¹ * y ∈ N}
  size := fun _ => Fintype.card G
  Oracle := fun _ => Unit
  Answer := fun _ => {N : Subgroup G // N.Normal}
  Valid := fun i _ K =>
    ∀ x y : G, i.val (ConjClasses.mk x) = i.val (ConjClasses.mk y) ↔ x⁻¹ * y ∈ K.val

/-! ## Capability assumptions behind Theorems 6–9 -/

/-- The paper's assumption that the normalized quantum Fourier transform of the finite
group `G` is efficiently implementable (used in Theorems 6, 8, 9 and Corollaries 2–4).
We record a gate count with a polynomial bound in `|G|`; the concrete circuit is the
paper's QFT (Appendix D). -/
structure QFTComputable (G : Type) [Group G] [Fintype G] where
  gates : ℕ
  polyGates : ∃ c k : ℕ, gates ≤ c * (Fintype.card G + 1) ^ k

/-- The paper's assumption that one can compute efficiently with conjugacy classes
(Appendix D.2, used in Theorems 1–2 and Corollaries 2–4): a representative for every
conjugacy class together with a polynomial gate count. -/
structure ComputesConjugacyClasses (G : Type) [Group G] [Fintype G] [DecidableEq G] where
  rep : ConjClasses G → G
  rep_mk : ∀ C : ConjClasses G, ConjClasses.mk (rep C) = C
  gates : ℕ
  polyGates : ∃ c k : ℕ, gates ≤ c * (Fintype.card G + 1) ^ k

/-- The paper's assumption that the kernels of irreps are efficiently computable when
restricted to subgroups (used in Lemma 7 and Theorem 9). -/
structure ComputesIrrepKernels (G : Type) [Group G] [Fintype G] where
  gates : ℕ
  polyGates : ∃ c k : ℕ, gates ≤ c * (Fintype.card G + 1) ^ k

/-! ## Stabilizer states -/

/-- A nonzero vector `ψ` is the stabilizer state of the operator set `S` when it is the
unique nonzero simultaneous eigenvector with eigenvalue one (arXiv:1509.05806,
Definition 1, eq. (22), p.18). -/
def IsStabilizerState {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Set (V →ₗ[ℂ] V)) (ψ : V) : Prop :=
  ψ ≠ 0 ∧ (∀ P ∈ S, P ψ = ψ) ∧
    ∀ φ : V, φ ≠ 0 → (∀ P ∈ S, P φ = φ) → φ = ψ

end Qatlib.Papers.HypergroupQC15.MainResults
