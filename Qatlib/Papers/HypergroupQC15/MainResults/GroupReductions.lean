/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypergroupQC15.MainResults.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# HypergroupQC15 — Theorem 1 and Theorem 2 (HNSP ≤ CC-HSHP)

Fixed source: arXiv:1509.05806, §3.2, p.10–11.

Theorem 1: a class-function HNSP oracle is constant on every product `C_g · N` of a
conjugacy class with the hidden normal subgroup `N`, takes distinct values on distinct
`N`-cosets, and therefore induces a well-defined hiding function on the conjugacy-class
hypergroup `Ḡ`.  Theorem 2: for a homomorphism oracle `f : G →* H`, the map
`x ↦ [f(x)]` (conjugacy class of the image) is a class function, because a homomorphism
sends conjugates to conjugates, and it is constant on `N`-cosets.

Both proofs are the paper's proofs: conjugation invariance plus `N`-invariance, and
`MonoidHom.map_isConj` respectively.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HypergroupQC15.MainResults

open scoped BigOperators

/-! ## Theorem 1 -/

/-- Theorem 1 (arXiv:1509.05806, Theorem 1, p.10–11).  Let `N ◁ G` and let `f : G → α`
be a class function hiding `N`.  Then `f` is constant on every set `C_g · N` and its
equality classes are exactly the `N`-cosets; consequently the lifted function on
conjugacy classes (`conjClassLift f`) is a well-defined hiding function for the
subhypergroup `N^G`, which is the CC-HSHP oracle built in the proof.

Proof (paper): `f(xn) = f((xn)^a) = f(x^a n^a) = f(x^a) = f(x)` for `x` in a class and
`n ∈ N`; distinctness on distinct cosets is the hiding property. -/
theorem theorem1_class_function_constancy {G : Type} [Group G] {α : Type}
    (N : Subgroup G) [N.Normal] (f : G → α)
    (hclass : IsClassFunction f) (hhide : Hides f N) :
    (∀ g c n : G, n ∈ N → f (c * g * c⁻¹ * n) = f g) ∧
    (∀ x y : G, f x = f y ↔ ∃ n : G, n ∈ N ∧ y = x * n) := by
  constructor
  · intro g c n hn
    have h1 : f (c * g * c⁻¹ * n) = f (c * g * c⁻¹) := by
      apply (hhide (c * g * c⁻¹ * n) (c * g * c⁻¹)).mpr
      have hmem : (c * g * c⁻¹ * n)⁻¹ * (c * g * c⁻¹) = n⁻¹ := by group
      rw [hmem]
      exact N.inv_mem hn
    rw [h1, hclass g c]
  · intro x y
    rw [hhide x y]
    constructor
    · intro h
      refine ⟨x⁻¹ * y, h, ?_⟩
      group
    · rintro ⟨n, hn, rfl⟩
      have : x⁻¹ * (x * n) = n := by group
      rw [this]
      exact hn

/-- Theorem 1, reduction form (arXiv:1509.05806, p.10–11): the identity oracle
translation `f ↦ conjClassLift f` is an efficient reduction from the class-function
HNSP to the CC-HSHP.  Its efficiency is the paper's assumption that one can compute
efficiently with conjugacy classes (encoded in the `transport` fields); no information
is lost because the two oracles carry the same labels. -/
theorem theorem1_hnsp_class_reduces_to_ccHshp (G α : Type) [Group G] [Fintype G]
    [DecidableEq G] [Fintype α] [DecidableEq α] :
    Nonempty (EfficientReduction (hnspClassProblem G α) (ccHshpProblem G α)) :=
  ⟨hnspClassToCc G α⟩

/-- Composition form of Theorem 1: efficient solvability of the CC-HSHP implies efficient
solvability of the class-function HNSP (arXiv:1509.05806, Corollary 2 relies on this). -/
theorem theorem1_hnsp_class_solvable_of_cc (G α : Type) [Group G] [Fintype G]
    [DecidableEq G] [Fintype α] [DecidableEq α]
    (hcc : HasEfficientQuantumAlgorithm (ccHshpProblem G α)) :
    HasEfficientQuantumAlgorithm (hnspClassProblem G α) :=
  (hnspClassToCc G α).preserves hcc

/-! ## Theorem 2 -/

/-- Theorem 2 (arXiv:1509.05806, Theorem 2, p.11).  Let `f : G →* H` be a homomorphism
whose hiding function hides the normal subgroup `N ◁ G`.  Then the map
`x ↦ [f(x)] ∈ ConjClasses H` is a class function on `G` and is constant on `N`-cosets;
this is exactly the oracle translation used to reduce the HNSP to the CC-HSHP
("the function `f̃` taking `x` to the conjugacy class label of `f(x)` is a class
function").  The induced map on `ConjClasses G` is exhibited in the last conjunct.

Proof (paper): `f(x^a) = f(a⁻¹ x a) = f(a)⁻¹ f(x) f(a)`, so `f` sends conjugates to
conjugates; `f(e) = e` gives that it hides the same subgroup. -/
theorem theorem2_homomorphism_class_translation {G H : Type} [Group G] [Group H]
    (f : G →* H) (N : Subgroup G) (hN : N.Normal) (hhide : Hides (f : G → H) N) :
    IsClassFunction (fun x : G => ConjClasses.map f (ConjClasses.mk x)) ∧
    (∀ x y : G, x⁻¹ * y ∈ N →
      ConjClasses.map f (ConjClasses.mk x) = ConjClasses.map f (ConjClasses.mk y)) ∧
    (∃ g : ConjClasses G → ConjClasses H,
      ∀ x : G, g (ConjClasses.mk x) = ConjClasses.map f (ConjClasses.mk x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g c
    have hconj : ConjClasses.mk (c * g * c⁻¹) = ConjClasses.mk g :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr (IsConj.symm (isConj_iff.mpr ⟨c, rfl⟩))
    show ConjClasses.map f (ConjClasses.mk (c * g * c⁻¹)) = ConjClasses.map f (ConjClasses.mk g)
    rw [hconj]
  · intro x y hxy
    have hf : f x = f y := (hhide x y).mpr hxy
    show ConjClasses.map f (ConjClasses.mk x) = ConjClasses.map f (ConjClasses.mk y)
    rw [show ConjClasses.map f (ConjClasses.mk x) = ConjClasses.mk (f x) from rfl,
        show ConjClasses.map f (ConjClasses.mk y) = ConjClasses.mk (f y) from rfl, hf]
  · exact ⟨ConjClasses.map f, fun x => rfl⟩

end Qatlib.Papers.HypergroupQC15.MainResults
