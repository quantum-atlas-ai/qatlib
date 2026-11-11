/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Recursive NAND certificates

This module defines binary NAND formulas `NNode`, their evaluation `NNode.eval`, and the indexed
certificate family `Cert` for a fixed Boolean input. These recursive certificates encode the
branch choices underlying the certificate structure discussed in [Ambainis2007].

## Main statements

* `Cert.eval_eq` proves that a certificate gives the indicated evaluation.
* `Cert.nonempty` constructs a certificate for either evaluation value.
* `lemma1_structure` decomposes a false certificate at an internal node into true certificates
  for both children.
* `lemma1_branch_exclusive` expresses a true certificate at an internal node through a false
  certificate for one chosen child.

## References

* [Ambainis, 2007][Ambainis2007]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NANDAmbainis07.MainResults

/-- Binary NAND formulas with naturally indexed input leaves and a two-child NAND node
constructor. -/
inductive NNode where
  | leaf : ℕ → NNode
  | node : NNode → NNode → NNode
  deriving DecidableEq, Repr

/-- Evaluates a binary NAND formula on a Boolean input assignment by reading its leaves and
applying NAND at each internal node. -/
def NNode.eval (x : ℕ → Bool) : NNode → Bool
  | NNode.leaf i => x i
  | NNode.node l r => !(NNode.eval x l && NNode.eval x r)

/-- Evaluation of an input leaf returns the assigned Boolean value at its index. -/
@[simp] lemma NNode.eval_leaf (x : ℕ → Bool) (i : ℕ) : (NNode.leaf i).eval x = x i := rfl

/-- Evaluation of an internal node is the NAND of its two children's evaluations. -/
@[simp] lemma NNode.eval_node (x : ℕ → Bool) (l r : NNode) :
    (NNode.node l r).eval x = !(l.eval x && r.eval x) := rfl

/-- Recursive certificates for the value of a NAND formula under a fixed input. A false
internal-node certificate contains true certificates for both children, while a true one
chooses a false certificate for one child. -/
inductive Cert (x : ℕ → Bool) : NNode → Bool → Type
  | leafT {i : ℕ} (h : x i = true) : Cert x (NNode.leaf i) true
  | leafF {i : ℕ} (h : x i = false) : Cert x (NNode.leaf i) false
  | nodeF {l r : NNode} (cl : Cert x l true) (cr : Cert x r true) :
      Cert x (NNode.node l r) false
  | nodeTl {l r : NNode} (c : Cert x l false) : Cert x (NNode.node l r) true
  | nodeTr {l r : NNode} (c : Cert x r false) : Cert x (NNode.node l r) true

/-- A certificate for Boolean value `b` ensures that the formula evaluates to `b` on the fixed
input. -/
theorem Cert.eval_eq {x : ℕ → Bool} : {e : NNode} → {b : Bool} → Cert x e b → e.eval x = b
  | _, _, Cert.leafT h => by simpa using h
  | _, _, Cert.leafF h => by simpa using h
  | _, _, Cert.nodeF cl cr => by
      rw [NNode.eval_node, Cert.eval_eq cl, Cert.eval_eq cr]
      rfl
  | _, _, Cert.nodeTl c => by
      rw [NNode.eval_node, Cert.eval_eq c]
      rfl
  | _, _, Cert.nodeTr c => by
      rw [NNode.eval_node, Cert.eval_eq c]
      simp

/-- Every formula has a certificate for its actual evaluation, with separate implications for
the false and true cases. -/
theorem Cert.nonempty {x : ℕ → Bool} : ∀ (e : NNode),
    (e.eval x = false → Nonempty (Cert x e false)) ∧
    (e.eval x = true → Nonempty (Cert x e true))
  | NNode.leaf i => by
      refine ⟨?_, ?_⟩
      · intro h
        exact ⟨Cert.leafF (by simpa using h)⟩
      · intro h
        exact ⟨Cert.leafT (by simpa using h)⟩
  | NNode.node l r => by
      obtain ⟨ihlF, ihlT⟩ := Cert.nonempty l
      obtain ⟨ihrF, ihrT⟩ := Cert.nonempty r
      refine ⟨?_, ?_⟩
      · intro h
        rw [NNode.eval_node] at h
        have h1 : l.eval x = true := by
          cases hl : l.eval x <;> cases hr : r.eval x <;> simp_all
        have h2 : r.eval x = true := by
          cases hl : l.eval x <;> cases hr : r.eval x <;> simp_all
        exact ⟨Cert.nodeF (ihlT h1).some (ihrT h2).some⟩
      · intro h
        rw [NNode.eval_node] at h
        by_cases hl : l.eval x = false
        · exact ⟨Cert.nodeTl (ihlF hl).some⟩
        · have hlt : l.eval x = true := by
            cases hv : l.eval x <;> simp_all
          have hr : r.eval x = false := by
            cases hv : r.eval x <;> simp_all
          exact ⟨Cert.nodeTr (ihrF hr).some⟩

/-- A false certificate for an internal node is a `Cert.nodeF` certificate built from true
certificates for both children. This is the false-node decomposition corresponding to
[Ambainis, Lemma 1][Ambainis2007]. -/
theorem lemma1_structure {x : ℕ → Bool} {z₁ z₂ : NNode}
    (cw : Cert x (NNode.node z₁ z₂) false) :
    ∃ (cl : Cert x z₁ true) (cr : Cert x z₂ true), cw = Cert.nodeF cl cr := by
  cases cw with
  | nodeF cl cr => exact ⟨cl, cr, rfl⟩

/-- A true certificate for an internal node is constructed from a false certificate for either
the left child or the right child, using the corresponding constructor. -/
theorem lemma1_branch_exclusive {x : ℕ → Bool} {y₁ y₂ : NNode}
    (cl : Cert x (NNode.node y₁ y₂) true) :
    (∃ ca : Cert x y₁ false, cl = Cert.nodeTl ca) ∨
    (∃ cb : Cert x y₂ false, cl = Cert.nodeTr cb) := by
  cases cl with
  | nodeTl ca => exact Or.inl ⟨ca, rfl⟩
  | nodeTr cb => exact Or.inr ⟨cb, rfl⟩

end Qatlib.Papers.NANDAmbainis07.MainResults
