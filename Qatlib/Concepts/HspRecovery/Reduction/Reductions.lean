/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralCosetRecord
import Mathlib.Data.Sym.Sym2

/-!
# Hidden-shift and reflection oracle constructions

This module defines hidden-shift, hidden-reflection, and Simon-type collision promises over an
additive commutative group. It supplies tagged and unordered-pair oracle constructions for the
reductions discussed in [Kuperberg2005], together with the power-of-two embeddings used for
parity descent.

## Main definitions

* `HiddenShift`: injective functions related by translation.
* `AbelianReflectionHides`: the two-element collision relation on a tagged register.
* `shiftToReflectionOracle`: an unordered-pair oracle built from two functions.
* `parityRestrictedOracle` and `parityLift`: restriction and reconstruction for a chosen parity.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- The tagged register `A × Bool` for an abelian dihedral construction. -/
abbrev AbelianDihedralReg (A : Type*) := A × Bool

/-- The map that sends `(a, false)` to `(a + s, true)` and `(a, true)` to `(a - s, false)`. -/
def abelianReflect {A : Type*} [AddCommGroup A] (s : A) :
    AbelianDihedralReg A → AbelianDihedralReg A
  | (a, false) => (a + s, true)
  | (a, true) => (a - s, false)

/-- The promise that two oracle values agree exactly when their tagged inputs coincide or are
related by `abelianReflect s`. -/
def AbelianReflectionHides {A S : Type*} [AddCommGroup A]
    (h : AbelianDihedralReg A → S) (s : A) : Prop :=
  ∀ p q, h p = h q ↔ q = p ∨ q = abelianReflect s p

/-- The hidden-shift promise that `f` and `g` are injective and `f a = g (a + s)` for every `a`. -/
def HiddenShift {A S : Type*} [AddCommGroup A] (f g : A → S) (s : A) : Prop :=
  Function.Injective f ∧ Function.Injective g ∧ ∀ a, f a = g (a + s)

/-- The tagged oracle that uses `f` on the false sector and `g` on the true sector. -/
def shiftToDihedralOracle {A S : Type*} (f g : A → S) :
    AbelianDihedralReg A → S
  | (a, false) => f a
  | (a, true) => g a

/-- The promise that `h a = h b` holds exactly when `b = a` or `b = s - a`. -/
def AbelianReflection {A S : Type*} [AddCommGroup A] (h : A → S) (s : A) : Prop :=
  ∀ a b, h a = h b ↔ b = a ∨ b = s - a

/-- The oracle returning the unordered pair of values `f (-a)` and `g a`. -/
def shiftToReflectionOracle {A S : Type*} [AddCommGroup A]
    (f g : A → S) (a : A) : Sym2 S := s(f (-a), g a)

/-- The left oracle in the reflection-to-shift construction, returning `(h (-a), h (v - a))`. -/
def reflectionToShiftLeft {A S : Type*} [AddCommGroup A]
    (h : A → S) (v a : A) : S × S := (h (-a), h (v - a))

/-- The right oracle in the reflection-to-shift construction, returning `(h a, h (a - v))`. -/
def reflectionToShiftRight {A S : Type*} [AddCommGroup A]
    (h : A → S) (v a : A) : S × S := (h a, h (a - v))

/-- The collision promise that `h a = h b` holds exactly when `b = a` or `b = a + s`. -/
def SimonShiftPromise {A S : Type*} [AddCommGroup A] (h : A → S) (s : A) : Prop :=
  ∀ a b, h a = h b ↔ b = a ∨ b = a + s

/-- The power-of-two dihedral embedding that doubles the residue coordinate and adds the chosen
parity bit only in the true sector. -/
def paritySubgroupEmbedding (n : ℕ) (b : Bool) :
    Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ n) →
      Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ (n + 1))
  | (a, false) => (2 * (a.val : ZMod (2 ^ (n + 1))), false)
  | (a, true) => (2 * (a.val : ZMod (2 ^ (n + 1))) + if b then 1 else 0, true)

/-- The oracle obtained by precomposing `f` with the embedding for parity `b`. -/
def parityRestrictedOracle (n : ℕ) {S : Type*}
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ (n + 1)) → S) (b : Bool) :
      Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ n) → S :=
  f ∘ paritySubgroupEmbedding n b

/-- The lifted slope `2 * t.val + b` modulo `2 ^ (n + 1)`, interpreting the Boolean `b` as zero
or one. -/
def parityLift (n : ℕ) (b : Bool) (t : ZMod (2 ^ n)) : ZMod (2 ^ (n + 1)) :=
  2 * (t.val : ZMod (2 ^ (n + 1))) + if b then 1 else 0

end Qatlib.Concepts.HspRecovery.ReductionCore
