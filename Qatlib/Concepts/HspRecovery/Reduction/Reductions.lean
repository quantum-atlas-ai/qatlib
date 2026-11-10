/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.DihedralCosetRecord
import Mathlib.Data.Sym.Sym2
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

abbrev AbelianDihedralReg (A : Type*) := A × Bool

def abelianReflect {A : Type*} [AddCommGroup A] (s : A) :
    AbelianDihedralReg A → AbelianDihedralReg A
  | (a, false) => (a + s, true)
  | (a, true) => (a - s, false)

def AbelianReflectionHides {A S : Type*} [AddCommGroup A]
    (h : AbelianDihedralReg A → S) (s : A) : Prop :=
  ∀ p q, h p = h q ↔ q = p ∨ q = abelianReflect s p

def HiddenShift {A S : Type*} [AddCommGroup A] (f g : A → S) (s : A) : Prop :=
  Function.Injective f ∧ Function.Injective g ∧ ∀ a, f a = g (a + s)

def shiftToDihedralOracle {A S : Type*} (f g : A → S) :
    AbelianDihedralReg A → S
  | (a, false) => f a
  | (a, true) => g a

def AbelianReflection {A S : Type*} [AddCommGroup A] (h : A → S) (s : A) : Prop :=
  ∀ a b, h a = h b ↔ b = a ∨ b = s - a

def shiftToReflectionOracle {A S : Type*} [AddCommGroup A]
    (f g : A → S) (a : A) : Sym2 S := s(f (-a), g a)

def reflectionToShiftLeft {A S : Type*} [AddCommGroup A]
    (h : A → S) (v a : A) : S × S := (h (-a), h (v - a))

def reflectionToShiftRight {A S : Type*} [AddCommGroup A]
    (h : A → S) (v a : A) : S × S := (h a, h (a - v))

def SimonShiftPromise {A S : Type*} [AddCommGroup A] (h : A → S) (s : A) : Prop :=
  ∀ a b, h a = h b ↔ b = a ∨ b = a + s

def paritySubgroupEmbedding (n : ℕ) (b : Bool) :
    Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ n) →
      Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ (n + 1))
  | (a, false) => (2 * (a.val : ZMod (2 ^ (n + 1))), false)
  | (a, true) => (2 * (a.val : ZMod (2 ^ (n + 1))) + if b then 1 else 0, true)

def parityRestrictedOracle (n : ℕ) {S : Type*}
    (f : Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ (n + 1)) → S) (b : Bool) :
      Qatlib.Concepts.HspRecovery.RecordExtract.DihedralReg (2 ^ n) → S :=
  f ∘ paritySubgroupEmbedding n b

def parityLift (n : ℕ) (b : Bool) (t : ZMod (2 ^ n)) : ZMod (2 ^ (n + 1)) :=
  2 * (t.val : ZMod (2 ^ (n + 1))) + if b then 1 else 0

end Qatlib.Concepts.HspRecovery.ReductionCore
