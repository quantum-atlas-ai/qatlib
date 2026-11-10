/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.FourierRecovery
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical
open Qatlib.Concepts.IntWordFraming.WordFraming

structure CompactPresentation where

  generators : ℕ

  relations : ℕ

  table : Vector (Vector SmithIntegerCode relations) generators

namespace CompactPresentation

def relationMatrix (p : CompactPresentation) :
    Matrix (Fin p.generators) (Fin p.relations) ℤ :=
  tableMatrix (smithDecodeRelations p.table)

def smith (p : CompactPresentation) : NormalizedSmithData p.generators p.relations :=
  normalizedSmith (smithDecodeRelations p.table)

def isFinite (p : CompactPresentation) : Bool :=
  p.smith.isFinite

def factors (p : CompactPresentation) : List ℕ :=
  p.smith.factors

def generatorWords (p : CompactPresentation) : List (Vector ℤ p.generators) :=
  p.smith.generatorWords

end CompactPresentation

abbrev FactorLabel {m n : ℕ} (p : NormalizedSmithData m n) := Fin m → ℕ

def gcdList (d : ℕ) : List ℕ → ℕ
  | [] => d
  | c :: cs => Nat.gcd (gcdList d cs) c

def labelGcdScan {m : ℕ} (r : Fin m) :
    List (Fin m → ℕ) → ℕ → ℕ × ℕ × ℕ
  | [], d => (d, 0, 0)
  | l :: L, d =>
      let res := labelGcdScan r L d
      (Nat.gcd res.1 (l r), res.2.1 + 1, res.2.2 + 1)

def labelGcd {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (r : Fin m) : ℕ :=
  (labelGcdScan r L (p.coeff r)).1

def annGenerator {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (r : Fin m) : ℕ :=
  p.coeff r / labelGcd p L r

def compactDecode {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p)) :
    Fin m → ℕ :=
  fun r => annGenerator p L r

def decodedSet {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (x : Fin m → ℕ) : Prop :=
  ∀ r, annGenerator p L r ∣ x r

def recordAnn {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (x : Fin m → ℕ) : Prop :=
  ∀ l ∈ L, ∀ r, p.coeff r ∣ l r * x r

structure DecodeLedger where

  labelReads : ℕ

  gcdReductions : ℕ

  groupEnumeration : ℕ

def compactDecodeLedger {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : DecodeLedger where
  labelReads := ∑ r : Fin m, (labelGcdScan r L (p.coeff r)).2.1
  gcdReductions := ∑ r : Fin m, (labelGcdScan r L (p.coeff r)).2.2
  groupEnumeration := 0

def compactDecodeNormalized {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : NormalizedCoordinates p :=
  fun r => ((compactDecode p L r.1 : ℕ) : ZMod (p.coeff r.1))

def compactDecodeOriginal {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : Fin m → ℤ :=
  normalizedDecode p (compactDecodeNormalized p L)

def cyclicLabel {N : ℕ} (l : ZMod N) : Fin 1 → ℕ := fun _ => l.val

def cyclicRecordLabels {N : ℕ} (xs : List (ZMod N)) : List (Fin 1 → ℕ) :=
  xs.map cyclicLabel

def cyclicAnnGenerator {N : ℕ} (xs : List (ZMod N)) : ℕ :=
  N / gcdList N (xs.map (fun l => l.val))

def cyclicDecodedSet {N : ℕ} (hN : 0 < N) (xs : List (ZMod N)) : Finset (ZMod N) :=
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  Finset.univ.filter (fun x => cyclicAnnGenerator xs ∣ x.val)

end Qatlib.Concepts.HspRecovery.ReductionCore
