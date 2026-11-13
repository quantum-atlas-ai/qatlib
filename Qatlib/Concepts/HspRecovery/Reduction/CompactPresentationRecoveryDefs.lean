/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.FourierRecovery
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic

/-!
# Definitions for compact presentation recovery

`CompactPresentation` packages an encoded integer relation table and exposes its normalized
Smith data, invariant factors, and generator words. The gcd scans and divisibility predicates
describe coordinatewise annihilation without enumerating group elements.

`compactDecodeLedger` records label reads and gcd reductions, while `compactDecodeOriginal`
converts the coordinate output to a word in the original generators. The finite abelian group
setting is described in [KitaevShenVyalyi2002].

## Main statements

* `compactDecode`: computes a gcd quotient for each coordinate.
* `decodedSet` and `recordAnn`: express decoded divisibility and record annihilation.
* `compactDecodeLedger`: records the decoder's operations.
* `cyclicDecodedSet`: specializes the construction to a cyclic group.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical
open Qatlib.Concepts.IntWordFraming.WordFraming

/-- An encoded integer relation table together with its numbers of generators and relations. -/
structure CompactPresentation where

  generators : ℕ

  relations : ℕ

  table : Vector (Vector SmithIntegerCode relations) generators

namespace CompactPresentation

/-- The integer relation matrix decoded from a compact presentation's table. -/
def relationMatrix (p : CompactPresentation) :
    Matrix (Fin p.generators) (Fin p.relations) ℤ :=
  tableMatrix (smithDecodeRelations p.table)

/-- The normalized Smith data computed from a compact presentation's relation table. -/
def smith (p : CompactPresentation) : NormalizedSmithData p.generators p.relations :=
  normalizedSmith (smithDecodeRelations p.table)

/-- The Boolean finiteness test supplied by a compact presentation's normalized Smith data. -/
def isFinite (p : CompactPresentation) : Bool :=
  p.smith.isFinite

/-- The invariant factor list supplied by a compact presentation's normalized Smith data. -/
def factors (p : CompactPresentation) : List ℕ :=
  p.smith.factors

/-- The generator words supplied by a compact presentation's normalized Smith data. -/
def generatorWords (p : CompactPresentation) : List (Vector ℤ p.generators) :=
  p.smith.generatorWords

end CompactPresentation

/-- A natural number label for each generator coordinate of the Smith data. -/
abbrev FactorLabel {m n : ℕ} (_p : NormalizedSmithData m n) := Fin m → ℕ

/-- The iterated gcd of an initial natural number `d` with the elements of a list. -/
def gcdList (d : ℕ) : List ℕ → ℕ
  | [] => d
  | c :: cs => Nat.gcd (gcdList d cs) c

/-- A scan computing the gcd in coordinate `r` together with counts of label reads and gcd
reductions. -/
def labelGcdScan {m : ℕ} (r : Fin m) :
    List (Fin m → ℕ) → ℕ → ℕ × ℕ × ℕ
  | [], d => (d, 0, 0)
  | l :: L, d =>
      let res := labelGcdScan r L d
      (Nat.gcd res.1 (l r), res.2.1 + 1, res.2.2 + 1)

/-- The gcd of a Smith coefficient with the recorded labels in the same coordinate. -/
def labelGcd {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (r : Fin m) : ℕ :=
  (labelGcdScan r L (p.coeff r)).1

/-- The quotient of a Smith coefficient by the gcd of its recorded coordinate labels. -/
def annGenerator {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (r : Fin m) : ℕ :=
  p.coeff r / labelGcd p L r

/-- The vector of coordinate annihilator generators obtained by gcd division. -/
def compactDecode {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p)) :
    Fin m → ℕ :=
  fun r => annGenerator p L r

/-- The predicate that each coordinate of `x` is divisible by the corresponding computed
annihilator generator. -/
def decodedSet {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (x : Fin m → ℕ) : Prop :=
  ∀ r, annGenerator p L r ∣ x r

/-- The predicate that every recorded label annihilates `x` coordinatewise modulo the Smith
coefficients. -/
def recordAnn {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (x : Fin m → ℕ) : Prop :=
  ∀ l ∈ L, ∀ r, p.coeff r ∣ l r * x r

/-- Counts of label reads, gcd reductions, and group enumeration operations for decoding. -/
structure DecodeLedger where

  labelReads : ℕ

  gcdReductions : ℕ

  groupEnumeration : ℕ

/-- The compact decoder's operation ledger, summing the coordinate scans and recording zero
group enumeration. -/
def compactDecodeLedger {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : DecodeLedger where
  labelReads := ∑ r : Fin m, (labelGcdScan r L (p.coeff r)).2.1
  gcdReductions := ∑ r : Fin m, (labelGcdScan r L (p.coeff r)).2.2
  groupEnumeration := 0

/-- The compact decoder output reduced into the normalized modular coordinate type. -/
def compactDecodeNormalized {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : NormalizedCoordinates p :=
  fun r => ((compactDecode p L r.1 : ℕ) : ZMod (p.coeff r.1))

/-- The original-generator word obtained by decoding the compact normalized output. -/
def compactDecodeOriginal {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) : Fin m → ℤ :=
  normalizedDecode p (compactDecodeNormalized p L)

/-- The one-coordinate natural label given by a residue's natural representative. -/
def cyclicLabel {N : ℕ} (l : ZMod N) : Fin 1 → ℕ := fun _ => l.val

/-- The list of one-coordinate labels associated with a cyclic sample record. -/
def cyclicRecordLabels {N : ℕ} (xs : List (ZMod N)) : List (Fin 1 → ℕ) :=
  xs.map cyclicLabel

/-- The cyclic annihilator generator `N / gcdList N` of the sample representatives. -/
def cyclicAnnGenerator {N : ℕ} (xs : List (ZMod N)) : ℕ :=
  N / gcdList N (xs.map (fun l => l.val))

/-- The finite set of residues whose natural representatives are divisible by the cyclic
annihilator generator. -/
def cyclicDecodedSet {N : ℕ} (hN : 0 < N) (xs : List (ZMod N)) : Finset (ZMod N) :=
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  Finset.univ.filter (fun x => cyclicAnnGenerator xs ∣ x.val)

end Qatlib.Concepts.HspRecovery.ReductionCore
