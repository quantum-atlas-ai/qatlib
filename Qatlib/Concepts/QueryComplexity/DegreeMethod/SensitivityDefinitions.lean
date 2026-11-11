/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Lattice
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

/-!
# Sensitivity and certificate complexity

This module defines block flips, local and global block sensitivity, certificate size,
and deterministic query complexity for Boolean functions on finitely many bits.
These are the combinatorial measures used alongside polynomial degree in [BealsEtAl2001].

`IsCertificateFor` expresses that fixing a coordinate set determines the function value.
Minimum certificate sizes and query complexities are expressed by infima of natural-number sets.

## Main statements

* `blockSensitivityAt`: the largest disjoint sensitive-block family at an input.
* `certificateComplexity`: the maximum minimum certificate size over all inputs.
* `deterministicQueryComplexity`: the least maximum query count of a correct Boolean tree.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option autoImplicit false

open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib
open scoped Classical

/-- Flip exactly the Boolean coordinates belonging to a specified finite block. -/
def flipBlock {N : ℕ} (x : Fin N → Bool) (B : Finset (Fin N)) : Fin N → Bool :=
  fun i => if i ∈ B then !(x i) else x i

/-- A block is sensitive at `x` when flipping it changes the value of `f`. -/
def BlockSensitive {N : ℕ} (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (B : Finset (Fin N)) : Prop :=
  f x ≠ f (flipBlock x B)

/-- The maximum cardinality of a pairwise disjoint family of sensitive blocks at the input `x`. -/
noncomputable def blockSensitivityAt {N : ℕ} (f : (Fin N → Bool) → Bool)
    (x : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun 𝔅 : Finset (Finset (Fin N)) =>
      (∀ B ∈ 𝔅, BlockSensitive f x B) ∧
        ∀ B₁ ∈ 𝔅, ∀ B₂ ∈ 𝔅, B₁ ≠ B₂ → B₁ ∩ B₂ = ∅).sup Finset.card

/-- The maximum block sensitivity over all Boolean inputs. -/
noncomputable def blockSensitivity {N : ℕ} (f : (Fin N → Bool) → Bool) : ℕ :=
  (Finset.univ.image fun x : Fin N → Bool => blockSensitivityAt f x).sup id

/-- A coordinate set certifies `f` at `x` when every input agreeing with `x` there has the same
function value. -/
def IsCertificateFor {N : ℕ} (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (S : Finset (Fin N)) : Prop :=
  ∀ y : Fin N → Bool, (∀ i ∈ S, y i = x i) → f y = f x

/-- The infimum of the cardinalities of coordinate sets certifying `f` at `x`. -/
noncomputable def certificateSizeAt {N : ℕ} (f : (Fin N → Bool) → Bool)
    (x : Fin N → Bool) : ℕ :=
  sInf ((Finset.univ.filter fun S : Finset (Fin N) => IsCertificateFor f x S).image
    Finset.card : Set ℕ)

/-- The maximum minimum certificate size over all Boolean inputs. -/
noncomputable def certificateComplexity {N : ℕ} (f : (Fin N → Bool) → Bool) : ℕ :=
  (Finset.univ.image fun x : Fin N → Bool => certificateSizeAt f x).sup id

/-- The maximum minimum certificate size among inputs on which `f` is true, with value zero if
there are none. -/
noncomputable def oneCertificateComplexity {N : ℕ} (f : (Fin N → Bool) → Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin N → Bool => f x = true).image
    (certificateSizeAt f) |>.sup id

/-- The infimum of maximum query counts among Boolean query trees that compute `f` correctly on
every input. -/
noncomputable def deterministicQueryComplexity {N : ℕ}
    (f : (Fin N → Bool) → Bool) : ℕ :=
  sInf (Set.range fun t : {t : BoolQueryTree (Fin N) Bool //
      ∀ x : Fin N → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) t).1 = f x} =>
    t.1.MaxQueries)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
