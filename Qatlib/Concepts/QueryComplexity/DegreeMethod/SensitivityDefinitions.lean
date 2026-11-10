/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Lattice
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery

set_option autoImplicit false

open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib
open scoped Classical

def flipBlock {N : ℕ} (x : Fin N → Bool) (B : Finset (Fin N)) : Fin N → Bool :=
  fun i => if i ∈ B then !(x i) else x i

def BlockSensitive {N : ℕ} (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (B : Finset (Fin N)) : Prop :=
  f x ≠ f (flipBlock x B)

noncomputable def blockSensitivityAt {N : ℕ} (f : (Fin N → Bool) → Bool)
    (x : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun 𝔅 : Finset (Finset (Fin N)) =>
      (∀ B ∈ 𝔅, BlockSensitive f x B) ∧
        ∀ B₁ ∈ 𝔅, ∀ B₂ ∈ 𝔅, B₁ ≠ B₂ → B₁ ∩ B₂ = ∅).sup Finset.card

noncomputable def blockSensitivity {N : ℕ} (f : (Fin N → Bool) → Bool) : ℕ :=
  (Finset.univ.image fun x : Fin N → Bool => blockSensitivityAt f x).sup id

def IsCertificateFor {N : ℕ} (f : (Fin N → Bool) → Bool) (x : Fin N → Bool)
    (S : Finset (Fin N)) : Prop :=
  ∀ y : Fin N → Bool, (∀ i ∈ S, y i = x i) → f y = f x

noncomputable def certificateSizeAt {N : ℕ} (f : (Fin N → Bool) → Bool)
    (x : Fin N → Bool) : ℕ :=
  sInf ((Finset.univ.filter fun S : Finset (Fin N) => IsCertificateFor f x S).image
    Finset.card : Set ℕ)

noncomputable def certificateComplexity {N : ℕ} (f : (Fin N → Bool) → Bool) : ℕ :=
  (Finset.univ.image fun x : Fin N → Bool => certificateSizeAt f x).sup id

noncomputable def oneCertificateComplexity {N : ℕ} (f : (Fin N → Bool) → Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin N → Bool => f x = true).image
    (certificateSizeAt f) |>.sup id

noncomputable def deterministicQueryComplexity {N : ℕ}
    (f : (Fin N → Bool) → Bool) : ℕ :=
  sInf (Set.range fun t : {t : BoolQueryTree (Fin N) Bool //
      ∀ x : Fin N → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun i => x i) t).1 = f x} =>
    t.1.MaxQueries)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
