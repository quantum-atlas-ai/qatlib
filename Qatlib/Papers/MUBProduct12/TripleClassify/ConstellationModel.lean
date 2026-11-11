/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — the product constellation `{5,5,4}⊗₆`

Model for the `{5,5,4}` product constellation of McNulty–Weigert,
fixed arXiv:1203.6887v2, Sec. 3, pp. 7–8:

> the constellation `{5,5,4}⊗₆` consists of two product bases (five orthonormal rays in
> `C⁶` determine a unique sixth state, so it is not listed in this notation), and a set `S`
> of four orthogonal product states.

`Constellation554` records the two five-state product families `A`, `B`, the four
orthogonal product states `S`, and all the mutual-unbiasedness conditions between them.
`ContainsConstellationInTriple` / `ContainsConstellationInSet` record that the constellation
sits inside a MU triple / inside a complete set of seven MU bases.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

/-- The product constellation `{5,5,4}⊗₆` (arXiv:1203.6887v2, Sec. 3, p. 8): two product
bases of five rays each (`finA`, `finB`) plus four mutually orthogonal product states
(`four`), pairwise MU across the three parts. -/
structure Constellation554 where
  /-- The five listed rays of the first product basis. -/
  finA : Fin 5 → QState (Fin 2 × Fin 3)
  /-- The five listed rays of the second product basis. -/
  finB : Fin 5 → QState (Fin 2 × Fin 3)
  /-- The four orthogonal product states. -/
  four : Fin 4 → QState (Fin 2 × Fin 3)
  /-- The rays of the first part are product states. -/
  finA_prod : ∀ i, IsProductState (finA i)
  /-- The rays of the second part are product states. -/
  finB_prod : ∀ i, IsProductState (finB i)
  /-- The four states are product states. -/
  four_prod : ∀ i, IsProductState (four i)
  /-- The five rays of the first part are orthonormal. -/
  finA_orth : ∀ i j, Inner (finA i) (finA j) = if i = j then 1 else 0
  /-- The five rays of the second part are orthonormal. -/
  finB_orth : ∀ i j, Inner (finB i) (finB j) = if i = j then 1 else 0
  /-- The four states are orthonormal. -/
  four_orth : ∀ i j, Inner (four i) (four j) = if i = j then 1 else 0
  /-- The two five-ray parts are MU to each other. -/
  finAB_mu : ∀ i j, Complex.normSq (Inner (finA i) (finB j)) = 1 / 6
  /-- The first part is MU to the four states. -/
  finA_four_mu : ∀ i k, Complex.normSq (Inner (finA i) (four k)) = 1 / 6
  /-- The second part is MU to the four states. -/
  finB_four_mu : ∀ i k, Complex.normSq (Inner (finB i) (four k)) = 1 / 6

/-- The constellation is contained in a MU triple `T`: its first part lies in `T 0`, its
second part in `T 1`, and its four states in `T 2`. -/
def ContainsConstellationInTriple
    (T : Fin 3 → Fin 6 → QState (Fin 2 × Fin 3)) (C : Constellation554) : Prop :=
  (∃ embA : Fin 5 ↪ Fin 6, ∀ i, T 0 (embA i) = C.finA i) ∧
  (∃ embB : Fin 5 ↪ Fin 6, ∀ i, T 1 (embB i) = C.finB i) ∧
  (∃ embS : Fin 4 ↪ Fin 6, ∀ i, T 2 (embS i) = C.four i)

/-- A complete set of seven MU bases of `C² ⊗ C³`. -/
def IsCompleteMuSet (M : Fin 7 → Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  (∀ r, OrthonormalFamily (M r)) ∧
  ∀ r s, r ≠ s → ∀ i j, Complex.normSq (Inner (M r i) (M s j)) = 1 / 6

/-- The constellation is contained in a complete set of seven MU bases: its two five-ray
parts and its four states lie in three distinct bases of the set. -/
def ContainsConstellationInSet
    (M : Fin 7 → Fin 6 → QState (Fin 2 × Fin 3)) (C : Constellation554) : Prop :=
  ∃ rA rB rS : Fin 7, rA ≠ rB ∧ rA ≠ rS ∧ rB ≠ rS ∧
    (∃ embA : Fin 5 ↪ Fin 6, ∀ i, M rA (embA i) = C.finA i) ∧
    (∃ embB : Fin 5 ↪ Fin 6, ∀ i, M rB (embB i) = C.finB i) ∧
    (∃ embS : Fin 4 ↪ Fin 6, ∀ i, M rS (embS i) = C.four i)

end Qatlib.Papers.MUBProduct12.TripleClassify.ConstellationModel
