/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Lemma 3: classification of MU product pairs in `C² ⊗ C³`

McNulty–Weigert, fixed arXiv:1203.6887v2, Lemma 3, p. 8, Eq. (29):

> Any pair of MU product bases in `C² ⊗ C³` is equivalent to a member of the families
> `P0 = {|j_z,J_z⟩; |j_x,J_x⟩}`,
> `P1 = {|j_z,J_z⟩; |0_x,J_x⟩, |1_x, R̂_{ξ,η}J_x⟩}`,
> `P2 = {|0_z,J_z⟩,|1_z,J_y⟩; |0_x,J_x⟩,|1_x,J_w⟩}`,
> `P3 = {|0_z,J_z⟩,|1_z,Ŝ_{ζ,χ}J_z⟩; |j_x,0_x⟩,|r̂_σ j_x,1_x⟩,|r̂_τ j_x,2_x⟩}`,
> where `R̂_{ξ,η}` is a diagonal phase operator and `Ŝ`, `r̂_σ`, `r̂_τ` are analogous.

The four `Shape*` predicates below capture the four structural types:
* `ShapeP0` — both bases are direct product bases;
* `ShapeP1` — direct first basis, indirect second basis whose two qutrit sectors differ by a
  diagonal (unit-phase) unitary `R` applied to `{|J_x⟩}`;
* `ShapeP2` — both bases indirect, each splitting into two qutrit bases that are MU to each
  other (the `{|J_z⟩}`/`{|J_y⟩}` and `{|J_x⟩}`/`{|J_w⟩}` pairs);
* `ShapeP3` — indirect first basis with a diagonal `Ŝ` rotation, and second basis whose
  qubit basis `{|j_x⟩}, {|r̂_J j_x⟩}` varies with the qutrit label `J`.

The theorem states the paper's conclusion: every MU product pair is equivalent
(`ProductEquivPair`) to a representative of one of the four shapes.

**Status.**  The statement is registered as a `Prop`-valued definition; the proof is not
formalised.  The classification is imported from [19] (exhaustive search);
the paper does not reprove it.  The `Shape*` predicates here encode the structural families
at the level of the paper's notation (parameters `ξ,η,ζ,χ,σ,τ` are existentially quantified
through the matrices `R`, `S` and the per-`J` qubit bases), but the concrete `F₃, H_y, H_w`
tables and the equivalence-reduction are not formalised.  Candidate reuse: the qutrit
Hadamard tables in `Mub6Maximum.ThreeBasis.MUBProductBases`
(`H`, `K`).  Suggested route: build the concrete `C²⊗C³` qutrit bases with `Complex.exp`
roots of unity, enumerate pairs with `fin_cases`, and close the equivalence by Gram
computations.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Lemma3PairClassification

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

/-- Orthonormal qubit family. -/
def IsOnQubit (a : Fin 2 → C2State) : Prop :=
  ∀ i j, Inner (a i) (a j) = if i = j then 1 else 0

/-- Orthonormal qutrit family. -/
def IsOnQutrit (f : Fin 3 → C3State) : Prop :=
  ∀ J K, Inner (f J) (f K) = if J = K then 1 else 0

/-- Two qutrit bases are mutually unbiased (all cross overlaps of modulus squared `1/3`). -/
def IsMuQutritPair (f g : Fin 3 → C3State) : Prop :=
  ∀ J K, Complex.normSq (Inner (f J) (g K)) = 1 / 3

/-- `R` is a diagonal unitary with unit phase entries (the paper's `R̂_{ξ,η}`,
`Ŝ_{ζ,χ}`). -/
def IsPhaseDiagonal (R : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  R ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
  ∃ d : Fin 3 → ℂ, (∀ J, ‖d J‖ = 1) ∧ R = Matrix.diagonal d

/-- Shape `P0`: both bases are direct product bases. -/
def ShapeP0 (A B : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  IsDirectProductBasis A ∧ IsDirectProductBasis B

/-- Shape `P1`: direct first basis; indirect second basis whose `|0_x⟩`-sector uses a
qutrit basis `f` and whose `|1_x⟩`-sector uses the diagonal-phase rotation `R f`. -/
def ShapeP1 (A B : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  IsDirectProductBasis A ∧
  ∃ (a : Fin 2 → C2State) (f : Fin 3 → C3State) (R : Matrix (Fin 3) (Fin 3) ℂ)
    (e : Fin 6 ≃ Fin 2 × Fin 3),
    IsOnQubit a ∧ IsOnQutrit f ∧ IsPhaseDiagonal R ∧
    ∀ k, B k = TensorState (a (e k).1)
      ((if (e k).1 = 0 then f else fun J => ApplyGate R (f J)) (e k).2)

/-- Shape `P2`: both bases indirect, each splitting into two MU qutrit bases. -/
def ShapeP2 (A B : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  ∃ (a b : Fin 2 → C2State) (f g h k : Fin 3 → C3State)
    (eA eB : Fin 6 ≃ Fin 2 × Fin 3),
    IsOnQubit a ∧ IsOnQubit b ∧ IsOnQutrit f ∧ IsOnQutrit g ∧
    IsOnQutrit h ∧ IsOnQutrit k ∧ IsMuQutritPair f g ∧ IsMuQutritPair h k ∧
    (∀ j, A j = TensorState (a (eA j).1)
      ((if (eA j).1 = 0 then f else g) (eA j).2)) ∧
    (∀ j, B j = TensorState (b (eB j).1)
      ((if (eB j).1 = 0 then h else k) (eB j).2))

/-- Shape `P3`: indirect first basis with a diagonal `Ŝ` rotation; second basis with a
qubit basis that varies with the qutrit label `J`. -/
def ShapeP3 (A B : Fin 6 → QState (Fin 2 × Fin 3)) : Prop :=
  ∃ (a : Fin 2 → C2State) (f : Fin 3 → C3State) (S : Matrix (Fin 3) (Fin 3) ℂ)
    (eA : Fin 6 ≃ Fin 2 × Fin 3) (aJ : Fin 3 → Fin 2 → C2State)
    (eB : Fin 6 ≃ Fin 3 × Fin 2),
    IsOnQubit a ∧ IsOnQutrit f ∧ IsPhaseDiagonal S ∧ (∀ J, IsOnQubit (aJ J)) ∧
    (∀ k, A k = TensorState (a (eA k).1)
      ((if (eA k).1 = 0 then f else fun J => ApplyGate S (f J)) (eA k).2)) ∧
    (∀ k, B k = TensorState (aJ (eB k).1 (eB k).2) (Ket (eB k).1))

/-- **Lemma 3** (arXiv:1203.6887v2, p. 8, Eq. (29)).  Any pair of MU product bases of
`C² ⊗ C³` is equivalent, under a common product unitary, permutations and phases, to a
representative of one of the four structural families `P0`, `P1`, `P2`, `P3`.
Registered as a `Prop`-valued definition; the proof is not formalised. -/
def lemma3_pair_classification
    (A B : Fin 6 → QState (Fin 2 × Fin 3))
    (hA : OrthonormalFamily A) (hB : OrthonormalFamily B)
    (hAprod : ∀ k, IsProductState (A k)) (hBprod : ∀ k, IsProductState (B k))
    (hMU : ∀ i j, Complex.normSq (Inner (A i) (B j)) = 1 / 6) : Prop :=
  (∃ A' B', ShapeP0 A' B' ∧ ProductEquivPair A B A' B') ∨
  (∃ A' B', ShapeP1 A' B' ∧ ProductEquivPair A B A' B') ∨
  (∃ A' B', ShapeP2 A' B' ∧ ProductEquivPair A B A' B') ∨
  (∃ A' B', ShapeP3 A' B' ∧ ProductEquivPair A B A' B')

end Qatlib.Papers.MUBProduct12.TripleClassify.Lemma3PairClassification
