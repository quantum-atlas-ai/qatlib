/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.GUnitExistenceQuan

/-!
# Orthogonality of local QTM transition families

The module introduces the inner product `bra` and the explicit head-centered window `wH`. It
identifies head basis states with configuration kets and assembles the orthogonality relations
among head states, one-step states, and the auxiliary window families.

`lemma1_transition_orthonormal` packages these relations in `Lemma1OrthonormalExchange`,
supplying the orthogonality input for the local unitary construction. See [Yao1993].

## Main statements

* `headBasis_eq_Ket`: identifies the head state with its explicit window ket.
* `lemma1_transition_orthonormal`: proves the collected orthogonality relations.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Lemma1Orthogonality

open Matrix
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath

/-- The complex inner product `star x ⬝ᵥ y` on finite state vectors, conjugate-linear in the
first argument. -/
abbrev bra {X : Type} [Fintype X] (x y : QState X) : ℂ := star x ⬝ᵥ y

/-- Moving a matrix from the first inner-product argument to the second replaces it by its
conjugate transpose. -/
theorem bra_mulVec_adjoint {X : Type} [Fintype X] (A : Matrix X X ℂ) (x y : QState X) :
    bra (A *ᵥ x) y = bra x (Aᴴ *ᵥ y) := by
  unfold bra
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/-- Applying the same unitary matrix to both arguments preserves `bra`. -/
theorem bra_mulVec_unitary {X : Type} [Fintype X] [DecidableEq X] {G : Matrix X X ℂ}
    (hG : G ∈ Matrix.unitaryGroup X ℂ) (x y : QState X) :
    bra (G *ᵥ x) (G *ᵥ y) = bra x y := by
  rw [bra_mulVec_adjoint]
  have h : Gᴴ * G = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hG)
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- The inner product of a basis ket with `y` is the corresponding coordinate of `y`. -/
theorem bra_ket_left {X : Type} [Fintype X] [DecidableEq X] (w : X) (y : QState X) :
    bra (Ket w) y = y w := by
  classical
  rw [bra]
  simp only [dotProduct]
  rw [Finset.sum_eq_single w]
  · simp [Ket]
  · intro i _ hi
    simp [Ket, hi]
  · intro hw
    exact absurd (Finset.mem_univ w) hw

/-- Two configuration kets have inner product one when their labels agree and zero otherwise. -/
theorem bra_ket_ket {X : Type} [Fintype X] [DecidableEq X] (w z : X) :
    bra (Ket w) (Ket z) = if w = z then (1 : ℂ) else 0 := by
  classical
  rw [bra_ket_left]
  simp [Ket]

section Point
variable {Q A : Type*}

/-- The three-cell window with head marker and state `q` in the center, center symbol `a`, and
neighboring symbols `b` and `c`. -/
def wH (q : Q) (a b c : A) : GWindow Q A :=
  ![((0 : Fin 3), none, b), ((1 : Fin 3), some q, a), ((0 : Fin 3), none, c)]

/-- The center, left, and right entries of `wH q a b c` are respectively `(1, some q, a)`, `(0,
none, b)`, and `(0, none, c)`. -/
theorem wH_spec (q : Q) (a b c : A) :
    wH q a b c 1 = (1, some q, a) ∧ wH q a b c 0 = (0, none, b) ∧
      wH q a b c 2 = (0, none, c) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [wH]

/-- Equality of two explicit head windows forces equality of the state and all three tape
symbols. -/
theorem wH_inj {q q' : Q} {a a' b b' c c' : A}
    (h : wH q a b c = wH q' a' b' c') : q = q' ∧ a = a' ∧ b = b' ∧ c = c' := by
  have h1 : wH q a b c 1 = wH q' a' b' c' 1 := by rw [h]
  have h0 : wH q a b c 0 = wH q' a' b' c' 0 := by rw [h]
  have h2 : wH q a b c 2 = wH q' a' b' c' 2 := by rw [h]
  simp [wH] at h0 h1 h2
  exact ⟨h1.1, h1.2, h0, h2⟩

end Point

section Families
variable {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]

omit [Fintype Q] [Fintype A] in

/-- The head basis vector is the configuration ket of its explicit window `wH`. -/
theorem headBasis_eq_Ket (q : Q) (a b c : A) :
    headBasis q a b c = Ket (wH q a b c) := by
  funext z
  simp only [headBasis, Ket]
  by_cases h : z 1 = (1, some q, a) ∧ z 0 = (0, none, b) ∧ z 2 = (0, none, c)
  · rw [if_pos h, if_pos]
    funext j
    fin_cases j
    · simpa [wH] using h.2.1
    · simpa [wH] using h.1
    · simpa [wH] using h.2.2
  · rw [if_neg h, if_neg]
    intro hz
    exact h (by rw [hz]; exact wH_spec q a b c)

/-- A one-step superposition has zero amplitude at every explicit head window `wH`. -/
theorem stepSuperposition_at_wH (M : LocalQTM Q A) (q q' : Q) (a b c a' b' c' : A) :
    stepSuperposition M q a b c (wH q' a' b' c') = 0 := by
  simp only [stepSuperposition, wH]
  simp

/-- Every `vFamily` vector has zero amplitude at each explicit head window `wH`. -/
theorem vFamily_at_wH (M : LocalQTM Q A) (q₀ q : Q) (a₀ b c a b' c' : A) :
    vFamily M q₀ a₀ b c (wH q a b' c') = 0 := by
  simp only [vFamily, wH]
  simp

/-- Every `uFamily` vector has zero amplitude at each explicit head window `wH`. -/
theorem uFamily_at_wH (M : LocalQTM Q A) (q₀ q : Q) (a₀ a'' b c d a b' c' : A) :
    uFamily M q₀ a₀ a'' b c d (wH q a b' c') = 0 := by
  simp only [uFamily, wH]
  simp

end Families

/-- The conjunction of orthonormality for the head and step families, their mutual
orthogonality, and their orthogonality to the type-I, `vFamily`, and `uFamily` vectors. -/
def Lemma1OrthonormalExchange {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (M : LocalQTM Q A) : Prop :=
  (∀ q : Q, ∀ a b c : A, ∀ q' : Q, ∀ a' b' c' : A,
      bra (headBasis q a b c) (headBasis q' a' b' c')
        = if wH q a b c = wH q' a' b' c' then 1 else 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ q' : Q, ∀ a' b' c' : A,
      bra (stepSuperposition M q a b c) (stepSuperposition M q' a' b' c')
        = if wH q a b c = wH q' a' b' c' then 1 else 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ q' : Q, ∀ a' b' c' : A,
      bra (headBasis q a b c) (stepSuperposition M q' a' b' c') = 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ z : GWindow Q A, IsTypeI z → bra (headBasis q a b c) (Ket z) = 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ z : GWindow Q A, IsTypeI z →
      bra (stepSuperposition M q a b c) (Ket z) = 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ q₀ : Q, ∀ a₀ b' c' : A,
      bra (headBasis q a b c) (vFamily M q₀ a₀ b' c') = 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ q₀ : Q, ∀ a₀ b' c' : A,
      bra (stepSuperposition M q a b c) (vFamily M q₀ a₀ b' c') = 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ q₀ : Q, ∀ a₀ a'' b' c' d : A,
      bra (headBasis q a b c) (uFamily M q₀ a₀ a'' b' c' d) = 0) ∧
  (∀ q : Q, ∀ a b c : A, ∀ q₀ : Q, ∀ a₀ a'' b' c' d : A,
      bra (stepSuperposition M q a b c) (uFamily M q₀ a₀ a'' b' c' d) = 0)

/-- Every `LocalQTM` satisfies the head, step, and auxiliary-family orthogonality relations
collected in `Lemma1OrthonormalExchange`. This is the local orthogonality statement
associated with Lemma 1 of [Yao1993]. -/
theorem lemma1_transition_orthonormal {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) :
    Lemma1OrthonormalExchange M := by
  obtain ⟨G, hG, hfix, hstep⟩ := gUnitExistence Q A M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q a b c q' a' b' c'
    rw [headBasis_eq_Ket, headBasis_eq_Ket, bra_ket_ket]
  · intro q a b c q' a' b' c'
    calc bra (stepSuperposition M q a b c) (stepSuperposition M q' a' b' c')
        = bra (G *ᵥ headBasis q a b c) (G *ᵥ headBasis q' a' b' c') := by
          rw [← hstep q a b c, ← hstep q' a' b' c']
      _ = bra (headBasis q a b c) (headBasis q' a' b' c') := bra_mulVec_unitary hG _ _
      _ = if wH q a b c = wH q' a' b' c' then 1 else 0 := by
          rw [headBasis_eq_Ket, headBasis_eq_Ket, bra_ket_ket]
  · intro q a b c q' a' b' c'
    rw [headBasis_eq_Ket, bra_ket_left]
    exact stepSuperposition_at_wH M q' q a' b' c' a b c
  · intro q a b c z hI
    rw [headBasis_eq_Ket, bra_ket_ket, if_neg]
    intro h
    apply hI.1
    rw [← h]
    exact congrArg Prod.fst (wH_spec q a b c).1
  · intro q a b c z hI
    have hz : G *ᵥ Ket z = Ket z := hfix.1 z hI
    calc bra (stepSuperposition M q a b c) (Ket z)
        = bra (G *ᵥ headBasis q a b c) (G *ᵥ Ket z) := by
          rw [← hstep q a b c]
          exact congrArg (bra (G *ᵥ headBasis q a b c)) hz.symm
      _ = bra (headBasis q a b c) (Ket z) := bra_mulVec_unitary hG _ _
      _ = 0 := by
          rw [headBasis_eq_Ket, bra_ket_ket, if_neg]
          intro h
          apply hI.1
          rw [← h]
          exact congrArg Prod.fst (wH_spec q a b c).1
  · intro q a b c q₀ a₀ b' c'
    rw [headBasis_eq_Ket, bra_ket_left]
    exact vFamily_at_wH M q₀ q a₀ b' c' a b c
  · intro q a b c q₀ a₀ b' c'
    have hv : G *ᵥ vFamily M q₀ a₀ b' c' = vFamily M q₀ a₀ b' c' := hfix.2.1 q₀ a₀ b' c'
    calc bra (stepSuperposition M q a b c) (vFamily M q₀ a₀ b' c')
        = bra (G *ᵥ headBasis q a b c) (G *ᵥ vFamily M q₀ a₀ b' c') := by
          rw [← hstep q a b c]
          exact congrArg (bra (G *ᵥ headBasis q a b c)) hv.symm
      _ = bra (headBasis q a b c) (vFamily M q₀ a₀ b' c') := bra_mulVec_unitary hG _ _
      _ = 0 := by
          rw [headBasis_eq_Ket, bra_ket_left]
          exact vFamily_at_wH M q₀ q a₀ b' c' a b c
  · intro q a b c q₀ a₀ a'' b' c' d
    rw [headBasis_eq_Ket, bra_ket_left]
    exact uFamily_at_wH M q₀ q a₀ a'' b' c' d a b c
  · intro q a b c q₀ a₀ a'' b' c' d
    have hu : G *ᵥ uFamily M q₀ a₀ a'' b' c' d = uFamily M q₀ a₀ a'' b' c' d :=
      hfix.2.2 q₀ a₀ a'' b' c' d
    calc bra (stepSuperposition M q a b c) (uFamily M q₀ a₀ a'' b' c' d)
        = bra (G *ᵥ headBasis q a b c) (G *ᵥ uFamily M q₀ a₀ a'' b' c' d) := by
          rw [← hstep q a b c]
          exact congrArg (bra (G *ᵥ headBasis q a b c)) hu.symm
      _ = bra (headBasis q a b c) (uFamily M q₀ a₀ a'' b' c' d) := bra_mulVec_unitary hG _ _
      _ = 0 := by
          rw [headBasis_eq_Ket, bra_ket_left]
          exact uFamily_at_wH M q₀ q a₀ a'' b' c' d a b c

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Lemma1Orthogonality
