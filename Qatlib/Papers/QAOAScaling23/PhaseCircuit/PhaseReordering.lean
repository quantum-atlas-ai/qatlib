/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Papers.QAOAScaling23.PhaseCircuit.FourBody
public import Qatlib.Papers.QAOAScaling23.PhaseCircuit.GreedyOrder

@[expose] public section

/-!
# Reordering diagonal LABS phase terms

Every term scheduled by Algorithm 2 is represented by a diagonal matrix with
the angle prescribed by Eq. (4): `4γ` for a four-body term and `2γ` for a
two-body term.  Multiplicities and coefficients are retained, so any
permutation of the terms yields the same product.  The estimate uses the
Euclidean operator norm `Matrix.Norms.L2Operator`; it does not permit moving
CNOT instructions out of one term's implementation.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QAOAScaling23.PhaseCircuit

/-- The diagonal unitary represented by one scheduled phase term. -/
def phaseTermMatrix {n : ℕ} (γ : ℝ) (term : PhaseTerm n) :
    Matrix (Reg n) (Reg n) ℂ :=
  match term with
  | .inl four => rzzzz (4 * γ) four.top.1 four.top.2 four.bottom.1 four.bottom.2
  | .inr pair => rzz (2 * γ) pair.1 pair.2

/-- The ordered product represented by a list of scheduled phase terms. -/
def phaseWordMatrix {n : ℕ} (γ : ℝ) (terms : List (PhaseTerm n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  (terms.map (phaseTermMatrix γ)).prod

/-- A four-wire diagonal coupling is unitary even if wire labels coincide. -/
theorem rzzzz_unitary {n : ℕ} (θ : ℝ) (i j k l : Fin n) :
    rzzzz θ i j k l ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [rzzzz]
  apply diagonal_mem_unitaryGroup
  intro x
  simp [couplingPhase, Complex.norm_exp, Complex.mul_re]

/-- Every LABS phase term is a unitary diagonal matrix. -/
theorem phaseTermMatrix_unitary {n : ℕ} (γ : ℝ) (term : PhaseTerm n) :
    phaseTermMatrix γ term ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  cases term with
  | inl four => exact rzzzz_unitary _ four.top.1 four.top.2 four.bottom.1 four.bottom.2
  | inr pair => exact rzz_unitary _ pair.1 pair.2

/-- A list of LABS phase terms evaluates to a unitary matrix. -/
theorem phaseWordMatrix_unitary {n : ℕ} (γ : ℝ) (terms : List (PhaseTerm n)) :
    phaseWordMatrix γ terms ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  unfold phaseWordMatrix
  exact Submonoid.list_prod_mem
    (s := Matrix.unitaryGroup (Reg n) ℂ)
    (fun U hU => by
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hU
      exact phaseTermMatrix_unitary γ term)

/-- LABS phase terms are diagonal and therefore commute. -/
theorem phaseTermMatrix_comm {n : ℕ} (γ : ℝ) (a b : PhaseTerm n) :
    phaseTermMatrix γ a * phaseTermMatrix γ b =
      phaseTermMatrix γ b * phaseTermMatrix γ a := by
  unfold phaseTermMatrix
  cases a <;> cases b <;>
    simp [rzz, rzzzz, Matrix.diagonal_mul_diagonal, mul_comm]

/-- Permuting a multiset of LABS phase terms leaves the product unchanged. -/
theorem phaseWordMatrix_perm {n : ℕ} (γ : ℝ) {terms reordered : List (PhaseTerm n)}
    (hp : terms.Perm reordered) :
    phaseWordMatrix γ terms = phaseWordMatrix γ reordered := by
  unfold phaseWordMatrix
  induction hp with
  | nil => rfl
  | cons a _ ih =>
      simp only [List.map_cons, List.prod_cons]
      exact congrArg (fun P => phaseTermMatrix γ a * P) ih
  | swap a b rest =>
      simp only [List.map_cons, List.prod_cons]
      rw [← mul_assoc, ← mul_assoc, phaseTermMatrix_comm γ a b]
  | trans _ _ ih_left ih_right => exact ih_left.trans ih_right

/-- The corrected greedy schedule has the same diagonal phase product as its input multiset. -/
theorem greedy_phaseWordMatrix {n : ℕ} (γ : ℝ)
    (four : List (FourBodyTerm n)) (two : List (WirePair n)) :
    phaseWordMatrix γ (greedyOrder four two) =
      phaseWordMatrix γ (four.map Sum.inl ++ two.map Sum.inr) :=
  phaseWordMatrix_perm γ (greedy_emits_perm four two).1

/-- Exact reordering has zero operator-norm error, hence admits a uniform positive bound of one. -/
theorem phase_reordering_norm_bound :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧ ∀ (n : ℕ) (_hn : 0 < n) [Nonempty (Reg n)] (γ : ℝ)
        (terms reordered : List (PhaseTerm n)) (_hp : terms.Perm reordered),
      ‖phaseWordMatrix γ terms - phaseWordMatrix γ reordered‖ ≤ C := by
  refine ⟨1, one_pos, le_refl 1, fun n _hn _ γ terms reordered hp => ?_⟩
  rw [phaseWordMatrix_perm γ hp, sub_self, norm_zero]
  exact zero_le_one

end Qatlib.Papers.QAOAScaling23.PhaseCircuit
