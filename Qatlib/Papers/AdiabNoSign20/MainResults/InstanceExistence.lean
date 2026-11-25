/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# AdiabNoSign20 — a nonempty instance family for the corrected Theorem 1 contract

Source: M. B. Hastings, *The Power of Adiabatic Quantum Computation with No
Sign Problem*, arXiv:2005.03791v1, Definition 1 (Section 1.1, p. 3-4).

The legacy lower bound `Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel.NoAlgorithmBeatsInModel`
quantifies over every finite computational basis, including the empty type, on
which no `AdNSP` instance exists and the success condition holds vacuously
(`noAlgorithmBeats_modified_unsat`).  The corrected contract therefore needs an
inhabitedness assumption on the instance family.  This module supplies a
concrete family witnessing that the assumption is satisfiable:

* `plateauHamiltonian` — the constant-in-`s` diagonal Hamiltonian whose ground
  value `0` is attained only at the vertex `0` and whose other diagonal entries
  are `1`;
* `plateauParams` — polynomial data for which this family is admissible, with
  `p N = N`, sparsity `1`, entries bounded by `1`, derivative bound `1`, gap
  bound `1` and path length `1`;
* `plateauParams_family_inhabited` — for every `N ≥ 2` the type
  `AdNSPInstance (Fin (plateauParams.p N)) plateauParams N` is nonempty.

This only establishes that the inhabitedness hypothesis of the corrected
Theorem 1 is consistent; the query lower bound itself is not proved here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabNoSign20.MainResults.InstanceExistence

open Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel
open scoped BigOperators

/-- The diagonal Hamiltonian with ground value `0` at the vertex `0` and value
`1` at every other vertex.  Its ground state is `basisVector 0` and the
spectral gap above it is `1`. -/
def plateauHamiltonian (N : ℕ) [NeZero N] : Hamiltonian (Fin N) :=
  fun i j => if i = j then (if i = 0 then (0 : ℝ) else 1) else 0

/-- Polynomial data making the plateau family admissible: `p N = N`, and all
structural bounds are the constants `1`. -/
def plateauParams : AdNSPParameters where
  p := fun N => N
  sparseBound := fun _ => 1
  entryBound := fun _ => 1
  derivBound := fun _ => 1
  gapBound := fun _ => 1
  lengthBound := fun _ => 1
  pPoly := ⟨1, fun N => by
    rw [pow_one]
    exact Nat.le_succ N⟩
  gapInversePoly := ⟨1, one_pos, 1, fun N hN => by
    rw [pow_one]
    exact div_le_one_of_le₀ (by exact_mod_cast hN) (by positivity)⟩

section

variable {N : ℕ} [NeZero N]

/-- The quadratic form of the plateau Hamiltonian is its diagonal part. -/
lemma sum_quadform_plateau (φ : Fin N → ℝ) :
    (∑ i, ∑ j, φ i * plateauHamiltonian N i j * φ j) =
      ∑ i, φ i * (if i = 0 then (0 : ℝ) else 1) * φ i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [plateauHamiltonian]
  · intro j _ hj
    have hji : ¬ (i = j) := fun h => hj h.symm
    simp [plateauHamiltonian, hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The Rayleigh quotient of the plateau Hamiltonian. -/
lemma rayleigh_plateau (φ : Fin N → ℝ) :
    rayleigh (plateauHamiltonian N) φ =
      (∑ i, φ i * (if i = 0 then (0 : ℝ) else 1) * φ i) / (∑ i, φ i * φ i) := by
  rw [rayleigh, sum_quadform_plateau]

/-- The squared norm of the basis vector at `0` is one. -/
lemma sum_sq_basis_zero :
    (∑ i, basisVector (0 : Fin N) i * basisVector (0 : Fin N) i) = 1 := by
  rw [Finset.sum_eq_single (0 : Fin N)]
  · simp [basisVector]
  · intro j _ hj
    simp [basisVector, hj]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin N)) h

/-- The diagonal quadratic form vanishes on the basis vector at `0`. -/
lemma sum_quadform_basis_zero :
    (∑ i, basisVector (0 : Fin N) i * (if i = 0 then (0 : ℝ) else 1) *
      basisVector (0 : Fin N) i) = 0 := by
  rw [Finset.sum_eq_single (0 : Fin N)]
  · simp [basisVector]
  · intro j _ hj
    simp [basisVector, hj]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin N)) h

/-- Pairing with the basis vector at `0` reads off the `0`-th coordinate. -/
lemma basisVector_zero_dot (φ : Fin N → ℝ) :
    (∑ i, basisVector (0 : Fin N) i * φ i) = φ 0 := by
  rw [Finset.sum_eq_single (0 : Fin N)]
  · simp [basisVector]
  · intro j _ hj
    simp [basisVector, hj]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin N)) h

/-- On vectors whose `0`-coordinate vanishes, the diagonal quadratic form of
the plateau Hamiltonian equals the squared norm. -/
lemma sum_quadform_eq_sum_sq_of_zero_coord {φ : Fin N → ℝ} (hφ0 : φ 0 = 0) :
    (∑ i, φ i * (if i = 0 then (0 : ℝ) else 1) * φ i) = ∑ i, φ i * φ i := by
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : i = 0
  · subst hi
    simp [hφ0]
  · simp [hi]

/-- On the orthogonal complement of the ground state the Rayleigh quotient of
the plateau Hamiltonian equals `1`. -/
lemma rayleigh_plateau_eq_one {φ : Fin N → ℝ} (hφ0 : φ 0 = 0)
    (hden : (∑ i, φ i * φ i) ≠ 0) :
    rayleigh (plateauHamiltonian N) φ = 1 := by
  rw [rayleigh_plateau, sum_quadform_eq_sum_sq_of_zero_coord hφ0]
  exact div_self hden

/-- The basis vector at `0` is a ground state of the plateau Hamiltonian. -/
lemma isGroundState_basis_zero :
    IsGroundState (plateauHamiltonian N) (basisVector (0 : Fin N)) := by
  refine ⟨?_, ?_⟩
  · rw [sum_sq_basis_zero]
    norm_num
  · intro φ _hφ
    have hψ : rayleigh (plateauHamiltonian N) (basisVector (0 : Fin N)) = 0 := by
      rw [rayleigh_plateau, sum_quadform_basis_zero, sum_sq_basis_zero]
      norm_num
    have hnum : 0 ≤ ∑ i, φ i * (if i = 0 then (0 : ℝ) else 1) * φ i := by
      refine Finset.sum_nonneg ?_
      intro i _
      by_cases hi : i = 0
      · simp [hi]
      · simp only [hi, ite_false]
        nlinarith [sq_nonneg (φ i)]
    have hden : 0 ≤ ∑ i, φ i * φ i :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg (φ i)
    have hφr : 0 ≤ rayleigh (plateauHamiltonian N) φ := by
      rw [rayleigh_plateau]
      exact div_nonneg hnum hden
    rw [hψ]
    exact hφr

/-- The plateau Hamiltonian has a unique ground state separated by gap `1`. -/
lemma uniqueGappedGroundState_plateau :
    UniqueGappedGroundState (plateauHamiltonian N) 1 := by
  refine ⟨basisVector (0 : Fin N), isGroundState_basis_zero, ?_⟩
  intro φ horth hden
  have hφ0 : φ 0 = 0 := by
    rw [← basisVector_zero_dot φ]
    exact horth
  have hψ : rayleigh (plateauHamiltonian N) (basisVector (0 : Fin N)) = 0 := by
    rw [rayleigh_plateau, sum_quadform_basis_zero, sum_sq_basis_zero]
    norm_num
  rw [hψ, rayleigh_plateau_eq_one hφ0 hden]
  norm_num

/-- The plateau Hamiltonian is symmetric. -/
lemma symmetric_plateau : IsSymmetricHamiltonian (plateauHamiltonian N) := by
  intro i j
  by_cases h : i = j
  · subst h
    rfl
  · have hji : ¬ (j = i) := fun h' => h h'.symm
    simp [plateauHamiltonian, h, hji]

/-- The plateau Hamiltonian is row sparse with bound `1`. -/
lemma rowSparse_plateau : IsRowSparse (plateauHamiltonian N) 1 := by
  intro i
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have ha' : a = i := by
    by_contra hne
    have hia : ¬ (i = a) := fun h => hne h.symm
    exact ha (by simp [plateauHamiltonian, hia])
  have hb' : b = i := by
    by_contra hne
    have hib : ¬ (i = b) := fun h => hne h.symm
    exact hb (by simp [plateauHamiltonian, hib])
  rw [ha', hb']

/-- The entries of the plateau Hamiltonian are bounded by `1`. -/
lemma boundedEntries_plateau : HasBoundedEntries (plateauHamiltonian N) 1 := by
  intro i j
  by_cases h : i = j
  · subst h
    by_cases hi : i = 0 <;> simp [plateauHamiltonian, hi]
  · simp [plateauHamiltonian, h]

/-- The constant plateau path is admissible with the polynomial data
`plateauParams` on the interval `[0, 1]`. -/
lemma admissible_plateau :
    IsAdmissiblePath plateauParams N (fun _ => plateauHamiltonian N) 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · simp [plateauParams]
  · intro _
    exact symmetric_plateau
  · intro _ i j hij
    simp [plateauHamiltonian, hij]
  · intro _
    exact rowSparse_plateau
  · intro _
    exact boundedEntries_plateau
  · intro _ _ _
    exact differentiableAt_const _
  · intro _ _ _
    rw [deriv_const]
    simp [plateauParams]
  · intro _
    exact uniqueGappedGroundState_plateau

/-- The plateau path with the endpoint condition is an `AdNSP` instance. -/
noncomputable def plateauInstance : AdNSPInstance (Fin N) plateauParams N where
  H := fun _ => plateauHamiltonian N
  a := 0
  b := 1
  admissible := admissible_plateau
  endpoint :=
    ⟨⟨0, isGroundState_basis_zero⟩, ⟨0, isGroundState_basis_zero⟩⟩

end

/-- For every `N ≥ 2` the family of plateau instances is nonempty; this is the
inhabitedness hypothesis needed by the corrected Theorem 1 contract. -/
theorem plateauParams_family_inhabited {N : ℕ} (hN : 2 ≤ N) :
    Nonempty (AdNSPInstance (Fin (plateauParams.p N)) plateauParams N) := by
  have : NeZero N := ⟨by omega⟩
  have : NeZero (plateauParams.p N) :=
    ⟨by simpa [plateauParams] using (show N ≠ 0 by omega)⟩
  exact ⟨plateauInstance⟩

end Qatlib.Papers.AdiabNoSign20.MainResults.InstanceExistence
