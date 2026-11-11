/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Finite pointer shifts and readout

This module studies a finite cyclic pointer model motivated by the observable-pointer coupling
in [Zalka1998], Eq. (17). `pointerShift` translates a pointer modulo `M`, and `pointerCoupling`
conditions that translation on a preserved system basis label.

`pointerDistribution` and `pointerSlice` describe pointer probabilities and the corresponding
unnormalized system components. A separate two-state example, `pointerMomentumTwo`, has
Hamiltonian evolution equal to a bit flip at unit time.

## Main statements

* `pointerShift_unitary` and `pointerCoupling_unitary` prove unitarity of the finite
  translations.
* `pointerCoupling_eigenstate_readout` gives deterministic readout for a system basis state with
  an initially zero pointer.
* `pointerMomentumTwo_evolution_one` and `pointerMomentumTwo_evolution_nat` compute the
  two-state evolution.
* `pointerDistribution_initial` sums spectral weights sharing a pointer position, and
  `pointerSlice_initial_separated` isolates a uniquely separated label.

## References

* [Zalka, 1998][Zalka1998]
-/

set_option autoImplicit false
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QSystemSim96.MainResults

open Qatlib.Foundations.PureStateMath

noncomputable section

/-- The permutation matrix translating a cyclic pointer position by the integer `s` modulo the
nonzero size `M`. -/
def pointerShift (M : ℕ) [NeZero M] (s : ℤ) : Matrix (ZMod M) (ZMod M) ℂ :=
  permMatrix (fun x => x + (s : ZMod M))

/-- The finite pointer shift sends `Ket x` to `Ket (x + s)` modulo `M`, modeling the translation
in [Zalka1998], Eq. (17). -/
theorem pointerShift_ket {M : ℕ} [NeZero M] (s : ℤ) (x : ZMod M) :
    ApplyGate (pointerShift M s) (Ket x) = Ket (x + (s : ZMod M)) := by
  unfold ApplyGate pointerShift
  funext i
  simp only [permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Ket]
  rw [Finset.sum_eq_single x]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- Composing cyclic pointer shifts by `t` and `s` gives the shift by `s + t`. -/
theorem pointerShift_mul {M : ℕ} [NeZero M] (s t : ℤ) :
    pointerShift M s * pointerShift M t = pointerShift M (s + t) := by
  ext i j
  simp only [pointerShift, permMatrix, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (j + (t : ZMod M))]
  · have h : j + (t : ZMod M) + (s : ZMod M) = j + ((s + t : ℤ) : ZMod M) := by
      push_cast
      abel
    simp [h]
  · intro k _ hk
    have hzero : (if k = j + (t : ZMod M) then (1 : ℂ) else 0) = 0 := by
      simp [hk]
    rw [hzero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (j + (t : ZMod M))) h

/-- The conjugate transpose of a pointer-shift matrix equals its transpose, since its entries
are real. -/
theorem pointerShift_star {M : ℕ} [NeZero M] (s : ℤ) :
    star (pointerShift M s) = (pointerShift M s)ᵀ := by
  ext i j
  simp [pointerShift, permMatrix, Matrix.star_apply, Matrix.transpose_apply]

/-- A pointer-shift matrix multiplied by its transpose equals the identity. -/
theorem pointerShift_mul_transpose {M : ℕ} [NeZero M] (s : ℤ) :
    pointerShift M s * (pointerShift M s)ᵀ = 1 := by
  ext i j
  simp only [pointerShift, permMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (i - (s : ZMod M))]
  · have h : i - (s : ZMod M) + (s : ZMod M) = i := sub_add_cancel _ _
    simp [h, eq_comm]
  · intro k _ hk
    have hne : i ≠ k + (s : ZMod M) := by
      intro h
      apply hk
      rw [h]
      abel
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ (i - (s : ZMod M))) h

/-- Every finite cyclic pointer shift is unitary, as required for the pointer translation
modeled on [Zalka1998], Eq. (17). -/
theorem pointerShift_unitary {M : ℕ} [NeZero M] (s : ℤ) :
    pointerShift M s ∈ Matrix.unitaryGroup (ZMod M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, pointerShift_star]
  exact pointerShift_mul_transpose s

/-- The block-diagonal matrix that shifts the pointer by `s a` in the block indexed by the
preserved system label `a`. -/
def pointerCoupling {M : ℕ} [NeZero M] {ι : Type*} [DecidableEq ι] (s : ι → ℤ) :
    Matrix (ZMod M × ι) (ZMod M × ι) ℂ :=
  Matrix.blockDiagonal (fun a => pointerShift M (s a))

/-- The coupling shifts the pointer by `s a` while preserving the system basis label `a`, giving
a finite counterpart of [Zalka1998], Eq. (17). -/
theorem pointerCoupling_ket {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → ℤ) (x : ZMod M) (a : ι) :
    ApplyGate (pointerCoupling s) (Ket (x, a)) = Ket (x + (s a : ZMod M), a) := by
  unfold ApplyGate pointerCoupling
  funext ib
  obtain ⟨i, b⟩ := ib
  simp only [Matrix.mulVec, dotProduct, Ket]
  rw [Finset.sum_eq_single (x, a)]
  · by_cases hba : b = a
    · subst hba
      simp [Matrix.blockDiagonal_apply, pointerShift, permMatrix]
    · simp [Matrix.blockDiagonal_apply, pointerShift, permMatrix, hba]
  · rintro ⟨j, c⟩ _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ (x, a)) h

/-- The conjugate transpose of the coupling is the block-diagonal matrix of conjugate-transposed
pointer shifts. -/
theorem pointerCoupling_star {M : ℕ} [NeZero M] {ι : Type*} [DecidableEq ι]
    (s : ι → ℤ) :
    star (pointerCoupling s) =
      Matrix.blockDiagonal (fun a => star (pointerShift M (s a))) := by
  rw [pointerCoupling, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_conjTranspose]
  simp only [Matrix.star_eq_conjTranspose]

/-- The finite controlled pointer translation is unitary, providing the coupling model
associated with [Zalka1998], Eq. (17). -/
theorem pointerCoupling_unitary {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → ℤ) :
    pointerCoupling s ∈ Matrix.unitaryGroup (ZMod M × ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, pointerCoupling_star]
  unfold pointerCoupling
  rw [← Matrix.blockDiagonal_mul]
  simp only [pointerShift_star]
  have h : (fun a => pointerShift M (s a) * (pointerShift M (s a))ᵀ) =
      (fun _ => (1 : Matrix (ZMod M) (ZMod M) ℂ)) := by
    funext a
    exact pointerShift_mul_transpose (s a)
  rw [h]
  exact Matrix.blockDiagonal_one (m := ZMod M) (o := ι) (α := ℂ)

/-- Multiplying couplings with shift functions `s` and `t` gives the coupling with pointwise
shift `s a + t a`. -/
theorem pointerCoupling_mul {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s t : ι → ℤ) :
    pointerCoupling (M := M) s * pointerCoupling (M := M) t =
      pointerCoupling (M := M) (fun a => s a + t a) := by
  unfold pointerCoupling
  rw [← Matrix.blockDiagonal_mul]
  congr 1
  funext a
  exact pointerShift_mul (M := M) (s a) (t a)

/-- The marginal Born weight at pointer position `x`, obtained by summing over all system
labels. -/
def pointerDistribution {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    (ψ : QState (ZMod M × ι)) (x : ZMod M) : ℝ :=
  ∑ a, BornProb ψ (x, a)

/-- For a normalized joint state, the pointer marginal weights sum to one. -/
theorem pointerDistribution_sum {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    (ψ : QState (ZMod M × ι)) (hψ : Normalized ψ) :
    ∑ x, pointerDistribution ψ x = 1 := by
  unfold pointerDistribution
  rw [← Fintype.sum_prod_type]
  exact hψ

/-- Starting from pointer position zero and system label `a`, the coupled pointer has weight one
at `s a` modulo `M` and zero elsewhere, giving the finite readout law of [Zalka1998], Eq.
(17). -/
theorem pointerCoupling_eigenstate_readout {M : ℕ} [NeZero M] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (s : ι → ℤ) (a : ι) :
    pointerDistribution (ApplyGate (pointerCoupling s) (Ket ((0 : ZMod M), a)))
        (s a : ZMod M) = 1 ∧
      ∀ x : ZMod M, x ≠ (s a : ZMod M) →
        pointerDistribution (ApplyGate (pointerCoupling s) (Ket ((0 : ZMod M), a))) x = 0 := by
  have hket : ApplyGate (pointerCoupling s) (Ket ((0 : ZMod M), a)) =
      Ket ((s a : ZMod M), a) := by
    simpa using pointerCoupling_ket (M := M) s (0 : ZMod M) a
  constructor
  · rw [hket]
    unfold pointerDistribution
    rw [Finset.sum_eq_single a]
    · simp [bornProb_ket]
    · intro b _ hb
      simp [bornProb_ket, hb]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro x hx
    rw [hket]
    unfold pointerDistribution
    simp only [bornProb_ket]
    apply Finset.sum_eq_zero
    intro b _
    have hne : (x, b) ≠ ((s a : ZMod M), a) := by
      intro h
      exact hx (congrArg Prod.fst h)
    simp [hne]

/-- The diagonal two-state matrix with eigenvalues zero at `false` and `Real.pi` at `true`. -/
noncomputable def pointerSpectrumTwo : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if b then (Real.pi : ℂ) else 0)

/-- The two-state matrix obtained by conjugating `pointerSpectrumTwo` by the Hadamard matrix. -/
noncomputable def pointerMomentumTwo : Matrix Bool Bool ℂ :=
  Hadamard * pointerSpectrumTwo * Hadamard

/-- The two-state pointer momentum matrix is Hermitian, furnishing a finite Hamiltonian example
motivated by [Zalka1998], Eq. (17). -/
theorem pointerMomentumTwo_isHermitian : pointerMomentumTwo.IsHermitian := by
  have hD : (Matrix.diagonal (fun b : Bool => if b then (Real.pi : ℂ) else 0))ᴴ =
      Matrix.diagonal (fun b : Bool => if b then (Real.pi : ℂ) else 0) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext b
    cases b
    · simp
    · simp
  unfold Matrix.IsHermitian pointerMomentumTwo pointerSpectrumTwo
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hadamard_conjTranspose, hD,
    mul_assoc]

/-- Hamiltonian evolution under `pointerMomentumTwo` at unit time is exactly `PauliX`, giving a
two-state translation example for [Zalka1998], Eq. (17). -/
theorem pointerMomentumTwo_evolution_one :
    HamiltonianEvolution pointerMomentumTwo 1 = PauliX := by
  have hInv : Hadamard⁻¹ = Hadamard := Matrix.inv_eq_right_inv hadamard_mul_self
  have hunit : IsUnit Hadamard :=
    ⟨⟨Hadamard, Hadamard, hadamard_mul_self, hadamard_mul_self⟩, rfl⟩
  have hscalar : (-Complex.I * ((1 : ℝ) : ℂ)) •
      (Hadamard * pointerSpectrumTwo * Hadamard) =
      Hadamard * ((-Complex.I) • pointerSpectrumTwo) * Hadamard := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_assoc,
      show ((1 : ℝ) : ℂ) = 1 by norm_num, mul_one]
  have hconj : Hadamard * ((-Complex.I) • pointerSpectrumTwo) * Hadamard⁻¹ =
      Hadamard * ((-Complex.I) • pointerSpectrumTwo) * Hadamard := by rw [hInv]
  unfold HamiltonianEvolution pointerMomentumTwo
  rw [hscalar, ← hconj, Matrix.exp_conj Hadamard _ hunit, hInv]
  have hspec : NormedSpace.exp ((-Complex.I) • pointerSpectrumTwo) = PauliZ := by
    unfold pointerSpectrumTwo PauliZ
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext b
    rw [Pi.coe_exp]
    simp only [Pi.smul_apply, smul_eq_mul]
    cases b
    · simp
    · simp only [if_true]
      rw [← Complex.exp_eq_exp_ℂ]
      rw [show -Complex.I * (Real.pi : ℂ) = -(Real.pi * Complex.I) by ring]
      exact Complex.exp_neg_pi_mul_I
  rw [hspec]
  ext i j
  rcases i <;> rcases j <;>
    simp [Matrix.mul_apply, Hadamard, PauliZ, PauliX, permMatrix] <;>
      ring_nf <;> norm_num [sqrt2_sq]

/-- At every natural time `n`, evolution under the two-state pointer momentum is `PauliX ^ n`,
extending the finite translation example for [Zalka1998], Eq. (17). -/
theorem pointerMomentumTwo_evolution_nat (n : ℕ) :
    HamiltonianEvolution pointerMomentumTwo (n : ℝ) = PauliX ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, hamiltonianEvolution_zero, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, hamiltonianEvolution_add, ih, pointerMomentumTwo_evolution_one,
      pow_succ]

/-- Unit-time evolution under the two-state pointer momentum flips either Boolean basis state,
realizing a finite pointer translation motivated by [Zalka1998], Eq. (17). -/
theorem pointerMomentumTwo_ket (b : Bool) :
    ApplyGate (HamiltonianEvolution pointerMomentumTwo 1) (Ket b) = Ket (!b) := by
  rw [pointerMomentumTwo_evolution_one]
  exact applyGate_pauliX_ket b

/-- The joint state with system amplitudes `c` supported only at pointer position zero. -/
def pointerInitial {M : ℕ} [NeZero M] {ι : Type*} (c : ι → ℂ) :
    QState (ZMod M × ι) :=
  fun xa => if xa.1 = 0 then c xa.2 else 0

/-- After coupling an initially zero pointer, the joint amplitude at `(x, a)` is `c a` exactly
when `x = s a` modulo `M`, and is zero otherwise. -/
theorem pointerCoupling_initial {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → ℤ) (c : ι → ℂ) :
    ApplyGate (pointerCoupling s) (pointerInitial (M := M) c) =
      fun xa => if xa.1 = (s xa.2 : ZMod M) then c xa.2 else 0 := by
  unfold ApplyGate pointerCoupling pointerInitial
  funext ib
  obtain ⟨i, b⟩ := ib
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (0, b)]
  · simp [Matrix.blockDiagonal_apply, pointerShift, permMatrix]
  · rintro ⟨j, c'⟩ _ hne
    by_cases hb : c' = b
    · subst hb
      have hj : j ≠ (0 : ZMod M) := by
        intro h0
        exact hne (Prod.ext h0 rfl)
      simp [Matrix.blockDiagonal_apply, hj]
    · have hbc : ¬ (b = c') := fun h => hb h.symm
      simp [Matrix.blockDiagonal_apply, hbc]
  · intro h
    exact absurd (Finset.mem_univ (0, b)) h

/-- The unnormalized system state obtained by fixing the pointer coordinate of a joint state to
`x`. -/
def pointerSlice {M : ℕ} [NeZero M] {ι : Type*} (ψ : QState (ZMod M × ι))
    (x : ZMod M) : QState ι :=
  fun a => ψ (x, a)

/-- The pointer slice after coupling retains exactly those initial system amplitudes whose
shifts equal the observed position modulo `M`. -/
theorem pointerSlice_initial {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → ℤ) (c : ι → ℂ) (x : ZMod M) :
    pointerSlice (ApplyGate (pointerCoupling s) (pointerInitial (M := M) c)) x =
      fun a => if (s a : ZMod M) = x then c a else 0 := by
  rw [pointerCoupling_initial]
  funext a
  simp [pointerSlice, eq_comm]

/-- The pointer weight after coupling is the sum of `‖c a‖ ^ 2` over labels whose shifts equal
that pointer position modulo `M`, the finite spectral-weight law corresponding to
[Zalka1998], Eq. (17). -/
theorem pointerDistribution_initial {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → ℤ) (c : ι → ℂ) (x : ZMod M) :
    pointerDistribution (ApplyGate (pointerCoupling s) (pointerInitial (M := M) c)) x =
      ∑ a, if (s a : ZMod M) = x then ‖c a‖ ^ 2 else 0 := by
  unfold pointerDistribution BornProb
  change (∑ a, ‖pointerSlice (ApplyGate (pointerCoupling s)
      (pointerInitial (M := M) c)) x a‖ ^ 2) =
    ∑ a, if (s a : ZMod M) = x then ‖c a‖ ^ 2 else 0
  rw [pointerSlice_initial]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (s a : ZMod M) = x
  · simp [h]
  · simp [h]

/-- If no other label shares the shift of `a` modulo `M`, the slice at that shift contains only
the amplitude `c a` on label `a`, giving the unnormalized separated-label component
associated with [Zalka1998], Eq. (17). -/
theorem pointerSlice_initial_separated {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → ℤ) (c : ι → ℂ) (a : ι)
    (hsep : ∀ b, (s b : ZMod M) = (s a : ZMod M) → b = a) :
    pointerSlice (ApplyGate (pointerCoupling s) (pointerInitial (M := M) c))
        (s a : ZMod M) = fun b => if b = a then c a else 0 := by
  rw [pointerSlice_initial]
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · have hne : (s b : ZMod M) ≠ (s a : ZMod M) := fun h => hb (hsep b h)
    simp [hb, hne]

end

end Qatlib.Papers.QSystemSim96.MainResults
