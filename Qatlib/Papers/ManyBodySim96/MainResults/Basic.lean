/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.TrotterFormula.LieStrang.TrotterFirstOrderTailSumAthe
import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutatorConsumers
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite models for many-body Hamiltonian simulation

This module defines qubit and discretized-particle registers, diagonal potential layers, and
kinetic layers in a supplied unitary basis. It proves exact layer identities, finite
product-formula error and word-length bounds, and exponential growth of basis cardinalities.
`twoState_finite_components` and `particle_finite_components` collect these finite-dimensional
statements.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `twoState_finite_components`: Combines the selected Strang word's length, unitarity, and
  operator and observable error bounds with the exponential qubit basis cardinality and growth
  statements.
* `kineticLayer_eq_evolution`: In a unitary basis, the kinetic layer equals the exact evolution
  of the kinetic Hamiltonian.
* `particle_finite_components`: For positive particle number and word size and a unitary basis
  matrix, collects exact kinetic and potential layers, selected Strang accuracy and length
  bounds, and exponential register cardinality and growth.

## References

* [Wiesner, 1996][Wiesner1996]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.FiniteStrang
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ManyBodySim96.MainResults

/-- The `N`-qubit computational basis register. -/
abbrev TwoStateRegister (N : ℕ) := Reg N

/-- The basis dimension `2 ^ N` of an `N`-qubit register. -/
def twoStateDim (N : ℕ) : ℕ := 2 ^ N

/-- The two-state dimension equals the cardinality of the qubit register basis. -/
theorem twoStateDim_eq_card (N : ℕ) : twoStateDim N = Fintype.card (Reg N) := by
  rw [twoStateDim, card_reg]

/-- Adding one two-state system doubles the basis dimension. -/
theorem twoStateDim_succ (N : ℕ) : twoStateDim (N + 1) = 2 * twoStateDim N := by
  unfold twoStateDim
  rw [pow_succ]
  ring

/-- The dimension of `N` two-state systems is at least `N + 1`. -/
theorem twoStateDim_ge_succ (N : ℕ) : N + 1 ≤ twoStateDim N := by
  unfold twoStateDim
  exact Nat.succ_le_iff.mpr Nat.lt_two_pow_self

/-- The count `N * (N + 1) / 2` of one-body terms and unordered two-body pairs. -/
def oneTwoBodyTermCount (N : ℕ) : ℕ := N * (N + 1) / 2

/-- The first-order Taylor matrix `1 + i * dt * H` with the source's positive-sign convention. -/
def taylorStep {D : ℕ} (H : Operator D) (dt : ℝ) : Operator D :=
  1 + (Complex.I * (dt : ℂ)) • H

/-- The diagonal operator with prescribed complex entries. -/
def phaseDiag {D : ℕ} (v : Fin D → ℂ) : Operator D := Matrix.diagonal v

/-- A diagonal operator acts on each state coordinate by multiplication by its corresponding
diagonal entry. -/
theorem phaseDiag_mulVec_apply {D : ℕ} (v : Fin D → ℂ) (ψ : QState (Fin D)) (i : Fin D) :
    (phaseDiag v *ᵥ ψ) i = v i * ψ i := by
  unfold phaseDiag
  rw [Matrix.mulVec_diagonal]

/-- A diagonal operator is unitary when each entry satisfies `star (v i) * v i = 1`. -/
theorem phaseDiag_mem_unitaryGroup {D : ℕ} (v : Fin D → ℂ)
    (hv : ∀ i, star (v i) * v i = 1) :
    phaseDiag v ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  unfold phaseDiag
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  change star (v i) * v i = 1
  exact hv i

/-- A diagonal operator with real entries is Hermitian. -/
theorem phaseDiag_ofReal_isHermitian {D : ℕ} (v : Fin D → ℝ) :
    (phaseDiag (fun i => (v i : ℂ))).IsHermitian := by
  show (phaseDiag (fun i => (v i : ℂ))).conjTranspose = _
  unfold phaseDiag
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- For `M ≥ 4`, the exponential `2 ^ M` is at least `2 * M + 3`. -/
theorem linear_le_two_pow (M : ℕ) (hM : 4 ≤ M) : 2 * M + 3 ≤ 2 ^ M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    have h2 : 2 ≤ 2 ^ M := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by
      rw [pow_succ]
      ring
    rw [hp]
    omega

/-- For `M ≥ 6`, the exponential `2 ^ M` is at least `(M + 1) ^ 2`. -/
theorem pow_two_le_two_pow (M : ℕ) (hM : 6 ≤ M) : (M + 1) ^ 2 ≤ 2 ^ M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    have hlin : 2 * M + 3 ≤ 2 ^ M := linear_le_two_pow M (by omega)
    have hstep : (M + 1 + 1) ^ 2 = (M + 1) ^ 2 + (2 * M + 3) := by ring
    rw [hstep]
    have h2 : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by
      rw [pow_succ]
      ring
    rw [h2]
    omega

/-- Every fixed natural multiple of `M + 1` is eventually bounded above by `2 ^ M`. -/
theorem eventually_linear_le_two_pow (k : ℕ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, k * (M + 1) ≤ 2 ^ M := by
  refine ⟨k + 6, ?_⟩
  intro M hM
  have h6 : 6 ≤ M := by omega
  have hk : k ≤ M + 1 := by omega
  calc k * (M + 1) ≤ (M + 1) * (M + 1) := Nat.mul_le_mul_right (M + 1) hk
    _ = (M + 1) ^ 2 := by ring
    _ ≤ 2 ^ M := pow_two_le_two_pow M h6

/-- Every fixed power `(N + 1) ^ d` is eventually strictly smaller than `2 ^ N`. -/
theorem eventually_pow_lt_two_pow (d : ℕ) : ∃ T : ℕ, ∀ N ≥ T, (N + 1) ^ d < 2 ^ N := by
  induction d with
  | zero =>
    refine ⟨1, ?_⟩
    intro N hN
    have h2 : 1 < 2 ^ N := Nat.one_lt_two_pow (by omega)
    simpa using! h2
  | succ d ih =>
    obtain ⟨Td, hTd⟩ := ih
    obtain ⟨Mk, hMk⟩ := eventually_linear_le_two_pow (2 ^ (d + 1))
    let Mreq := max (d + 1) (max Td Mk)
    refine ⟨2 * Mreq, ?_⟩
    intro N hN
    have hN2 : Mreq * 2 ≤ N := by omega
    have hm : Mreq ≤ N / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr hN2
    have hm_e : d + 1 ≤ N / 2 := le_trans (le_max_left _ _) hm
    have hm_Td : Td ≤ N / 2 :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
    have hm_Mk : Mk ≤ N / 2 :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
    have hdiv : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
    have hmod : N % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hNle : N + 1 ≤ 2 * (N / 2 + 1) := by omega
    have hm2 : 2 * (N / 2) ≤ N := by omega
    have hIH : (N / 2 + 1) ^ d < 2 ^ (N / 2) := hTd (N / 2) hm_Td
    have hE : 2 ^ (d + 1) * (N / 2 + 1) ≤ 2 ^ (N / 2) := hMk (N / 2) hm_Mk
    have h1 : (N + 1) ^ (d + 1) ≤ (2 * (N / 2 + 1)) ^ (d + 1) :=
      Nat.pow_le_pow_left hNle (d + 1)
    have h2 : (2 * (N / 2 + 1)) ^ (d + 1) = 2 ^ (d + 1) * (N / 2 + 1) ^ (d + 1) := by
      rw [Nat.mul_pow]
    have h3 : (N / 2 + 1) ^ (d + 1) = (N / 2 + 1) ^ d * (N / 2 + 1) := by
      rw [pow_succ]
    have h4 : (N / 2 + 1) ^ d * (N / 2 + 1) < 2 ^ (N / 2) * (N / 2 + 1) :=
      Nat.mul_lt_mul_of_pos_right hIH (by omega)
    have h5 : 2 ^ (d + 1) * ((N / 2 + 1) ^ d * (N / 2 + 1)) <
        2 ^ (d + 1) * (2 ^ (N / 2) * (N / 2 + 1)) :=
      Nat.mul_lt_mul_of_pos_left h4 (by positivity)
    have h6 : 2 ^ (d + 1) * (2 ^ (N / 2) * (N / 2 + 1)) ≤
        2 ^ (N / 2) * 2 ^ (N / 2) := by
      have hEq : 2 ^ (d + 1) * (2 ^ (N / 2) * (N / 2 + 1)) =
          2 ^ (N / 2) * (2 ^ (d + 1) * (N / 2 + 1)) := by ring
      rw [hEq]
      exact Nat.mul_le_mul_left _ hE
    have h7 : 2 ^ (N / 2) * 2 ^ (N / 2) = 2 ^ (2 * (N / 2)) := by
      rw [← pow_add]
      congr 1
      omega
    have h8 : 2 ^ (2 * (N / 2)) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hm2
    calc (N + 1) ^ (d + 1) ≤ (2 * (N / 2 + 1)) ^ (d + 1) := h1
      _ = 2 ^ (d + 1) * (N / 2 + 1) ^ (d + 1) := h2
      _ = 2 ^ (d + 1) * ((N / 2 + 1) ^ d * (N / 2 + 1)) := by rw [h3]
      _ < 2 ^ (d + 1) * (2 ^ (N / 2) * (N / 2 + 1)) := h5
      _ ≤ 2 ^ (N / 2) * 2 ^ (N / 2) := h6
      _ = 2 ^ (2 * (N / 2)) := h7
      _ ≤ 2 ^ N := h8

/-- For any natural coefficient and degree, some `2 ^ N` exceeds `c * (N + 1) ^ d`. -/
theorem twoPow_not_eventually_polynomial (c d : ℕ) :
    ∃ N : ℕ, c * (N + 1) ^ d < 2 ^ N := by
  obtain ⟨T, hT⟩ := eventually_pow_lt_two_pow (c + d)
  refine ⟨max T 1, ?_⟩
  have hbase : 2 ≤ max T 1 + 1 := by omega
  have hc : c ≤ (max T 1 + 1) ^ c := by
    calc c ≤ 2 ^ c := (Nat.lt_two_pow_self).le
      _ ≤ (max T 1 + 1) ^ c := Nat.pow_le_pow_left hbase c
  have hsplit : (max T 1 + 1) ^ (c + d) = (max T 1 + 1) ^ c * (max T 1 + 1) ^ d := by
    rw [pow_add]
  have hle : c * (max T 1 + 1) ^ d ≤ (max T 1 + 1) ^ (c + d) := by
    rw [hsplit]
    exact Nat.mul_le_mul_right _ hc
  exact lt_of_le_of_lt hle (hT _ (le_max_left _ _))

/-- For Hermitian summands and a positive segment count, bounds the first-order product-formula
error by the tail-commutator sum times `|T| ^ 2 / (2 * r)`. -/
theorem twoState_first_order_error
    (N M r : ℕ) (H : Fin M → Operator (2 ^ N)) (T : ℝ)
    (hr : 0 < r) (hH : ∀ j, (H j).IsHermitian) :
    ‖pfFamily H T r - HamiltonianEvolution (∑ j, H j) T‖ ≤
      |T| ^ 2 / (2 * (r : ℝ)) * ∑ j : Fin M, ‖pfComm (finiteStrangTail H j) (H j)‖ :=
  trotterFirstOrderTailSum (2 ^ N) M r H T hr hH

/-- The first-order product-formula word has exactly `M * r` factors. -/
theorem twoState_first_order_word_length
    (N M r : ℕ) (H : Fin M → Operator (2 ^ N)) (T : ℝ) :
    (pfFamilyWord H T r).length = M * r := by
  unfold pfFamilyWord
  simp [List.length_flatten, List.length_ofFn, Nat.mul_comm]

/-- The selected Strang word has positive segment count, length `2 * M * r`, unitary
interpretation, operator error at most `ε`, and conjugated-observable error at most `2 * ‖O‖
* ε`. -/
theorem twoState_selected_accuracy
    (N M : ℕ) (H : Fin M → Operator (2 ^ N)) (T ε : ℝ) (O : Operator (2 ^ N))
    (hH : ∀ j, (H j).IsHermitian) (hε : 0 < ε) :
    let r := finiteStrangSegments H T ε
    let w := finiteStrangWord H T r
    0 < r ∧ w.length = 2 * M * r ∧
      pfInterpret w ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ ∧
      ‖pfInterpret w - HamiltonianEvolution (∑ j, H j) T‖ ≤ ε ∧
      ‖Matrix.conjTranspose (pfInterpret w) * O * pfInterpret w -
        Matrix.conjTranspose (HamiltonianEvolution (∑ j, H j) T) * O *
          HamiltonianEvolution (∑ j, H j) T‖ ≤ 2 * ‖O‖ * ε :=
  finite_strang_selected_accuracy_and_observable (2 ^ N) M H T ε O hH hε

/-- Under the one- and two-body term-count bound, the Strang word has length `2 * M * r ≤ 2 *
oneTwoBodyTermCount N * r`. -/
theorem twoState_word_ledger
    (N M r : ℕ) (H : Fin M → Operator (2 ^ N)) (T : ℝ) (price : ℕ → ℕ)
    (hH : ∀ j, (H j).IsHermitian) (hr : 0 < r)
    (hM : M ≤ oneTwoBodyTermCount N) :
    let w := finiteStrangWord H T r
    w.length = 2 * M * r ∧ w.length ≤ 2 * oneTwoBodyTermCount N * r := by
  obtain ⟨_, hlen, _, _, _⟩ :=
    finite_strang_same_word_error_and_tariffs (2 ^ N) M r H T price hH hr
  refine ⟨hlen, ?_⟩
  rw [hlen]
  exact Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 hM)

/-- Collects the qubit basis cardinality, its doubling recurrence and linear lower bound, and
the failure of every natural polynomial to bound all basis dimensions. -/
theorem twoState_classical_obstruction (N : ℕ) :
    Fintype.card (Reg N) = 2 ^ N ∧
      twoStateDim (N + 1) = 2 * twoStateDim N ∧
      N + 1 ≤ twoStateDim N ∧
      (∀ c d : ℕ, ∃ N' : ℕ, c * (N' + 1) ^ d < 2 ^ N') :=
  ⟨(twoStateDim_eq_card N).symm, twoStateDim_succ N, twoStateDim_ge_succ N,
    twoPow_not_eventually_polynomial⟩

/-- Combines the selected Strang word's length, unitarity, and operator and observable error
bounds with the exponential qubit basis cardinality and growth statements. [Wiesner1996] -/
theorem twoState_finite_components
    (N M : ℕ) (H : Fin M → Operator (2 ^ N)) (T ε : ℝ) (O : Operator (2 ^ N))
    (hH : ∀ j, (H j).IsHermitian) (hε : 0 < ε) (hM : M ≤ oneTwoBodyTermCount N) :
    let r := finiteStrangSegments H T ε
    let w := finiteStrangWord H T r
    0 < r ∧ w.length = 2 * M * r ∧ w.length ≤ 2 * oneTwoBodyTermCount N * r ∧
      pfInterpret w ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ ∧
      ‖pfInterpret w - HamiltonianEvolution (∑ j, H j) T‖ ≤ ε ∧
      ‖Matrix.conjTranspose (pfInterpret w) * O * pfInterpret w -
        Matrix.conjTranspose (HamiltonianEvolution (∑ j, H j) T) * O *
          HamiltonianEvolution (∑ j, H j) T‖ ≤ 2 * ‖O‖ * ε ∧
      Fintype.card (Reg N) = 2 ^ N ∧
      twoStateDim (N + 1) = 2 * twoStateDim N ∧
      (∀ c d : ℕ, ∃ N' : ℕ, c * (N' + 1) ^ d < 2 ^ N') := by
  (try dsimp only)
  obtain ⟨hr, hlen, hu, herr, hobs⟩ :=
    finite_strang_selected_accuracy_and_observable (2 ^ N) M H T ε O hH hε
  refine ⟨hr, hlen, ?_, hu, herr, hobs, (twoStateDim_eq_card N).symm,
    twoStateDim_succ N, twoPow_not_eventually_polynomial⟩
  rw [hlen]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hM)

/-- The register assigning `k` qubits to each of `N` particles. -/
abbrev ParticleRegister (N k : ℕ) := Reg (N * k)

/-- The basis dimension `2 ^ (N * k)` of the discretized particle register. -/
def particleDim (N k : ℕ) : ℕ := 2 ^ (N * k)

/-- The particle dimension equals the cardinality of the particle register basis. -/
theorem particleDim_eq_card (N k : ℕ) :
    particleDim N k = Fintype.card (ParticleRegister N k) := by
  unfold particleDim ParticleRegister
  rw [card_reg]

/-- The equivalence between `k`-bit basis strings and the `2 ^ k` position labels. -/
def positionLabel (k : ℕ) : Reg k ≃ Fin (2 ^ k) := bitVecEquiv k

/-- The discrete kinetic energy `(p.val : ℝ) ^ 2 / (2 * mass)`. -/
def kineticEigenvalue {D : ℕ} (mass : ℝ) (p : Fin D) : ℝ :=
  (p.val : ℝ) ^ 2 / (2 * mass)

/-- The complex phase `exp(-i * r)` for real `r`. -/
def phaseVal (r : ℝ) : ℂ := NormedSpace.exp ((r : ℂ) * (-Complex.I))

/-- Each phase satisfies `star (phaseVal r) * phaseVal r = 1`. -/
theorem phaseVal_star_mul (r : ℝ) : star (phaseVal r) * phaseVal r = 1 := by
  unfold phaseVal
  rw [NormedSpace.star_exp]
  rw [← NormedSpace.exp_add]
  have hzero : star ((r : ℂ) * (-Complex.I)) + (r : ℂ) * (-Complex.I) = 0 := by
    have hconj : star ((r : ℂ) * (-Complex.I)) = (r : ℂ) * Complex.I := by
      rw [star_mul, star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj]
    ring
  rw [hzero, NormedSpace.exp_zero]

/-- The kinetic evolution phases `phaseVal (dt * lam i)` in the diagonalizing basis. -/
def kineticPhaseVec {D : ℕ} (lam : Fin D → ℝ) (dt : ℝ) : Fin D → ℂ :=
  fun i => phaseVal (dt * lam i)

/-- The potential evolution phases `phaseVal (dt * V i)` in the position basis. -/
def potentialPhaseVec {D : ℕ} (V : Fin D → ℝ) (dt : ℝ) : Fin D → ℂ :=
  fun i => phaseVal (dt * V i)

/-- The matrix `Fᴴ * diag(lam) * F` determined by a real kinetic spectrum and a supplied basis
matrix. -/
def kineticHamiltonian {D : ℕ} (F : Operator D) (lam : Fin D → ℝ) : Operator D :=
  Matrix.conjTranspose F * phaseDiag (fun i => (lam i : ℂ)) * F

/-- The matrix `Fᴴ * diag(exp(-i * dt * lam)) * F` for one kinetic layer. -/
def kineticLayer {D : ℕ} (F : Operator D) (lam : Fin D → ℝ) (dt : ℝ) : Operator D :=
  Matrix.conjTranspose F * phaseDiag (kineticPhaseVec lam dt) * F

/-- The diagonal Hamiltonian with real position potentials `V`. -/
def potentialHamiltonian {D : ℕ} (V : Fin D → ℝ) : Operator D :=
  phaseDiag (fun i => (V i : ℂ))

/-- The diagonal potential evolution matrix with phases `exp(-i * dt * V i)`. -/
def potentialLayer {D : ℕ} (V : Fin D → ℝ) (dt : ℝ) : Operator D :=
  phaseDiag (potentialPhaseVec V dt)

/-- The kinetic Hamiltonian is Hermitian for every basis matrix `F` and real spectrum. -/
theorem kineticHamiltonian_isHermitian {D : ℕ} (F : Operator D) (lam : Fin D → ℝ) :
    (kineticHamiltonian F lam).IsHermitian := by
  show (kineticHamiltonian F lam).conjTranspose = _
  unfold kineticHamiltonian
  simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, (phaseDiag_ofReal_isHermitian lam).eq]

/-- A real diagonal potential Hamiltonian is Hermitian. -/
theorem potentialHamiltonian_isHermitian {D : ℕ} (V : Fin D → ℝ) :
    (potentialHamiltonian V).IsHermitian := by
  unfold potentialHamiltonian
  exact phaseDiag_ofReal_isHermitian V

/-- Scalar multiplication of a diagonal matrix multiplies each of its diagonal entries by the
scalar. -/
theorem diag_smul {D : ℕ} (c : ℂ) (v : Fin D → ℂ) :
    c • phaseDiag v = phaseDiag (fun i => c * v i) := by
  ext i j
  unfold phaseDiag
  rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp [smul_eq_mul]
  · simp [h]

/-- A scalar multiplying a three-matrix product can be moved to its middle factor. -/
theorem smul_mul_mul {D : ℕ} (c : ℂ) (A B C : Operator D) :
    c • (A * B * C) = A * (c • B) * C := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]

/-- The conjugate transpose of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup {D : ℕ} {F : Operator D}
    (hF : F ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix.conjTranspose F ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  exact (Matrix.mem_unitaryGroup_iff' (A := F)).mp hF

/-- A kinetic layer is unitary when its supplied basis matrix is unitary. -/
theorem kineticLayer_mem_unitaryGroup {D : ℕ} (F : Operator D)
    (hF : F ∈ Matrix.unitaryGroup (Fin D) ℂ) (lam : Fin D → ℝ) (dt : ℝ) :
    kineticLayer F lam dt ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  unfold kineticLayer
  exact Submonoid.mul_mem (Matrix.unitaryGroup (Fin D) ℂ)
    (Submonoid.mul_mem (Matrix.unitaryGroup (Fin D) ℂ)
      (conjTranspose_mem_unitaryGroup hF)
      (phaseDiag_mem_unitaryGroup (kineticPhaseVec lam dt)
        (fun i => phaseVal_star_mul (dt * lam i))))
    hF

/-- Every real-potential phase layer is unitary. -/
theorem potentialLayer_mem_unitaryGroup {D : ℕ} (V : Fin D → ℝ) (dt : ℝ) :
    potentialLayer V dt ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  unfold potentialLayer
  exact phaseDiag_mem_unitaryGroup (potentialPhaseVec V dt)
    (fun i => phaseVal_star_mul (dt * V i))

/-- In a unitary basis, the kinetic layer equals the exact evolution of the kinetic Hamiltonian.
[Wiesner1996] -/
theorem kineticLayer_eq_evolution {D : ℕ} (F : Operator D)
    (hF : F ∈ Matrix.unitaryGroup (Fin D) ℂ) (lam : Fin D → ℝ) (dt : ℝ) :
    HamiltonianEvolution (kineticHamiltonian F lam) dt = kineticLayer F lam dt := by
  have hF1 : F * Matrix.conjTranspose F = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff (A := F)).mp hF
    simpa [Matrix.star_eq_conjTranspose] using! h
  have hF2 : Matrix.conjTranspose F * F = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff' (A := F)).mp hF
    simpa [Matrix.star_eq_conjTranspose] using! h
  have hunitFH : IsUnit (Matrix.conjTranspose F) :=
    ⟨⟨Matrix.conjTranspose F, F, hF2, hF1⟩, rfl⟩
  have hinv : (Matrix.conjTranspose F)⁻¹ = F := Matrix.inv_eq_left_inv hF1
  unfold HamiltonianEvolution kineticHamiltonian kineticLayer
  rw [smul_mul_mul]
  have hexp := Matrix.exp_conj (Matrix.conjTranspose F)
      ((-Complex.I * (dt : ℂ)) • phaseDiag (fun i => (lam i : ℂ))) hunitFH
  rw [hinv] at hexp
  rw [hexp]
  congr 1
  have hdiag : (-Complex.I * (dt : ℂ)) • phaseDiag (fun i => (lam i : ℂ)) =
      phaseDiag (fun i => (-Complex.I * (dt : ℂ)) * (lam i : ℂ)) := by
    unfold phaseDiag
    rw [← Matrix.diagonal_smul]
    simp [smul_eq_mul]
  rw [hdiag]
  unfold phaseDiag
  rw [Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  unfold kineticPhaseVec phaseVal
  congr 1
  push_cast
  ring_nf

/-- The potential layer equals the exact evolution of its real diagonal Hamiltonian.
[Wiesner1996] -/
theorem potentialLayer_eq_evolution {D : ℕ} (V : Fin D → ℝ) (dt : ℝ) :
    HamiltonianEvolution (potentialHamiltonian V) dt = potentialLayer V dt := by
  unfold HamiltonianEvolution potentialHamiltonian potentialLayer
  rw [diag_smul]
  unfold phaseDiag
  rw [Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  unfold potentialPhaseVec phaseVal
  congr 1
  push_cast
  ring_nf

/-- The two-term Hamiltonian family consisting of `K` followed by `V`. -/
def layeredHamiltonian {D : ℕ} (K V : Operator D) : Fin 2 → Operator D := ![K, V]

/-- For Hermitian `K` and `V`, the selected Strang word has length `4 * r`, is unitary, and
approximates the evolution of `K + V` within `ε`, with observable error at most `2 * ‖O‖ *
ε`. -/
theorem particle_selected_accuracy
    (N k : ℕ) (K V : Operator (2 ^ (N * k))) (T ε : ℝ) (O : Operator (2 ^ (N * k)))
    (hK : K.IsHermitian) (hV : V.IsHermitian) (hε : 0 < ε) :
    let H := layeredHamiltonian K V
    let r := finiteStrangSegments H T ε
    let w := finiteStrangWord H T r
    0 < r ∧ w.length = 2 * 2 * r ∧
      pfInterpret w ∈ Matrix.unitaryGroup (Fin (2 ^ (N * k))) ℂ ∧
      ‖pfInterpret w - HamiltonianEvolution (K + V) T‖ ≤ ε ∧
      ‖Matrix.conjTranspose (pfInterpret w) * O * pfInterpret w -
        Matrix.conjTranspose (HamiltonianEvolution (K + V) T) * O *
          HamiltonianEvolution (K + V) T‖ ≤ 2 * ‖O‖ * ε := by
  have hH : ∀ j, (layeredHamiltonian K V j).IsHermitian := by
    intro j
    fin_cases j
    · simpa [layeredHamiltonian] using! hK
    · simpa [layeredHamiltonian] using! hV
  have hsum : (∑ j : Fin 2, layeredHamiltonian K V j) = K + V := by
    simp [layeredHamiltonian, Fin.sum_univ_two]
  have hmain :=
    finite_strang_selected_accuracy_and_observable (2 ^ (N * k)) 2
      (layeredHamiltonian K V) T ε O hH hε
  (try dsimp only at hmain ⊢)
  rw [hsum] at hmain
  exact hmain

/-- One kinetic term plus the count of one- and two-body potential terms. -/
def particleTermCount (N : ℕ) : ℕ := 1 + oneTwoBodyTermCount N

/-- Under the particle term-count bound, the Strang word has length `2 * M * r ≤ 2 *
particleTermCount N * r`. -/
theorem particle_word_ledger
    (N k M r : ℕ) (H : Fin M → Operator (2 ^ (N * k))) (T : ℝ) (price : ℕ → ℕ)
    (hH : ∀ j, (H j).IsHermitian) (hr : 0 < r)
    (hM : M ≤ particleTermCount N) :
    let w := finiteStrangWord H T r
    w.length = 2 * M * r ∧ w.length ≤ 2 * particleTermCount N * r := by
  obtain ⟨_, hlen, _, _, _⟩ :=
    finite_strang_same_word_error_and_tariffs (2 ^ (N * k)) M r H T price hH hr
  refine ⟨hlen, ?_⟩
  rw [hlen]
  exact Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 hM)

/-- Adding one particle multiplies the particle basis dimension by `2 ^ k`. -/
theorem particleDim_succ (N k : ℕ) :
    particleDim (N + 1) k = 2 ^ k * particleDim N k := by
  unfold particleDim
  rw [Nat.succ_mul, pow_add]
  ring

/-- For `k ≥ 1`, every fixed natural polynomial in `N + 1` is exceeded by some particle basis
dimension. -/
theorem particleDim_not_polynomial (k : ℕ) (hk : 1 ≤ k) (c d : ℕ) :
    ∃ N : ℕ, c * (N + 1) ^ d < particleDim N k := by
  obtain ⟨N, hN⟩ := twoPow_not_eventually_polynomial c d
  refine ⟨N, lt_of_lt_of_le hN ?_⟩
  unfold particleDim
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right N (by omega))

/-- For positive particle number and word size and a unitary basis matrix, collects exact
kinetic and potential layers, selected Strang accuracy and length bounds, and exponential
register cardinality and growth. [Wiesner1996] -/
theorem particle_finite_components
    (N k : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (F : Operator (2 ^ (N * k))) (lam : Fin (2 ^ (N * k)) → ℝ)
    (V : Fin (2 ^ (N * k)) → ℝ) (T ε : ℝ) (O : Operator (2 ^ (N * k)))
    (hF : F ∈ Matrix.unitaryGroup (Fin (2 ^ (N * k))) ℂ) (hε : 0 < ε) :
    let K := kineticHamiltonian F lam
    let Vh := potentialHamiltonian V
    let H := layeredHamiltonian K Vh
    let r := finiteStrangSegments H T ε
    let w := finiteStrangWord H T r
    Fintype.card (ParticleRegister N k) = particleDim N k ∧
      kineticLayer F lam (T / r) = HamiltonianEvolution K (T / r) ∧
      potentialLayer V (T / r) = HamiltonianEvolution Vh (T / r) ∧
      0 < r ∧ w.length = 2 * 2 * r ∧ w.length ≤ 2 * particleTermCount N * r ∧
      pfInterpret w ∈ Matrix.unitaryGroup (Fin (2 ^ (N * k))) ℂ ∧
      ‖pfInterpret w - HamiltonianEvolution (K + Vh) T‖ ≤ ε ∧
      ‖Matrix.conjTranspose (pfInterpret w) * O * pfInterpret w -
        Matrix.conjTranspose (HamiltonianEvolution (K + Vh) T) * O *
          HamiltonianEvolution (K + Vh) T‖ ≤ 2 * ‖O‖ * ε ∧
      particleDim (N + 1) k = 2 ^ k * particleDim N k ∧
      (∀ c d : ℕ, ∃ N' : ℕ, c * (N' + 1) ^ d < particleDim N' k) := by
  (try dsimp only)
  have hK : (kineticHamiltonian F lam).IsHermitian :=
    kineticHamiltonian_isHermitian F lam
  have hV : (potentialHamiltonian V).IsHermitian :=
    potentialHamiltonian_isHermitian V
  obtain ⟨hr, hlen, hu, herr, hobs⟩ :=
    particle_selected_accuracy N k (kineticHamiltonian F lam) (potentialHamiltonian V)
      T ε O hK hV hε
  have h2 : 2 ≤ particleTermCount N := by
    unfold particleTermCount oneTwoBodyTermCount
    have hge : 2 ≤ N * (N + 1) := by
      calc 2 = 1 * 2 := by norm_num
        _ ≤ N * (N + 1) := Nat.mul_le_mul hN (by omega)
    have hpos : 0 < N * (N + 1) / 2 := Nat.div_pos hge (by norm_num)
    omega
  have hledger : (finiteStrangWord (layeredHamiltonian (kineticHamiltonian F lam)
      (potentialHamiltonian V)) T (finiteStrangSegments (layeredHamiltonian
      (kineticHamiltonian F lam) (potentialHamiltonian V)) T ε)).length ≤
      2 * particleTermCount N *
        finiteStrangSegments (layeredHamiltonian (kineticHamiltonian F lam)
          (potentialHamiltonian V)) T ε := by
    rw [hlen]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h2)
  exact ⟨(particleDim_eq_card N k).symm, (kineticLayer_eq_evolution F hF lam (T / _)).symm,
    (potentialLayer_eq_evolution V (T / _)).symm, hr, hlen, hledger, hu, herr, hobs,
    particleDim_succ N k, particleDim_not_polynomial k hk⟩

end Qatlib.Papers.ManyBodySim96.MainResults
