/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# Five-Qubit Heisenberg Demonstration Circuit

This module formalizes the two-spin Heisenberg demonstration identities in
Section 8 ("An experimental implementation") of Temme et al. on quantum
Metropolis sampling. For the two-qubit ferromagnetic Heisenberg Hamiltonian
`heisenbergH2 = -(1/2) (X ⊗ X + Y ⊗ Y + Z ⊗ Z)`:

* adding the energy offset `(1/2) • 1` yields spectrum `{0, 2}` and exact
  time-`π / 2` unitary evolution equal to `swapGate` (Eq. (80));
* without the offset, time-`π / 2` evolution equals `swapGate` up to the
  unit-modulus global phase `e ^ (i π / 4)`;
* the acceptance-coin rotation sequence `R_y(-θ) · X · R_y(θ)` (Eq. (81)) has
  diagonal amplitude `sin θ` and off-diagonal amplitude `cos θ`.

## Main statements

* `source_W_gate_sequence` and `source_rotation_block`: gate decomposition and
  amplitudes of the temperature-encoding coin `R_y(-θ) · X · R_y(θ)` (Eq. (81)).
* `source_swap_evolution`: exact `SWAP` evolution at `t = π / 2` for the
  offset two-spin Heisenberg Hamiltonian (Eq. (80)).
* `source_swap_evolution_up_to_phase`: `SWAP` evolution up to a unit-modulus
  phase for the unshifted Hamiltonian `heisenbergH2` (Eqs. (79)-(80)).

## References

* [Temme et al., 2011][TemmeEtAl2011], Section 8, Eqs. (79)-(81).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.AcceptanceCoin.HeisenbergDemo

open Matrix
open Qatlib.Foundations.PureStateMath

/-- Single-qubit Pauli `X` matrix. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Single-qubit Pauli `Y` matrix. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Single-qubit Pauli `Z` matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Kronecker product of two single-qubit matrices on `Fin 2 × Fin 2`. -/
def kron2 (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => A p.1 q.1 * B p.2 q.2

/-- Two-spin ferromagnetic Heisenberg Hamiltonian (Eq. (79)). -/
noncomputable def heisenbergH2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (-(1 / 2 : ℂ)) • (kron2 pauliX pauliX + kron2 pauliY pauliY + kron2 pauliZ pauliZ)

/-- Two-qubit `SWAP` gate. -/
def swapGate : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- Single-qubit `Y`-rotation `R_y(θ) = exp(-i θ Y / 2)`. -/
noncomputable def rotY (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), (-(Real.sin (θ / 2)) : ℂ);
     (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]

/-- Action of a single-qubit gate on the second qubit of `Fin 2 × Fin 2`. -/
def kron2Map (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => A p.2 q.2 * (if p.1 = q.1 then 1 else 0)

/-- The Metropolis acceptance-coin unitary `W(θ) = R_y(-θ) · X · R_y(θ)` (Eq. (81)). -/
noncomputable def metropolisW (θ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kron2Map (rotY (-θ)) * kron2Map pauliX * kron2Map (rotY θ)

/-- Gate decomposition of `metropolisW` (Eq. (81)). -/
theorem source_W_gate_sequence (θ : ℝ) :
    metropolisW θ = kron2Map (rotY (-θ)) * kron2Map pauliX * kron2Map (rotY θ) := rfl

/-- The local `2 × 2` block `R_y(-θ) · X · R_y(θ)` has `(0, 0)` entry `sin θ`
and `(0, 1)` entry `cos θ`, encoding inverse temperature via `cos θ_β = e ^ (-β)`. -/
theorem source_rotation_block (θ : ℝ) :
    (rotY (-θ) * pauliX * rotY θ) 0 0 = (Real.sin θ : ℂ) ∧
    (rotY (-θ) * pauliX * rotY θ) 0 1 = (Real.cos θ : ℂ) := by
  have hsin : (Real.sin θ : ℂ) =
      2 * ((Real.sin (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)) := by
    have hθ : θ = 2 * (θ / 2) := by ring
    conv_lhs => rw [hθ, Real.sin_two_mul]
    push_cast; ring
  have hcos : (Real.cos θ : ℂ) =
      (Real.cos (θ / 2) : ℂ) ^ 2 - (Real.sin (θ / 2) : ℂ) ^ 2 := by
    have hθ : θ = 2 * (θ / 2) := by ring
    conv_lhs => rw [hθ, Real.cos_two_mul']
    push_cast; ring
  push_cast at hsin hcos
  constructor <;>
    simp [rotY, pauliX, Matrix.mul_apply, Fin.sum_univ_two, neg_div, Real.sin_neg, Real.cos_neg]
  · rw [hsin]; ring
  · rw [hcos]; ring

private noncomputable def singletProj : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - swapGate)

private lemma singletProj_idempotent : singletProj * singletProj = singletProj := by
  ext p q
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    norm_num [singletProj, swapGate, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma heisenbergH2_offset :
    heisenbergH2 + (1 / 2 : ℂ) • 1 = (2 : ℂ) • singletProj := by
  ext p q
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    norm_num [heisenbergH2, kron2, pauliX, pauliY, pauliZ, singletProj, swapGate]

private lemma singletProj_swap :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - (2 : ℂ) • singletProj = swapGate := by
  ext p q
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    norm_num [singletProj, swapGate]

private lemma exp_smul_idempotent
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hP : P * P = P) (c : ℂ) :
    NormedSpace.exp (c • P) = 1 + (Complex.exp c - 1) • P := by
  have hpow (k : ℕ) : (c • P) ^ (k + 1) = c ^ (k + 1) • P := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_smul_comm, hP, ← pow_succ]
  have hc : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * c ^ k) (Complex.exp c) := by
    simpa only [Complex.exp_eq_exp_ℂ, div_eq_mul_inv, mul_comm] using
      NormedSpace.expSeries_div_hasSum_exp c
  have htail : HasSum (fun k : ℕ => ((k + 1).factorial : ℂ)⁻¹ * c ^ (k + 1))
      (Complex.exp c - 1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hc
  have hmatrix : HasSum (fun k : ℕ => ((k + 1).factorial : ℂ)⁻¹ • (c • P) ^ (k + 1))
      ((Complex.exp c - 1) • P) := by
    simpa only [hpow, smul_smul] using htail.smul_const P
  have hseries : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ • (c • P) ^ k)
      (1 + (Complex.exp c - 1) • P) := by
    simpa only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one,
      pow_zero, one_smul] using
      hmatrix.sum_range_add (f := fun k : ℕ => (k.factorial : ℂ)⁻¹ • (c • P) ^ k) (k := 1)
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact hseries.tsum_eq

/-- With the additive offset `(1 / 2) • 1`, the time-`π / 2` evolution of
`heisenbergH2` equals `swapGate` exactly (Eq. (80)). -/
theorem source_swap_evolution (t : ℝ) (ht : t = Real.pi / 2) :
    HamiltonianEvolution (heisenbergH2 + (1 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
        t = swapGate := by
  subst ht
  rw [HamiltonianEvolution, heisenbergH2_offset, smul_smul]
  have hscalar : (-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * 2 =
      -(Complex.I * Real.pi) := by push_cast; ring
  have hexp : Complex.exp (-(Complex.I * Real.pi)) = -1 := by
    rw [Complex.exp_neg, mul_comm Complex.I, Complex.exp_mul_I]
    simp
  rw [hscalar, exp_smul_idempotent singletProj singletProj_idempotent, hexp]
  convert singletProj_swap using 1
  module

/-- Without the energy offset, the time-`π / 2` evolution of `heisenbergH2`
equals `swapGate` up to a unit-modulus global phase (Eqs. (79)-(80)). -/
theorem source_swap_evolution_up_to_phase :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧
      HamiltonianEvolution heisenbergH2 (Real.pi / 2) =
        φ • swapGate := by
  refine ⟨Complex.exp (Complex.I * (Real.pi / 4 : ℝ)),
    Complex.norm_exp_I_mul_ofReal _, ?_⟩
  have hsplit : (-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • heisenbergH2 =
      (-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
        (heisenbergH2 + (1 / 2 : ℂ) • 1) +
      (Complex.I * (Real.pi / 4 : ℝ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    push_cast
    module
  have hcomm : Commute
      ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
        (heisenbergH2 + (1 / 2 : ℂ) • 1))
      ((Complex.I * (Real.pi / 4 : ℝ)) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) :=
    ((Commute.one_right _).smul_right _)
  have hone (z : ℂ) :
      NormedSpace.exp (z • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) =
        Complex.exp z • 1 := by
    rw [exp_smul_idempotent 1 (one_mul 1)]
    module
  rw [HamiltonianEvolution, hsplit, Matrix.exp_add_of_commute _ _ hcomm, hone]
  change HamiltonianEvolution (heisenbergH2 + (1 / 2 : ℂ) • 1) (Real.pi / 2) * _ = _
  rw [source_swap_evolution _ rfl, Matrix.mul_smul, mul_one]

end Qatlib.Papers.QMetropolis11.AcceptanceCoin.HeisenbergDemo
