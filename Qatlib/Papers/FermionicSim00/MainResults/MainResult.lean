/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionHubbard

/-!
# Jordan-Wigner identities and hopping evolution

`source_main_result_jordan_wigner` packages the Pauli-word realization, canonical
anticommutation relations, adjoint relation, and vacuum annihilation for the fermionic matrices.
The module also defines `hoppingHamiltonian`, proves it is Hermitian for real coefficients, and
deduces unitary evolution and preservation of normalized states.

These constructions belong to the formalization of [OrtizEtAl2001].

## Main statements

* `source_main_result_jordan_wigner`: the collected Jordan-Wigner identities.
* `hoppingHamiltonian_isHermitian`: real weighted hopping sums are Hermitian.
* `hopping_evolution_preserves_normalized`: hopping evolution preserves normalization.

## References

* [Ortiz et al., 2001][OrtizEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermionicSim00.MainResults

/-- The Jordan-Wigner realization satisfies the Pauli-word formulas, all three canonical
anticommutation identities, the creation-annihilation adjoint relation, and annihilation of
the vacuum. [OrtizEtAl2001] -/
theorem source_main_result_jordan_wigner (n : ℕ) :
    (∀ i : Fin n, annihilation i = jwPauliWord i ∧ creation i = (jwPauliWord i)ᴴ) ∧
    (∀ i j : Fin n,
      annihilation i * creation j + creation j * annihilation i
          = (if i = j then (1 : Matrix (Reg n) (Reg n) ℂ) else 0) ∧
      annihilation i * annihilation j + annihilation j * annihilation i = 0 ∧
      creation i * creation j + creation j * creation i = 0) ∧
    (∀ i : Fin n, creation i = (annihilation i)ᴴ) ∧
    (∀ i : Fin n, annihilation i *ᵥ Ket (ZeroStr n) = 0) := by
  obtain ⟨hcar, hadj, _hnum, _hpar, hjw, hvac⟩ := g1 n
  exact ⟨hjw, hcar, hadj, hvac⟩

/-- The sum of hopping from `j` to `i` and from `i` to `j` is Hermitian. See [OrtizEtAl2001]. -/
theorem jw_hopping_term_isHermitian (n : ℕ) (i j : Fin n) :
    (creation i * annihilation j + creation j * annihilation i).IsHermitian := by
  obtain ⟨_, hadj, _, _, _, _⟩ := g1 n
  show (creation i * annihilation j + creation j * annihilation i)ᴴ
      = creation i * annihilation j + creation j * annihilation i
  have hci : (creation i)ᴴ = annihilation i := by
    rw [hadj i, Matrix.conjTranspose_conjTranspose]
  have hcj : (creation j)ᴴ = annihilation j := by
    rw [hadj j, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hci, hcj]
  rw [hadj i, hadj j]
  exact add_comm _ _

/-- Distinct register configurations give distinct computational basis vectors. See
[OrtizEtAl2001]. -/
theorem jw_ket_injective {n : ℕ} :
    Function.Injective
      (Qatlib.Foundations.PureStateMath.Ket : Reg n → QState (Reg n)) := by
  intro x y h
  have hx : (1 : ℂ) = if x = y then 1 else 0 := by
    simpa [Qatlib.Foundations.PureStateMath.Ket] using! congrFun h x
  by_cases hxy : x = y
  · exact hxy
  · rw [if_neg hxy] at hx
    exact absurd hx one_ne_zero

/-- Every register state equals the sum of computational basis vectors weighted by its
amplitudes. See [OrtizEtAl2001]. -/
theorem jw_ket_expansion {n : ℕ} (ψ : QState (Reg n)) :
    (∑ x : Reg n, ψ x • Qatlib.Foundations.PureStateMath.Ket x) = ψ := by
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single y]
  · simp
  · intro x _ hxy
    simp [Ne.symm hxy]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- Annihilation clears an occupied bit with the Jordan-Wigner sign and gives zero if that bit
is unoccupied. See [OrtizEtAl2001]. -/
theorem jw_annihilation_action {n : ℕ} (i : Fin n) (x : Reg n) :
    annihilation i *ᵥ Qatlib.Foundations.PureStateMath.Ket x
      = if x i then
          jwSign i x •
            Qatlib.Foundations.PureStateMath.Ket
              (Function.update x i false)
        else 0 := by
  funext y
  simp only [Matrix.mulVec, dotProduct, annihilation,
    Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single x]
  · by_cases hx : x i
    · simp [hx, Qatlib.Foundations.PureStateMath.Ket]
    · simp [hx]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- The Jordan-Wigner annihilation Pauli words have zero anticommutator at every pair of
indices. See [OrtizEtAl2001]. -/
theorem jwPauliWord_anticommute {n : ℕ} (i j : Fin n) :
    jwPauliWord i * jwPauliWord j + jwPauliWord j * jwPauliWord i = 0 := by
  obtain ⟨hcar, _, _, _, hjw, _⟩ := g1 n
  rw [← (hjw i).1, ← (hjw j).1]
  exact (hcar i j).2.1

/-- The double sum of symmetric hopping terms weighted by the real coefficients `t i j`. -/
noncomputable def hoppingHamiltonian (n : ℕ) (t : Fin n → Fin n → ℝ) :
    Matrix (Reg n) (Reg n) ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (t i j : ℂ) • (creation i * annihilation j + creation j * annihilation i)

/-- A finite sum of Hermitian register matrices is Hermitian. -/
theorem isHermitian_finset_sum {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Matrix (Reg n) (Reg n) ℂ) (hf : ∀ i, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a).add ih

/-- The hopping Hamiltonian is Hermitian for every choice of real coefficients. See
[OrtizEtAl2001]. -/
theorem hoppingHamiltonian_isHermitian (n : ℕ) (t : Fin n → Fin n → ℝ) :
    (hoppingHamiltonian n t).IsHermitian := by
  unfold hoppingHamiltonian
  refine isHermitian_finset_sum Finset.univ (fun i => ∑ j : Fin n,
    (t i j : ℂ) • (creation i * annihilation j + creation j * annihilation i)) ?_
  intro i
  refine isHermitian_finset_sum Finset.univ (fun j =>
    (t i j : ℂ) • (creation i * annihilation j + creation j * annihilation i)) ?_
  intro j
  refine (jw_hopping_term_isHermitian n i j).smul ?_
  show star (t i j : ℂ) = (t i j : ℂ)
  simp

/-- Hamiltonian evolution generated by the hopping Hamiltonian is unitary at every real time.
See [OrtizEtAl2001]. -/
theorem hopping_evolution_unitary (n : ℕ) (t : ℝ) (c : Fin n → Fin n → ℝ) :
    HamiltonianEvolution (hoppingHamiltonian n c) t ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  hamiltonianEvolution_unitary (hoppingHamiltonian_isHermitian n c) t

/-- Evolution generated by the hopping Hamiltonian preserves normalization of register states.
See [OrtizEtAl2001]. -/
theorem hopping_evolution_preserves_normalized (n : ℕ) (t : ℝ)
    (c : Fin n → Fin n → ℝ) (ψ : QState (Reg n)) (hψ : Normalized ψ) :
    Normalized (ApplyGate (HamiltonianEvolution (hoppingHamiltonian n c) t) ψ) :=
  normalized_applyGate (hopping_evolution_unitary n t c) hψ

end Qatlib.Papers.FermionicSim00.MainResults
