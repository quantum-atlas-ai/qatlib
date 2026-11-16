/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.FormAlgebra.PauliCommutantFin
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section


/-!
# The complete local Pauli family in an arbitrary energy basis

The proposal labels are exactly the `3 * n` pairs `(site, axis)`.  Every
proposal has its original Pauli normalization; there is no division by the
number of sites, axes, or Hilbert-space dimension.  The family contains the
actual `Y = i X Z`, even though only its `X` and `Z` members are needed for
the scalar joint-commutant theorem.

The energy-basis family is a unitary change of basis of this same fixed
physical family.  Its joint commutant is scalar for every unitary, including
unitaries that mix all sites.  No statement about a parent kernel or gap is
assumed here.
-/

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.GibbsSource.FormAlgebra



namespace Qatlib.Concepts.GibbsSource.SourceForms

set_option backward.isDefEq.respectTransparency false

open Matrix

/-- The computational basis of an `n`-qubit register, using the exact index
type of the existing Pauli commutant theorem. -/
def fullPauliDim (n : ℕ) : ℕ := Fintype.card (Fin n → ZMod 2)

/-- Full Pauli Dim eq two pow for the stated finite source data. -/
theorem fullPauliDim_eq_two_pow (n : ℕ) : fullPauliDim n = 2 ^ n := by
  simpa only [fullPauliDim, Fintype.card_fin] using card_regIndexEquiv (Fin n)

/-- Full Pauli Dim pos for the stated finite source data. -/
theorem fullPauliDim_pos (n : ℕ) : 0 < fullPauliDim n := by
  rw [fullPauliDim_eq_two_pow]
  exact pow_pos (by norm_num) _

/-- Even the empty register has its unique computational basis vector. -/
instance fullPauliIndex_nonempty (n : ℕ) : Nonempty (Fin (fullPauliDim n)) :=
  ⟨⟨0, fullPauliDim_pos n⟩⟩

/-- Full Pauli Dim ge two for the stated finite source data. -/
theorem fullPauliDim_ge_two (n : ℕ) (hn : 0 < n) : 2 ≤ fullPauliDim n := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ k =>
    rw [fullPauliDim_eq_two_pow, pow_succ]
    have hk : 1 ≤ (2 : ℕ) ^ k := Nat.succ_le_of_lt (pow_pos (by norm_num) _)
    simpa only [one_mul] using Nat.mul_le_mul_right 2 hk

/-- One of the three Pauli axes at one of the `n` physical sites. -/
abbrev FullPauliLabel (n : ℕ) := Fin n × Fin 3

/-- Full Pauli Label card for the stated finite source data. -/
theorem fullPauliLabel_card (n : ℕ) :
    Fintype.card (FullPauliLabel n) = 3 * n := by
  simp [FullPauliLabel, Nat.mul_comm]

/-- Actual local `X`, transported only by the fixed computational-basis
enumeration from register bit strings to `Fin (2^n)`. -/
noncomputable def fullPauliX (n : ℕ) (i : Fin n) :
    Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv (Fin n)))
    (cssPauliX (Pi.single i 1))

/-- Actual local `Z` in the same computational basis. -/
noncomputable def fullPauliZ (n : ℕ) (i : Fin n) :
    Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv (Fin n)))
    (cssPauliZ (Pi.single i 1))

/-- Actual local `Y = i X Z`, with the same unit Pauli normalization. -/
noncomputable def fullPauliY (n : ℕ) (i : Fin n) :
    Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ :=
  Complex.I • (fullPauliX n i * fullPauliZ n i)

/-- All `3n` equal-weight, unnormalized local Pauli proposals. -/
noncomputable def fullPauliFamily (n : ℕ) (a : FullPauliLabel n) :
    Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ :=
  if a.2 = 0 then fullPauliX n a.1
  else if a.2 = 1 then fullPauliY n a.1
  else fullPauliZ n a.1

/-- Axis zero of the complete local Pauli family is its original X operator. -/
@[simp] theorem fullPauliFamily_x (n : ℕ) (i : Fin n) :
    fullPauliFamily n (i, 0) = fullPauliX n i := by
  simp [fullPauliFamily]

/-- Axis one of the complete local Pauli family is its original Y operator. -/
@[simp] theorem fullPauliFamily_y (n : ℕ) (i : Fin n) :
    fullPauliFamily n (i, 1) = fullPauliY n i := by
  simp [fullPauliFamily]

/-- Axis two of the complete local Pauli family is its original Z operator. -/
@[simp] theorem fullPauliFamily_z (n : ℕ) (i : Fin n) :
    fullPauliFamily n (i, 2) = fullPauliZ n i := by
  simp [fullPauliFamily]

/-- Full Pauli X is Hermitian for the stated finite source data. -/
theorem fullPauliX_isHermitian (n : ℕ) (i : Fin n) :
    (fullPauliX n i).IsHermitian := by
  simpa only [fullPauliX, fullPauliDim, Matrix.coe_reindexAlgEquiv] using
    (cssPauliX_isHermitian (Pi.single i 1)).reindex (regIndexEquiv (Fin n))

/-- Full Pauli Z is Hermitian for the stated finite source data. -/
theorem fullPauliZ_isHermitian (n : ℕ) (i : Fin n) :
    (fullPauliZ n i).IsHermitian := by
  simpa only [fullPauliZ, fullPauliDim, Matrix.coe_reindexAlgEquiv] using
    (cssPauliZ_isHermitian (Pi.single i 1)).reindex (regIndexEquiv (Fin n))

/-- The local anticommutation phase certifies that the included `i X Z`
is the actual Hermitian Pauli `Y`. -/
theorem fullPauliZ_mul_X (n : ℕ) (i : Fin n) :
    fullPauliZ n i * fullPauliX n i =
      -(fullPauliX n i * fullPauliZ n i) := by
  have hreg : cssPauliZ (Pi.single i 1) * cssPauliX (Pi.single i 1) =
      -(cssPauliX (Pi.single i 1) * cssPauliZ (Pi.single i 1)) := by
    simpa [bitDot_single_left] using
      cssPauliZX_phase (Pi.single i 1) (Pi.single i 1)
  convert! congrArg (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv (Fin n))) hreg using 1 <;>
    simp only [map_mul, map_neg, fullPauliX, fullPauliZ, fullPauliDim]

/-- Full Pauli Y is Hermitian for the stated finite source data. -/
theorem fullPauliY_isHermitian (n : ℕ) (i : Fin n) :
    (fullPauliY n i).IsHermitian := by
  rw [fullPauliY, Matrix.IsHermitian, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, (fullPauliX_isHermitian n i).eq,
    (fullPauliZ_isHermitian n i).eq, fullPauliZ_mul_X]
  simp

/-- Full Pauli Family is Hermitian for the stated finite source data. -/
theorem fullPauliFamily_isHermitian (n : ℕ) (a : FullPauliLabel n) :
    (fullPauliFamily n a).IsHermitian := by
  unfold fullPauliFamily
  split
  · exact fullPauliX_isHermitian n a.1
  · split
    · exact fullPauliY_isHermitian n a.1
    · exact fullPauliZ_isHermitian n a.1

/-- The complete fixed physical family has only scalar common commutants.
This consumes the existing register-Pauli theorem, rather than reproving
Pauli spanning or hypercube connectivity. -/
theorem fullPauliFamily_commutant_scalar (n : ℕ)
    (Z : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)
    (hZ : ∀ a, Z * fullPauliFamily n a = fullPauliFamily n a * Z) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin (fullPauliDim n))
      (Fin (fullPauliDim n)) ℂ) := by
  apply singleSitePauli_commutant_scalar_fin (ι := Fin n)
  · intro i
    convert! hZ (i, 0) using 1
  · intro i
    convert! hZ (i, 2) using 1

/-- The original local Pauli proposals expressed in the energy basis `U`.
Using the star algebra automorphism keeps the complete unitary transport
explicit, without any special product structure on `U`. -/
noncomputable def fullPauliEnergyFamily (n : ℕ)
    (U : Matrix.unitaryGroup (Fin (fullPauliDim n)) ℂ)
    (a : FullPauliLabel n) :
    Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ :=
  Unitary.conjStarAlgAut ℂ _ (star U) (fullPauliFamily n a)

/-- Full Pauli Energy Family eq for the stated finite source data. -/
theorem fullPauliEnergyFamily_eq (n : ℕ)
    (U : Matrix.unitaryGroup (Fin (fullPauliDim n)) ℂ)
    (a : FullPauliLabel n) :
    fullPauliEnergyFamily n U a =
      (U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ *
        fullPauliFamily n a * U := by
  simp only [fullPauliEnergyFamily, Unitary.conjStarAlgAut_star_apply,
    Matrix.star_eq_conjTranspose]

/-- Full Pauli Energy Family is Hermitian for the stated finite source data. -/
theorem fullPauliEnergyFamily_isHermitian (n : ℕ)
    (U : Matrix.unitaryGroup (Fin (fullPauliDim n)) ℂ)
    (a : FullPauliLabel n) :
    (fullPauliEnergyFamily n U a).IsHermitian := by
  rw [fullPauliEnergyFamily_eq]
  exact Matrix.isHermitian_conjTranspose_mul_mul _ (fullPauliFamily_isHermitian n a)

/-- Transporting an energy-basis proposal back recovers the original fixed
local Pauli, with no rotation-dependent rescaling. -/
theorem fullPauliEnergyFamily_reconstruct (n : ℕ)
    (U : Matrix.unitaryGroup (Fin (fullPauliDim n)) ℂ)
    (a : FullPauliLabel n) :
    (U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) *
        fullPauliEnergyFamily n U a *
        (U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ =
      fullPauliFamily n a := by
  have hUU : (U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) *
      (U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  rw [fullPauliEnergyFamily_eq]
  calc
    _ = ((U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) *
        (U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ) *
        fullPauliFamily n a *
        ((U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) *
        (U : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)ᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = fullPauliFamily n a := by rw [hUU]; simp

/-- A complete Pauli family retains its scalar joint commutant in every
energy basis.  Only the actual commutation equations are premises. -/
theorem fullPauliEnergyFamily_commutant_scalar (n : ℕ)
    (U : Matrix.unitaryGroup (Fin (fullPauliDim n)) ℂ)
    (Z : Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ)
    (hZ : ∀ a, Z * fullPauliEnergyFamily n U a =
      fullPauliEnergyFamily n U a * Z) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin (fullPauliDim n))
      (Fin (fullPauliDim n)) ℂ) := by
  let e := Unitary.conjStarAlgAut ℂ
    (Matrix (Fin (fullPauliDim n)) (Fin (fullPauliDim n)) ℂ) (star U)
  have hpre : ∀ a, e.symm Z * fullPauliFamily n a =
      fullPauliFamily n a * e.symm Z := by
    intro a
    apply e.injective
    change e (e.symm Z * fullPauliFamily n a) =
      e (fullPauliFamily n a * e.symm Z)
    rw [map_mul, map_mul]
    change e (e.symm Z) * e (fullPauliFamily n a) =
      e (fullPauliFamily n a) * e (e.symm Z)
    rw [e.apply_symm_apply]
    exact hZ a
  obtain ⟨c, hc⟩ := fullPauliFamily_commutant_scalar n (e.symm Z) hpre
  refine ⟨c, ?_⟩
  have h := congrArg e hc
  simpa only [StarAlgEquiv.apply_symm_apply, map_smul, map_one] using h

end Qatlib.Concepts.GibbsSource.SourceForms
