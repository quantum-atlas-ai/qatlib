/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding

/-!
# Steane code and decoder data

The matrices `steaneH` and `steaneData` define the seven-qubit CSS code of [Steane1996], using
the same three-by-seven binary matrix for X and Z checks. The module proves row orthogonality,
rank three, one encoded qubit, and the nonzero and distinct column properties.

Column lookup defines the X and Z corrections in `steaneDecoder`. The remaining data specify a
constant code family, a syndrome-round gadget with explicit location and resource counts, and
Bernoulli fault-set weights.

## Main statements

* `steaneH_mul_transpose`: proves compatibility of the X and Z checks.
* `steaneH_rank`: gives rank three.
* `steaneData_encodedQubits`: gives one encoded qubit.
* `steaneColIdx_col`: verifies lookup of each parity-check column.
* `steaneDecoder`: defines syndrome-dependent Pauli corrections.
* `steaneRoundGadget`: records seven locations, space seven, and time three.

## References

* [Steane, 1996][Steane1996]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.CodingDecoding.CssTesters

open Matrix
open Qatlib
open scoped Classical

/-- One of the three binary parity-check rows used to define the seven-qubit Steane code. -/
def steaneRow (k : Fin 3) : Fin 7 → ZMod 2 :=
  match k with
  | 0 => fun i => if i = 0 then 1 else if i = 3 then 1 else if i = 4 then 1 else if i = 6 then 1 else 0
  | 1 => fun i => if i = 1 then 1 else if i = 3 then 1 else if i = 5 then 1 else if i = 6 then 1 else 0
  | 2 => fun i => if i = 2 then 1 else if i = 4 then 1 else if i = 5 then 1 else if i = 6 then 1 else 0

/-- The three-by-seven binary Steane parity-check matrix with rows `steaneRow`. -/
def steaneH : Matrix (Fin 3) (Fin 7) (ZMod 2) := fun k i => steaneRow k i

/-- The column of the Steane parity-check matrix indexed by qubit `i`. -/
def steaneCol (i : Fin 7) : Fin 3 → ZMod 2 := fun k => steaneRow k i

/-- The Steane parity-check rows are mutually orthogonal over `ZMod 2`. -/
theorem steaneH_mul_transpose : steaneH * steaneHᵀ = 0 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide

/-- The CSS data using `steaneH` for both X and Z checks, as in the seven-qubit code of
[Steane1996]. -/
def steaneData : CssData (Fin 7) (Fin 3) (Fin 3) where
  hX := steaneH
  hZ := steaneH
  hcompat := steaneH_mul_transpose

/-- The first column of the Steane parity-check matrix is the first standard basis vector. -/
theorem steaneH_col0 (k : Fin 3) : steaneH k 0 = if k = 0 then 1 else 0 := by
  fin_cases k <;> decide

/-- The second column of the Steane parity-check matrix is the second standard basis vector. -/
theorem steaneH_col1 (k : Fin 3) : steaneH k 1 = if k = 1 then 1 else 0 := by
  fin_cases k <;> decide

/-- The third column of the Steane parity-check matrix is the third standard basis vector. -/
theorem steaneH_col2 (k : Fin 3) : steaneH k 2 = if k = 2 then 1 else 0 := by
  fin_cases k <;> decide

/-- The Steane parity-check map sends the first seven-dimensional unit vector to the first
three-dimensional unit vector. -/
theorem steaneH_mulVecLin_e0 : steaneH.mulVecLin (Pi.single (0 : Fin 7) (1 : ZMod 2))
    = Pi.single (0 : Fin 3) (1 : ZMod 2) := by
  funext k
  simp [Matrix.mulVec, dotProduct, steaneH_col0, Pi.single_apply]

/-- The Steane parity-check map sends the second seven-dimensional unit vector to the second
three-dimensional unit vector. -/
theorem steaneH_mulVecLin_e1 : steaneH.mulVecLin (Pi.single (1 : Fin 7) (1 : ZMod 2))
    = Pi.single (1 : Fin 3) (1 : ZMod 2) := by
  funext k
  simp [Matrix.mulVec, dotProduct, steaneH_col1, Pi.single_apply]

/-- The Steane parity-check map sends the third seven-dimensional unit vector to the third
three-dimensional unit vector. -/
theorem steaneH_mulVecLin_e2 : steaneH.mulVecLin (Pi.single (2 : Fin 7) (1 : ZMod 2))
    = Pi.single (2 : Fin 3) (1 : ZMod 2) := by
  funext k
  simp [Matrix.mulVec, dotProduct, steaneH_col2, Pi.single_apply]

/-- The linear map defined by the Steane parity-check matrix is surjective. -/
theorem steaneH_range_eq_top : steaneH.mulVecLin.range = ⊤ := by
  classical
  refine eq_top_iff.2 fun v _ => ?_
  have hsplit : v = (v 0) • (Pi.single (0 : Fin 3) (1 : ZMod 2)) + (v 1) • (Pi.single (1 : Fin 3) (1 : ZMod 2))
      + (v 2) • (Pi.single (2 : Fin 3) (1 : ZMod 2)) := by
    funext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    fin_cases k <;> simp
  refine ⟨(v 0) • (Pi.single (0 : Fin 7) (1 : ZMod 2)) + (v 1) • (Pi.single (1 : Fin 7) (1 : ZMod 2))
      + (v 2) • (Pi.single (2 : Fin 7) (1 : ZMod 2)), ?_⟩
  simp only [map_add, map_smul]
  rw [steaneH_mulVecLin_e0, steaneH_mulVecLin_e1, steaneH_mulVecLin_e2]
  exact hsplit.symm

/-- The binary Steane parity-check matrix has rank three. -/
theorem steaneH_rank : Matrix.rank steaneH = 3 := by
  classical
  rw [Matrix.rank, steaneH_range_eq_top, finrank_top, Module.finrank_fin_fun]

/-- The Steane CSS data encodes one qubit. -/
theorem steaneData_encodedQubits : steaneData.encodedQubits = 1 := by
  classical
  show (Fintype.card (Fin 7) - Matrix.rank steaneH - Matrix.rank steaneH) = 1
  rw [steaneH_rank]
  norm_num

/-- Every column of the Steane parity-check matrix is nonzero. -/
theorem steaneCol_ne_zero (i : Fin 7) : steaneCol i ≠ 0 := by
  fin_cases i <;> decide

/-- Distinct Steane qubit indices have distinct parity-check columns. -/
theorem steaneCol_injective : ∀ i j : Fin 7, steaneCol i = steaneCol j → i = j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- The binary vector equal to one at `a` and zero at all other indices. -/
def unitLabel {ι : Type*} [DecidableEq ι] (a : ι) : ι → ZMod 2 := fun k => if k = a then 1 else 0

/-- The single-site binary label at Steane qubit `i`. -/
def steaneSingle (i : Fin 7) : Fin 7 → ZMod 2 := unitLabel i

/-- The column lookup index for a three-bit vector, with default value six. -/
def steaneColIdx (u : Fin 3 → ZMod 2) : Fin 7 :=
  if u = steaneCol 0 then 0
  else if u = steaneCol 1 then 1
  else if u = steaneCol 2 then 2
  else if u = steaneCol 3 then 3
  else if u = steaneCol 4 then 4
  else if u = steaneCol 5 then 5
  else 6

/-- Looking up a Steane column returns its original qubit index. -/
theorem steaneColIdx_col (i : Fin 7) : steaneColIdx (steaneCol i) = i := by
  fin_cases i <;> decide

/-- Every three-bit vector is either a Steane parity-check column or zero. -/
theorem steaneCol_or_zero : ∀ u : Fin 3 → ZMod 2,
    (∃ i : Fin 7, u = steaneCol i) ∨ u = 0 := by decide

/-- Every nonzero three-bit vector is the Steane column at its lookup index. -/
theorem steaneColIdx_ne_zero (u : Fin 3 → ZMod 2) (hu : u ≠ 0) :
    steaneCol (steaneColIdx u) = u := by
  rcases steaneCol_or_zero u with ⟨i, hi⟩ | hz
  · subst hi
    rw [steaneColIdx_col i]
  · exact absurd hz hu

/-- The Steane X correction obtained by looking up the second syndrome component, with zero
correction for a zero component. -/
def steaneCorrX (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : Fin 7 → ZMod 2 :=
  if η.2 = 0 then 0 else steaneSingle (steaneColIdx η.2)

/-- The Steane Z correction obtained by looking up the first syndrome component, with zero
correction for a zero component. -/
def steaneCorrZ (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : Fin 7 → ZMod 2 :=
  if η.1 = 0 then 0 else steaneSingle (steaneColIdx η.1)

/-- The Pauli correction pairing the Steane X and Z syndrome corrections. -/
def steaneCorr (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : PauliLabel (Fin 7) :=
  (steaneCorrX η, steaneCorrZ η)

/-- The Steane recovery program with correction `steaneCorr` and assigned decoding time three. -/
def steaneDecoder : RecoveryProgram steaneData where
  corr := steaneCorr
  decodeTime := fun _ => 3

/-- The constant family consisting of the seven-qubit Steane CSS data. -/
def steaneFamily : CssFamily where
  N := fun _ => 7
  mX := fun _ => 3
  mZ := fun _ => 3
  code := fun _ => steaneData

/-- The binary indicator vector of a set of faulty Steane qubits. -/
def steaneResidualX (F : Finset (Fin 7)) : Fin 7 → ZMod 2 := fun k => if k ∈ F then 1 else 0

/-- The Steane syndrome-round gadget with seven locations, space seven, time three, and X
residual given by the fault-set indicator. -/
def steaneRoundGadget : GadgetSpec steaneData where
  kind := .syndromeRound
  locations := 7
  space := 7
  time := 3
  ideal := (0, 0)
  residual := fun F => (steaneResidualX F, 0)

/-- The Bernoulli weight of a fault set among `ζ` locations with fault parameter `p`. -/
def steaneNoiseLaw (ζ : ℕ) (p : ℝ) (F : Finset (Fin ζ)) : ℝ :=
  p ^ F.card * (1 - p) ^ (ζ - F.card)

end Qatlib.Concepts.CodingDecoding.CssTesters
