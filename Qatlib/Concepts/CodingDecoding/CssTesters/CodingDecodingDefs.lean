/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
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

def steaneRow (k : Fin 3) : Fin 7 → ZMod 2 :=
  match k with
  | 0 => fun i => if i = 0 then 1 else if i = 3 then 1 else if i = 4 then 1 else if i = 6 then 1 else 0
  | 1 => fun i => if i = 1 then 1 else if i = 3 then 1 else if i = 5 then 1 else if i = 6 then 1 else 0
  | 2 => fun i => if i = 2 then 1 else if i = 4 then 1 else if i = 5 then 1 else if i = 6 then 1 else 0

def steaneH : Matrix (Fin 3) (Fin 7) (ZMod 2) := fun k i => steaneRow k i

def steaneCol (i : Fin 7) : Fin 3 → ZMod 2 := fun k => steaneRow k i

theorem steaneH_mul_transpose : steaneH * steaneHᵀ = 0 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide

def steaneData : CssData (Fin 7) (Fin 3) (Fin 3) where
  hX := steaneH
  hZ := steaneH
  hcompat := steaneH_mul_transpose

theorem steaneH_col0 (k : Fin 3) : steaneH k 0 = if k = 0 then 1 else 0 := by
  fin_cases k <;> decide

theorem steaneH_col1 (k : Fin 3) : steaneH k 1 = if k = 1 then 1 else 0 := by
  fin_cases k <;> decide

theorem steaneH_col2 (k : Fin 3) : steaneH k 2 = if k = 2 then 1 else 0 := by
  fin_cases k <;> decide

theorem steaneH_mulVecLin_e0 : steaneH.mulVecLin (Pi.single (0 : Fin 7) (1 : ZMod 2))
    = Pi.single (0 : Fin 3) (1 : ZMod 2) := by
  funext k
  simp [Matrix.mulVec, dotProduct, steaneH_col0, Pi.single_apply]

theorem steaneH_mulVecLin_e1 : steaneH.mulVecLin (Pi.single (1 : Fin 7) (1 : ZMod 2))
    = Pi.single (1 : Fin 3) (1 : ZMod 2) := by
  funext k
  simp [Matrix.mulVec, dotProduct, steaneH_col1, Pi.single_apply]

theorem steaneH_mulVecLin_e2 : steaneH.mulVecLin (Pi.single (2 : Fin 7) (1 : ZMod 2))
    = Pi.single (2 : Fin 3) (1 : ZMod 2) := by
  funext k
  simp [Matrix.mulVec, dotProduct, steaneH_col2, Pi.single_apply]

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

theorem steaneH_rank : Matrix.rank steaneH = 3 := by
  classical
  rw [Matrix.rank, steaneH_range_eq_top, finrank_top, Module.finrank_fin_fun]

theorem steaneData_encodedQubits : steaneData.encodedQubits = 1 := by
  classical
  show (Fintype.card (Fin 7) - Matrix.rank steaneH - Matrix.rank steaneH) = 1
  rw [steaneH_rank]
  norm_num

theorem steaneCol_ne_zero (i : Fin 7) : steaneCol i ≠ 0 := by
  fin_cases i <;> decide

theorem steaneCol_injective : ∀ i j : Fin 7, steaneCol i = steaneCol j → i = j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

def unitLabel {ι : Type*} [DecidableEq ι] (a : ι) : ι → ZMod 2 := fun k => if k = a then 1 else 0

def steaneSingle (i : Fin 7) : Fin 7 → ZMod 2 := unitLabel i

def steaneColIdx (u : Fin 3 → ZMod 2) : Fin 7 :=
  if u = steaneCol 0 then 0
  else if u = steaneCol 1 then 1
  else if u = steaneCol 2 then 2
  else if u = steaneCol 3 then 3
  else if u = steaneCol 4 then 4
  else if u = steaneCol 5 then 5
  else 6

theorem steaneColIdx_col (i : Fin 7) : steaneColIdx (steaneCol i) = i := by
  fin_cases i <;> decide

theorem steaneCol_or_zero : ∀ u : Fin 3 → ZMod 2,
    (∃ i : Fin 7, u = steaneCol i) ∨ u = 0 := by decide

theorem steaneColIdx_ne_zero (u : Fin 3 → ZMod 2) (hu : u ≠ 0) :
    steaneCol (steaneColIdx u) = u := by
  rcases steaneCol_or_zero u with ⟨i, hi⟩ | hz
  · subst hi
    rw [steaneColIdx_col i]
  · exact absurd hz hu

def steaneCorrX (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : Fin 7 → ZMod 2 :=
  if η.2 = 0 then 0 else steaneSingle (steaneColIdx η.2)

def steaneCorrZ (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : Fin 7 → ZMod 2 :=
  if η.1 = 0 then 0 else steaneSingle (steaneColIdx η.1)

def steaneCorr (η : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) : PauliLabel (Fin 7) :=
  (steaneCorrX η, steaneCorrZ η)

def steaneDecoder : RecoveryProgram steaneData where
  corr := steaneCorr
  decodeTime := fun _ => 3

def steaneFamily : CssFamily where
  N := fun _ => 7
  mX := fun _ => 3
  mZ := fun _ => 3
  code := fun _ => steaneData

def steaneResidualX (F : Finset (Fin 7)) : Fin 7 → ZMod 2 := fun k => if k ∈ F then 1 else 0

def steaneRoundGadget : GadgetSpec steaneData where
  kind := .syndromeRound
  locations := 7
  space := 7
  time := 3
  ideal := (0, 0)
  residual := fun F => (steaneResidualX F, 0)

def steaneNoiseLaw (ζ : ℕ) (p : ℝ) (F : Finset (Fin ζ)) : ℝ :=
  p ^ F.card * (1 - p) ^ (ζ - F.card)

end Qatlib.Concepts.CodingDecoding.CssTesters
