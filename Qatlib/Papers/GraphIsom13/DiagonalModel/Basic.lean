/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsom13.GiCost
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GraphIsom13.DiagonalModel

open Qatlib.Papers.GraphIsom13.GiCost

def cbsKet {N : ℕ} (s : IntStr N) : IntStr N → ℂ :=
  Pi.single s 1

def problemHamiltonian {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    Matrix (IntStr N) (IntStr N) ℂ :=
  Matrix.diagonal (fun s => (cost G G' s : ℂ))

theorem problemHamiltonian_mulVec_cbsKet {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (s : IntStr N) :
    problemHamiltonian G G' *ᵥ cbsKet s = (cost G G' s : ℂ) • cbsKet s := by
  unfold problemHamiltonian cbsKet
  rw [Matrix.diagonal_mulVec_single, mul_one]
  ext t
  by_cases h : t = s
  · subst h
    simp
  · simp [h]

def energies {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] : Finset ℕ :=
  Finset.univ.image (cost G G')

theorem energies_nonempty {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] : (energies G G').Nonempty := by
  unfold energies
  rw [Finset.image_nonempty]
  exact ⟨fun _ => ⟨0, Nat.pow_pos (by norm_num)⟩, Finset.mem_univ _⟩

def minimumCost {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] : ℕ :=
  (energies G G').min' (energies_nonempty G G')

theorem minimumCost_eq_zero_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    minimumCost G G' = 0 ↔ ∃ s : IntStr N, cost G G' s = 0 := by
  unfold minimumCost
  constructor
  · intro h
    have hmem : 0 ∈ energies G G' := by
      rw [← h]
      exact (energies G G').min'_mem (energies_nonempty G G')
    rw [energies, Finset.mem_image] at hmem
    obtain ⟨s, -, hs⟩ := hmem
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    have hle : (energies G G').min' (energies_nonempty G G') ≤ cost G G' s :=
      (energies G G').min'_le (cost G G' s)
        (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
    have hge : 0 ≤ (energies G G').min' (energies_nonempty G G') := Nat.zero_le _
    omega

theorem minimumCost_zero_iff_iso {N : ℕ}
    (G G' : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    minimumCost G G' = 0 ↔ Nonempty (G ≃g G') :=
  (minimumCost_eq_zero_iff G G').trans (gi_cop_zero_iff G G')

end Qatlib.Papers.GraphIsom13.DiagonalModel
