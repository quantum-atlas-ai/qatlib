/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.MainTheorem.ShadowsDefs
import Qatlib.Papers.ClassShadows20.MainTheorem.GlobalShadowEffective
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ClassShadows20.LowerBound

namespace Qatlib.Papers.ClassShadows20.MainTheorem

open Qatlib
open Qatlib.Papers.ClassShadows20.MainTheorem
open Qatlib.Papers.ClassShadows20.MainTheorem.GlobalShadowEffective

set_option linter.unusedSectionVars false

theorem generalSampler_acceptanceMass (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) :
    acceptanceMass (generalSampler m b hm hb)
      = (m : ℝ) * ((2 ^ b : ℕ) : ℝ)⁻¹ := by
  rfl

theorem generalSampler_rejectionTail (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) :
    rejectionTail (generalSampler m b hm hb)
      = 1 - (m : ℝ) * ((2 ^ b : ℕ) : ℝ)⁻¹ := by
  rw [rejectionTail, generalSampler_acceptanceMass]

theorem generalSampler_uniform (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) (i : Fin m) :
    acceptedMemberProb (generalSampler m b hm hb) i /
        acceptanceMass (generalSampler m b hm hb)
      = 1 / (m : ℝ) := by
  rw [memberDecode_uniform]
  norm_num [generalSampler]

theorem generalSampler_fairBits (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) :
    (generalSampler m b hm hb).fairBits = b := rfl

theorem generalSampler_terminates (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) (t : ℕ) :
    rejectionTail (generalSampler m b hm hb) ^ t ≤ 1 :=
  rejection_terminates (generalSampler m b hm hb) t

theorem generalSampler_size_pos (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) :
    0 < (generalSampler m b hm hb).size := hm

theorem generalSampler_size_le (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) :
    (generalSampler m b hm hb).size ≤ 2 ^ (generalSampler m b hm hb).fairBits := hb

theorem basisPacking_separated (d : ℕ) (hd : 0 < d) :
    (basisPackingFamily d).Separated := by
  refine ⟨hd, ?_, ?_, ?_⟩
  · simp [basisPackingFamily]
  · intro i
    exact normalized_ket i
  · intro i j hij
    have hd' : i ≠ j := hij
    simp only [basisPackingFamily]
    rw [basis_distance d i j hd']

theorem basisPacking_size (d : ℕ) :
    (basisPackingFamily d).size = d := rfl

theorem theorem5_wrapper_with_packing {d : ℕ} (P : PackingFamily d)
    (hP : P.Separated) (N r : ℕ) (δ α : ℝ)
    (hr : 0 < r) (hrd : r ≤ d) (hα : 0 < α)
    (hallow : 0 < Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α)
    (hN : (N : ℝ) ≥ Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand P.size δ /
        Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α) :
    Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand P.size δ ≤
      (N : ℝ) * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α := by
  have hM : 1 ≤ P.size := by
    have hpos : 0 < P.size := hP.1
    omega
  exact theorem5_wrapper N P.size d r δ α hr hrd hα hallow hN

theorem theorem5_wrapper_basis_packing (d : ℕ) (hd : 0 < d)
    (N r : ℕ) (δ α : ℝ)
    (hr : 0 < r) (hrd : r ≤ d) (hα : 0 < α)
    (hallow : 0 < Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α)
    (hN : (N : ℝ) ≥ Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand d δ /
        Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α) :
    Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand d δ ≤
      (N : ℝ) * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α := by
  exact theorem5_wrapper_with_packing (basisPackingFamily d)
    (basisPacking_separated d hd) N r δ α hr hrd hα hallow hN

theorem clause6_endpoint :
    (∀ (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) (i : Fin m),
      acceptedMemberProb (generalSampler m b hm hb) i /
          acceptanceMass (generalSampler m b hm hb) = 1 / (m : ℝ)) ∧
    (∀ (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b),
      acceptanceMass (generalSampler m b hm hb)
        = (m : ℝ) * ((2 ^ b : ℕ) : ℝ)⁻¹) ∧
    (∀ (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b),
      rejectionTail (generalSampler m b hm hb)
        = 1 - (m : ℝ) * ((2 ^ b : ℕ) : ℝ)⁻¹) ∧
    (∀ (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b),
      (generalSampler m b hm hb).fairBits = b) ∧
    (∀ (m b : ℕ) (hm : 0 < m) (hb : m ≤ 2 ^ b) (t : ℕ),
      rejectionTail (generalSampler m b hm hb) ^ t ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m b hm hb i
    exact generalSampler_uniform m b hm hb i
  · intro m b hm hb
    exact generalSampler_acceptanceMass m b hm hb
  · intro m b hm hb
    exact generalSampler_rejectionTail m b hm hb
  · intro m b hm hb
    exact generalSampler_fairBits m b hm hb
  · intro m b hm hb t
    exact generalSampler_terminates m b hm hb t

theorem clause7_endpoint :
    (∀ (d : ℕ) (hd : 0 < d), (basisPackingFamily d).Separated) ∧
    (∀ (d : ℕ), (basisPackingFamily d).size = d) ∧
    (∀ {d : ℕ} (P : PackingFamily d) (hP : P.Separated) (N r : ℕ) (δ α : ℝ)
      (hr : 0 < r) (hrd : r ≤ d) (hα : 0 < α)
      (hallow : 0 < Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α)
      (hN : (N : ℝ) ≥ Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand P.size δ /
          Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α),
      Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperDemand P.size δ ≤
        (N : ℝ) * Qatlib.Papers.ClassShadows20.LowerBound.theorem5WrapperAllowance d r α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact basisPacking_separated d hd
  · intro d
    exact basisPacking_size d
  · intro d P hP N r δ α hr hrd hα hallow hN
    exact theorem5_wrapper_with_packing P hP N r δ α hr hrd hα hallow hN

end Qatlib.Papers.ClassShadows20.MainTheorem
