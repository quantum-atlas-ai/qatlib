/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SlowHamSim26.Amplification.Definitions

@[expose] public section

/-!
# Modular subtraction on the truncated Floquet register

Lemma 5.1 of arXiv:2608.17653v1 uses the unique representative in
`{-L+1,…,L}` and embeds the smaller register in the larger one
without changing its signed index.
-/

set_option autoImplicit false

open Qatlib.Papers.SlowHamSim26.FourierTrunc
open Qatlib.Papers.SlowHamSim26.Amplification

namespace Qatlib.Papers.SlowHamSim26.FourierTrunc

/-- Each Floquet register index labels an integer in the source interval. -/
theorem floquetIndexVal_mem {L : ℕ} (i : Fin (2 * L)) :
    floquetIndexVal L i ∈ Set.Icc (-(L : ℤ) + 1) (L : ℤ) := by
  have hi : (i : ℤ) < 2 * (L : ℤ) := by exact_mod_cast i.isLt
  have h₀ : 0 ≤ (i : ℤ) := by positivity
  change -(L : ℤ) + 1 ≤ floquetIndexVal L i ∧ floquetIndexVal L i ≤ (L : ℤ)
  unfold floquetIndexVal
  omega

/-- The register entry selected by modular reduction is in the source
interval and is congruent to the input, as required in Lemma 5.1. -/
theorem wrapIndex_spec {L : ℕ} (i₀ : Fin (2 * L)) (x : ℤ) :
    floquetIndexVal L (wrapIndex i₀ x) ∈ Set.Icc (-(L : ℤ) + 1) (L : ℤ) ∧
      (x - (-(L : ℤ) + 1)) % (2 * (L : ℤ)) =
        (floquetIndexVal L (wrapIndex i₀ x) - (-(L : ℤ) + 1)) % (2 * (L : ℤ)) := by
  refine ⟨floquetIndexVal_mem _, ?_⟩
  have hN : (0 : ℤ) < 2 * (L : ℤ) := by
    have hi : (i₀ : ℤ) < 2 * (L : ℤ) := by exact_mod_cast i₀.isLt
    have h₀ : 0 ≤ (i₀ : ℤ) := by positivity
    omega
  set m := (x - (-(L : ℤ) + 1)) % (2 * (L : ℤ))
  have hm : 0 ≤ m := Int.emod_nonneg _ hN.ne'
  have he : floquetIndexVal L (wrapIndex i₀ x) = m - (L : ℤ) + 1 := by
    change (m.toNat : ℤ) - (L : ℤ) + 1 = _
    rw [Int.toNat_of_nonneg hm]
  rw [he, show m - (L : ℤ) + 1 - (-(L : ℤ) + 1) = m by ring]
  exact (Int.emod_emod _ _).symm

/-- The source embedding from `D^L` to `D^{4L}` preserves the signed
Floquet index. -/
theorem floquetIndexVal_embedIndex (L : ℕ) (j : Fin (2 * L)) :
    floquetIndexVal (4 * L) (embedIndex L j) = floquetIndexVal L j := by
  simp only [floquetIndexVal, embedIndex, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

end Qatlib.Papers.SlowHamSim26.FourierTrunc
