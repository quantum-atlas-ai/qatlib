/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DQIOptim24.MainResults.Source.Definitions
public import Qatlib.Concepts.CodingDecoding.DecoderCapacity.Basic

@[expose] public section


set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIOptim24.MainResults

open Qatlib.Papers.DQIOptim24.MainResults.Source

/-- `2` is prime.  Recorded as an instance so that `ZMod 2` is a field when the
Frozen decoder-capacity module is instantiated at `𝔽₂`. -/
instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- `2ℓ < d⊥` implies the Frozen notion of a separated kernel for the linear
syndrome map `Bᵀ` at radius `ℓ` (paper §8.1, pages 19 and 21). -/
theorem kernelSeparated_of_minDistance
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (d L : ℕ)
    (hd : IsMinDistance B d) (hL : 2 * L < d) :
    Qatlib.Concepts.CodingDecoding.DecoderCapacity.KernelSeparated
      (syndromeLin B) L := by
  intro z hz hz0
  have hz' : syndrome B z = 0 := hz
  have hw : d ≤ weight z := hd.1 z hz0 hz'
  simp only [weight] at hw ⊢
  omega

/-- The syndrome map `Bᵀ` is injective on errors of weight at most `ℓ` when
`2ℓ < d⊥` (paper §8.1, low-weight uniqueness; Frozen
`DecoderCapacity.lowWeight_injective`). -/
theorem syndrome_injective_on_lowWeight
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (d L : ℕ)
    (hd : IsMinDistance B d) (hL : 2 * L + 1 < d) :
    Set.InjOn (syndromeLin B) {y : Fin m → ZMod 2 | weight y ≤ L} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsep := kernelSeparated_of_minDistance B d L hd (by omega)
  have h := Qatlib.Concepts.CodingDecoding.DecoderCapacity.lowWeight_injective
    (ZMod 2) (Fin m) (Fin n) (syndromeLin B) L hsep
  simpa [weight] using h

/-- Consequence used in the norm computation: if both errors have weight at
most `ℓ` and they share a syndrome, then they coincide. -/
theorem syndrome_eq_imp_eq_of_weight_le
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (d L : ℕ)
    (hd : IsMinDistance B d) (hL : 2 * L + 1 < d)
    {y y' : Fin m → ZMod 2} (hy : weight y ≤ L) (hy' : weight y' ≤ L)
    (h : syndrome B y = syndrome B y') : y = y' := by
  have hinj := syndrome_injective_on_lowWeight B d L hd hL
  have hlin : syndromeLin B y = syndromeLin B y' := h
  exact hinj hy hy' hlin

end Qatlib.Papers.DQIOptim24.MainResults
