/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.DecoderCapacity.DecoderDefs
public import Mathlib.FieldTheory.Finiteness

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.CodingDecoding.DecoderCapacity

/-- The syndrome map is injective on the errors correctly recovered by the decoder. -/
theorem correctErrors_injective {E S : Type*} [DecidableEq E]
    (syndrome : E → S) (decode : S → E) (errors : Finset E) :
    Set.InjOn syndrome (correctErrors syndrome decode errors : Set E) := by
  intro a ha b hb hab
  have ha' : decode (syndrome a) = a := (Finset.mem_filter.mp ha).2
  have hb' : decode (syndrome b) = b := (Finset.mem_filter.mp hb).2
  exact ha'.symm.trans ((congrArg decode hab).trans hb')

/-- The number of correctly decoded errors is at most the cardinality of the syndrome range,
expressed using its dimension over `K`. -/
theorem decoder_capacity
    (K ι κ : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [Fintype κ]
    (syndrome : (ι → K) →ₗ[K] (κ → K))
    (decode : (κ → K) → (ι → K)) (errors : Finset (ι → K)) :
    (correctErrors syndrome decode errors).card ≤
      Fintype.card K ^ Module.finrank K (LinearMap.range syndrome) := by
  classical
  let : Fintype (LinearMap.range syndrome) := Fintype.ofFinite _
  let encode : ↥(correctErrors syndrome decode errors) → LinearMap.range syndrome :=
    fun e => ⟨syndrome e, LinearMap.mem_range_self syndrome e⟩
  have encode_injective : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    exact correctErrors_injective syndrome decode errors a.property b.property
      (congrArg Subtype.val hab)
  have hcard : (correctErrors syndrome decode errors).card ≤
      Fintype.card (LinearMap.range syndrome) := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective encode encode_injective
  calc
    (correctErrors syndrome decode errors).card ≤
        Fintype.card (LinearMap.range syndrome) := hcard
    _ = Fintype.card K ^ Module.finrank K (LinearMap.range syndrome) :=
      Module.card_eq_pow_finrank

/-- The Hamming weight of a difference is at most the sum of the two Hamming weights. -/
theorem hammingNorm_sub_le {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι]
    (a b : ι → K) :
    hammingNorm (a - b) ≤ hammingNorm a + hammingNorm b := by
  calc
    hammingNorm (a - b) = hammingDist b a := by
      rw [hammingDist_eq_hammingNorm]
      congr 1
      ext i
      simp [sub_eq_add_neg, add_comm]
    _ ≤ hammingDist b 0 + hammingDist 0 a := hammingDist_triangle b 0 a
    _ = hammingNorm a + hammingNorm b := by simp [Nat.add_comm]

/-- Kernel separation implies that the syndrome map is injective on errors of Hamming weight at
most `radius`. -/
theorem lowWeight_injective
    (K ι κ : Type*) [Field K] [DecidableEq K] [Fintype ι]
    (syndrome : (ι → K) →ₗ[K] (κ → K)) (radius : ℕ)
    (separated : KernelSeparated syndrome radius) :
    Set.InjOn syndrome {e | hammingNorm e ≤ radius} := by
  intro a ha b hb hab
  change hammingNorm a ≤ radius at ha
  change hammingNorm b ≤ radius at hb
  have hker : syndrome (a - b) = 0 := by rw [map_sub, hab, sub_self]
  by_contra hne
  have hlarge := separated (a - b) hker (sub_ne_zero.mpr hne)
  have hsmall : hammingNorm (a - b) ≤ 2 * radius := by
    calc
      hammingNorm (a - b) ≤ hammingNorm a + hammingNorm b := hammingNorm_sub_le a b
      _ ≤ radius + radius := Nat.add_le_add ha hb
      _ = 2 * radius := (two_mul radius).symm
  exact (not_lt_of_ge hsmall) hlarge

end Qatlib.Concepts.CodingDecoding.DecoderCapacity
