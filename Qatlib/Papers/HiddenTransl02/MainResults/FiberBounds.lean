/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HiddenTransl02.MainResults.Section3.Lemma34Subset
public import Qatlib.Papers.HiddenTransl02.MainResults.FourierSamplingPair
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section

/-!
# Fiber weights and dimension bounds for hidden translation

The complement of the failed span-extension set has the count given by
Lemma 3.4. Frequencies in a fixed inner-product fiber receive the same
Fourier weight. The exact dimension expression gives the polynomial cap
on the associated sample-count expression.
-/

set_option autoImplicit false

open Qatlib.Papers.HiddenTransl02.MainResults.Section3
open Qatlib.Papers.HiddenTransl02.MainResults.FourierSamplingPair
open scoped Classical BigOperators

namespace Qatlib.Papers.HiddenTransl02.MainResults

/-- The set of vectors that escape the existing span in a nonzero fiber has the
cardinality guaranteed by the rearranged inequality of Lemma 3.4. -/
theorem card_compl_RSet_ge {p n : ℕ} [NeZero p] (hp : p.Prime) (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (hW : ¬ (MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) (p - 1) ≤ W))
    {k : ZMod p} (hk : k ≠ 0) :
    (VSet u k).card ≤ p * ((VSet u k) \ RSet u W k).card := by
  have hsub : RSet u W k ⊆ VSet u k := by
    intro v hv
    have hm := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.2.2⟩
  rw [Finset.card_sdiff_of_subset hsub, Nat.mul_sub]
  have h := lemma34_ratio hp u W hW hk
  have hmul : (p - 1) * (VSet u k).card = p * (VSet u k).card - (VSet u k).card := by
    rw [Nat.sub_mul, one_mul]
  rw [hmul] at h
  have hv : (VSet u k).card ≤ p * (VSet u k).card := by
    simpa using Nat.mul_le_mul_right (VSet u k).card hp.one_lt.le
  omega

/-- The true-bit sampling probabilities of Lemma 3.1 agree on a dot-product fiber. -/
theorem pairProb_const_on_dotU_fiber {p n : ℕ} [NeZero p]
    (e : (Fin n → ZMod p) ≃ AddChar (Fin n → ZMod p) ℂ)
    (hchar : ∀ y u, (e y) u = (ZMod.toCircle (dotU u y) : ℂ)) (u y y' : Fin n → ZMod p)
    (h : dotU u y = dotU u y') :
    pairProb e u y true = pairProb e u y' true := by
  apply pairProb_one_depends_only_on_character
  rw [hchar, hchar, h]

/-- The homogeneous-space dimension expression is bounded by the source polynomial. -/
theorem choose_dim_le_pow (n p : ℕ) :
    Nat.choose (n + p - 2) (p - 1) ≤ (n + p) ^ (p - 1) :=
  (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

/-- The sample-count expression of Theorem 3.5 is at most its polynomial budget. -/
theorem source_sample_count_le (n p : ℕ) :
    13 * p * Nat.choose (n + p - 2) (p - 1) ≤ 13 * p * (n + p) ^ (p - 1) :=
  Nat.mul_le_mul_left _ (choose_dim_le_pow n p)

end Qatlib.Papers.HiddenTransl02.MainResults
