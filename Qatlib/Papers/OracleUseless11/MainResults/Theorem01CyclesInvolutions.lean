/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OracleUseless11.MainResults.CycleClasses
import Qatlib.Papers.OracleUseless11.MainResults.ClassicalTranscript

set_option backward.isDefEq.respectTransparency false

/-!
# Cycles Versus Fixed-Point-Free Involutions: Classical Indistinguishability and One-Query Quantum Separation

This module formalizes Section 2.1 (Theorems 1 and 2) of Harrow and Rosenbaum:
no classical query algorithm can distinguish uniformly random `N`-cycles from
uniformly random fixed-point-free involutions with unbounded error regardless of
the number of queries, whereas the one-query pair-transition probabilities
separate the two permutation classes for `N ≥ 3`.

## Main definitions

* `cycleAnswerModel`, `involutionAnswerModel`: classical answer models for `N`-cycles and fixed-point-free involutions.
* `pairClassProb`: joint probability that a uniformly random class element maps `x ↦ z` and `x' ↦ z'`.

## Main statements

* `theorem1_no_classical_unbounded_error`: Theorem 1, classical indistinguishability with unbounded error for any query count.
* `theorem2_one_query_separation`: Theorem 2, existence of a separating pair-transition matrix element for `3 ≤ N`.

## References

* [Harrow and Rosenbaum, 2011][HarrowRosenbaum2011], Section 2.1, Theorems 1 and 2, pp. 2--3.
-/

namespace Qatlib.Papers.OracleUseless11.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The class `CYC` of `N`-cycles is closed under conjugation. -/
theorem isFullCycle_conj (σ π : Equiv.Perm Y) :
    IsFullCycle π ↔ IsFullCycle (σ * π * σ⁻¹) := by
  constructor
  · rintro ⟨hc, hs⟩
    exact ⟨hc.conj, by rw [Equiv.Perm.support_conj, hs, Finset.map_univ_equiv]⟩
  · intro h
    have h2 : IsFullCycle (σ⁻¹ * (σ * π * σ⁻¹) * (σ⁻¹)⁻¹) :=
      ⟨h.1.conj, by rw [Equiv.Perm.support_conj, h.2, Finset.map_univ_equiv]⟩
    have heq : σ⁻¹ * (σ * π * σ⁻¹) * (σ⁻¹)⁻¹ = π := by group
    rwa [heq] at h2

/-- Every `N`-cycle moves every point (its support is everything). -/
theorem isFullCycle_free {π : Equiv.Perm Y} (h : IsFullCycle π) (x : Y) : π x ≠ x := by
  intro hx
  have hmem : x ∉ π.support := by simp [Equiv.Perm.mem_support, hx]
  rw [h.2] at hmem
  exact hmem (Finset.mem_univ x)

/-- Fixed-point-free involutions are closed under conjugation. -/
theorem isFixedPointFreeInvolution_conj (σ π : Equiv.Perm Y) :
    IsFixedPointFreeInvolution π ↔ IsFixedPointFreeInvolution (σ * π * σ⁻¹) := by
  constructor
  · rintro ⟨hsq, hfree⟩
    refine ⟨?_, fun x hx => ?_⟩
    · calc (σ * π * σ⁻¹) * (σ * π * σ⁻¹) = σ * (π * π) * σ⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    · have hs : π.support = Finset.univ := by
        ext y
        simp [Equiv.Perm.mem_support, hfree]
      have hmem : x ∈ (σ * π * σ⁻¹).support := by
        rw [Equiv.Perm.support_conj, hs, Finset.map_univ_equiv]
        exact Finset.mem_univ x
      exact Equiv.Perm.mem_support.mp hmem hx
  · intro h
    have h2 : IsFixedPointFreeInvolution (σ⁻¹ * (σ * π * σ⁻¹) * (σ⁻¹)⁻¹) := by
      refine ⟨?_, fun x hx => ?_⟩
      · calc (σ⁻¹ * (σ * π * σ⁻¹) * (σ⁻¹)⁻¹) * (σ⁻¹ * (σ * π * σ⁻¹) * (σ⁻¹)⁻¹)
            = σ⁻¹ * ((σ * π * σ⁻¹) * (σ * π * σ⁻¹)) * (σ⁻¹)⁻¹ := by group
          _ = 1 := by rw [h.1]; group
      · have hx' : (σ⁻¹ * (σ * π * σ⁻¹) * (σ⁻¹)⁻¹) x = x := hx
        have hπ : π x = x := by
          simpa [Equiv.Perm.mul_apply] using hx'
        exact h.2 (σ x) (by simp [Equiv.Perm.mul_apply, hπ])
    have heq : σ⁻¹ * (σ * π * σ⁻¹) * (σ⁻¹)⁻¹ = π := by group
    rwa [heq] at h2

/-- The answer law of a uniformly random `N`-cycle: uniform on `[N] ∖ {x}`. -/
theorem cycleAnswerLaw_eq_uniform {N : ℕ} [Nonempty {π : Equiv.Perm (Fin N) // IsFullCycle π}]
    (hN : 2 ≤ N) (x : Fin N) :
    classAnswerLaw (IsFullCycle (Y := Fin N)) x = uniformOffDiag (by simpa using hN) x :=
  classAnswerLaw_eq_uniformOffDiag IsFullCycle isFullCycle_conj
    (fun _ h => isFullCycle_free h) (by simpa using hN) x

/-- The answer law of a uniformly random fixed-point-free involution: uniform on
`[N] ∖ {x}`. -/
theorem involutionAnswerLaw_eq_uniform {N : ℕ}
    [Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π}]
    (hN : 2 ≤ N) (x : Fin N) :
    classAnswerLaw (IsFixedPointFreeInvolution (Y := Fin N)) x
      = uniformOffDiag (by simpa using hN) x :=
  classAnswerLaw_eq_uniformOffDiag IsFixedPointFreeInvolution isFixedPointFreeInvolution_conj
    (fun _ h => h.2) (by simpa using hN) x

/-- The classical answer model of the cycle class. -/
noncomputable def cycleAnswerModel (N : ℕ)
    [Nonempty {π : Equiv.Perm (Fin N) // IsFullCycle π}] (_hN : 2 ≤ N) : AnswerModel N :=
  ⟨fun x => classAnswerLaw (IsFullCycle (Y := Fin N)) x⟩

/-- The classical answer model of the involution class. -/
noncomputable def involutionAnswerModel (N : ℕ)
    [Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π}] (_hN : 2 ≤ N) :
    AnswerModel N :=
  ⟨fun x => classAnswerLaw (IsFixedPointFreeInvolution (Y := Fin N)) x⟩

/-- **The two classes are classically indistinguishable.** Both answer laws are the
uniform law on `[N] ∖ {x}` (paper §2.1, p. 2). -/
theorem cycleAnswerModel_eq_involutionAnswerModel (N : ℕ)
    [Nonempty {π : Equiv.Perm (Fin N) // IsFullCycle π}]
    [Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π}]
    (hN : 2 ≤ N) :
    (cycleAnswerModel N hN).law = (involutionAnswerModel N hN).law := by
  funext x
  show classAnswerLaw (IsFullCycle (Y := Fin N)) x
      = classAnswerLaw (IsFixedPointFreeInvolution (Y := Fin N)) x
  rw [cycleAnswerLaw_eq_uniform hN, involutionAnswerLaw_eq_uniform hN]

/-- **Theorem 1 (p. 2).** Classical algorithms cannot distinguish cycles from
fixed-point-free involutions with unbounded error, using any number of queries. -/
theorem theorem1_no_classical_unbounded_error (N : ℕ)
    [Nonempty {π : Equiv.Perm (Fin N) // IsFullCycle π}]
    [Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π}]
    (hN : 2 ≤ N) :
    ¬ ∃ (k : ℕ) (A : AdaptiveClassicalAlg N) (D : (Fin k → Fin N) → Bool),
        1 / 2 < acceptProb (cycleAnswerModel N hN) A k D ∧
        1 / 2 < 1 - acceptProb (involutionAnswerModel N hN) A k D := by
  rintro ⟨k, A, D, h1, h2⟩
  exact not_both_win (fun x => congrFun (cycleAnswerModel_eq_involutionAnswerModel N hN) x)
    A k D ⟨h1, h2⟩

-- Theorem 2: a separating matrix element of the one-copy encoding

/-- Probability, for a uniformly random member `π` of the class `P`, that `π x = z` and
`π x' = z'`. -/
noncomputable def pairClassProb {N : ℕ} (P : Equiv.Perm (Fin N) → Prop) (x x' z z' : Fin N) : ℝ :=
  (Fintype.card {π : Equiv.Perm (Fin N) // P π ∧ π x = z ∧ π x' = z'} : ℝ) /
    (Fintype.card {π : Equiv.Perm (Fin N) // P π} : ℝ)

/-- **Theorem 2 (p. 2), in matrix-element form.** The one-query encoding separates the
cycle class from the involution class for `3 ≤ N`. -/
theorem theorem2_one_query_separation (N : ℕ)
    [Nonempty {π : Equiv.Perm (Fin N) // IsFullCycle π}]
    [Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π}]
    (hN : 3 ≤ N) :
    ∃ (x x' z z' : Fin N),
      pairClassProb (IsFullCycle (Y := Fin N)) x x' z z'
        ≠ pairClassProb (IsFixedPointFreeInvolution (Y := Fin N)) x x' z z' := by
  obtain ⟨⟨π₀, hπ₀⟩⟩ :=
    (inferInstance : Nonempty {π : Equiv.Perm (Fin N) // IsFixedPointFreeInvolution π})
  let x : Fin N := ⟨0, by omega⟩
  let z : Fin N := π₀ x
  have hxz : z ≠ x := hπ₀.2 x
  have hπ₀_z : π₀ z = x := by
    simpa [Equiv.Perm.mul_apply] using
      congrArg (fun σ : Equiv.Perm (Fin N) => σ x) hπ₀.1
  have hInvPos : 0 < pairClassProb (IsFixedPointFreeInvolution (Y := Fin N)) x z z x := by
    apply div_pos
    · exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨⟨π₀, hπ₀, rfl, hπ₀_z⟩⟩)
    · exact Nat.cast_pos.mpr Fintype.card_pos
  have hEmpty : IsEmpty {π : Equiv.Perm (Fin N) //
      IsFullCycle π ∧ π x = z ∧ π z = x} := by
    refine ⟨?_⟩
    rintro ⟨π, hcyc, hx, hz⟩
    have hcard : 0 < (((Finset.univ : Finset (Fin N)).erase x).erase z).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxz, Finset.mem_univ z⟩),
        Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_fin]
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
    have hyx : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
    have hyz : y ≠ z := (Finset.mem_erase.mp hy).1
    obtain ⟨k, hk⟩ := hcyc.1.sameCycle (isFullCycle_free hcyc x) (isFullCycle_free hcyc y)
    have hpow (σ : Equiv.Perm (Fin N)) (hσx : σ x = z) (hσz : σ z = x) (m : ℕ) :
        ((σ ^ m) x = x ∨ (σ ^ m) x = z) ∧ ((σ ^ m) z = x ∨ (σ ^ m) z = z) := by
      induction m with
      | zero => simp
      | succ m ih =>
        constructor
        · rcases ih.1 with h | h <;> simp [pow_succ', Equiv.Perm.mul_apply, h, hσx, hσz]
        · rcases ih.2 with h | h <;> simp [pow_succ', Equiv.Perm.mul_apply, h, hσx, hσz]
    have hix : π⁻¹ x = z := Equiv.Perm.inv_eq_iff_eq.mpr hz.symm
    have hiz : π⁻¹ z = x := Equiv.Perm.inv_eq_iff_eq.mpr hx.symm
    have horbit : (π ^ k) x = x ∨ (π ^ k) x = z := by
      cases k with
      | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using (hpow π hx hz m).1
      | negSucc m =>
        simpa only [zpow_negSucc, ← inv_pow] using (hpow π⁻¹ hix hiz (m + 1)).1
    rcases horbit with h | h
    · exact hyx (hk.symm.trans h)
    · exact hyz (hk.symm.trans h)
  have hCycZero : pairClassProb (IsFullCycle (Y := Fin N)) x z z x = 0 := by
    have hcard := Fintype.card_eq_zero_iff.mpr hEmpty
    have hCycPos : (0 : ℝ) <
        (Fintype.card {π : Equiv.Perm (Fin N) // IsFullCycle π} : ℝ) :=
      Nat.cast_pos.mpr Fintype.card_pos
    exact (div_eq_iff hCycPos.ne').mpr (by rw [hcard, Nat.cast_zero, zero_mul])
  exact ⟨x, z, z, x, by linarith⟩

end Qatlib.Papers.OracleUseless11.MainResults
