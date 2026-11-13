/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabEquiv04.MainResults.Model.HistoryConstruction
import Qatlib.Papers.AdiabEquiv04.MainResults.Model.SpectralBasics

/-!
# The initial circuit history vector

This module identifies the time-zero history vector with the all-zero total basis vector and
proves its normalization. The clock, input, and initial-clock penalties annihilate this vector,
and positivity of `Hinit` makes it a ground vector for the construction of
[AharonovEtAl2007Adiabatic].

## Main statements

* `gamma_zero`: the time-zero history vector is `zeroTotal`.
* `Hinit_isPositive`: the initial Hamiltonian has nonnegative Rayleigh expressions.
* `gamma0_isGroundVector`: the initial history vector is a ground vector.

## References

* [Aharonov et al., 2007][AharonovEtAl2007Adiabatic]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- The product of zero circuit gates is the identity matrix. -/
theorem prefixU_zero {n : ℕ} (gates : GateSeq n) :
    prefixU gates 0 = 1 := by
  simp [prefixU]

/-- The computational vector at time zero is the all-zero basis vector. -/
theorem alpha_zero {n : ℕ} (gates : GateSeq n) : alpha gates 0 = zeroBasis n := by
  simp [alpha, prefixU_zero]

/-- The total basis vector supported on the all-zero computational and clock configurations. -/
def zeroTotal (n L : ℕ) : Vector (TotalBasis n L) :=
  fun p => if p = ((fun _ => 0), (fun _ => 0)) then 1 else 0

/-- The all-zero total basis vector has squared norm one. -/
theorem normSq_zeroTotal (n L : ℕ) : normSq (zeroTotal n L) = 1 := by
  classical
  unfold normSq zeroTotal
  rw [Finset.sum_eq_single ((fun _ => 0), (fun _ => 0))]
  · simp
  · intro b _ hb
    have hp : b ≠ ((fun _ => 0), (fun _ => 0)) := hb
    simp [hp]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The time-zero history vector equals the all-zero total basis vector. -/
theorem gamma_zero (n L : ℕ) (gates : GateSeq n) :
    gamma (L := L) gates ⟨0, Nat.zero_lt_succ L⟩ = zeroTotal n L := by
  classical
  funext p
  have hlc : legalClock L 0 = (fun _ => 0) := by
    funext i
    simp [legalClock]
  have halpha : alpha gates 0 = zeroBasis n := alpha_zero gates
  simp only [gamma, hlc, halpha, zeroTotal]
  by_cases h1 : p.1 = (fun _ => 0)
  · by_cases h2 : p.2 = (fun _ => 0)
    · have hp : p = ((fun _ => 0), (fun _ => 0)) := Prod.ext h1 h2
      simp [zeroBasis, hp]
    · have hp : p ≠ ((fun _ => 0), (fun _ => 0)) := by
        intro h; exact h2 (congrArg Prod.snd h)
      simp [zeroBasis, h2, hp]
  · have hp : p ≠ ((fun _ => 0), (fun _ => 0)) := by
      intro h; exact h1 (congrArg Prod.fst h)
    simp [zeroBasis, h1, hp]

/-- Multiplication of a vector by a finite sum of matrices equals the sum of the individual
matrix-vector products. -/
theorem finset_sum_mulVec {κ : Type} {ι : Type} [Fintype ι]
    (s : Finset κ) (f : κ → Matrix ι ι ℂ) (ψ : Vector ι) :
    (∑ k ∈ s, f k) *ᵥ ψ = ∑ k ∈ s, f k *ᵥ ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, Matrix.add_mulVec, ih]

/-- The initial-clock penalty annihilates the time-zero history vector. -/
theorem Hclockinit_mulVec_gamma0 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    Hclockinit n L hL2 *ᵥ gamma (L := L) gates ⟨0, Nat.zero_lt_succ L⟩ = 0 := by
  classical
  rw [gamma_zero]
  funext p
  unfold Hclockinit
  rw [basisProj_mulVec]
  by_cases h : (p.2 ⟨0, by omega⟩) = 1
  · have hp : p ≠ ((fun _ => 0), (fun _ => 0)) := by
      intro hp
      have h0 : p.2 ⟨0, by omega⟩ = 0 := by rw [hp]
      omega
    simp [h, zeroTotal, hp]
  · simp [h]

/-- The input penalty annihilates the time-zero history vector. -/
theorem Hinput_mulVec_gamma0 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    Hinput n L hL2 *ᵥ gamma (L := L) gates ⟨0, Nat.zero_lt_succ L⟩ = 0 := by
  classical
  rw [gamma_zero]
  unfold Hinput
  rw [finset_sum_mulVec]
  apply Finset.sum_eq_zero
  intro q _
  funext p
  rw [basisProj_mulVec]
  by_cases h : (p.1 q = 1 ∧ p.2 ⟨0, by omega⟩ = 0)
  · obtain ⟨h1, h2⟩ := h
    have hp : p ≠ ((fun _ => 0), (fun _ => 0)) := by
      intro hp
      have hq : p.1 q = 0 := by rw [hp]
      omega
    simp [h1, h2, zeroTotal, hp]
  · simp [h]

/-- The clock penalty annihilates the time-zero history vector. -/
theorem Hclock_mulVec_gamma0 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    Hclock n L hL2 *ᵥ gamma (L := L) gates ⟨0, Nat.zero_lt_succ L⟩ = 0 := by
  classical
  rw [gamma_zero]
  unfold Hclock
  rw [finset_sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  funext p
  rw [basisProj_mulVec]
  by_cases h : (p.2 ⟨i.val, by omega⟩ = 0 ∧ p.2 ⟨i.val + 1, by omega⟩ = 1)
  · obtain ⟨h1, h2⟩ := h
    have hp : p ≠ ((fun _ => 0), (fun _ => 0)) := by
      intro hp
      have hb : p.2 ⟨i.val + 1, by omega⟩ = 0 := by rw [hp]
      omega
    simp [h1, h2, zeroTotal, hp]
  · simp [h]

/-- The initial Hamiltonian annihilates the time-zero history vector. -/
theorem Hinit_mulVec_gamma0 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    (Hinit n L hL2).mat *ᵥ gamma (L := L) gates ⟨0, Nat.zero_lt_succ L⟩ = 0 := by
  unfold Hinit
  simp only
  rw [Matrix.add_mulVec, Matrix.add_mulVec,
    Hclockinit_mulVec_gamma0 n L hL2 gates,
    Hinput_mulVec_gamma0 n L hL2 gates,
    Hclock_mulVec_gamma0 n L hL2 gates]
  simp

/-- The Rayleigh expression of the initial Hamiltonian is nonnegative on every vector. -/
theorem Hinit_isPositive (n L : ℕ) (hL2 : 2 ≤ L) :
    IsPositive (Hinit n L hL2).mat := by
  unfold Hinit
  simp only
  refine ((basisProj_isPositive _).add
    (IsPositive.finset_sum _ (fun _ _ => basisProj_isPositive _))).add
    (IsPositive.finset_sum _ (fun _ _ => basisProj_isPositive _))

/-- The time-zero history vector has Rayleigh expression zero for the initial Hamiltonian. -/
theorem rayleigh_Hinit_gamma0 (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    rayleigh (Hinit n L hL2).mat
      (gamma (L := L) gates ⟨0, Nat.zero_lt_succ L⟩) = 0 := by
  unfold rayleigh
  rw [Hinit_mulVec_gamma0]
  simp

/-- The normalized time-zero history vector is a ground vector of the initial Hamiltonian. See
[AharonovEtAl2007Adiabatic]. -/
theorem gamma0_isGroundVector (n L : ℕ) (hL2 : 2 ≤ L) (gates : GateSeq n) :
    IsGroundVector (Hinit n L hL2)
      (gamma (L := L) gates ⟨0, Nat.zero_lt_succ L⟩) := by
  refine ⟨?_, ?_⟩
  · rw [gamma_zero]
    exact isNormalized_basisKet _
  · intro φ _
    rw [rayleigh_Hinit_gamma0]
    exact Hinit_isPositive n L hL2 φ

end Qatlib.Papers.AdiabEquiv04.MainResults.Model
