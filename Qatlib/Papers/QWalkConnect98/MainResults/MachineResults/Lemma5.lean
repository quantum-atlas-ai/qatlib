/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.Connectivity
import Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing.SpectralGapProof
import Qatlib.Papers.QWalkConnect98.MainResults.MachineResults.MachineDefs

/-!
# A machine interface for regular graph connectivity

`walkAcceptProb` is the squared diagonal-to-diagonal entry of a projected walk on a
`GraphInstance`. Connected instances have acceptance bounded below after the mixing threshold,
while disconnected instances have zero acceptance.

An explicit polynomial step count packages these bounds into a `USTCONMachine` record with
logarithmic space and polynomial time bounds in the abstract interface. The final results
discharge the spectral-gap hypothesis using regularity. The formalization follows [Watrous1998].

## Main statements

* `lemma5_acceptance_connected_uncond`: positive acceptance for connected instances after the
  stated threshold.
* `lemma5_acceptance_disconnected`: zero acceptance for disconnected instances.
* `lemma5_dUSTCON_machine_uncond`: existence of a machine record with the required resource and
  acceptance bounds.

## References

* [Watrous, 1998][Watrous1998]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

open Finset
open Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator
open Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing
open Qatlib.Papers.QWalkConnect98.MainResults.Connectivity
open scoped BigOperators

set_option autoImplicit false
noncomputable section

/-- The squared entry of `walkQ ^ k` from the diagonal source state to the diagonal target state
of a graph instance. -/
def walkAcceptProb {d : ℕ} (I : GraphInstance d) (k : ℕ) : ℝ := by
  letI := I.instFintype
  letI := I.instDecEq
  letI := I.instDecRel
  exact ((walkQ I.G (d : ℝ) ^ k) (I.t, I.t) (I.s, I.s)) ^ 2

/-- The component spectral-gap predicate for the graph of an instance at its source vertex. -/
def InstanceSpectralGap {d : ℕ} (I : GraphInstance d) : Prop := by
  letI := I.instFintype
  letI := I.instDecEq
  letI := I.instDecRel
  exact SpectralGap I.G (d : ℝ) I.s

/-- The polynomial step count `(d * (d + 1) ^ 2 + 1) * (InstanceSize I + 1) ^ 4`. -/
private def stepCount (d : ℕ) (I : GraphInstance d) : ℕ :=
  (d * (d + 1) ^ 2 + 1) * (InstanceSize I + 1) ^ 4

/-- For a connected instance of degree at least two with the assumed spectral gap, acceptance
exceeds `1 / (4 * InstanceSize I ^ 2)` after the stated step threshold. -/
theorem lemma5_acceptance_connected {d : ℕ} (hd : 2 ≤ d) (I : GraphInstance d)
    (hconn : InstanceConnected I) (hg : InstanceSpectralGap I) (k : ℕ)
    (hk : ((d : ℝ) * ((d : ℝ) + 1) ^ 2 * (InstanceSize I : ℝ) ^ 2 / 8) *
      Real.log (2 * (InstanceSize I : ℝ)) ≤ (k : ℝ)) :
    1 / (4 * (InstanceSize I : ℝ) ^ 2) < walkAcceptProb I k := by
  letI := I.instFintype
  letI := I.instDecEq
  letI := I.instDecRel
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hreg : RegularDegree I.G (d : ℝ) := fun v => by
    have := I.regular v
    exact_mod_cast this
  have hgap : SpectralGap I.G (d : ℝ) I.s := hg
  exact corollary4_overlap I.G hreg hdR I.s I.t hconn hgap k hk

/-- A disconnected instance has zero walk acceptance probability at every step count. See
[Watrous1998]. -/
theorem lemma5_acceptance_disconnected {d : ℕ} (I : GraphInstance d) (k : ℕ)
    (h : ¬ InstanceConnected I) : walkAcceptProb I k = 0 := by
  letI := I.instFintype
  letI := I.instDecEq
  letI := I.instDecRel
  have hzero : ((walkQ I.G (d : ℝ) ^ k) (I.t, I.t) (I.s, I.s)) = 0 :=
    corollary4_disconnected I.G (d : ℝ) k I.s I.t h
  have hval : walkAcceptProb I k =
      ((walkQ I.G (d : ℝ) ^ k) (I.t, I.t) (I.s, I.s)) ^ 2 := rfl
  rw [hval, hzero]
  ring

/-- The `USTCONMachine` record with zero space function, step count `stepCount`, and walk
acceptance clipped above at one. -/
private def ustconMachine (d : ℕ) : USTCONMachine d where
  space := fun _ => 0
  steps := fun I => stepCount d I
  acceptProb := fun I => min 1 (walkAcceptProb I (stepCount d I))
  acceptProb_nonneg := fun I => by
    dsimp [walkAcceptProb]
    exact le_min (by norm_num) (sq_nonneg _)
  acceptProb_le_one := fun I => min_le_left _ _

/-- Assuming component spectral gaps for all degree-`d` instances and `2 ≤ d`, a
logarithmic-space, polynomial-time machine record has the stated positive acceptance on
connected instances and zero acceptance on disconnected instances. -/
theorem lemma5_dUSTCON_machine (d : ℕ) (hd : 2 ≤ d)
    (hgap : ∀ I : GraphInstance d, InstanceSpectralGap I) :
    ∃ M : USTCONMachine d, M.LogSpace ∧ M.PolyTime ∧
      (∀ I : GraphInstance d, InstanceConnected I →
        1 / (4 * (InstanceSize I : ℝ) ^ 2) < M.acceptProb I) ∧
      (∀ I : GraphInstance d, ¬ InstanceConnected I → M.acceptProb I = 0) := by
  refine ⟨ustconMachine d, ?_, ?_, ?_, ?_⟩
  · refine ⟨0, fun I => ?_⟩
    simp [ustconMachine]
  · refine ⟨d * (d + 1) ^ 2 + 5, fun I => ?_⟩
    show stepCount d I ≤ (InstanceSize I + 1) ^ (d * (d + 1) ^ 2 + 5)
    have hn2 : 2 ≤ InstanceSize I + 1 := by
      have h : 0 < InstanceSize I := by
        simpa [InstanceSize] using
          (@Fintype.card_pos_iff I.V I.instFintype).mpr ⟨I.s⟩
      omega
    have hK : d * (d + 1) ^ 2 + 1 ≤
        (InstanceSize I + 1) ^ (d * (d + 1) ^ 2 + 1) := by
      have h1 : d * (d + 1) ^ 2 + 1 < 2 ^ (d * (d + 1) ^ 2 + 1) :=
        Nat.lt_two_pow_self (n := d * (d + 1) ^ 2 + 1)
      have h2 : 2 ^ (d * (d + 1) ^ 2 + 1) ≤
          (InstanceSize I + 1) ^ (d * (d + 1) ^ 2 + 1) :=
        Nat.pow_le_pow_left hn2 (d * (d + 1) ^ 2 + 1)
      omega
    dsimp [stepCount]
    calc (d * (d + 1) ^ 2 + 1) * (InstanceSize I + 1) ^ 4
        ≤ (InstanceSize I + 1) ^ (d * (d + 1) ^ 2 + 1) * (InstanceSize I + 1) ^ 4 :=
          Nat.mul_le_mul_right _ hK
      _ = (InstanceSize I + 1) ^ (d * (d + 1) ^ 2 + 5) := by
          rw [← Nat.pow_add]
  · intro I hconn
    show 1 / (4 * (InstanceSize I : ℝ) ^ 2) <
      min 1 (walkAcceptProb I (stepCount d I))
    have hn1 : (1 : ℝ) ≤ (InstanceSize I : ℝ) := by
      have h : 0 < InstanceSize I := by
        simpa [InstanceSize] using
          (@Fintype.card_pos_iff I.V I.instFintype).mpr ⟨I.s⟩
      exact_mod_cast h
    have hden : (0 : ℝ) < 4 * (InstanceSize I : ℝ) ^ 2 := by positivity
    have hquarter : 1 / (4 * (InstanceSize I : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ hden]
      have hprod : (0 : ℝ) ≤ ((InstanceSize I : ℝ) - 1) * ((InstanceSize I : ℝ) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod]
    have hone : 1 / (4 * (InstanceSize I : ℝ) ^ 2) < 1 := by linarith
    have hk : ((d : ℝ) * ((d : ℝ) + 1) ^ 2 * (InstanceSize I : ℝ) ^ 2 / 8) *
        Real.log (2 * (InstanceSize I : ℝ)) ≤ ((stepCount d I : ℕ) : ℝ) := by
      have hnpos : (0 : ℝ) < (InstanceSize I : ℝ) := by linarith
      have hlog : Real.log (2 * (InstanceSize I : ℝ)) ≤ 2 * (InstanceSize I : ℝ) :=
        Real.log_le_self (by positivity)
      have hstep1 : ((d : ℝ) * ((d : ℝ) + 1) ^ 2 * (InstanceSize I : ℝ) ^ 2 / 8) *
          Real.log (2 * (InstanceSize I : ℝ))
          ≤ ((d : ℝ) * ((d : ℝ) + 1) ^ 2 * (InstanceSize I : ℝ) ^ 2 / 8) *
            (2 * (InstanceSize I : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have hstep2 : ((d : ℝ) * ((d : ℝ) + 1) ^ 2 * (InstanceSize I : ℝ) ^ 2 / 8) *
          (2 * (InstanceSize I : ℝ))
          = ((d : ℝ) * ((d : ℝ) + 1) ^ 2 / 4) * (InstanceSize I : ℝ) ^ 3 := by ring
      have hcube : (InstanceSize I : ℝ) ^ 3 ≤ ((InstanceSize I : ℝ) + 1) ^ 4 := by
        have h1 : (InstanceSize I : ℝ) ^ 3 ≤ ((InstanceSize I : ℝ) + 1) ^ 3 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 3
        have h2 : ((InstanceSize I : ℝ) + 1) ^ 3 ≤ ((InstanceSize I : ℝ) + 1) ^ 4 := by
          calc ((InstanceSize I : ℝ) + 1) ^ 3
              = ((InstanceSize I : ℝ) + 1) ^ 3 * 1 := by ring
            _ ≤ ((InstanceSize I : ℝ) + 1) ^ 3 * ((InstanceSize I : ℝ) + 1) := by
                apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = ((InstanceSize I : ℝ) + 1) ^ 4 := by ring
        linarith
      have hKmaj : (d : ℝ) * ((d : ℝ) + 1) ^ 2 / 4 ≤
          (d : ℝ) * ((d : ℝ) + 1) ^ 2 + 1 := by
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
        have hprod : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) + 1) ^ 2 :=
          mul_nonneg hd0 (sq_nonneg _)
        nlinarith [hprod]
      have hfinal : ((d : ℝ) * ((d : ℝ) + 1) ^ 2 / 4) * (InstanceSize I : ℝ) ^ 3
          ≤ ((d : ℝ) * ((d : ℝ) + 1) ^ 2 + 1) * ((InstanceSize I : ℝ) + 1) ^ 4 :=
        mul_le_mul hKmaj hcube (by positivity) (by positivity)
      have hcast : ((stepCount d I : ℕ) : ℝ) =
          ((d : ℝ) * ((d : ℝ) + 1) ^ 2 + 1) * ((InstanceSize I : ℝ) + 1) ^ 4 := by
        dsimp [stepCount]
        push_cast
        ring
      linarith
    have hacc := lemma5_acceptance_connected hd I hconn (hgap I) (stepCount d I) hk
    exact lt_min hone hacc
  · intro I hdis
    show min 1 (walkAcceptProb I (stepCount d I)) = 0
    rw [lemma5_acceptance_disconnected I (stepCount d I) hdis]
    exact min_eq_right zero_le_one

/-- Every graph instance of degree at least two satisfies `InstanceSpectralGap`. -/
private theorem instanceSpectralGap {d : ℕ} (hd : 2 ≤ d) (I : GraphInstance d) :
    InstanceSpectralGap I := by
  letI := I.instFintype
  letI := I.instDecEq
  letI := I.instDecRel
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hreg : RegularDegree I.G (d : ℝ) := fun v => by
    have := I.regular v
    exact_mod_cast this
  exact spectralGap_of_regular I.G hreg hdR I.s

/-- For a connected instance of degree at least two, acceptance exceeds `1 / (4 * InstanceSize I
^ 2)` after the stated step threshold. See [Watrous1998]. -/
theorem lemma5_acceptance_connected_uncond {d : ℕ} (hd : 2 ≤ d) (I : GraphInstance d)
    (hconn : InstanceConnected I) (k : ℕ)
    (hk : ((d : ℝ) * ((d : ℝ) + 1) ^ 2 * (InstanceSize I : ℝ) ^ 2 / 8) *
      Real.log (2 * (InstanceSize I : ℝ)) ≤ (k : ℝ)) :
    1 / (4 * (InstanceSize I : ℝ) ^ 2) < walkAcceptProb I k :=
  lemma5_acceptance_connected hd I hconn (instanceSpectralGap hd I) k hk

/-- For `2 ≤ d`, there exists a logarithmic-space, polynomial-time `USTCONMachine d` record with
acceptance greater than `1 / (4 * InstanceSize I ^ 2)` on connected instances and zero on
disconnected instances. See [Watrous1998]. -/
theorem lemma5_dUSTCON_machine_uncond (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : USTCONMachine d, M.LogSpace ∧ M.PolyTime ∧
      (∀ I : GraphInstance d, InstanceConnected I →
        1 / (4 * (InstanceSize I : ℝ) ^ 2) < M.acceptProb I) ∧
      (∀ I : GraphInstance d, ¬ InstanceConnected I → M.acceptProb I = 0) :=
  lemma5_dUSTCON_machine d hd (fun I => instanceSpectralGap hd I)

end

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
