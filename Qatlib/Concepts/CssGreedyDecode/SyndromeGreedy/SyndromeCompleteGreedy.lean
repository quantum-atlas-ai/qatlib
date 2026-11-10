/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy.QuantumLDPCDecoding
import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

set_option autoImplicit false

namespace Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy

open Matrix

theorem greedyDecode_flip_budget :
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ],
    ∀ (H : Matrix κ ι (ZMod 2)) (moves : List (ι → ZMod 2))
      (fuel : ℕ) (s : κ → ZMod 2),
      let r := greedyDecode H moves fuel s
      bitWeight r.syndrome + r.flips ≤ bitWeight s ∧ r.flips ≤ fuel := by
  intro ι κ _ _ H moves fuel
  induction fuel with
  | zero => intro s; simp [greedyDecode]
  | succ fuel ih =>
    intro s
    simp only [greedyDecode]
    split
    · simp
    · rename_i f hf
      have hw := (chooseReducingFlip_spec H s moves f hf).2
      obtain ⟨hweight, hflips⟩ := ih (s + H *ᵥ f)
      dsimp only at hweight hflips ⊢
      constructor <;> omega

private theorem chooseReducingFlip_none {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (s : κ → ZMod 2) (moves : List (ι → ZMod 2))
    (hnone : (chooseReducingFlip H s moves).1 = none) :
    ∀ f ∈ moves, ¬bitWeight (s + H *ᵥ f) < bitWeight s := by
  induction moves with
  | nil => simp
  | cons g moves ih =>
    simp only [chooseReducingFlip] at hnone
    split at hnone
    · cases hnone
    · rename_i hg
      intro f hf
      rcases List.mem_cons.mp hf with hfg | hf
      · subst f; exact hg
      · exact ih hnone f hf

private theorem bitWeight_add_single_lt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : κ → ZMod 2) (j : κ) (hj : s j ≠ 0) :
    bitWeight (s + Pi.single j 1) < bitWeight s := by
  classical
  have hjone : s j = 1 := by
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (s j) with h | h
    · exact (hj h).elim
    · exact h
  have hs : (Finset.univ.filter fun i : κ => (s + (Pi.single j 1 : κ → ZMod 2)) i ≠ 0) =
      (Finset.univ.filter fun i => s i ≠ 0).erase j := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [hjone, CharTwo.add_self_eq_zero]
    · simp [Pi.single_apply, hij]
  unfold bitWeight
  rw [hs]
  exact Finset.card_erase_lt_of_mem (by simp [hj])

theorem greedyDecode_syndromeComplete :
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ],
    ∀ (H : Matrix κ ι (ZMod 2)) (moves : List (ι → ZMod 2)),
      (∀ j : κ, ∃ f ∈ moves, H *ᵥ f = Pi.single j 1) →
      ∀ (s : κ → ZMod 2),
        let r := greedyDecode H moves (bitWeight s) s
        r.syndrome = 0 ∧ H *ᵥ r.correction = s ∧
          r.candidateChecks ≤ bitWeight s * moves.length := by
  intro ι κ _ _ _ H moves hcover s
  let r := greedyDecode H moves (bitWeight s) s
  have hz : r.syndrome = 0 := by
    have hnone := greedyDecode_terminal H moves (bitWeight s) s (le_refl _)
    by_contra hnonzero
    have hex : ∃ j, r.syndrome j ≠ 0 := by
      by_contra h
      push Not at h
      exact hnonzero (funext h)
    obtain ⟨j, hj⟩ := hex
    obtain ⟨f, hf, hsingle⟩ := hcover j
    have hlt := bitWeight_add_single_lt r.syndrome j hj
    rw [← hsingle] at hlt
    exact chooseReducingFlip_none H r.syndrome moves hnone f hf hlt
  refine ⟨hz, ?_, greedyDecode_checks H moves (bitWeight s) s⟩
  have htransport := greedyDecode_syndrome H moves (bitWeight s) s
  change r.syndrome = s + H *ᵥ r.correction at htransport
  rw [hz] at htransport
  ext i
  have heq := congrArg (fun v => s i + v i) htransport
  change s i + 0 = s i + (s i + (H *ᵥ r.correction) i) at heq
  simpa only [add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] using heq.symm

theorem greedyDecode_css_correct :
    ∀ {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
      [DecidableEq ι] [DecidableEq κX],
    ∀ (c : CssData ι κX κZ) (moves : List (ι → ZMod 2)),
      (∀ j : κX, ∃ f ∈ moves, c.hX *ᵥ f = Pi.single j 1) →
      ∀ (e : ι → ZMod 2),
        let s := c.hX *ᵥ e
        let r := greedyDecode c.hX moves (bitWeight s) s
        bitWeight r.correction ≤ bitWeight e →
        ((2 * bitWeight e : ℕ) : ℕ∞) < cssDistance c →
        e + r.correction ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ) ∧
          r.syndrome = 0 ∧ r.candidateChecks ≤ bitWeight s * moves.length := by
  intro ι κX κZ _ _ _ _ _ c moves hcover e
  dsimp only
  intro hweight hradius
  obtain ⟨hzero, hsyn, hchecks⟩ := greedyDecode_syndromeComplete c.hX moves hcover (c.hX *ᵥ e)
  exact ⟨correction_succeeds_below_half_distance c e _ hsyn hweight hradius, hzero, hchecks⟩

end Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy
