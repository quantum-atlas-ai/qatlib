/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland.Lemma4
import Qatlib.Papers.NonlinBool08.MainResults.BentCore.BentFacts
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

abbrev mmF {m : ℕ} (π : Equiv.Perm (BVec m)) : BVec m × BVec m → ZMod 2 :=
  mm π 0

def mmGs {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m)
    (p : BVec m × BVec m) : ZMod 2 :=
  mm π 0 (p + s)

abbrev mmFdual {m : ℕ} (π : Equiv.Perm (BVec m)) (u v : BVec m) : ZMod 2 :=
  mmDual π 0 u v

lemma mmGs_zero {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m) :
    mmGs π s (0, 0) = dot s.1 (π s.2) := by
  simp [mmGs, mm]

lemma mmGs_basis {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m) (i : Fin m) :
    mmGs π s (Pi.single i (1 : ZMod 2), 0)
      = (π s.2) i + dot s.1 (π s.2) := by
  simp only [mmGs, mm, Prod.fst_add, Prod.snd_add, Pi.zero_apply, zero_add, add_zero]
  have hdot : dot (Pi.single i (1 : ZMod 2) + s.1) (π s.2)
      = dot (Pi.single i (1 : ZMod 2)) (π s.2) + dot s.1 (π s.2) := by
    show dotProduct (Pi.single i (1 : ZMod 2) + s.1) (π s.2)
        = dotProduct (Pi.single i (1 : ZMod 2)) (π s.2) + dotProduct s.1 (π s.2)
    exact add_dotProduct _ _ _
  rw [hdot]
  congr 1
  rw [show dot (Pi.single i (1 : ZMod 2)) (π s.2)
      = dot (π s.2) (Pi.single i (1 : ZMod 2)) from by
    simp only [dot]; rw [dotProduct_comm]]
  rw [dot_single]
  simp

theorem mmGs_recover_pi {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m) :
    (fun i : Fin m => mmGs π s (Pi.single i (1 : ZMod 2), 0) + mmGs π s (0, 0))
      = π s.2 := by
  funext i
  rw [mmGs_basis, mmGs_zero]
  rw [add_assoc, BentCore.add_self_zmod2, add_zero]

lemma mmFdual_basis {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m)
    (i : Fin m) :
    mmFdual π (π s.2) (Pi.single i (1 : ZMod 2)) = s.2 i := by
  simp only [mmFdual, mmDual, Equiv.symm_apply_apply, Pi.zero_apply, add_zero]
  rw [dot_single]
  simp

lemma mmGs_recover_s1 {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m)
    (i : Fin m) :
    mmGs π s (0, π.symm (Pi.single i (1 : ZMod 2)) + s.2) = s.1 i := by
  simp only [mmGs, mm, Prod.fst_add, Prod.snd_add, Pi.zero_apply, zero_add]
  rw [show π.symm (Pi.single i (1 : ZMod 2)) + s.2 + s.2
      = π.symm (Pi.single i (1 : ZMod 2)) from by
    rw [add_assoc, BentCore.add_self_bvec, add_zero]]
  rw [Equiv.apply_symm_apply]
  rw [dot_single]
  simp

theorem mmDual_upper {m : ℕ} (π : Equiv.Perm (BVec m)) (s : BVec m × BVec m) :
    (fun i : Fin m => mmGs π s (Pi.single i (1 : ZMod 2), 0) + mmGs π s (0, 0))
        = π s.2 ∧
      (fun i : Fin m => mmFdual π (π s.2) (Pi.single i (1 : ZMod 2))) = s.2 ∧
      (fun i : Fin m => mmGs π s (0, π.symm (Pi.single i (1 : ZMod 2)) + s.2))
        = s.1 := by
  refine ⟨mmGs_recover_pi π s, ?_, ?_⟩
  · funext i
    exact mmFdual_basis π s i
  · funext i
    exact mmGs_recover_s1 π s i

lemma card_transcript (q : ℕ) : Fintype.card (Fin q → ZMod 2) = 2 ^ q := by
  simp [ZMod.card]

lemma card_shift (m : ℕ) : Fintype.card (BVec m × BVec m) = 2 ^ (2 * m) := by
  rw [Fintype.card_prod, BentCore.card_bvec_nat, ← pow_add]
  congr 1
  omega

theorem mmDual_lower {m q : ℕ} (hq : q < 2 * m) :
    ¬ ∃ (T : BVec m × BVec m → (Fin q → ZMod 2))
        (out : (Fin q → ZMod 2) → BVec m × BVec m),
        ∀ s, out (T s) = s := by
  rintro ⟨T, out, hout⟩
  have hinj : Function.Injective T := by
    intro a b hab
    have h1 : out (T a) = out (T b) := by rw [hab]
    rw [hout a, hout b] at h1
    exact h1
  have hcard := Fintype.card_le_of_injective T hinj
  rw [card_shift, card_transcript] at hcard
  have hlt : 2 ^ q < 2 ^ (2 * m) := Nat.pow_lt_pow_iff_right (by norm_num) |>.mpr hq
  omega

theorem theorem8_classical_linear {m : ℕ} (π : Equiv.Perm (BVec m)) :
    (∀ s : BVec m × BVec m,
        (fun i : Fin m => mmGs π s (Pi.single i (1 : ZMod 2), 0) + mmGs π s (0, 0))
            = π s.2 ∧
        (fun i : Fin m => mmFdual π (π s.2) (Pi.single i (1 : ZMod 2))) = s.2 ∧
        (fun i : Fin m => mmGs π s (0, π.symm (Pi.single i (1 : ZMod 2)) + s.2))
            = s.1) ∧
      (∀ q : ℕ, q < 2 * m →
        ¬ ∃ (T : BVec m × BVec m → (Fin q → ZMod 2))
            (out : (Fin q → ZMod 2) → BVec m × BVec m),
            ∀ s, out (T s) = s) :=
  ⟨fun s => mmDual_upper π s, fun _ hq => mmDual_lower hq⟩

end Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland
