/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.MachineResults.Lemma6
set_option warningAsError false

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

open Finset
open scoped BigOperators

set_option autoImplicit false
noncomputable section

def ampDot (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2

def ampU : ℝ × ℝ := (1, 0)

def ampW (p s : ℝ) : ℝ × ℝ := (p, s)

def ampAccept (p s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (ampDot (ampW p s) x / p) • ampW p s

def ampReject (p s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - (ampAccept p s x).1, x.2 - (ampAccept p s x).2)

def ampReflect (x : ℝ × ℝ) : ℝ × ℝ := (x.1, -x.2)

def ampStep (p s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := ampReflect (ampReject p s x)

def ampZ (p s : ℝ) : ℝ × ℝ := (1 - p, s)

theorem ampDot_smul_left (c : ℝ) (x y : ℝ × ℝ) :
    ampDot (c • x) y = c * ampDot x y := by
  simp only [ampDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem ampDot_smul_right (c : ℝ) (x y : ℝ × ℝ) :
    ampDot x (c • y) = c * ampDot x y := by
  simp only [ampDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem ampDot_add_left (x y z : ℝ × ℝ) :
    ampDot (x + y) z = ampDot x z + ampDot y z := by
  simp only [ampDot, Prod.fst_add, Prod.snd_add]; ring

theorem ampDot_add_right (x y z : ℝ × ℝ) :
    ampDot x (y + z) = ampDot x y + ampDot x z := by
  simp only [ampDot, Prod.fst_add, Prod.snd_add]; ring

theorem ampDot_u_u : ampDot ampU ampU = 1 := by
  simp [ampDot, ampU]

theorem ampDot_u_w (p s : ℝ) : ampDot ampU (ampW p s) = p := by
  simp only [ampDot, ampU, ampW]; ring

theorem ampDot_w_u (p s : ℝ) : ampDot (ampW p s) ampU = p := by
  simp only [ampDot, ampU, ampW]; ring

theorem ampDot_w_w (p s : ℝ) (hs : s ^ 2 = p * (1 - p)) :
    ampDot (ampW p s) (ampW p s) = p := by
  simp only [ampDot, ampW]; nlinarith [hs]

theorem ampDot_z_z (p s : ℝ) (hs : s ^ 2 = p * (1 - p)) :
    ampDot (ampZ p s) (ampZ p s) = 1 - p := by
  simp only [ampDot, ampZ]; nlinarith [hs]

theorem ampDot_z_w (p s : ℝ) (hs : s ^ 2 = p * (1 - p)) :
    ampDot (ampZ p s) (ampW p s) = 2 * p * (1 - p) := by
  simp only [ampDot, ampZ, ampW]; nlinarith [hs]

theorem ampDot_w_z (p s : ℝ) (hs : s ^ 2 = p * (1 - p)) :
    ampDot (ampW p s) (ampZ p s) = 2 * p * (1 - p) := by
  simp only [ampDot, ampZ, ampW]; nlinarith [hs]

theorem ampAccept_w (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p)) :
    ampAccept p s (ampW p s) = ampW p s := by
  rw [ampAccept, ampDot_w_w p s hs]
  rw [div_self hp, one_smul]

theorem ampAccept_u (p s : ℝ) (hp : p ≠ 0) (_hs : s ^ 2 = p * (1 - p)) :
    ampAccept p s ampU = ampW p s := by
  rw [ampAccept, ampDot_w_u p s]
  rw [div_self hp, one_smul]

theorem ampAccept_add (p s : ℝ) (x y : ℝ × ℝ) :
    ampAccept p s (x + y) = ampAccept p s x + ampAccept p s y := by
  simp only [ampAccept, ampDot_add_right, add_div, add_smul]

theorem ampAccept_smul (p s : ℝ) (c : ℝ) (x : ℝ × ℝ) :
    ampAccept p s (c • x) = c • ampAccept p s x := by
  simp only [ampAccept, ampDot_smul_right, smul_smul, mul_div_assoc]

theorem ampAccept_affine (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p))
    (α β : ℝ) :
    ampAccept p s (α • ampU + β • ampW p s) = (α + β) • ampW p s := by
  rw [ampAccept_add, ampAccept_smul, ampAccept_smul, ampAccept_u p s hp hs,
    ampAccept_w p s hp hs, ← add_smul]

theorem ampReflect_u : ampReflect ampU = ampU := by
  simp [ampReflect, ampU]

theorem ampReflect_w (p s : ℝ) : ampReflect (ampW p s) = (p, -s) := by
  simp [ampReflect, ampW]

theorem ampZ_eq (p s : ℝ) : ampZ p s = (1 - 2 * p) • ampU + ampW p s := by
  ext
  all_goals simp [ampZ, ampU, ampW]
  all_goals ring

theorem ampStep_affine (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p))
    (α β : ℝ) :
    ampStep p s (α • ampU + β • ampW p s) = α • ampZ p s := by
  have hacc := ampAccept_affine p s hp hs α β

  have hrej : ampReject p s (α • ampU + β • ampW p s) = α • (1 - p, -s) := by
    simp only [ampReject, hacc]
    ext <;> (simp [ampU, ampW]; ring)

  simp only [ampStep, hrej, ampReflect, ampZ]
  ext <;> simp

def ampState (p s : ℝ) : ℕ → ℝ × ℝ
  | 0 => ampU
  | j + 1 => ampStep p s (ampState p s j)

theorem ampState_one (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p)) :
    ampState p s 1 = ampZ p s := by
  have h := ampStep_affine p s hp hs 1 0
  simpa [ampState, ampZ] using h

theorem ampState_closed (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p)) :
    ∀ j : ℕ, 1 ≤ j → ampState p s j = (1 - 2 * p) ^ (j - 1) • ampZ p s := by
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using ampState_one p s hp hs
    · have ihn : ampState p s n = (1 - 2 * p) ^ (n - 1) • ampZ p s := ih (by omega)
      rw [ampState, ihn]

      have hdecomp : (1 - 2 * p) ^ (n - 1) • ampZ p s =
          (1 - 2 * p) ^ n • ampU + (1 - 2 * p) ^ (n - 1) • ampW p s := by
        rw [ampZ_eq, smul_add, smul_smul, ← pow_succ, Nat.sub_one_add_one_eq_of_pos hn]
      rw [hdecomp, ampStep_affine p s hp hs ((1 - 2 * p) ^ n) ((1 - 2 * p) ^ (n - 1))]
      simp only [Nat.add_sub_cancel]

theorem ampNormSq (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p)) :
    ∀ j : ℕ, 1 ≤ j →
      ampDot (ampState p s j) (ampState p s j) = (1 - p) * (1 - 2 * p) ^ (2 * (j - 1)) := by
  intro j hj
  rw [ampState_closed p s hp hs j hj, ampDot_smul_left, ampDot_smul_right, ampDot_z_z p s hs]
  have hpow : ((1 - 2 * p) ^ (j - 1)) * ((1 - 2 * p) ^ (j - 1)) =
      (1 - 2 * p) ^ (2 * (j - 1)) := by
    rw [show 2 * (j - 1) = (j - 1) + (j - 1) by ring, pow_add]
  rw [← mul_assoc, hpow]; ring

def ampLocalAccept (p s : ℝ) (j : ℕ) : ℝ :=
  ampDot (ampState p s j) (ampAccept p s (ampState p s j))

theorem ampLocalAccept_zero (p s : ℝ) (hp : p ≠ 0) :
    ampLocalAccept p s 0 = p := by
  have hu : ampState p s 0 = ampU := rfl
  rw [ampLocalAccept, hu, ampAccept, ampDot_smul_right, ampDot_u_w p s, ampDot_w_u p s]
  rw [div_self hp, one_mul]

theorem ampLocalAccept_succ (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p))
    (j : ℕ) :
    ampLocalAccept p s (j + 1) = p * (1 - 2 * p) ^ (2 * j) * (2 - 2 * p) ^ 2 := by
  have hstate : ampState p s (j + 1) = (1 - 2 * p) ^ j • ampZ p s :=
    ampState_closed p s hp hs (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
  rw [ampLocalAccept, hstate, ampAccept_smul, ampDot_smul_left, ampDot_smul_right]

  have hQz : ampAccept p s (ampZ p s) = (2 - 2 * p) • ampW p s := by
    rw [ampAccept, ampDot_w_z p s hs]
    have hc : 2 * p * (1 - p) / p = 2 - 2 * p := by
      field_simp
    rw [hc]
  rw [hQz, ampDot_smul_right, ampDot_z_w p s hs]

  set c : ℝ := (1 - 2 * p) ^ j with hcdef
  have hcq : c * c = (1 - 2 * p) ^ (2 * j) := by
    rw [hcdef, show 2 * j = j + j by ring, pow_add]
  rw [← mul_assoc, hcq]
  ring

theorem ampTotalAccept (p s : ℝ) (hp : p ≠ 0) (hs : s ^ 2 = p * (1 - p)) (f : ℕ) :
    (∑ j ∈ Finset.range (f + 1), ampLocalAccept p s j) =
      1 - (1 - p) * (1 - 2 * p) ^ (2 * f) := by
  rw [Finset.sum_range_succ']
  rw [ampLocalAccept_zero p s hp]
  have hsucc : (∑ j ∈ Finset.range f, ampLocalAccept p s (j + 1)) =
      ∑ j ∈ Finset.range f, p * (1 - 2 * p) ^ (2 * j) * (2 - 2 * p) ^ 2 :=
    Finset.sum_congr rfl fun j _ => ampLocalAccept_succ p s hp hs j
  rw [hsucc, add_comm]
  exact lemma6_amplification_identity p f

end

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
