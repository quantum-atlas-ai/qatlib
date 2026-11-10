/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Representation

open Matrix

lemma isPhase_one : IsPhase (1 : ℂ) := by
  simp [IsPhase]

lemma isPhase_neg_one : IsPhase (-1 : ℂ) := by
  simp [IsPhase]

lemma isPhase_ne_zero {z : ℂ} (h : IsPhase z) : z ≠ 0 := by
  intro hz
  have h' := h
  rw [IsPhase, hz] at h'
  simp at h'

lemma isPhase_mul {z w : ℂ} (hz : IsPhase z) (hw : IsPhase w) :
    IsPhase (z * w) := by
  rw [IsPhase, star_mul]
  calc z * w * (star w * star z) = z * (w * star w) * star z := by noncomm_ring
    _ = z * star z := by rw [hw, mul_one]
    _ = 1 := hz

lemma isPhase_star {z : ℂ} (h : IsPhase z) : IsPhase (star z) := by
  simpa [IsPhase, mul_comm] using h

lemma isPhase_inv {z : ℂ} (h : IsPhase z) : IsPhase z⁻¹ := by
  rw [IsPhase]
  have hz : z * star z = 1 := h
  have hz' : star z * z = 1 := by rw [mul_comm]; exact hz
  rw [inv_eq_of_mul_eq_one_right hz]
  simpa [star_star] using hz'

def RepEquivalentUpToPhase {G : Type*} [Group G] {d : ℕ}
    (ρ ρ' : G → CM d) : Prop :=
  ∃ U : CM d, U ∈ unitaryGroup (Fin d) ℂ ∧
    ∀ g : G, ∃ c : ℂ, IsPhase c ∧ U * ρ g * star U = c • ρ' g

lemma unitary_star {d : ℕ} {U : CM d} (hU : U ∈ unitaryGroup (Fin d) ℂ) :
    star U ∈ unitaryGroup (Fin d) ℂ := by
  rw [mem_unitaryGroup_iff]
  rw [star_star]
  exact mem_unitaryGroup_iff'.mp hU

lemma unitary_mul {d : ℕ} {U V : CM d}
    (hU : U ∈ unitaryGroup (Fin d) ℂ) (hV : V ∈ unitaryGroup (Fin d) ℂ) :
    U * V ∈ unitaryGroup (Fin d) ℂ := by
  rw [mem_unitaryGroup_iff]
  rw [star_mul]
  have h1 := mem_unitaryGroup_iff.mp hU
  have h2 := mem_unitaryGroup_iff.mp hV
  calc (U * V) * (star V * star U) = U * (V * star V) * star U := by noncomm_ring
    _ = U * star U := by rw [h2, mul_one]
    _ = 1 := h1

lemma repEquivUpToPhase_refl {G : Type*} [Group G] {d : ℕ} (ρ : G → CM d) :
    RepEquivalentUpToPhase ρ ρ := by
  refine ⟨1, ?_, fun g => ⟨1, isPhase_one, ?_⟩⟩
  · rw [mem_unitaryGroup_iff]; simp
  · simp

lemma repEquivUpToPhase_symm {G : Type*} [Group G] {d : ℕ} {ρ ρ' : G → CM d}
    (h : RepEquivalentUpToPhase ρ ρ') : RepEquivalentUpToPhase ρ' ρ := by
  obtain ⟨U, hU, hphase⟩ := h
  refine ⟨star U, unitary_star hU, fun g => ?_⟩
  obtain ⟨c, hc, hcU⟩ := hphase g
  refine ⟨c⁻¹, isPhase_inv hc, ?_⟩
  have h2 : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have hc0 : c ≠ 0 := isPhase_ne_zero hc
  have key : star U * (U * ρ g * star U) * U = ρ g := by
    calc star U * (U * ρ g * star U) * U
        = (star U * U) * ρ g * (star U * U) := by noncomm_ring
      _ = ρ g := by rw [h2]; simp
  have hsmul : c • (star U * ρ' g * U) = ρ g := by
    calc c • (star U * ρ' g * U) = star U * (c • ρ' g) * U := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = star U * (U * ρ g * star U) * U := by rw [hcU]
      _ = ρ g := key
  rw [star_star]
  calc star U * ρ' g * U = c⁻¹ • (c • (star U * ρ' g * U)) := by
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • ρ g := by rw [hsmul]

lemma repEquivUpToPhase_trans {G : Type*} [Group G] {d : ℕ} {ρ ρ' ρ'' : G → CM d}
    (h1 : RepEquivalentUpToPhase ρ ρ') (h2 : RepEquivalentUpToPhase ρ' ρ'') :
    RepEquivalentUpToPhase ρ ρ'' := by
  obtain ⟨U1, hU1, hp1⟩ := h1
  obtain ⟨U2, hU2, hp2⟩ := h2
  refine ⟨U2 * U1, unitary_mul hU2 hU1, fun g => ?_⟩
  obtain ⟨c1, hc1, hc1U⟩ := hp1 g
  obtain ⟨c2, hc2, hc2U⟩ := hp2 g
  refine ⟨c1 * c2, isPhase_mul hc1 hc2, ?_⟩
  calc (U2 * U1) * ρ g * star (U2 * U1)
      = U2 * (U1 * ρ g * star U1) * star U2 := by
        rw [star_mul]; noncomm_ring
    _ = U2 * (c1 • ρ' g) * star U2 := by rw [hc1U]
    _ = c1 • (U2 * ρ' g * star U2) := by rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = c1 • (c2 • ρ'' g) := by rw [hc2U]
    _ = (c1 * c2) • ρ'' g := by rw [smul_smul]

def jonesLabel (m n : ℕ) : ℕ × ℕ := ((m + n) / 2, (m - n) / 2)

lemma jonesLabel_sum {m n : ℕ} (h : n ≤ m) (hpar : (m + n) % 2 = 0) :
    (jonesLabel m n).1 + (jonesLabel m n).2 = m := by
  simp only [jonesLabel]
  omega

lemma jonesLabel_diff {m n : ℕ} (h : n ≤ m) (hpar : (m + n) % 2 = 0) :
    (jonesLabel m n).1 - (jonesLabel m n).2 = n := by
  simp only [jonesLabel]
  omega

lemma jonesLabel_six_zero : jonesLabel 6 0 = (3, 3) := by
  norm_num [jonesLabel]

lemma jonesLabel_six_two : jonesLabel 6 2 = (4, 2) := by
  norm_num [jonesLabel]

lemma jonesLabel_three_one : jonesLabel 3 1 = (2, 1) := by
  norm_num [jonesLabel]

lemma boundary_one_label_boxes (n : ℕ) (hn : n % 2 = 1) :
    ((n + 1) / 2) + ((n - 1) / 2) = n := by
  omega

lemma boundary_one_label_diff (n : ℕ) (hn : n % 2 = 1) :
    ((n + 1) / 2) - ((n - 1) / 2) = 1 := by
  omega

end Qatlib.Papers.ModularFunct00.MainResults.Representation
