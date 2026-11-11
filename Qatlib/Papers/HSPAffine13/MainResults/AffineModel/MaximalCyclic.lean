/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HSPAffine13.MainResults.AffineModel.InjectiveOnC

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3: maximal cyclic non-normal subgroups are `C_b`

The paper's Lemma 3 classifies the subgroups named in the title: if `H` is a
maximal subgroup of the affine group which is cyclic and not normal, then
`H = C_b` for some `b ∈ F`.

The proof has three steps.

* A generator `g = (a, x)` of `H` cannot have `a = 1`: then `H` lies in the
  translation subgroup, and maximality forces `H` to be the whole translation
  subgroup, which is normal.
* For `a ≠ 1`, write `a = u^j` for the fixed generator `u` of `Fˣ`, and put
  `b = x * (u - 1) / (a - 1)`.  The power formula gives
  `(u, b)^j = (a, x) = g`, hence `H ≤ C_b`.
* Maximality and the properness of `C_b` upgrade the inclusion to equality.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HSPAffine13.MainResults

open AffineGroup

variable {F : Type*} [Field F]

/-- **Lemma 3 (HSPAffine13).**  If `u` generates `Fˣ`, `u ≠ 1`, and `H` is a
maximal cyclic subgroup of the affine group which is not normal, then
`H = C_b` for some `b`. -/
theorem lemma3_maximal_cyclic_eq_C (u : Fˣ) (hu : (u : F) ≠ 1)
    (hgen : Subgroup.zpowers u = ⊤) {H : Subgroup (AffineGroup F)}
    (hH : ∃ g : AffineGroup F, H = Subgroup.zpowers g)
    (hmax : IsMaximalSubgroup H) (hnorm : ¬ H.Normal) :
    ∃ b : F, H = C u b := by
  obtain ⟨g, hHg⟩ := hH
  have hgane : (g.a : F) ≠ 1 := by
    intro hga1
    have hleT : H ≤ translationSubgroup (F := F) := by
      rw [hHg]
      have hgu : g.a = 1 := Units.ext hga1
      exact Subgroup.zpowers_le.mpr (by simpa [translationSubgroup, aHom] using hgu)
    have hTne : translationSubgroup (F := F) ≠ ⊤ := by
      intro htop
      have hmem : (⟨u, 0⟩ : AffineGroup F) ∈ translationSubgroup := by
        rw [htop]
        exact Subgroup.mem_top _
      simp [translationSubgroup, aHom] at hmem
      exact hu (by simpa using hmem)
    have hHneT : H ≠ translationSubgroup (F := F) := by
      intro hEq
      exact hnorm (hEq.symm ▸ (MonoidHom.normal_ker (aHom (F := F))))
    have hlt : H < translationSubgroup (F := F) := lt_of_le_of_ne hleT hHneT
    exact hTne (hmax.2 (translationSubgroup (F := F)) hlt)
  have hgen_a : g.a ∈ Subgroup.zpowers u := by
    rw [hgen]
    exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgen_a
  let b : F := g.b * ((u : F) - 1) / ((g.a : F) - 1)
  have hden_u : (u : F) - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hden_a : (g.a : F) - 1 ≠ 0 := sub_ne_zero.mpr hgane
  have hval : (u : F) ^ j = (g.a : F) := by
    simpa using congrArg (fun z : Fˣ => (z : F)) hj
  have hg_eq : (⟨u, b⟩ : AffineGroup F) ^ j = g := by
    ext
    · have h := congrArg (fun z : Fˣ => (z : F)) hj
      simpa [zpow_a] using h
    · rw [zpow_b_eq u b hu j, hval]
      simp only [b]
      field_simp [hden_u, hden_a]
  have hgC : g ∈ C u b := by
    rw [mem_C_iff]
    exact ⟨j, hg_eq⟩
  have hle : H ≤ C u b := by
    rw [hHg]
    exact Subgroup.zpowers_le.mpr hgC
  have hCne : C u b ≠ ⊤ := by
    intro htop
    have hmem : (⟨1, 1⟩ : AffineGroup F) ∈ C u b := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := (mem_C_iff u b _).mp hmem
    have hkunit : u ^ k = 1 := by
      have h := congrArg (fun z : AffineGroup F => z.a) hk
      simpa [zpow_a] using h
    have hkval : (u : F) ^ k = 1 := by
      simpa using congrArg (fun z : Fˣ => (z : F)) hkunit
    have hkb : (1 : F) = 0 := by
      have h := congrArg (fun z : AffineGroup F => z.b) hk
      change ((⟨u, b⟩ : AffineGroup F) ^ k).b = (1 : F) at h
      rw [zpow_b_eq u b hu k, hkval] at h
      simp at h
    exact one_ne_zero hkb
  have hEq : H = C u b := by
    by_contra hne
    exact hCne (hmax.2 (C u b) (lt_of_le_of_ne hle hne))
  exact ⟨b, hEq⟩

end Qatlib.Papers.HSPAffine13.MainResults
