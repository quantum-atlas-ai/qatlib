/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KhovanovHom25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 9 (Hodge theory)

Source: arXiv:2501.12378v2, Theorem 9, p. 33, eq. (6.1)-(6.3).

The paper's statement, for a cochain complex `C` of finite-dimensional complex
inner-product spaces, is

`Cⁱ ≅ ℋⁱ ⊕ Im(dᵢ₋₁) ⊕ Im(dᵢ†)`   (eq. (6.3))

with `ℋⁱ ≅ Hⁱ(C)`, and `Δᵢ` positive definite on `ℋⁱ⊥ = Im(dᵢ₋₁) ⊕ Im(dᵢ†)`.

Since our cochains are indexed by `ℕ`, the degree-`i` statements involving the
"previous" differential are stated one degree up: the decomposition of `Cⁱ⁺¹`
involves `Im dᵢ` and `Im dᵢ₊₁†`.  This is the same content as eq. (6.3).

The decomposition, the cycle/harmonic split, positive definiteness on `ℋ⊥`, and
the orthogonal-complement identity are proved from the finite-dimensional
inner-product structure; the cohomology isomorphism is stated separately as
`harmonic_iso_homology` (the quotient construction is not needed for the
numerical claims of this paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.KhovanovHom25.MainResults

namespace CochainComplex

variable (K : CochainComplex)

/-- The cycles at degree `i`, `ker dᵢ`. -/
def cycles (i : ℕ) : Submodule ℂ (K.C i) :=
  (K.d i).ker

/-- The boundaries in degree `i+1`, `Im dᵢ`. -/
def boundaries (i : ℕ) : Submodule ℂ (K.C (i + 1)) :=
  (K.d i).range

/-- Boundaries are cycles: `Im dᵢ ⊆ ker dᵢ₊₁`. -/
theorem boundaries_le_cycles (i : ℕ) : K.boundaries i ≤ K.cycles (i + 1) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact K.d_comp i y

/-- The boundaries as a subspace of the cycles at degree `i+1`. -/
def boundariesInCycles (i : ℕ) : Submodule ℂ (K.cycles (i + 1)) :=
  (K.boundaries i).comap (K.cycles (i + 1)).subtype

/-- The cohomology in degree `i+1`, `Hⁱ⁺¹(C) = ker dᵢ₊₁ / Im dᵢ`. -/
abbrev homology (i : ℕ) : Type :=
  K.cycles (i + 1) ⧸ K.boundariesInCycles i

/-- **Theorem 9 (Hodge theory), decomposition part.**  At degree `i+1`, the
harmonic subspace is `ker dᵢ₊₁ ∩ ker dᵢ†`; together with the two image spaces it
spans the cochain space, and the harmonic part is orthogonal to them.

This is eq. (6.3) of arXiv:2501.12378v2, p. 33. -/
theorem theorem9_hodge_decomposition (i : ℕ) :
    K.harmonic (i + 1) = (K.d (i + 1)).ker ⊓ K.upKer (i + 1) ∧
    K.harmonic (i + 1) ⊔ ((K.d i).range ⊔ (K.dAdj (i + 1)).range) = ⊤ ∧
    Disjoint (K.harmonic (i + 1)) ((K.d i).range ⊔ (K.dAdj (i + 1)).range) :=
  ⟨K.harmonic_eq_inf (i + 1), K.harmonic_sup_ranges i,
    K.harmonic_disjoint_ranges i⟩

/-- **Theorem 9 (Hodge theory), orthogonal-complement form.**  The orthogonal
complement of `ℋᵢ₊₁` is `Im dᵢ ⊔ Im dᵢ₊₁†`, as in eq. (6.3). -/
theorem theorem9_harmonic_orthogonal (i : ℕ) :
    (K.harmonic (i + 1))ᗮ = (K.d i).range ⊔ (K.dAdj (i + 1)).range :=
  K.harmonic_orthogonal_eq_ranges i

/-- **Theorem 9 (Hodge theory), cycle split.**  Every cycle is harmonic plus a
boundary, `ker dᵢ₊₁ = ℋᵢ₊₁ ⊔ Im dᵢ`. -/
theorem theorem9_cycles_split (i : ℕ) :
    (K.d (i + 1)).ker = K.harmonic (i + 1) ⊔ K.boundaries i :=
  K.cycles_eq_harmonic_sup_range i

/-- **Theorem 9 (Hodge theory), positive definiteness on `ℋ⊥`.**  On the
orthogonal complement of the harmonic chains the Laplacian has no kernel: a
vector in `ℋᵢ₊₁⊥` annihilated by `Δᵢ₊₁` is zero, i.e. `Δ` is positive definite
there. -/
theorem theorem9_lap_positive_definite_on_orthogonal (i : ℕ) :
    ∀ x ∈ (K.harmonic (i + 1))ᗮ, K.lap (i + 1) x = 0 → x = 0 := by
  intro x hxorth hx
  have hxharm : x ∈ K.harmonic (i + 1) := (K.mem_harmonic (i + 1) x).mpr hx
  rw [Submodule.mem_orthogonal] at hxorth
  have hzero : ⟪x, x⟫ = 0 := hxorth x hxharm
  exact inner_self_eq_zero.mp hzero

/-- Harmonic chains are cycles: `ℋⁱ⁺¹ ≤ ker dⁱ⁺¹`. -/
theorem harmonic_le_cycles (i : ℕ) :
    K.harmonic (i + 1) ≤ K.cycles (i + 1) := by
  intro x hx
  rw [harmonic_eq_inf] at hx
  exact hx.1

/-- Harmonic chains are disjoint from the boundaries. -/
theorem disjoint_harmonic_boundaries (i : ℕ) :
    Disjoint (K.harmonic (i + 1)) (K.boundaries i) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hh, hb⟩ := hx
  have hsplit := K.harmonic_disjoint_ranges i
  rw [disjoint_iff_inf_le] at hsplit
  have hxs : x ∈ (K.d i).range ⊔ (K.dAdj (i + 1)).range :=
    Submodule.mem_sup_left hb
  have hxbot : x ∈ (⊥ : Submodule ℂ (K.C (i + 1))) :=
    hsplit (by rw [Submodule.mem_inf]; exact ⟨hh, hxs⟩)
  rwa [Submodule.mem_bot] at hxbot

/-- The canonical map from harmonic chains to cohomology: inclusion into the
cycles followed by the quotient projection. -/
def harmonicToHomology (K : CochainComplex) (i : ℕ) :
    K.harmonic (i + 1) →ₗ[ℂ] K.homology i :=
  (Submodule.mkQ (K.boundariesInCycles i)).comp
    (LinearMap.codRestrict (K.cycles (i + 1)) (K.harmonic (i + 1)).subtype
      (fun x => K.harmonic_le_cycles i x.2))

/-- **Theorem 9 (Hodge theory), cohomology isomorphism.**  The harmonic space at
degree `i+1` is linearly isomorphic to the cohomology `Hⁱ⁺¹(C)`.

The isomorphism sends a harmonic chain to its class modulo boundaries.  It is
injective because `ℋⁱ⁺¹ ∩ Im dᵢ = 0` (`disjoint_harmonic_boundaries`), and
surjective by `theorem9_cycles_split`: every cycle is a harmonic chain plus a
boundary, and the boundary part vanishes in the quotient. -/
theorem harmonic_iso_homology (i : ℕ) :
    Nonempty (K.harmonic (i + 1) ≃ₗ[ℂ] K.homology i) := by
  have hle := K.harmonic_le_cycles i
  refine ⟨LinearEquiv.ofBijective (harmonicToHomology K i) ⟨?_, ?_⟩⟩
  · intro x y hxy
    have hd : ((LinearMap.codRestrict (K.cycles (i + 1))
          (K.harmonic (i + 1)).subtype (fun x => hle x.2)) x -
        (LinearMap.codRestrict (K.cycles (i + 1)) (K.harmonic (i + 1)).subtype
          (fun x => hle x.2)) y : K.cycles (i + 1)) ∈
        K.boundariesInCycles i := by
      have h2 : (Submodule.Quotient.mk
          ((LinearMap.codRestrict (K.cycles (i + 1)) (K.harmonic (i + 1)).subtype
            (fun x => hle x.2)) x) : K.homology i) =
          Submodule.Quotient.mk ((LinearMap.codRestrict (K.cycles (i + 1))
            (K.harmonic (i + 1)).subtype (fun x => hle x.2)) y) := hxy
      exact (Submodule.Quotient.eq (K.boundariesInCycles i)).mp h2
    have hd : x.val - y.val ∈ K.boundaries i := hd
    have hharmonic : x.val - y.val ∈ K.harmonic (i + 1) :=
      Submodule.sub_mem _ x.2 y.2
    have hbot : x.val - y.val ∈ (⊥ : Submodule ℂ (K.C (i + 1))) :=
      (disjoint_iff_inf_le.mp (K.disjoint_harmonic_boundaries i))
        (by rw [Submodule.mem_inf]; exact ⟨hharmonic, hd⟩)
    rw [Submodule.mem_bot] at hbot
    exact Subtype.ext (sub_eq_zero.mp hbot)
  · rintro ⟨c⟩
    have hcyc : c.val ∈ K.harmonic (i + 1) ⊔ K.boundaries i := by
      have h0 : c.val ∈ (K.d (i + 1)).ker := c.2
      rw [K.theorem9_cycles_split i] at h0
      exact h0
    obtain ⟨h, hh, b, hb, hsum⟩ := Submodule.mem_sup.mp hcyc
    refine ⟨⟨h, hh⟩, ?_⟩
    have hcl : ((LinearMap.codRestrict (K.cycles (i + 1))
          (K.harmonic (i + 1)).subtype (fun x => hle x.2)) ⟨h, hh⟩ - c :
        K.cycles (i + 1)) ∈ K.boundariesInCycles i := by
      show _ - _ ∈ K.boundaries i
      have hneg : h - c.val = -b := by rw [← hsum]; abel
      simp only [LinearMap.codRestrict_apply, Submodule.coe_subtype]
      rw [hneg]
      exact Submodule.neg_mem _ hb
    have hfin : (Submodule.Quotient.mk ((LinearMap.codRestrict (K.cycles (i + 1))
          (K.harmonic (i + 1)).subtype (fun x => hle x.2)) ⟨h, hh⟩ :
        K.cycles (i + 1)) : K.homology i) = Submodule.Quotient.mk c :=
      (Submodule.Quotient.eq (K.boundariesInCycles i)).mpr hcl
    exact hfin

end CochainComplex

end Qatlib.Papers.KhovanovHom25.MainResults
