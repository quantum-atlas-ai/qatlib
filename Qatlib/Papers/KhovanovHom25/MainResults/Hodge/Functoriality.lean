/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Hodge.ChainMap

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Propositions 14 and 16: functoriality of harmonic chains and their complement

Source: arXiv:2501.12378v2, Section 6.2, Propositions 14 and 16 (pp. 35-36).

Proposition 14. `h` is a functor: `h(C)` is a complex with zero differential,
`h(g ∘ f) = h(g) ∘ h(f)` and `h(id) = id`.
Proposition 16. `h⊥` is a functor on `d(C) ⊕ d†(C)`.

The harmonic composition law follows from the cycle/boundary decomposition.
For complement maps, composition requires preservation of the complement by
`f`; this compatibility is stated explicitly in `proposition16_comp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.KhovanovHom25.MainResults
open Qatlib.Papers.KhovanovHom25.MainResults

open CochainComplex

namespace ChainMap

/-- The identity chain map. -/
def id (K : CochainComplex) : ChainMap K K where
  f _ := LinearMap.id
  comm _ _ := rfl

end ChainMap

variable {K L M : CochainComplex}

/-- **Proposition 14, identity law.**  The induced map of the identity chain map
on harmonic chains is the identity. -/
theorem proposition14_id (K : CochainComplex) (i : ℕ) :
    harmonicMap (ChainMap.id K) i = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show K.harmonicProj i ((ChainMap.id K).f i (x : K.C i)) = (x : K.C i)
  rw [show (ChainMap.id K).f i (x : K.C i) = (x : K.C i) from rfl]
  exact K.harmonicProj_apply_harmonic i x

/-- **Proposition 14, composition law.** Chain maps induce composable maps
on harmonic representatives because cycle representatives differ by boundaries. -/
theorem proposition14_comp (f : ChainMap K L) (g : ChainMap L M) (i : ℕ) :
    harmonicMap (ChainMap.mk (fun i => (g.f i).comp (f.f i))
        (fun i x => by rw [LinearMap.comp_apply, LinearMap.comp_apply, f.comm, g.comm]))
      i =
      (harmonicMap g i).comp (harmonicMap f i) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change M.harmonicProj i (g.f i (f.f i x)) =
    M.harmonicProj i (g.f i (L.harmonicProj i (f.f i x)))
  have hcyc : f.f i x ∈ (L.d i).ker := by
    have hx : (x : K.C i) ∈ (K.d i).ker :=
      ((K.harmonic_eq_inf i).le.trans inf_le_left) x.property
    change K.d i x = 0 at hx
    change L.d i (f.f i x) = 0
    rw [← f.comm, hx, map_zero]
  cases i with
  | zero =>
    have hh : f.f 0 x ∈ L.harmonic 0 := by
      rw [L.harmonic_eq_inf]
      exact ⟨hcyc, Submodule.mem_top⟩
    rw [show L.harmonicProj 0 (f.f 0 x) = f.f 0 x from
      L.harmonicProj_apply_harmonic 0 ⟨_, hh⟩]
  | succ j =>
    rw [L.cycles_eq_harmonic_sup_range j] at hcyc
    obtain ⟨h, hh, b, ⟨y, rfl⟩, heq⟩ := Submodule.mem_sup.mp hcyc
    have hb : L.harmonicProj (j + 1) (L.d j y) = 0 := by
      change (L.harmonic (j + 1)).starProjection (L.d j y) = 0
      apply (Submodule.starProjection_apply_eq_zero_iff (K := L.harmonic (j + 1))).mpr
      exact L.orthogonal_of_le_orthogonal
        (L.harmonic_le_orthogonal_range_left j) ⟨y, rfl⟩
    have hb' : M.harmonicProj (j + 1) (g.f (j + 1) (L.d j y)) = 0 := by
      rw [g.comm]
      change (M.harmonic (j + 1)).starProjection (M.d j (g.f j y)) = 0
      apply (Submodule.starProjection_apply_eq_zero_iff (K := M.harmonic (j + 1))).mpr
      exact M.orthogonal_of_le_orthogonal
        (M.harmonic_le_orthogonal_range_left j) ⟨g.f j y, rfl⟩
    have hhproj : L.harmonicProj (j + 1) h = h :=
      L.harmonicProj_apply_harmonic (j + 1) ⟨h, hh⟩
    rw [← heq]
    simp only [map_add, hhproj, hb, hb', add_zero]

/-- **Proposition 14.**  `h` is a functor on harmonic chains: identity and
composition laws together. -/
theorem proposition14 :
    (∀ (K : CochainComplex) (i : ℕ),
        harmonicMap (ChainMap.id K) i = LinearMap.id) ∧
      (∀ (K L M : CochainComplex) (f : ChainMap K L) (g : ChainMap L M) (i : ℕ),
        harmonicMap (ChainMap.mk (fun i => (g.f i).comp (f.f i))
            (fun i x => by
              rw [LinearMap.comp_apply, LinearMap.comp_apply, f.comm, g.comm])) i =
          (harmonicMap g i).comp (harmonicMap f i)) :=
  ⟨proposition14_id, fun _ _ _ f g i => proposition14_comp f g i⟩

/-- The complement `h⊥(C) = (d(C) ⊕ d†(C))` of the harmonic chains at degree `i`
(Theorem 9, eq. (6.3)). -/
def harmonicComplement (K : CochainComplex) (i : ℕ) : Submodule ℂ (K.C i) :=
  (K.harmonic i)ᗮ

/-- Proposition 16's `h⊥(f)`: the collapse map of `d(C) ⊕ d†(C)` to
`d(D) ⊕ d†(D)`, defined by projecting `f x` onto `h⊥(D)`. -/
def harmonicComplementMap (f : ChainMap K L) (i : ℕ) :
    harmonicComplement K i →ₗ[ℂ] harmonicComplement L i :=
  (((harmonicComplement L i).orthogonalProjectionOnto :
      L.C i →L[ℂ] harmonicComplement L i).toLinearMap).comp
    ((f.f i).comp (harmonicComplement K i).subtype)

/-- **Proposition 16, well-definedness.**  `h⊥(f)` lands in `d(D) ⊕ d†(D)`,
which is `h⊥(D)` by Theorem 9 (eq. (6.3)). -/
theorem proposition16_wellDefined (f : ChainMap K L) (i : ℕ) :
    ∀ x : harmonicComplement K (i + 1),
      (harmonicComplementMap f (i + 1) x : L.C (i + 1)) ∈
        (L.d i).range ⊔ (L.dAdj (i + 1)).range := by
  intro x
  rw [← L.harmonic_orthogonal_eq_ranges i]
  exact Submodule.starProjection_apply_mem ((L.harmonic (i + 1))ᗮ) ((f.f (i + 1)) x)

/-- **Proposition 16, composition law.** The first map is required to preserve
harmonic complements; arbitrary chain maps need not preserve them. -/
theorem proposition16_comp (f : ChainMap K L) (g : ChainMap L M) (i : ℕ)
    (hf : ∀ x ∈ harmonicComplement K i, f.f i x ∈ harmonicComplement L i) :
    harmonicComplementMap
        (ChainMap.mk (fun i => (g.f i).comp (f.f i))
          (fun i x => by rw [LinearMap.comp_apply, LinearMap.comp_apply, f.comm, g.comm]))
        i =
      (harmonicComplementMap g i).comp (harmonicComplementMap f i) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (harmonicComplement M i).starProjection (g.f i (f.f i x)) =
    (harmonicComplement M i).starProjection
      (g.f i ((harmonicComplement L i).starProjection (f.f i x)))
  rw [Submodule.starProjection_eq_self_iff.mpr (hf x x.property)]

end Qatlib.Papers.KhovanovHom25.MainResults
