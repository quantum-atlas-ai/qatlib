/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.Group
import Qatlib.Papers.SemidirectHSP07.MainResults.CommutatorStructure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

def Hx (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r)))
    (H : Subgroup (SDG p r φ)) : Subgroup (SDG p r φ) :=
  H ⊓ Subgroup.zpowers (xGen p r φ)

def Hy (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r)))
    (H : Subgroup (SDG p r φ)) : Subgroup (SDG p r φ) :=
  H ⊓ Subgroup.zpowers (yGen p r φ)

def HxGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (m : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.zpowers (xGen p r φ ^ p ^ m)

def HyGen (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (n : ℕ) :
    Subgroup (SDG p r φ) :=
  Subgroup.zpowers (yGen p r φ ^ p ^ n)

theorem form1a_isCyclic (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r)))
    (i : ℕ) : IsCyclic (form1a p r φ i) := by
  show IsCyclic (Subgroup.zpowers (xGen p r φ ^ p ^ i))
  infer_instance

theorem form1b_isCyclic (p r : ℕ) (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r)))
    (i j t : ℕ) : IsCyclic (form1b p r φ i j t) := by
  show IsCyclic (Subgroup.zpowers (xGen p r φ ^ (t * p ^ i) * yGen p r φ ^ p ^ j))
  infer_instance

theorem range_inl_eq_zpowers_xGen (p r : ℕ) [NeZero (p ^ r)]
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    (SemidirectProduct.inl : Cyc (p ^ r) →* SDG p r φ).range
      = Subgroup.zpowers (xGen p r φ) := by
  rw [MonoidHom.range_eq_map, ← zpowers_cycGen (p ^ r), MonoidHom.map_zpowers]
  rfl

theorem ker_rightHom_eq_zpowers_xGen (p r : ℕ) [NeZero (p ^ r)]
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    (SemidirectProduct.rightHom : SDG p r φ →* Cyc (p ^ 2)).ker
      = Subgroup.zpowers (xGen p r φ) := by
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom, range_inl_eq_zpowers_xGen]

theorem cyclic_of_Hx_eq_bot (p r : ℕ) [NeZero (p ^ r)]
    (φ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) (H : Subgroup (SDG p r φ))
    (hHx : Hx p r φ H = ⊥) : IsCyclic H := by
  let f : H →* Cyc (p ^ 2) :=
    (SemidirectProduct.rightHom : SDG p r φ →* Cyc (p ^ 2)).comp H.subtype
  apply isCyclic_of_injective f
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hx
  change (SemidirectProduct.rightHom : SDG p r φ →* Cyc (p ^ 2))
    (x : SDG p r φ) = 1 at hx
  have hx' : ((x : SDG p r φ) ∈ H ⊓ Subgroup.zpowers (xGen p r φ)) := by
    refine ⟨x.2, ?_⟩
    have hker : (x : SDG p r φ) ∈
        (SemidirectProduct.rightHom : SDG p r φ →* Cyc (p ^ 2)).ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    rwa [ker_rightHom_eq_zpowers_xGen] at hker
  rw [show H ⊓ Subgroup.zpowers (xGen p r φ) = Hx p r φ H from rfl,
    hHx, Subgroup.mem_bot] at hx'
  exact Subtype.ext hx'

end Qatlib.Papers.SemidirectHSP07.MainResults
