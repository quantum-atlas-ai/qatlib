/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.AlgorithmicInterface
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Model

theorem hasPolyQuerySolverFor_self {G : Type*} [Group G] (e : BlackBoxEncoding G) :
    HasPolyQuerySolverFor e := by
  classical
  letI : Fintype e.Token := e.fintype
  letI : DecidableEq e.Token := e.decEq
  letI : Fintype G := Fintype.ofSurjective e.enc e.surj

  let tok : G → e.Token := fun g => Classical.choose (e.surj g)
  have htok : ∀ g : G, e.enc (tok g) = g := fun g => Classical.choose_spec (e.surj g)

  let t0 : e.Token := tok 1
  have ht0 : e.enc t0 = (1 : G) := htok 1

  let s : HSPSolver e :=
    { output := fun f => Finset.univ.filter (fun g => f (tok g) = f t0)
      correct := by
        intro H f hf
        have hset : (↑(Finset.univ.filter (fun g => f (tok g) = f t0)) : Set G)
            = (H : Set G) := by
          ext g
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          have h := hf (tok g) t0
          rw [htok g, ht0] at h
          constructor
          · intro hfg
            obtain ⟨hh, hprod⟩ := h.mp hfg
            have hg : g = (hh : G)⁻¹ := by
              calc g = g * (hh : G) * (hh : G)⁻¹ := by simp
                _ = 1 * (hh : G)⁻¹ := by rw [hprod]
                _ = (hh : G)⁻¹ := by simp
            rw [hg]
            exact H.inv_mem hh.property
          · intro hg
            exact h.mpr ⟨⟨g⁻¹, H.inv_mem hg⟩, by simp⟩
        rw [hset, Subgroup.closure_eq] }
  refine ⟨s, 1, ?_⟩
  refine ⟨Finset.univ, ?_, ?_⟩
  · simp [BlackBoxEncoding.size]
  · intro f g hagree
    have hfg : f = g := funext fun x => hagree x (Finset.mem_univ x)
    rw [hfg]

theorem hasPolynomialQueryHSPSolver (G : Type*) [Group G] :
    HasPolynomialQueryHSPSolver G := fun e => hasPolyQuerySolverFor_self e

end Qatlib.Papers.SemiDirectHSP04.MainResults.Model
