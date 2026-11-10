/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ReturningStages
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped ENNReal
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.OraclePairLaw

def join {S O : Type} (p : CostedLaw S) (q : S → CostedLaw O) : PMF (O × (ℕ × ℕ)) :=
  PMF.bind p fun z => (q z.1).map fun w => (w.1,(z.2,w.2))

theorem first_mean {S O : Type} (p : CostedLaw S) (q : S → CostedLaw O) :
    expectation (join p q) (fun z => (z.2.1 : ℝ≥0∞)) = expectedCost p := by
  unfold join
  rw [expectation_bind]
  simp only [expectation_map, expectation_const]
  rfl

theorem second_mean {S O : Type} (p : CostedLaw S) (q : S → CostedLaw O) :
    expectation (join p q) (fun z => (z.2.2 : ℝ≥0∞)) =
      expectation p (fun z => expectedCost (q z.1)) := by
  unfold join
  rw [expectation_bind]
  simp only [expectation_map, expectedCost]

theorem second_bound {S O : Type} (p : CostedLaw S) (q : S → CostedLaw O)
    (b : ℝ≥0∞) (hq : ∀ s, expectedCost (q s) ≤ b) :
    expectation (join p q) (fun z => (z.2.2 : ℝ≥0∞)) ≤ b := by
  rw [second_mean, ← expectation_const p b]
  unfold expectation
  exact ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hq z.1)

theorem support {S O : Type} (p : CostedLaw S) (q : S → CostedLaw O)
    (o : O) (a b : ℕ) (h : join p q (o,(a,b)) ≠ 0) :
    ∃ s, p (s,a) ≠ 0 ∧ q s (o,b) ≠ 0 := by
  change (o,(a,b)) ∈ (PMF.bind p fun z => (q z.1).map fun w => (w.1,(z.2,w.2))).support at h
  obtain ⟨z,hz,hw⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
  obtain ⟨w,hw,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hw
  have ha : z.2 = a := congrArg (fun v => v.2.1) he
  have hb : w.2 = b := congrArg (fun v => v.2.2) he
  have ho : w.1 = o := congrArg Prod.fst he
  have hz' : p (z.1,z.2) ≠ 0 := hz
  have hw' : q z.1 (w.1,w.2) ≠ 0 := hw
  exact ⟨z.1, by simpa only [ha] using hz', by simpa only [ho,hb] using hw'⟩

theorem combined {S O : Type} (p : CostedLaw S) (q : S → CostedLaw O) :
    (join p q).map (fun z => (z.1,z.2.1+z.2.2)) = CostedLaw.bind p q := by
  unfold join CostedLaw.bind CostedLaw.charge
  rw [PMF.map_bind]
  apply congrArg (PMF.bind p)
  funext z
  rw [PMF.map_comp]
  rfl

end Qatlib.Papers.CollisionProb97.MainResults.OraclePairLaw
