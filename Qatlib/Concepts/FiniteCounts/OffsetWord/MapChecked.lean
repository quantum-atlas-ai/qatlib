/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteCounts.OffsetWord.BinaryWord
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteCounts.OffsetWord

variable {G H : Type*} [AddCommGroup G] [DecidableEq G]
    [AddCommGroup H] [DecidableEq H]

theorem map_badInputs_iff (f : G →+ H) (hf : Function.Injective f) (a B : G) :
    f a ∈ badInputs (f B) ↔ a ∈ badInputs B := by
  have h0 : f a = 0 ↔ a = 0 := by rw [← f.map_zero]; exact hf.eq_iff
  have hn : f a = -f B ↔ a = -B := by rw [← f.map_neg]; exact hf.eq_iff
  have hn2 : f a = -(f B+f B) ↔ a = -(B+B) := by
    rw [← f.map_add, ← f.map_neg]
    exact hf.eq_iff
  simp only [badInputs, Finset.mem_insert, Finset.mem_singleton,
    h0, hf.eq_iff, hn, hn2]

theorem checkedRun_map (f : G →+ H) (hf : Function.Injective f)
    (ss : List (Instruction G)) (a : G) :
    checkedRun (f a) (ss.map (fun s => (s.1,f s.2))) = (checkedRun a ss).map f := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨c,B⟩ := s
    cases c
    · simpa only [List.map_cons, checkedRun, Bool.false_eq_true, ↓reduceIte] using ih a
    · simp only [List.map_cons, checkedRun, ↓reduceIte, map_badInputs_iff f hf]
      split_ifs with hb
      · rfl
      · rw [← f.map_add, ih]

theorem checkedRun_map_success (f : G →+ H) (hf : Function.Injective f)
    (ss : List (Instruction G)) (a z : G) (h : checkedRun a ss = some z) :
    checkedRun (f a) (ss.map (fun s => (s.1,f s.2))) = some (f z) := by
  rw [checkedRun_map f hf, h]
  rfl

end Qatlib.Concepts.FiniteCounts.OffsetWord
