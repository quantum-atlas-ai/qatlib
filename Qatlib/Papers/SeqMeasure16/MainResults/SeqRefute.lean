/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SeqMeasure16.MainResults.Testers.SourceTesterModel
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SeqMeasure16.MainResults.ContractRefute

open Matrix
open Qatlib.Papers.SeqMeasure16.MainResults.Testers

/-- The empty function domain makes the legacy isomorphic and far promises overlap. -/
theorem emptyG_noTester :
    ¬ Nonempty (GIsomorphismTester (Fin 0) (Fin 1) {Equiv.refl (Fin 0)} 1) := by
  classical
  rintro ⟨T⟩
  let f : Fin 0 → Fin 1 := fun _ => 0
  have hy : (2 : ℝ) / 3 ≤ T.acceptProb f f :=
    T.accepts_isomorphic f f ⟨Equiv.refl (Fin 0), by simp, by intro x; rfl⟩
  have hn : T.acceptProb f f ≤ 1 / 3 := T.rejects_far f f (by
    intro σ hσ
    simp)
  linarith

/-- The full legacy G-isomorphism existence claim fails on the empty domain. -/
theorem g_iso_counter :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (G : Finset (Equiv.Perm (Fin 0))) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ T : GIsomorphismTester (Fin 0) (Fin 1) G ε,
          (T.queries : ℝ) ≤ c * Real.log (G.card : ℝ) / ε) := by
  classical
  rintro ⟨c, _hc, h⟩
  obtain ⟨T, _hcost⟩ := h {Equiv.refl (Fin 0)} 1 (by norm_num) (by norm_num)
  exact emptyG_noTester ⟨T⟩

/-- In dimension zero the normalized-overlap formula gives self-distance one. -/
theorem empty_self_dist :
    unitaryDistance (1 : Matrix (Fin 0) (Fin 0) ℂ) 1 = 1 := by
  simp [unitaryDistance, unitaryOverlap, Matrix.trace]

/-- The empty unitary is simultaneously a member and far in the legacy property model. -/
theorem emptyU_noTester :
    ¬ Nonempty (UnitaryPropertyTester 0 {(1 : Matrix (Fin 0) (Fin 0) ℂ)} 1) := by
  classical
  rintro ⟨T⟩
  have hU : IsUnitary (1 : Matrix (Fin 0) (Fin 0) ℂ) := by
    simp [IsUnitary]
  have hy := T.accepts_member 1 (by simp) hU
  have hn := T.rejects_far 1 hU (by
    intro V hV
    have hv : V = 1 := by simpa using hV
    subst V
    exact le_of_eq empty_self_dist.symm)
  linarith

/-- The full legacy unitary-property existence claim fails at dimension zero. -/
theorem unitary_counter :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (P : Finset (Matrix (Fin 0) (Fin 0) ℂ)) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ T : UnitaryPropertyTester 0 P ε,
          (T.uses : ℝ) ≤ c * Real.log (P.card : ℝ) / ε ^ 2) := by
  classical
  rintro ⟨c, _hc, h⟩
  obtain ⟨T, _hcost⟩ := h {1} 1 (by norm_num) (by norm_num)
  exact emptyU_noTester ⟨T⟩

/-- Zero-dimensional unitary isomorphism likewise has overlapping correctness promises. -/
theorem emptyIso_noTest :
    ¬ Nonempty (UnitaryIsomorphismTester 0 {(1 : Matrix (Fin 0) (Fin 0) ℂ)} 1) := by
  classical
  rintro ⟨T⟩
  have hU : IsUnitary (1 : Matrix (Fin 0) (Fin 0) ℂ) := by
    simp [IsUnitary]
  have hy := T.accepts_isomorphic 1 1 hU hU ⟨1, by simp, by simp⟩
  have hn := T.rejects_far 1 1 hU hU (by
    intro U hmem
    have hu : U = 1 := by simpa using hmem
    subst U
    simpa using (le_of_eq empty_self_dist.symm))
  linarith

/-- The full legacy unitary-isomorphism existence claim fails at dimension zero. -/
theorem iso_counter :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (Matrix (Fin 0) (Fin 0) ℂ)) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ T : UnitaryIsomorphismTester 0 S ε,
          (T.uses : ℝ) ≤ c * Real.log (S.card : ℝ) / ε ^ 2) := by
  classical
  rintro ⟨c, _hc, h⟩
  obtain ⟨T, _hcost⟩ := h {1} 1 (by norm_num) (by norm_num)
  exact emptyIso_noTest ⟨T⟩

end Qatlib.Papers.SeqMeasure16.MainResults.ContractRefute
