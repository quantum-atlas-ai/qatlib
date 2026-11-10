/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutingLLL13.MainResults.Defs
import Qatlib.Papers.CommutingLLL13.MainResults.EntropyChain
import Qatlib.Papers.CommutingLLL13.MainResults.FailureBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

noncomputable section

namespace Qatlib.Papers.CommutingLLL13.MainResults.MainTheorem

open Qatlib.Papers.CommutingLLL13.MainResults

variable {D : Type} [Fintype D] [DecidableEq D]

noncomputable def naturalSlack (P : Defs.QSatParams) : ℝ :=
  (P.k : ℝ) - Real.log ((P.g : ℝ) * (P.r : ℝ) * Real.exp 1)

noncomputable def naturalEta (P : Defs.QSatParams) (δ : ℝ) : ℝ :=
  Defs.etaNatural δ (P.k : ℝ) (P.r : ℝ) (P.g : ℝ)

noncomputable def naturalThreshold (P : Defs.QSatParams) (δ : ℝ) : ℕ :=
  Defs.thresholdNatural P.m (naturalEta P δ)

theorem zeroSweep_satisfies_mem {m : ℕ} (F : Defs.QSatFamily D m)
    (hcomm : Defs.CommutingFamily F) (l : List (Fin m)) (M : Matrix D D ℂ) :
    ∀ i ∈ l, F.P i * (l.foldr (Defs.zeroPostselect F) M) = 0 := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons i0 rest ih =>
    intro j hj
    rw [List.foldr_cons] at ⊢
    rw [List.mem_cons] at hj
    rcases hj with rfl | hmem
    · exact Defs.zeroPostselect_satisfies_own F _
        (rest.foldr (Defs.zeroPostselect F) M)
    · exact Defs.zeroPostselect_preserves F hcomm _ j
        (rest.foldr (Defs.zeroPostselect F) M) (ih j hmem)

theorem zeroSweep_covers_satisfies {m : ℕ} (F : Defs.QSatFamily D m)
    (hcomm : Defs.CommutingFamily F) (l : List (Fin m))
    (M : Matrix D D ℂ) (hcov : ∀ i, i ∈ l) :
    Defs.SatisfiesMat (l.foldr (Defs.zeroPostselect F) M) F := by
  intro i
  exact zeroSweep_satisfies_mem F hcomm l M i (hcov i)

theorem kappa_pos_of_qlll (P : Defs.QSatParams) (hk : 1 ≤ P.k) (hg : 1 ≤ P.g)
    (hcond : (P.g : ℝ) < 2 ^ (P.k : ℝ) / ((P.r : ℝ) * Real.exp 1)) :
    0 < naturalSlack P := by
  have hgR : (0 : ℝ) < (P.g : ℝ) := by exact_mod_cast (by omega : 0 < P.g)
  have hrR : (0 : ℝ) < (P.r : ℝ) := by exact_mod_cast P.hr
  have hexp : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hkR : (1 : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < (P.r : ℝ) * Real.exp 1 := by positivity
  have hlogrhs : Real.log (2 ^ (P.k : ℝ) / ((P.r : ℝ) * Real.exp 1))
      = (P.k : ℝ) * Real.log 2 - (Real.log (P.r : ℝ) + 1) := by
    rw [Real.log_div (by positivity : (2 : ℝ) ^ (P.k : ℝ) ≠ 0) hden.ne',
        Real.log_rpow (by norm_num)]
    have : Real.log ((P.r : ℝ) * Real.exp 1) = Real.log (P.r : ℝ) + 1 := by
      rw [Real.log_mul hrR.ne' hexp, Real.log_exp]
    rw [this]
  have hlg : Real.log (P.g : ℝ) < (P.k : ℝ) * Real.log 2 - (Real.log (P.r : ℝ) + 1) := by
    rw [← hlogrhs]
    exact Real.log_lt_log hgR hcond
  have hlogger : Real.log ((P.g : ℝ) * (P.r : ℝ) * Real.exp 1)
      = Real.log (P.g : ℝ) + Real.log (P.r : ℝ) + 1 := by
    rw [show (P.g : ℝ) * (P.r : ℝ) * Real.exp 1
          = ((P.g : ℝ) * (P.r : ℝ)) * Real.exp 1 by ring,
        Real.log_mul (by positivity) hexp, Real.log_mul hgR.ne' hrR.ne', Real.log_exp]
  have hlog2lt : Real.log 2 < 1 := by
    have h := Real.log_two_lt_d9; linarith
  rw [naturalSlack, hlogger]
  nlinarith [hlg, hlog2lt, hkR]

theorem conditional_natural_bound (P : Defs.QSatParams) (hm : 2 ≤ P.m)
    (δ : ℝ) (hδ : 0 < δ)
    (hκ : 0 < naturalSlack P) :
    (Real.log ((naturalThreshold P δ : ℝ)) + (P.m : ℝ))
        / ((naturalThreshold P δ : ℝ) * naturalSlack P) ≤ δ := by
  have hηpos : 0 < naturalEta P δ := by
    rw [naturalEta]
    unfold Defs.etaNatural
    exact div_pos one_pos (mul_pos hδ hκ)
  have hηδ : naturalEta P δ * δ * naturalSlack P = 1 := by
    rw [naturalEta, naturalSlack]
    unfold Defs.etaNatural
    have h1 : δ ≠ 0 := hδ.ne'
    have h2 : (P.k : ℝ) - Real.log ((P.g : ℝ) * (P.r : ℝ) * Real.exp 1) ≠ 0 := hκ.ne'
    field_simp
  exact FailureBound.eq5_le_delta P.m hm (naturalEta P δ) (naturalSlack P) δ hηpos hκ hηδ

theorem conditional_natural_and_sweep (P : Defs.QSatParams) (hm : 2 ≤ P.m) (hk : 1 ≤ P.k)
    (hg : 1 ≤ P.g)
    (hcond : (P.g : ℝ) < 2 ^ (P.k : ℝ) / ((P.r : ℝ) * Real.exp 1))
    (δ : ℝ) (hδ : 0 < δ) (F : Defs.QSatFamily D P.m)
    (hcomm : Defs.CommutingFamily F) :
    (∀ pFail : ℝ,
        pFail ≤ (Real.log ((naturalThreshold P δ : ℝ)) + (P.m : ℝ))
                   / ((naturalThreshold P δ : ℝ) * naturalSlack P) → pFail ≤ δ)
      ∧ (∀ (M : Matrix D D ℂ) (l : List (Fin P.m)),
          (∀ i, i ∈ l) → Defs.SatisfiesMat (l.foldr (Defs.zeroPostselect F) M) F) := by
  have hκ : 0 < naturalSlack P := kappa_pos_of_qlll P hk hg hcond
  refine ⟨?_, ?_⟩
  · intro pFail hp
    exact le_trans hp (conditional_natural_bound P hm δ hδ hκ)
  · intro M l hl
    exact zeroSweep_covers_satisfies F hcomm l M hl

end Qatlib.Papers.CommutingLLL13.MainResults.MainTheorem
