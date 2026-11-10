/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.PrefixProgram
import Qatlib.Papers.SingleQuery97.MainResults.EncoderCircuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.BalancedQueries

open EncoderCircuit WalshProgram LinearCodeProgram

variable {N m : ℕ}

def rowWeight (label : Fin N → Fin m → ZMod 2) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j => label j i ≠ 0)).card

def flip (label : Fin N → Fin m → ZMod 2) (i : Fin m) : ZMod 2 :=
  if 2*rowWeight label i ≤ N then 0 else 1

def oriented (label : Fin N → Fin m → ZMod 2) : Fin N → Fin m → ZMod 2 :=
  fun j i => label j i + flip label i

def unorient (label : Fin N → Fin m → ZMod 2) (z : Fin m → ZMod 2) : Fin m → ZMod 2 :=
  fun i => z i - flip label i

theorem unorient_oriented (label : Fin N → Fin m → ZMod 2) (j : Fin N) :
    unorient label (oriented label j) = label j := by
  funext i
  exact add_sub_cancel_right _ _

theorem oriented_row_weight (label : Fin N → Fin m → ZMod 2) (i : Fin m) :
    2*rowWeight (oriented label) i ≤ N := by
  classical
  by_cases h : 2*rowWeight label i ≤ N
  · have hf : flip label i = 0 := by rw [flip, if_pos h]
    simpa only [rowWeight, oriented, hf, add_zero] using h
  · have hb : ∀ b : ZMod 2, b+1 ≠ 0 ↔ ¬(b ≠ 0) := by decide
    have hf : flip label i = 1 := by rw [flip, if_neg h]
    have hc : rowWeight (oriented label) i = N-rowWeight label i := by
      simp only [rowWeight, oriented, hf, hb, Finset.filter_not,
        Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [hc]
    omega

theorem two_pass_bound (label : Fin N → Fin m → ZMod 2) :
    2*(support (generators (oriented label))).card ≤ m*N := by
  rw [support_card, Finset.mul_sum]
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (fun (i : Fin m) _ => oriented_row_weight label i)
  simpa only [rowWeight, generators, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] using h

noncomputable def experiment [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ) (m : ℕ) : PMF (Fin N × Fin N) :=
  prior.bind fun t =>
    (outputLaw (generators (oriented (PrefixProgram.truncated bits m))) (database t)).map
      (fun p => (t, PrefixProgram.decoder bits length m
        (unorient (PrefixProgram.truncated bits m) p.1.1)))

theorem experiment_eq [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ) (m : ℕ) :
    experiment prior bits length m = PrefixProgram.experiment prior bits length m := by
  rw [PrefixProgram.experiment_eq]
  unfold experiment PMF.map
  apply congrArg (PMF.bind prior)
  funext t
  have h := outputLaw_decoded (generators (oriented (PrefixProgram.truncated bits m)))
    (database t) (fun z => (t,PrefixProgram.decoder bits length m
      (unorient (PrefixProgram.truncated bits m) z)))
  simpa only [response_database, unorient_oriented, PMF.map, Function.comp_apply] using h

theorem error_le_tail [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ)
    (hprefix : PrefixProgram.PrefixFree bits length) (m : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (experiment prior bits length m) (fun p => p.2 ≠ p.1) ≤
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event prior (fun t => m < length t) := by
  rw [experiment_eq]
  exact PrefixProgram.experiment_error_le_tail prior bits length hprefix m

end Qatlib.Papers.SingleQuery97.MainResults.BalancedQueries
