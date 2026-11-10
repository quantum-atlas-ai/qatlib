/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.Execution.KrausRefinement

open Matrix
open scoped ComplexOrder Kronecker

variable {O : Type*} [Fintype O] {D E : ℕ}

noncomputable def Instrument.krausFamily (I : Instrument O D E)
    (a : O × (Fin E × Fin D)) : Matrix (Fin E) (Fin D) ℂ :=
  (Classical.choose (MatrixMap.IsCompletelyPositive.exists_kraus (I.branch a.1)
    ((Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mp (I.cp a.1)))) a.2

theorem Instrument.branch_eq_kraus (I : Instrument O D E) (o : O) :
    I.branch o = ∑ k : Fin E × Fin D, conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k)) := by
  have h := Classical.choose_spec
    (MatrixMap.IsCompletelyPositive.exists_kraus (I.branch o)
      ((Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mp (I.cp o)))
  rw [MatrixMap.of_kraus_eq_sum_conj] at h
  exact h

theorem Instrument.branch_apply_eq_kraus (I : Instrument O D E) (o : O)
    (A : Operator D) :
    I.branch o A = ∑ k : Fin E × Fin D,
      (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k) * A * ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k)).conjTranspose := by
  rw [(Qatlib.Concepts.Execution.KrausRefinement.Instrument.branch_eq_kraus I) o,
      LinearMap.sum_apply]
  rfl

theorem Instrument.krausFamily_complete (I : Instrument O D E) :
    ∑ a : O × (Fin E × Fin D),
      ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) a).conjTranspose * (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) a = 1 := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [Finset.sum_mul, Matrix.trace_sum, Matrix.one_mul, Fintype.sum_prod_type]
  calc
    _ = ∑ o : O, ∑ k : Fin E × Fin D,
        Matrix.trace ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k) * A *
          ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k)).conjTranspose) := by
      apply Finset.sum_congr rfl
      intro o _
      apply Finset.sum_congr rfl
      intro k _
      exact (Matrix.trace_mul_cycle _ _ _).symm
    _ = Matrix.trace (∑ o, I.branch o A) := by
      rw [Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [(Qatlib.Concepts.Execution.KrausRefinement.Instrument.branch_apply_eq_kraus I) o,
          Matrix.trace_sum]
    _ = Matrix.trace A := I.total A

noncomputable def Instrument.krausRefinement (I : Instrument O D E) :
    Instrument (O × (Fin E × Fin D)) D E :=
  Instrument.ofKraus (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily_complete I)

@[simp] theorem Instrument.krausRefinement_branch (I : Instrument O D E)
    (a : O × (Fin E × Fin D)) :
    (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch a = conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) a) := rfl

theorem Instrument.krausRefinement_sum_branch (I : Instrument O D E) (o : O) :
    ∑ k : Fin E × Fin D, (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch (o, k) = I.branch o :=
  ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.branch_eq_kraus I) o).symm

private theorem instrument_eq_of_branch_eq (I J : Instrument O D E)
    (h : I.branch = J.branch) : I = J := by
  cases I
  cases J
  cases h
  rfl

theorem Instrument.coarsen_krausRefinement [DecidableEq O] (I : Instrument O D E) :
    (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).coarsen Prod.fst = I := by
  have hb : ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).coarsen Prod.fst).branch = I.branch := by
    funext o
    change (∑ a : O × (Fin E × Fin D) with a.1 = o,
      (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch a) = I.branch o
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_sum_branch I) o
  exact instrument_eq_of_branch_eq _ _ hb

theorem Instrument.exists_kraus_refinement [DecidableEq O] (I : Instrument O D E) :
    ∃ K : O × (Fin E × Fin D) → Matrix (Fin E) (Fin D) ℂ,
      ∃ hK : ∑ a, (K a).conjTranspose * K a = 1,
        (Instrument.ofKraus K hK).coarsen Prod.fst = I :=
  ⟨(Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I), (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily_complete I), (Qatlib.Concepts.Execution.KrausRefinement.Instrument.coarsen_krausRefinement I)⟩

theorem Instrument.krausRefinement_sum_prob (I : Instrument O D E) (o : O)
    (A : Operator D) :
    ∑ k : Fin E × Fin D, instrumentProb (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I) A (o, k) =
      instrumentProb I A o := by
  simp only [instrumentProb, ← Complex.re_sum, ← Matrix.trace_sum,
    ← LinearMap.sum_apply, (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_sum_branch I) o]

theorem Instrument.krausRefinement_sum_tensorLeft (I : Instrument O D E) (o : O)
    (R : ℕ) (A : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    (∑ k : Fin E × Fin D, tensorLeft ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch (o, k)) A) =
      tensorLeft (I.branch o) A := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp only [Matrix.sum_apply, tensorLeft]
  simpa only [LinearMap.sum_apply, Matrix.sum_apply] using
    congrFun₂ (congrArg (fun T : Operator D →ₗ[ℂ] Operator E =>
      T (fun x y => A (x, r) (y, s))) ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_sum_branch I) o)) i j

theorem Instrument.krausRefinement_sum_amplification (I : Instrument O D E) (o : O)
    (R : ℕ) (A : Matrix (Fin R × Fin D) (Fin R × Fin D) ℂ) :
    (∑ k : Fin E × Fin D,
      ChannelAmplification ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch (o, k)) R A) =
      ChannelAmplification (I.branch o) R A := by
  ext ⟨r, i⟩ ⟨s, j⟩
  simp only [Matrix.sum_apply, ChannelAmplification]
  simpa only [LinearMap.sum_apply, Matrix.sum_apply] using
    congrFun₂ (congrArg (fun T : Operator D →ₗ[ℂ] Operator E =>
      T (fun x y => A (r, x) (s, y))) ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_sum_branch I) o)) i j

end Qatlib.Concepts.Execution.KrausRefinement
