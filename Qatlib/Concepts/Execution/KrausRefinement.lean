/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

/-!
# Kraus refinement of finite quantum instruments

`Instrument.krausFamily` chooses a finite Kraus representation of every completely positive
branch, using the finite matrix representation underlying [Choi1975]. Combining the chosen
operators yields a complete family indexed by the original outcome and a matrix index pair.

`Instrument.krausRefinement` exposes those Kraus indices as additional outcomes. Coarsening
recovers the original instrument, including its branch weights and its actions with reference
systems.

## Main statements

* `Instrument.krausFamily_complete`: the combined Kraus family satisfies completeness.
* `Instrument.coarsen_krausRefinement`: forgetting the added indices recovers the original
  instrument.
* `Instrument.exists_kraus_refinement`: every finite instrument is a coarsening of a Kraus
  instrument.
* `Instrument.krausRefinement_sum_amplification`: branch recovery holds after amplification by a
  reference system.

## References

* [Choi, 1975][Choi1975]
-/

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

/-- A chosen rectangular Kraus operator for a branch of `I`, indexed by the outcome and an
output-input index pair. -/
noncomputable def Instrument.krausFamily (I : Instrument O D E)
    (a : O × (Fin E × Fin D)) : Matrix (Fin E) (Fin D) ℂ :=
  (Classical.choose (MatrixMap.IsCompletelyPositive.exists_kraus (I.branch a.1)
    ((Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mp (I.cp a.1)))) a.2

/-- Each instrument branch is the sum of the conjugation maps associated with its chosen Kraus
operators. -/
theorem Instrument.branch_eq_kraus (I : Instrument O D E) (o : O) :
    I.branch o = ∑ k : Fin E × Fin D, conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k)) := by
  have h := Classical.choose_spec
    (MatrixMap.IsCompletelyPositive.exists_kraus (I.branch o)
      ((Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib _).mp (I.cp o)))
  rw [MatrixMap.of_kraus_eq_sum_conj] at h
  exact h

/-- Evaluating an instrument branch gives the sum of the chosen Kraus conjugations of its input
operator. -/
theorem Instrument.branch_apply_eq_kraus (I : Instrument O D E) (o : O)
    (A : Operator D) :
    I.branch o A = ∑ k : Fin E × Fin D,
      (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k) * A * ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (o, k)).conjTranspose := by
  rw [(Qatlib.Concepts.Execution.KrausRefinement.Instrument.branch_eq_kraus I) o,
      LinearMap.sum_apply]
  rfl

/-- The Kraus operators chosen across all instrument branches satisfy the completeness relation. -/
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

/-- The instrument that refines each original outcome by exposing its chosen Kraus index. -/
noncomputable def Instrument.krausRefinement (I : Instrument O D E) :
    Instrument (O × (Fin E × Fin D)) D E :=
  Instrument.ofKraus (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily_complete I)

/-- Each refined branch is conjugation by the corresponding chosen Kraus operator. -/
@[simp] theorem Instrument.krausRefinement_branch (I : Instrument O D E)
    (a : O × (Fin E × Fin D)) :
    (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch a = conjBranch ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I) a) := rfl

/-- Summing the refined branches over the additional Kraus index recovers the original branch. -/
theorem Instrument.krausRefinement_sum_branch (I : Instrument O D E) (o : O) :
    ∑ k : Fin E × Fin D, (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch (o, k) = I.branch o :=
  ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.branch_eq_kraus I) o).symm

/-- Two instruments with identical branch maps are equal. -/
private theorem instrument_eq_of_branch_eq (I J : Instrument O D E)
    (h : I.branch = J.branch) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- Forgetting the additional Kraus index in the refined instrument recovers the original
instrument. -/
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

/-- Every finite instrument is a coarsening of an instrument generated by a complete rectangular
Kraus family [Choi1975]. -/
theorem Instrument.exists_kraus_refinement [DecidableEq O] (I : Instrument O D E) :
    ∃ K : O × (Fin E × Fin D) → Matrix (Fin E) (Fin D) ℂ,
      ∃ hK : ∑ a, (K a).conjTranspose * K a = 1,
        (Instrument.ofKraus K hK).coarsen Prod.fst = I :=
  ⟨(Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily I), (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausFamily_complete I), (Qatlib.Concepts.Execution.KrausRefinement.Instrument.coarsen_krausRefinement I)⟩

/-- Summing refined branch weights over the added Kraus index recovers the original outcome
weight. -/
theorem Instrument.krausRefinement_sum_prob (I : Instrument O D E) (o : O)
    (A : Operator D) :
    ∑ k : Fin E × Fin D, instrumentProb (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I) A (o, k) =
      instrumentProb I A o := by
  simp only [instrumentProb, ← Complex.re_sum, ← Matrix.trace_sum,
    ← LinearMap.sum_apply, (Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_sum_branch I) o]

/-- The sum of refined branch actions on the left tensor factor equals the original branch
action, with the reference factor unchanged. -/
theorem Instrument.krausRefinement_sum_tensorLeft (I : Instrument O D E) (o : O)
    (R : ℕ) (A : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    (∑ k : Fin E × Fin D, tensorLeft ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement I).branch (o, k)) A) =
      tensorLeft (I.branch o) A := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp only [Matrix.sum_apply, tensorLeft]
  simpa only [LinearMap.sum_apply, Matrix.sum_apply] using
    congrFun₂ (congrArg (fun T : Operator D →ₗ[ℂ] Operator E =>
      T (fun x y => A (x, r) (y, s))) ((Qatlib.Concepts.Execution.KrausRefinement.Instrument.krausRefinement_sum_branch I) o)) i j

/-- After amplification by an arbitrary finite reference system, summing over the added Kraus
index recovers the original branch action. -/
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
