/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.BipartiteEffectiveGapCorrectedStat
import Qatlib.Concepts.QueryComplexity.Reflections.EffectiveSpectralGapCorrectedRefl
import Qatlib.Concepts.QueryComplexity.Reflections.KernelWitnessCorrectedRefl

/-!
# Corrected bipartite effective spectral gap

Identifies the source marked adjacency with an effective-gap adjacency and proves its Hermitian
property. The theorem `bipartiteEffectiveGapCorrected` combines nonzero kernel witnesses with
the corrected effective-gap bound under source dual feasibility and `W ≥ 1`.

The resulting positive root concentration and negative low-energy mass estimates formalize the
corrected local version of the bipartite argument in [Reichardt2011].

## Main statements

* `source_marked_adjacency_effective`: identifies the source graph with the generic
  effective-gap graph.
* `bipartiteEffectiveGapCorrected`: proves the dual-feasible bipartite gap contract.

## References

* [Reichardt, Lemma 3.3][Reichardt2011]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators

/-- Identifies the source marked adjacency matrix with the effective-gap adjacency formed from
the restricted biadjacency and the extended target vector. -/
theorem source_marked_adjacency_effective {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    sourceMarkedAdjacency input f v W x=
      effectiveGapAdjacency (sourceRestrictedBiadj input f v x) (Sum.elim (tvec W) 0) := by
  ext p q
  cases p with
  | inl p=>cases p <;> cases q with
    | inl q=>rfl
    | inr q=>cases q <;> rfl
  | inr p=>cases p <;> cases q with
    | inl q=>cases q <;> rfl
    | inr q=>rfl

/-- The source marked adjacency matrix is Hermitian. -/
theorem source_marked_adjacency_hermitian {X : Type} [Fintype X] [DecidableEq X] {n m : ℕ}
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ) (x : X) :
    (sourceMarkedAdjacency input f v W x).IsHermitian := by
  rw [source_marked_adjacency_effective]
  exact effective_gap_adjacency_hermitian _ _

/-- A column-side kernel vector extends by zero to a kernel vector of the block adjacency. -/
theorem source_block_kernel {R C : Type} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]
    (B : Matrix R C ℂ) (ψ : QState C) (hψ : B*ᵥψ=0) : blockAdjacency B*ᵥSum.elim 0 ψ=0 := by
  ext p
  cases p <;> simp [blockAdjacency,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    show ∀ r,(∑ c,B r c*ψ c)=0 from congrFun hψ]

/-- Under source dual feasibility and `W ≥ 1`, establishes the nonzero positive-input kernel
witness and negative-input low-energy spectral bound in `BipartiteEffectiveGapCorrected`.
See [Reichardt, Lemma 3.3][Reichardt2011]. -/
theorem bipartiteEffectiveGapCorrected : BipartiteEffectiveGapCorrected := by
  intro X _ _ n m input f v W hd hW
  have hw : 0 < W := by linarith
  have hk:=kernelWitnessCorrected X n m input f v W hd hW
  constructor
  · intro x hx
    have hs:=hk.1 x hx
    refine ⟨sourcePositiveWitness input f v W x,hs.1,?_,hs.2.2⟩
    exact source_block_kernel _ _ hs.2.1
  · intro x hx c hc k V ρ hV hVV hEV
    have hs:=hk.2 x hx
    let ψ:=sourceNegativeWitness input f v x
    let t : QState (RowLab X f n m):=Sum.elim (tvec W) 0
    let δ:=1/(9*W*(W+1))
    have hδ : 0 < δ := by dsimp [δ];positivity
    have hover : δ*(∑ r : RowLab X f n m,‖ψ r‖^2) ≤ ‖Qatlib.Foundations.PureStateMath.Inner t ψ‖^2 := by
      simpa [ψ,t,δ,Qatlib.Foundations.PureStateMath.Inner,dotProduct,Fintype.sum_sum_type] using hs.2.2
    rw [source_marked_adjacency_effective] at hEV
    have hb:=effectiveSpectralGapCorrected (RowLab X f n m) (IVert n m)
      (sourceRestrictedBiadj input f v x) t ψ δ hδ hs.1 hs.2.1 hover
      (c/W) (div_nonneg hc hw.le) k V ρ hV hVV hEV
    have hr : 8*(c/W)^2/δ=72*(1+1/W)*c^2 := by dsimp [δ];field_simp;ring
    exact hb.trans_eq hr
end Qatlib.Concepts.QueryComplexity.Reflections
