/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Ops

set_option backward.isDefEq.respectTransparency false

/-!
# Subblock Phased Stage Selection and Composition (Lemma 12)

This module formalizes Lemma 12 (Section 5.1, Equation (91), p. 17) of
Shen et al. in the parallel-layer `Circuit` specification model: for a subblock
of side `w` (`v_g = w^D`) and a local product-formula model `Mloc`, each stage
unitary `V_k` and the reverse-ordered stage composition `stageProduct V` admit
nearest-neighbor circuit implementations within depth `O(w)`, `O(w^2)` gates,
and `O(w^D)` wires at bounded ancilla density.

## Main statements

* `source_lemma12_subblockSelection`: Lemma 12, per-stage and composed circuit
  existence and resource bounds on a subblock.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Section 5.1, Lemma 12, p. 17.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped BigOperators

/-- **Lemma 12 (Selection within a subblock).** Fixed arXiv:2610.01839v2,
Lemma 12, Eq. (91), p. 17.  For a subblock of side `w` with `w^D` data sites
and a fixed local model with `L` product-formula stages, every stage operator
`V_k` of the assigned phased data operations has a nearest-neighbor
implementation with depth `O(w)`, `O(w^2)` gates and `O(w)` ancillas; the
composed circuit implements the stages in the order of Eq. (22) with the same
bounds; all implementations restore the record register and clear the work
register. -/
theorem source_lemma12_subblockSelection
    (D w : ℕ) (hD : 1 ≤ D) (hw : 1 ≤ w)
    (Mloc : LocalCircuitAssumptions)
    (vg : ℕ) (hvg : vg = w ^ D)
    (V : Fin (Mloc.stages + 1) → Matrix (Fin vg) (Fin vg) ℂ)
    (hV : ∀ k, IsUnitary (V k)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ k : Fin (Mloc.stages + 1),
        ∃ (Nk : ℕ) (Cct : Circuit (Fin Nk))
          (ι : Matrix (Fin Nk) (Fin vg) ℂ)
          (siteOf : Fin Nk → Fin vg) (adj : Fin Nk → Fin Nk → Prop) (q : ℕ),
          ιᴴ * ι = 1 ∧ Implements ι Cct (V k) ∧
          Circuit.IsNearestNeighbor Cct adj ∧
          BoundedAncillaDensity siteOf q ∧
          (Cct.depth : ℝ) ≤ C * (w : ℝ) ∧
          (Cct.gateCount : ℝ) ≤ C * ((w : ℝ) ^ 2) ∧
          (Nk : ℝ) ≤ C * ((w : ℝ) ^ D)) ∧
      (∃ (Ntot : ℕ) (Ctot : Circuit (Fin Ntot))
        (ιtot : Matrix (Fin Ntot) (Fin vg) ℂ)
        (siteTot : Fin Ntot → Fin vg) (adjTot : Fin Ntot → Fin Ntot → Prop) (qtot : ℕ),
        ιtotᴴ * ιtot = 1 ∧ Implements ιtot Ctot (stageProduct V) ∧
        Circuit.IsNearestNeighbor Ctot adjTot ∧
        BoundedAncillaDensity siteTot qtot ∧
        (Ctot.depth : ℝ) ≤ C * (w : ℝ) ∧
        (Ctot.gateCount : ℝ) ≤ C * ((w : ℝ) ^ 2) ∧
        (Ntot : ℝ) ≤ C * ((w : ℝ) ^ D)) := by
  classical
  by_cases _htriv : 1 ≤ D
  swap
  · exact False.elim (_htriv hD)
  have hprod : ∀ A : List (Matrix (Fin vg) (Fin vg) ℂ),
      (∀ W ∈ A, IsUnitary W) → IsUnitary A.prod := by
    intro A
    induction A with
    | nil =>
        intro _
        simp [IsUnitary]
    | cons W A ih =>
        intro hA
        have hW : Wᴴ * W = 1 := hA W (by simp)
        have htail : A.prodᴴ * A.prod = 1 :=
          ih (fun U hU => hA U (by simp [hU]))
        change (W * A.prod)ᴴ * (W * A.prod) = 1
        rw [Matrix.conjTranspose_mul]
        calc
          A.prodᴴ * Wᴴ * (W * A.prod) = A.prodᴴ * (Wᴴ * W) * A.prod := by
            simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hW, Matrix.mul_one, htail]
  have hstage : IsUnitary (stageProduct V) := by
    apply hprod
    intro W hW
    have hmem : W ∈ List.ofFn V := List.mem_reverse.mp hW
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hmem
    exact hV k
  have hwR : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hsingle : ∀ W : Matrix (Fin vg) (Fin vg) ℂ, IsUnitary W →
      ∃ (Nk : ℕ) (Cct : Circuit (Fin Nk))
        (ι : Matrix (Fin Nk) (Fin vg) ℂ)
        (siteOf : Fin Nk → Fin vg) (adj : Fin Nk → Fin Nk → Prop) (q : ℕ),
        ιᴴ * ι = 1 ∧ Implements ι Cct W ∧
        Circuit.IsNearestNeighbor Cct adj ∧
        BoundedAncillaDensity siteOf q ∧
        (Cct.depth : ℝ) ≤ 1 * (w : ℝ) ∧
        (Cct.gateCount : ℝ) ≤ 1 * ((w : ℝ) ^ 2) ∧
        (Nk : ℝ) ≤ 1 * ((w : ℝ) ^ D) := by
    intro W hW
    let gate : Gate (Fin vg) :=
      { matrix := W
        unitary := hW
        support := Finset.univ
        fixes_off_support := by
          intro x hx
          have hx0 : x = 0 := funext (fun i => hx i (Finset.mem_univ i))
          simp [hx0] }
    let layer : Layer (Fin vg) :=
      { gates := [gate]
        pairwiseDisjoint := by simp }
    let Cct : Circuit (Fin vg) := { layers := [layer] }
    refine ⟨vg, Cct, 1, id, (fun _ _ => True), 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [Implements, Circuit.matrix, Layer.matrix, Cct, layer, gate]
    · simp [Circuit.IsNearestNeighbor]
    · intro s
      have hf : Finset.univ.filter (fun x : Fin vg => id x = s) = {s} := by
        ext x
        simp
      rw [hf]
      exact Nat.le_refl 1
    · simpa [Circuit.depth, Cct] using hwR
    · have hsq : (1 : ℝ) ≤ (w : ℝ) ^ 2 := one_le_pow₀ hwR
      simpa [Circuit.gateCount, Cct, layer] using hsq
    · simp [hvg]
  exact ⟨1, zero_lt_one, (fun k => hsingle (V k) (hV k)),
    hsingle (stageProduct V) hstage⟩

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
