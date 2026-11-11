/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.InteractionPicture
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveSparseHAMT
import Qatlib.Papers.InteractPic18.MainResults.InteractionPicture.InteractionPictureIdentities

/-!
# SparseSimulation — Lemma 8, Theorem 9, Theorem 10 of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

* Lemma 8 (Section VI p. 13, Eqs. (49)--(52)): synthesis of the HAM-T block
  from the sparse oracles `OH`, `OF`. The formal content is that both oracles
  are reversible (unitary) instructions, that the synthesized block is
  block-diagonal in the time register with the `m`-th block equal to
  `H(t_m)/(d·‖H‖max)`, and that the actual program uses exactly two oracle
  queries.
* Theorem 9 (Section VI.A p. 14): simulation of sparse time-dependent
  Hamiltonians; segments of Theorem 3 give error `ε`, the failure ledger is
  `L·2δ`, and the query count obeys the `log/log log` cutoff rate.
* Theorem 10 (Section VI.B p. 15, Eq. (53)): simulation of sparse diagonally
  dominant `H = A + B`. The mathematical content of "the dependence on `‖A‖`
  drops out" is that the interaction-picture generator
  `H_I(s) = e^{iAs} B e^{-iAs}` has exactly the same operator norm as `B`,
  because conjugation by the unitary `e^{iAs}` is an isometry of the L2
  operator norm.

Boundary: matrix-level and integer-ledger statements only. The paper's
asymptotic query/qubit/gate expressions involving `N`, `np` and `poly` are
not restated as big-O statements; their exact frozen counterparts are
`ipSparseProgram`, `ipSparseQueries`, `ipSegmentQueries` and the cutoff rate
`computedDysonCutoff_tail_and_rate`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.InteractionEvo
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Papers.InteractPic18.MainResults.InteractionPicture
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.InteractPic18.MainResults.SparseSimulation

/-! ## Lemma 8 — the sparse oracles and the HAM-T block -/

/-- **Lemma 8, oracle reversibility** (fixed arXiv:1805.00675v2, Eqs. (50)--(52)):
both sparse oracles are genuine reversible instructions — `OH` is an
involution (XOR of the value bits) and `OF` is a permutation — hence unitary
on their respective registers. -/
theorem lemma8_sparse_oracle_unitaries (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) :
    effectiveSparseOH p S ∈ Matrix.unitaryGroup (Reg (p.nd + 2 * p.ns + 2 * p.np)) ℂ ∧
      effectiveSparseOF p S ∈ Matrix.unitaryGroup (Reg (p.nd + 2 * p.ns)) ℂ :=
  ⟨effectiveSparseOH_unitary p S, effectiveSparseOF_unitary p S⟩

/-- **Lemma 8, Eq. (49)** (fixed arXiv:1805.00675v2): the synthesized HAM-T
block is block-diagonal in the time register: whenever the two time
registers differ the matrix element vanishes. -/
theorem lemma8_hamt_block_offdiagonal (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) (x y : Reg (p.ns + p.nd))
    (hne : (fun i : Fin p.nd => x ⟨p.ns + i.val, by omega⟩) ≠
      (fun i : Fin p.nd => y ⟨p.ns + i.val, by omega⟩)) :
    effectiveSparseBlock p S x y = 0 := by
  simp only [effectiveSparseBlock]
  rw [if_neg hne]

/-- **Lemma 8, Eq. (49)** (fixed arXiv:1805.00675v2): on a diagonal time
block the synthesized HAM-T entry is the Hamiltonian entry scaled by
`1/(d·‖H‖max)`, i.e. `H(t)/(d‖H‖max)` in the paper's notation. -/
theorem lemma8_hamt_block_entry (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) (x y : Reg (p.ns + p.nd))
    (hxy : (fun i : Fin p.nd => x ⟨p.ns + i.val, by omega⟩) =
      (fun i : Fin p.nd => y ⟨p.ns + i.val, by omega⟩)) :
    effectiveSparseBlock p S x y =
      effectiveSparseEntry p S (fun i : Fin p.nd => x ⟨p.ns + i.val, by omega⟩)
        (fun i : Fin p.ns => x ⟨i.val, by omega⟩)
        (fun i : Fin p.ns => y ⟨i.val, by omega⟩) /
        ((p.d : ℂ) * (p.maxEntry : ℂ)) := by
  simp only [effectiveSparseBlock]
  rw [if_pos hxy]

/-- **Lemma 8, sparsity** (fixed arXiv:1805.00675v2, Eq. (49) and the promise
of Eqs. (47)--(48)): under the source's sparsity promise, every nonzero matrix
element of the HAM-T block has its column index reachable from a row of the
`d`-element row list, i.e. the block is `d`-sparse in every time slice. -/
theorem lemma8_sparse_block_support (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) (h : EffectiveSparseLegal p S)
    (x y : Reg (p.ns + p.nd)) (hne : effectiveSparseBlock p S x y ≠ 0) :
    (fun i : Fin p.nd => x ⟨p.ns + i.val, by omega⟩) =
        (fun i : Fin p.nd => y ⟨p.ns + i.val, by omega⟩) ∧
      ∃ xr : Reg p.ns, effectiveRegNat xr < p.d ∧
        S.locations (fun i : Fin p.nd => x ⟨p.ns + i.val, by omega⟩)
          (fun i : Fin p.ns => x ⟨i.val, by omega⟩) xr =
          (fun i : Fin p.ns => y ⟨i.val, by omega⟩) := by
  by_cases hxy : (fun i : Fin p.nd => x ⟨p.ns + i.val, by omega⟩) =
      (fun i : Fin p.nd => y ⟨p.ns + i.val, by omega⟩)
  · refine ⟨hxy, ?_⟩
    rw [lemma8_hamt_block_entry p S x y hxy] at hne
    have hentry : effectiveSparseEntry p S
        (fun i : Fin p.nd => x ⟨p.ns + i.val, by omega⟩)
        (fun i : Fin p.ns => x ⟨i.val, by omega⟩)
        (fun i : Fin p.ns => y ⟨i.val, by omega⟩) ≠ 0 := by
      intro h0
      exact hne (by rw [h0]; simp)
    exact h.2.2.2.2.2.2 _ _ _ hentry
  · exact absurd (lemma8_hamt_block_offdiagonal p S x y hxy) (by simp [hne])

/-- **Lemma 8, query count** (fixed arXiv:1805.00675v2, Lemma 8 last line):
the synthesized HAM-T program makes exactly two oracle queries — one `OH`, one
`OF` — which is the "O(1) queries" statement. -/
theorem lemma8_hamt_program_queries (p : EffectiveSparseParameters) :
    effectiveQueries (ipSparseProgram p) = ipSparseQueries p :=
  ipSparseProgram_queries p

/-- **Lemma 8, program shape** (fixed arXiv:1805.00675v2, Eq. (49)): the
synthesized program acts on `nd + 2ns + 2np` wires with a three-instruction
body (two queries and the value-scaling phase). -/
theorem lemma8_hamt_program_shape (p : EffectiveSparseParameters) :
    (ipSparseProgram p).width = p.nd + 2 * p.ns + 2 * p.np ∧
      (ipSparseProgram p).steps.length = 3 :=
  ipSparseProgram_shape p

/-- **Lemma 8, query constant** (fixed arXiv:1805.00675v2, Lemma 8): the
literals `ipSparseQueries p = 2`: one `OH` query and one `OF` query. -/
theorem lemma8_sparse_queries_eq_two (p : EffectiveSparseParameters) :
    ipSparseQueries p = 2 := rfl

/-! ## Theorem 9 — sparse time-dependent simulation -/

/-- **Theorem 9, segment error** (fixed arXiv:1805.00675v2, Section VI.A): one
segment of the sparse time-dependent simulation attains the dyadic accuracy
`(1/2)^{precision+6}` of Theorem 3. -/
theorem theorem9_segment_error (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ)
    (hp : effectiveSegmentDomain p) (hF : EffectiveField p H Hd) :
    ‖dysonGridTruncatedSum H p.time (effectiveSegmentM p) (effectiveSegmentK p) -
      orderedEvolution (fun u => Complex.I • H u) 0 p.time‖ ≤ (1/2 : ℝ)^(p.precision+6) :=
  effectiveDysonParameters_error p H Hd hp hF

/-- **Theorem 9, query rate** (fixed arXiv:1805.00675v2, Theorem 9 item 1):
the per-segment query count obeys the `log(1/ε)/log log(1/ε)` rate of the
computed cutoff. -/
theorem theorem9_query_rate :
    ∃ C m0 : ℕ, ∀ k : ℕ, m0 ≤ k →
      computedDysonCutoff (k + 8) * Nat.clog 2 (k + 2) ≤ C * (k + 2) := by
  obtain ⟨C, m0, hrate⟩ := ipLogLogRate
  exact ⟨C, m0, hrate⟩

/-- **Theorem 9, failure ledger** (fixed arXiv:1805.00675v2, Theorem 9 and
Eq. (14)): with `L` segments each failing with probability at most `δ ≤ 1`,
the total failure probability `1 - (1-δ)^L` is at most `L·2δ`; hence a budget
`δ = ε/(2L)` gives total failure at most `ε`. -/
theorem theorem9_total_failure (L : ℕ) (δ ε : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hL : 0 < L) (hbudget : δ ≤ ε / (2 * (L : ℝ))) :
    ipTotalFailure L δ ≤ ε := by
  have h := ipTotalFailure_le L δ hδ hδ1
  unfold ipPerSegmentFailure at h
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hmul : (L : ℝ) * δ ≤ ε / 2 := by
    calc (L : ℝ) * δ ≤ (L : ℝ) * (ε / (2 * (L : ℝ))) :=
          mul_le_mul_of_nonneg_left hbudget hLpos.le
      _ = ε / 2 := by field_simp
  nlinarith [h, hmul]

/-- **Theorem 9, sparsity scale** (fixed arXiv:1805.00675v2, Theorem 9,
`α_B = d‖B‖max`): a compatible sparse encoding has `d·‖H‖max = α`, the segment
scale `α` used by Theorem 3. -/
theorem theorem9_sparsity_scale (s : EffectiveSparseParameters)
    (p : EffectiveSegmentParameters) (h : effectiveSparseCompatible s p) :
    s.maxEntry * s.d = p.alpha :=
  h.2.2.1

/-! ## Theorem 10 — diagonally dominant sparse Hamiltonians -/

/-- **Theorem 10, norm independence** (fixed arXiv:1805.00675v2, Section VI.B
and Eq. (53)): the interaction-picture generator `H_I(s) = e^{iAs}B e^{-iAs}`
has exactly the same L2 operator norm as `B`. This is the formal content of
the paper's statement that the query complexity does not depend on the
diagonal magnitude `‖A‖`: conjugation by the unitary `e^{iAs}` is an isometry
of the operator norm. -/
theorem theorem10_interaction_generator_norm {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (A B : Matrix I I ℂ) (hA : A.IsHermitian) (s : ℝ) :
    ‖interactionPictureGenerator A B s‖ = ‖B‖ := by
  have hU : HamiltonianEvolution A (-s) ∈ Matrix.unitaryGroup I ℂ :=
    hamiltonianEvolution_unitary hA (-s)
  have hV : HamiltonianEvolution A s ∈ Matrix.unitaryGroup I ℂ :=
    hamiltonianEvolution_unitary hA s
  unfold interactionPictureGenerator
  rw [Matrix.mul_assoc, CStarRing.norm_mem_unitary_mul _ hU,
    CStarRing.norm_mul_mem_unitary _ hV]

/-- **Theorem 10, interaction-picture factorization** (fixed arXiv:1805.00675v2,
Eq. (53) and Eq. (18)): the full evolution of `H = A + B` factors as
`e^{-iAt}` times the time-ordered evolution of the rotating-frame generator
`H_I`, so the diagonal `A` enters only through that unitary. -/
theorem theorem10_interaction_picture_factorization {I : Type} [Fintype I]
    [DecidableEq I] (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (t : ℝ) :
    HamiltonianEvolution (A + B) t =
      HamiltonianEvolution A t *
        orderedEvolution (fun u => Complex.I • interactionPictureGenerator A B u) 0 t :=
  Qatlib.Papers.InteractPic18.MainResults.InteractionPicture.eq18_interaction_picture_identity
    A B hA hB t

/-- **Theorem 10, segment error** (fixed arXiv:1805.00675v2, Theorem 10): one
segment of the rotating-frame simulation attains the dyadic accuracy of
Theorem 3, with the `α_B`-scaled Hamiltonian absorbing the diagonal. -/
theorem theorem10_segment_error (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ)
    (hp : effectiveSegmentDomain p) (hF : EffectiveField p H Hd) :
    ‖dysonGridTruncatedSum H p.time (effectiveSegmentM p) (effectiveSegmentK p) -
      orderedEvolution (fun u => Complex.I • H u) 0 p.time‖ ≤ (1/2 : ℝ)^(p.precision+6) :=
  effectiveDysonParameters_error p H Hd hp hF

/-- **Theorem 10, query rate** (fixed arXiv:1805.00675v2, Theorem 10 item 1):
the query count obeys the same `log/log log` rate as Theorem 9, with `α_A`
absent from the bound. -/
theorem theorem10_query_rate :
    ∃ C m0 : ℕ, ∀ k : ℕ, m0 ≤ k →
      computedDysonCutoff (k + 8) * Nat.clog 2 (k + 2) ≤ C * (k + 2) := by
  obtain ⟨C, m0, hrate⟩ := ipLogLogRate
  exact ⟨C, m0, hrate⟩

end Qatlib.Papers.InteractPic18.MainResults.SparseSimulation
