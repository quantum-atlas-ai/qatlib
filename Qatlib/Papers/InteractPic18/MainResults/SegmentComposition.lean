/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.SegmentProduct.Corollary4CompositeErrorHami
import Qatlib.Concepts.InteractionEvo.SegmentProduct.Lemma6SegmentCompositeHami
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPictureDefs
import Qatlib.Concepts.RandCompile.ChannelBudget.InteractionPicture
import Qatlib.Papers.InteractPic18.MainResults.InteractionPicture.InteractionPictureIdentities

/-!
# SegmentComposition — Corollary 4 and Lemma 6 of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

* Corollary 4 (p. 5--6, Eqs. (11)--(13)): if every one of the `L` segment
  macros `W_j` is a contraction and approximates the exact interaction-picture
  segment to `δ`, then the composed `L`-fold program approximates the full
  evolution `e^{-i(A+B)t}` to `L δ`.
* Lemma 6 (p. 7, Eq. (19)): the exact identity
  `(e^{-iAτ} T[e^{-i∫_0^τ H_I}])^L = e^{-i(A+B)Lτ}`.
* Lemma 6 (p. 7, Eq. (20) and the cost list): the Eq. (20) HAM-T oracle block
  `Σ_m |m⟩⟨m| ⊗ e^{iAτm/M} B e^{-iAτm/M}/α_B`, whose every diagonal block is a
  contraction (`‖B‖/α_B ≤ 1`), and the cost ledger it drives: `⌈2α_B t⌉`
  segments each making `computedDysonCutoff (precision+8)` HAM-T queries, so
  the total query count is their product and obeys the
  `log(1/ε)/log log(1/ε)` rate; the qubit and primitive-gate ledgers are
  `ipTotalQubits` and `ipTotalGates`.

Boundary: matrix-macro error composition and the resource ledger only. The
paper's asymptotic `O(·)` expressions are not restated as big-O statements;
their exact frozen counterparts are the `ip*` definitions. The per-segment
HAM-T gate rate is registered separately (c005, Theorem 7,
`EffectiveInteractionGateRate`); the failure-probability bound `O(ε)` of
Eq. (14) is not asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.InteractionEvo.SegmentProduct
open Qatlib.Papers.InteractPic18.MainResults.InteractionPicture
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.InteractPic18.MainResults.SegmentComposition

/-- **Corollary 4** (fixed arXiv:1805.00675v2, p. 5, Eqs. (11)--(13)): `L`
composed contractive segment macros, each within `δ` of the exact
interaction-picture segment, are `L·δ`-close to the full evolution
`e^{-i(A+B)Lτ}`. -/
theorem corollary4_multi_segment_error {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (L : ℕ) (τ δ : ℝ) (hδ : 0 ≤ δ) (W : Matrix I I ℂ) (hW : ‖W‖ ≤ 1)
    (herror : ‖W - (HamiltonianEvolution A τ *
      orderedEvolution (fun u => Complex.I • interactionGenerator A (fun _ => B) u) 0 τ)‖ ≤ δ) :
    ‖W ^ L - HamiltonianEvolution (A + B) ((L : ℝ) * τ)‖ ≤ (L : ℝ) * δ :=
  corollary4CompositeError I A B hA hB L τ δ hδ W hW herror

/-- **Lemma 6, Eq. (19)** (fixed arXiv:1805.00675v2, p. 7): `L` repetitions of
the interaction-picture segment macro `e^{-iAτ} T[e^{-i∫_0^τ H_I(s) ds}]`
compose exactly to evolution by `A+B` for the full time `Lτ`. Stated with the
paper's `H_I` from Eq. (17). -/
theorem lemma6_segment_power_identity {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (L : ℕ) (τ : ℝ) :
    (HamiltonianEvolution A τ *
      orderedEvolution (fun u => Complex.I • interactionPictureGenerator A B u) 0 τ) ^ L
        = HamiltonianEvolution (A + B) ((L : ℝ) * τ) := by
  simpa [interactionPictureGenerator, interactionGenerator]
    using lemma6SegmentComposite I A B hA hB L τ

/-! ## Lemma 6 — the Eq. (20) HAM-T block and the cost ledger -/

/-- **Lemma 6, Eq. (20)** (fixed arXiv:1805.00675v2, p. 7): the HAM-T oracle's
zero-ancilla block is the block-diagonal matrix whose `m`-th time block is
`e^{iAτm/M} B e^{-iAτm/M}/α_B`. The matrix below is indexed by the time
register `Fin M` and the system register `I` and records exactly that block
together with the normalization by `α_B`. -/
noncomputable def eq20HamtBlock {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (τ : ℚ) (M : ℕ) (αB : ℝ) :
    Matrix (Fin M × I) (Fin M × I) ℂ :=
  fun x y =>
    if x.1 = y.1 then
      ((αB : ℂ)⁻¹ • (HamiltonianEvolution A ((τ * (x.1.val : ℚ) / (M : ℚ) : ℚ) : ℝ) * B *
        HamiltonianEvolution A (-((τ * (x.1.val : ℚ) / (M : ℚ) : ℚ) : ℝ)))) x.2 y.2
    else 0

/-- **Lemma 6, Eq. (20)** (fixed arXiv:1805.00675v2, p. 7): different time
blocks of the HAM-T oracle never mix — the oracle is block-diagonal in the
time register `m`. -/
theorem lemma6_hamt_block_no_crosstalk {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (τ : ℚ) (M : ℕ) (αB : ℝ) (m m' : Fin M) (i j : I)
    (h : m ≠ m') : eq20HamtBlock A B τ M αB (m, i) (m', j) = 0 := by
  simp [eq20HamtBlock, h]

/-- **Lemma 6, Eq. (20)** (fixed arXiv:1805.00675v2, p. 7): the `m`-th diagonal
block of the HAM-T oracle is the conjugated Hamiltonian
`e^{iAτm/M} B e^{-iAτm/M}` scaled by `1/α_B`. -/
theorem lemma6_hamt_block_diagonal {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (τ : ℚ) (M : ℕ) (αB : ℝ) (m : Fin M) :
    (fun i j : I => eq20HamtBlock A B τ M αB (m, i) (m, j)) =
      (αB : ℂ)⁻¹ •
        (HamiltonianEvolution A ((τ * (m.val : ℚ) / (M : ℚ) : ℚ) : ℝ) * B *
          HamiltonianEvolution A (-((τ * (m.val : ℚ) / (M : ℚ) : ℚ) : ℝ))) := by
  ext i j
  simp [eq20HamtBlock]

/-- **Lemma 6, Eq. (20) normalization** (fixed arXiv:1805.00675v2, p. 7): the
`m`-th diagonal block of the HAM-T oracle has operator norm `‖B‖/α_B`, because
conjugation by the unitaries `e^{±iAτm/M}` preserves the operator norm. -/
theorem lemma6_hamt_block_norm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (τ : ℚ) (M : ℕ) (αB : ℝ)
    (hα : 0 < αB) (m : Fin M) :
    ‖Matrix.of (fun i j : I => eq20HamtBlock A B τ M αB (m, i) (m, j))‖ = ‖B‖ / αB := by
  have hgen : ∀ s : ℝ,
      ‖(αB : ℂ)⁻¹ • (HamiltonianEvolution A s * B * HamiltonianEvolution A (-s))‖ =
        ‖B‖ / αB := by
    intro s
    have hU : HamiltonianEvolution A s ∈ Matrix.unitaryGroup I ℂ :=
      hamiltonianEvolution_unitary hA s
    have hV : HamiltonianEvolution A (-s) ∈ Matrix.unitaryGroup I ℂ :=
      hamiltonianEvolution_unitary hA (-s)
    rw [norm_smul, Matrix.mul_assoc, CStarRing.norm_mem_unitary_mul _ hU,
      CStarRing.norm_mul_mem_unitary _ hV]
    have hc : ‖(αB : ℂ)⁻¹‖ = αB⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
    rw [hc, div_eq_mul_inv, mul_comm]
  have hmat : Matrix.of (fun i j : I => eq20HamtBlock A B τ M αB (m, i) (m, j)) =
      (αB : ℂ)⁻¹ •
        (HamiltonianEvolution A ((τ * (m.val : ℚ) / (M : ℚ) : ℚ) : ℝ) * B *
          HamiltonianEvolution A (-((τ * (m.val : ℚ) / (M : ℚ) : ℚ) : ℝ))) := by
    ext i j
    exact congrFun (congrFun (lemma6_hamt_block_diagonal A B τ M αB m) i) j
  rw [hmat]
  exact hgen _

/-- **Lemma 6, Eq. (20) contraction** (fixed arXiv:1805.00675v2, p. 7): under
the source's promise `‖B‖ ≤ α_B`, every diagonal block of the HAM-T oracle is
a contraction, i.e. the oracle block is a valid corner of a unitary with the
paper's normalization. -/
theorem lemma6_hamt_block_contraction {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (A B : Matrix I I ℂ) (hA : A.IsHermitian) (τ : ℚ) (M : ℕ)
    (αB : ℝ) (hα : 0 < αB) (hB : ‖B‖ ≤ αB) (m : Fin M) :
    ‖Matrix.of (fun i j : I => eq20HamtBlock A B τ M αB (m, i) (m, j))‖ ≤ 1 := by
  rw [lemma6_hamt_block_norm A B hA τ M αB hα m]
  exact (div_le_one hα).mpr hB

/-- **Lemma 6, item 1** (fixed arXiv:1805.00675v2, p. 7): the run uses
`L = ⌈2α_B t⌉` segments (with at least one when `t` is small), each requiring
one simulation of `e^{-iAτ}`. -/
theorem lemma6_segment_count (p : EffectiveSegmentParameters) :
    ipSegmentCount p = max 1 ⌈2 * p.alpha * abs p.time⌉₊ := rfl

/-- **Lemma 6, item 1** (fixed arXiv:1805.00675v2, p. 7): the segment count is
`O(α_B t)` — explicitly at most `1 + 2α_B|t|`. -/
theorem lemma6_segment_count_le (p : EffectiveSegmentParameters) (hα : 0 ≤ p.alpha) :
    (ipSegmentCount p : ℝ) ≤ 1 + 2 * (p.alpha : ℝ) * |(p.time : ℝ)| := by
  have hq : (0 : ℚ) ≤ 2 * p.alpha * abs p.time :=
    mul_nonneg (mul_nonneg (by norm_num) hα) (abs_nonneg _)
  have hceil : ((⌈2 * p.alpha * abs p.time⌉₊ : ℕ) : ℝ) <
      ((2 * p.alpha * abs p.time : ℚ) : ℝ) + 1 := by
    exact_mod_cast Nat.ceil_lt_add_one hq
  have hqR : ((2 * p.alpha * abs p.time : ℚ) : ℝ) =
      2 * (p.alpha : ℝ) * |(p.time : ℝ)| := by
    push_cast
    rfl
  rw [hqR] at hceil
  have hk : ((⌈2 * p.alpha * abs p.time⌉₊ : ℕ) : ℝ) ≤
      2 * (p.alpha : ℝ) * |(p.time : ℝ)| + 1 := le_of_lt hceil
  have hpos : (0 : ℝ) ≤ 2 * (p.alpha : ℝ) * |(p.time : ℝ)| :=
    mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast hα)) (abs_nonneg _)
  rw [lemma6_segment_count]
  have hmax : ((max 1 ⌈2 * p.alpha * abs p.time⌉₊ : ℕ) : ℝ) =
      max 1 ((⌈2 * p.alpha * abs p.time⌉₊ : ℕ) : ℝ) := by push_cast; rfl
  rw [hmax, max_le_iff]
  constructor <;> linarith

/-- **Lemma 6, item 2** (fixed arXiv:1805.00675v2, p. 7): each segment makes
exactly `computedDysonCutoff (precision+8)` queries to HAM-T. -/
theorem lemma6_segment_queries_eq_cutoff (p : EffectiveSegmentParameters) :
    ipSegmentQueries p = computedDysonCutoff (p.precision + 8) := rfl

/-- **Lemma 6, item 2** (fixed arXiv:1805.00675v2, p. 7): the total number of
HAM-T queries is the number of segments times the per-segment cutoff. -/
theorem lemma6_total_queries (p : EffectiveSegmentParameters) :
    ipTotalQueries p = ipSegmentCount p * computedDysonCutoff (p.precision + 8) := rfl

/-- **Lemma 6, item 3** (fixed arXiv:1805.00675v2, p. 7): the qubit ledger —
the segment width plus the `⌈log₂ L⌉` time-selection wires. -/
theorem lemma6_total_qubits (p : EffectiveSegmentParameters) :
    ipTotalQubits p = ipSegmentWidth (effectiveLongLocal p) + Nat.clog 2 (ipSegmentCount p) :=
  rfl

/-- **Lemma 6, item 4** (fixed arXiv:1805.00675v2, p. 7): the primitive-gate
ledger — per segment the oracle query and the triangle-encoding phase gates,
multiplied by the segment count. -/
theorem lemma6_total_gates (p : EffectiveSegmentParameters) :
    ipTotalGates p = ipSegmentCount p *
      (computedDysonCutoff ((effectiveLongLocal p).precision + 8) +
        computedDysonCutoff ((effectiveLongLocal p).precision + 8)) := rfl

/-- **Lemma 6, item 2 rate** (fixed arXiv:1805.00675v2, p. 7): the per-segment
cutoff obeys the source's `log(1/ε)/log log(1/ε)` rate. -/
theorem lemma6_query_rate :
    ∃ C m0 : ℕ, ∀ k : ℕ, m0 ≤ k →
      computedDysonCutoff (k + 8) * Nat.clog 2 (k + 2) ≤ C * (k + 2) := by
  obtain ⟨C, m0, hrate⟩ := ipLogLogRate
  exact ⟨C, m0, hrate⟩

end Qatlib.Papers.InteractPic18.MainResults.SegmentComposition
