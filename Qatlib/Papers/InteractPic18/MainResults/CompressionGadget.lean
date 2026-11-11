/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveCompressionGadget
import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions

/-!
# CompressionGadget — Lemma 13 of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

* Lemma 13 (Appendix C p. 26, Eqs. (B1)--(B3)): the compression gadget that
  turns `K` controlled applications of unitaries `U_k` into one block-diagonal
  operator on a counter register of width `n_b ∈ O(n_c) = O(log K)`, at the
  price of one query to each `CC-U_k` and `O(K(n_a + log K))` primitive
  gates.

Formalized content: the block-diagonal structure of
`effectiveCompressionBlock ns nb K B` — the counter values above `K` are
killed (Eq. (B3)), two different counter values never mix (the block is
diagonal in the counter), the `m`-th diagonal block is the reversed prefix
product `B m ⋯ B 1` (Eq. (B1)), and a counter register of width
`⌈log₂(K+1)⌉` encodes all `K+1` counter values (`n_b ∈ O(log K)`). Also
recorded is the frozen obstruction `effectiveCompression_naive_reuse_counterexample`:
the counter cannot simply be reused across non-unitary corners, which is why
the gadget must track failed branches.

Boundary: the primitive-gate ledger `O(K(n_a + log K))` is not formalized —
the frozen layer has no program constructor for the gadget, only the block
operator. No query or gate count is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.InteractionEvo
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.InteractPic18.MainResults.CompressionGadget

/-- **Lemma 13, Eq. (B1)** (fixed arXiv:1805.00675v2, Appendix C p. 26): the
compression gadget is block-diagonal in the counter register; entries with
different counter values vanish. -/
theorem lemma13_compression_block_offdiagonal (ns nb K : ℕ)
    (B : ℕ → Matrix (Reg ns) (Reg ns) ℂ) (x y : Reg (ns + nb))
    (hne : (fun i : Fin nb => x ⟨ns + i.val, by omega⟩) ≠
      (fun i : Fin nb => y ⟨ns + i.val, by omega⟩)) :
    effectiveCompressionBlock ns nb K B x y = 0 := by
  simp only [effectiveCompressionBlock]
  rw [if_neg]
  intro h
  exact hne h.1

/-- **Lemma 13, Eq. (B2)** (fixed arXiv:1805.00675v2, Appendix C p. 26): on
counter value `m ≤ K` the gadget entry is the reversed prefix product
`B m ⋯ B 1`, and it vanishes for `m > K` (Eq. (B3)). -/
theorem lemma13_compression_block_entry (ns nb K : ℕ)
    (B : ℕ → Matrix (Reg ns) (Reg ns) ℂ) (x y : Reg (ns + nb))
    (hxy : (fun i : Fin nb => x ⟨ns + i.val, by omega⟩) =
      (fun i : Fin nb => y ⟨ns + i.val, by omega⟩)) :
    effectiveCompressionBlock ns nb K B x y =
      (if effectiveRegNat (fun i : Fin nb => y ⟨ns + i.val, by omega⟩) ≤ K then
        (((List.range (effectiveRegNat (fun i : Fin nb => y ⟨ns + i.val, by omega⟩))).map
          (fun j => B (j + 1))).reverse.prod)
          (fun i : Fin ns => x ⟨i.val, by omega⟩)
          (fun i : Fin ns => y ⟨i.val, by omega⟩)
      else 0) := by
  simp only [effectiveCompressionBlock]
  by_cases hK : effectiveRegNat (fun i : Fin nb => y ⟨ns + i.val, by omega⟩) ≤ K
  · rw [if_pos ⟨hxy, hK⟩, if_pos hK]
  · rw [if_neg (by intro h; exact hK h.2), if_neg hK]

/-- **Lemma 13, Eq. (B3)** (fixed arXiv:1805.00675v2, Appendix C p. 26): all
counter values above `K` are truncated away. -/
theorem lemma13_compression_block_above (ns nb K : ℕ)
    (B : ℕ → Matrix (Reg ns) (Reg ns) ℂ) (x y : Reg (ns + nb))
    (hK : K < effectiveRegNat (fun i : Fin nb => y ⟨ns + i.val, by omega⟩)) :
    effectiveCompressionBlock ns nb K B x y = 0 := by
  simp only [effectiveCompressionBlock]
  rw [if_neg]
  intro h
  exact absurd h.2 (not_le.mpr hK)

/-- **Lemma 13, gadget at counter zero** (fixed arXiv:1805.00675v2, Eq. (B1)
with `m = 0`): on the all-zero counter value the gadget is the identity on the
system register, which is the base case of the `K`-fold product identity. -/
theorem lemma13_compression_block_zero (ns nb K : ℕ)
    (B : ℕ → Matrix (Reg ns) (Reg ns) ℂ) (x y : Reg (ns + nb))
    (hx : (fun i : Fin nb => x ⟨ns + i.val, by omega⟩) = fun _ => false)
    (hy : (fun i : Fin nb => y ⟨ns + i.val, by omega⟩) = fun _ => false) :
    effectiveCompressionBlock ns nb K B x y =
      (if (fun i : Fin ns => x ⟨i.val, by omega⟩) =
          (fun i : Fin ns => y ⟨i.val, by omega⟩) then 1 else 0) := by
  rw [lemma13_compression_block_entry ns nb K B x y (hx.trans hy.symm)]
  have hzero : effectiveRegNat (fun i : Fin nb => y ⟨ns + i.val, by omega⟩) = 0 := by
    rw [hy]
    simp [effectiveRegNat]
  rw [hzero, if_pos (Nat.zero_le K)]
  simp only [List.range_zero, List.map_nil, List.reverse_nil, List.prod_nil]
  exact Matrix.one_apply

/-- **Lemma 13, counter register width** (fixed arXiv:1805.00675v2, Lemma 13:
`n_b ∈ O(n_c) = O(log K)`): a counter register of width `⌈log₂(K+1)⌉` holds
all `K+1` counter values. -/
theorem lemma13_counter_register_width (K : ℕ) :
    ∃ nb : ℕ, K < 2 ^ nb ∧ nb ≤ Nat.clog 2 (K + 1) := by
  refine ⟨Nat.clog 2 (K + 1), ?_, le_rfl⟩
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (K + 1)
  omega

/-- **Lemma 13, counter-reuse obstruction** (fixed arXiv:1805.00675v2,
Appendix C): the gadget cannot be simulated by naively reusing a single
counter across non-unitary corners — two unitary calls can return the ancilla
to its initial value even though each single-call corner vanishes. This is
the frozen counterexample, recorded as the reason the gadget must track
failed branches. -/
theorem lemma13_naive_reuse_obstruction :
    ∃ (R : Matrix Bool Unit ℂ) (U : Matrix Bool Bool ℂ),
      U ∈ Matrix.unitaryGroup Bool ℂ ∧ Rᴴ * R = 1 ∧ Rᴴ * U * R = 0 ∧
        Rᴴ * (U * U) * R = 1 :=
  effectiveCompression_naive_reuse_counterexample

end Qatlib.Papers.InteractPic18.MainResults.CompressionGadget
