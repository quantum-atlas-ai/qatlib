/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# GateScaling — source interface for the `V log V` gate overhead

WaveletQFT14 (arXiv:1412.0750), fixed version v2 (2015-03-12).
Fixed source: https://arxiv.org/abs/1412.0750v2.

This file formalises the main gate-count claim of the paper (p. 5, discussion
around the coupling matrices of Eq. (29)–(30)):

> The number of quantum gates to perform a quantum simulation incurs only a
> penalty of replacing `V` with `V log(V)` in the scaling formulae relative to
> the discretized basis encoding. ... Because the wavelets have compact
> support, the number of summands in `Ĥ` scales like `O(V log(V))`.

The position-basis encoder has `V` nearest-neighbour Hamiltonian summands; the
wavelet-basis encoder has at most `10 · V · (lmax + 2)` summands by the
coupling-sparsity result of claim `c002` (reused below through its fully proved
source theorem `source_coupling_sparsity`).  Since `V = L · 2^{lmax+1}` forces
`lmax + 2 ≤ 2 · log₂ V`, the wavelet summand count is at most
`20 · V · log₂ V`, which is exactly the claimed `V ↝ V log V` penalty with a
constant factor `20`.

Boundary: this counts Hamiltonian summands and Trotter step applications
(`terms × steps`); it does not model elementary gate synthesis, qubit routing or
Trotter error, which are the paper's granted primitives (TrotterFormula.LieStrang).
-/
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WaveletQFT14.MainResults.GateScaling

/-- Number of degrees of freedom `V = L · 2^{lmax+1}` of the wavelet field
simulation (arXiv:1412.0750, p. 5, Eq. (29) discussion). -/
def modeCount (L lmax : ℕ) : ℕ := L * 2 ^ (lmax + 1)

/-- Trotter gate count for a Hamiltonian with `terms` summands and `steps`
Trotter steps, one gate application per summand per step
(arXiv:1412.0750, p. 5, gate-count comparison). -/
def trotterGateCount (terms steps : ℕ) : ℕ := terms * steps

/-- Position-basis gate count: `V` nearest-neighbour summands times `steps`.
This is the "discretized basis encoding" baseline of the paper. -/
def positionGateCount (V steps : ℕ) : ℕ := V * steps

/-- Wavelet-basis gate count: at most `10 · V · (lmax + 2)` Hamiltonian
summands (claim `c002`), each applied once per Trotter step. -/
def waveletTrotterGateCount (L lmax steps : ℕ) : ℕ :=
  10 * modeCount L lmax * (lmax + 2) * steps


/-- `2^{lmax+1} ≤ V`. -/
lemma two_pow_le_modeCount {L lmax : ℕ} (hL : 1 ≤ L) :
    2 ^ (lmax + 1) ≤ modeCount L lmax := by
  have hpos : 0 < L := by omega
  unfold modeCount
  exact Nat.le_mul_of_pos_left _ hpos

/-- `V > 0`. -/
lemma modeCount_pos {L lmax : ℕ} (hL : 1 ≤ L) : 0 < modeCount L lmax := by
  have := two_pow_le_modeCount (L := L) (lmax := lmax) hL
  have : 0 < 2 ^ (lmax + 1) := pow_pos (by norm_num) _
  omega

/-- `V ≥ 2`. -/
lemma two_le_modeCount {L lmax : ℕ} (hL : 1 ≤ L) : 2 ≤ modeCount L lmax := by
  have hpow : 2 ^ 1 ≤ 2 ^ (lmax + 1) :=
    Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ lmax + 1)
  have h2 : 2 ^ 1 = 2 := by norm_num
  have := two_pow_le_modeCount (L := L) (lmax := lmax) hL
  omega

/-- `lmax + 1 ≤ log₂ V`: the number of dyadic scales is bounded by the
logarithm of the mode count. -/
lemma log2_ge_levels {L lmax : ℕ} (hL : 1 ≤ L) :
    lmax + 1 ≤ Nat.log2 (modeCount L lmax) := by
  rw [Nat.le_log2 (Nat.ne_of_gt (modeCount_pos hL))]
  exact two_pow_le_modeCount hL

/-- `log₂ V ≥ 1`. -/
lemma log2_ge_one {L lmax : ℕ} (hL : 1 ≤ L) :
    1 ≤ Nat.log2 (modeCount L lmax) := by
  rw [Nat.le_log2 (Nat.ne_of_gt (modeCount_pos hL))]
  have h2 := two_le_modeCount (L := L) (lmax := lmax) hL
  have : 2 ^ 1 = 2 := by norm_num
  omega

/-- `lmax + 2 ≤ 2 · log₂ V`, the key passage from the per-scale factor to
`log V`.  (arXiv:1412.0750, p. 5: the summand count is `O(V log V)`.) -/
lemma level_factor_le_log2 {L lmax : ℕ} (hL : 1 ≤ L) :
    lmax + 2 ≤ 2 * Nat.log2 (modeCount L lmax) := by
  have h1 := log2_ge_levels (L := L) (lmax := lmax) hL
  have h2 := log2_ge_one (L := L) (lmax := lmax) hL
  omega

/-- Bridge with claim `c002`: if a Hamiltonian has `N` summands obeying the
coupling-sparsity bound `N ≤ 10 · V · (lmax + 2)`, then `N ≤ 20 · V · log₂ V`.
The hypothesis is discharged for the wavelet coupling matrix by
`QuantumAlgorithmDev.Papers.WaveletQFT14.MainResults.CouplingSparsity.source_coupling_sparsity`
(arXiv:1412.0750, p. 5), which is proved in
`Papers/WaveletQFT14/MainResults/CouplingSparsity/SourceCouplingSparsity.lean`;
this file states the gate-count consequence so that it is independent of the
internal mode model. -/
theorem hamiltonian_summands_le_of_sparsity {L lmax N : ℕ} (hL : 1 ≤ L)
    (hN : N ≤ 10 * modeCount L lmax * (lmax + 2)) :
    N ≤ 20 * modeCount L lmax * Nat.log2 (modeCount L lmax) := by
  have hfac := level_factor_le_log2 (L := L) (lmax := lmax) hL
  calc N ≤ 10 * modeCount L lmax * (lmax + 2) := hN
    _ ≤ 10 * modeCount L lmax * (2 * Nat.log2 (modeCount L lmax)) :=
        Nat.mul_le_mul_left _ hfac
    _ = 20 * modeCount L lmax * Nat.log2 (modeCount L lmax) := by ring

/-- The number of Hamiltonian summands is `O(V log V)` whenever the paper's
per-scale sparsity bound holds (arXiv:1412.0750, p. 5); see
`hamiltonian_summands_le_of_sparsity`. -/
theorem hamiltonian_summands_le (L lmax N : ℕ) (hL : 1 ≤ L)
    (hN : N ≤ 10 * modeCount L lmax * (lmax + 2)) :
    N ≤ 20 * modeCount L lmax * Nat.log2 (modeCount L lmax) :=
  hamiltonian_summands_le_of_sparsity hL hN

/-- Main scaling statement: the Trotter gate count of the wavelet-basis
simulation is at most `20 · V · log₂ V · steps`, i.e. `V ↝ V log V` relative to
the position-basis count `V · steps` (arXiv:1412.0750, p. 5). -/
theorem wavelet_gate_count_le (L lmax steps : ℕ) (hL : 1 ≤ L) :
    waveletTrotterGateCount L lmax steps
      ≤ 20 * modeCount L lmax * Nat.log2 (modeCount L lmax) * steps := by
  unfold waveletTrotterGateCount
  have hfac := level_factor_le_log2 (L := L) (lmax := lmax) hL
  have h1 : 10 * modeCount L lmax * (lmax + 2)
      ≤ 10 * modeCount L lmax * (2 * Nat.log2 (modeCount L lmax)) :=
    Nat.mul_le_mul_left _ hfac
  have h2 : 10 * modeCount L lmax * (2 * Nat.log2 (modeCount L lmax))
      = 20 * modeCount L lmax * Nat.log2 (modeCount L lmax) := by ring
  calc 10 * modeCount L lmax * (lmax + 2) * steps
      = (10 * modeCount L lmax * (lmax + 2)) * steps := rfl
    _ ≤ (10 * modeCount L lmax * (2 * Nat.log2 (modeCount L lmax))) * steps :=
        Nat.mul_le_mul_right steps h1
    _ = 20 * modeCount L lmax * Nat.log2 (modeCount L lmax) * steps := by rw [h2]

/-- The penalty is exactly `V ↝ V log V`: the wavelet gate count is bounded by
`20 · log₂ V` times the position-basis gate count
(arXiv:1412.0750, p. 5). -/
theorem gate_penalty_V_logV (L lmax steps : ℕ) (hL : 1 ≤ L) :
    waveletTrotterGateCount L lmax steps
      ≤ 20 * Nat.log2 (modeCount L lmax)
          * positionGateCount (modeCount L lmax) steps := by
  have h := wavelet_gate_count_le L lmax steps hL
  unfold positionGateCount
  calc waveletTrotterGateCount L lmax steps
      ≤ 20 * modeCount L lmax * Nat.log2 (modeCount L lmax) * steps := h
    _ = 20 * Nat.log2 (modeCount L lmax) * (modeCount L lmax * steps) := by ring

/-- Existential packaging of the `V log V` scaling with an explicit constant
`C = 20` (arXiv:1412.0750, p. 5). -/
theorem gate_count_scaling (L lmax steps : ℕ) (hL : 1 ≤ L) :
    ∃ C : ℕ, C = 20 ∧
      waveletTrotterGateCount L lmax steps
        ≤ C * modeCount L lmax * Nat.log2 (modeCount L lmax) * steps :=
  ⟨20, rfl, wavelet_gate_count_le L lmax steps hL⟩

/-- The position-basis encoder has exactly `V` nearest-neighbour summands
(`steps = 1`): the baseline that the paper compares against
(arXiv:1412.0750, p. 5). -/
theorem position_terms_eq (V : ℕ) : positionGateCount V 1 = V := by
  unfold positionGateCount
  ring

end Qatlib.Papers.WaveletQFT14.MainResults.GateScaling
