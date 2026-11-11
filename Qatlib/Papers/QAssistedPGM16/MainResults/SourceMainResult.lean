/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAssistedPGM16.MainResults.SourceLearningRule

set_option backward.isDefEq.respectTransparency false

/-!
# QAssistedPGM16 — main result: hardware-embedded gray-box training

Fixed source: arXiv:1609.02542, abstract and Sec. II D / Sec. III (p.1-6).

Claim c001 of the paper's extraction states the main construction: data are
enlarged by an embedding that replicates every logical variable inside a
hardware subgraph (Eq. (6), p.5), a fully visible quantum Boltzmann model is
trained on the enlarged data, and the gray-box learning rule works without
knowledge of the effective temperature or transverse field (p.2-3, p.5-6).

This file records the two mathematical components of that claim:

* `blockEmbedding` / `blockEmbedding_spin`: the replication map of Eq. (6) sends
  every physical copy in the block of logical variable `i` to the same logical
  spin;
* `gray_box_training_temperature_free`: the update direction of the learning
  rule is the positive-minus-negative phase correlator difference.  The
  inverse temperature `β` only rescales the learning rate, so no per-iteration
  estimate of `β` (or of the effective transverse field) is needed.

The physical premise that the annealer samples a Gibbs-like distribution
(p.5) is an assumption of the source experiment and is not asserted here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QAssistedPGM16.MainResults

/-- Replication embedding of Eq. (6), p.5, in its simplest uniform-block form:
logical variable `i` of a data point `s : Fin N → Bool` is copied into the `Q`
physical qubits indexed by `Fin N × Fin Q ≃ Fin (N*Q)`. -/
def blockEmbedding (N Q : ℕ) (s : Fin N → Bool) : Config (N * Q) :=
  fun k => s (finProdFinEquiv.symm k).1

/-- Every physical copy of logical variable `i` carries the spin of `s i`. -/
theorem blockEmbedding_spin (N Q : ℕ) (s : Fin N → Bool) (i : Fin N) (k : Fin Q) :
    spin (blockEmbedding N Q s) (finProdFinEquiv (i, k)) = spin s i := by
  unfold blockEmbedding spin
  simp

/-- All copies of one logical variable agree: the redundancy introduced by the
embedding is exact (Eq. (6), p.5). -/
theorem blockEmbedding_replicates (N Q : ℕ) (s : Fin N → Bool) (i : Fin N) (k l : Fin Q) :
    spin (blockEmbedding N Q s) (finProdFinEquiv (i, k)) =
      spin (blockEmbedding N Q s) (finProdFinEquiv (i, l)) := by
  rw [blockEmbedding_spin, blockEmbedding_spin]

/-- Main structural claim of c001 (p.1-6): the gray-box parameter update
direction depends only on measured phase averages, not on the effective
temperature.  For any data weights `p` and Gibbs model at inverse temperature
`β ≠ 0`, the unit-speed log-likelihood derivative in coordinate `a` is
`g = ⟨A_a⟩_{ρ_D} − ⟨A_a⟩_ρ`; equivalently the update
`θ_a ← θ_a + η g` is gradient ascent on `L/β` and requires neither `β` nor the
effective transverse field. -/
theorem gray_box_training_temperature_free {M : ℕ} (p : Config M → ℝ)
    (hp : ∑ z : Config M, p z = 1) (β : ℝ) (hβ : β ≠ 0)
    (θ : ParamIndex M → ℝ) (a : ParamIndex M) :
    ∃ g : ℝ,
      g = (∑ z : Config M, p z * feature a z) - expectation β θ (feature a) ∧
      HasDerivAt
        (fun t : ℝ => (1 / β) * -relativeEntropy p (gibbsDist β (path θ a t))) g 0 := by
  refine ⟨_, rfl, ?_⟩
  have h := (logLikelihood_gradient p hp β θ a).const_mul (1 / β)
  convert h using 1
  field_simp [hβ]

end Qatlib.Papers.QAssistedPGM16.MainResults
