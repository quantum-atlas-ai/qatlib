/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRelatedKey13.MainResults.HidingFunction.SourceHidingFunction
import Qatlib.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry

set_option backward.isDefEq.respectTransparency false

/-!
# Main result: expected polynomial-time key extraction

Rötteler–Steinwandt, *A note on quantum related-key attacks*, fixed
arXiv:1306.2301v2 (14 Nov 2013), abstract (p. 1) and Section 3 (pp. 3--6):

> if the secret key is (i) uniquely determined by a small number of
> plaintext-ciphertext pairs, (ii) the block cipher can be evaluated
> efficiently, and (iii) a superposition of related keys can be queried, then
> the key can be extracted efficiently.

The attack of Section 3 (p. 6) is:

1. test `s = 0^k` by comparing `E_{0^k}(~m)` with the given tuple `E_s(~m)`;
2. otherwise run Simon's algorithm on the hiding function `f_s` of Theorem 2.

The proof below reuses the compiled verified Simon chain
`QuantumAlgorithm.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry`:

* `simon_verified_actual_trial_success_and_soundness` — one fresh block
  succeeds with probability at least `1/2` and never outputs a wrong key;
* `simon_verified_unbounded_expected_queries_and_cutoff` — the restart kernel
  recovers the secret almost surely with expected at most `2` blocks, and
  `(k+3)` queries per block, i.e. expected `O(k)` oracle queries.

Since each query is one evaluation of `f_s`, whose ledger is polynomial in `k`
by Theorem 2, the total expected work is polynomial; this is
`attackExpectedWork_poly`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Papers.QRelatedKey13.MainResults.SourceModel
open Qatlib.Papers.QRelatedKey13.MainResults.HidingFunction

open scoped ENNReal Classical

namespace Qatlib.Papers.QRelatedKey13.MainResults.KeyExtraction

/-- **Paper Section 3, step 1** (p. 6): comparing `E_{0^k}(~m)` with the given
ciphertext tuple `E_s(~m)` identifies the all-zero key exactly, because the
tuple map `K ↦ E_K(~m)` is injective (hypothesis (i), Section 2.1). -/
theorem zeroKeyTest_iff {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : BooleanVec k)
    (hE : Function.Injective (fun K => E K m)) :
    (E 0 m = E s m ↔ s = 0) := by
  constructor
  · intro h
    exact (hE h).symm
  · intro h
    rw [h]

/-- **Main result** (abstract, p. 1; Section 3, pp. 3--6). Fixed
arXiv:1306.2301v2. Assume hypothesis (i): the secret key is uniquely determined
by the plaintext-ciphertext tuple `~m` (`K ↦ E_K(~m)` injective), and let
`s ≠ 0^k` be the target key, queried through superpositions of related keys
(hypothesis (iii)). Then:

* the encoded hiding function satisfies the Simon promise (Theorem 2);
* the verified Simon restart kernel never fails to halt
  (`generalNeverMass = 0`) and halts with the true key `s` with probability 1;
* the expected number of restart blocks is at most `2`, and therefore the
  expected number of oracle queries is at most `2 * (k + 3)`.

The efficiency hypothesis (ii) enters through `hidingEvalCost_poly`. -/
theorem relatedKey_attack_expected_poly {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : Reg k) (hs : s ≠ ZeroStr k)
    (hE : Function.Injective (fun K => E K m)) :
    BooleanSimonPromise (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s))
        (regBooleanEquiv k s) ∧
      generalNeverMass
        (simonVerifiedRetryKernel (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)))
        (Sum.inr ()) = 0 ∧
      (∑' K : ℕ, haltJoint
        (simonVerifiedRetryKernel (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)))
        (Sum.inr ()) s K) = 1 ∧
      generalUnboundedTime
        (simonVerifiedRetryKernel (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)))
        (Sum.inr ()) ≤ 2 ∧
      ((k + 3 : ℕ) : ℝ≥0∞) *
        generalUnboundedTime
          (simonVerifiedRetryKernel (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)))
          (Sum.inr ()) ≤ (2 * (k + 3) : ℕ) := by
  have hs' : regBooleanEquiv k s ≠ 0 := by
    intro h
    exact hs (regBooleanEquiv_injective k (by rw [h, regBooleanEquiv_zeroStr]))
  have hg := encodedRelatedKeyHidingFunction_simonPromise E m (regBooleanEquiv k s) hE hs'
  obtain ⟨hnever, htime, hhalt, hcost, _htail⟩ :=
    simon_verified_unbounded_expected_queries_and_cutoff
      (n := k) (R := BooleanVec (r * n) × BooleanVec (r * n))
      (f := encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)) (s := s) hg
  exact ⟨hg, hnever, hhalt, htime, hcost⟩

/-- **Complete attack of Section 3** (p. 6): for every target key `s`, either
the direct comparison `E_{0^k}(~m) = E_s(~m)` certifies `s = 0^k` (step 1), or
`s ≠ 0^k` and the verified Simon branch recovers `s` almost surely. -/
theorem relatedKey_attack_complete {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : Reg k)
    (hE : Function.Injective (fun K => E K m)) :
    ((E 0 m = E (regBooleanEquiv k s) m) ↔ s = ZeroStr k) ∧
      (s ≠ ZeroStr k →
        generalNeverMass
          (simonVerifiedRetryKernel (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)))
          (Sum.inr ()) = 0 ∧
        (∑' K : ℕ, haltJoint
          (simonVerifiedRetryKernel (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)))
          (Sum.inr ()) s K) = 1) := by
  refine ⟨?_, fun hs => ?_⟩
  · rw [zeroKeyTest_iff E m (regBooleanEquiv k s) hE]
    constructor
    · intro h
      exact regBooleanEquiv_injective k (by rw [h, regBooleanEquiv_zeroStr])
    · intro h
      rw [h, regBooleanEquiv_zeroStr]
  · obtain ⟨_, hnever, hhalt, _htime, _hcost⟩ :=
      relatedKey_attack_expected_poly E m s hs hE
    exact ⟨hnever, hhalt⟩

/-- **Correctness of the extraction** (paper Section 3, pp. 3--6): the restart
kernel cannot halt on a wrong key. Its total first-halt mass at every `t ≠ s`
is zero, because each completed block is verified against the two-value
identity `f_s(t) = f_s(0)` and a wrong candidate is rejected. -/
theorem relatedKey_attack_output_is_exact {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : Reg k) (hs : s ≠ ZeroStr k)
    (hE : Function.Injective (fun K => E K m)) :
    ∀ t : Reg k, t ≠ s →
      (∑' K : ℕ, haltJoint
        (simonVerifiedRetryKernel (encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)))
        (Sum.inr ()) t K) = 0 := by
  intro t ht
  have hs' : regBooleanEquiv k s ≠ 0 := by
    intro h
    exact hs (regBooleanEquiv_injective k (by rw [h, regBooleanEquiv_zeroStr]))
  have hg := encodedRelatedKeyHidingFunction_simonPromise E m (regBooleanEquiv k s) hE hs'
  have hsound :=
    (simon_verified_actual_trial_success_and_soundness (n := k)
      (R := BooleanVec (r * n) × BooleanVec (r * n))
      (f := encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)) (s := s) hg).2.1 t ht
  apply ENNReal.tsum_eq_zero.mpr
  intro K
  cases K with
  | zero => exact GeneralExecution.runFor_point_halt_zero _ 0 () t
  | succ K =>
    rw [(simon_verified_actual_geometric_joint_law (n := k)
      (R := BooleanVec (r * n) × BooleanVec (r * n))
      (f := encodedRelatedKeyHidingFunction E m (regBooleanEquiv k s)) K t).2, hsound,
      mul_zero]

/-- The paper's expected work ledger for the attack: at most two restart blocks
(`simon_verified_unbounded_expected_queries_and_cutoff`), `k + 3` oracle
queries per block, and `tF` gate operations per query evaluation (paper
Theorem 1's `O(k · t_f + g(k))`, p. 3). -/
def attackExpectedWork (tF k : ℕ) : ℕ :=
  2 * (k + 3) * tF

/-- **Main result, efficiency part** (abstract p. 1; Theorem 2 p. 6): if the
per-query evaluation ledger `t_{f_s}` is polynomially bounded in the key length,
then so is the expected total work `2 · (k+3) · t_{f_s}` of the attack. -/
theorem attackExpectedWork_poly (tF : ℕ → ℕ) (ht : PolyBounded tF) :
    PolyBounded (fun k => attackExpectedWork (tF k) k) := by
  obtain ⟨C, D, hC⟩ := ht
  refine ⟨6 * C, D + 1, fun k => ?_⟩
  unfold attackExpectedWork
  have hk : k + 3 ≤ 3 * (k + 1) := by omega
  calc 2 * (k + 3) * tF k ≤ 2 * (k + 3) * (C * (k + 1) ^ D) :=
        Nat.mul_le_mul_left (2 * (k + 3)) (hC k)
    _ = 2 * C * ((k + 3) * (k + 1) ^ D) := by ring
    _ ≤ 2 * C * ((3 * (k + 1)) * (k + 1) ^ D) :=
        Nat.mul_le_mul_left (2 * C) (Nat.mul_le_mul_right _ hk)
    _ = 6 * C * (k + 1) ^ (D + 1) := by rw [pow_succ]; ring

end Qatlib.Papers.QRelatedKey13.MainResults.KeyExtraction
