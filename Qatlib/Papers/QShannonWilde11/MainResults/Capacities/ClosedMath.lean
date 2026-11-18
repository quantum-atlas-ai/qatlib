/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ProtocolCaps

@[expose] public section


/-!
# Reviewed closed fragment of Wilde, arXiv:1106.1445v8

Only closed definitions and proofs are present. Capacity records have unconstrained
fields; conditional limits and averaging steps do not establish operational coding
or source algorithm costs. See the per-declaration source review receipt.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.Capacities

open Matrix
open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Filter Topology
open scoped BigOperators

noncomputable section

/-- Pauli entropy `H(p) = −Σ_j p_j log p_j` of a Pauli channel. -/
def pauliEnt (h : HashingCode) : ℝ :=
  -(h.pI * Real.log h.pI + h.pX * Real.log h.pX +
    h.pY * Real.log h.pY + h.pZ * Real.log h.pZ)

/-- **Lemma 25.4.1** — arXiv:1106.1445v8, fixed PDF p. 707. If a dynamic-capacity formula
`f` is additive against every channel, then its regularised version equals `f`
itself at every block length, hence single-letterises.
Proved from the additivity hypothesis and the tensor-power recursion; the
operational meaning is inherited from the interface field `C.dynCap`/`C.reg`.
Deps: `QChanInfo.reg`, `QChanInfo.tensor`, `QChanInfo.tensorPow`. -/
theorem reg_eq_and_tendsto_of_additive_tensor_power (C : QChanInfo) (f : C.Ch → ℝ) (N : C.Ch)
    (hadd : ∀ M, f (C.tensor N M) = f N + f M)
    (h1 : C.tensorPow N 1 = N)
    (hstep : ∀ k, 1 ≤ k → C.tensorPow N (k + 1) = C.tensor N (C.tensorPow N k)) :
    (∀ k, 1 ≤ k → C.reg f N k = f N) ∧
      Tendsto (fun k => C.reg f N k) atTop (nhds (f N)) := by
  have hpow : ∀ k, 1 ≤ k → f (C.tensorPow N k) = (k : ℝ) * f N := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp [h1]
      · have ihk : f (C.tensorPow N k) = (k : ℝ) * f N := ih (by omega)
        rw [hstep k (by omega), hadd, ihk]
        push_cast
        ring
  have hconst : ∀ k, 1 ≤ k → C.reg f N k = f N := by
    intro k hk
    unfold QChanInfo.reg
    rw [hpow k hk]
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hkpos)]
  refine ⟨hconst, ?_⟩
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hconst k hk⟩] with k hk
  exact hk.symm

/-- Specialize an assumed equality of dynamic and single-letter regions to one channel.
This is the literal model bridge retained for Theorem 25.4.1 of
arXiv:1106.1445v8, fixed PDF p. 707; it proves no optimisation or coding result.
Deps: `DynInfo.dynRegion`, `DynInfo.slRegionOf`. -/
theorem dyn_region_eq_single_letter_of_forall (D : DynInfo) (N : D.Ch)
    (hsl : ∀ M, D.dynRegion M = D.slRegionOf M) :
    D.dynRegion N = D.slRegionOf N :=
  hsl N

end

end Qatlib.Papers.QShannonWilde11.MainResults.Capacities
