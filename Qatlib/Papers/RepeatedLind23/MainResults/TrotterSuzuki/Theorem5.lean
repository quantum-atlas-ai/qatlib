/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepeatedLind23.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# RepeatedLind23 c005 — Theorem 5 (Higher Order Trotter–Suzuki Cost)

Fixed source: arXiv:2312.05371 (2023-12-08 posting), Theorem 5, Eq. (57) on
page 17, proof Eqs. (58)–(62) on pages 17–18.

The RI map is implemented by a `2k`-th order Trotter–Suzuki channel `T^{2k}(t)`
of Definition 4 / Eq. (55). Such a product formula has `Υ = 2·5^{k-1}` stages
(Eq. (56)); repeating the time slice `t/r` for `r` repetitions and multiplying by
the `l` Hamiltonian summands gives `q_TS(2k) = lΥr` exponential gates. The paper
bounds the per-subsystem repetition count by Eq. (62),

`r ≤ ( ((α₀ + mω_n)t + mα_{I_n}√(νt)) / (mν·ε^{1/(2k)}) )^{1 + 1/(2k)}`,

and hence

`q_TS(2k) ∈ O( lΥ·max_n ( ((α₀ + mω_n)t + mα_{I_n}√(νt)) / (mν·ε^{1/(2k)}) )^{1 + 1/(2k)} )`
(Eq. (57)).

This file defines the paper's gate-count expression (`highOrderTrotterGates` in
`SourceModel.lean`) and proves the final assembly step "multiplying by `lΥ`
completes the proof", taking the cited channel-Trotter bound of Ref. [41],
Theorem 2 (Eq. (62)) as an explicit hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Papers.RepeatedLind23.MainResults
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.RepeatedLind23.MainResults.TrotterSuzuki

/-- **Theorem 5** (Higher Order Trotter–Suzuki Cost), arXiv:2312.05371,
Theorem 5 / Eq. (57), p. 17.

Let `q_TS(2k) = lΥr` be the number of exponential gates of the `2k`-th order
Trotter–Suzuki implementation with `Υ = 2·5^{k-1}` stages (Eq. (56)) and `l`
Hamiltonian summands. If the per-subsystem repetition count `r` satisfies the
channel-Trotter bound Eq. (62) (Ref. [41], Theorem 2), then

`q_TS(2k) ≤ lΥ·max_n ( ((α₀ + mω_n)t + mα_{I_n}√(νt))/(mν·ε^{1/(2k)}) )^{1+1/(2k)}`,

i.e. `q_TS(2k) ∈ O(·)` of Eq. (57) with constant `1`. -/
theorem theorem5_higher_order_trotter_cost
    {m : ℕ} (hm : 0 < m) (α0 αI ω : Fin m → ℝ) (ν : ℕ) (t ε : ℝ) (k l : ℕ)
    (qTS r : ℝ) (hl : 0 ≤ (l : ℝ))
    (hq : qTS = (l : ℝ) * (suzukiStages k : ℝ) * r)
    (hr : r ≤ (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      (fun n => highOrderTrotterSteps (α0 n) (αI n) (ω n) m ν t ε k)) :
    qTS ≤ highOrderTrotterGates hm α0 αI ω ν t ε k l := by
  rw [hq, highOrderTrotterGates]
  exact mul_le_mul_of_nonneg_left hr (mul_nonneg hl (by positivity))

/-- **Theorem 5, O-form** (Eq. (57)): the gate count `lΥr` of the `2k`-th order
Trotter–Suzuki implementation is `O` of the paper's budget whenever the
per-subsystem repetition bound Eq. (62) holds. This is the `∈ O(·)` rendering of
`theorem5_higher_order_trotter_cost`; the constant is `1` because Eq. (57) is the
tight product-form bound rather than an asymptotic relaxation. -/
theorem theorem5_higher_order_trotter_cost_O
    {m : ℕ} (hm : 0 < m) (α0 αI ω : Fin m → ℝ) (ν : ℕ) (t ε : ℝ) (k l : ℕ)
    (qTS r : ℝ) (hl : 0 ≤ (l : ℝ))
    (hq : qTS = (l : ℝ) * (suzukiStages k : ℝ) * r)
    (hr : r ≤ (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      (fun n => highOrderTrotterSteps (α0 n) (αI n) (ω n) m ν t ε k)) :
    ∃ C : ℝ, 0 < C ∧ qTS ≤ C * highOrderTrotterGates hm α0 αI ω ν t ε k l :=
  ⟨1, one_pos,
    by simpa using theorem5_higher_order_trotter_cost hm α0 αI ω ν t ε k l qTS r hl hq hr⟩

end Qatlib.Papers.RepeatedLind23.MainResults.TrotterSuzuki
