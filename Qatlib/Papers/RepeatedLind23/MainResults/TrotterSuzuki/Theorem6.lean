/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepeatedLind23.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# RepeatedLind23 c006 — Theorem 6 (Trotterization Cost)

Fixed source: arXiv:2312.05371 (2023-12-08 posting), Theorem 6, Eq. (63) on
page 18, proof Eqs. (64)–(67) on page 18.

For the first-order Trotter–Suzuki channel (`k = 1`, one stage) the commutator
structure of the RI map gives the sharper explicit bound Eq. (63):

`q_TS(1) ≤ l · max_n [ t^{3/2}/(2ε√ν)·( Σ_j ‖[H₀ⱼ, H_{I_n}]‖ + m‖[H_{E_n}, H_{I_n}]‖ )
                         + t²/(2εν)·Σ_{p,q} (1/m)‖[H₀ₚ, H₀_q]‖ ]`,

where the outer `l` is the number of Hamiltonian summands and `r ≤ [...]` is the
rearranged Trotter error (Eq. (67)). Since `[H_{E_n}, H₀] = 0`, the interaction
commutators are the only ones that survive.

This file defines the Eq. (63) bracket (`firstOrderTrotterBracket` in
`SourceModel.lean`), the outer `l·max_n` bound, and proves the final assembly
step of the paper ("trivially bound the number of operator exponentials `q_TS(1)`
by multiplying by the total number of terms `l`"), with the cited Trotter error
of Ref. [41], Theorem 2 (Eq. (67)) as an explicit hypothesis.
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

/-- Eq. (63) right-hand side: `l · max_n [ t^{3/2}/(2ε√ν)(Σ_j ‖[H₀ⱼ,H_{I_n}]‖ +
m‖[H_{E_n},H_{I_n}]‖) + t²/(2εν)·Σ_{p,q}(1/m)‖[H₀ₚ,H₀_q]‖ ]`.

The `n`-th bracket is `firstOrderTrotterBracket` with the commutator norms
`commHI n = Σ_j ‖[H₀ⱼ, H_{I_n}]‖`, `commEI n = ‖[H_{E_n}, H_{I_n}]‖` and the
system–system commutator sum `commH0`. -/
def firstOrderTrotterGateBound {m : ℕ} (hm : 0 < m)
    (commHI commEI : Fin m → ℝ) (commH0 : ℝ) (t ε ν : ℝ) (l : ℕ) : ℝ :=
  (l : ℝ) * (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun n => firstOrderTrotterBracket (commHI n) (commEI n) commH0 t ε ν (m : ℝ))

/-- **Theorem 6** (Trotterization Cost), arXiv:2312.05371, Theorem 6 / Eq. (63),
p. 18.

Let `q_TS(1) = l·r` be the number of exponential gates of the first-order
Trotter–Suzuki implementation, with `l` Hamiltonian summands and repetition count
`r`. If `r` satisfies the first-order Trotter error bound Eq. (67) (Ref. [41],
Theorem 2, using `[H_{E_n}, H₀] = 0`), then

`q_TS(1) ≤ l · max_n [ t^{3/2}/(2ε√ν)(Σ_j‖[H₀ⱼ,H_{I_n}]‖ + m‖[H_{E_n},H_{I_n}]‖)
                        + t²/(2εν)·Σ_{p,q}(1/m)‖[H₀ₚ,H₀_q]‖ ]`,

which is exactly Eq. (63). -/
theorem theorem6_trotterization_cost
    {m : ℕ} (hm : 0 < m) (commHI commEI : Fin m → ℝ) (commH0 : ℝ)
    (t ε ν : ℝ) (l : ℕ) (qTS r : ℝ) (hl : 0 ≤ (l : ℝ))
    (hq : qTS = (l : ℝ) * r)
    (hr : r ≤ (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      (fun n => firstOrderTrotterBracket (commHI n) (commEI n) commH0 t ε ν (m : ℝ))) :
    qTS ≤ firstOrderTrotterGateBound hm commHI commEI commH0 t ε ν l := by
  rw [hq, firstOrderTrotterGateBound]
  exact mul_le_mul_of_nonneg_left hr hl

/-- Eq. (63) as an `O(·)` statement: the first-order Trotter–Suzuki gate count
`l·r` is bounded by `1` times the paper's Eq. (63) bracket, given the
per-subsystem Trotter bound Eq. (67). The constant is `1` because Eq. (63) is a
tight inequality, not an asymptotic relaxation. -/
theorem theorem6_trotterization_cost_O
    {m : ℕ} (hm : 0 < m) (commHI commEI : Fin m → ℝ) (commH0 : ℝ)
    (t ε ν : ℝ) (l : ℕ) (qTS r : ℝ) (hl : 0 ≤ (l : ℝ))
    (hq : qTS = (l : ℝ) * r)
    (hr : r ≤ (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      (fun n => firstOrderTrotterBracket (commHI n) (commEI n) commH0 t ε ν (m : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ qTS ≤ C * firstOrderTrotterGateBound hm commHI commEI commH0 t ε ν l :=
  ⟨1, one_pos,
    by simpa using theorem6_trotterization_cost hm commHI commEI commH0 t ε ν l qTS r hl hq hr⟩

end Qatlib.Papers.RepeatedLind23.MainResults.TrotterSuzuki
