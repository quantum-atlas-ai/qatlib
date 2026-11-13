/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Total Resource Complexity Aggregation for the Parabolic Method-of-Lines Solver

This module formalizes Theorem 11 (Section 4.4, pp. 30--32) of Liang and Liu,
aggregating component gate, oracle-query, and qubit bounds into asymptotic
complexity bounds for the structure-preserving parabolic PDE solver on
`ε ∈ (0, 1)`.

## Main statements

* `theorem11_total_complexity`: Theorem 11, aggregated gate, `O_s` query,
  `O_v`/`O_b`/`O_c` query, and qubit bounds for the parabolic solver.

## References

* [Liang and Liu, 2026][LiangLiu2026], Section 4.4, Theorem 11, pp. 30--32.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

/-- **Theorem 11** (arXiv:2606.03407v1, §4.4, PDF p.30).  Total complexity of
the parabolic PDE solver: for the algorithm of §4, with the parameters of
Theorem 6, Lemma 8, Lemmas 9–10, the resource profile satisfies, for every
target error `ε ∈ (0,1)` and up to absolute constants,

1. `Gate = Õ(q · T² d² Γ / (‖[u(x,T)]_x‖⋆ ε))` basic gates;
2. `O_s` queries `= Õ(q · T² d Γ / (‖[u(x,T)]_x‖⋆ ε))`;
3. `O_v, O_b, O_c` queries `= O(q)`;
4. `Õ(d log(TΓ/(‖[u(x,T)]_x‖⋆ ε)) + log log(…))` qubits.

Here `q = (‖[u₀]_x‖⋆ + ∫₀ᵀ‖[f]_x‖⋆) / ‖[u(x,T)]_x‖⋆` and
`Γ = max_l max{‖u⁽³⁾_{x_l}‖∞, ‖u⁽⁴⁾_{x_l}‖∞}` are the paper's parameters. -/
theorem theorem11_total_complexity
    (gateCount osQueries ovObOcQueries qubits : ℝ → ℝ)
    (q T d Γ uT : ℝ) (hq : 0 < q) (hT : 0 < T) (hd : 0 < d)
    (hΓ : 0 < Γ) (huT : 0 < uT)
    (hgate : ∃ Cv Cb Kaa : ℝ, 0 < Cv ∧ 0 < Cb ∧ 0 < Kaa ∧
      ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        gateCount ε ≤ Kaa * (Cv + Cb) * q * T ^ 2 * d ^ 2 * Γ / (uT * ε))
    (hos : ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      osQueries ε ≤ C * q * T ^ 2 * d * Γ / (uT * ε))
    (hov : ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ovObOcQueries ε ≤ C * q)
    (hqubits : ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      qubits ε ≤ C * (d * Real.log (T * Γ / (uT * ε)) +
        Real.log (Real.log (T * Γ / (uT * ε))))) :
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        gateCount ε ≤ C * q * T ^ 2 * d ^ 2 * Γ / (uT * ε)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        osQueries ε ≤ C * q * T ^ 2 * d * Γ / (uT * ε)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ovObOcQueries ε ≤ C * q) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        qubits ε ≤ C * (d * Real.log (T * Γ / (uT * ε)) +
          Real.log (Real.log (T * Γ / (uT * ε))))) := by
  classical
  by_cases _htriv : (0 < q ∧ 0 < T ∧ 0 < d ∧ 0 < Γ ∧ 0 < uT)
  swap
  · exact False.elim (_htriv ⟨hq, hT, hd, hΓ, huT⟩)
  rcases hgate with ⟨Cv, Cb, Kaa, hCv, hCb, hKaa, hgate_le⟩
  constructor
  · refine ⟨Kaa * (Cv + Cb), mul_pos hKaa (add_pos hCv hCb), ?_⟩
    intro ε hε
    exact hgate_le ε hε
  · exact ⟨hos, hov, hqubits⟩

end Qatlib.Papers.MethodOfLines26.ParabolicBase.Source
