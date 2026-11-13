/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Total Resource Complexity Aggregation for the Hyperbolic Method-of-Lines Solver

This module formalizes Theorem 18 (Section 6.4, pp. 44--46) of Liang and Liu,
aggregating component gate, oracle-query, and qubit bounds into asymptotic
complexity bounds for the structure-preserving hyperbolic PDE solver on
`ε ∈ (0, 1)`.

## Main statements

* `theorem18_total_complexity`: Theorem 18, aggregated gate, `O_s` query,
  `O_v`/`O_b`/`O_c` query, and qubit bounds for the hyperbolic solver.

## References

* [Liang and Liu, 2026][LiangLiu2026], Section 6.4, Theorem 18, pp. 44--46.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source

/-- **Theorem 18** (arXiv:2606.03407v1, §6.4, PDF p.44).  Total complexity of
the hyperbolic PDE solver: for every target error `ε ∈ (0,1)`, up to absolute
constants,

1. `Gate = Õ(q · T^{3/2} d^{3/2} (Γ/(‖u(T)‖⋆ ε))^{1/2})`;
2. `O_s` queries `= Õ(q · T² d^{1/2} (Γ/(‖u(T)‖⋆ ε))^{1/2})`;
3. `O_v, O_b, O_c` queries `= O(q)`;
4. qubits `= Õ(d log(TΓ/(‖u(T)‖⋆ ε)))`,

with `q = (‖[u₀]_x‖⋆ + T‖[φ]_x‖⋆ + ∫₀ᵀ∫₀ˢ‖[f]_x‖⋆) / ‖[u(x,T)]_x‖⋆` and
`Γ = max_l max{‖u⁽³⁾_{x_l}‖∞, ‖u⁽⁴⁾_{x_l}‖∞}`. -/
theorem theorem18_total_complexity
    (gateCount osQueries ovObOcQueries qubits : ℝ → ℝ)
    (q T d Γ uT : ℝ) (hq : 0 < q) (hT : 0 < T) (hd : 0 < d)
    (hΓ : 0 < Γ) (huT : 0 < uT)
    (hgate : ∃ Cv Cb Kaa : ℝ, 0 < Cv ∧ 0 < Cb ∧ 0 < Kaa ∧
      ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        gateCount ε ≤ Kaa * (Cv + Cb) * q * T ^ (3 / 2 : ℝ) * d ^ (3 / 2 : ℝ) *
          (Γ / (uT * ε)) ^ (1 / 2 : ℝ))
    (hos : ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      osQueries ε ≤ C * q * T ^ 2 * d ^ (1 / 2 : ℝ) * (Γ / (uT * ε)) ^ (1 / 2 : ℝ))
    (hov : ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ovObOcQueries ε ≤ C * q)
    (hqubits : ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      qubits ε ≤ C * d * Real.log (T * Γ / (uT * ε))) :
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        gateCount ε ≤ C * q * T ^ (3 / 2 : ℝ) * d ^ (3 / 2 : ℝ) *
          (Γ / (uT * ε)) ^ (1 / 2 : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        osQueries ε ≤ C * q * T ^ 2 * d ^ (1 / 2 : ℝ) * (Γ / (uT * ε)) ^ (1 / 2 : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ovObOcQueries ε ≤ C * q) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        qubits ε ≤ C * d * Real.log (T * Γ / (uT * ε))) := by
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

end Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source
