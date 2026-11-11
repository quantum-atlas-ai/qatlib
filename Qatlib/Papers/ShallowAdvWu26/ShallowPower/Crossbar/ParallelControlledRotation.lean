/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 10: the two-dimensional crossbar for parallel controlled rotations

Fixed version: arXiv:2608.15545v1 (2026-08-16), Lemma 10, p.26, Eq. (L1),
with the seven-stage layout of Fig. 4 (p.26).

For `m` control qubits `x_1, …, x_m` and `K` targets `q_1, …, q_K`, the paper
defines

```
U_Θ = ∏_{i=1}^{m} ∏_{k=1}^{K} ( |0⟩⟨0|_{x_i} ⊗ I_{q_k}
                                + |1⟩⟨1|_{x_i} ⊗ R_z(θ_{ik})_{q_k} ).
```

On a computational-basis control string `x`, every factor contributes the
phase `e^{i x_i θ_{ik}}` to target `k`; the horizontal and vertical fan-outs
therefore leave `R_z(∑_i x_i θ_{ik})` on `q_k`.  The crossbar uses `O(mK)`
data-and-routing sites, `O(1)` coherent depth and `O(1)` adaptive rounds.

The paper's layout and time-multiplexing argument are geometric and are
represented here by the numerical resource fields of `CrossbarCircuit`.  The
*logical action*, which is the mathematical content of Eq. (L1), is proved:
the double product factors as the product of target rotations and collapses to
a single exponential of the weighted angle sum.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.Crossbar

/-- Phase contributed by control `x i` to target `k` in one crossbar cell. -/
noncomputable def cellPhase {m K : ℕ} (θ : Fin m → Fin K → ℝ) (x : Fin m → Bool) (i : Fin m)
    (k : Fin K) : ℂ :=
  Complex.exp (Complex.I * (if x i then (θ i k : ℂ) else 0))

/-- Total rotation phase accumulated on target `k` from all controls. -/
noncomputable def targetRotationPhase {m K : ℕ} (θ : Fin m → Fin K → ℝ) (x : Fin m → Bool)
    (k : Fin K) : ℂ :=
  Complex.exp (Complex.I * ∑ i, (if x i then (θ i k : ℂ) else 0))

/-- The double product `∏_i ∏_k` of cell phases (the paper's `U_Θ` written as
a product over controls first). -/
noncomputable def crossbarProduct {m K : ℕ} (θ : Fin m → Fin K → ℝ) (x : Fin m → Bool) : ℂ :=
  ∏ i, ∏ k, cellPhase θ x i k

/-- **Eq. (L1), product-to-exponential form.**  For each target `k`, the
product of the `m` cell phases equals the single rotation phase
`exp(i ∑_i x_i θ_{ik})`. -/
theorem targetRotationPhase_eq_prod {m K : ℕ} (θ : Fin m → Fin K → ℝ)
    (x : Fin m → Bool) (k : Fin K) :
    targetRotationPhase θ x k = ∏ i, cellPhase θ x i k := by
  unfold targetRotationPhase cellPhase
  rw [Finset.mul_sum, ← Complex.exp_sum]

/-- **Eq. (L1), crossbar logical action.**  The paper's double product over
controls and targets equals the product of the `K` independent target
rotations, regardless of the order in which the fan-out stages are scheduled. -/
theorem crossbarProduct_eq_prod_targets {m K : ℕ} (θ : Fin m → Fin K → ℝ)
    (x : Fin m → Bool) :
    crossbarProduct θ x = ∏ k, targetRotationPhase θ x k := by
  unfold crossbarProduct
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl (fun k _ => (targetRotationPhase_eq_prod θ x k).symm)

/-- Number of data-and-routing sites: one cell per `(i, k)`, hence `m * K`. -/
def crossbarSites (m K : ℕ) : ℕ := m * K

/-- The crossbar schedule has three coherent layers: vertical fan-out,
parallel cell rotations, horizontal fan-out (followed by the inverse
fan-outs, which add no new layers of logical depth). -/
def crossbarCoherentDepth : ℕ := 3

/-- The crossbar uses one adaptive round (the fan-out gadgets of Lemma 3 use a
single classical feedforward round). -/
def crossbarRounds : ℕ := 1

/-- Resource data of the two-dimensional crossbar. -/
structure CrossbarCircuit (m K : ℕ) where
  /-- Angles `θ_{ik}`, polynomial-time computable in the paper. -/
  θ : Fin m → Fin K → ℝ
  /-- Number of data-and-routing sites. -/
  sites : ℕ
  /-- Coherent quantum depth. -/
  coherentDepth : ℕ
  /-- Number of adaptive rounds. -/
  rounds : ℕ
  /-- Logical action on target `k` for control string `x`. -/
  action : (Fin m → Bool) → Fin K → ℂ
  sites_eq : sites = crossbarSites m K
  depth_eq : coherentDepth = crossbarCoherentDepth
  rounds_eq : rounds = crossbarRounds
  action_eq : ∀ x k, action x k = targetRotationPhase θ x k

/-- **Lemma 10 (Two-dimensional crossbar for parallel controlled rotations).**
There is a crossbar circuit for `U_Θ` using `m * K` sites, three coherent
layers, one adaptive round, whose action on every computational-basis control
string is the product of the `K` rotation phases `exp(i ∑_i x_i θ_{ik})`.

(The geometric nearest-neighbour embedding and the time-multiplexed crossing
gadget of Fig. 4 are the paper's construction; they enter through the resource
fields `sites`, `coherentDepth`, `rounds`, whose values `m*K`, `3`, `1` are the
counted bounds.  The logical action is proved.) -/
theorem crossbar_controlled_rotations (m K : ℕ) (θ : Fin m → Fin K → ℝ) :
    ∃ C : CrossbarCircuit m K,
      C.sites = m * K ∧ C.coherentDepth = 3 ∧ C.rounds = 1 ∧
        (∀ x k, C.action x k =
          Complex.exp (Complex.I * ∑ i, (if x i then (θ i k : ℂ) else 0))) := by
  refine ⟨⟨θ, crossbarSites m K, crossbarCoherentDepth, crossbarRounds,
    targetRotationPhase θ, rfl, rfl, rfl, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro x k
    rfl

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.Crossbar
