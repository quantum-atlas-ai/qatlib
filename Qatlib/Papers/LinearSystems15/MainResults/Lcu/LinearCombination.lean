/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.GeomSum
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# LinearSystems15 — linear combinations of unitaries

Paper-layer statements for Childs–Kothari–Somma (arXiv:1511.02306), §2.1.

* `lemma6_lcu_corner` — source **Lemma 6** (pp. 6–7, eq. (4)): the corner
  fibre of `W = V† U V` on `|0^m>|ψ>` is `(1/α) M|ψ>`.  This is the frozen
  LCU contraction `lcu_corner_apply`, rewritten with the paper's weights
  `α_i/α` and matrix `M = Σ α_i U_i`.
* `lemma7_nonunitary_lcu_corner` — source **Lemma 7** (pp. 7–8, eqs. (5)–(11)):
  when each `U_i` block-encodes `T_i` on the `|0^t>` block, the `|0^m>|0^t>`
  fibre of `W` is `(1/α) M|φ>` with `M = Σ α_i T_i`.  The amplitude
  amplification / expected-cost layer is documented but not formalised here.
* `lemma8_powers_gate_cost` — source **Lemma 8** (p. 8): the binary-controlled
  expansion of `U = Σ_{i≤N} |i><i| ⊗ Y^i` costs `O(Σ_j G_j) = O(N G)` gates.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Qatlib.Papers.LinearSystems15.MainResults.Lcu

open Matrix
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BlockEncoding.LinearCombination
variable {J I T : Type*} [Fintype J] [DecidableEq J] [Nonempty J] [Fintype I]
  [DecidableEq I] [Fintype T] [DecidableEq T]

/-! ## Lemma 6 — the LCU corner contraction -/

/-- **Source Lemma 6** (arXiv:1511.02306, §2.1, pp. 6–7, eq. (4)).
Let `M = Σ_i α_i U_i` with `α_i > 0`, `α = Σ_i α_i`, and let `V` (`P` here)
satisfy `V|0^m> = (1/√α) Σ_i √α_i |i>`.  Then the `|0^m>` corner fibre of
`W = V† (Σ_i |i><i| ⊗ U_i) V` on `|0^m>|ψ>` is exactly `(1/α) M|ψ>`.

This is the paper's equation (4) in corner form: the remainder `|Ψ⊥>`
is precisely the part of `W|0^m>|ψ>` outside the `j₀` corner, i.e. it has no
component on `|0^m>` by construction of the fibre projection.

Reuses the frozen `lcu_corner_apply` (full FQN
`QuantumAlgorithm.Papers.QWalkAmbainis03.QRAMModel.lcu_corner_apply`) with the
normalised weights `w_j = α_j/α`. -/
theorem lemma6_lcu_corner (U : J → Matrix I I ℂ) (α : J → ℝ) (hα : ∀ j, 0 < α j)
    (P : Matrix J J ℂ) (j₀ : J)
    (hP : IsPrepare P (fun j => α j / ∑ k, α k) j₀) (ψ : QState I) :
    (fun i' => (LCUWorkspace U P *ᵥ TensorState (Ket j₀) ψ) (j₀, i'))
      = (1 / (∑ k, α k)) • ((∑ j, α j • U j) *ᵥ ψ) := by
  have htot : 0 < ∑ k, α k :=
    Finset.sum_pos (fun j _ => hα j) Finset.univ_nonempty
  rw [lcu_corner_apply (w := fun j => α j / ∑ k, α k)
    U (fun j => (div_nonneg (hα j).le htot.le)) hP ψ]
  have hmat : (∑ j, (α j / (∑ k, α k)) • U j) =
      (1 / (∑ k, α k)) • (∑ j, α j • U j) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    field_simp
  rw [hmat, smul_mulVec]

/-! ## Lemma 7 — the non-unitary LCU corner -/

/-- The `|z>`-block of a matrix on `T × I`, the paper's `T_i` of eq. (5). -/
def zeroBlock (U : Matrix (T × I) (T × I) ℂ) (z : T) : Matrix I I ℂ :=
  fun a b => U (z, a) (z, b)

omit [DecidableEq J] [Nonempty J] [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
/-- Extracting the `|z>`-block commutes with addition. -/
lemma zeroBlock_sum (A : J → Matrix (T × I) (T × I) ℂ) (z : T) :
    zeroBlock (∑ j, A j) z = ∑ j, zeroBlock (A j) z := by
  ext a b
  simp [zeroBlock, Matrix.sum_apply]

omit [DecidableEq J] [Nonempty J] [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
/-- Extracting the `|z>`-block commutes with scalar multiplication. -/
lemma zeroBlock_smul (c : ℝ) (M : Matrix (T × I) (T × I) ℂ) (z : T) :
    zeroBlock (c • M) z = c • zeroBlock M z := by
  ext a b
  simp [zeroBlock]

omit [DecidableEq I] in
/-- The `|z>`-corner fibre of `M` applied to `|z>|φ>` is `M`'s `|z>`-block
applied to `φ` (the paper's eq. (10), corner form). -/
lemma cornerBlock_mulVec (M : Matrix (T × I) (T × I) ℂ) (z : T) (φ : QState I) :
    (fun i' : I => (M *ᵥ TensorState (Ket z) φ) (z, i')) = zeroBlock M z *ᵥ φ := by
  funext i'
  simp only [Matrix.mulVec, dotProduct, TensorState, Ket, Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single z]
  · simp [zeroBlock]
  · intro a _ ha
    rw [Finset.sum_eq_zero]
    intro b _
    simp [ha]
  · intro hcon
    exact absurd (Finset.mem_univ z) hcon

/-- **Source Lemma 7** (arXiv:1511.02306, §2.1, pp. 7–8, eqs. (5)–(11)).
Let `M = Σ_i α_i T_i` with `α_i > 0`, and let each `U_i` satisfy
`U_i |0^t>|φ> = |0^t> T_i |φ> + |Φ_i⊥>` with `(|0^t><0^t| ⊗ 1)|Φ_i⊥> = 0`.
Then the `|0^m>|0^t>` corner fibre of `W = V† (Σ_i |i><i| ⊗ U_i) V` applied
to `|0^m>|0^t>|φ>` is `(1/α) M|φ>`.

`zeroBlock (U j) z` is the paper's `T_i` (`z` is the all-zero bit string of the
`t`-qubit register), and the hypothesis that `U_i` has no leakage out of the
`|0^t>` block is exactly the paper's orthogonality of `|Φ_i⊥>`.  This is the
corner form of the paper's eq. (10); the amplitude-amplification step that
turns success probability `(‖M|b>‖/α)²` into `O(α/‖M|b>‖)` expected uses is
the query/cost layer and is not modelled here.
-/
theorem lemma7_nonunitary_lcu_corner (U : J → Matrix (T × I) (T × I) ℂ)
    (z : T) (α : J → ℝ) (hα : ∀ j, 0 < α j) (P : Matrix J J ℂ) (j₀ : J)
    (hP : IsPrepare P (fun j => α j / ∑ k, α k) j₀) (φ : QState I) :
    (fun i' =>
        (LCUWorkspace U P *ᵥ TensorState (Ket j₀) (TensorState (Ket z) φ))
          (j₀, (z, i')))
      = (1 / (∑ k, α k)) • ((∑ j, α j • zeroBlock (U j) z) *ᵥ φ) := by
  have htot : 0 < ∑ k, α k :=
    Finset.sum_pos (fun j _ => hα j) Finset.univ_nonempty
  -- Apply the Lemma 6 corner contraction on the joint register `T × I`.
  have hcorner := lcu_corner_apply (w := fun j => α j / ∑ k, α k)
    U (fun j => (div_nonneg (hα j).le htot.le)) hP (TensorState (Ket z) φ)
  -- Flatten the normalised weights into `(1/α)` times the raw weights.
  have hmat : (∑ j, (α j / (∑ k, α k)) • U j) =
      (1 / (∑ k, α k)) • (∑ j, α j • U j) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    field_simp
  funext i'
  have hc := congrFun hcorner (z, i')
  rw [hc, hmat]
  have hcb := congrFun
    (cornerBlock_mulVec ((1 / (∑ k, α k)) • (∑ j, α j • U j)) z φ) i'
  rw [hcb, zeroBlock_smul, zeroBlock_sum]
  simp only [zeroBlock_smul]
  rw [smul_mulVec]

/-! ## Lemma 8 — gate complexity of powers of a single unitary -/

/-- **Source Lemma 8** (arXiv:1511.02306, §2.1, p. 8).  If the gate complexity
of `Y^{2^j}` is `G_j ≤ 2^j G` for `0 ≤ j ≤ ⌊log₂ N⌋`, then the binary-
controlled circuit implementing `U = Σ_{i=0}^{N} |i><i| ⊗ Y^i` (one controlled
`Y^{2^j}` per bit `j`) has gate complexity at most `2 N G`, i.e.
`O(Σ_j G_j) = O(N G)`.

The statement is the gate-count core of the source proof: each bit contributes
one controlled `Y^{2^j}` of cost `G_j`, and the geometric sum is bounded by
`2^{n+1} G ≤ 2 N G`. -/
theorem lemma8_powers_gate_cost (N : ℕ) (hN : 1 ≤ N) (G : ℕ) (Gj : ℕ → ℕ)
    (hGj : ∀ j ≤ Nat.log2 N, Gj j ≤ 2 ^ j * G) :
    (∑ j ∈ Finset.range (Nat.log2 N + 1), Gj j) ≤ 2 * N * G := by
  have hstep : (∑ j ∈ Finset.range (Nat.log2 N + 1), Gj j) ≤
      ∑ j ∈ Finset.range (Nat.log2 N + 1), 2 ^ j * G := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact hGj j (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj)
  refine hstep.trans ?_
  -- Evaluate the geometric sum.
  have hgeom : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), 2 ^ j) + 1 = 2 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by
          rw [pow_succ]
          ring
        rw [hpow]
        omega
  have hsum : (∑ j ∈ Finset.range (Nat.log2 N + 1), 2 ^ j * G) =
      (∑ j ∈ Finset.range (Nat.log2 N + 1), 2 ^ j) * G := by
    rw [Finset.sum_mul]
  rw [hsum]
  have hpow : 2 ^ (Nat.log2 N + 1) ≤ 2 * N := by
    have hlog : 2 ^ Nat.log2 N ≤ N := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · omega
      · rw [Nat.log2_eq_log_two]
        exact Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hpos)
    calc 2 ^ (Nat.log2 N + 1) = 2 ^ Nat.log2 N * 2 := pow_succ _ _
      _ ≤ N * 2 := Nat.mul_le_mul_right 2 hlog
      _ = 2 * N := Nat.mul_comm _ _
  have hgeomN : (∑ j ∈ Finset.range (Nat.log2 N + 1), 2 ^ j) ≤ 2 ^ (Nat.log2 N + 1) := by
    have h := hgeom (Nat.log2 N)
    omega
  calc (∑ j ∈ Finset.range (Nat.log2 N + 1), 2 ^ j) * G
      ≤ 2 ^ (Nat.log2 N + 1) * G := Nat.mul_le_mul_right G hgeomN
    _ ≤ (2 * N) * G := Nat.mul_le_mul_right G hpow
    _ = 2 * N * G := rfl

end Qatlib.Papers.LinearSystems15.MainResults.Lcu
