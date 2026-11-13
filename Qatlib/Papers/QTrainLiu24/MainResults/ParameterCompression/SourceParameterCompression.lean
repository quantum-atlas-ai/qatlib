/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# QTrainLiu24.MainResults.ParameterCompression

Paper: Chen-Yu Liu et al., *Quantum-Train: Rethinking Hybrid Quantum-Classical
Machine Learning in the Model Compression Perspective*, fixed arXiv:2405.11304v2.

Claim c004 (main result): a classical network with `M` parameters (Eq. (1),
p.2) is trained through an `N = ⌈log₂ M⌉`-qubit QNN plus a classical mapping
network, reducing the *trainable* parameter count from `M` to `O(polylog M)`
(Abstract p.1; §II-A Eq. (1)–(4) p.2–3; main-result bullet "Model compression
during training" p.2; restated p.8–9).

This module formalises the counting content only:

* `qubitCount M = Nat.clog 2 M` is the paper's `N = ⌈log₂ M⌉`.
* `qnnParams nblocks N = nblocks * N` — one trainable `R_y` angle per qubit per
  block (§II-B, p.3).
* `totalParams` adds the mapping-model parameters *separately* (§II-A p.3:
  "the input to the mapping model has a length of `N + 1`", so the mapping
  network is a separate `poly(N)` ledger).
* `qubit_coverage` (`M ≤ 2^N`), `qubitCount_le_log_succ` (`N ≤ ⌊log₂ M⌋ + 1`),
  `qnnParams_polylog` / `totalParams_polylog` (polynomial in `N ⇒` polylog in
  `M`), and `main_compression_polylog`.
* `qubitCount_lt_params` (`N < M` for `M ≥ 2`): the qubit address width is
  strictly below the classical parameter count.
* Concrete checks against Tables I and III (p.12) for the reported topologies.

Boundary: this is the *counting* statement, not a trainability, accuracy or
generalisation guarantee. The source's tables are recorded as data in the
sibling `EmpiricalResults` module.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QTrainLiu24.MainResults.ParameterCompression

/-! ## Qubit and parameter count vocabulary -/

/-- The paper's qubit number `N = ⌈log₂ M⌉` for a classical network with `M`
parameters (Eq. (1) and §II-A, p.2: `N = ⌈log₂ M⌉`). -/
def qubitCount (M : ℕ) : ℕ := Nat.clog 2 M

/-- Trainable QNN parameters: with `N` qubits and one `R_y` angle per qubit per
block, `nblocks` blocks contribute `nblocks · N` parameters (§II-B, p.3). -/
def qnnParams (nblocks N : ℕ) : ℕ := nblocks * N

/-- Total trainable parameters: the QNN ledger plus the mapping model's
parameters, which are counted separately (§II-A, p.3). -/
def totalParams (nblocks N mapParams : ℕ) : ℕ := qnnParams nblocks N + mapParams

/-! ## Coverage and logarithmic width -/

/-- `M` parameters are addressed by `N = ⌈log₂ M⌉` qubits: the computational
basis has `2^N ≥ M` strings (Eq. (1) and the paragraph after Eq. (2), p.2). -/
theorem qubit_coverage (M : ℕ) (_hM : 1 ≤ M) : M ≤ 2 ^ qubitCount M := by
  unfold qubitCount
  exact Nat.le_pow_clog (by norm_num) M

/-- The qubit count is at most one more than the floor base-2 logarithm:
`⌈log₂ M⌉ ≤ ⌊log₂ M⌋ + 1`. -/
theorem qubitCount_le_log_succ (M : ℕ) (_hM : 1 ≤ M) :
    qubitCount M ≤ Nat.log 2 M + 1 := by
  unfold qubitCount
  have hlt : M < 2 ^ (Nat.log 2 M).succ :=
    Nat.lt_pow_succ_log_self (by norm_num) M
  have hle : M ≤ 2 ^ (Nat.log 2 M + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.le_of_lt hlt
  exact Nat.clog_le_of_le_pow hle

/-- `M ≤ 2^(M-1)` for `M ≥ 1`; used to show the address width stays below `M`. -/
theorem le_two_pow_pred (M : ℕ) (hM : 1 ≤ M) : M ≤ 2 ^ (M - 1) := by
  induction M with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; norm_num
      · have ih' : n ≤ 2 ^ (n - 1) := ih (by omega)
        have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        have hstep : n + 1 ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := by
          calc n + 1 ≤ 2 ^ (n - 1) + 1 := Nat.succ_le_succ ih'
            _ ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := by omega
        calc n + 1 ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := hstep
          _ = 2 ^ (n - 1 + 1) := by rw [Nat.pow_succ]; ring
          _ = 2 ^ n := by congr 1; omega

/-- For `M ≥ 2` the qubit address width is strictly below the classical
parameter count: `N = ⌈log₂ M⌉ < M`. This is the exponential-address reduction
the framework exploits, not an accuracy guarantee. -/
theorem qubitCount_lt_params (M : ℕ) (hM : 2 ≤ M) : qubitCount M < M := by
  have h1 : 1 ≤ M := by omega
  have hpred : qubitCount M ≤ M - 1 := by
    unfold qubitCount
    rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    exact le_two_pow_pred M h1
  omega

/-! ## Polynomial-in-`N` ⇒ polylog-in-`M` -/

/-- If the QNN block schedule is polynomial of degree `d` in `N+1`, the QNN
parameter count is polynomial of degree `d+1` in `N+1`. This is the source's
`O(polylog M)` claim for the quantum ledger (§II-B p.3; p.8–9). -/
theorem qnnParams_polylog (C d nblocks M : ℕ)
    (hnb : nblocks ≤ C * (qubitCount M + 1) ^ d) :
    qnnParams nblocks (qubitCount M) ≤ C * (qubitCount M + 1) ^ (d + 1) := by
  unfold qnnParams
  calc nblocks * qubitCount M
      ≤ (C * (qubitCount M + 1) ^ d) * (qubitCount M + 1) :=
        Nat.mul_le_mul hnb (Nat.le_succ (qubitCount M))
    _ = C * (qubitCount M + 1) ^ (d + 1) := by
        rw [Nat.pow_succ]; ring

/-- QNN plus mapping-model parameters, both polynomial in `N+1`, are together
polynomial of degree `d+1`: the two ledgers are kept separate as in §II-A. -/
theorem totalParams_polylog (Cq Cm d nblocks mapParams M : ℕ)
    (hnb : nblocks ≤ Cq * (qubitCount M + 1) ^ d)
    (hmap : mapParams ≤ Cm * (qubitCount M + 1) ^ d) :
    totalParams nblocks (qubitCount M) mapParams
      ≤ (Cq + Cm) * (qubitCount M + 1) ^ (d + 1) := by
  unfold totalParams
  have hq := qnnParams_polylog Cq d nblocks M hnb
  have hb1 : 1 ≤ qubitCount M + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hmono : (qubitCount M + 1) ^ d ≤ (qubitCount M + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right hb1 (Nat.le_succ d)
  have hm : mapParams ≤ Cm * (qubitCount M + 1) ^ (d + 1) :=
    le_trans hmap (Nat.mul_le_mul_left Cm hmono)
  calc qnnParams nblocks (qubitCount M) + mapParams
      ≤ Cq * (qubitCount M + 1) ^ (d + 1)
          + Cm * (qubitCount M + 1) ^ (d + 1) :=
        Nat.add_le_add hq hm
    _ = (Cq + Cm) * (qubitCount M + 1) ^ (d + 1) := by ring

/-- `qubitCount M + 1 ≤ ⌊log₂ M⌋ + 2`, rewriting the polylog bound in the
floor logarithm. -/
theorem qubitCount_add_one_le_log_add_two (M : ℕ) (hM : 1 ≤ M) :
    qubitCount M + 1 ≤ Nat.log 2 M + 2 := by
  have := qubitCount_le_log_succ M hM
  omega

/-- Main result (Abstract p.1; §II-A p.2; p.8–9): with a polynomial block
schedule, the total trainable parameter count is bounded by a polynomial in
`⌊log₂ M⌋ + 2`, i.e. `O(polylog M)`, while the `M` classical parameters are
covered by `N ≤ ⌊log₂ M⌋ + 1` qubits. -/
theorem main_compression_polylog (Cq Cm d nblocks mapParams M : ℕ) (hM : 1 ≤ M)
    (hnb : nblocks ≤ Cq * (qubitCount M + 1) ^ d)
    (hmap : mapParams ≤ Cm * (qubitCount M + 1) ^ d) :
    totalParams nblocks (qubitCount M) mapParams
        ≤ (Cq + Cm) * (Nat.log 2 M + 2) ^ (d + 1)
      ∧ qubitCount M ≤ Nat.log 2 M + 1 := by
  refine ⟨?_, qubitCount_le_log_succ M hM⟩
  exact le_trans (totalParams_polylog Cq Cm d nblocks mapParams M hnb hmap)
    (Nat.mul_le_mul_left (Cq + Cm)
      (Nat.pow_le_pow_left (qubitCount_add_one_le_log_add_two M hM) (d + 1)))

/-! ## Concrete checks against Tables I and III (p.12) -/

/-- Mapping-model parameter count of the `(14-4, 4-20, 20-4, 4-1)` MLP used in
Tables I (MNIST) and II (FashionMNIST): `14·4+4 + 4·20+20 + 20·4+4 + 4·1+1
= 249`. -/
def mnistMapParams : ℕ := 249

/-- Mapping-model parameter count of the `(20-40, 40-200, 200-40, 40-1)` MLP used
in Table III (CIFAR-10): `840 + 8200 + 8040 + 41 = 17121`. -/
def cifarMapParams : ℕ := 17121

/-- Table I: `N = ⌈log₂ 6690⌉ = 13` (p.4). -/
theorem mnist_qubits : qubitCount 6690 = 13 := by
  unfold qubitCount; decide

/-- Table III: `N = ⌈log₂ 285226⌉ = 19` (p.4). -/
theorem cifar_qubits : qubitCount 285226 = 19 := by
  unfold qubitCount; decide

/-- Table I, QT-16: `16·13 + 249 = 457` trainable parameters. -/
theorem mnist_qt16_total : totalParams 16 13 mnistMapParams = 457 := by
  unfold totalParams qnnParams mnistMapParams; decide

/-- Table I, QT-121: `121·13 + 249 = 1822` trainable parameters. -/
theorem mnist_qt121_total : totalParams 121 13 mnistMapParams = 1822 := by
  unfold totalParams qnnParams mnistMapParams; decide

/-- Table III, QT-19: `19·19 + 17121 = 17482` trainable parameters. -/
theorem cifar_qt19_total : totalParams 19 19 cifarMapParams = 17482 := by
  unfold totalParams qnnParams cifarMapParams; decide

/-- Table III, QT-323: `323·19 + 17121 = 23258` trainable parameters. -/
theorem cifar_qt323_total : totalParams 323 19 cifarMapParams = 23258 := by
  unfold totalParams qnnParams cifarMapParams; decide

/-- Table I: the QT-16 trainable count is below the classical `M = 6690`. -/
theorem mnist_qt16_below_classical :
    totalParams 16 13 mnistMapParams < 6690 := by
  unfold totalParams qnnParams mnistMapParams; decide

/-- Table III: the QT-323 trainable count is below the classical `M = 285226`. -/
theorem cifar_qt323_below_classical :
    totalParams 323 19 cifarMapParams < 285226 := by
  unfold totalParams qnnParams cifarMapParams; decide

end Qatlib.Papers.QTrainLiu24.MainResults.ParameterCompression
