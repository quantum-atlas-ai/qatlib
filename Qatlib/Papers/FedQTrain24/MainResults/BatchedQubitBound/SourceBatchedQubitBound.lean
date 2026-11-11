/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# FedQTrain24 — batched parameter generation: the source qubit-count bound

Liu & Chen, *Federated Quantum-Train with Batched Parameter Generation*,
fixed **arXiv:2409.02763v1** (quant-ph, 4 Sep 2024; source text
`assets/2409.02763v1.pdf`, SHA-256
`6dda0b5c530c974ed49cb806d13c0375aada82e92109a1728adb979996b4c07a`).

Source locations used below:

* §IV “Quantum-Train with Batched Parameter Generation”, **Eqs. (5)–(7)**, p. 3:
  the `m` parameters of the target model are split into
  `n_ch = ⌈m / n_mlp⌉` chunks of `n_mlp` parameters, each chunk being produced
  from one basis-measurement probability by the mapping model `G̃_β`;
  the QNN `|ψ(θ)⟩` therefore needs
  `N = ⌈log₂ n_ch⌉ = ⌈log₂ ⌈m / n_mlp⌉⌉` qubits, down from the vanilla QT
  count `N = ⌈log₂ m⌉`; “effectively saving approximately `⌈log₂ n_mlp⌉`
  qubits”, and `n_mlp = 1` is the original QT proposal.
* Highlight bullet on p. 1 and §VI p. 4: for the CIFAR-10 CNN with
  `m = 285226` parameters the qubit usage drops from `19` to `8`.

This module fixes the arithmetic core of claim `c001`:

* `chunkCount m n` — the number of chunks, i.e. ceiling division `⌈m/n⌉`;
* `qnnQubits m` — `⌈log₂ m⌉`, the vanilla QT qubit count;
* `batchedQubits m n` — `Nat.clog 2 (chunkCount m n)`, Eq. (7).

Everything is elementary arithmetic over `ℕ`; the only external input is
Mathlib's ceiling-logarithm Galois connection (`Nat.clog_le_iff_le_pow`,
`Nat.le_pow_clog`, `Nat.clog_mono_right`). No `sorry`, no extra axiom.
-/

set_option autoImplicit false

namespace Qatlib.Papers.FedQTrain24.MainResults.BatchedQubitBound

/-! ## The three source quantities -/

/-- The number of parameter chunks, `n_ch = ⌈m / n_mlp⌉` (§IV, Eq. (4.1),
p. 3): `m` parameters are cut into consecutive chunks of `n_mlp` parameters,
the last chunk possibly partial. Realised as ceiling division
`(m + n - 1) / n`; the value `0` for `n = 0` is junk and every theorem below
assumes `0 < n`. -/
def chunkCount (m n : ℕ) : ℕ := (m + n - 1) / n

/-- The vanilla Quantum-Train qubit count, `N = ⌈log₂ m⌉` (§III p. 2, and the
premise of Eq. (7)): the least `k` with `m ≤ 2 ^ k`. -/
def qnnQubits (m : ℕ) : ℕ := Nat.clog 2 m

/-- The qubit usage of batched parameter generation, **Eq. (7)** (§IV p. 3):
`N = ⌈log₂ n_ch⌉ = ⌈log₂ ⌈m / n_mlp⌉⌉`, where `n = n_mlp` is the batch size. -/
def batchedQubits (m n : ℕ) : ℕ := Nat.clog 2 (chunkCount m n)

/-- Eq. (7) read literally, with the chunk count unfolded to ceiling
division: `N = ⌈log₂ ⌈m/n_mlp⌉⌉`. -/
theorem batchedQubits_eq_clog_chunkCount (m n : ℕ) :
    batchedQubits m n = Nat.clog 2 ((m + n - 1) / n) := rfl

/-! ## Ceiling-division properties of the chunk count -/

/-- §IV p. 3: the chunk count is a true ceiling. With `0 < m`, `0 < n`,
`n_ch = ⌈m/n⌉` is the unique integer with `n_ch * n ≥ m` and
`n_ch * n < m + n`; i.e. `n_ch` chunks of `n` parameters cover all `m`
parameters and no whole chunk can be dropped. -/
theorem chunkCount_spec {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    m ≤ chunkCount m n * n ∧ chunkCount m n * n < m + n := by
  constructor
  · unfold chunkCount
    have hlt : m + n - 1 < ((m + n - 1) / n + 1) * n :=
      (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_succ_self _)
    have hexp : ((m + n - 1) / n + 1) * n = (m + n - 1) / n * n + n := by ring
    rw [hexp] at hlt
    omega
  · unfold chunkCount
    have h := Nat.div_mul_le_self (m + n - 1) n
    omega

/-- The chunk count never exceeds the parameter count: for every positive
batch size, `⌈m/n⌉ ≤ m`. This is the monotonicity input for the qubit
reduction. -/
theorem chunkCount_le_self {m n : ℕ} (hn : 0 < n) : chunkCount m n ≤ m := by
  unfold chunkCount
  rw [Nat.div_le_iff_le_mul hn]
  have hmul : m ≤ m * n := Nat.le_mul_of_pos_right m hn
  omega

/-- With batch size `1`, there is one chunk per parameter: `⌈m/1⌉ = m`.
This is the source sentence “the original method can be considered as a
special case with `n_mlp = 1`” (§IV p. 3). -/
theorem chunkCount_one (m : ℕ) : chunkCount m 1 = m := by
  simp [chunkCount]

/-! ## The Eq. (7) qubit count -/

/-- Eq. (7) with `n_mlp = 1` returns the vanilla QT count: batched parameter
generation degenerates to the original single-parameter scheme
(§IV p. 3, “the original method can be considered as a special case with
`n_mlp = 1`”). -/
theorem batchedQubits_one (m : ℕ) : batchedQubits m 1 = qnnQubits m := by
  simp [batchedQubits, qnnQubits, chunkCount]

/-- Batched parameter generation never needs more qubits than vanilla QT:
`⌈log₂ ⌈m/n_mlp⌉⌉ ≤ ⌈log₂ m⌉` for every `0 < n_mlp`. This is the direction
“we reduce the qubit usage from `⌈log₂ m⌉` to `⌈log₂ ⌈m/n_mlp⌉⌉`”
(p. 1 highlight bullet). -/
theorem batchedQubits_le_qnnQubits {m n : ℕ} (hn : 0 < n) :
    batchedQubits m n ≤ qnnQubits m := by
  unfold batchedQubits qnnQubits
  exact Nat.clog_mono_right 2 (chunkCount_le_self hn)

/-- The quantitative form of “effectively saving approximately
`⌈log₂ n_mlp⌉` qubits” (§IV p. 3): the saving `N_QT − N_batched` is bounded
by `⌈log₂ n_mlp⌉ + 1`.  Proof: `m ≤ n_ch · n_mlp ≤ 2^⌈log₂ n_ch⌉·2^⌈log₂ n_mlp⌉
= 2^(⌈log₂ n_ch⌉ + ⌈log₂ n_mlp⌉)`, hence `⌈log₂ m⌉ ≤ ⌈log₂ n_ch⌉ +
⌈log₂ n_mlp⌉ + 1`. -/
theorem qnnQubits_le_batchedQubits_add {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    qnnQubits m ≤ batchedQubits m n + Nat.clog 2 n + 1 := by
  unfold qnnQubits batchedQubits
  apply Nat.clog_le_of_le_pow
  calc
    m ≤ chunkCount m n * n := (chunkCount_spec hm hn).1
    _ ≤ 2 ^ Nat.clog 2 (chunkCount m n) * 2 ^ Nat.clog 2 n :=
        Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) _) (Nat.le_pow_clog (by norm_num) _)
    _ = 2 ^ (Nat.clog 2 (chunkCount m n) + Nat.clog 2 n) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ (Nat.clog 2 (chunkCount m n) + Nat.clog 2 n + 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)

/-- Helper: a ceiling logarithm is pinned down by exact powers of two:
if `2^(k-1) < n ≤ 2^k` then `⌈log₂ n⌉ = k`. -/
theorem clog_two_eq_of_bounds {n k : ℕ} (hlo : 2 ^ (k - 1) < n) (hhi : n ≤ 2 ^ k) :
    Nat.clog 2 n = k := by
  apply le_antisymm
  · rwa [Nat.clog_le_iff_le_pow (by norm_num)]
  · exact Nat.le_of_pred_lt ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlo)

/-! ## The numerical instance of §VI (CIFAR-10 CNN, `m = 285226`) -/

/-- The CIFAR-10 target CNN has `m = 285226` parameters (§VI p. 4); with batch
size `2000` this gives `n_ch = ⌈285226/2000⌉ = ⌈142.613⌉ = 143` chunks. -/
theorem chunkCount_285226_2000 : chunkCount 285226 2000 = 143 := by decide

/-- With batch size `1000` the paper's CNN gives `n_ch = ⌈285.226⌉ = 286`. -/
theorem chunkCount_285226_1000 : chunkCount 285226 1000 = 286 := by decide

/-- With batch size `500` the paper's CNN gives `n_ch = ⌈570.452⌉ = 571`. -/
theorem chunkCount_285226_500 : chunkCount 285226 500 = 571 := by decide

/-- Vanilla QT needs `⌈log₂ 285226⌉ = 19` qubits for the CIFAR-10 CNN
(§VI p. 4: “the original QT with the same CNN model required 19 qubits”). -/
theorem qnnQubits_285226 : qnnQubits 285226 = 19 := by
  unfold qnnQubits
  exact clog_two_eq_of_bounds (by norm_num) (by norm_num)

/-- Eq. (7) for `n_mlp = 2000`: `⌈log₂ 143⌉ = 8` qubits (§VI p. 4:
“The required qubit usage, derived from Eq. 7, is 8, 9, and 10 qubits,
respectively”). -/
theorem batchedQubits_285226_2000 : batchedQubits 285226 2000 = 8 := by
  unfold batchedQubits
  rw [chunkCount_285226_2000]
  exact clog_two_eq_of_bounds (by norm_num) (by norm_num)

/-- Eq. (7) for `n_mlp = 1000`: `⌈log₂ 286⌉ = 9` qubits. -/
theorem batchedQubits_285226_1000 : batchedQubits 285226 1000 = 9 := by
  unfold batchedQubits
  rw [chunkCount_285226_1000]
  exact clog_two_eq_of_bounds (by norm_num) (by norm_num)

/-- Eq. (7) for `n_mlp = 500`: `⌈log₂ 571⌉ = 10` qubits. -/
theorem batchedQubits_285226_500 : batchedQubits 285226 500 = 10 := by
  unfold batchedQubits
  rw [chunkCount_285226_500]
  exact clog_two_eq_of_bounds (by norm_num) (by norm_num)

/-- Claim `c001`, numerical instance: for the CIFAR-10 CNN with `m = 285226`
parameters, batched parameter generation needs `8 / 9 / 10` qubits for the
batch sizes `2000 / 1000 / 500`, while vanilla QT needs `19` (§VI p. 4,
“reduced qubit usage from 19 to as low as 8”). -/
theorem cifar10_qubit_usage :
    batchedQubits 285226 2000 = 8 ∧ batchedQubits 285226 1000 = 9 ∧
    batchedQubits 285226 500 = 10 ∧ qnnQubits 285226 = 19 :=
  ⟨batchedQubits_285226_2000, batchedQubits_285226_1000,
    batchedQubits_285226_500, qnnQubits_285226⟩

/-- Claim `c001`, general form: for every positive parameter count `m` and
positive batch size `n_mlp`, the qubit usage of Eq. (7) never exceeds the
vanilla QT count and the saving over vanilla QT is at most
`⌈log₂ n_mlp⌉ + 1`; for `n_mlp = 1` the counts coincide. -/
theorem qubit_reduction_general (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    batchedQubits m n ≤ qnnQubits m ∧
    qnnQubits m ≤ batchedQubits m n + Nat.clog 2 n + 1 ∧
    batchedQubits m 1 = qnnQubits m :=
  ⟨batchedQubits_le_qnnQubits hn, qnnQubits_le_batchedQubits_add hm hn,
    batchedQubits_one m⟩

end Qatlib.Papers.FedQTrain24.MainResults.BatchedQubitBound
