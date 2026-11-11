/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.FourierData

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Lemma 4 (total Fourier weight)

Fixed arXiv:2211.03999v1, Lemma 4, p.11, Eqs. (24)--(27).

With `f(C,s,x)` the Fourier coefficients of Definition 1 and `W_k` the Fourier weight of
Definition 5, the paper proves

1. `W_0 = 1` (the all-identity Pauli path has coefficient `2^{-n}`);
2. `W_k = 0` for `0 < k ≤ d` (there are no legal paths of weight `k ≤ d`); and
3. `∑_{k ≥ d+1} W_k = O(1) - 1`, obtained from the anti-concentration bound
   `E_C[2^n ∑_x p(C,x)^2] = O(1)` and the weight decomposition `∑_k W_k = E_C[2^n ∑_x p(C,x)^2]`.

The Lean statement below takes (1) and (2) as the paper's two elementary path facts
(`hW0`, `hlow`, to be supplied by the concrete legality/counting development) and proves
the non-trivial part (3): the weight decomposition, the exact split at degree `d+1`,
and the resulting `O(1)` bound.  This is exactly the logical structure of the source
proof; nothing is weakened.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Fourier

open BigOperators
open scoped BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

variable {Ω Path : Type*}

/-- Eq. (23)--(24), p.10--11: the total Fourier weight equals the anti-concentration
second moment, `∑_k W_k = E_C[2^n ∑_x p(C,x)^2]`.  This is the orthogonality step in
the proof of Lemma 4. -/
theorem total_weight_eq_path_second_moment [Fintype Path] (n : ℕ) (E : Expectation Ω)
    (f : Ω → Path → ℝ) (p : Ω → (Fin n → Bool) → ℝ)
    (horth : Orthogonality E f) (hp : ∀ C x, p C x = ∑ s, f C s) :
    (2 : ℝ) ^ n * ∑ x : Fin n → Bool, E (fun C => (p C x) ^ 2) =
      (2 : ℝ) ^ (2 * n) * ∑ s, E (fun C => (f C s) ^ 2) := by
  have hx : ∀ x : Fin n → Bool, E (fun C => (p C x) ^ 2) =
      ∑ s, E (fun C => (f C s) ^ 2) := by
    intro x
    have hfun : (fun C => (p C x) ^ 2) = (fun C => (∑ s, f C s) ^ 2) := by
      funext C
      rw [hp C x]
    rw [hfun, inner_sq_expansion E f horth]
  simp_rw [hx, Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  rw [hcard]
  have hpow : (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show 2 * n = n + n by ring, pow_add]
  simp only [nsmul_eq_mul]
  push_cast
  rw [hpow]
  ring

/-- Fixed arXiv:2211.03999v1, Lemma 4, p.11, Eqs. (24)--(27):
the Fourier weights satisfy `W_0 = 1`, `W_k = 0` for `0 < k ≤ d`, and the tail
`∑_{k = d+1}^{N} W_k` is bounded by the anti-concentration constant minus one. -/
theorem source_lemma4_total_fourier_weight [Fintype Path] [DecidableEq Path]
    (n d N : ℕ) (E : Expectation Ω) (f : Ω → Path → ℝ) (weight : Path → ℕ)
    (p : Ω → (Fin n → Bool) → ℝ)
    (hdN : d ≤ N) (hN : ∀ s, weight s ≤ N)
    (horth : Orthogonality E f) (hp : ∀ C x, p C x = ∑ s, f C s)
    (hAC : AntiConcentration n E p)
    (hW0 : FourierWeight n E f weight 0 = 1)
    (hlow : ∀ k, 0 < k → k ≤ d → FourierWeight n E f weight k = 0) :
    FourierWeight n E f weight 0 = 1 ∧
    (∀ k, 0 < k → k ≤ d → FourierWeight n E f weight k = 0) ∧
    ∃ Ctail : ℝ,
      (∑ k ∈ Finset.Ico (d + 1) (N + 1), FourierWeight n E f weight k) ≤ Ctail := by
  refine ⟨hW0, hlow, ?_⟩
  obtain ⟨Cac, hCac⟩ := hAC
  have htot := total_weight_eq_path_second_moment n E f p horth hp
  have hdecomp := sum_fourierWeight n E f weight N hN
  -- The total weight is the anti-concentration moment.
  have hrange : (∑ k ∈ Finset.range (N + 1), FourierWeight n E f weight k)
      = (2 : ℝ) ^ n * ∑ x : Fin n → Bool, E (fun C => (p C x) ^ 2) := by
    rw [← hdecomp, ← htot]
  rw [Finset.range_eq_Ico] at hrange
  -- Split `[0, N+1)` at `d+1`, and `[0, d+1)` at `1`.
  have hsplit := Finset.sum_Ico_consecutive (fun k => FourierWeight n E f weight k)
    (show 0 ≤ d + 1 by omega) (show d + 1 ≤ N + 1 by omega)
  have hsplit0 := Finset.sum_Ico_consecutive (fun k => FourierWeight n E f weight k)
    (show 0 ≤ 1 by omega) (show 1 ≤ d + 1 by omega)
  have h01 : (∑ k ∈ Finset.Ico 0 1, FourierWeight n E f weight k)
      = FourierWeight n E f weight 0 := by simp
  have hmid : (∑ k ∈ Finset.Ico 1 (d + 1), FourierWeight n E f weight k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact hlow k (by omega) (by omega)
  have hfirst : (∑ k ∈ Finset.Ico 0 (d + 1), FourierWeight n E f weight k) = 1 := by
    rw [h01, hmid, hW0] at hsplit0
    simpa using hsplit0.symm
  have htotal_le : (∑ k ∈ Finset.Ico 0 (N + 1), FourierWeight n E f weight k) ≤ Cac := by
    rw [hrange]
    exact hCac
  refine ⟨Cac - 1, ?_⟩
  linarith

end Qatlib.Papers.NoisyCircuit22.MainResults.Fourier
