/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# PEPSObs16 — paper-layer statements for all active claims

Fixed source: arXiv:1606.06301v2 (M. Schwarz, O. Buerschaper, J. Eisert,
*Approximating local observables on projected entangled pair states*,
Phys. Rev. A 95, 060102 (2017)). The arXiv v2 PDF is the version used here
(local copy `assets/1606.06301.pdf`); the statements below cite its
page/equation numbers.

This module contains the four active claims of the paper:

* `c002` — Theorem 1 (computation of observables), pp. 2–3, eqs. (1), (13)–(15),
  together with the classical contraction count `(Dd)^{O(ℓ^d)}`; the quantum
  sampling count `O(1/ε²)` is in the companion file `QuantumSampling.lean`;
* `c003` — Conjecture 1 (weak PEPS conjecture), p. 2 (open, statement only);
* `c004` — Conjecture 2 (strong PEPS conjecture), p. 2 (open, statement only);
* `c005` — transfer-operator gap, eqs. (19)–(24), pp. 6–7.

The Hilbert-space model is fixed once at the top; the paper's tensor-network
class (PEPS of a given bond dimension, injectivity, gapped parent Hamiltonian)
is passed as an explicit predicate interface to the two conjectures, so that no
tensor-network structure is silently assumed. Theorem 1's *dynamical* hypothesis
is the paper's eq. (13) per-step clustering bound; everything after it
(iteration by the triangle inequality, the radius (15), and the contraction
count) is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSObs16.MainResults

open scoped BigOperators

/-! ## Shared Hilbert-space model -/

/-- A pure state vector on `N` qudits of physical dimension `d` (the paper's `ω`). -/
abbrev PepsState (N d : ℕ) := (Fin N → Fin d) → ℂ

/-- An observable matrix on the same `d^N`-dimensional Hilbert space. -/
abbrev Observable (N d : ℕ) := Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ

/-- The normalized expectation `⟨ω|O|ω⟩ / ⟨ω|ω⟩` (the paper keeps states
unnormalised, so the denominator is explicit). -/
def expectation {N d : ℕ} (ψ : PepsState N d) (O : Observable N d) : ℂ :=
  (∑ y, star (ψ y) * ∑ z, O y z * ψ z) / (∑ x, star (ψ x) * ψ x)

/-- `O` is supported on the site set `X`: no matrix element connects
computational-basis configurations differing outside `X` (the operator acts as
the identity on the complement). This is the paper's `O_X` (Theorem 1, p. 2:
"supported on `|X| < k` sites"). -/
def IsSupportedOn {N d : ℕ} (O : Observable N d) (X : Finset (Fin N)) : Prop :=
  ∀ y z : Fin N → Fin d, (∃ i, i ∉ X ∧ y i ≠ z i) → O y z = 0

/-- `O` is `k`-local: supported on at most `k` sites, as in Theorem 1. -/
def IsKLocal {N d : ℕ} (O : Observable N d) (k : ℕ) : Prop :=
  ∃ X : Finset (Fin N), X.card ≤ k ∧ IsSupportedOn O X

/-! ## Theorem 1 — disentangling error (eqs. (5), (13)–(15), pp. 3–5) -/

/-- Per-step error of absorbing one boundary tensor, eq. (13) (p. 5):
`e^{-O(ℓΔ*)} ‖O_X‖ κ(A_i)²`, written with a fixed clustering rate `c`. -/
def stepError (c Δ ell κ Onorm : ℝ) : ℝ :=
  Real.exp (-(c * ell * Δ)) * κ ^ 2 * Onorm

/-- The per-step error is nonnegative under a nonnegative observable norm. -/
theorem stepError_nonneg (c Δ ell κ Onorm : ℝ) (hO : 0 ≤ Onorm) :
    0 ≤ stepError c Δ ell κ Onorm := by
  unfold stepError
  positivity

/-- Triangle-inequality telescope: if every step `i < n` changes the running
value by at most `B i`, the total change is at most the sum of the `B i`
(the `O(ℓ^{d-1})`-fold use of the triangle inequality before eq. (5), p. 4). -/
theorem telescoping_error_bound (f : ℕ → ℝ) (B : ℕ → ℝ) (n : ℕ)
    (h : ∀ i, i < n → |f (i + 1) - f i| ≤ B i) :
    |f n - f 0| ≤ ∑ i ∈ Finset.range n, B i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : f (n + 1) - f 0 = (f (n + 1) - f n) + (f n - f 0) := by ring
      rw [hsplit]
      calc
        |(f (n + 1) - f n) + (f n - f 0)| ≤ |f (n + 1) - f n| + |f n - f 0| :=
          abs_add_le _ _
        _ ≤ B n + ∑ i ∈ Finset.range n, B i :=
          add_le_add (h n (Nat.lt_succ_self n))
            (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
        _ = ∑ i ∈ Finset.range (n + 1), B i := by
            rw [Finset.sum_range_succ, add_comm]

/-- Uniform-step version of the telescope. -/
theorem iteration_error_bound (f : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (h : ∀ i, i < n → |f (i + 1) - f i| ≤ B) :
    |f n - f 0| ≤ (n : ℝ) * B := by
  have ht := telescoping_error_bound f (fun _ => B) n h
  simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using ht

/-- **Eq. (14) (p. 4):** after `nb` disentangling steps of size at most
`stepError`, with `nb ≤ ℓ^{d-1}` boundary tensors, the accumulated error is at
most `ℓ^{d-1} · stepError`. This is the paper's move
`|⟨ω*|O_X|ω*⟩ − ⟨ω|O_X|ω⟩/⟨ω|ω⟩| ≤ ℓ^{d-1} e^{-O(ℓΔ*)} κ_*² ‖O_X‖`. -/
theorem disentangling_error_bound (f : ℕ → ℝ) (d ell nb : ℕ) (c Δ κ Onorm : ℝ)
    (hO : 0 ≤ Onorm) (hnb : nb ≤ ell ^ (d - 1))
    (hstep : ∀ i, i < nb → |f (i + 1) - f i| ≤ stepError c Δ (ell : ℝ) κ Onorm) :
    |f nb - f 0| ≤ (ell : ℝ) ^ (d - 1) * stepError c Δ (ell : ℝ) κ Onorm := by
  have hB : 0 ≤ stepError c Δ (ell : ℝ) κ Onorm := stepError_nonneg _ _ _ _ _ hO
  have h1 := iteration_error_bound f nb (stepError c Δ (ell : ℝ) κ Onorm) hstep
  have hcast : (nb : ℝ) ≤ (ell : ℝ) ^ (d - 1) := by
    exact_mod_cast hnb
  exact h1.trans (mul_le_mul_of_nonneg_right hcast hB)

/-- `exp (2 log κ) = κ²` for `κ > 0`, used to read eq. (13) in exponential form. -/
private theorem exp_two_log_eq_sq (κ : ℝ) (hκ : 0 < κ) :
    Real.exp (2 * Real.log κ) = κ ^ 2 := by
  rw [show (2 : ℝ) * Real.log κ = ((2 : ℕ) : ℝ) * Real.log κ by norm_num,
    Real.exp_nat_mul, Real.exp_log hκ]

/-- **Eq. (15) (p. 5), real form.** If the radius satisfies
`log x + 2 log κ + log ε⁻¹ + log ‖O_X‖ ≤ c ℓ Δ`, then the accumulated error
`x · e^{-cℓΔ} κ² ‖O_X‖` is at most `ε`. Here `x` will be the number
`ℓ^{d-1}` of boundary tensors. -/
theorem radius_sufficient_real (x c Δ ell κ Onorm ε : ℝ)
    (hx : 0 < x) (hκ : 0 < κ) (hO : 0 < Onorm) (hε : 0 < ε)
    (hradius : Real.log x + 2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm
      ≤ c * ell * Δ) :
    x * stepError c Δ ell κ Onorm ≤ ε := by
  have hExpL : Real.exp (Real.log x + 2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm)
      = x * κ ^ 2 * ε⁻¹ * Onorm := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hx,
      exp_two_log_eq_sq κ hκ, Real.exp_log (inv_pos.mpr hε), Real.exp_log hO]
  have hle : Real.exp (-(c * ell * Δ)) ≤ (x * κ ^ 2 * ε⁻¹ * Onorm)⁻¹ := by
    calc
      Real.exp (-(c * ell * Δ))
          ≤ Real.exp (-(Real.log x + 2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm)) :=
            Real.exp_le_exp_of_le (by linarith [hradius])
      _ = (Real.exp (Real.log x + 2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm))⁻¹ :=
            Real.exp_neg _
      _ = (x * κ ^ 2 * ε⁻¹ * Onorm)⁻¹ := by rw [hExpL]
  calc
    x * stepError c Δ ell κ Onorm
        = x * (Real.exp (-(c * ell * Δ)) * κ ^ 2 * Onorm) := by
          unfold stepError; ring
    _ = (x * κ ^ 2 * Onorm) * Real.exp (-(c * ell * Δ)) := by ring
    _ ≤ (x * κ ^ 2 * Onorm) * (x * κ ^ 2 * ε⁻¹ * Onorm)⁻¹ :=
          mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ε := by
          field_simp [hx.ne', hε.ne', hO.ne', pow_ne_zero 2 hκ.ne']

/-- **Eq. (15) (p. 5), boundary-count form.** With `nb` boundary tensors and
the radius condition written with `log nb`, the error `nb · stepError` is at
most `ε`. -/
theorem radius_sufficient_nat (nb : ℕ) (c Δ ell κ Onorm ε : ℝ)
    (hnb : 0 < nb) (hκ : 0 < κ) (hO : 0 < Onorm) (hε : 0 < ε)
    (hradius : Real.log (nb : ℝ) + 2 * Real.log κ + Real.log ε⁻¹
      + Real.log Onorm ≤ c * ell * Δ) :
    (nb : ℝ) * stepError c Δ ell κ Onorm ≤ ε := by
  exact radius_sufficient_real (nb : ℝ) c Δ ell κ Onorm ε
    (by exact_mod_cast hnb) hκ hO hε hradius

/-- **Eq. (14)–(15) in the paper's power form.** If the boundary count is at
most `ℓ^{d-1}` and the radius obeys
`(d-1) log ℓ + 2 log κ + log ε⁻¹ + log ‖O_X‖ ≤ c ℓ Δ`, then the
disentangling error `ℓ^{d-1} e^{-cℓΔ} κ² ‖O_X‖` is at most `ε`. -/
theorem radius_power_sufficient (d ell : ℕ) (c Δ κ Onorm ε : ℝ)
    (hell : 1 ≤ ell) (hκ : 0 < κ) (hO : 0 < Onorm) (hε : 0 < ε)
    (hradius : ((d - 1 : ℕ) : ℝ) * Real.log (ell : ℝ) + 2 * Real.log κ
      + Real.log ε⁻¹ + Real.log Onorm ≤ c * (ell : ℝ) * Δ) :
    (ell : ℝ) ^ (d - 1) * stepError c Δ (ell : ℝ) κ Onorm ≤ ε := by
  have hellpos : 0 < (ell : ℝ) := by exact_mod_cast hell
  refine radius_sufficient_real ((ell : ℝ) ^ (d - 1)) c Δ (ell : ℝ) κ Onorm ε
    (pow_pos hellpos _) hκ hO hε ?_
  rw [Real.log_pow]
  exact hradius

/-- **The paper's radius (1)/(15) is attainable.** For every lattice dimension
`d` and constants `c, Δ, κ, ‖O_X‖, ε > 0`, there is a radius `ℓ ≥ 1` with
`(d-1) log ℓ + 2 log κ + log ε⁻¹ + log ‖O_X‖ ≤ c ℓ Δ`. This is the content of
`ℓ ∈ O((2 ln κ_* + ln ε⁻¹ + ln ‖O_X‖)/Δ_*)`: the polynomial factor `ℓ^{d-1}`
contributes only `(d-1) log ℓ`, which is dominated by the linear right-hand
side (`Real.isLittleO_log_id_atTop`). -/
theorem exists_radius (d : ℕ) (c Δ κ Onorm ε : ℝ)
    (hc : 0 < c) (hΔ : 0 < Δ) (hκ : 1 ≤ κ) (hO : 0 < Onorm) (hε : 0 < ε) :
    ∃ ell : ℕ, 1 ≤ ell ∧
      ((d - 1 : ℕ) : ℝ) * Real.log (ell : ℝ) + 2 * Real.log κ
        + Real.log ε⁻¹ + Real.log Onorm ≤ c * (ell : ℝ) * Δ := by
  have hcΔ : 0 < c * Δ := mul_pos hc hΔ
  have hcΔ2 : 0 < c * Δ / 2 := half_pos hcΔ
  set k : ℕ := max 1 (d - 1) with hk
  have hk1 : 1 ≤ k := le_max_left _ _
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk1
  have hlog : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x‖ ≤ ((c * Δ / 2) / (k : ℝ)) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (div_pos hcΔ2 hkpos)
  rw [Filter.eventually_atTop] at hlog
  obtain ⟨L, hL⟩ := hlog
  set M : ℝ := max L (max 1
    ((2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm) / (c * Δ / 2))) with hM
  obtain ⟨ell, hellM⟩ := exists_nat_gt M
  have h1M : (1 : ℝ) ≤ M :=
    le_trans (le_max_left 1 _) (le_max_right L _)
  have hell1 : (1 : ℝ) ≤ (ell : ℝ) := by linarith
  have hell1n : 1 ≤ ell := by exact_mod_cast hell1
  have hellL : L ≤ (ell : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left L _) hellM)
  have hinner : max 1 ((2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm) / (c * Δ / 2))
      ≤ M := le_max_right L _
  have hellinner : (2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm) / (c * Δ / 2)
      ≤ (ell : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right (1 : ℝ) _) hinner) hellM)
  have hlogell : Real.log (ell : ℝ) ≤ ((c * Δ / 2) / (k : ℝ)) * (ell : ℝ) := by
    have h := hL (ell : ℝ) hellL
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hell1),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (ell : ℝ))] using h
  have hfirst : ((d - 1 : ℕ) : ℝ) * Real.log (ell : ℝ) ≤ (c * Δ / 2) * (ell : ℝ) := by
    have hdle : ((d - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      rw [hk]
      exact_mod_cast Nat.le_max_right 1 (d - 1)
    have hlognn : 0 ≤ Real.log (ell : ℝ) := Real.log_nonneg hell1
    calc
      ((d - 1 : ℕ) : ℝ) * Real.log (ell : ℝ)
          ≤ (k : ℝ) * Real.log (ell : ℝ) := mul_le_mul_of_nonneg_right hdle hlognn
      _ ≤ (k : ℝ) * (((c * Δ / 2) / (k : ℝ)) * (ell : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogell hkpos.le
      _ = (c * Δ / 2) * (ell : ℝ) := by field_simp
  have hsecond : 2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm
      ≤ (c * Δ / 2) * (ell : ℝ) := by
    have hle := hellinner
    rw [div_le_iff₀ hcΔ2] at hle
    simpa [mul_comm] using hle
  refine ⟨ell, hell1n, ?_⟩
  calc
    ((d - 1 : ℕ) : ℝ) * Real.log (ell : ℝ) + 2 * Real.log κ + Real.log ε⁻¹
        + Real.log Onorm
        = ((d - 1 : ℕ) : ℝ) * Real.log (ell : ℝ)
          + (2 * Real.log κ + Real.log ε⁻¹ + Real.log Onorm) := by ring
    _ ≤ (c * Δ / 2) * (ell : ℝ) + (c * Δ / 2) * (ell : ℝ) := add_le_add hfirst hsecond
    _ = c * (ell : ℝ) * Δ := by ring

/-! ## Classical contraction cost (p. 6, discussion after eq. (18)) -/

/-- Number of index assignments enumerated when the patch of `ℓ^d` sites is
contracted: `d^{ℓ^d}` physical assignments and `D^{2 d ℓ^d}` virtual ones
(p. 6: "summing over all `2(dℓ^d)` indices of dimension `D` and `ℓ^d` indices
of physical dimension `d`"). -/
def patchIndexCount (D d ell : ℕ) : ℕ :=
  d ^ (ell ^ d) * D ^ (2 * (d * ell ^ d))

/-- The paper's classical cost `(Dd)^{O(ℓ^d)}` with explicit constant:
`(Dd)^{3 d ℓ^d}`. -/
def classicalCost (D d ell : ℕ) : ℕ :=
  (D * d) ^ (3 * d * ell ^ d)

/-- **Classical contraction count (p. 6).** The number of index assignments of
the patch is at most `(Dd)^{3 d ℓ^d}`, i.e. `(Dd)^{O(ℓ^d)}` for constant `d`. -/
theorem patchIndexCount_le_classicalCost (D d ell : ℕ) (hD : 1 ≤ D) (hd : 1 ≤ d) :
    patchIndexCount D d ell ≤ classicalCost D d ell := by
  unfold patchIndexCount classicalCost
  have hdpos : 0 < d := by omega
  have hDpos : 0 < D := by omega
  have hDdpos : 0 < D * d := Nat.mul_pos hDpos hdpos
  have hd_le : d ≤ D * d := Nat.le_mul_of_pos_left d hDpos
  have hD_le : D ≤ D * d := Nat.le_mul_of_pos_right D hdpos
  have h1 : d ^ (ell ^ d) ≤ (D * d) ^ (ell ^ d) := Nat.pow_le_pow_left hd_le _
  have h2 : D ^ (2 * (d * ell ^ d)) ≤ (D * d) ^ (2 * (d * ell ^ d)) :=
    Nat.pow_le_pow_left hD_le _
  have hmul : d ^ (ell ^ d) * D ^ (2 * (d * ell ^ d))
      ≤ (D * d) ^ (ell ^ d) * (D * d) ^ (2 * (d * ell ^ d)) :=
    Nat.mul_le_mul h1 h2
  calc
    d ^ (ell ^ d) * D ^ (2 * (d * ell ^ d))
        ≤ (D * d) ^ (ell ^ d) * (D * d) ^ (2 * (d * ell ^ d)) := hmul
    _ = (D * d) ^ (ell ^ d + 2 * (d * ell ^ d)) := (pow_add _ _ _).symm
    _ ≤ (D * d) ^ (3 * d * ell ^ d) := by
        apply Nat.pow_le_pow_right hDdpos
        calc
          ell ^ d + 2 * (d * ell ^ d) = ell ^ d * (1 + 2 * d) := by ring
          _ ≤ ell ^ d * (3 * d) := by
              apply Nat.mul_le_mul_left
              omega
          _ = 3 * d * ell ^ d := by ring

/-! ## Theorem 1 (Computation of observables), top-level guarantee -/

/-- **Theorem 1 (Computation of observables), pp. 2–3.**

Model of the paper's algorithm at fixed radius: `f ell i` is the expectation
value after `i` boundary tensors have been disentangled (so `f ell 0` is the
exact global value `⟨ω|O_X|ω⟩/⟨ω|ω⟩`), and `nbOf ell` is the number of boundary
tensors removed. The hypothesis `hstep` is exactly the paper's per-step bound
eq. (13): each absorbed tensor costs at most `e^{-cℓΔ*} κ² ‖O_X‖` (the
exponential-clustering theorem supplies it; the paper cites it, pp. 3–4). Then
some radius `ℓ ≥ 1` achieves error at most `ε`, and the patch has at most
`(Dd)^{3 d ℓ^d}` contraction terms, the paper's classical time `(Dd)^{O(ℓ^d)}`. -/
theorem theorem1_computation_of_observables
    (D d : ℕ) (c Δ κ Onorm ε : ℝ)
    (hD : 1 ≤ D) (hd : 1 ≤ d) (hc : 0 < c) (hΔ : 0 < Δ) (hκ : 1 ≤ κ)
    (hO : 0 < Onorm) (hε : 0 < ε)
    (f : ℕ → ℕ → ℝ) (nbOf : ℕ → ℕ) (exact : ℝ)
    (hnb : ∀ ell, 1 ≤ ell → nbOf ell ≤ ell ^ (d - 1))
    (hstep : ∀ ell i, 1 ≤ ell → i < nbOf ell →
      |f ell (i + 1) - f ell i| ≤ stepError c Δ (ell : ℝ) κ Onorm)
    (hexact : ∀ ell, f ell 0 = exact) :
    ∃ ell : ℕ, 1 ≤ ell ∧ |f ell (nbOf ell) - exact| ≤ ε ∧
      patchIndexCount D d ell ≤ classicalCost D d ell := by
  obtain ⟨ell, hell1, hrad⟩ := exists_radius d c Δ κ Onorm ε hc hΔ hκ hO hε
  refine ⟨ell, hell1, ?_, patchIndexCount_le_classicalCost D d ell hD hd⟩
  have hbound := disentangling_error_bound (f ell) d ell (nbOf ell) c Δ κ Onorm
    hO.le (hnb ell hell1) (fun i hi => hstep ell i hell1 hi)
  rw [hexact ell] at hbound
  have hrad' := radius_power_sufficient d ell c Δ κ Onorm ε hell1
    (lt_of_lt_of_le zero_lt_one hκ) hO hε hrad
  exact hbound.trans hrad'

/-! ## Conjecture 1 (weak PEPS conjecture), p. 2 -/

/-- **Conjecture 1 (Weak PEPS conjecture), arXiv:1606.06301v2 p. 2.**

`IsPepsWithBond ω D` is the paper's class of PEPS states of bond dimension `D`
(an interface parameter: the paper layer does not redefine the tensor network);
`IsGappedGroundState ρ` says that `ρ` is the ground state of the gapped local
Hamiltonian fixed at the start of the paper (p. 2). For every `k`-local
observable `O_X` and every `ε > 0` there is a PEPS of bond dimension bounded by
`C · (N ε⁻¹)^c` (the paper's `D = O(poly(N, ε⁻¹))`) whose expectation differs
from that of `ρ` by less than `ε`.

The paper states this without proof; this definition asserts nothing. -/
def WeakPepsConjecture
    (IsPepsWithBond : ∀ {N d : ℕ}, PepsState N d → ℕ → Prop)
    (IsGappedGroundState : ∀ {N d : ℕ}, PepsState N d → Prop) : Prop :=
  ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ (N d k : ℕ) (ρ : PepsState N d) (O : Observable N d),
      IsGappedGroundState ρ → IsKLocal O k → ∀ ε : ℝ, 0 < ε →
        ∃ D : ℕ, (D : ℝ) ≤ C * ((N : ℝ) * ε⁻¹) ^ c ∧
          ∃ ω : PepsState N d, IsPepsWithBond ω D ∧
            ‖expectation ω O - expectation ρ O‖ < ε

/-- Literal quantifier form of Conjecture 1 (p. 2); definitional unfolding. -/
theorem weakPepsConjecture_unfold
    (IsPepsWithBond : ∀ {N d : ℕ}, PepsState N d → ℕ → Prop)
    (IsGappedGroundState : ∀ {N d : ℕ}, PepsState N d → Prop) :
    WeakPepsConjecture IsPepsWithBond IsGappedGroundState ↔
      ∃ (C : ℝ) (c : ℕ), 0 < C ∧
        ∀ (N d k : ℕ) (ρ : PepsState N d) (O : Observable N d),
          IsGappedGroundState ρ → IsKLocal O k → ∀ ε : ℝ, 0 < ε →
            ∃ D : ℕ, (D : ℝ) ≤ C * ((N : ℝ) * ε⁻¹) ^ c ∧
              ∃ ω : PepsState N d, IsPepsWithBond ω D ∧
                ‖expectation ω O - expectation ρ O‖ < ε :=
  Iff.rfl

/-! ## Conjecture 2 (strong PEPS conjecture), p. 2 -/

/-- **Conjecture 2 (Strong PEPS conjecture), arXiv:1606.06301v2 p. 2.**

`IsPepsWithBond ω D` is the paper's injective-PEPS class of bond dimension `D`
(injectivity is part of this class), `HasGappedParent ω Δ` says that `ω` has a
parent Hamiltonian with constant spectral gap `Δ > 0`, and
`IsGappedGroundState ρ` is the gapped ground state of the model under
consideration. The bond-dimension bound is the paper's
`D = O(poly(N, ε⁻¹))`, independent of `Δ`.

The paper states this without proof; this definition asserts nothing. -/
def StrongPepsConjecture
    (IsPepsWithBond : ∀ {N d : ℕ}, PepsState N d → ℕ → Prop)
    (IsGappedGroundState : ∀ {N d : ℕ}, PepsState N d → Prop)
    (HasGappedParent : ∀ {N d : ℕ}, PepsState N d → ℝ → Prop) : Prop :=
  ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ (N d k : ℕ) (ρ : PepsState N d) (O : Observable N d),
      IsGappedGroundState ρ → IsKLocal O k → ∀ ε : ℝ, 0 < ε →
        ∃ (D : ℕ) (Δ : ℝ), (D : ℝ) ≤ C * ((N : ℝ) * ε⁻¹) ^ c ∧ 0 < Δ ∧
          ∃ ω : PepsState N d, IsPepsWithBond ω D ∧ HasGappedParent ω Δ ∧
            ‖expectation ω O - expectation ρ O‖ < ε

/-- Literal quantifier form of Conjecture 2 (p. 2); definitional unfolding. -/
theorem strongPepsConjecture_unfold
    (IsPepsWithBond : ∀ {N d : ℕ}, PepsState N d → ℕ → Prop)
    (IsGappedGroundState : ∀ {N d : ℕ}, PepsState N d → Prop)
    (HasGappedParent : ∀ {N d : ℕ}, PepsState N d → ℝ → Prop) :
    StrongPepsConjecture IsPepsWithBond IsGappedGroundState HasGappedParent ↔
      ∃ (C : ℝ) (c : ℕ), 0 < C ∧
        ∀ (N d k : ℕ) (ρ : PepsState N d) (O : Observable N d),
          IsGappedGroundState ρ → IsKLocal O k → ∀ ε : ℝ, 0 < ε →
            ∃ (D : ℕ) (Δ : ℝ), (D : ℝ) ≤ C * ((N : ℝ) * ε⁻¹) ^ c ∧ 0 < Δ ∧
              ∃ ω : PepsState N d, IsPepsWithBond ω D ∧ HasGappedParent ω Δ ∧
                ‖expectation ω O - expectation ρ O‖ < ε :=
  Iff.rfl

/-! ## Transfer-operator gap, eqs. (22)–(24), pp. 6–7 -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral expansion of the two-point correlation along the line `L`,
eq. (23), after the boundary term `O(e^{-|L|})` has been dropped in the
thermodynamic limit: the sum over all eigenvalues except the Perron
eigenvalue `j1`. -/
def spectralCorrelation (lam a b : ι → ℝ) (j1 : ι) (x : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.erase j1, (lam j) ^ x * a j * b j

/-- **Eq. (24), eigenvalue form.** If the second eigenvalue's `x`-th power obeys
`λ₂^x ≤ c₁ e^{−c₂ x δ}` for every `x ≥ 1`, then `λ₂ ≤ e^{−c₂ δ}`. Taking
`x → ∞` removes the constant `c₁`; this is the analytic step behind "the
transfer operator along `L` itself inherits the gap of the parent Hamiltonian"
(p. 7). -/
theorem second_eigenvalue_decay (lam2 c1 c2 δ : ℝ)
    (hlam2 : 0 ≤ lam2) (hc1 : 0 < c1) (hc2 : 0 < c2) (hδ : 0 < δ)
    (hdecay : ∀ x : ℕ, 1 ≤ x →
      lam2 ^ x ≤ c1 * Real.exp (-(c2 * (x : ℝ) * δ))) :
    lam2 ≤ Real.exp (-(c2 * δ)) := by
  by_contra hcon
  push_neg at hcon
  set E : ℝ := Real.exp (-(c2 * δ)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hratio : 1 < lam2 / E := (one_lt_div hEpos).mpr hcon
  have hgrowth : ∀ᶠ x : ℕ in Filter.atTop, c1 < (lam2 / E) ^ x :=
    (tendsto_pow_atTop_atTop_of_one_lt hratio).eventually
      (Filter.eventually_gt_atTop c1)
  obtain ⟨x, hxgt, hx1⟩ :=
    Filter.Eventually.exists (hgrowth.and (Filter.eventually_ge_atTop 1))
  have hEpow : E ^ x = Real.exp (-(c2 * (x : ℝ) * δ)) := by
    rw [hE, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hlamx : lam2 ^ x = (lam2 / E) ^ x * E ^ x := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hle := hdecay x hx1
  rw [hlamx, hEpow] at hle
  have hExpos : 0 < E ^ x := pow_pos hEpos x
  have hratio_le : (lam2 / E) ^ x ≤ c1 := le_of_mul_le_mul_right hle (Real.exp_pos _)
  linarith

/-- Choosing the observable pair that projects onto the second eigenvector, the
spectral sum (23) collapses to `λ₂^x` (the paper's "choosing `O_A`, `O_B`"
step between eqs. (22) and (23)). -/
theorem spectralCorrelation_second (lam : ι → ℝ) (j1 j2 : ι) (hj : j2 ≠ j1)
    (x : ℕ) :
    spectralCorrelation lam (fun j => if j = j2 then 1 else 0) (fun _ => 1) j1 x =
      (lam j2) ^ x := by
  unfold spectralCorrelation
  have hmem : j2 ∈ Finset.univ.erase j1 :=
    Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j2⟩
  have h := Finset.sum_eq_single (s := Finset.univ.erase j1)
    (f := fun j => (lam j) ^ x * (if j = j2 then 1 else 0) * 1) j2 ?_ ?_
  · rw [h]
    simp
  · intro j _ hjj2
    simp [hjj2]
  · intro hnot
    exact absurd hmem hnot

/-- **Eqs. (22)–(24) (Appendix, pp. 6–7): transfer-operator gap.**

Assume the spectral decomposition (23) with Perron eigenvalue `λ₁ = 1`, that
the correlation of every observable pair decays as
`|⟨O_A ⊗ O_B⟩ − ⟨O_A⟩⟨O_B⟩| ≤ c₁ e^{−c₂ x δ}` (eq. (22)), and that some
observable pair projects onto the second eigenvector (`hproj`: unit matrix
elements selecting it, all other products vanishing). Then the transfer
operator is gapped with `λ₂/λ₁ ≤ e^{−c₂ δ}` (eq. (24)). -/
theorem transfer_operator_gap (lam a b : ι → ℝ) (j1 j2 : ι) (hj : j2 ≠ j1)
    (hlam2 : 0 ≤ lam j2) (c1 c2 δ : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hδ : 0 < δ)
    (hdecay : ∀ x : ℕ, 1 ≤ x →
      |spectralCorrelation lam a b j1 x| ≤ c1 * Real.exp (-(c2 * (x : ℝ) * δ)))
    (hproj : a j2 = 1 ∧ b j2 = 1 ∧ ∀ j, j ≠ j1 → j ≠ j2 → a j * b j = 0)
    (hlam1 : lam j1 = 1) :
    lam j2 / lam j1 ≤ Real.exp (-(c2 * δ)) := by
  have hcorr : ∀ x : ℕ, spectralCorrelation lam a b j1 x = (lam j2) ^ x := by
    intro x
    unfold spectralCorrelation
    have hmem : j2 ∈ Finset.univ.erase j1 :=
      Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j2⟩
    have h := Finset.sum_eq_single (s := Finset.univ.erase j1)
      (f := fun j => (lam j) ^ x * a j * b j) j2 ?_ ?_
    · rw [h, hproj.1, hproj.2.1]
      ring
    · intro j hmemj hjj2
      have hjj1 : j ≠ j1 := (Finset.mem_erase.mp hmemj).1
      show lam j ^ x * a j * b j = 0
      rw [show lam j ^ x * a j * b j = lam j ^ x * (a j * b j) by ring,
        hproj.2.2 j hjj1 hjj2, mul_zero]
    · intro hnot
      exact absurd hmem hnot
  have hcore : lam j2 ≤ Real.exp (-(c2 * δ)) := by
    apply second_eigenvalue_decay (lam j2) c1 c2 δ hlam2 hc1 hc2 hδ
    intro x hx
    have hc := hdecay x hx
    rw [hcorr x, abs_of_nonneg (pow_nonneg hlam2 x)] at hc
    exact hc
  rwa [hlam1, div_one]

end Qatlib.Papers.PEPSObs16.MainResults
