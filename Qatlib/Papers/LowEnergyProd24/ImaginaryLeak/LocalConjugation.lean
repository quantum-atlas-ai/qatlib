/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.SupportedSeries
import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.Hadamard
import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Weights

/-!
# Local imaginary-time conjugation and leakage

Support-sensitive bounds on repeated commutators with the total Hamiltonian control
imaginary-time conjugation of a local operator. The geometric bound `actual_local_conjugation`
yields a half-radius estimate and an exponential bound on transitions between separated energy
sectors in `actual_local_leakage`. See [HejaziZiniArrazola2024].

## Main statements

* `actual_adIter_norm`: For nonnegative `J` and an operator supported on at most `(m + 1) * k`
  sites, the `n`-fold commutator with the total Hamiltonian has norm at most `n! * choose (n +
  m) m * (J * k * d)^n * ‖A‖`.
* `actual_local_conjugation`: For nonnegative `J` and `lam` with `lam * J * k * d < 1`,
  imaginary-time weighting of an operator supported on at most `(m + 1) * k` sites has norm at
  most `‖A‖ / (1 - lam * J * k * d)^(m + 1)`.
* `actual_local_leakage`: For positive `J`, `k`, and `d`, the transition block from energies at
  most `Δ` to energies above `Λ` of an operator supported on at most `(m + 1) * k` sites has
  norm at most `exp(-(Λ - Δ) / (2 * J * k * d)) * 2^(m + 1) * ‖A‖`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.LocalModel.SupportedSeries
open Qatlib.Foundations.MatrixAlgebra.TensorSupport
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) :=
    NormedAlgebra.restrictScalars ℝ ℂ _

/-- Repeated commutation with the total Hamiltonian equals nesting commutators with the full
selected interaction set at every level. -/
theorem actual_adIter (h : Hamiltonian N R M k d J) (A : Matrix (Register N) (Register N) ℂ) (n : ℕ) :
    adIter h.total n A=nested h A (List.replicate n Finset.univ) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [adIter,List.replicate_succ,nested,ih,← total_selected]
    rfl

/-- For nonnegative `J` and an operator supported on at most `(m + 1) * k` sites, the `n`-fold
commutator with the total Hamiltonian has norm at most `n! * choose (n + m) m * (J * k *
d)^n * ‖A‖`. -/
theorem actual_adIter_norm (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J) (s : Finset (Fin N))
    (m : ℕ) (hs : s.card ≤ (m+1)*k) (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s) (n : ℕ) :
    ‖adIter h.total n A‖ ≤ (n.factorial:ℝ)*((n+m).choose m:ℝ)*(J*k*d)^n*‖A‖ := by
  rw [actual_adIter]
  have hb:=nested_norm h hJ s (m+1) hs A hA (List.replicate n Finset.univ)
  simp only [List.length_replicate,Nat.ascFactorial_eq_factorial_mul_choose] at hb
  have hc : (m+n).choose n=(n+m).choose m := by rw [Nat.add_comm m n,Nat.choose_symm_add]
  rw [hc] at hb
  convert hb using 1
  push_cast
  ring

/-- For nonnegative `J` and `lam`, the degree-`n` Hadamard term of an operator supported on at
most `(m + 1) * k` sites has norm at most `choose (n + m) m * (lam * J * k * d)^n * ‖A‖`. -/
theorem actual_hadamard_term (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J) (s : Finset (Fin N))
    (m : ℕ) (hs : s.card ≤ (m+1)*k) (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s)
    (lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    ‖(lam^n/(n.factorial:ℝ)) • adIter h.total n A‖ ≤ ((n+m).choose m:ℝ)*(lam*J*k*d)^n*‖A‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ lam^n/(n.factorial:ℝ))]
  calc
    _ ≤ (lam^n/(n.factorial:ℝ))*((n.factorial:ℝ)*((n+m).choose m:ℝ)*(J*k*d)^n*‖A‖) :=
      mul_le_mul_of_nonneg_left (actual_adIter_norm h hJ s m hs A hA n) (by positivity)
    _ = _ := by
      have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp
      ring

/-- For nonnegative `J` and `lam` with `lam * J * k * d < 1`, imaginary-time weighting of an
operator supported on at most `(m + 1) * k` sites has norm at most `‖A‖ / (1 - lam * J * k *
d)^(m + 1)`. -/
theorem actual_local_conjugation (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J) (s : Finset (Fin N))
    (m : ℕ) (hs : s.card ≤ (m+1)*k) (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s)
    (lam : ℝ) (hlam : 0 ≤ lam) (hsmall : lam*J*k*d < 1) :
    ‖weighted h.total A lam‖ ≤ ‖A‖/(1-lam*J*k*d)^(m+1) := by
  have hr : ‖lam*J*k*d‖ < 1 := by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact hsmall
  have hm : HasSum (fun n : ℕ=>((n+m).choose m:ℝ)*(lam*J*k*d)^n*‖A‖)
      ((1/(1-lam*J*k*d)^(m+1))*‖A‖) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one m (r:=lam*J*k*d) hr).mul_right ‖A‖
  have he (t : ℝ) : t • h.total=(t:ℂ) • h.total := by
    ext i j
    exact Complex.real_smul
  have hsA : HasSum (fun n : ℕ=>(lam^n/(n.factorial:ℝ)) • adIter h.total n A)
      (weighted h.total A lam) := by
    simpa only [he,weighted,Complex.ofReal_neg] using (conjugation_hasSum h.total A lam)
  have hb : ‖weighted h.total A lam‖ ≤ (1/(1-lam*J*k*d)^(m+1))*‖A‖ :=
    HasSum.norm_le_of_bounded hsA hm (actual_hadamard_term h hJ s m hs A hA lam hlam)
  convert hb using 1
  ring

/-- For positive `J`, `k`, and `d`, weighting at `1 / (2 * J * k * d)` increases the norm of an
operator supported on at most `(m + 1) * k` sites by at most the factor `2^(m + 1)`. -/
theorem actual_local_conjugation_half (h : Hamiltonian N R M k d J) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
    (s : Finset (Fin N)) (m : ℕ) (hs : s.card ≤ (m+1)*k)
    (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s) :
    ‖weighted h.total A (1/(2*J*k*d))‖ ≤ 2^(m+1)*‖A‖ := by
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hd' : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have he : (1/(2*J*k*d))*J*k*d=(1/2:ℝ) := by field_simp
  have hb:=actual_local_conjugation h hJ.le s m hs A hA (1/(2*J*k*d)) (by positivity)
      (by rw [he]; norm_num)
  rw [he] at hb
  convert hb using 1
  rw [div_eq_mul_inv,← inv_pow]
  norm_num
  ring

/-- For positive `J`, `k`, and `d`, the transition block from energies at most `Δ` to energies
above `Λ` of an operator supported on at most `(m + 1) * k` sites has norm at most `exp(-(Λ
- Δ) / (2 * J * k * d)) * 2^(m + 1) * ‖A‖`. -/
theorem actual_local_leakage (h : Hamiltonian N R M k d J) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
    (s : Finset (Fin N)) (m : ℕ) (hs : s.card ≤ (m+1)*k)
    (A : Matrix (Register N) (Register N) ℂ) (hA : A∈onSupport s) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*A*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*(2^(m+1)*‖A‖) :=
  (weighted_leakage h.total A h.total_hermitian Δ Λ (1/(2*J*k*d)) (by positivity)).trans
    (mul_le_mul_of_nonneg_left (actual_local_conjugation_half h hJ hk hd s m hs A hA) (Real.exp_pos _).le)

end Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
