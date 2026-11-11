/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic
import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates

/-!
# Purity kernels from tensor Pauli shadows

This module defines an exact rational product kernel for purity estimation from two tensor Pauli
records. It identifies the kernel with the snapshot trace pairing, proves its mean and variance
bounds, and counts local product operations for the quadratic shadow construction
[HuangKuengPreskill2020].

## Main statements

* `tensor_purity_actual_pair_kernel_and_mean`: explicit kernel and purity expectation.
* `tensor_purity_derived_moment_and_variance_bounds`: moment and U-statistic error bounds.
* `tensorPurityKernelCounted_spec`: exact value and local multiplication count.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowVariance

open Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false

/-- The rational one-qubit purity kernel, equal to one half of one plus nine times the sign
product when the axes match. -/
def tensorPurityLocalRational (a b : Fin 3 × Bool) : ℚ :=
  (1 + if a.1 = b.1 then
    9 * (if a.2 then 1 else -1) * (if b.2 then 1 else -1) else 0) / 2

/-- The product of the rational local purity kernels over all qubits. -/
def tensorPurityKernelRational (n : ℕ) (a b : Fin n → Fin 3 × Bool) : ℚ :=
  ∏ i, tensorPurityLocalRational (a i) (b i)

/-- The real embedding of the rational tensor purity kernel. -/
def tensorPurityKernel (n : ℕ) (a b : Fin n → Fin 3 × Bool) : ℝ :=
  tensorPurityKernelRational n a b

set_option maxHeartbeats 800000 in

/-- The trace of the product of two single-qubit Pauli shadows equals the complex embedding of
the rational local purity kernel. -/
private theorem tensorPurityLocal_trace (a b : Fin 3 × Bool) :
    Matrix.trace (PauliShadow a.2 a.1 * PauliShadow b.2 b.1) =
      (tensorPurityLocalRational a b : ℂ) := by
  rcases a with ⟨a, s⟩
  rcases b with ⟨b, t⟩
  fin_cases a <;> fin_cases b <;> cases s <;> cases t <;>
    norm_num [tensorPurityLocalRational, PauliShadow, PauliProjector, pauliMatrix,
      pauliX, pauliY, pauliZ, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.ofNat_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- The tensor purity kernel is the real trace of the product of the two tensor Pauli snapshots. -/
theorem tensorPurityKernel_trace (n : ℕ) (a b : Fin n → Fin 3 × Bool) :
    tensorPurityKernel n a b = (Matrix.trace (tensorPauliSnapshot n a * tensorPauliSnapshot n b)).re := by
  rw [tensorPauliSnapshot, tensorPauliSnapshot, tensorPauliProduct_mul, tensorPauliProduct_trace]
  simp_rw [tensorPurityLocal_trace]
  rw [← Rat.cast_prod, Complex.ratCast_re]
  rfl

/-- The purity kernel equals both the snapshot trace pairing and the explicit rational product
formula, and its mean under independent Pauli records is the state's purity. See
[HuangKuengPreskill2020]. -/
theorem tensor_purity_actual_pair_kernel_and_mean (n : ℕ)
    (a b : Fin n → Fin 3 × Bool) :
    tensorPurityKernel n a b = (Matrix.trace (tensorPauliSnapshot n a * tensorPauliSnapshot n b)).re ∧
      tensorPurityKernel n a b = ∏ i,
        ((1 + (if (a i).1 = (b i).1 then
          9 * (if (a i).2 then 1 else -1) * (if (b i).2 then 1 else -1) else 0 : ℚ)) / 2 : ℚ) ∧
      ∀ (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ),
        pairKernelMean (tensorPauliLaw n ρ hρ) (tensorPurityKernel n) =
          (Matrix.trace (ρ * ρ)).re := by
  refine ⟨tensorPurityKernel_trace n a b, ?_, ?_⟩
  · simp only [tensorPurityKernel, tensorPurityKernelRational, tensorPurityLocalRational]
  · intro ρ hρ
    have hs := tensor_pauli_snapshot_reconstructs_entangled_input n ρ hρ
    conv_rhs => rw [← hs]
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
      pairKernelMean, tensorPurityKernel_trace]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Matrix.trace_mul_comm (tensorPauliSnapshot n x) (tensorPauliSnapshot n y)]
    simp [Complex.mul_re, mul_comm]

/-- The pair U-statistic of the tensor purity kernel, evaluated by `pairUCounted`. -/
noncomputable def tensorPurityU (n : ℕ) {m : ℕ}
    (ω : Fin m → Fin n → Fin 3 × Bool) : ℝ := (pairUCounted (tensorPurityKernel n) ω).1

/-- The local purity kernel of a record with itself is five. -/
private theorem tensorPurityLocal_self (a : Fin 3 × Bool) :
    tensorPurityLocalRational a a = 5 := by
  rcases a with ⟨a, b⟩
  cases b <;> norm_num [tensorPurityLocalRational]

/-- The tensor purity kernel of a record with itself is `5 ^ n`. -/
private theorem tensorPurityKernel_self (n : ℕ) (a : Fin n → Fin 3 × Bool) :
    tensorPurityKernel n a a = (5 : ℝ) ^ n := by
  simp [tensorPurityKernel, tensorPurityKernelRational, tensorPurityLocal_self]

set_option maxHeartbeats 800000 in

/-- Every tensor Pauli snapshot is Hermitian. -/
private theorem tensorPuritySnapshot_hermitian (n : ℕ) (a : Fin n → Fin 3 × Bool) :
    (tensorPauliSnapshot n a).IsHermitian := by
  have hl (b : Fin 3 × Bool) : (PauliShadow b.2 b.1).IsHermitian := by
    rcases b with ⟨b, s⟩
    ext i j
    fin_cases b <;> cases s <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply, PauliShadow, PauliProjector, pauliMatrix,
        pauliX, pauliY, pauliZ, Matrix.smul_apply, Matrix.ofNat_apply]
  unfold tensorPauliSnapshot Matrix.IsHermitian
  rw [tensorPauliProduct_conjTranspose]
  congr 1
  funext i
  exact hl (a i)

/-- The squared real trace pairing of two Hermitian matrices is bounded by the product of the
real traces of their squares. -/
private theorem hermitian_trace_pairing_sq {D : ℕ} (A B : Operator D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).re ^ 2 ≤ (Matrix.trace (A * A)).re * (Matrix.trace (B * B)).re := by
  let a : HermitianMat (Fin D) ℂ := ⟨A, hA⟩
  let b : HermitianMat (Fin D) ℂ := ⟨B, hB⟩
  have hc := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm a b) 2
  rw [sq_abs, mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hc
  simpa only [HermitianMat.inner_eq_re_trace] using! hc

/-- The real trace of the square of a density operator is at most one. -/
private theorem density_purity_le_one {D : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (Matrix.trace (ρ * ρ)).re ≤ 1 := by
  let r := Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState (Fin D) ⟨ρ, hρ⟩
  have hr : inner ℝ r.M r.M ≤ 1 := by
    simpa using HermitianMat.inner_le_mul_trace r.nonneg r.nonneg
  simpa only [HermitianMat.inner_eq_re_trace] using! hr

/-- Averaging the second purity record replaces its snapshot by the input density operator in
the trace pairing. -/
private theorem tensorPurityConditional (n : ℕ) (ρ : Operator (2 ^ n))
    (hρ : IsDensityOperator ρ) (a : Fin n → Fin 3 × Bool) :
    (∑ b, (tensorPauliLaw n ρ hρ).prob b * tensorPurityKernel n a b) =
      (Matrix.trace (tensorPauliSnapshot n a * ρ)).re := by
  conv_rhs => rw [← tensor_pauli_snapshot_reconstructs_entangled_input n ρ hρ]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, tensorPurityKernel_trace]
  apply Finset.sum_congr rfl
  intro b _
  simp [Complex.mul_re]

/-- The purity kernel has conditional variance at most `5 ^ n` and kernel variance at most `25 ^
n`; for `m ≥ 2`, the U-statistic mean squared error satisfies the displayed bound with
coefficients `4 / m` and `2 / (m * (m - 1))`. See [HuangKuengPreskill2020]. -/
theorem tensor_purity_derived_moment_and_variance_bounds (n m : ℕ)
    (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ) (hm : 2 ≤ m) :
    let p := tensorPauliLaw n ρ hρ
    pairConditionalVariance p (tensorPurityKernel n) ≤ (5 : ℝ) ^ n ∧
      pairKernelVariance p (tensorPurityKernel n) ≤ (25 : ℝ) ^ n ∧
      (∑ ω : Fin m → Fin n → Fin 3 × Bool, p.probOf ω *
        (tensorPurityU n ω - (Matrix.trace (ρ * ρ)).re) ^ 2) ≤
          4 * (5 : ℝ) ^ n / (m : ℝ) + 2 * (25 : ℝ) ^ n / ((m : ℝ) * (m - 1 : ℕ)) := by
  classical
  let p := tensorPauliLaw n ρ hρ
  let H := tensorPurityKernel n
  have hmean := (tensor_purity_actual_pair_kernel_and_mean n (fun _ => (0, false))
    (fun _ => (0, false))).2.2 ρ hρ
  have hcond (a : Fin n → Fin 3 × Bool) : (∑ b, p.prob b * H a b) ^ 2 ≤ (5 : ℝ) ^ n := by
    rw [tensorPurityConditional]
    have hs := hermitian_trace_pairing_sq (tensorPauliSnapshot n a) ρ
      (tensorPuritySnapshot_hermitian n a) hρ.1.isHermitian
    rw [← tensorPurityKernel_trace n a a, tensorPurityKernel_self] at hs
    exact hs.trans ((mul_le_mul_of_nonneg_left (density_purity_le_one ρ hρ) (by positivity)).trans
      (mul_one _).le)
  have hpair (a b : Fin n → Fin 3 × Bool) : H a b ^ 2 ≤ (25 : ℝ) ^ n := by
    have hs := hermitian_trace_pairing_sq (tensorPauliSnapshot n a) (tensorPauliSnapshot n b)
      (tensorPuritySnapshot_hermitian n a) (tensorPuritySnapshot_hermitian n b)
    rw [← tensorPurityKernel_trace n a b, ← tensorPurityKernel_trace n a a,
      ← tensorPurityKernel_trace n b b, tensorPurityKernel_self, tensorPurityKernel_self] at hs
    calc H a b ^ 2 ≤ (5 : ℝ) ^ n * (5 : ℝ) ^ n := hs
      _ = (25 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  have hμ : (∑ a, p.prob a * ∑ b, p.prob b * H a b) = pairKernelMean p H := by
    simp only [pairKernelMean, Finset.mul_sum, mul_assoc]
  have hcraw := finite_pair_variance_le_second p (fun a => ∑ b, p.prob b * H a b)
  rw [hμ] at hcraw
  have hc : pairConditionalVariance p H ≤ (5 : ℝ) ^ n := by
    calc pairConditionalVariance p H ≤ ∑ a, p.prob a * (∑ b, p.prob b * H a b) ^ 2 := hcraw
      _ ≤ ∑ a, p.prob a * (5 : ℝ) ^ n :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hcond a) (p.nonneg a)
      _ = (5 : ℝ) ^ n := by rw [← Finset.sum_mul, p.sum_one, one_mul]
  let q : FinDist ((Fin n → Fin 3 × Bool) × (Fin n → Fin 3 × Bool)) :=
    { prob := fun x => p.prob x.1 * p.prob x.2
      nonneg := fun x => mul_nonneg (p.nonneg _) (p.nonneg _)
      sum_one := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.sum_one] }
  have hpraw : pairKernelVariance p H ≤ ∑ a, ∑ b, p.prob a * p.prob b * H a b ^ 2 := by
    simpa only [q, Fintype.sum_prod_type, pairKernelVariance, pairKernelMean] using
      finite_pair_variance_le_second q (fun x => H x.1 x.2)
  have hp : pairKernelVariance p H ≤ (25 : ℝ) ^ n := by
    calc pairKernelVariance p H ≤ ∑ a, ∑ b, p.prob a * p.prob b * H a b ^ 2 := hpraw
      _ ≤ ∑ a, ∑ b, p.prob a * p.prob b * (25 : ℝ) ^ n :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hpair a b) (mul_nonneg (p.nonneg a) (p.nonneg b))
      _ = (25 : ℝ) ^ n := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, p.sum_one, one_mul, mul_one]
  have hsym : ∀ a b, H a b = H b a := by
    intro a b
    change tensorPurityKernel n a b = tensorPurityKernel n b a
    rw [tensorPurityKernel_trace, tensorPurityKernel_trace, Matrix.trace_mul_comm]
  have hU (ω : Fin m → Fin n → Fin 3 × Bool) : tensorPurityU n ω = pairUStatistic H ω :=
    (finite_pair_u_statistic_actual_value_and_count _ m H ω).1
  have hv := finite_pair_u_statistic_exact_variance _ p m H hm hsym
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmp : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (by omega : 0 < m - 1)
  have hcoeff : (4 * (m - 2 : ℕ) : ℝ) / ((m : ℝ) * (m - 1 : ℕ)) ≤ 4 / (m : ℝ) := by
    rw [div_le_div_iff₀ (mul_pos hmpos hmp) hmpos]
    have hpred : ((m - 2 : ℕ) : ℝ) ≤ (m - 1 : ℕ) := by exact_mod_cast (by omega : m - 2 ≤ m - 1)
    nlinarith
  refine ⟨hc, hp, ?_⟩
  simp_rw [hU, ← hmean]
  rw [hv]
  calc
    _ ≤ (4 * (m - 2 : ℕ) : ℝ) / ((m : ℝ) * (m - 1 : ℕ)) * (5 : ℝ) ^ n +
        2 / ((m : ℝ) * (m - 1 : ℕ)) * (25 : ℝ) ^ n := by
      gcongr
    _ ≤ (4 / (m : ℝ)) * (5 : ℝ) ^ n +
        2 / ((m : ℝ) * (m - 1 : ℕ)) * (25 : ℝ) ^ n := by
      gcongr
    _ = _ := by ring

/-- The rational purity kernel computed by a fold, together with the number of local factors
multiplied. -/
def tensorPurityKernelCounted (n : ℕ) (a b : Fin n → Fin 3 × Bool) : ℚ × ℕ :=
  (List.ofFn (fun i => tensorPurityLocalRational (a i) (b i))).foldl
    (fun acc c => (acc.1 * c, acc.2 + 1)) (1, 0)

/-- Folding counted multiplication over rational factors multiplies the initial value by their
product and increases the count by the list length. -/
private theorem tensorPurity_product_fold (cs : List ℚ) (acc : ℚ × ℕ) :
    cs.foldl (fun acc c => (acc.1 * c, acc.2 + 1)) acc =
      (acc.1 * cs.prod, acc.2 + cs.length) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp [ih, mul_assoc, add_assoc, Nat.add_comm]

/-- The counted purity kernel returns `tensorPurityKernelRational` and performs exactly `n`
local multiplications. -/
theorem tensorPurityKernelCounted_spec (n : ℕ) (a b : Fin n → Fin 3 × Bool) :
    (tensorPurityKernelCounted n a b).1 = tensorPurityKernelRational n a b ∧
      (tensorPurityKernelCounted n a b).2 = n := by
  simp [tensorPurityKernelCounted, tensorPurity_product_fold, tensorPurityKernelRational,
    List.prod_ofFn]

end Qatlib.Concepts.ShadowModels.ShadowVariance
