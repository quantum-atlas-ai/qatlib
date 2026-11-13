/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.ShadowPurityConsumers
import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution

/-!
# Quadratic observables from Pauli shadows

This module constructs the symmetrized pair kernel and U-statistic for a two-register
observable. It proves unbiasedness, an exact variance decomposition, median concentration for
many observables sharing the same Born records, and quantum and classical resource counts in the
setting of [HuangKuengPreskill2020].

## Main statements

* `quadratic_shadow_actual_u_unbiased`: unbiased estimation of the quadratic trace functional.
* `quadratic_shadow_exact_covariance_from_same_records`: exact pair U-statistic variance.
* `quadratic_same_born_records_many_observables`: simultaneous median concentration.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowVariance

open Matrix
open scoped Classical BigOperators ComplexOrder Kronecker
set_option autoImplicit false

/-- The average of a two-register observable and its conjugate by the register-swap matrix. -/
noncomputable def quadraticSymmetric {D : ℕ}
    (O : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :=
  (1 / 2 : ℂ) • (O + swapRegisterMatrix D * O * swapRegisterMatrix D)

/-- The real trace pairing of the symmetrized observable with the tensor product of two Pauli
snapshots. -/
noncomputable def quadraticShadowKernel (n : ℕ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (a b : Fin n → Fin 3 × Bool) : ℝ :=
  (Matrix.trace (quadraticSymmetric O *
    TensorGate (tensorPauliSnapshot n a) (tensorPauliSnapshot n b))).re

/-- The pair U-statistic of the quadratic shadow kernel on a finite record. -/
noncomputable def quadraticShadowU (n m : ℕ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ω : Fin m → Fin n → Fin 3 × Bool) : ℝ :=
  pairUStatistic (quadraticShadowKernel n O) ω

/-- The second moment of the trace pairing with one Pauli snapshot and one copy of the state. -/
noncomputable def quadraticShadowFirstMoment (n : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ) : ℝ :=
  ∑ a, (tensorPauliLaw n ρ hρ).prob a *
    (Matrix.trace (quadraticSymmetric O * TensorGate (tensorPauliSnapshot n a) ρ)).re ^ 2

/-- The second moment of the quadratic shadow kernel on two independent Pauli records. -/
noncomputable def quadraticShadowPairMoment (n : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ) : ℝ :=
  ∑ a, ∑ b, (tensorPauliLaw n ρ hρ).prob a *
    (tensorPauliLaw n ρ hρ).prob b * quadraticShadowKernel n O a b ^ 2

/-- The sorted median of `2 * r + 1` blockwise quadratic shadow U-statistics. -/
noncomputable def quadraticShadowMedian (n m r : ℕ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) : ℝ :=
  sortedBlockMedian r (fun b => quadraticShadowU n m O (ω b))

/-- Conjugation by the register-swap matrix exchanges the factors of a tensor product. -/
theorem quadratic_swap_tensor {D : ℕ} (A B : Operator D) :
    swapRegisterMatrix D * TensorGate A B * swapRegisterMatrix D = TensorGate B A := by
  classical
  have hleft (x y : Fin D × Fin D) :
      (swapRegisterMatrix D * TensorGate A B) x y = A x.2 y.1 * B x.1 y.2 := by
    simp only [Matrix.mul_apply, swapRegisterMatrix_apply]
    rw [Fintype.sum_eq_single (Prod.swap x)
      (fun p hp => by rw [if_neg (fun e => hp (by rw [e, Prod.swap_swap])), zero_mul])]
    rw [Prod.swap_swap, if_pos rfl, one_mul]
    rfl
  ext x y
  change (∑ p, (swapRegisterMatrix D * TensorGate A B) x p * swapRegisterMatrix D p y) = _
  rw [Fintype.sum_eq_single (Prod.swap y)
    (fun p hp => by rw [swapRegisterMatrix_apply, if_neg hp, mul_zero])]
  rw [hleft]
  simp only [swapRegisterMatrix_apply, ite_true, mul_one]
  exact mul_comm _ _

/-- Moving register-swap conjugation from the observable to a tensor product exchanges its
factors in the trace pairing. -/
private theorem quadratic_swap_trace {D : ℕ}
    (O : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (A B : Operator D) :
    Matrix.trace ((swapRegisterMatrix D * O * swapRegisterMatrix D) * TensorGate A B) =
      Matrix.trace (O * TensorGate B A) := by
  calc
    _ = Matrix.trace (swapRegisterMatrix D * (O * swapRegisterMatrix D * TensorGate A B)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((O * swapRegisterMatrix D * TensorGate A B) * swapRegisterMatrix D) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (O * (swapRegisterMatrix D * TensorGate A B * swapRegisterMatrix D)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [quadratic_swap_tensor]

/-- Pairing a symmetrized observable with a tensor product averages the trace pairings in the
two factor orders. -/
theorem quadratic_symmetric_trace {D : ℕ}
    (O : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (A B : Operator D) :
    Matrix.trace (quadraticSymmetric O * TensorGate A B) =
      (1/2 : ℂ) * (Matrix.trace (O * TensorGate A B) + Matrix.trace (O * TensorGate B A)) := by
  rw [quadraticSymmetric, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
    Matrix.trace_add, quadratic_swap_trace]
  rfl

/-- Symmetrization preserves Hermiticity, makes the shadow kernel symmetric, and preserves its
trace pairing with two identical input operators. See [HuangKuengPreskill2020]. -/
theorem quadratic_actual_symmetrization_and_kernel (n : ℕ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ρ : Operator (2^n)) (hO : O.IsHermitian) :
    (quadraticSymmetric O).IsHermitian ∧
      (∀ a b, quadraticShadowKernel n O a b = quadraticShadowKernel n O b a) ∧
      Matrix.trace (quadraticSymmetric O * TensorGate ρ ρ) = Matrix.trace (O * TensorGate ρ ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold quadraticSymmetric Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      swapRegisterMatrix_conjTranspose, hO.eq, Matrix.mul_assoc]
    norm_num
  · intro a b
    simp only [quadraticShadowKernel, quadratic_symmetric_trace, add_comm]
  · rw [quadratic_symmetric_trace]
    ring

/-- Tensoring with a fixed left factor distributes over a finite sum in the right factor. -/
private theorem quadratic_tensor_sum_right {D : ℕ} {X : Type} [Fintype X]
    (A : Operator D) (B : X → Operator D) :
    TensorGate A (∑ x, B x) = ∑ x, TensorGate A (B x) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [TensorGate, Matrix.sum_apply, Finset.mul_sum]

/-- Tensoring with a fixed right factor distributes over a finite sum in the left factor. -/
private theorem quadratic_tensor_sum_left {D : ℕ} {X : Type} [Fintype X]
    (A : X → Operator D) (B : Operator D) :
    TensorGate (∑ x, A x) B = ∑ x, TensorGate (A x) B := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [TensorGate, Matrix.sum_apply, Finset.sum_mul]

/-- Averaging the second record of the quadratic shadow kernel replaces its snapshot by the
input density operator. -/
theorem quadraticShadowKernel_conditional (n : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (a : Fin n → Fin 3 × Bool) :
    (∑ b, (tensorPauliLaw n ρ hρ).prob b * quadraticShadowKernel n O a b) =
      (Matrix.trace (quadraticSymmetric O * TensorGate (tensorPauliSnapshot n a) ρ)).re := by
  conv_rhs => rw [← tensor_pauli_snapshot_reconstructs_entangled_input n ρ hρ]
  rw [quadratic_tensor_sum_right]
  simp only [TensorGate, Matrix.kronecker_smul,
    Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp [quadraticShadowKernel, TensorGate, Complex.mul_re]

/-- The mean quadratic shadow kernel equals the real trace pairing of the observable with two
copies of the state. -/
theorem quadraticShadowKernel_mean (n : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ) :
    pairKernelMean (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n O) =
      (Matrix.trace (O * TensorGate ρ ρ)).re := by
  rw [pairKernelMean]
  simp_rw [mul_assoc, ← Finset.mul_sum, quadraticShadowKernel_conditional]
  have ht : Matrix.trace (quadraticSymmetric O * TensorGate ρ ρ) =
      Matrix.trace (O * TensorGate ρ ρ) := by rw [quadratic_symmetric_trace]; ring
  rw [← ht]
  conv_rhs => arg 1; arg 1; arg 2; arg 1; rw [← tensor_pauli_snapshot_reconstructs_entangled_input n ρ hρ]
  rw [quadratic_tensor_sum_left]
  simp only [TensorGate, Matrix.smul_kronecker,
    Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp [Complex.mul_re]

/-- With at least two records, the quadratic shadow U-statistic is unbiased for the real trace
pairing of a Hermitian observable with two copies of the state. See
[HuangKuengPreskill2020]. -/
theorem quadratic_shadow_actual_u_unbiased (n m : ℕ) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (hm : 2 ≤ m) (_hO : O.IsHermitian) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool,
      (tensorPauliLaw n ρ hρ).probOf ω * quadraticShadowU n m O ω) =
        (Matrix.trace (O * TensorGate ρ ρ)).re := by
  simp only [quadraticShadowU]
  rw [finite_pair_u_statistic_unbiased _ _ _ _ hm,
    quadraticShadowKernel_mean]

/-- For a symmetric quadratic shadow kernel and `m ≥ 2`, the mean squared error equals the
conditional variance weighted by `4 * (m - 2) / (m * (m - 1))` plus the kernel variance
weighted by `2 / (m * (m - 1))`. See [HuangKuengPreskill2020]. -/
theorem quadratic_shadow_exact_covariance_from_same_records (n m : ℕ)
    (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (hm : 2 ≤ m) (hO : O.IsHermitian) :
    let p := tensorPauliLaw n ρ hρ
    let h := quadraticShadowKernel n O
    let μ := (Matrix.trace (O * TensorGate ρ ρ)).re
    (∑ ω : Fin m → Fin n → Fin 3 × Bool, p.probOf ω * (quadraticShadowU n m O ω - μ)^2) =
      (4*(m-2:ℕ):ℝ)/((m:ℝ)*(m-1:ℕ))*pairConditionalVariance p h +
        2/((m:ℝ)*(m-1:ℕ))*pairKernelVariance p h := by
  (try dsimp only)
  rw [← quadraticShadowKernel_mean n ρ hρ O]
  exact finite_pair_u_statistic_exact_variance _ _ m _ hm
    (quadratic_actual_symmetrization_and_kernel n O ρ hO).2.1

/-- The quadratic shadow mean squared error is at most `4 / m` times
`quadraticShadowFirstMoment` plus `4 / m ^ 2` times `quadraticShadowPairMoment`. See
[HuangKuengPreskill2020]. -/
theorem quadratic_shadow_computed_moments_and_variance (n m : ℕ)
    (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (hm : 2 ≤ m) (hO : O.IsHermitian) :
    let μ := (Matrix.trace (O * TensorGate ρ ρ)).re
    (∑ ω : Fin m → Fin n → Fin 3 × Bool,
      (tensorPauliLaw n ρ hρ).probOf ω * (quadraticShadowU n m O ω - μ)^2) ≤
      4/(m:ℝ)*quadraticShadowFirstMoment n ρ hρ O +
        4/(m:ℝ)^2*quadraticShadowPairMoment n ρ hρ O := by
  classical
  (try dsimp only)
  let p := tensorPauliLaw n ρ hρ
  let h := quadraticShadowKernel n O
  have hμ : (∑ a, p.prob a * ∑ b, p.prob b * h a b) = pairKernelMean p h := by
    simp only [pairKernelMean, Finset.mul_sum, mul_assoc]
  have hc : pairConditionalVariance p h ≤ quadraticShadowFirstMoment n ρ hρ O := by
    have hh := finite_pair_variance_le_second p (fun a => ∑ b, p.prob b * h a b)
    rw [hμ] at hh
    simpa only [pairConditionalVariance, quadraticShadowFirstMoment, p, h,
      quadraticShadowKernel_conditional] using! hh
  let q : FinDist ((Fin n → Fin 3 × Bool) × (Fin n → Fin 3 × Bool)) :=
    { prob := fun x => p.prob x.1 * p.prob x.2
      nonneg := fun x => mul_nonneg (p.nonneg _) (p.nonneg _)
      sum_one := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.sum_one] }
  have hp : pairKernelVariance p h ≤ quadraticShadowPairMoment n ρ hρ O := by
    simpa only [q, Fintype.sum_prod_type, pairKernelVariance, pairKernelMean,
      quadraticShadowPairMoment, p, h] using!
      finite_pair_variance_le_second q (fun x => h x.1 x.2)
  have hc0 : 0 ≤ quadraticShadowFirstMoment n ρ hρ O :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (p.nonneg _) (sq_nonneg _)
  have hp0 : 0 ≤ quadraticShadowPairMoment n ρ hρ O :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (mul_nonneg (p.nonneg _) (p.nonneg _)) (sq_nonneg _)
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hcast1 : ((m-1:ℕ):ℝ) = (m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
  have hcast2 : ((m-2:ℕ):ℝ) = (m:ℝ)-2 := by
    rw [Nat.cast_sub hm]; norm_num
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 < (m:ℝ)*(m-1:ℕ) := by
    rw [hcast1]
    exact mul_pos hm0 (by linarith)
  have hcoeff1 : (4*(m-2:ℕ):ℝ)/((m:ℝ)*(m-1:ℕ)) ≤ 4/(m:ℝ) := by
    apply (div_le_div_iff₀ hd hm0).2
    rw [hcast1, hcast2]
    nlinarith
  have hcoeff2 : (2:ℝ)/((m:ℝ)*(m-1:ℕ)) ≤ 4/(m:ℝ)^2 := by
    apply (div_le_div_iff₀ hd (sq_pos_of_pos hm0)).2
    rw [hcast1]
    nlinarith
  rw [quadratic_shadow_exact_covariance_from_same_records n m ρ hρ O hm hO]
  calc _ ≤ (4*(m-2:ℕ):ℝ)/((m:ℝ)*(m-1:ℕ))*quadraticShadowFirstMoment n ρ hρ O +
      2/((m:ℝ)*(m-1:ℕ))*quadraticShadowPairMoment n ρ hρ O :=
        add_le_add (mul_le_mul_of_nonneg_left hc (by positivity))
          (mul_le_mul_of_nonneg_left hp (by positivity))
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoeff1 hc0)
      (mul_le_mul_of_nonneg_right hcoeff2 hp0)

/-- Grouped quadratic shadow estimation has the displayed fresh-record resource counts and uses
`(2 * r + 1) * m.choose 2` pair-kernel evaluations. See [HuangKuengPreskill2020]. -/
theorem quadratic_shadow_actual_quantum_and_pair_ledger (n m r : ℕ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) :
    tensorPauliFreshResourceCounts n m (2*r+1) ω =
      ((2*r+1)*m, 2*n*((2*r+1)*m), n*((2*r+1)*m), 0) ∧
      (∑ b, (pairUCounted (quadraticShadowKernel n O) (ω b)).2) = (2*r+1)*m.choose 2 := by
  constructor
  · exact tensorPauliFreshResourceCounts_spec n m (2*r+1) ω
  · simp only [(finite_pair_u_statistic_actual_value_and_count _ m _ _).2,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

/-- Under the stated moment budgets, the probability that any observable's median estimate
exceeds error `ε` is at most the number of observables times `2 ^ (2 * r + 1) * (1 / 16) ^
(r + 1)`. See [HuangKuengPreskill2020]. -/
theorem quadratic_same_born_records_many_observables (n m r : ℕ)
    (Z : Type) [Fintype Z] (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (O : Z → Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ε : ℝ) (hm : 2 ≤ m) (hε : 0 < ε)
    (hbudget : ∀ z, (O z).IsHermitian ∧
      16*(4/(m:ℝ)*quadraticShadowFirstMoment n ρ hρ (O z) +
        4/(m:ℝ)^2*quadraticShadowPairMoment n ρ hρ (O z)) ≤ ε^2) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
      ∃ z, ε < |quadraticShadowMedian n m r (O z) ω - (Matrix.trace (O z * TensorGate ρ ρ)).re|),
      ∏ b, (tensorPauliLaw n ρ hρ).probOf (ω b)) ≤
        (Fintype.card Z:ℝ)*(2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) := by
  classical
  let p := tensorPauliLaw n ρ hρ
  let Y := Fin m → Fin n → Fin 3 × Bool
  let q : FinDist Y :=
    { prob := p.probOf
      nonneg := fun ω => Finset.prod_nonneg fun _ _ => p.nonneg _
      sum_one := p.sum_probOf m }
  let θ := fun z => (Matrix.trace (O z * TensorGate ρ ρ)).re
  have hμ (z : Z) : q.expect (quadraticShadowU n m (O z)) = θ z :=
    quadratic_shadow_actual_u_unbiased n m ρ hρ (O z) hm (hbudget z).1
  have hv (z : Z) : q.expect (fun ω =>
      (quadraticShadowU n m (O z) ω - q.expect (quadraticShadowU n m (O z)))^2) ≤ ε^2/16 := by
    rw [hμ]
    exact (quadratic_shadow_computed_moments_and_variance n m ρ hρ (O z) hm
      (hbudget z).1).trans (by linarith [(hbudget z).2])
  have hc := heterogeneous_same_records_many_observables r 1 (fun _ _ => q)
    (fun _ _ _ => 1) (fun z _ _ => quadraticShadowU n m (O z)) θ ε hε
    (fun z _ => by simpa only [Fin.sum_univ_one, one_mul] using! hμ z)
    (fun z _ => by simpa only [Fin.sum_univ_one, one_pow, one_mul] using! hv z)
  let e : (Fin (2*r+1) → Y) ≃ (Fin (2*r+1) → Fin 1 → Y) :=
    { toFun := fun ω j _ => ω j
      invFun := fun ω j => ω j 0
      left_inv := fun _ => rfl
      right_inv := by
        intro ω
        funext j b
        have hb : b = 0 := Subsingleton.elim _ _
        subst b
        rfl }
  have hblock (z : Z) (ω : Fin (2*r+1) → Y) :
      weightedBlock r 1 (fun _ _ => 1) (fun _ _ => quadraticShadowU n m (O z)) (e ω) =
        fun j => quadraticShadowU n m (O z) (ω j) := by
    funext j
    change (∑ _b : Fin 1, (1:ℝ)*quadraticShadowU n m (O z) (ω j)) = _
    simp only [Fin.sum_univ_one, one_mul]
  have hprob (ω : Fin (2*r+1) → Y) :
      (blockRecordLaw r 1 (fun _ _ => q)).prob (e ω) = ∏ j, p.probOf (ω j) := by
    change (∏ j, ∏ _b : Fin 1, p.probOf (ω j)) = _
    simp only [Fin.prod_univ_one]
  rw [Finset.sum_filter] at hc ⊢
  rw [← e.sum_comp] at hc
  simp_rw [hblock, hprob] at hc
  simpa only [quadraticShadowMedian, θ, p, mul_assoc] using! hc

/-- The quadratic shadow median computed by counted insertion sort, together with its number of
block values and comparisons. -/
noncomputable def quadraticShadowMedianCounted (n m r : ℕ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) : ℝ × ℕ × ℕ :=
  let values := List.ofFn (fun b => quadraticShadowU n m O (ω b))
  let result := insertionSortCounted values
  (result.1.getD r 0, values.length, result.2)

/-- The counted median equals `quadraticShadowMedian`, uses `2 * r + 1` block values, and
performs at most `(2 * r + 1) ^ 2` comparisons. -/
theorem quadraticShadowMedianCounted_spec (n m r : ℕ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) :
    (quadraticShadowMedianCounted n m r O ω).1 = quadraticShadowMedian n m r O ω ∧
      (quadraticShadowMedianCounted n m r O ω).2.1 = 2*r+1 ∧
      (quadraticShadowMedianCounted n m r O ω).2.2 ≤ (2*r+1)^2 := by
  refine ⟨rfl, ?_, ?_⟩
  · exact List.length_ofFn
  · simpa only [quadraticShadowMedianCounted, List.length_ofFn, pow_two] using!
      insertionSortCounted_cost_le (List.ofFn (fun b => quadraticShadowU n m O (ω b)))

end Qatlib.Concepts.ShadowModels.ShadowVariance
