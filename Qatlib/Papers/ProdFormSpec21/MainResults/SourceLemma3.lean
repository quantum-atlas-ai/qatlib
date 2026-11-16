/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ProdFormSpec21.MainResults.SourceModel
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3 (real-Hamiltonian off-diagonal cancellation, energy shift) — paper-layer Lean

Source: *Spectral Analysis of Product Formulas for Quantum Simulation*,
arXiv:2102.12655v1, **Lemma 3**, pp.3–4, Eq (18)–(19); proof in Appendix E.

Paper statement.  When every layer Hamiltonian has only **real** matrix elements
(the "real-Hamiltonian class"), the first-order perturbation of the effective
Hamiltonian `H̃` does not shift any eigenenergy: for an eigenvector `|ψk⟩` of the
target Hamiltonian `H` with real amplitudes,

  `⟨ψk| (iδt/2) Σ_{l>m} [Hi^l, Hi^m] |ψk⟩ = 0`        (Eq (18))

and therefore the effective eigenenergy `Ẽk` differs from `Ek` only at second
order,

  `|Ẽk − Ek| = O(N² δt² max{1, 1/lam²})`.                  (Eq (19))

Appendix E argues: for real symmetric `A,B` and a real vector `v`,
`⟨v|[A,B]|v⟩ = ⟨v|AB|v⟩ − ⟨v|BA|v⟩` and both terms equal `(Av)·(Bv)`, so the
commutator expectation — pure imaginary for Hermitian `A,B` — is a real number and
hence vanishes.  The residual magnitude `O(N²δt²/lam²)` (Eq (19)) then follows from
the second-order Magnus term `Σ[H̃_l, H̃_m]` at `t = O(1/lam)`.

We prove the algebraic cancellation for symmetric layers and a real vector.
The energy estimate is repaired at the analytic interface: the energy difference
is twice continuously differentiable on `[0, lam/N]` and its first derivative at
zero vanishes. Taylor's theorem supplies a uniform constant on that interval.
Deriving these hypotheses from the product-formula spectrum requires a separate
source bridge absent from the shared model.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ProdFormSpec21.MainResults
open Qatlib.Papers.ProdFormSpec21.MainResults

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I]

/-- A state vector is **real**: every amplitude has zero imaginary part. -/
def IsRealVec (v : QState I) : Prop := ∀ i, (v i).im = 0

/-- A matrix is **real**: every entry has zero imaginary part. -/
def IsRealMat (M : Matrix I I ℂ) : Prop := ∀ i j, (M i j).im = 0

/-! ## Linearity of `expectOf` and real-vector normal forms -/

/-- `expectOf` is additive in the matrix argument. -/
theorem expectOf_add (M N : Matrix I I ℂ) (v : QState I) :
    expectOf (M + N) v = expectOf M v + expectOf N v := by
  classical
  rw [expectOf, expectOf, expectOf, ApplyGate, ApplyGate, ApplyGate, Matrix.add_mulVec,
    inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- `expectOf` vanishes on the zero matrix. -/
theorem expectOf_zero (v : QState I) : expectOf 0 v = 0 := by
  classical
  rw [expectOf, ApplyGate]
  simp [inner_apply]

/-- `expectOf` is subtractive in the matrix argument. -/
theorem expectOf_sub (M N : Matrix I I ℂ) (v : QState I) :
    expectOf (M - N) v = expectOf M v - expectOf N v := by
  classical
  rw [expectOf, expectOf, expectOf, ApplyGate, ApplyGate, ApplyGate, Matrix.sub_mulVec,
    inner_apply, inner_apply, inner_apply]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `expectOf` is homogeneous in the matrix argument. -/
theorem expectOf_smul (c : ℂ) (M : Matrix I I ℂ) (v : QState I) :
    expectOf (c • M) v = c * expectOf M v := by
  classical
  rw [expectOf, expectOf, ApplyGate, ApplyGate, smul_mulVec, Inner_smul_right]

/-- `expectOf` is additive over finite matrix sums. -/
theorem expectOf_sum {J : Type*} (s : Finset J) (M : J → Matrix I I ℂ) (v : QState I) :
    expectOf (∑ j ∈ s, M j) v = ∑ j ∈ s, expectOf (M j) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expectOf_zero]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, expectOf_add, ih]

/-- For a real vector `v`, the expectation `⟨v|M|v⟩` is the real quadratic form
`∑ᵢ vᵢ (M v)ᵢ` (the conjugate in the inner product acts trivially). -/
theorem expectOf_real (M : Matrix I I ℂ) (v : QState I) (hv : IsRealVec v) :
    expectOf M v = ∑ i, v i * (M *ᵥ v) i := by
  classical
  have h1 : expectOf M v = ∑ i, star (v i) * (M *ᵥ v) i := by
    rw [expectOf, ApplyGate, inner_apply]
    simp only [RCLike.star_def]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (v i) = v i := by
    rw [Complex.star_def, Complex.conj_eq_iff_im]
    exact hv i
  rw [h]

/-- For a symmetric matrix `A`, the bilinear form `∑ᵢ vᵢ (A u)ᵢ` is symmetric in
`u` and `v`: swapping the two vectors amounts to transposing `A`. -/
theorem sum_mulVec_symm (A : Matrix I I ℂ) (u v : QState I) (hA : A.IsSymm) :
    (∑ i, v i * (A *ᵥ u) i) = ∑ i, u i * (A *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  calc ∑ i, ∑ j, v i * (A i j * u j)
      = ∑ j, ∑ i, v i * (A i j * u j) := by rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, u j * (A j i * v i) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hA.apply i j]
        ring
    _ = ∑ i, ∑ j, u i * (A i j * v j) := by rw [Finset.sum_comm]

/-- **Lemma 3, Eq (18) — the commutator expectation vanishes.**  For real symmetric
`A,B` and a real vector `v`, `⟨v| [A,B] |v⟩ = 0`.

Appendix E proof sketch: `⟨v|AB|v⟩ = Σ_i v_i (ABv)_i = Σ_{i,j} v_i A_{ij} B_{jk} v_k`
equals, after swapping `i↔k` (both `A,B` real symmetric) and using `v` real, the
complex conjugate of `⟨v|BA|v⟩`; as `[A,B]` is skew-Hermitian its expectation is
purely imaginary, and the reality argument makes it real, hence zero.

Proof: expand `expectOf` with `expectOf_real`, rewrite `(A*B) v = A (B v)`, and use
`sum_mulVec_symm` to identify `⟨v|AB|v⟩ = (Av)·(Bv) = ⟨v|BA|v⟩`.
The identity only needs symmetry of `A,B` and a real vector `v`; real matrix
entries are not required. -/
theorem lemma3_commutator_expectation_zero
    (A B : Matrix I I ℂ) (v : QState I)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (hv : IsRealVec v) :
    expectOf (A * B - B * A) v = 0 := by
  have hAB : expectOf (A * B) v = ∑ i, v i * (A *ᵥ (B *ᵥ v)) i := by
    rw [expectOf_real (A * B) v hv, Matrix.mulVec_mulVec]
  have hBA : expectOf (B * A) v = ∑ i, v i * (B *ᵥ (A *ᵥ v)) i := by
    rw [expectOf_real (B * A) v hv, Matrix.mulVec_mulVec]
  rw [expectOf_sub, hAB, hBA]
  have h1 : ∑ i, v i * (A *ᵥ (B *ᵥ v)) i = ∑ i, (B *ᵥ v) i * (A *ᵥ v) i :=
    sum_mulVec_symm A (B *ᵥ v) v hA
  have h2 : ∑ i, v i * (B *ᵥ (A *ᵥ v)) i = ∑ i, (A *ᵥ v) i * (B *ᵥ v) i :=
    sum_mulVec_symm B (A *ᵥ v) v hB
  rw [h1, h2, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring

/-- **Lemma 3, Eq (18) — first-order perturbation is diagonal-free.**  The leading
Magnus perturbation `V = (iδt/2) Σ_{l>m} [H^l, H^m]` has zero expectation in a real
eigenvector of the target Hamiltonian, by summing
`lemma3_commutator_expectation_zero` over layers. The strict layer ordering avoids
the identically cancelling sum over all pairs.

Proof: `expectOf` of a complex multiple is the multiple of the expectation, and the
sum of zero summands is zero (`Finset.sum_eq_zero`).  The layer-wise vanishing is
`lemma3_commutator_expectation_zero`. -/
theorem lemma3_first_perturbation_offdiagonal
    {J : Type*} [Fintype J] [LinearOrder J]
    (δt : ℝ) (layer : J → Matrix I I ℂ) (v : QState I)
    (hsym : ∀ j, (layer j).IsSymm)
    (hv : IsRealVec v) :
    expectOf ((Complex.I * (δt : ℂ) / 2) •
      (∑ j, ∑ k ∈ Finset.univ.filter (fun k => k < j),
        (layer j * layer k - layer k * layer j))) v = 0 := by
  rw [expectOf_smul]
  have hsum1 : expectOf (∑ j, ∑ k ∈ Finset.univ.filter (fun k => k < j),
        (layer j * layer k - layer k * layer j)) v
      = ∑ j, expectOf (∑ k ∈ Finset.univ.filter (fun k => k < j),
        (layer j * layer k - layer k * layer j)) v := by
    simpa using expectOf_sum (Finset.univ)
      (fun j => ∑ k ∈ Finset.univ.filter (fun k => k < j),
        (layer j * layer k - layer k * layer j)) v
  rw [hsum1]
  have hpair : ∀ j k, expectOf (layer j * layer k - layer k * layer j) v = 0 := by
    intro j k
    exact lemma3_commutator_expectation_zero (layer j) (layer k) v
      (hsym j) (hsym k) hv
  have hsum2 : ∀ j, expectOf (∑ k ∈ Finset.univ.filter (fun k => k < j),
        (layer j * layer k - layer k * layer j)) v
      = ∑ k ∈ Finset.univ.filter (fun k => k < j),
        expectOf (layer j * layer k - layer k * layer j) v := by
    intro j
    simpa using expectOf_sum (Finset.univ.filter (fun k => k < j))
      (fun k => layer j * layer k - layer k * layer j) v
  have hinner : ∀ j, expectOf (∑ k ∈ Finset.univ.filter (fun k => k < j),
        (layer j * layer k - layer k * layer j)) v = 0 := by
    intro j
    rw [hsum2 j]
    exact Finset.sum_eq_zero fun k _ => hpair j k
  rw [Finset.sum_eq_zero fun j _ => hinner j, mul_zero]

/-- Linear energy drift satisfies the original base-point hypothesis but admits
no uniform quadratic bound, even with width and gap both equal to one. -/
private theorem linear_drift_counterexample :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → |s| ≤ C * s ^ 2 := by
  rintro ⟨C, hC, hb⟩
  let s := 1 / (C + 1)
  have hs : 0 < s := by dsimp [s]; positivity
  have hid : (C + 1) * s = 1 := by
    dsimp [s]
    field_simp
  have h := hb s hs.le
  rw [abs_of_pos hs] at h
  have hi := congrArg (fun x : ℝ => x * s) hid
  nlinarith [sq_pos_of_pos hs]

/-- **Lemma 3, Eq (19) — effective energy shift.**  Uniformly in the step size
`0 ≤ δt ≤ lam/N`, the effective eigenenergy `Ẽk(δt)` deviates from the target `Ek` only at
second order:

  `|Ẽk(δt) − Ek| ≤ C · N² · δt² · max{1, 1/lam²}`,

for a constant `C` independent of `δt` (the paper's `O(N²δt² max{1,1/lam²})`).

The analytic hypotheses express second-order regularity and first-order
cancellation without assuming an error bound. The constant is uniform in step
size on this interval; no uniformity in `N` or `lam` is claimed. The physical
spectral bridge is not part of this theorem. -/
theorem lemma3_energy_shift
    (N lam : ℝ) (Eeff Ek : ℝ → ℝ)
    (hN : 0 < N) (hlam : 0 < lam)
    (hbase : Eeff 0 = Ek 0)
    (hsmooth : ContDiffOn ℝ 2 (fun s => Eeff s - Ek s) (Set.Icc 0 (lam / N)))
    (hfirst : HasDerivWithinAt (fun s => Eeff s - Ek s) 0
      (Set.Icc 0 (lam / N)) 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ δt : ℝ, 0 ≤ δt → δt ≤ lam / N →
        |Eeff δt - Ek δt| ≤ C * N ^ 2 * δt ^ 2 * max 1 (1 / lam ^ 2) := by
  have hr : 0 < lam / N := div_pos hlam hN
  obtain ⟨K, hK⟩ := exists_taylor_mean_remainder_bound (n := 1) hr.le hsmooth
  have hd : derivWithin (fun s => Eeff s - Ek s) (Set.Icc 0 (lam / N)) 0 = 0 :=
    hfirst.derivWithin ((uniqueDiffOn_Icc hr) 0 ⟨le_rfl, hr.le⟩)
  have ht (s : ℝ) :
      taylorWithinEval (fun s => Eeff s - Ek s) 1 (Set.Icc 0 (lam / N)) 0 s = 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ]
    simp [iteratedDerivWithin_one, hd, hbase]
  let C := (|K| + 1) / (N ^ 2 * max 1 (1 / lam ^ 2))
  have hden : 0 < N ^ 2 * max 1 (1 / lam ^ 2) := by positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s hs hsr
  have hb := hK s ⟨hs, hsr⟩
  rw [ht] at hb
  simp only [sub_zero, Real.norm_eq_abs] at hb
  have hc : C * N ^ 2 * s ^ 2 * max 1 (1 / lam ^ 2) = (|K| + 1) * s ^ 2 := by
    dsimp [C]
    field_simp
  rw [hc]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (sq_nonneg s))

end Qatlib.Papers.ProdFormSpec21.MainResults
