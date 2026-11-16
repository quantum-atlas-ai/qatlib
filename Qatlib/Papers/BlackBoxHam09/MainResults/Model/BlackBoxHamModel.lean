/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# A paper-level model of black-box Hamiltonian simulation

Source: D. W. Berry and A. M. Childs, *Black-box Hamiltonian simulation and unitary
implementation*, arXiv:0910.4157v4 (2 Nov 2011), §II.A "Model" and §III.

This file fixes the vocabulary of the whole paper layer:

* `Ham` — a Hermitian matrix (the paper's black-box Hamiltonian `H ∈ ℂ^{M×M}`);
* `spectralNorm`, `colSumNorm`, `maxEntryNorm` — the three norms `‖H‖`, `‖H‖₁`,
  `‖H‖_max` of §II.A;
* `IsColumnSparse` — the sparsity promise of §II.A (at most `D` nonzero entries per
  column; the paper states rows *or* columns);
* `band`, `magThresholds`, `breakNorm` — the `break(H)` function of Eq. (74)–(75)
  (§VII.A), implemented over the finite set of realized matrix-element magnitudes
  (the paper's maximum over all real `a,b` is attained there);
* `evolution` — the evolution `e^{-iHt}`, taken from the library's
  `HamiltonianEvolution` from the pure-state library, with a bridge theorem to
  the Foundations `DysonPropagator.evolution`;
* `Register`, `valueOracle` — the register `(j,k,z)` and the matrix-element oracle
  `O_H : |j,k⟩|z⟩ ↦ |j,k⟩|z ⊕ H_jk⟩` of Eq. (1);
* `Step2`, `Circuit2`, `QueryCount2`, `Run2` — counted-query circuits with *two*
  oracle calls (`queryH` for `O_H`, `queryF` for `O_F`), reusing the library's
  `Step`/`ApplyGate` machinery and counting both kinds of query;
* `SimulableWithin` — the paper's task predicate: an oracle circuit whose implemented
  operator is within trace distance `δ` of `e^{-iHt}` and which uses at most `q`
  queries in total;
* the closed-form query cost expressions of Theorems 1, 2, 9 and Corollaries 3, 12, 13.

The model is deliberately *task level*: an oracle `O_H` must be a genuine Eq. (1)
value oracle for `H` (`valueOracle φ` with `dec (φ j k) = H j k`), `O_F` is a unitary
on the same register representing the position oracle of Eq. (3), and a simulation is
a concrete counted circuit run against those two unitaries.  The paper's algorithmic
constructions (walk steps, phase estimation, amplitude amplification) are not built
here. The norm bounds in this module are proved directly. The sandwich estimate
requires nonnegative `ε`, and the accumulated-error estimate requires nonnegative `t`.
`BlackBox` does not impose sparsity through its parameter `D` or specify the action of
`OF`; those promises must be imposed separately by consumers. Circuit gates are
arbitrary matrices, so the task predicate by itself does not enforce oracle-independent
gate selection or establish an algorithmic query lower bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Model

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {L : ℕ}

/-! ## 1. Hamiltonians and the norms of §II.A -/

/-- A Hamiltonian on the finite index set `ι`: a Hermitian complex matrix. -/
structure Ham (ι : Type) [Fintype ι] where
  mat : Matrix ι ι ℂ
  herm : mat.IsHermitian

/-- The spectral norm `‖H‖` of §II.A. -/
def spectralNorm (H : Ham ι) : ℝ := ‖H.mat‖

/-- The induced column-sum norm `‖H‖₁ := max_j ∑_k |H_jk|` of §II.A. -/
def colSumNorm (H : Ham ι) : ℝ := sSup (Set.range fun j : ι => ∑ k, ‖H.mat j k‖)

/-- The max-entry norm `‖H‖_max := max_{j,k} |H_jk|` of §II.A. -/
def maxEntryNorm (H : Ham ι) : ℝ := sSup (Set.range fun p : ι × ι => ‖H.mat p.1 p.2‖)

/-- The sparsity promise of §II.A: at most `D` nonzero entries in each column. -/
def IsColumnSparse (H : Ham ι) (D : ℕ) : Prop :=
  ∀ j : ι, (Finset.univ.filter (fun k : ι => H.mat j k ≠ 0)).card ≤ D

/-- The max-entry norm is nonnegative. -/
theorem maxEntryNorm_nonneg {ι : Type} [Fintype ι] (H : Ham ι) : 0 ≤ maxEntryNorm H := by
  unfold maxEntryNorm
  exact Real.sSup_nonneg (by rintro _ ⟨p, rfl⟩; exact norm_nonneg _)

/-- Every entry is bounded by `‖H‖_max`. -/
theorem norm_entry_le_maxEntryNorm {ι : Type} [Fintype ι] (H : Ham ι) (j k : ι) :
    ‖H.mat j k‖ ≤ maxEntryNorm H := by
  unfold maxEntryNorm
  exact le_csSup (Set.finite_range _).bddAbove ⟨(j, k), rfl⟩

/-! ## 2. The `break` function of Eq. (74)–(75) -/

/-- The band matrix `H^{ab}` of Eq. (75): entries with magnitude in `(a, b]`. -/
def band (H : Ham ι) (a b : ℝ) : Matrix ι ι ℂ :=
  fun j k => if a < ‖H.mat j k‖ ∧ ‖H.mat j k‖ ≤ b then H.mat j k else 0

/-- The finite set of realized magnitudes together with `0`.  The paper's maximum over
all real `a,b` in Eq. (74) only depends on `a,b` through this set. -/
def magThresholds (H : Ham ι) : Finset ℝ :=
  insert 0 (Finset.univ.image fun p : ι × ι => ‖H.mat p.1 p.2‖)

/-- The threshold set is nonempty. -/
theorem magThresholds_nonempty {ι : Type} [Fintype ι] (H : Ham ι) : (magThresholds H).Nonempty :=
  ⟨0, Finset.mem_insert_self 0 _⟩

/-- `break(H)` of Eq. (74): the maximum of `‖H^{ab}‖/‖H‖` over the finite threshold
pairs (the paper maximizes over all real `a,b`; the band only changes at thresholds),
floored at `1` so that the definition is total at `H = 0`. -/
def breakNorm (H : Ham ι) : ℝ :=
  max 1 (if spectralNorm H = 0 then 1 else
    ((magThresholds H).sup' (magThresholds_nonempty H) fun b =>
      (magThresholds H).sup' (magThresholds_nonempty H) fun a => ‖band H a b‖)
      / spectralNorm H)

/-- `break(H) ≥ 1` (§VII.A, immediately after Eq. (75): `break(H) ≥ 1` because the full
band `(0, ‖H‖_max]` is `H` itself and `‖H‖/‖H‖ = 1`; the zero Hamiltonian is floored at
`1` by the definition, which is the natural limit). -/
theorem breakNorm_ge_one (H : Ham ι) : 1 ≤ breakNorm H := le_max_left _ _

/-- Rounding a real threshold down preserves every nonzero matrix entry comparison. -/
private theorem threshold_round {ι : Type} [Fintype ι] (H : Ham ι) (c : ℝ) :
    ∃ d ∈ magThresholds H, ∀ j k, H.mat j k ≠ 0 →
      (‖H.mat j k‖ ≤ d ↔ ‖H.mat j k‖ ≤ c) := by
  let S := (magThresholds H).filter (fun d => d ≤ max 0 c)
  have hn : S.Nonempty := ⟨0, by simp [S, magThresholds]⟩
  refine ⟨S.sup' hn id, ?_, ?_⟩
  · obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup' hn id
    rw [he]
    exact (Finset.mem_filter.mp hd).1
  · intro j k hjk
    have hp : 0 < ‖H.mat j k‖ := norm_pos_iff.mpr hjk
    have hu : S.sup' hn id ≤ max 0 c := by
      exact Finset.sup'_le _ _ (fun d hd => (Finset.mem_filter.mp hd).2)
    constructor
    · intro h
      have : ‖H.mat j k‖ ≤ max 0 c := h.trans hu
      rcases le_max_iff.mp this with h | h
      · exact False.elim ((not_le_of_gt hp) h)
      · exact h
    · intro h
      apply Finset.le_sup' (f := id)
      exact Finset.mem_filter.mpr ⟨by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨(j,k), Finset.mem_univ _, rfl⟩,
        h.trans (le_max_right _ _)⟩

/-- **Every band ratio is bounded by `breakNorm`.**  This is the direction of Eq. (74)
that the paper actually uses: the norm of any single band `H^{ab}` is at most
`break(H) · ‖H‖`.  (For arbitrary `a,b` the band agrees with the band at the
surrounding realized thresholds, which are part of the finite maximum.) -/
theorem band_norm_div_le_breakNorm (H : Ham ι) (a b : ℝ) (hH : 0 < spectralNorm H) :
    ‖band H a b‖ / spectralNorm H ≤ breakNorm H := by
  obtain ⟨a', ha', ha⟩ := threshold_round H a
  obtain ⟨b', hb', hb⟩ := threshold_round H b
  have he : band H a b = band H a' b' := by
    ext j k
    by_cases hz : H.mat j k = 0
    · simp [band, hz]
    · have h1 := ha j k hz
      have h2 := hb j k hz
      simp only [band, ← not_le, h1, h2]
  rw [he]
  have hs : ‖band H a' b'‖ ≤
      (magThresholds H).sup' (magThresholds_nonempty H) (fun d =>
        (magThresholds H).sup' (magThresholds_nonempty H) (fun e => ‖band H e d‖)) := by
    exact le_trans
      (Finset.le_sup' (fun d => ‖band H d b'‖) ha')
      (Finset.le_sup' (fun d => (magThresholds H).sup'
        (magThresholds_nonempty H) (fun e => ‖band H e d‖)) hb')
  unfold breakNorm
  rw [ite_eq_right (ne_of_gt hH)]
  exact (div_le_div_of_nonneg_right hs hH.le).trans (le_max_right _ _)

/-- Squared column Euclidean length is bounded by squared operator norm. -/
private theorem column_sq_le (A : Matrix ι ι ℂ) (j : ι) :
    ∑ i, ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have he : A *ᵥ Pi.single j (1 : ℂ) = fun i => A i j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  simpa [he, EuclideanSpace.norm_sq_eq] using
    (sq_le_sq₀ (by positivity) (by positivity)).2 h

/-- Row sparsity controls the norm of any entrywise restriction. -/
private theorem restriction_norm (H : Ham ι) (D : ℕ) (hsp : IsColumnSparse H D)
    (a b : ℝ) : ‖band H a b‖ ≤ Real.sqrt (D : ℝ) * spectralNorm H := by
  have hH0 : 0 ≤ spectralNorm H := norm_nonneg H.mat
  rw [← Matrix.l2_opNorm_toEuclideanCLM (A := band H a b)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [EuclideanSpace.norm_sq_eq]
  have hrow : ∀ i, ‖(band H a b *ᵥ v) i‖ ^ 2 ≤
      (D : ℝ) * ∑ j, ‖H.mat i j‖ ^ 2 * ‖v j‖ ^ 2 := by
    intro i
    let S := Finset.univ.filter (fun j => H.mat i j ≠ 0)
    have he : (band H a b *ᵥ v) i = ∑ j ∈ S, band H a b i j * v j := by
      simp only [Matrix.mulVec, dotProduct]
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      have hz : H.mat i j = 0 := by simpa [S] using hj
      simp [band, hz]
    have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
      (fun j => ‖band H a b i j * v j‖)
    have hn : ‖∑ j ∈ S, band H a b i j * v j‖ ≤
        ∑ j ∈ S, ‖band H a b i j * v j‖ := norm_sum_le _ _
    rw [he]
    calc
      _ ≤ (∑ j ∈ S, ‖band H a b i j * v j‖) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).2 hn
      _ ≤ (S.card : ℝ) * ∑ j ∈ S, ‖band H a b i j * v j‖ ^ 2 := by
        simpa using hc
      _ ≤ (D : ℝ) * ∑ j, ‖H.mat i j‖ ^ 2 * ‖v j‖ ^ 2 := by
        apply mul_le_mul
        · exact_mod_cast hsp i
        · apply (Finset.sum_le_sum (fun j _ => ?_)).trans
            (Finset.sum_le_univ_sum_of_nonneg (fun j => by positivity))
          by_cases h : a < ‖H.mat i j‖ ∧ ‖H.mat i j‖ ≤ b
          · simp [band, h, mul_pow]
          · simp [band, h]
            positivity
        · positivity
        · positivity
  calc
    ∑ i, ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (band H a b) v i‖ ^ 2
        ≤ ∑ i, (D : ℝ) * ∑ j, ‖H.mat i j‖ ^ 2 * ‖v j‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact hrow i
    _ = (D : ℝ) * ∑ j, (∑ i, ‖H.mat i j‖ ^ 2) * ‖v j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ (D : ℝ) * ∑ j, spectralNorm H ^ 2 * ‖v j‖ ^ 2 := by
      gcongr with j
      exact column_sq_le H.mat j
    _ = (Real.sqrt (D : ℝ) * spectralNorm H * ‖v‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg D),
        EuclideanSpace.norm_sq_eq, Finset.mul_sum, Finset.mul_sum]
      simp only [mul_assoc]

/-- **`break(H) ≤ √D` for a `D`-sparse Hamiltonian** (§VII.A: `‖H^{ab}‖ ≤ ‖H^{ab}‖₁ ≤
‖H‖₁ ≤ √D ‖H‖`). -/
theorem breakNorm_le_sqrt_sparse (H : Ham ι) (D : ℕ) (hsp : IsColumnSparse H D)
    (hD : 0 < D) :
    breakNorm H ≤ Real.sqrt (D : ℝ) := by
  have h1 : 1 ≤ Real.sqrt (D : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg D)).2 (by exact_mod_cast hD)
  unfold breakNorm
  apply max_le h1
  split_ifs with hz
  · exact h1
  · apply (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg H.mat) (Ne.symm hz))).2
    apply Finset.sup'_le
    intro b _
    apply Finset.sup'_le
    intro a _
    exact restriction_norm H D hsp a b

/-! ## 3. Time evolution `e^{-iHt}` and its bridge to the Dyson propagator -/

/-- Real scalar multiplication on complex matrices agrees with multiplication by the
coerced complex scalar. -/
theorem real_smul_eq_complex_smul {ι : Type} (r : ℝ) (A : Matrix ι ι ℂ) :
    r • A = (r : ℂ) • A := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- The evolution `e^{-iHt}` under the Hamiltonian `H` (paper §III, Eq. (9)–(22)). -/
def evolution (H : Ham ι) (t : ℝ) : Matrix ι ι ℂ := HamiltonianEvolution H.mat t

/-- The paper's evolution is the matrix exponential of `-i t H`. -/
theorem evolution_def (H : Ham ι) (t : ℝ) :
    evolution H t = NormedSpace.exp ((-Complex.I * (t : ℂ)) • H.mat) := rfl

/-- **Bridge to the Foundations Dyson propagator.**  The library's
`ContractiveDuhamel.evolution A t = exp(-t • A)` is the same operator as `e^{-iHt}`
with generator `A = i H`.  This connects the paper's evolution to the bound
`TimeEvolution.DysonPropagator` unit. -/
theorem evolution_eq_dysonPropagator (H : Ham ι) (t : ℝ) :
    evolution H t =
      Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
        (Complex.I • H.mat) t := by
  simp [evolution, HamiltonianEvolution,
    Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution,
    real_smul_eq_complex_smul, smul_smul, mul_comm]

/-- Time evolution is unitary (reuse of `hamiltonianEvolution_unitary`). -/
theorem evolution_mem_unitaryGroup (H : Ham ι) (t : ℝ) :
    evolution H t ∈ Matrix.unitaryGroup ι ℂ :=
  hamiltonianEvolution_unitary H.herm t

/-- Evolution at time zero is the identity. -/
@[simp] theorem evolution_zero (H : Ham ι) : evolution H 0 = 1 :=
  hamiltonianEvolution_zero H.mat

/-- The evolution group law `e^{-iH(s+t)} = e^{-iHs} e^{-iHt}`. -/
theorem evolution_add (H : Ham ι) (s t : ℝ) :
    evolution H (s + t) = evolution H s * evolution H t :=
  hamiltonianEvolution_add H.mat s t

/-! ## 4. The oracle register and the value oracle of Eq. (1) -/

/-- The oracle register of §II.A: row index, column index, and an `L`-bit value
register `z` (`Reg L` is the library's `Fin L → Bool`). -/
abbrev Register (ι : Type) (L : ℕ) := ι × ι × Reg L

/-- Pointwise XOR of bit registers — the `⊕` of Eq. (1). -/
def regXor (z φ : Reg L) : Reg L := fun i => Bool.xor (z i) (φ i)

/-- The permutation underlying the value oracle: XOR the encoded entry of `(j,k)` into
the value register. -/
def oraclePerm (φ : ι × ι → Reg L) (p : Register ι L) : Register ι L :=
  (p.1, p.2.1, regXor p.2.2 (φ (p.1, p.2.1)))

/-- XOR is an involution: applying the same value twice is the identity. -/
@[simp] theorem regXor_regXor (z φ : Reg L) : regXor (regXor z φ) φ = z := by
  funext i
  cases hz : z i <;> cases hφ : φ i <;> simp [regXor, hz, hφ]

/-- The encoded matrix-element oracle `O_H` of Eq. (1):
`O_H |j,k⟩|z⟩ = |j,k⟩|z ⊕ φ(j,k)⟩`.  `φ` is the binary encoding of the matrix
elements (the paper represents real and imaginary parts in binary). -/
def valueOracle (φ : ι × ι → Reg L) : Matrix (Register ι L) (Register ι L) ℂ :=
  fun p q => if q = oraclePerm φ p then 1 else 0

/-- The XOR permutation is an involution. -/
@[simp] theorem oraclePerm_involutive {ι : Type} (φ : ι × ι → Reg L) (p : Register ι L) :
    oraclePerm φ (oraclePerm φ p) = p := by
  simp [oraclePerm, regXor_regXor]

/-- The value register action of `valueOracle`. -/
theorem valueOracle_apply {ι : Type} [DecidableEq ι] (φ : ι × ι → Reg L) (j k : ι) (z : Reg L) :
    valueOracle φ (j, k, z) =
      Qatlib.Foundations.PureStateMath.Ket (j, k, regXor z (φ (j, k))) := by
  funext q
  unfold valueOracle oraclePerm
  by_cases h : q = (j, k, regXor z (φ (j, k)))
  · subst h
    simp [Qatlib.Foundations.PureStateMath.Ket]
  · simp [h, Qatlib.Foundations.PureStateMath.Ket]

/-- **The value oracle is its own inverse** (XOR is an involution). -/
theorem valueOracle_mul_self (φ : ι × ι → Reg L) :
    valueOracle φ * valueOracle φ = 1 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (oraclePerm φ p)]
  · have h1 : valueOracle φ p (oraclePerm φ p) = 1 := by
      show (if oraclePerm φ p = oraclePerm φ p then (1 : ℂ) else 0) = 1
      rw [ite_eq_left rfl]
    have h2 : valueOracle φ (oraclePerm φ p) q = (if q = p then 1 else 0) := by
      show (if q = oraclePerm φ (oraclePerm φ p) then (1 : ℂ) else 0) = _
      rw [oraclePerm_involutive]
    rw [h1, one_mul, h2]
    by_cases h : q = p
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (fun hpq => h hpq.symm)]
  · intro r _ hr
    have hpr : valueOracle φ p r = 0 := by
      show (if r = oraclePerm φ p then (1 : ℂ) else 0) = 0
      rw [ite_eq_right hr]
    rw [hpr, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype ι] in
/-- The value oracle is real, hence symmetric. -/
theorem valueOracle_transpose (φ : ι × ι → Reg L) :
    (valueOracle φ)ᵀ = valueOracle φ := by
  ext p q
  rw [Matrix.transpose_apply]
  by_cases hq : p = oraclePerm φ q
  · have hq' : q = oraclePerm φ p := by rw [hq, oraclePerm_involutive]
    show (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [ite_eq_left hq, ite_eq_left hq']
  · have hq' : q ≠ oraclePerm φ p := by
      intro h
      exact hq (by rw [h]; exact (oraclePerm_involutive φ p).symm)
    show (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [ite_eq_right hq, ite_eq_right hq']

omit [Fintype ι] in
/-- The value oracle is fixed by `star` (all its entries are real `0`/`1`). -/
theorem valueOracle_star (φ : ι × ι → Reg L) :
    star (valueOracle φ) = valueOracle φ := by
  ext p q
  rw [Matrix.star_apply]
  by_cases hq : p = oraclePerm φ q
  · have hq' : q = oraclePerm φ p := by rw [hq, oraclePerm_involutive]
    show star (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [ite_eq_left hq, ite_eq_left hq']
    simp
  · have hq' : q ≠ oraclePerm φ p := by
      intro h
      exact hq (by rw [h]; exact (oraclePerm_involutive φ p).symm)
    show star (if p = oraclePerm φ q then (1 : ℂ) else 0) =
      (if q = oraclePerm φ p then (1 : ℂ) else 0)
    rw [ite_eq_right hq, ite_eq_right hq']
    simp

/-- **The value oracle is unitary.** -/
theorem valueOracle_mem_unitaryGroup (φ : ι × ι → Reg L) :
    valueOracle φ ∈ Matrix.unitaryGroup (Register ι L) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [valueOracle_star]
  exact valueOracle_mul_self φ

/-! ## 5. Black-box model and counted two-oracle circuits -/

variable {D : ℕ}

/-- The black-box data of §II.A: a Hamiltonian `H`, its matrix-element oracle `O_H`
(a genuine Eq. (1) value oracle with decoder `dec`), and the position oracle `O_F`
(a unitary on the same register, §II.A Eq. (3)). -/
structure BlackBox (ι : Type) [Fintype ι] [DecidableEq ι] (D L : ℕ) where
  H : Ham ι
  OH : Matrix (Register ι L) (Register ι L) ℂ
  OF : Matrix (Register ι L) (Register ι L) ℂ
  OH_mem : OH ∈ Matrix.unitaryGroup (Register ι L) ℂ
  OF_mem : OF ∈ Matrix.unitaryGroup (Register ι L) ℂ
  /-- `O_H` is the Eq. (1) oracle of the encoded matrix elements of `H`. -/
  value_encoding : ∃ (φ : ι × ι → Reg L) (dec : Reg L → ℂ),
    (∀ j k, dec (φ (j, k)) = H.mat j k) ∧ OH = valueOracle φ

/-- A step of a counted circuit with two oracles: a fixed gate, a query to `O_H`, or a
query to `O_F` (§II.A). -/
inductive Step2 (ι : Type) (L : ℕ) where
  | gate : Matrix (Register ι L) (Register ι L) ℂ → Step2 ι L
  | queryH : Step2 ι L
  | queryF : Step2 ι L

/-- A counted two-oracle circuit, executed left to right. -/
abbrev Circuit2 (ι : Type) (L : ℕ) := List (Step2 ι L)

/-- The query count: **total** calls to `O_H` and `O_F` (the paper counts both). -/
def QueryCount2 : Circuit2 ι L → ℕ
  | [] => 0
  | Step2.gate _ :: C => QueryCount2 C
  | Step2.queryH :: C => QueryCount2 C + 1
  | Step2.queryF :: C => QueryCount2 C + 1

/-- Execution of a two-oracle circuit. -/
def Run2 (OH OF : Matrix (Register ι L) (Register ι L) ℂ) :
    Circuit2 ι L → QState (Register ι L) → QState (Register ι L)
  | [], ψ => ψ
  | Step2.gate U :: C, ψ => Run2 OH OF C (ApplyGate U ψ)
  | Step2.queryH :: C, ψ => Run2 OH OF C (ApplyGate OH ψ)
  | Step2.queryF :: C, ψ => Run2 OH OF C (ApplyGate OF ψ)

/-- Fixed-gate unitarity of a two-oracle circuit. -/
def IsUnitaryCircuit2 : Circuit2 ι L → Prop
  | [] => True
  | Step2.gate U :: C => U ∈ Matrix.unitaryGroup (Register ι L) ℂ ∧ IsUnitaryCircuit2 C
  | Step2.queryH :: C => IsUnitaryCircuit2 C
  | Step2.queryF :: C => IsUnitaryCircuit2 C

/-- The empty circuit has no queries. -/
@[simp] theorem queryCount2_nil {ι : Type} : QueryCount2 ([] : Circuit2 ι L) = 0 := rfl

/-- A fixed gate is free. -/
@[simp] theorem queryCount2_gate {ι : Type} (U : Matrix (Register ι L) (Register ι L) ℂ) (C : Circuit2 ι L) :
    QueryCount2 (Step2.gate U :: C) = QueryCount2 C := rfl

/-- An `O_H` query costs one. -/
@[simp] theorem queryCount2_queryH {ι : Type} (C : Circuit2 ι L) :
    QueryCount2 (Step2.queryH :: C) = QueryCount2 C + 1 := rfl

/-- An `O_F` query costs one. -/
@[simp] theorem queryCount2_queryF {ι : Type} (C : Circuit2 ι L) :
    QueryCount2 (Step2.queryF :: C) = QueryCount2 C + 1 := rfl

/-- Query counts are additive under concatenation. -/
theorem queryCount2_append {ι : Type} (C D : Circuit2 ι L) :
    QueryCount2 (C ++ D) = QueryCount2 C + QueryCount2 D := by
  induction C with
  | nil => simp
  | cons s C ih => cases s <;> simp [QueryCount2, ih] <;> omega

/-- `k`-fold repetition of a circuit block. -/
def RepeatCircuit2 (C : Circuit2 ι L) : ℕ → Circuit2 ι L
  | 0 => []
  | k + 1 => C ++ RepeatCircuit2 C k

omit [Fintype ι] [DecidableEq ι] in
/-- **Repeating a block `k` times costs `k · (queries per block)`** — the counting
identity behind every walk-step bound (reuses the library's `queryCount_repeatCircuit`
pattern). -/
theorem queryCount2_repeatCircuit (C : Circuit2 ι L) (k : ℕ) :
    QueryCount2 (RepeatCircuit2 C k) = k * QueryCount2 C := by
  induction k with
  | zero => simp [RepeatCircuit2]
  | succ k ih => rw [RepeatCircuit2, queryCount2_append, ih, Nat.succ_mul]; omega

/-- Unitarity is stable under concatenation. -/
theorem isUnitaryCircuit2_append (C D : Circuit2 ι L) :
    IsUnitaryCircuit2 (C ++ D) ↔ IsUnitaryCircuit2 C ∧ IsUnitaryCircuit2 D := by
  induction C with
  | nil => simp [IsUnitaryCircuit2]
  | cons s C ih => cases s <;> simp [IsUnitaryCircuit2, ih, and_assoc]

/-- Repeating a valid block preserves validity. -/
theorem isUnitaryCircuit2_repeatCircuit {C : Circuit2 ι L} (hC : IsUnitaryCircuit2 C)
    (k : ℕ) : IsUnitaryCircuit2 (RepeatCircuit2 C k) := by
  induction k with
  | zero => simp [RepeatCircuit2, IsUnitaryCircuit2]
  | succ k ih => rw [RepeatCircuit2, isUnitaryCircuit2_append]; exact ⟨hC, ih⟩

/-! ## 6. The paper's task predicate: simulation within a query budget -/

variable [Inhabited ι]

/-- The computational input state: amplitude `ψ` on the row register, with the column
index and the value register initialized to `(default, 0)`. -/
def inputState (ψ : ι → ℂ) : QState (Register ι L) :=
  fun p => if p.2.1 = default ∧ p.2.2 = ZeroStr L then ψ p.1 else 0

/-- Read-out of the row register at `(default, 0)`. -/
def readout (ρ : QState (Register ι L)) (j : ι) : ℂ := ρ (j, default, ZeroStr L)

/-- The operator implemented by a two-oracle circuit: run it on every basis input and
read out the row register. -/
def implementedMap (BB : BlackBox ι D L) (C : Circuit2 ι L) : Matrix ι ι ℂ :=
  fun j i => readout (Run2 BB.OH BB.OF C (inputState (Qatlib.Foundations.PureStateMath.Ket i))) j

/-- The error of a simulated operator against the exact evolution, measured in trace
distance: `½ ‖K − e^{-iHt}‖₁` (paper §II.A: the error is the trace distance). -/
def simulationError (K E : Matrix ι ι ℂ) : ℝ := (1 / 2) * Matrix.traceNorm (K - E)

/-- **`SimulableWithin BB t δ q`**: there is a counted oracle circuit that implements a
unitary within trace distance `δ` of `e^{-iHt}` and makes at most `q` queries to
`O_H`/`O_F` in total.  This is the paper's task statement of §II.B. -/
def SimulableWithin (BB : BlackBox ι D L) (t δ q : ℝ) : Prop :=
  ∃ C : Circuit2 ι L,
    IsUnitaryCircuit2 C ∧
    implementedMap BB C ∈ Matrix.unitaryGroup ι ℂ ∧
    (QueryCount2 C : ℝ) ≤ q ∧
    simulationError (implementedMap BB C) (evolution BB.H t) ≤ δ

/-! ## 6b. Walk-state preparation, perturbation sandwich, and unitary encoding -/

/-- The row-sum `σ_j = ∑_k |H_jk|` of Eq. (12). -/
def sigmaRow (H : Ham ι) (j : ι) : ℝ := ∑ k, ‖H.mat j k‖

/-- The largest absolute diagonal perturbation `x_max = max_j |x_j|` of Eq. (64). -/
def maxAbs (x : ι → ℝ) : ℝ := sSup (Set.range fun j : ι => |x j|)

/-- The diagonal matrix `x = diag(x_1,…,x_M)` of Eq. (60). -/
def diagMatrix (x : ι → ℝ) : Matrix ι ι ℂ := fun j k => if j = k then (x j : ℂ) else 0

/-- The supremum of the absolute coordinates is nonnegative. -/
private theorem maxAbs_nonneg {ι : Type} (x : ι → ℝ) : 0 ≤ maxAbs x :=
  Real.sSup_nonneg (by rintro _ ⟨j, rfl⟩; exact abs_nonneg _)

/-- The diagonal operator norm is the maximum absolute coordinate. -/
private theorem diagMatrix_norm (x : ι → ℝ) : ‖diagMatrix x‖ = maxAbs x := by
  have hd : diagMatrix x = Matrix.diagonal (fun j => (x j : ℂ)) := by
    ext i j
    simp only [diagMatrix, Matrix.diagonal_apply]
  rw [hd, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (maxAbs_nonneg x)).2
    intro j
    simpa [maxAbs] using (le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩ :
      |x j| ≤ maxAbs x)
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro _ ⟨j, rfl⟩
      simpa using norm_le_pi_norm (fun j => (x j : ℂ)) j

/-- The perturbed Hamiltonian `xH + Hx + xHx` of Eq. (63). -/
def sandwich (H : Ham ι) (x : ι → ℝ) : Matrix ι ι ℂ :=
  diagMatrix x * H.mat + H.mat * diagMatrix x + diagMatrix x * H.mat * diagMatrix x

/-- **The sandwich norm bound of Lemma 7, Eq. (63)–(64).**
For `ε ≥ 0` and `Λ₁ > 0`,
`‖(ε/Λ₁)(xH + Hx + xHx)‖ ≤ (ε‖H‖/Λ₁)(2x_max + x_max²)`. -/
theorem sandwich_norm_le (H : Ham ι) (x : ι → ℝ) (ε Λ1 : ℝ) (hΛ1 : 0 < Λ1) (hε : 0 ≤ ε) :
    ‖(ε / Λ1) • sandwich H x‖ ≤
      (ε * spectralNorm H / Λ1) * (2 * maxAbs x + (maxAbs x) ^ 2) := by
  have hm : 0 ≤ maxAbs x := maxAbs_nonneg x
  have hH : 0 ≤ spectralNorm H := norm_nonneg _
  have h1 : ‖diagMatrix x * H.mat‖ ≤ maxAbs x * spectralNorm H := by
    calc ‖diagMatrix x * H.mat‖ ≤ ‖diagMatrix x‖ * ‖H.mat‖ := Matrix.l2_opNorm_mul _ _
      _ = maxAbs x * spectralNorm H := by rw [diagMatrix_norm, spectralNorm]
  have h2 : ‖H.mat * diagMatrix x‖ ≤ maxAbs x * spectralNorm H := by
    calc ‖H.mat * diagMatrix x‖ ≤ ‖H.mat‖ * ‖diagMatrix x‖ := Matrix.l2_opNorm_mul _ _
      _ = maxAbs x * spectralNorm H := by rw [diagMatrix_norm, spectralNorm]; ring
  have h3 : ‖diagMatrix x * H.mat * diagMatrix x‖ ≤ maxAbs x ^ 2 * spectralNorm H := by
    calc ‖diagMatrix x * H.mat * diagMatrix x‖
        ≤ ‖diagMatrix x * H.mat‖ * ‖diagMatrix x‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (maxAbs x * spectralNorm H) * maxAbs x :=
          mul_le_mul h1 (le_of_eq (diagMatrix_norm x)) (norm_nonneg _) (mul_nonneg hm hH)
      _ = maxAbs x ^ 2 * spectralNorm H := by ring
  have hsum : ‖sandwich H x‖ ≤ (2 * maxAbs x + maxAbs x ^ 2) * spectralNorm H := by
    calc ‖sandwich H x‖
        = ‖diagMatrix x * H.mat + H.mat * diagMatrix x +
            diagMatrix x * H.mat * diagMatrix x‖ := rfl
      _ ≤ ‖diagMatrix x * H.mat + H.mat * diagMatrix x‖ +
            ‖diagMatrix x * H.mat * diagMatrix x‖ := norm_add_le _ _
      _ ≤ (‖diagMatrix x * H.mat‖ + ‖H.mat * diagMatrix x‖) +
            ‖diagMatrix x * H.mat * diagMatrix x‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ (2 * maxAbs x + maxAbs x ^ 2) * spectralNorm H := by
            nlinarith [h1, h2, h3]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ε / Λ1)]
  have heq : (ε / Λ1) * ((2 * maxAbs x + maxAbs x ^ 2) * spectralNorm H)
      = (ε * spectralNorm H / Λ1) * (2 * maxAbs x + maxAbs x ^ 2) := by ring
  rw [← heq]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **Lemma 7, amplified over time `t`.**  Evolving for time `t` multiplies the
perturbation by `tΛ₁/ε` for `t ≥ 0` (after Eq. (64)), so a relative weight error
`x_max ≤ ε ≤ 1` produces a simulation error `≤ 3‖H‖tε = O(‖H‖tε)`.
No upper bound on `‖H‖` by `Λ₁` is needed: the positive scale `Λ₁` cancels. -/
theorem lemma7_error_amplification (H : Ham ι) (x : ι → ℝ) (ε Λ1 t : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : maxAbs x ≤ ε) (hΛ1 : 0 < Λ1)
    (ht : 0 ≤ t) :
    (t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖ ≤ 3 * spectralNorm H * t * ε := by
  have hb := sandwich_norm_le H x ε Λ1 hΛ1 (le_of_lt hε)
  have hstep : (t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖ ≤
      (t * Λ1 / ε) * ((ε * spectralNorm H / Λ1) *
        (2 * maxAbs x + (maxAbs x) ^ 2)) := by
    gcongr
  have hm : 0 ≤ maxAbs x := maxAbs_nonneg x
  have hH0 : 0 ≤ spectralNorm H := norm_nonneg _
  have hsimp : (t * Λ1 / ε) * ((ε * spectralNorm H / Λ1) *
        (2 * maxAbs x + (maxAbs x) ^ 2))
      = t * spectralNorm H * (2 * maxAbs x + (maxAbs x) ^ 2) := by
    field_simp
  rw [hsimp] at hstep
  have hkey : 2 * maxAbs x + (maxAbs x) ^ 2 ≤ 3 * ε := by nlinarith
  have hc : 0 ≤ t * spectralNorm H := mul_nonneg ht hH0
  calc (t * Λ1 / ε) * ‖(ε / Λ1) • sandwich H x‖
      ≤ t * spectralNorm H * (2 * maxAbs x + (maxAbs x) ^ 2) := hstep
    _ ≤ t * spectralNorm H * (3 * ε) := by gcongr
    _ = 3 * spectralNorm H * t * ε := by ring

/-- The target walk state `|φ_j⟩` of Eq. (25).  The first term is the paper's
`√(ε/Λ₁) ∑_k H*_{jk}|k⟩|0⟩`; the flagged `|ζ_j⟩|1⟩` component is supplied by `ζ` and
encoded into the value register being non-zero (so the two components are orthogonal,
as in the paper's ancilla flag). -/
def walkTarget (H : Ham ι) (Λ1 ε : ℝ) (ζ : ι → QState (Register ι L)) (j : ι) :
    QState (Register ι L) :=
  fun p =>
    (if p.2.1 = default ∧ p.2.2 = ZeroStr L then
        (Real.sqrt (ε / Λ1) : ℂ) * star (H.mat j p.1) else 0) +
      (if p.2.2 = ZeroStr L then 0 else
        (Real.sqrt (1 - ε * sigmaRow H j / Λ1) : ℂ) * ζ j p)

/-- `|φ_j⟩` can be prepared from `|j⟩|0…0⟩` up to a global phase using a circuit with
at most `q` oracle queries.  This is the state-preparation task of Lemma 4 (Eq. (25)). -/
def PreparesWalkStateWithin (BB : BlackBox ι D L) (Λ1 ε q : ℝ) : Prop :=
  ∃ C : Circuit2 ι L,
    IsUnitaryCircuit2 C ∧ (QueryCount2 C : ℝ) ≤ q ∧
    ∀ j : ι, ∃ ζ : ι → QState (Register ι L), ∃ θ : ℝ,
      Run2 BB.OH BB.OF C (inputState (Qatlib.Foundations.PureStateMath.Ket j)) =
        Complex.exp (θ * Complex.I) • walkTarget BB.H Λ1 ε ζ j

/-- The first-term amplitude `√(ε/Λ₁) H*_{jk}` of Eq. (25). -/
def firstTermAmp (H : Ham ι) (Λ1 ε : ℝ) (j k : ι) : ℂ :=
  (Real.sqrt (ε / Λ1) : ℂ) * star (H.mat j k)

/-- `|φ_j⟩` can be prepared with **relative error `ε` in the first-term weights**
(Lemma 6, Eq. (43)) using at most `q` oracle queries. -/
def PreparesWalkStateApproxWithin (BB : BlackBox ι D L) (Λ1 ε q : ℝ) : Prop :=
  ∃ C : Circuit2 ι L,
    IsUnitaryCircuit2 C ∧ (QueryCount2 C : ℝ) ≤ q ∧
    ∀ j : ι, ∃ ρ : QState (Register ι L),
      Run2 BB.OH BB.OF C (inputState (Qatlib.Foundations.PureStateMath.Ket j)) = ρ ∧
      ∀ k : ι, ‖ρ (k, default, ZeroStr L) - firstTermAmp BB.H Λ1 ε j k‖ ≤
        ε * ‖firstTermAmp BB.H Λ1 ε j k‖

/-- Lemma 6 query expression, Eq. (43)–(44): `O(√(ε Λ_max D/Λ₁) + 1)`. -/
def lemma6QueryExpr (Λ1 ε : ℝ) (D : ℕ) (Λmax : ℝ) : ℝ :=
  Real.sqrt (ε * Λmax * (D : ℝ) / Λ1) + 1

/-- The max-entry bound `‖U‖_max` for an `N × N` unitary. -/
def unitaryMaxEntry {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sSup (Set.range fun p : Fin N × Fin N => ‖U p.1 p.2‖)

/-- The column-sum norm `‖U‖₁` of a matrix. -/
def unitaryColSum {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sSup (Set.range fun j : Fin N => ∑ k, ‖U j k‖)

/-- `Λ₁ ≥ max{‖U‖₁, ‖U†‖₁}` (Corollary 12). -/
def unitaryColSumBound {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (Λ1 : ℝ) : Prop :=
  unitaryColSum U ≤ Λ1 ∧ unitaryColSum (Matrix.conjTranspose U) ≤ Λ1

/-- **Block encoding of Eq. (123).**  The black-box Hamiltonian `H = [[0,U],[U†,0]]`
on `Bool × Fin N` encodes the `N × N` unitary `U`. -/
def BlockEncodes {N : ℕ} (BB : BlackBox (Bool × Fin N) N L)
    (U : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ j : Fin N, BB.H.mat (false, j) (false, j) = 0 ∧ BB.H.mat (true, j) (true, j) = 0) ∧
  (∀ j k : Fin N, BB.H.mat (false, j) (true, k) = U j k) ∧
  (∀ j k : Fin N, BB.H.mat (true, j) (false, k) = star (U k j))

/-- **Unitary implementation within error `δ` and `q` queries** (Sec. VIII):
there is a black box whose Hamiltonian is the block encoding of `U`, and a counted
circuit that simulates it for time `π/2` within trace distance `δ`, using `q` queries.
Simulating the block Hamiltonian for `π/2` implements `U` (Eq. (127)–(128)). -/
def UnitaryImplementsWithin {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hN : 0 < N)
    (δ q : ℝ) : Prop :=
  letI : Inhabited (Fin N) := ⟨⟨0, hN⟩⟩
  ∃ (L : ℕ), ∃ BB : BlackBox (Bool × Fin N) N L,
    BlockEncodes BB U ∧ SimulableWithin BB (Real.pi / 2) δ q

/-- As `UnitaryImplementsWithin`, additionally requiring `break(H) ≤ Υ` (Theorem 9 /
Corollary 13). -/
def UnitaryImplementsWithBreakWithin {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hN : 0 < N)
    (Υ δ q : ℝ) : Prop :=
  letI : Inhabited (Fin N) := ⟨⟨0, hN⟩⟩
  ∃ (L : ℕ), ∃ BB : BlackBox (Bool × Fin N) N L,
    BlockEncodes BB U ∧ breakNorm BB.H ≤ Υ ∧ SimulableWithin BB (Real.pi / 2) δ q

/-! ## 7. Closed-form query cost expressions of §II.B, §VI, §VII, §VIII -/

/-- `log log D`, the paper's double logarithm. -/
def loglog (D : ℕ) : ℝ := Real.log (Real.log (D : ℝ))

/-- `log log D` floored at `1`: for `D ≤ e` the paper's `O(·)` convention absorbs the
constant, so the floored form is the honest `O(1)`-equivalent expression. -/
def loglogSafe (D : ℕ) : ℝ := max 1 (loglog D)

/-- `log D` floored at `1` (same `O(1)` convention). -/
def logSafe (D : ℕ) : ℝ := max 1 (Real.log (D : ℝ))

/-- Theorem 1, Eq. (4): `Λt/√δ + D Λ_max t + 1`. -/
def theorem1QueryExpr (Λ : ℝ) (D : ℕ) (Λmax t δ : ℝ) : ℝ :=
  Λ * t / Real.sqrt δ + (D : ℝ) * Λmax * t + 1

/-- Theorem 2, Eq. (5): `D^{2/3} [(log log D) Λt]^{4/3} δ^{-1/3}`. -/
def theorem2QueryExpr (Λ : ℝ) (D : ℕ) (t δ : ℝ) : ℝ :=
  Real.rpow (D : ℝ) (2 / 3) * Real.rpow (loglogSafe D * Λ * t) (4 / 3) *
    Real.rpow δ (-(1 / 3))

/-- Lemma 8, Eq. (65): `t^{3/2} √(Λ_max D Λ₁ Λ / δ)`. -/
def lemma8QueryExpr (Λ Λ1 Λmax : ℝ) (D : ℕ) (t δ : ℝ) : ℝ :=
  Real.rpow t (3 / 2) * Real.sqrt (Λmax * (D : ℝ) * Λ1 * Λ / δ)

/-- Theorem 9, Eq. (76): `√(ΥD/δ) (log D)^{7/4} (Λt)^{3/2}`. -/
def theorem9QueryExpr (Λ Υ : ℝ) (D : ℕ) (t δ : ℝ) : ℝ :=
  Real.sqrt (Υ * (D : ℝ) / δ) * Real.rpow (logSafe D) (7 / 4) *
    Real.rpow (Λ * t) (3 / 2)

/-- Corollary 3, Eq. (6): `N^{2/3} (log log N)^{4/3} δ^{-1/3}`. -/
def corollary3QueryExpr (N : ℕ) (δ : ℝ) : ℝ :=
  Real.rpow (N : ℝ) (2 / 3) * Real.rpow (loglogSafe N) (4 / 3) *
    Real.rpow δ (-(1 / 3))

/-- Corollary 12, Eq. (132): `√(Λ_max N Λ₁ / δ)`. -/
def corollary12QueryExpr (N : ℕ) (Λ1 Λmax δ : ℝ) : ℝ :=
  Real.sqrt (Λmax * (N : ℝ) * Λ1 / δ)

/-- Corollary 13, Eq. (133): `√(ΥN/δ) (log N)^{7/4}`. -/
def corollary13QueryExpr (N : ℕ) (Υ δ : ℝ) : ℝ :=
  Real.sqrt (Υ * (N : ℝ) / δ) * Real.rpow (logSafe N) (7 / 4)

end Qatlib.Papers.BlackBoxHam09.MainResults.Model
