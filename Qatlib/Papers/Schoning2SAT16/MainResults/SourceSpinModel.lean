/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.Schoning2SAT16.MainResults

noncomputable section

open Matrix BigOperators ComplexOrder

/-!
# Spin model for arXiv:1603.06985v1

Fixed version: **arXiv:1603.06985v1** (E. Farhi, S. Kimmel, K. Temme, 22 Mar 2016,
MIT-CTP/4789).  All section/equation references below are to that version.

This file builds the concrete `n`-qubit operator model used by every active claim of
`Schoning2SAT16`:

* `hz`, `sigmaZAt` — the single-qubit `σ^z` and its action on qubit `i`;
* `totalSpin`, `totalSpinSq` — the operator `Ŝ = Σ_i σ^z_i` and `Ŝ²` of Eq. (10);
* `restrictedAmp`, `clauseProj` — the restricted clause projector `Φ_α = |φ_α⟩⟨φ_α|`
  with `|φ_α⟩ = a_α |01⟩_{i,j} + b_α |10⟩_{i,j}` of Eq. (5);
* `qubitTwirl` — the unitary twirl `Λ_i` of Eq. (7), `Λ_i(X) = (I_i/2) ⊗ tr_i(X)`;
* `stepMapOf`, `stepMap` — one step `T_α` of Eq. (6) and its clause-specialisation;
* `hamiltonian`, `familyChannel`, `chanPower`, `maximallyMixed` — `H = Σ_α Φ_α`,
  `T = (1/L) Σ_α T_α` (Eq. (8)), its `T`-fold iterate and the algorithm's initial state;
* the instance predicates `IsYesInstance` / `IsNoInstance` used by Results 1 and 2;
* probability helpers `outcomeProb`, `zeroCount` for the measurement-outcome law.

The operator identities Eq. (16) and Eq. (22),
`Φ_α (σ^z_i + σ^z_j) = (σ^z_i + σ^z_j) Φ_α = 0` and `Φ_α σ^z_i σ^z_j = σ^z_i σ^z_j Φ_α = -Φ_α`,
are proved below (`clauseProj_mul_signsum`, `signsum_mul_clauseProj`,
`clauseProj_mul_pair`, `pair_mul_clauseProj`); they are the algebraic core of Lemma 1.
-/

/-- Bit-string index of an `n`-qubit computational basis state. -/
abbrev QIdx (n : ℕ) := Fin n → Fin 2

/-- An `n`-qubit operator. -/
abbrev NOp (n : ℕ) := Matrix (QIdx n) (QIdx n) ℂ

/-- The `z`-axis eigenvalue of a computational-basis bit: `hz 0 = 1`, `hz 1 = -1`. -/
def hz (b : Fin 2) : ℂ := if b = 0 then 1 else -1

/-- `σ^z_i` on `n` qubits: diagonal in the computational basis with eigenvalue `hz (s i)`. -/
def sigmaZAt {n : ℕ} (i : Fin n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun s t => if s = t then hz (s i) else 0

/-- The total spin `Ŝ = Σ_i σ^z_i`, Eq. (10) of arXiv:1603.06985v1. -/
def totalSpin (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ i : Fin n, sigmaZAt i

/-- `Ŝ²`, Eq. (10). -/
def totalSpinSq (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  totalSpin n * totalSpin n

/-- The hz zero property in the paper model. -/
@[simp] theorem hz_zero : hz 0 = 1 := by simp [hz]
/-- The hz one property in the paper model. -/
@[simp] theorem hz_one : hz 1 = -1 := by simp [hz]

/-- On unequal bits the product of `z`-eigenvalues is `-1`. -/
theorem hz_mul_hz_neg {p q : Fin 2} (h : p ≠ q) : hz p * hz q = -1 := by
  fin_cases p <;> fin_cases q <;> simp_all

/-- `hz` distinguishes the two bits. -/
theorem hz_add_hz {p q : Fin 2} (h : p ≠ q) : hz p + hz q = 0 := by
  fin_cases p <;> fin_cases q <;> simp_all

/-! ## Restricted clause projectors (Eq. (5)) -/

/-- The two-qubit restricted-clause amplitude `a |01⟩ + b |10⟩`. -/
def restrictedAmp (a b : ℂ) (p q : Fin 2) : ℂ :=
  if p = 0 ∧ q = 1 then a else if p = 1 ∧ q = 0 then b else 0

/-- The restricted two-qubit projector `|φ⟩⟨φ|`, `|φ⟩ = a|01⟩ + b|10⟩` (Eq. (5)). -/
def clauseMat2 (a b : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => restrictedAmp a b x.1 x.2 * starRingEnd ℂ (restrictedAmp a b y.1 y.2)

/-- The restricted clause projector `Φ_α = |φ_α⟩⟨φ_α| ⊗ I` on `n` qubits, supported on
qubits `i, j` (Eq. (5)).  The guard `hij : i ≠ j` records that a clause has two-qubit
support. -/
def clauseProj {n : ℕ} (a b : ℂ) (i j : Fin n) (hij : i ≠ j) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun s t => if (∀ k, k ≠ i → k ≠ j → s k = t k) then
      restrictedAmp a b (s i) (s j) * starRingEnd ℂ (restrictedAmp a b (t i) (t j))
    else 0

/-- The Type II clause projector `Φ_α = |11⟩⟨11|` on qubits `i, j` (Appendix A, Eq. (A2)). -/
def typeIIProjector {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun s t => if (∀ k, k ≠ i → k ≠ j → s k = t k) ∧ s i = 1 ∧ s j = 1 ∧
      t i = 1 ∧ t j = 1 then 1 else 0

/-- The qubit twirl `Λ_i` of Eq. (7), `Λ_i(X) = (I_i/2) ⊗ tr_i(X)`. -/
def qubitTwirl {n : ℕ} (i : Fin n) (X : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun s t => if s i = t i then (1 / 2 : ℂ) * ∑ u : Fin 2,
      X (Function.update s i u) (Function.update t i u) else 0

/-- One step of the quantum Markov process with a fixed clause projector, Eq. (6):
`T_α(ρ) = (1−Φ) ρ (1−Φ) + ½ Λ_i(Φ ρ Φ) + ½ Λ_j(Φ ρ Φ)`. -/
def stepMapOf {n : ℕ} (Φ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (i j : Fin n)
    (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (1 - Φ) * ρ * (1 - Φ)
    + (1 / 2 : ℂ) • qubitTwirl i (Φ * ρ * Φ)
    + (1 / 2 : ℂ) • qubitTwirl j (Φ * ρ * Φ)

/-- The restricted-clause step `T_α` of Eq. (6). -/
def stepMap {n : ℕ} (a b : ℂ) (i j : Fin n) (hij : i ≠ j)
    (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  stepMapOf (clauseProj a b i j hij) i j ρ

/-- `H = Σ_α Φ_α` for a restricted-clause family (Eq. (1) with restricted clauses). -/
def hamiltonian {n L : ℕ} (a b : Fin L → ℂ) (ci cj : Fin L → Fin n)
    (hne : ∀ α, ci α ≠ cj α) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ α : Fin L, clauseProj (a α) (b α) (ci α) (cj α) (hne α)

/-- The mixed Type I / Type II Hamiltonians of Appendix A, Eq. (A1)-(A2). -/
def hamiltonianMixed {n L : ℕ} (κ : Fin L → Bool) (a b : Fin L → ℂ)
    (ci cj : Fin L → Fin n) (hne : ∀ α, ci α ≠ cj α) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ α : Fin L, if κ α then typeIIProjector (ci α) (cj α) (hne α)
    else clauseProj (a α) (b α) (ci α) (cj α) (hne α)

/-- The generator `T = (1/L) Σ_α T_α` of Eq. (8), for a restricted-clause family. -/
def familyChannel {n L : ℕ} (a b : Fin L → ℂ) (ci cj : Fin L → Fin n)
    (hne : ∀ α, ci α ≠ cj α) (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (1 / (L : ℂ)) • ∑ α : Fin L, stepMap (a α) (b α) (ci α) (cj α) (hne α) ρ

/-- One step of the Type I / Type II process of Appendix A, Eq. (A1)-(A2). -/
def stepMapMixed {n : ℕ} (k : Bool) (a b : ℂ) (i j : Fin n) (hij : i ≠ j)
    (ρ : NOp n) : NOp n :=
  stepMapOf (if k then typeIIProjector i j hij else clauseProj a b i j hij) i j ρ

/-- The generator `T = (1/L) Σ_α T_α` for a Type I / Type II clause family. -/
def familyChannelMixed {n L : ℕ} (κ : Fin L → Bool) (a b : Fin L → ℂ)
    (ci cj : Fin L → Fin n) (hne : ∀ α, ci α ≠ cj α) (ρ : NOp n) : NOp n :=
  (1 / (L : ℂ)) • ∑ α : Fin L, stepMapMixed (κ α) (a α) (b α) (ci α) (cj α) (hne α) ρ

/-- The `t`-fold iterate of the Type I / Type II process. -/
def chanPowerMixed {n L : ℕ} (κ : Fin L → Bool) (a b : Fin L → ℂ)
    (ci cj : Fin L → Fin n) (hne : ∀ α, ci α ≠ cj α) (t : ℕ) (ρ : NOp n) : NOp n :=
  (familyChannelMixed κ a b ci cj hne)^[t] ρ

/-- The `t`-fold iterate `ρ_t = T^t(ρ_0)` of the process. -/
def chanPower {n L : ℕ} (a b : Fin L → ℂ) (ci cj : Fin L → Fin n)
    (hne : ∀ α, ci α ≠ cj α) (t : ℕ) (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (familyChannel a b ci cj hne)^[t] ρ

/-- The maximally mixed initial state on `n` qubits, `I / 2^n`. -/
def maximallyMixed (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ((2 : ℂ) ^ n)⁻¹ • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)

/-! ## Instance predicates -/

/-- A YES instance of Restricted Quantum 2-SAT: some (`n`-qubit) state satisfies every
clause, `tr[Φ_α σ] = 0` for all `α` (Sec. I, definition of the YES case, restricted to
Eq. (5) clauses). -/
def IsYesInstance {n L : ℕ} (a b : Fin L → ℂ) (ci cj : Fin L → Fin n)
    (hne : ∀ α, ci α ≠ cj α) : Prop :=
  ∃ σ : NOp n, σ.PosSemidef ∧ Matrix.trace σ = 1 ∧ ∀ α,
    Matrix.trace (clauseProj (a α) (b α) (ci α) (cj α) (hne α) * σ) = 0

/-- A NO instance with promise gap `c`: every density matrix has energy at least `c`
(Sec. I, definition of the NO case). -/
def IsNoInstance {n L : ℕ} (a b : Fin L → ℂ) (ci cj : Fin L → Fin n)
    (hne : ∀ α, ci α ≠ cj α) (c : ℝ) : Prop :=
  ∀ σ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ, σ.PosSemidef → Matrix.trace σ = 1 →
    c ≤ (Matrix.trace (hamiltonian a b ci cj hne * σ)).re

/-! ## Measurement-outcome law -/

/-- The number of `0`-valued measurement outcomes in a run (Eq. (9) and Sec. I);
`false` denotes a satisfied projector (outcome `0`). -/
def zeroCount {T : ℕ} (o : Fin T → Bool) : ℕ :=
  (Finset.univ.filter (fun t => o t = false)).card

/-- The law of the outcome record under independent per-step Bernoulli trials with
`0`-probability `p t` (the binomial model of Result 1 and Result 2, Eqs. (43) and (54)). -/
def outcomeProb {T : ℕ} (p : Fin T → ℝ) (o : Fin T → Bool) : ℝ :=
  ∏ t, if o t then (1 - p t) else p t

/-- The per-step probability of outcome `0`, `1 − tr[H ρ_t]/L`, Eq. (27). -/
def zeroProbAt {n L : ℕ} (a b : Fin L → ℂ) (ci cj : Fin L → Fin n)
    (hne : ∀ α, ci α ≠ cj α) (t : ℕ) : ℝ :=
  1 - (Matrix.trace (hamiltonian a b ci cj hne *
    chanPower a b ci cj hne t (maximallyMixed n))).re / (L : ℝ)

/-! ## Local algebra (Eqs. (16) and (22)) -/

/-- A restricted amplitude vanishes on equal bits. -/
theorem restrictedAmp_self (a b : ℂ) (p : Fin 2) : restrictedAmp a b p p = 0 := by
  fin_cases p <;> simp [restrictedAmp]

/-- A nonzero restricted amplitude forces opposite bits. -/
theorem restrictedAmp_ne_zero {a b : ℂ} {p q : Fin 2} (h : restrictedAmp a b p q ≠ 0) :
    p ≠ q := by
  intro hpq
  subst hpq
  fin_cases p <;> simp [restrictedAmp] at h

/-- `σ^z_i σ^z_j` is diagonal with entry `hz (u i) * hz (u j)`. -/
theorem sigmaZ_mul_sigmaZ_apply {n : ℕ} (i j : Fin n) (u t : Fin n → Fin 2) :
    (sigmaZAt i * sigmaZAt j) u t =
      if u = t then hz (u i) * hz (u j) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hut : u = t
  · subst hut
    rw [if_pos rfl, Finset.sum_eq_single u]
    · simp [sigmaZAt]
    · intro x _ hxu; simp [sigmaZAt, hxu]
    · intro hu; exact absurd (Finset.mem_univ u) hu
  · rw [if_neg hut]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxt : x = t
    · have hux : ¬ (u = x) := by intro h'; exact hut (h'.trans hxt)
      simp [sigmaZAt, hux]
    · simp [sigmaZAt, hxt]

/-- The column index of a nonzero restricted-clause entry has opposite bits. -/
theorem clauseProj_col_bits {n : ℕ} {a b : ℂ} {i j : Fin n} {hij : i ≠ j}
    {s t : Fin n → Fin 2} (h : clauseProj a b i j hij s t ≠ 0) : t i ≠ t j := by
  by_contra hEq
  apply h
  unfold clauseProj
  by_cases hagree : (∀ k, k ≠ i → k ≠ j → s k = t k)
  · rw [if_pos hagree]
    have hz0 : restrictedAmp a b (t i) (t j) = 0 := by rw [hEq]; exact restrictedAmp_self a b _
    simp [hz0]
  · simp [hagree]

/-- The row index of a nonzero restricted-clause entry has opposite bits. -/
theorem clauseProj_row_bits {n : ℕ} {a b : ℂ} {i j : Fin n} {hij : i ≠ j}
    {s t : Fin n → Fin 2} (h : clauseProj a b i j hij s t ≠ 0) : s i ≠ s j := by
  by_contra hEq
  apply h
  unfold clauseProj
  by_cases hagree : (∀ k, k ≠ i → k ≠ j → s k = t k)
  · rw [if_pos hagree]
    have hz0 : restrictedAmp a b (s i) (s j) = 0 := by rw [hEq]; exact restrictedAmp_self a b _
    simp [hz0]
  · simp [hagree]

/-- **Eq. (16)**, left form: `Φ_α (σ^z_i + σ^z_j) = 0`. -/
theorem clauseProj_mul_signsum {n : ℕ} (a b : ℂ) (i j : Fin n) (hij : i ≠ j) :
    clauseProj a b i j hij * (sigmaZAt i + sigmaZAt j) = 0 := by
  ext s t
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single t]
  · have hdiag : (sigmaZAt i + sigmaZAt j) t t = hz (t i) + hz (t j) := by
      simp [sigmaZAt]
    rw [hdiag]
    by_cases hct : clauseProj a b i j hij s t = 0
    · simp [hct]
    · have hne : t i ≠ t j := clauseProj_col_bits hct
      rw [hz_add_hz hne, mul_zero]
      simp [Matrix.zero_apply]
  · intro u _ hut
    have : (sigmaZAt i + sigmaZAt j) u t = 0 := by simp [sigmaZAt, hut]
    rw [this, mul_zero]
  · intro ht; exact absurd (Finset.mem_univ t) ht

/-- **Eq. (16)**, right form: `(σ^z_i + σ^z_j) Φ_α = 0`. -/
theorem signsum_mul_clauseProj {n : ℕ} (a b : ℂ) (i j : Fin n) (hij : i ≠ j) :
    (sigmaZAt i + sigmaZAt j) * clauseProj a b i j hij = 0 := by
  ext s t
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single s]
  · have hdiag : (sigmaZAt i + sigmaZAt j) s s = hz (s i) + hz (s j) := by
      simp [sigmaZAt]
    rw [hdiag]
    by_cases hcs : clauseProj a b i j hij s t = 0
    · simp [hcs]
    · have hne : s i ≠ s j := clauseProj_row_bits hcs
      rw [hz_add_hz hne, zero_mul]
      simp [Matrix.zero_apply]
  · intro u _ hus
    have hsu : ¬ (s = u) := fun h' => hus h'.symm
    have : (sigmaZAt i + sigmaZAt j) s u = 0 := by simp [sigmaZAt, hsu]
    rw [this, zero_mul]
  · intro hs; exact absurd (Finset.mem_univ s) hs

/-- **Eq. (22)**: `Φ_α σ^z_i σ^z_j = -Φ_α`. -/
theorem clauseProj_mul_pair {n : ℕ} (a b : ℂ) (i j : Fin n) (hij : i ≠ j) :
    clauseProj a b i j hij * (sigmaZAt i * sigmaZAt j) = -clauseProj a b i j hij := by
  ext s t
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single t]
  · have hdiag : (sigmaZAt i * sigmaZAt j) t t = hz (t i) * hz (t j) := by
      rw [sigmaZ_mul_sigmaZ_apply]; simp
    rw [hdiag]
    by_cases hct : clauseProj a b i j hij s t = 0
    · simp [hct]
    · have hne : t i ≠ t j := clauseProj_col_bits hct
      rw [hz_mul_hz_neg hne, mul_neg, mul_one]
      simp [Matrix.neg_apply]
  · intro u _ hut
    rw [sigmaZ_mul_sigmaZ_apply]
    simp only [if_neg hut, mul_zero]
  · intro ht; exact absurd (Finset.mem_univ t) ht

/-- **Eq. (22)**, right form: `σ^z_i σ^z_j Φ_α = -Φ_α`. -/
theorem pair_mul_clauseProj {n : ℕ} (a b : ℂ) (i j : Fin n) (hij : i ≠ j) :
    (sigmaZAt i * sigmaZAt j) * clauseProj a b i j hij = -clauseProj a b i j hij := by
  ext s t
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single s]
  · have hdiag : (sigmaZAt i * sigmaZAt j) s s = hz (s i) * hz (s j) := by
      rw [sigmaZ_mul_sigmaZ_apply]; simp
    rw [hdiag]
    by_cases hcs : clauseProj a b i j hij s t = 0
    · simp [hcs]
    · have hne : s i ≠ s j := clauseProj_row_bits hcs
      rw [hz_mul_hz_neg hne, neg_mul, one_mul]
      simp [Matrix.neg_apply]
  · intro u _ hus
    rw [sigmaZ_mul_sigmaZ_apply]
    have hsu : ¬ (s = u) := fun h' => hus h'.symm
    simp only [if_neg hsu, zero_mul]
  · intro hs; exact absurd (Finset.mem_univ s) hs

end

end Qatlib.Papers.Schoning2SAT16.MainResults
