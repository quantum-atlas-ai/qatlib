/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# QMLBoolean13 — source model and main results

Yoo, Bang, Lee, Lee, "A quantum speedup in machine learning: Finding a N-bit Boolean
function for a classification", fixed arXiv:1303.6055v4 (14 Oct 2014).

This module proves the mathematical identities and model counterexamples listed below:

* Eq. (8)-(13), pp. 5-6: the 1-bit task-fidelity comparison for the
  constant-zero target `f1`.  `taskFidelity_comparison` (proved).
* Eq. (14)/(A.7), pp. 8 & 13, Appendix A:
  `optimal_phase_cancellation` (proved, Eq. (A.6)),
  `optimal_phase_oneBit_targetZero` (proved instance), and machine-checked counterexamples to the old unrestricted perfectness contract.
* Eq. (B.1), p. 14, Appendix B: the practical phase choice `φ_k = π p_k`.
  `practical_phase_tendsto` (proved), `practical_phase_oneBit_targetZero_dominates`
  (proved local instance), and a counterexample to the old domination contract with unrelated classical probabilities.

Boundary: the paper's fidelity objects are formalised directly from Eq. (6); the model
does not attempt a gate-level synthesis of the multi-controlled circuit, only the 2×2
stage operators of Eq. (5) used by the fidelity computation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMLBoolean13.MainResults

/-! ## Task-fidelity model for 1-bit Boolean functions (Section 3) -/

/-- Complement `q_j = 1 - p_j` of a control probability (Section 3, below Eq. (10)). -/
def qbar (p : ℝ) : ℝ := 1 - p

/-- Eq. (11), p. 6: the interference weight `p_int = 2 sqrt (p0 p1 q0 q1)`. -/
def interferenceWeight (p0 p1 : ℝ) : ℝ :=
  2 * Real.sqrt (p0 * p1 * qbar p0 * qbar p1)

/-- Real fourth root `x^{1/4} = sqrt (sqrt x)`, the task-fidelity exponent for `N = 1`
(Eq. (6) with `2^N = 2`, hence exponent `1/2` applied to the inner square roots). -/
def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

/-- Eq. (9), p. 6: classical task fidelity `Fc = (p0 (p0 p1 + q0 q1))^{1/4}` for the
constant-zero target `f1`. -/
def classicalTaskFidelity (p0 p1 : ℝ) : ℝ :=
  fourthRoot (p0 * (p0 * p1 + qbar p0 * qbar p1))

/-- Eq. (12), p. 6: quantum task fidelity `Fq = (Fc^4 + p0 p_int cos Δ)^{1/4}` for `f1`,
where `Fc^4 = p0 (p0 p1 + q0 q1)` and `Δ = φ1 - φ0`. -/
def quantumTaskFidelity (p0 p1 Δ : ℝ) : ℝ :=
  fourthRoot (p0 * (p0 * p1 + qbar p0 * qbar p1) + p0 * interferenceWeight p0 p1 * Real.cos Δ)

/-- The fourth root is strictly increasing on the nonnegative reals: if `0 ≤ x < y`
then `x^{1/4} < y^{1/4}` (composition of the strict monotonicity of `Real.sqrt`). -/
lemma fourthRoot_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : fourthRoot x < fourthRoot y := by
  unfold fourthRoot
  exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg x) (Real.sqrt_lt_sqrt hx hxy)

/-- On the interior of the unit cube the interference weight is strictly positive
(`p_int = 2 sqrt (p0 p1 q0 q1)` with all four factors positive). -/
lemma interferenceWeight_pos {p0 p1 : ℝ} (h0 : 0 < p0) (h0' : p0 < 1)
    (h1 : 0 < p1) (h1' : p1 < 1) : 0 < interferenceWeight p0 p1 := by
  unfold interferenceWeight qbar
  have hprod : 0 < p0 * p1 * (1 - p0) * (1 - p1) := by positivity
  have hs : 0 < Real.sqrt (p0 * p1 * (1 - p0) * (1 - p1)) := Real.sqrt_pos.mpr hprod
  linarith

/-- Elementary AM-GM used to keep `Fq^4 ≥ 0`: `2 sqrt (a b) ≤ a + b` for `a, b ≥ 0`,
proved as `(sqrt a - sqrt b)^2 ≥ 0`. -/
lemma two_sqrt_mul_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have hsq : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have h1 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have h2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  have h3 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b
  nlinarith [hsq, h1, h2, h3]

/-- `Fq^4 = Fc^4 + p0 p_int cos Δ ≥ 0`: since `p_int ≤ p0 p1 + q0 q1` (AM-GM) and
`cos Δ ≥ -1`, the correction `p0 p_int cos Δ` cannot push the base below zero.
Eq. (11) already records that this base is `p0 · Pq(0|1)`, a probability times `p0`. -/
lemma quantumBase_nonneg {p0 p1 Δ : ℝ} (h0 : 0 < p0) (h1 : 0 < p1)
    (hq0 : 0 < qbar p0) (hq1 : 0 < qbar p1) :
    0 ≤ p0 * (p0 * p1 + qbar p0 * qbar p1)
        + p0 * interferenceWeight p0 p1 * Real.cos Δ := by
  have hPc : 0 ≤ p0 * p1 + qbar p0 * qbar p1 := by positivity
  have hAGM : interferenceWeight p0 p1 ≤ p0 * p1 + qbar p0 * qbar p1 := by
    have h := two_sqrt_mul_le_add (mul_nonneg h0.le h1.le) (mul_nonneg hq0.le hq1.le)
    have harg : (p0 * p1) * (qbar p0 * qbar p1) = p0 * p1 * qbar p0 * qbar p1 := by ring
    rw [harg] at h
    unfold interferenceWeight
    exact h
  have hcos : -1 ≤ Real.cos Δ := Real.neg_one_le_cos Δ
  have hpInt_nn : 0 ≤ interferenceWeight p0 p1 := by
    unfold interferenceWeight; positivity
  have hstep : interferenceWeight p0 p1 * (-1) ≤ interferenceWeight p0 p1 * Real.cos Δ :=
    mul_le_mul_of_nonneg_left hcos hpInt_nn
  have hsum : 0 ≤ p0 * p1 + qbar p0 * qbar p1 + interferenceWeight p0 p1 * Real.cos Δ := by
    nlinarith [hAGM, hstep]
  have hfac : p0 * (p0 * p1 + qbar p0 * qbar p1)
        + p0 * interferenceWeight p0 p1 * Real.cos Δ
      = p0 * (p0 * p1 + qbar p0 * qbar p1 + interferenceWeight p0 p1 * Real.cos Δ) := by
    ring
  rw [hfac]
  exact mul_nonneg h0.le hsum

/-- **Eq. (13), p. 6.** For a constant-zero 1-bit target `f1` and `0 < p0, p1 < 1`,
the quantum task fidelity beats the classical one exactly when `cos Δ > 0`, and falls
below it when `cos Δ < 0`, where `Δ = φ1 - φ0` is the relative phase of the two unitaries.

This is the real-analysis shadow of Eq. (12): `Fq^4 - Fc^4 = p0 p_int cos Δ` with
`p0 > 0`, `p_int > 0`, so the sign of `Fq^4 - Fc^4` is the sign of `cos Δ`, and
`x ↦ x^{1/4}` is strictly increasing on `[0, ∞)`. -/
theorem taskFidelity_comparison (p0 p1 Δ : ℝ)
    (h0 : 0 < p0) (h0' : p0 < 1) (h1 : 0 < p1) (h1' : p1 < 1) :
    (0 < Real.cos Δ → classicalTaskFidelity p0 p1 < quantumTaskFidelity p0 p1 Δ) ∧
    (Real.cos Δ < 0 → quantumTaskFidelity p0 p1 Δ < classicalTaskFidelity p0 p1) := by
  have hq0 : 0 < qbar p0 := by unfold qbar; linarith
  have hq1 : 0 < qbar p1 := by unfold qbar; linarith
  have hbaseC_nn : 0 ≤ p0 * (p0 * p1 + qbar p0 * qbar p1) := by positivity
  have hpInt_pos : 0 < interferenceWeight p0 p1 := interferenceWeight_pos h0 h0' h1 h1'
  refine ⟨?_, ?_⟩
  · intro hcos
    have hcorr : 0 < p0 * interferenceWeight p0 p1 * Real.cos Δ := by positivity
    have hlt : p0 * (p0 * p1 + qbar p0 * qbar p1)
        < p0 * (p0 * p1 + qbar p0 * qbar p1) + p0 * interferenceWeight p0 p1 * Real.cos Δ := by
      linarith
    have hroot := fourthRoot_lt hbaseC_nn hlt
    simpa [classicalTaskFidelity, quantumTaskFidelity] using hroot
  · intro hcos
    have hcorr : p0 * interferenceWeight p0 p1 * Real.cos Δ < 0 := by
      have hpos : 0 < p0 * interferenceWeight p0 p1 := mul_pos h0 hpInt_pos
      have : 0 < (p0 * interferenceWeight p0 p1) * (-Real.cos Δ) :=
        mul_pos hpos (by linarith)
      nlinarith [this]
    have hbaseQ_nn := quantumBase_nonneg (Δ := Δ) h0 h1 hq0 hq1
    have hlt : p0 * (p0 * p1 + qbar p0 * qbar p1)
          + p0 * interferenceWeight p0 p1 * Real.cos Δ
        < p0 * (p0 * p1 + qbar p0 * qbar p1) := by
      linarith
    have hroot := fourthRoot_lt hbaseQ_nn hlt
    simpa [classicalTaskFidelity, quantumTaskFidelity] using hroot

/-! ## Gate model and `N`-bit fidelity functional (Appendix A) -/

/-- Eq. (5), p. 5: the 2×2 unitary stage operator
`Ĝ_k = [[√p_k, e^{iφ_k}√(1-p_k)], [e^{-iφ_k}√(1-p_k), -√p_k]]`. -/
def qGate (p φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ (Real.sqrt p : ℂ), Complex.exp (Complex.I * φ) * (Real.sqrt (1 - p) : ℂ);
      Complex.exp (-(Complex.I * φ)) * (Real.sqrt (1 - p) : ℂ), -(Real.sqrt p : ℂ) ]

/-- Product of the stage operators along an ordered active list, stacked on the work
channel (Eq. (A.2)-(A.3): `∏_{k∈A_x} Ĝ_k`).  A `List` keeps the noncommutative order of
application, unlike `Finset.prod`. -/
def gateProduct (A : List ℕ) (p φ : ℕ → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A.foldl (fun M k => M * qGate (p k) (φ k)) 1

/-- The work-channel amplitude `(∏_{k∈A_x} Ĝ_k) |0>` (the input signal `c` is fixed to 0,
so the initial qubit state is `|0> = (1,0)`). -/
def quantumAmplitude (A : List ℕ) (p φ : ℕ → ℝ) : Fin 2 → ℂ :=
  (gateProduct A p φ).mulVec (![1, 0] : Fin 2 → ℂ)

/-- Eq. (A.2), p. 12: the quantum conditional probability `P(f(x)|x)` is the squared
modulus of the `f(x)`-component of the stacked gate product applied to `|0>`. -/
def quantumConditionalProbability {N : ℕ} (A : Fin (2^N) → List ℕ) (p φ : ℕ → ℝ)
    (fx : Fin (2^N) → Fin 2) (x : Fin (2^N)) : ℝ :=
  Complex.normSq (quantumAmplitude (A x) p φ (fx x))

/-- The retired source's closed geometric mean of probabilities, which squares the
paper's task fidelity by omitting the square-root contribution in Eq. (6). -/
def legacyFidelity {N : ℕ} (P : Fin (2^N) → ℝ) : ℝ :=
  (∏ x, P x) ^ ((1 : ℝ) / (2 : ℝ) ^ N)

/-- Eq. (6)/(A.1), pp. 5 & 12: the task fidelity for a deterministic target, i.e. the
geometric mean of square roots `(∏_x P(f(x)|x))^{1/(2*2^N)}` of the per-input correct-output probabilities. -/
def taskFidelity {N : ℕ} (P : Fin (2^N) → ℝ) : ℝ :=
  (∏ x, P x) ^ ((1 : ℝ) / (2 * (2 : ℝ) ^ N))

/-- Eq. (14)/(A.7), pp. 8 & 13: the optimal phase condition `φ_k = π s_k`, where `s_k` is
the `k`-th component of a solution point. -/
def optimalPhase (s : ℕ → ℝ) (k : ℕ) : ℝ := Real.pi * s k

/-- The task fidelity is monotone in the per-input probabilities: if `0 ≤ P ≤ Q` pointwise
then `F(P) ≤ F(Q)`.  This is the step that turns the Appendix-A per-input domination into
`Fq ≥ Fc`. -/
lemma legacyFid_mono {N : ℕ} {P Q : Fin (2^N) → ℝ}
    (hP : ∀ x, 0 ≤ P x) (hPQ : ∀ x, P x ≤ Q x) :
    legacyFidelity P ≤ legacyFidelity Q := by
  unfold legacyFidelity
  refine Real.rpow_le_rpow (Finset.prod_nonneg fun x _ => hP x) ?_ (by positivity)
  exact Finset.prod_le_prod₀ (fun x _ => hP x) fun x _ => hPQ x

/-- The all-perfect machine has task fidelity `1` (the maximum of Eq. (6)). -/
lemma legacyFid_one {N : ℕ} : legacyFidelity (fun _ : Fin (2^N) => (1 : ℝ)) = 1 := by
  unfold legacyFidelity
  simp

/-- A fidelity bounded above by `1` per input has task fidelity `≤ 1`.  This is the
classical side of the comparison: classical per-input probabilities never exceed 1. -/
lemma legacyFid_le1 {N : ℕ} {P : Fin (2^N) → ℝ}
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1) : legacyFidelity P ≤ 1 := by
  unfold legacyFidelity
  have hprod : (∏ x, P x) ≤ 1 := by
    have h1 : (∏ x, P x) ≤ (∏ _ : Fin (2^N), (1 : ℝ)) :=
      Finset.prod_le_prod₀ (fun x _ => hP0 x) fun x _ => hP1 x
    simpa using h1
  have hnn : 0 ≤ ∏ x, P x := Finset.prod_nonneg fun x _ => hP0 x
  calc (∏ x, P x) ^ ((1 : ℝ) / (2 : ℝ) ^ N)
      ≤ (1 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ N) := Real.rpow_le_rpow hnn hprod (by positivity)
    _ = 1 := Real.one_rpow _



/-- The task fidelity is monotone in the per-input probabilities: if `0 ≤ P ≤ Q` pointwise
then `F(P) ≤ F(Q)`.  This is the step that turns the Appendix-A per-input domination into
`Fq ≥ Fc`. -/
lemma taskFidelity_mono {N : ℕ} {P Q : Fin (2^N) → ℝ}
    (hP : ∀ x, 0 ≤ P x) (hPQ : ∀ x, P x ≤ Q x) :
    taskFidelity P ≤ taskFidelity Q := by
  unfold taskFidelity
  refine Real.rpow_le_rpow (Finset.prod_nonneg fun x _ => hP x) ?_ (by positivity)
  exact Finset.prod_le_prod₀ (fun x _ => hP x) fun x _ => hPQ x

/-- The all-perfect machine has task fidelity `1` (the maximum of Eq. (6)). -/
lemma taskFidelity_one {N : ℕ} : taskFidelity (fun _ : Fin (2^N) => (1 : ℝ)) = 1 := by
  unfold taskFidelity
  simp

/-- A fidelity bounded above by `1` per input has task fidelity `≤ 1`.  This is the
classical side of the comparison: classical per-input probabilities never exceed 1. -/
lemma taskFidelity_le_one {N : ℕ} {P : Fin (2^N) → ℝ}
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1) : taskFidelity P ≤ 1 := by
  unfold taskFidelity
  have hprod : (∏ x, P x) ≤ 1 := by
    have h1 : (∏ x, P x) ≤ (∏ _ : Fin (2^N), (1 : ℝ)) :=
      Finset.prod_le_prod₀ (fun x _ => hP0 x) fun x _ => hP1 x
    simpa using h1
  have hnn : 0 ≤ ∏ x, P x := Finset.prod_nonneg fun x _ => hP0 x
  calc (∏ x, P x) ^ ((1 : ℝ) / (2 * (2 : ℝ) ^ N))
      ≤ (1 : ℝ) ^ ((1 : ℝ) / (2 * (2 : ℝ) ^ N)) := Real.rpow_le_rpow hnn hprod (by positivity)
    _ = 1 := Real.one_rpow _

/-- **Eq. (A.6), p. 13.** With the optimal phases `φ_k = π s_k` (`s_k ∈ {0,1}`), the
phase-difference factor `e^{iΔ}`, `Δ = φ_k - φ_l`, is `+1` when `s_k = s_l` and `-1`
when `s_k ≠ s_l`.  Hence exactly one of `Λ_- = 1 - e^{iΔ}` (equal bits) or
`Λ_+ = 1 + e^{iΔ}` (differing bits) vanishes — the `c`-dependent cross terms of the
two-gate product Eq. (A.5) are annihilated. -/
theorem optimal_phase_cancellation (sk sl : ℕ) (hk : sk ≤ 1) (hl : sl ≤ 1) :
    (sk = sl →
        (1 - Complex.exp
          (Complex.I * ((Real.pi * (sk : ℝ) - Real.pi * (sl : ℝ) : ℝ) : ℂ)) : ℂ) = 0) ∧
    (sk ≠ sl →
        (1 + Complex.exp
          (Complex.I * ((Real.pi * (sk : ℝ) - Real.pi * (sl : ℝ) : ℝ) : ℂ)) : ℂ) = 0) := by
  have hk01 : sk = 0 ∨ sk = 1 := by omega
  have hl01 : sl = 0 ∨ sl = 1 := by omega
  refine ⟨?_, ?_⟩
  · intro h
    have h0 : ((Real.pi * (sk : ℝ) - Real.pi * (sl : ℝ) : ℝ)) = 0 := by
      rw [show (sk : ℝ) = (sl : ℝ) by rw [h]]; ring
    rw [h0]; simp
  · intro hne
    rcases hk01 with hk0 | hk1 <;> rcases hl01 with hl0 | hl1
    · exact absurd (by rw [hk0, hl0]) hne
    · rw [hk0, hl1]
      have hΔ : ((Real.pi * ((0 : ℕ) : ℝ) - Real.pi * ((1 : ℕ) : ℝ) : ℝ)) = -Real.pi := by
        push_cast; ring
      rw [hΔ]
      have hneg : Complex.I * ((-Real.pi : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
        push_cast; ring
      rw [hneg, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    · rw [hk1, hl0]
      have hΔ : ((Real.pi * ((1 : ℕ) : ℝ) - Real.pi * ((0 : ℕ) : ℝ) : ℝ)) = Real.pi := by
        push_cast; ring
      rw [hΔ]
      have hpos : Complex.I * ((Real.pi : ℝ) : ℂ) = Real.pi * Complex.I := by
        ring
      rw [hpos, Complex.exp_pi_mul_I]
      norm_num
    · exact absurd (by rw [hk1, hl1]) hne

/-- **Instance, Eq. (14) specialised to `N = 1`, target `f1`.** For the constant-zero
target the solution point is `Q_{f1} = (1,1)`, so Eq. (14) gives `φ_0 = φ_1 = π`, i.e.
`Δ = 0` and `cos Δ = 1 > 0`.  By Eq. (13) (`taskFidelity_comparison`) the quantum task
fidelity then strictly exceeds the classical one for `0 < p0, p1 < 1`. -/
theorem optimal_phase_oneBit_targetZero (p0 p1 : ℝ)
    (h0 : 0 < p0) (h0' : p0 < 1) (h1 : 0 < p1) (h1' : p1 < 1) :
    classicalTaskFidelity p0 p1 < quantumTaskFidelity p0 p1 0 := by
  have hcos : 0 < Real.cos 0 := by rw [Real.cos_zero]; norm_num
  exact (taskFidelity_comparison p0 p1 0 h0 h0' h1 h1').1 hcos

/-! ## Practical machine (Appendix B) -/

/-- Eq. (B.1), p. 14: the practical phase choice `φ_k = π p_k`, locking the free phase to
the control probability so that it tracks the optimised phase `π s_k`. -/
def practicalPhase (p : ℝ) : ℝ := Real.pi * p

/-- An acceptable region for tolerance `εt`: the parameters whose task fidelity reaches at
least `1 - εt` (Section 3, p. 5: "the acceptable region can be seen as a set of
probabilities such that `1 - εt ≤ F`"). -/
def acceptableRegion {β : Type*} (F : β → ℝ) (εt : ℝ) : Set β := {b | 1 - εt ≤ F b}

/-- **Section 3, p. 5 (monotonicity of the acceptable region).** If the quantum fidelity
dominates the classical one at every parameter point, the quantum acceptable region
contains the classical one: "higher `F` guarantees a wider acceptable region". -/
theorem acceptableRegion_mono {β : Type*} {Fc Fq : β → ℝ} {εt : ℝ}
    (hdom : ∀ b, Fc b ≤ Fq b) :
    acceptableRegion Fc εt ⊆ acceptableRegion Fq εt := by
  intro b hb
  exact le_trans hb (hdom b)

/-- **Appendix B, p. 14.** As the control parameter approaches the solution value
`s`, the practical phase `π p` approaches the optimal phase `π s` (continuity of
`p ↦ π p`).  This is the rigorous content of the text's justification. -/
theorem practical_phase_tendsto (s : ℝ) :
    Filter.Tendsto practicalPhase (nhds s) (nhds (practicalPhase s)) := by
  unfold practicalPhase
  exact (continuous_const.mul continuous_id).tendsto s

/-- **Eq. (B.1) specialised to `N = 1`, target `f1`, near the solution point.** With
the practical phases `φ_0 = π p_0`, `φ_1 = π p_1` the relative phase is `Δ = π(p1 - p0)`;
when `|p1 - p0| < 1/2` we have `|Δ| < π/2`, hence `cos Δ > 0`, and Eq. (13) gives
`Fq > Fc`.  This is a rigorous local instance of the Appendix-B claim for the
constant-zero target. -/
theorem practical_phase_oneBit_targetZero_dominates (p0 p1 : ℝ)
    (h0 : 0 < p0) (h0' : p0 < 1) (h1 : 0 < p1) (h1' : p1 < 1)
    (hclose : |p1 - p0| < 1 / 2) :
    classicalTaskFidelity p0 p1
      < quantumTaskFidelity p0 p1 (practicalPhase p1 - practicalPhase p0) := by
  have hΔ : practicalPhase p1 - practicalPhase p0 = Real.pi * (p1 - p0) := by
    unfold practicalPhase; ring
  rw [hΔ]
  have hcos : 0 < Real.cos (Real.pi * (p1 - p0)) := by
    apply Real.cos_pos_of_mem_Ioo
    have habs := abs_lt.mp hclose
    constructor
    · have hstep := mul_lt_mul_of_pos_left habs.1 Real.pi_pos
      have heq : Real.pi * (-(1 / 2 : ℝ)) = -(Real.pi / 2) := by ring
      linarith [heq]
    · have hstep := mul_lt_mul_of_pos_left habs.2 Real.pi_pos
      have heq : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring
      linarith [heq]
  exact (taskFidelity_comparison p0 p1 (Real.pi * (p1 - p0)) h0 h0' h1 h1').1 hcos

/-! ## Diagnostics for the retired contracts

The source's Appendix A concludes perfect conditional probabilities only for x ≠ 0,
under a shared small displacement and the specific circuit activation lists. The old
header required perfection for every x and allowed arbitrary lists and independent
displacements. Appendix B's old header also supplied an unrelated Pc rather than the
classical machine built from the same p. These probes diagnose those headers only.
-/

/-- A single stage with p=0 has zero probability of returning zero, at any phase. -/
theorem zero_single_gate (φ : ℕ → ℝ) :
    quantumConditionalProbability (N := 1) (fun _ => [0]) (fun _ => 0) φ
      (fun _ => 0) 0 = 0 := by
  simp [quantumConditionalProbability, quantumAmplitude, gateProduct, qGate,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A single stage with p=1 returns zero with certainty, including the optimal phase. -/
theorem one_single_gate :
    quantumConditionalProbability (N := 1) (fun _ => [0]) (fun _ => 1)
      (optimalPhase (fun _ => 1)) (fun _ => 0) 0 = 1 := by
  simp [quantumConditionalProbability, quantumAmplitude, gateProduct, qGate,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The old near-solution premises are satisfiable while their perfection conclusion fails. -/
theorem legacy_perfect_refuted :
    (∀ _k : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ((0 : ℝ) = 1 - c ∨ (0 : ℝ) = 1 + c)) ∧
    (∀ x : Fin (2^1), quantumConditionalProbability (fun _ => [0]) (fun _ => 1)
      (optimalPhase (fun _ => 1)) (fun _ => 0) x = 1) ∧
    quantumConditionalProbability (N := 1) (fun _ => [0]) (fun _ => 0)
      (optimalPhase (fun _ => 1)) (fun _ => 0) 0 ≠ 1 := by
  refine ⟨fun _ => ⟨1, by norm_num, Or.inl (by norm_num)⟩, ?_, ?_⟩
  · intro x
    exact one_single_gate
  · rw [zero_single_gate]
    norm_num

/-- Unrelated classical probabilities can have fidelity one while this quantum model has zero. -/
theorem legacy_practical_refuted :
    ¬ legacyFidelity (fun _ : Fin (2^1) => (1 : ℝ)) ≤
      legacyFidelity (fun x : Fin (2^1) =>
        quantumConditionalProbability (fun _ => [0]) (fun _ => 0)
          (fun k => practicalPhase ((fun _ : ℕ => (0 : ℝ)) k)) (fun _ => 0) x) := by
  have hzero (x : Fin (2^1)) :
      quantumConditionalProbability (fun _ => [0]) (fun _ => 0)
        (fun k => practicalPhase ((fun _ : ℕ => (0 : ℝ)) k)) (fun _ => 0) x = 0 :=
    zero_single_gate _
  rw [show (fun x : Fin (2^1) =>
    quantumConditionalProbability (fun _ => [0]) (fun _ => 0)
      (fun k => practicalPhase ((fun _ : ℕ => (0 : ℝ)) k)) (fun _ => 0) x) =
      (fun _ => 0) from funext hzero, legacyFid_one]
  norm_num [legacyFidelity]

/-- The old domination consequence also fails under the same satisfiable optimal-phase
and near-solution data used by the perfectness counterexample. -/
theorem legacy_dom_refuted :
    ¬ legacyFidelity (fun _ : Fin (2^1) => (1 : ℝ)) ≤
      legacyFidelity (fun x : Fin (2^1) =>
        quantumConditionalProbability (fun _ => [0]) (fun _ => 0)
          (optimalPhase (fun _ => 1)) (fun _ => 0) x) := by
  have hzero (x : Fin (2^1)) :
      quantumConditionalProbability (fun _ => [0]) (fun _ => 0)
        (optimalPhase (fun _ => 1)) (fun _ => 0) x = 0 := zero_single_gate _
  rw [show (fun x : Fin (2^1) =>
    quantumConditionalProbability (fun _ => [0]) (fun _ => 0)
      (optimalPhase (fun _ => 1)) (fun _ => 0) x) =
      (fun _ => 0) from funext hzero, legacyFid_one]
  norm_num [legacyFidelity]

end Qatlib.Papers.QMLBoolean13.MainResults
