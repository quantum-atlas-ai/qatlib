/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.FluctThermal22.MainResults.Framework.ThermalWorkModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Work-cutoff and free-energy bounds (Thm. 1.3, Thm. 1.4, Thm. 1.6, Lemma 3.3)

Fixed source: arXiv:2203.08882v2 (22 September 2022; accepted in Quantum
22 August 2022).

This module proves the finite-matrix free-energy bound and finite-weight
consequences used in the paper's work-cutoff analysis:

* `freeEnergyDiff_abs_le_opNorm` — Thm. 1.6, `|ΔA(β)| ≤ ‖V‖` (fully proved from
  the frozen trace-exponential perturbation lemma `exp_trace_le`).
* `workCutoff_commuting` — Thm. 1.4, `Σ_{w<w_l} P(w)e^{-β(w-ΔA)} = 0` for
  commuting Hamiltonians and `U = 1l`, fully proved in the diagonal model.
* `workCutoff_equiv` — the already-squared finite-weight equivalence from
  Lemma 3.3, with a strictly positive exponential normalization factor.
* `workCutoff_general` — the finite-distribution second-moment implication
  in Thm. 1.3, deriving Eq. (6) from the explicit weighted second-moment
  bound. The Hamiltonian-to-moment bridge is an input to this theorem.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.FluctThermal22.MainResults

open Qatlib.Papers.FluctThermal22.MainResults.Framework
open Qatlib.Concepts.MatrixExpTrace.ExpPerturbation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Theorem 1.6 — free-energy difference bound -/

/-- **Theorem 1.6 (Free-energy difference)**, fixed arXiv:2203.08882v2 p.8, Eq. (11).

Let `H1 = H0 + V` be two Hamiltonians on the finite system `ι`, and let
`ΔA(β) = -(1/β) log(Z1(β)/Z0(β))` be the free-energy difference at inverse
temperature `β > 0`, so the proof can divide by `β` after comparing
the positive partition functions. Lean's operations are total at `β = 0`;
the theorem below concerns the positive-temperature parameter. Then
`|ΔA(β)| ≤ ‖V‖ = ‖H1 - H0‖`.

Proof route (source proof: Appendix C, p.43): both partition functions are related by the
trace-exponential comparison `Z1 ≤ e^{β‖H1-H0‖} Z0` and the symmetric
bound; taking logarithms gives `|log(Z1/Z0)| ≤ β‖H1-H0‖`.  We obtain the two
comparisons directly from the frozen lemma
`Qatlib.Concepts.MatrixExpTrace.ExpPerturbation.exp_trace_le`
applied to `-β H0` and `-β H1`. -/
theorem freeEnergyDiff_abs_le_opNorm [Nonempty ι]
    (β : ℝ) (hβ : 0 < β) (H0 H1 : Matrix ι ι ℂ)
    (h0 : H0.IsHermitian) (h1 : H1.IsHermitian) :
    |freeEnergyDiff β (partitionFun β H0) (partitionFun β H1)| ≤ ‖H1 - H0‖ := by
  have hk : IsSelfAdjoint (-β : ℝ) := by simp [IsSelfAdjoint]
  have hA : ((-(β : ℝ)) • H0).IsHermitian := h0.smul hk
  have hB : ((-(β : ℝ)) • H1).IsHermitian := h1.smul hk
  have hZ0 : 0 < partitionFun β H0 :=
    exp_trace_pos (I := ι) ⟨(-(β : ℝ)) • H0, hA⟩
  have hZ1 : 0 < partitionFun β H1 :=
    exp_trace_pos (I := ι) ⟨(-(β : ℝ)) • H1, hB⟩
  have hle1 : partitionFun β H1 ≤ Real.exp (β * ‖H1 - H0‖) * partitionFun β H0 := by
    have h := exp_trace_le ((-(β : ℝ)) • H0) ((-(β : ℝ)) • H1) hA hB
    rw [show ‖(-(β : ℝ)) • H0 - (-(β : ℝ)) • H1‖ = β * ‖H1 - H0‖ by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ, norm_sub_rev]] at h
    exact h
  have hle2 : partitionFun β H0 ≤ Real.exp (β * ‖H1 - H0‖) * partitionFun β H1 := by
    have h := exp_trace_le ((-(β : ℝ)) • H1) ((-(β : ℝ)) • H0) hB hA
    rw [show ‖(-(β : ℝ)) • H1 - (-(β : ℝ)) • H0‖ = β * ‖H1 - H0‖ by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ]] at h
    exact h
  have hlog1 : Real.log (partitionFun β H1 / partitionFun β H0) ≤ β * ‖H1 - H0‖ := by
    have hpos : 0 < partitionFun β H1 / partitionFun β H0 := div_pos hZ1 hZ0
    rw [Real.log_le_iff_le_exp hpos, div_le_iff₀ hZ0]
    exact hle1
  have hlog2 : -Real.log (partitionFun β H1 / partitionFun β H0) ≤ β * ‖H1 - H0‖ := by
    have hmul : -Real.log (partitionFun β H1 / partitionFun β H0) =
        Real.log (partitionFun β H0 / partitionFun β H1) := by
      rw [Real.log_div hZ1.ne' hZ0.ne', Real.log_div hZ0.ne' hZ1.ne']
      ring
    rw [hmul]
    rw [Real.log_le_iff_le_exp (div_pos hZ0 hZ1), div_le_iff₀ hZ1]
    exact hle2
  have habs : |Real.log (partitionFun β H1 / partitionFun β H0)| ≤ β * ‖H1 - H0‖ := by
    rw [abs_le]
    constructor <;> linarith
  unfold freeEnergyDiff
  rw [abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hβ)]
  calc (1 / β) * |Real.log (partitionFun β H1 / partitionFun β H0)|
      ≤ (1 / β) * (β * ‖H1 - H0‖) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = ‖H1 - H0‖ := by field_simp

/-! ## Theorem 1.4 — commuting Hamiltonians, `U = 1l` -/

/-- **Theorem 1.4 (Work cutoff for commuting Hamiltonians)**, fixed arXiv:2203.08882v2
p.7, Eq. (8).

When `[H0, H1] = 0` the Hamiltonians share an eigenbasis, so (with `U = 1l`)
the work values are `w_n = ε1,n - ε0,n` with Boltzmann probabilities, and
`w_n ≥ -‖V‖`.  Consequently for every cutoff `wl ≤ -B` with `B ≥ |ε1,n-ε0,n|`
for all `n` (in particular `B = ‖V‖`), the cutoff sum Eq. (8) is exactly `0`.
The model data `ε0, ε1` are the shared-basis eigenvalue lists; `B` is the
eigenvalue-shift bound `‖V‖` (standard `|⟨φ,Vφ⟩| ≤ ‖V‖` at a unit eigenvector). -/
theorem workCutoff_commuting
    (β wl B ΔA : ℝ) (ε0 ε1 : ι → ℝ)
    (hB : ∀ n, |ε1 n - ε0 n| ≤ B) (hwl : wl ≤ -B) :
    cutoffSum β wl ε0 ε1 (1 : Matrix ι ι ℂ) ΔA = 0 := by
  unfold cutoffSum
  apply Finset.sum_eq_zero
  intro m _
  apply Finset.sum_eq_zero
  intro n _
  by_cases hlt : workValue ε0 ε1 m n < wl
  · rw [ite_eq_left hlt, twoTimeProb_identity]
    by_cases hmn : n = m
    · rw [ite_eq_left hmn]
      exfalso
      have hbound : -B ≤ ε1 n - ε0 n := (abs_le.mp (hB n)).1
      unfold workValue at hlt
      subst hmn
      linarith
    · rw [ite_eq_right hmn, zero_mul]
  · rw [ite_eq_right hlt]

/-! ## Lemma 3.3 — equivalence of Eq. (62) and Eq. (4) -/

omit [DecidableEq ι]

/-- The cutoff functional Eq. (4) factors as `e^{βΔA}` times the
exponentially weighted tail `Σ_{w<w_l} P(w)e^{-βw}`.  (Paper Eq. (80).) -/
theorem cutoffSum_eq_exp_mul_tail
    (β wl ΔA : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ) :
    cutoffSum β wl ε0 ε1 V ΔA =
      Real.exp (β * ΔA) * workTailWeighted β wl ε0 ε1 V := by
  unfold cutoffSum workTailWeighted
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : workValue ε0 ε1 m n < wl
  · rw [ite_eq_left h, ite_eq_left h]
    rw [show -β * (workValue ε0 ε1 m n - ΔA)
          = (-β * workValue ε0 ε1 m n) + (β * ΔA) by ring, Real.exp_add]
    ring
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- **Lemma 3.3**, fixed arXiv:2203.08882v2 p.17, Eq. (78).

The work-cutoff condition Eq. (62),
`‖e^{-βW/2}Π_{<w_l}(U⊗1l)|Ψ0⟩‖ ≤ (ε/6)‖e^{-βW/2}(U⊗1l)|Ψ0⟩‖`, after squaring
and using Eq. (79)/(80) and the Jarzynski identity Eq. (59)
(`‖e^{-βW/2}(U⊗1l)|Ψ0⟩‖² = e^{-βΔA}`), is equivalent to Eq. (4),
`Σ_{w<w_l} P(w)e^{-β(w-ΔA)} ≤ (ε/6)²`.

We phrase it with the tail `Σ_{w<w_l}P(w)e^{-βw}` on the left (the squared
left side of Eq. (62), see Eq. (80)) and the strictly positive factor
`e^{-βΔA}`. The equivalence is purely algebraic for every real `ε`. -/
theorem workCutoff_equiv
    (β ε ΔA wl : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ) :
    (workTailWeighted β wl ε0 ε1 V ≤ (ε / 6) ^ 2 * Real.exp (-β * ΔA)) ↔
    (cutoffSum β wl ε0 ε1 V ΔA ≤ (ε / 6) ^ 2) := by
  rw [cutoffSum_eq_exp_mul_tail]
  set tail := workTailWeighted β wl ε0 ε1 V
  set c := (ε / 6) ^ 2
  have hEPos : 0 < Real.exp (β * ΔA) := Real.exp_pos _
  have hEin : Real.exp (β * ΔA) * Real.exp (-β * ΔA) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  constructor
  · intro h
    calc Real.exp (β * ΔA) * tail
        ≤ Real.exp (β * ΔA) * (c * Real.exp (-β * ΔA)) :=
          mul_le_mul_of_nonneg_left h hEPos.le
      _ = c := by
          rw [← mul_assoc, mul_comm (Real.exp (β * ΔA)) c, mul_assoc, hEin, mul_one]
  · intro h
    have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-β * ΔA)).le
    calc tail = Real.exp (-β * ΔA) * (Real.exp (β * ΔA) * tail) := by
            rw [← mul_assoc, mul_comm (Real.exp (-β * ΔA)) (Real.exp (β * ΔA)), hEin, one_mul]
      _ ≤ Real.exp (-β * ΔA) * c := hh
      _ = c * Real.exp (-β * ΔA) := by ring

/-! ## Theorem 1.3 — general-Hamiltonian cutoff (Eq. (6)) -/

/-- **Theorem 1.3 (Work cutoff for general Hamiltonians)**, fixed arXiv:2203.08882v2
p.7, Eq. (6).

Let `H1 = H0 + V`, `ε > 0`, and `V_U = H1 - U H0 U†` with `B = ‖V_U‖`.  For all
cutoffs `w_l ≤ -6‖V_U‖/ε`, the cutoff condition Eq. (6) (equivalently Eq. (4))
holds:
`Σ_{w<w_l} P(w)e^{-β(w-ΔA)} ≤ (ε/6)²`.

Proof route (paper Sec. 4.1, pp.26–27, Eqs. (140)–(150)): the Crooks equality Eq. (144)
together with the second-moment bound `Σ_w P^rev(w)w² ≤ ‖V_U‖²` (Eq. (148))
gives Eq. (149) `Σ_{w<w_l}P(w)e^{-βw} ≤ (‖V_U‖/w_l)² e^{-βΔA}`; the cutoff
hypothesis then yields Eq. (150)/Eq. (6). Here the full exponentially tilted
second-moment bound is an explicit input. The proof applies the finite
Chebyshev inequality directly; it does not establish the Hamiltonian bridge. -/
theorem workCutoff_general
    (β ε wl ΔA B : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ)
    (hε : 0 < ε) (hB : 0 ≤ B) (hwlneg : wl < 0)
    (hwl : wl ≤ -6 * B / ε)
    (hmoment : (∑ m, ∑ n, twoTimeProb β ε0 V m n *
      Real.exp (-β * (workValue ε0 ε1 m n - ΔA)) * (workValue ε0 ε1 m n) ^ 2) ≤ B ^ 2) :
    cutoffSum β wl ε0 ε1 V ΔA ≤ (ε / 6) ^ 2 := by
  have hprob (m n : ι) : 0 ≤ twoTimeProb β ε0 V m n := by
    unfold twoTimeProb eigenPartition boltzmannWeight
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le
      (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le)) (Complex.normSq_nonneg _)
  have hsum : wl ^ 2 * cutoffSum β wl ε0 ε1 V ΔA ≤ B ^ 2 := by
    apply le_trans ?_ hmoment
    unfold cutoffSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    by_cases ht : workValue ε0 ε1 m n < wl
    · rw [ite_eq_left ht]
      have hsq : wl ^ 2 ≤ (workValue ε0 ε1 m n) ^ 2 := by nlinarith
      have hp : 0 ≤ twoTimeProb β ε0 V m n *
          Real.exp (-β * (workValue ε0 ε1 m n - ΔA)) :=
        mul_nonneg (hprob m n) (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left hsq hp]
    · rw [ite_eq_right ht, mul_zero]
      exact mul_nonneg (mul_nonneg (hprob m n) (Real.exp_pos _).le) (sq_nonneg _)
  have hsqwl : 0 < wl ^ 2 := sq_pos_of_neg hwlneg
  have htail : cutoffSum β wl ε0 ε1 V ΔA ≤ (B / wl) ^ 2 := by
    rw [div_pow, le_div_iff₀ hsqwl]
    nlinarith [hsum]
  apply le_trans htail
  rw [sq_le_sq, abs_div, abs_of_nonneg hB, abs_of_neg hwlneg,
    abs_of_pos (by positivity : 0 < ε / 6), div_le_iff₀ (neg_pos.mpr hwlneg)]
  have hh := (le_div_iff₀ hε).mp hwl
  nlinarith

/-- The algebraic step Eq. (149) → Eq. (150) of Thm. 1.3, proved in full.

If the exponentially weighted tail obeys the Crooks/moment bound
`Σ_{w<w_l}P(w)e^{-βw} ≤ (B/w_l)² e^{-βΔA}` for a cutoff `w_l < 0` satisfying
`w_l ≤ -6B/ε`,
then Eq. (4)/(6) `Σ_{w<w_l}P(w)e^{-β(w-ΔA)} ≤ (ε/6)²` follows. -/
theorem workCutoff_of_moment
    (β ε wl ΔA B : ℝ) (ε0 ε1 : ι → ℝ) (V : Matrix ι ι ℂ)
    (hε : 0 < ε) (hB : 0 ≤ B) (hwlneg : wl < 0)
    (hwl : wl ≤ -6 * B / ε)
    (hmoment : workTailWeighted β wl ε0 ε1 V ≤ (B / wl) ^ 2 * Real.exp (-β * ΔA)) :
    cutoffSum β wl ε0 ε1 V ΔA ≤ (ε / 6) ^ 2 := by
  have hEPos : 0 < Real.exp (β * ΔA) := Real.exp_pos _
  have hEin : Real.exp (β * ΔA) * Real.exp (-β * ΔA) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  rw [cutoffSum_eq_exp_mul_tail]
  calc Real.exp (β * ΔA) * workTailWeighted β wl ε0 ε1 V
      ≤ Real.exp (β * ΔA) * ((B / wl) ^ 2 * Real.exp (-β * ΔA)) :=
        mul_le_mul_of_nonneg_left hmoment hEPos.le
    _ = (B / wl) ^ 2 := by
        rw [← mul_assoc, mul_comm (Real.exp (β * ΔA)) ((B / wl) ^ 2), mul_assoc, hEin, mul_one]
    _ ≤ (ε / 6) ^ 2 := by
        rw [sq_le_sq, abs_of_pos (by positivity : (0 : ℝ) < ε / 6)]
        -- reduce `|B/wl| ≤ ε/6` to `6B ≤ ε·(-wl)`, which is `wl ≤ -6B/ε`.
        have hwl' : 6 * B ≤ ε * (-wl) := by
          have h := mul_le_mul_of_nonneg_left hwl hε.le
          have h2 : ε * (-6 * B / ε) = -(6 * B) := by field_simp
          rw [h2] at h
          nlinarith
        have hbabs : |B / wl| ≤ ε / 6 := by
          rw [abs_div, abs_of_nonneg hB, abs_of_neg hwlneg]
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < -wl)]
          nlinarith
        exact hbabs

/-- The old Lean cutoff implication fails even for a one-point work distribution: all its
scalar premises hold with `B = 0`, but work `-2` lies below cutoff `-1` with probability one.
This refutes the old unlinked numerical statement, not the source Hamiltonian theorem. -/
theorem moment_fail :
    0 < (1 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧ (-1 : ℝ) < 0 ∧
      (-1 : ℝ) ≤ -6 * (0 : ℝ) / 1 ∧
      ¬ cutoffSum 0 (-1) (fun _ : Unit => 0) (fun _ : Unit => -2)
          (1 : Matrix Unit Unit ℂ) 0 ≤ ((1 : ℝ) / 6) ^ 2 := by
  norm_num [cutoffSum, twoTimeProb, boltzmannWeight, eigenPartition, workValue,
    Matrix.one_apply]

/-- A nonzero work value satisfies the repaired full moment premise at `B = 2`.
The corresponding cutoff `-12` then obeys the conclusion by the retained general theorem. -/
theorem moment_witness :
    (∑ m : Unit, ∑ n : Unit,
      twoTimeProb 0 (fun _ : Unit => 0) (1 : Matrix Unit Unit ℂ) m n *
        Real.exp (-(0 : ℝ) *
          (workValue (fun _ : Unit => 0) (fun _ : Unit => -2) m n - 0)) *
        (workValue (fun _ : Unit => 0) (fun _ : Unit => -2) m n) ^ 2) ≤ (2 : ℝ) ^ 2 ∧
      cutoffSum 0 (-12) (fun _ : Unit => 0) (fun _ : Unit => -2)
        (1 : Matrix Unit Unit ℂ) 0 ≤ ((1 : ℝ) / 6) ^ 2 := by
  have hmoment : (∑ m : Unit, ∑ n : Unit,
      twoTimeProb 0 (fun _ : Unit => 0) (1 : Matrix Unit Unit ℂ) m n *
        Real.exp (-(0 : ℝ) *
          (workValue (fun _ : Unit => 0) (fun _ : Unit => -2) m n - 0)) *
        (workValue (fun _ : Unit => 0) (fun _ : Unit => -2) m n) ^ 2) ≤ (2 : ℝ) ^ 2 := by
    norm_num [twoTimeProb, boltzmannWeight, eigenPartition, workValue, Matrix.one_apply]
  refine ⟨hmoment, ?_⟩
  exact workCutoff_general 0 1 (-12) 0 2 (fun _ : Unit => 0) (fun _ : Unit => -2)
    (1 : Matrix Unit Unit ℂ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmoment

end Qatlib.Papers.FluctThermal22.MainResults
