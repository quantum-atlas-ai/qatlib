/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionLipschitz.SourcePartitionFunctionLipschitz
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Qatlib.Concepts.MatrixExpTrace.GibbsNorm
import Qatlib.Concepts.MatrixWeights.WeightsCore

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalGibbs09 — Appendix C: Lipschitz continuity of Gibbs states

Poulin--Wocjan, fixed arXiv:0905.2199, Appendix C (eqs. (C1)--(C7), p. 7).

Claim `c005`: if `H̃ = H + E`, `‖E‖ ≤ ε/t` with `t = π/(4 E_max)`, and
`ρ(β) = e^{-βH}/Z(β)`, `ρ̃(β) = e^{-βH̃}/Z̃(β)` are the Gibbs states, then
the fidelity satisfies `F(ρ(β), ρ̃(β)) ≥ e^{-βε/t}` (eq. (C1)).

The paper's `F` is the (root) fidelity `Tr sqrt(sqrt ρ ρ̃ sqrt ρ)`
(eq. (C2)); the frozen library's `Froot ρ σ = ‖√ρ √σ‖₁` is the same quantity.
The proof of (C1) has two ingredients:

* (C4)--(C6): `F(ρ, ρ̃) ≥ Ẑ(β) / sqrt(Z(β) Z̃(β))`, where
  `Ĥ = (H + H̃)/2` and `Ẑ` is its partition function.  This is the
  strengthened Golden--Thompson inequality (C3) with `p = 2` applied to
  `A = -βH̃/2`, `B = -βH/2`.
* (C6)--(C7): the partition-function ratio is `≥ e^{-βε/t}`, obtained by
  applying Appendix B (claim `c004`) twice, first to `(H, Ĥ)` and then to
  `(H̃, Ĥ)`, using `‖H - Ĥ‖ = ‖H̃ - Ĥ‖ = ‖E‖/2 ≤ ε/(2t)`.

The second ingredient is proved below (`mid_partition_ratio_ge`), as is the
identity (C4) that turns the root fidelity of the two Gibbs states into the
trace norm of the product of the two half-exponentials (`froot_gibbs_eq`).
The first ingredient — the strengthened Golden--Thompson comparison
(paper (C3) at `p = 2`) — is `strengthened_golden_thompson_traceNorm`.
It follows from the frozen plain Golden--Thompson inequality
`matrix_mw_golden_thompson_trace_potential` (the `p = 1` case) together with
the domination of the real part of the trace by the trace norm, since the
relevant trace is nonnegative.  Hence eq. (C1) is fully proved here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Qatlib.Papers.ThermalGibbs09.MainResults.GibbsFidelity

open Qatlib.Papers.ThermalGibbs09.MainResults
open Qatlib.Papers.ThermalGibbs09.MainResults.PartitionFunctionLipschitz
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MatrixExpTrace.GibbsNorm

/-- `sqrt(exp(-βH)) = exp(-(β/2) H)` for a Hermitian Hamiltonian `H`.

The CFC square root of the positive-definite matrix exponential of a
Hermitian matrix halves the exponent; proved via uniqueness of the
positive-semidefinite square root. -/
theorem cfc_sqrt_exp_half (D : ℕ) (H : Matrix (Fin D) (Fin D) ℂ) (hH : H.IsHermitian)
    (β : ℝ) :
    CFC.sqrt (NormedSpace.exp ((-β) • H)) = NormedSpace.exp ((-(β/2)) • H) := by
  have hM : ((-(β/2)) • H).IsHermitian := hH.smul (R := ℝ) (IsSelfAdjoint.all _)
  have hprod : NormedSpace.exp ((-(β/2)) • H) * NormedSpace.exp ((-(β/2)) • H)
      = NormedSpace.exp ((-β) • H) := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _)]
    congr 1
    module
  have hpsd : (NormedSpace.exp ((-(β/2)) • H)).PosSemidef := exp_posSemidef _ hM
  exact CFC.sqrt_unique hprod (Matrix.PosSemidef.nonneg hpsd)

/-- The CFC square root of the Gibbs state `ρ(β) = e^{-βH}/Z(β)` is
`(√Z(β))⁻¹ • e^{-(β/2)H}`.

This is the paper's passing from `ρ` to `√ρ` in (C2)/(C4), using
`gibbsState β H = Z(β)⁻¹ • e^{-βH}`. -/
theorem cfc_sqrt_gibbs (D : ℕ) (hD : 0 < D) (H : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) (β : ℝ) :
    CFC.sqrt (gibbsState β H) =
      (Real.sqrt (partitionFunction β H))⁻¹ • NormedSpace.exp ((-(β/2)) • H) := by
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hZ : 0 < partitionFunction β H := partitionFunction_pos β H hH
  have hM : ((-(β/2)) • H).IsHermitian := hH.smul (R := ℝ) (IsSelfAdjoint.all _)
  have hpsd0 : (NormedSpace.exp ((-(β/2)) • H)).PosSemidef := exp_posSemidef _ hM
  have hpsd : ((Real.sqrt (partitionFunction β H))⁻¹ •
      NormedSpace.exp ((-(β/2)) • H)).PosSemidef := by
    apply Matrix.PosSemidef.smul hpsd0
    positivity
  have hprod : ((Real.sqrt (partitionFunction β H))⁻¹ • NormedSpace.exp ((-(β/2)) • H)) *
      ((Real.sqrt (partitionFunction β H))⁻¹ • NormedSpace.exp ((-(β/2)) • H))
      = gibbsState β H := by
    rw [gibbsState]
    rw [smul_mul_smul]
    have hexp : NormedSpace.exp ((-(β/2)) • H) * NormedSpace.exp ((-(β/2)) • H)
        = NormedSpace.exp ((-β) • H) := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _)]
      congr 1
      module
    rw [hexp]
    congr 1
    rw [← mul_inv, Real.mul_self_sqrt hZ.le]
  exact CFC.sqrt_unique hprod (Matrix.PosSemidef.nonneg hpsd)

/-- The trace norm scales by a nonnegative real factor. -/
theorem traceNorm_real_smul (D : ℕ) (r : ℝ) (hr : 0 ≤ r) (M : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.traceNorm (r • M) = r * Matrix.traceNorm M := by
  have h1 : r • M = (r : ℂ) • M := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul]
    ring
  rw [h1, Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

/-- **arXiv:0905.2199, Appendix C, eq. (C4).** The root fidelity of the two
Gibbs states is the trace norm of the product of the two half-exponentials,
divided by `sqrt (Z(β) Z̃(β))`.

This is exactly the identity (C4): substituting `√ρ = (√Z)⁻¹ e^{-βH/2}` and
`√ρ̃ = (√Z̃)⁻¹ e^{-βH̃/2}` into `F = ‖√ρ √ρ̃‖₁`. -/
theorem froot_gibbs_eq (D : ℕ) (hD : 0 < D) (H Ht : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) (hHt : Ht.IsHermitian) (β : ℝ) :
    Froot (gibbsState β H) (gibbsState β Ht) =
      Matrix.traceNorm (NormedSpace.exp ((-(β/2)) • H) *
        NormedSpace.exp ((-(β/2)) • Ht)) /
        Real.sqrt (partitionFunction β H * partitionFunction β Ht) := by
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hZ : 0 < partitionFunction β H := partitionFunction_pos β H hH
  have hZt : 0 < partitionFunction β Ht := partitionFunction_pos β Ht hHt
  rw [Froot, cfc_sqrt_gibbs D hD H hH β, cfc_sqrt_gibbs D hD Ht hHt β]
  rw [smul_mul_smul]
  rw [traceNorm_real_smul D _ (by positivity)]
  have hcoef : (Real.sqrt (partitionFunction β H))⁻¹ *
      (Real.sqrt (partitionFunction β Ht))⁻¹ =
      (Real.sqrt (partitionFunction β H * partitionFunction β Ht))⁻¹ := by
    rw [← mul_inv, Real.sqrt_mul hZ.le]
  rw [hcoef, div_eq_mul_inv]
  ring

/-- **arXiv:0905.2199, Appendix C, eq. (C3) at `p = 2` (strengthened
Golden--Thompson inequality).** For Hermitian `A`, `B`,
`Tr e^{A+B} ≤ ‖e^A e^B‖₁ = Tr((e^{B} e^{2A} e^{B})^{1/2})`.

This is the inequality (C3) of Friedland--So with the parameter `p = 2`,
which bounds the partition function `Ẑ(β) = Tr e^{-β(H+H̃)/2}` by the trace
norm that the root fidelity produces in (C4)/(C5).  It is derived from the
frozen plain Golden--Thompson inequality `matrix_mw_golden_thompson_trace_potential`
(the `p = 1` case), using that the real part of the trace is at most its
modulus, which is at most the trace norm. -/
theorem strengthened_golden_thompson_traceNorm (D : ℕ)
    (A B : Matrix (Fin D) (Fin D) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (NormedSpace.exp (A + B))).re ≤
      Matrix.traceNorm (NormedSpace.exp A * NormedSpace.exp B) := by
  /- Plain Golden--Thompson (frozen `matrix_mw_golden_thompson_trace_potential`,
     which is the `p = 1` case of (C3)) bounds `Tr e^{A+B}` by the real trace
     `Tr(e^A e^B)`; the trace norm `‖e^A e^B‖₁` then dominates its real part
     (`Re ≤ |Re| ≤ ‖Tr‖ ≤ ‖·‖₁`).  Since for the Gibbs fidelity the trace
     `Tr(e^{-βH/2} e^{-βH̃/2})` is nonnegative, the plain and the strengthened
     Golden--Thompson bounds coincide in the direction we need. -/
  have hGT := Qatlib.Concepts.MatrixWeights.WeightsCore.matrix_mw_golden_thompson_trace_potential
    D A B hA hB
  refine hGT.trans ?_
  exact (le_abs_self _).trans
    ((Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _))

/-- **arXiv:0905.2199, Appendix C, steps (C4)--(C7), second half.**
With `Ĥ = (H + H̃)/2` and `‖H̃ - H‖ ≤ ε/t`, the partition-function ratio
`Ẑ(β) / sqrt(Z(β) Z̃(β))` is at least `exp(-β ε / t)`.

This is the paper's reduction `(C6) ⇒ (C7)`, using Appendix B twice. -/
theorem mid_partition_ratio_ge
    (D : ℕ) (hD : 0 < D) (H Ht : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) (hHt : Ht.IsHermitian)
    (β ε t : ℝ) (hβ : 0 ≤ β) (ht : 0 < t) (hε0 : 0 ≤ ε)
    (hE : ‖Ht - H‖ ≤ ε / t) :
    Real.exp (-(β * ε / t)) ≤
      partitionFunction β ((1 / 2 : ℝ) • (H + Ht)) /
        Real.sqrt (partitionFunction β H * partitionFunction β Ht) := by
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  let Hmid : Matrix (Fin D) (Fin D) ℂ := (1 / 2 : ℝ) • (H + Ht)
  have hHmid : Hmid.IsHermitian := (hH.add hHt).smul (R := ℝ) (IsSelfAdjoint.all _)
  have hE1 : Hmid - H = (1 / 2 : ℝ) • (Ht - H) := by
    simp only [Hmid]
    module
  have hE2 : Hmid - Ht = (1 / 2 : ℝ) • (H - Ht) := by
    simp only [Hmid]
    module
  have hnorm1 : ‖Hmid - H‖ ≤ (ε / 2) / t := by
    rw [hE1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have : (1 / 2 : ℝ) * ‖Ht - H‖ ≤ (1 / 2) * (ε / t) :=
      mul_le_mul_of_nonneg_left hE (by norm_num)
    have hrew : (1 / 2 : ℝ) * (ε / t) = (ε / 2) / t := by ring
    linarith
  have hnorm2 : ‖Hmid - Ht‖ ≤ (ε / 2) / t := by
    rw [hE2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hEH : ‖H - Ht‖ = ‖Ht - H‖ := norm_sub_rev H Ht
    rw [hEH]
    have : (1 / 2 : ℝ) * ‖Ht - H‖ ≤ (1 / 2) * (ε / t) :=
      mul_le_mul_of_nonneg_left hE (by norm_num)
    have hrew : (1 / 2 : ℝ) * (ε / t) = (ε / 2) / t := by ring
    linarith
  -- Apply Appendix B (claim `c004`) to (H, Hmid) and (Ht, Hmid).
  have hlow1 : (1 / Real.exp (β * (ε / 2) / t)) * partitionFunction β H ≤
      partitionFunction β Hmid :=
    (partition_function_lipschitz H (Hmid - H) Hmid hH hHmid (by abel) (hHmid.sub hH)
      β (ε / 2) t hβ ht hnorm1).1
  have hlow2 : (1 / Real.exp (β * (ε / 2) / t)) * partitionFunction β Ht ≤
      partitionFunction β Hmid :=
    (partition_function_lipschitz Ht (Hmid - Ht) Hmid hHt hHmid (by abel) (hHmid.sub hHt)
      β (ε / 2) t hβ ht hnorm2).1
  have hZH0 : 0 ≤ partitionFunction β H := partitionFunction_nonneg β H hH
  have hZt0 : 0 ≤ partitionFunction β Ht := partitionFunction_nonneg β Ht hHt
  have hZm0 : 0 ≤ partitionFunction β Hmid := partitionFunction_nonneg β Hmid hHmid
  have hδpos : 0 < Real.exp (β * (ε / 2) / t) := Real.exp_pos _
  -- Rewrite the two Appendix-B lower bounds as `Z ≤ δ Zmid`.
  have hZH_le : partitionFunction β H ≤ Real.exp (β * (ε / 2) / t) * partitionFunction β Hmid := by
    have hlow1' : (Real.exp (β * (ε / 2) / t))⁻¹ * partitionFunction β H ≤
        partitionFunction β Hmid := by
      simpa [one_div] using hlow1
    have := (inv_mul_le_iff₀ hδpos).mp hlow1'
    linarith
  have hZt_le : partitionFunction β Ht ≤ Real.exp (β * (ε / 2) / t) * partitionFunction β Hmid := by
    have hlow2' : (Real.exp (β * (ε / 2) / t))⁻¹ * partitionFunction β Ht ≤
        partitionFunction β Hmid := by
      simpa [one_div] using hlow2
    have := (inv_mul_le_iff₀ hδpos).mp hlow2'
    linarith
  set δ1 := Real.exp (β * (ε / 2) / t) with hδ1
  have hprod_le : partitionFunction β H * partitionFunction β Ht ≤ (δ1 * partitionFunction β Hmid) ^ 2 := by
    have h1 : partitionFunction β H ≤ δ1 * partitionFunction β Hmid := hZH_le
    have h2 : partitionFunction β Ht ≤ δ1 * partitionFunction β Hmid := hZt_le
    have hrhs : 0 ≤ δ1 * partitionFunction β Hmid := mul_nonneg hδpos.le hZm0
    nlinarith [mul_le_mul h1 h2 hZt0 hrhs]
  have hsqrt_le : Real.sqrt (partitionFunction β H * partitionFunction β Ht) ≤
      δ1 * partitionFunction β Hmid := by
    have hrhs : 0 ≤ δ1 * partitionFunction β Hmid := mul_nonneg hδpos.le hZm0
    calc Real.sqrt (partitionFunction β H * partitionFunction β Ht)
        ≤ Real.sqrt ((δ1 * partitionFunction β Hmid) ^ 2) := Real.sqrt_le_sqrt hprod_le
      _ = δ1 * partitionFunction β Hmid := Real.sqrt_sq hrhs
  have hs_pos : 0 < Real.sqrt (partitionFunction β H * partitionFunction β Ht) := by
    exact Real.sqrt_pos.mpr (mul_pos (partitionFunction_pos β H hH) (partitionFunction_pos β Ht hHt))
  have hratio : 1 / δ1 ≤ partitionFunction β Hmid /
      Real.sqrt (partitionFunction β H * partitionFunction β Ht) := by
    rw [div_le_div_iff₀ hδpos hs_pos]
    nlinarith [hsqrt_le]
  have hexp_le : Real.exp (-(β * ε / t)) ≤ 1 / δ1 := by
    rw [hδ1, one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hle : β * (ε / 2) / t ≤ β * ε / t := by
      have : β * (ε / 2) ≤ β * ε := by nlinarith
      exact div_le_div_of_nonneg_right this ht.le
    linarith
  exact hexp_le.trans hratio

/-- **arXiv:0905.2199, Appendix C, eq. (C1).** Under the same perturbation
setup as Appendix B with `t = π/(4 E_max)`, the root fidelity between the
Gibbs states `ρ(β)` and `ρ̃(β)` satisfies `F(ρ(β), ρ̃(β)) ≥ e^{-β ε / t}`.

The fidelity is the paper's `F(ρ, ρ̃) = Tr sqrt(sqrt ρ ρ̃ sqrt ρ)`; the
library's `Froot` is the same quantity.  The proof chains the identity (C4)
(`froot_gibbs_eq`), the strengthened Golden--Thompson bound (C3)
(`strengthened_golden_thompson_traceNorm`) and the partition-function ratio
bound (C6)-(C7) (`mid_partition_ratio_ge`). -/
theorem gibbs_fidelity_lower_bound
    (D : ℕ) (hD : 0 < D) (H E Ht : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) (hHt : Ht.IsHermitian)
    (hHt_def : Ht = H + E) (_hE_Hermitian : E.IsHermitian)
    (β ε t Emax : ℝ) (hβ : 0 ≤ β) (ht : 0 < t) (hε0 : 0 ≤ ε)
    (_hEmax : 0 < Emax) (_htdef : t = Real.pi / (4 * Emax))
    (hE : ‖E‖ ≤ ε / t) :
    Froot (gibbsState β H) (gibbsState β Ht) ≥ Real.exp (-(β * ε / t)) := by
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hE' : ‖Ht - H‖ ≤ ε / t := by
    rw [hHt_def]
    simpa using hE
  have hA : ((-(β/2)) • H).IsHermitian := hH.smul (R := ℝ) (IsSelfAdjoint.all _)
  have hB : ((-(β/2)) • Ht).IsHermitian := hHt.smul (R := ℝ) (IsSelfAdjoint.all _)
  -- (C4): rewrite the root fidelity as the trace-norm ratio.
  rw [froot_gibbs_eq D hD H Ht hH hHt β]
  -- (C3) at `p = 2`: bound the trace norm from below by the mid partition function.
  have hGT := strengthened_golden_thompson_traceNorm D ((-(β/2)) • H) ((-(β/2)) • Ht) hA hB
  have hZmid_eq : partitionFunction β ((1 / 2 : ℝ) • (H + Ht)) =
      (Matrix.trace (NormedSpace.exp ((-(β/2)) • H + (-(β/2)) • Ht))).re := by
    rw [partitionFunction_eq_trace_exp]
    congr 1
    congr 2
    module
  rw [← hZmid_eq] at hGT
  -- (C6)-(C7): the partition-function ratio bound.
  have hratio := mid_partition_ratio_ge D hD H Ht hH hHt β ε t hβ ht hε0 hE'
  have hZZt_pos : 0 < Real.sqrt (partitionFunction β H * partitionFunction β Ht) :=
    Real.sqrt_pos.mpr (mul_pos (partitionFunction_pos β H hH) (partitionFunction_pos β Ht hHt))
  have hstep : partitionFunction β ((1 / 2 : ℝ) • (H + Ht)) /
        Real.sqrt (partitionFunction β H * partitionFunction β Ht) ≤
      Matrix.traceNorm (NormedSpace.exp ((-(β/2)) • H) *
        NormedSpace.exp ((-(β/2)) • Ht)) /
        Real.sqrt (partitionFunction β H * partitionFunction β Ht) := by
    apply div_le_div_of_nonneg_right hGT hZZt_pos.le
  exact hratio.trans hstep

end Qatlib.Papers.ThermalGibbs09.MainResults.GibbsFidelity
