/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric.ProvedMath
public import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
public import QuantumInfo.Channels.Dual

@[expose] public section

/-!
# Measurement and partial-trace contractions for trace distance

Paper version: **arXiv:1106.1445v8**, [Wilde2017], Corollary 9.1.1 and Corollary 9.1.2,
§9.1.5, pp. 257–258.
<https://arxiv.org/abs/1106.1445v8>

Corollary 9.1.1 bounds the change of a measurement probability by one half of the trace
norm of the difference between the two states. Corollary 9.1.2 states that discarding a subsystem cannot
increase the trace distance.  Both statements are proved here for finite index types with a
non-empty carrier, using the genuine matrix trace norm `Matrix.traceNorm` (the Schatten
one-norm), not a coordinatewise maximum norm.

For Corollary 9.1.1 we split the Hermitian difference `ρ - σ` into its positive and negative
spectral parts.  The positive part is measured by the effect at most once, while the negative
part gives a nonnegative contribution, and the two parts have equal trace because `ρ` and `σ`
are normalized.  This yields the sharp constant `1/2` uniformly in the dimension.

For Corollary 9.1.2 we invoke the trace-norm contraction of the partial trace on Hermitian
inputs and rewrite the marginal matrix as a partial trace.

The results are stated with the dimension-independent constants outside the universal
quantifiers, so the constants themselves are part of the public interface.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.ReferenceError.DensityToRaw
open scoped BigOperators ComplexOrder

noncomputable section

/-- Auxiliary upper bound for the effect expectation difference:
`Tr(E ρ) - Tr(E σ) ≤ (1/2) ‖ρ - σ‖₁` for an effect `0 ≤ E ≤ 1` and density operators
`ρ`, `σ` on a non-empty finite index type.  This is the positive/negative spectral-part
estimate used to prove the sharp form of Corollary 9.1.1. -/
private theorem effect_expectation_sub_le
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (ρ σ : Dens I) (E : Op I) (hE : IsEffect E) :
    (Matrix.trace (E * ρ.val)).re - (Matrix.trace (E * σ.val)).re ≤
      (1 / 2 : ℝ) * traceNormDiff ρ.val σ.val := by
  set X : Op I := ρ.val - σ.val with hXdef
  have hXherm : X.IsHermitian := ρ.property.1.1.sub σ.property.1.1
  set P : Op I := HermitianSplit.posPart hXherm with hPdef
  set N : Op I := HermitianSplit.negPart hXherm with hNdef
  have hPpsd : P.PosSemidef := by
    rw [hPdef]
    unfold HermitianSplit.posPart
    refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
    intro i
    exact_mod_cast le_max_right (hXherm.eigenvalues i) 0
  have hNpsd : N.PosSemidef := by
    rw [hNdef]
    unfold HermitianSplit.negPart
    refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
    intro i
    exact_mod_cast le_max_right (-hXherm.eigenvalues i) 0
  have hdecomp : P - N = X := by
    rw [hPdef, hNdef]
    exact HermitianSplit.sub_posPart_negPart hXherm
  have htrX : Matrix.trace X = 0 := by
    rw [hXdef, Matrix.trace_sub, ρ.property.2, σ.property.2, sub_self]
  have htrPN : Matrix.trace P = Matrix.trace N := by
    have h := congrArg Matrix.trace hdecomp
    rw [Matrix.trace_sub, htrX] at h
    exact sub_eq_zero.mp h
  have hPtr : (Matrix.trace P).re = P.traceNorm := by
    exact (congrArg Complex.re hPpsd.traceNorm_eq_trace).symm
  have hNtr : (Matrix.trace N).re = N.traceNorm := by
    exact (congrArg Complex.re hNpsd.traceNorm_eq_trace).symm
  have hleP : (Matrix.trace (E * P)).re ≤ (Matrix.trace P).re := by
    have hnonneg : 0 ≤ (Matrix.trace ((1 - E) * P)).re :=
      (RCLike.nonneg_iff.mp (Matrix.PosSemidef.trace_mul_nonneg hE.2 hPpsd)).1
    have hlin : Matrix.trace ((1 - E) * P) =
        Matrix.trace P - Matrix.trace (E * P) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
    rw [hlin, Complex.sub_re] at hnonneg
    linarith
  have hnonnegN : 0 ≤ (Matrix.trace (E * N)).re :=
    (RCLike.nonneg_iff.mp (Matrix.PosSemidef.trace_mul_nonneg hE.1 hNpsd)).1
  have hmain : (Matrix.trace (E * X)).re ≤ (1 / 2 : ℝ) * X.traceNorm := by
    have hsplit : Matrix.trace (E * X) =
        Matrix.trace (E * P) - Matrix.trace (E * N) := by
      conv_lhs => rw [← hdecomp]
      rw [Matrix.mul_sub, Matrix.trace_sub]
    rw [hsplit, Complex.sub_re]
    have hnorm : X.traceNorm = P.traceNorm + N.traceNorm := by
      rw [hXdef]
      exact HermitianSplit.traceNorm_sub_posPart_negPart hXherm
    have hPN : P.traceNorm = N.traceNorm := by
      rw [← hPtr, ← hNtr, htrPN]
    rw [hnorm, hPN]
    nlinarith [hleP, hnonnegN, hPtr, hNtr, hPN]
  have hdiff : (Matrix.trace (E * X)).re =
      (Matrix.trace (E * ρ.val)).re - (Matrix.trace (E * σ.val)).re := by
    rw [hXdef, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have hnormX : X.traceNorm = traceNormDiff ρ.val σ.val := by
    rw [hXdef]
    rfl
  rw [hdiff, hnormX] at hmain
  exact hmain

/-- **Corollary 9.1.1, sharp form (9.56)** — [Wilde2017], arXiv:1106.1445v8, fixed PDF
p. 257. For density operators `ρ` and `σ` on a non-empty finite index type and any effect
`E` with `0 ≤ E ≤ 1`, the measurement probability of `ρ` is at most half the trace norm
of `ρ - σ` below that of `σ`:
`Tr(E ρ) ≥ Tr(E σ) - (1/2) ‖ρ - σ‖₁`. -/
theorem measurement_close_states
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (ρ σ : Dens I) (E : Op I) (hE : IsEffect E) :
    (Matrix.trace (E * ρ.val)).re ≥
      (Matrix.trace (E * σ.val)).re - (1 / 2 : ℝ) * traceNormDiff ρ.val σ.val := by
  have hswap := effect_expectation_sub_le σ ρ E hE
  have hsymm : traceNormDiff (σ : Op I) (ρ : Op I) =
      traceNormDiff (ρ : Op I) (σ : Op I) := by
    unfold traceNormDiff
    rw [← neg_sub, Matrix.traceNorm_neg]
  have hswap' : (Matrix.trace (E * (σ : Op I))).re -
      (Matrix.trace (E * (ρ : Op I))).re ≤
      (1 / 2 : ℝ) * traceNormDiff (ρ : Op I) (σ : Op I) := by
    rw [hsymm] at hswap
    exact hswap
  have hle : (Matrix.trace (E * (σ : Op I))).re ≤
      (1 / 2 : ℝ) * traceNormDiff (ρ : Op I) (σ : Op I) +
        (Matrix.trace (E * (ρ : Op I))).re :=
    sub_le_iff_le_add.mp hswap'
  change (Matrix.trace (E * (σ : Op I))).re -
      (1 / 2 : ℝ) * traceNormDiff (ρ : Op I) (σ : Op I) ≤
    (Matrix.trace (E * (ρ : Op I))).re
  exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hle)

/-- **Corollary 9.1.1, weaker form (9.57)** — [Wilde2017], arXiv:1106.1445v8, fixed PDF
p. 257. Replacing the factor `1/2` by `1` gives the second displayed inequality of the
corollary. -/
theorem measurement_close_states_weak
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (ρ σ : Dens I) (E : Op I) (hE : IsEffect E) :
    (Matrix.trace (E * ρ.val)).re ≥
      (Matrix.trace (E * σ.val)).re - traceNormDiff ρ.val σ.val := by
  have h := measurement_close_states ρ σ E hE
  have hT : (1 / 2 : ℝ) * traceNormDiff ρ.val σ.val ≤ traceNormDiff ρ.val σ.val := by
    have hn : 0 ≤ traceNormDiff ρ.val σ.val := Matrix.traceNorm_nonneg _
    nlinarith
  exact le_trans (sub_le_sub_left hT (Matrix.trace (E * σ.val)).re) h

/-- The uniform-constant form of Corollary 9.1.1: a single positive constant `1/2` works for
all finite non-empty dimensions, all density operators and all effects. -/
theorem exists_uniform_measurement_close_states :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
        (ρ σ : Dens I) (E : Op I), IsEffect E →
        (Matrix.trace (E * ρ.val)).re ≥
          (Matrix.trace (E * σ.val)).re - C * traceNormDiff ρ.val σ.val := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro I _ _ _ ρ σ E hE
  exact measurement_close_states ρ σ E hE

/-- **Corollary 9.1.2** — [Wilde2017], arXiv:1106.1445v8, fixed PDF p. 258. Discarding the
right subsystem does not increase the trace norm of the difference of two density operators on
a non-empty finite bipartite index type. -/
theorem traceNormDiff_marginR_le
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (ρ σ : Dens (A × B)) :
    traceNormDiff (marginR ρ).val (marginR σ).val ≤ traceNormDiff ρ.val σ.val := by
  have hρ : (marginR ρ).val = Matrix.traceRight ρ.val := by
    show (localState (state ρ).traceRight).val = Matrix.traceRight ρ.val
    rw [localState_val]
    change ((state ρ).M.traceRight).mat = Matrix.traceRight ρ.val
    rw [HermitianMat.traceRight_mat]
    change Matrix.traceRight (state ρ).m = Matrix.traceRight ρ.val
    rw [state_m]
  have hσ : (marginR σ).val = Matrix.traceRight σ.val := by
    show (localState (state σ).traceRight).val = Matrix.traceRight σ.val
    rw [localState_val]
    change ((state σ).M.traceRight).mat = Matrix.traceRight σ.val
    rw [HermitianMat.traceRight_mat]
    change Matrix.traceRight (state σ).m = Matrix.traceRight σ.val
    rw [state_m]
  rw [hρ, hσ]
  unfold traceNormDiff
  have hX : (ρ.val - σ.val).IsHermitian := ρ.property.1.1.sub σ.property.1.1
  have h := traceRight_hermitian_trace_contraction (ρ.val - σ.val) hX
  rw [Matrix.traceRight_sub] at h
  exact h

/-- The uniform-constant form of Corollary 9.1.2: the constant `1` is independent of the two
subsystem dimensions. -/
theorem exists_uniform_traceNormDiff_marginR :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
        [Nonempty A] [Nonempty B] (ρ σ : Dens (A × B)),
        traceNormDiff (marginR ρ).val (marginR σ).val ≤ C * traceNormDiff ρ.val σ.val := by
  refine ⟨1, one_pos, ?_⟩
  intro A B _ _ _ _ _ _ ρ σ
  simpa using traceNormDiff_marginR_le ρ σ

end

end Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric
