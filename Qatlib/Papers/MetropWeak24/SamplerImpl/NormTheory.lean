/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MetropWeak24.SamplerImpl.Basic
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.SchattenDiamond
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

set_option backward.isDefEq.respectTransparency false

/-!
# Matrix and Superoperator Norm Bounds for Weak-Measurement Quantum Metropolis

This module establishes the trace-norm, induced star-norm, and weighted `σ`-norm
properties used in the weak-measurement quantum Metropolis analysis: variational
trace-norm duality, partial-trace contraction on rank-one operator sandwiches,
superoperator star-norm bounds from rank-one inputs, CPTP trace-norm contraction,
and the comparison `|M|_1^2 ≤ 2^n |M|_σ^2` for `σ ≥ I`.

## Main statements

* `lemma34_variational`: variational characterization of the trace norm over unitaries.
* `corollary35`: trace-norm bound `|tr_b(P |φ⟩⟨ψ| Q)|_1 ≤ 1` for contractions `P, Q`.
* `lemma36`: rank-one trace-norm bounds imply an induced superoperator star-norm bound.
* `lemma37`: partial-trace contraction sandwich `F(N) = tr_2(P (N ⊗ |w⟩⟨w|) Q)` has `|F|_⋆ ≤ 1`.
* `lemma38`: quantum channels have induced trace norm at most `1` and contract Hermitian inputs.
* `sigmaSq`, `sigmaNorm`: weighted `σ`-norm squared `Re tr(σ^{1/2} Mᴴ σ^{1/2} M)` and its square root.
* `lemma39`: `|M|_1^2 ≤ 2^n |M|_σ^2` for Hermitian `σ ≥ I`.

## References

* [Jiang and Irani, 2024][JiangIrani2024MetropWeak], Appendix B, Lemmas 34--39, pp. 29--30.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.MetropWeak24.SamplerImpl.NormTheory

open Qatlib.Papers.MetropWeak24.SamplerImpl
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Lemma 34 — variational characterization of the trace norm -/

/-- **Lemma 34**: for `M : Operator D`, `SchattenOne M` is the greatest value of
`Re tr(M U)` as `U` ranges over `D × D` unitary matrices. -/
theorem lemma34_variational {D : ℕ} (M : Operator D) :
    IsGreatest
      {x : ℝ | ∃ U : @Matrix.unitaryGroup (Fin D) (Classical.decEq (Fin D))
          (Fin.fintype D) ℂ Complex.commRing Complex.instStarRing,
        Complex.re ((M * U.val).trace) = x}
      (SchattenOne M) := by
  have h := Qatlib.Concepts.SpectralSketch.SpectrumPerturb.schattenPower_one_dual
    (k := Fin D) M
  have hpow : Qatlib.Concepts.SpectralSketch.SpectrumPerturb.schattenPower
      (1 : ℝ) M = SchattenOne M := by
    rw [Qatlib.Concepts.SpectralSketch.SpectrumPerturb.schattenPower_one,
      schattenOne_eq_traceNorm]
  have hset : {x : ℝ | ∃ U : @Matrix.unitaryGroup (Fin D) (Classical.decEq (Fin D))
        (Fin.fintype D) ℂ Complex.commRing Complex.instStarRing,
        Complex.re ((M * U.val).trace) = x}
      = {x : ℝ | ∃ U : @Matrix.unitaryGroup (Fin D) (Classical.decEq (Fin D))
        (Fin.fintype D) ℂ Complex.commRing Complex.instStarRing,
        Complex.re ((U.val * M).trace) = x} := by
    ext x
    constructor
    · rintro ⟨U, hU⟩
      exact ⟨U, by rw [Matrix.trace_mul_comm]; exact hU⟩
    · rintro ⟨U, hU⟩
      exact ⟨U, by rw [Matrix.trace_mul_comm]; exact hU⟩
  rw [hset, ← hpow]
  exact h

/-! ## Corollary 35 — partial trace of a rank-one sandwich -/

/-- **Corollary 35**: for unit vectors `φ, ψ` on `Fin Da × Fin Db` and contractions
`P, Q` (`‖P‖ ≤ 1`, `‖Q‖ ≤ 1`), `|tr_b(P |φ⟩⟨ψ| Q)|_1 ≤ 1`. -/
theorem corollary35 {Da Db : ℕ} (φ ψ : Fin Da × Fin Db → ℂ)
    (P Q : Matrix (Fin Da × Fin Db) (Fin Da × Fin Db) ℂ)
    (hφ : ∑ i, Complex.normSq (φ i) = 1)
    (hψ : ∑ i, Complex.normSq (ψ i) = 1)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    SchattenOne (PartialTrace (P * Matrix.vecMulVec φ (star ψ) * Q)) ≤ 1 := by
  classical
  obtain ⟨U, hU⟩ :=
    (lemma34_variational (PartialTrace (P * Matrix.vecMulVec φ (star ψ) * Q))).1
  have hUU : U.valᴴ * U.val = 1 := by
    have h := U.property.1
    ext i j
    by_cases hij : i = j <;>
      simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, hij] using
        congrArg (fun A : Operator Da => A i j) h
  let V := Matrix.kronecker U.val (1 : Operator Db)
  have hV : Vᴴ * V = 1 := by
    dsimp [V]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hUU, Matrix.one_kronecker_one]
  have hVnorm : ‖V‖ ≤ 1 := by
    have hs := CStarRing.norm_star_mul_self (x := V)
    have h1 : ‖(1 : Matrix (Fin Da × Fin Db) (Fin Da × Fin Db) ℂ)‖ ≤ 1 := by
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => (norm_one : ‖(1 : ℂ)‖ = 1).le
    change ‖Vᴴ * V‖ = ‖V‖ * ‖V‖ at hs
    rw [hV] at hs
    nlinarith [norm_nonneg V]
  have htrace (A : Matrix (Fin Da × Fin Db) (Fin Da × Fin Db) ℂ) :
      (PartialTrace A * U.val).trace = (A * V).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, PartialTrace,
      Fintype.sum_prod_type]
    simp only [V, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [← hU, htrace]
  calc
    _ ≤ ‖(P * Matrix.vecMulVec φ (star ψ) * Q * V).trace‖ := Complex.re_le_norm _
    _ ≤ (P * Matrix.vecMulVec φ (star ψ) * Q * V).traceNorm :=
      Matrix.abs_trace_le_traceNorm _
    _ ≤ (Matrix.vecMulVec φ (star ψ)).traceNorm := by
      simpa only [Matrix.mul_assoc] using Matrix.traceNorm_sandwich_le hP
        ((norm_mul_le Q V).trans (by nlinarith [norm_nonneg Q, norm_nonneg V]))
    _ ≤ 1 := by
      simpa [hφ, hψ] using
        Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_rankOne_le φ ψ

/-! ## Lemma 36 — rank-one data implies a star-norm bound -/

private theorem unitary_column_normSq {D : ℕ}
    (U : Matrix.unitaryGroup (Fin D) ℂ) (k : Fin D) :
    ∑ i, Complex.normSq (U.val i k) = 1 := by
  have hU : U.valᴴ * U.val = 1 := (Matrix.mem_unitaryGroup_iff').mp U.property
  have hk := congrArg (fun A : Operator D => (A k k).re) hU
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_re, Complex.normSq_apply, pow_two] using hk

private theorem inducedTraceNorm_le_of_rankOne {D : ℕ}
    (E : Operator D →ₗ[ℂ] Operator D) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u v : Fin D → ℂ, (∑ i, Complex.normSq (u i)) = 1 →
      (∑ i, Complex.normSq (v i)) = 1 →
      SchattenOne (E (Matrix.vecMulVec u (star v))) ≤ c) :
    InducedTraceNorm E ≤ c := by
  classical
  apply Real.sSup_le ?_ hc
  rintro r ⟨A, hA, rfl⟩
  let s : Fin D → ℝ := fun k =>
    Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues k)
  obtain ⟨U, V, hSVD⟩ := Matrix.exists_svd_sqrt_eigenvalues A
  have hs : ∑ k, s k = 1 := by
    exact (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.traceNorm_eq_sum_sqrt_gram
      A).symm.trans ((schattenOne_eq_traceNorm A).symm.trans hA)
  have hdecomp : A = ∑ k : Fin D, (s k : ℂ) •
      Matrix.vecMulVec (fun i => U.val i k) (star (fun j => V.val j k)) := by
    apply hSVD.trans
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    change U.val i k * (s k : ℂ) * star (V.val j k) = _
    ring
  rw [hdecomp, map_sum, schattenOne_eq_traceNorm]
  simp only [map_smul]
  apply Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_probability_sum_le
    s (fun _ => Real.sqrt_nonneg _) hs _ c
  intro k
  rw [← schattenOne_eq_traceNorm]
  exact h _ _ (unitary_column_normSq U k) (unitary_column_normSq V k)

/-- **Lemma 36**: if `E : SuperOp n` satisfies `|E(|u⟩⟨v|)|_1 ≤ c` for all unit vectors
`u, v`, then `StarNorm E ≤ c`. -/
theorem lemma36 {n : ℕ} (E : SuperOp n) (c : ℝ)
    (h : ∀ u v : Fin (2 ^ n) → ℂ, (∑ i, Complex.normSq (u i)) = 1 →
      (∑ i, Complex.normSq (v i)) = 1 →
      SchattenOne (E (Matrix.vecMulVec u (star v))) ≤ c) :
    StarNorm E ≤ c := by
  have hd : 0 < 2 ^ n := pow_pos (by decide) n
  let e : Fin (2 ^ n) → ℂ := Pi.single ⟨0, hd⟩ 1
  have he : ∑ i, Complex.normSq (e i) = 1 := by
    simp [e, Pi.single_apply, apply_ite]
  exact inducedTraceNorm_le_of_rankOne E
    ((schattenOne_nonneg _).trans (h e e he he)) h

/-! ## Lemma 37 — partial-trace sandwich has star norm ≤ 1 -/

/-- **Lemma 37**: for contractions `P, Q` (`‖P‖ ≤ 1`, `‖Q‖ ≤ 1`) and a unit vector `w`,
the superoperator `F(N) = tr_2(P (N ⊗ |w⟩⟨w|) Q)` satisfies `StarNorm F ≤ 1`. -/
theorem lemma37 {n m : ℕ}
    (P Q : Matrix (Fin (2 ^ n) × Fin (2 ^ m)) (Fin (2 ^ n) × Fin (2 ^ m)) ℂ)
    (w : Fin (2 ^ m) → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1)
    (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (F : SuperOp n)
    (hF : ∀ N : QOp n,
      F N = PartialTrace (P * Matrix.kronecker N (Matrix.vecMulVec w (star w)) * Q)) :
    StarNorm F ≤ 1 := by
  apply lemma36
  intro u v hu hv
  rw [hF]
  have hk : Matrix.kronecker (Matrix.vecMulVec u (star v))
      (Matrix.vecMulVec w (star w)) =
      Matrix.vecMulVec (fun p => u p.1 * w p.2) (star (fun p => v p.1 * w p.2)) := by
    ext i j
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, star_mul]
    ring
  rw [hk]
  apply corollary35 _ _ P Q _ _ hP hQ
  · simp only [Fintype.sum_prod_type, Complex.normSq_mul, ← Finset.mul_sum,
      hu, hw, mul_one]
  · simp only [Fintype.sum_prod_type, Complex.normSq_mul, ← Finset.mul_sum,
      hv, hw, mul_one]

/-! ## Lemma 38 — CPTP trace-norm contraction -/

private theorem channel_rankOne_le {m : ℕ} (T : QuantumChannel m m)
    (u v : Fin m → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1)
    (hv : ∑ i, Complex.normSq (v i) = 1) :
    SchattenOne (T.map (Matrix.vecMulVec u (star v))) ≤ 1 := by
  classical
  let A := T.map (Matrix.vecMulVec u (star u))
  let B := T.map (Matrix.vecMulVec v (star v))
  let X := T.map (Matrix.vecMulVec u (star v))
  let Y := T.map (Matrix.vecMulVec v (star u))
  let w : Fin 2 × Fin m → ℂ := fun p => if p.1 = 0 then u p.2 else v p.2
  have hC := T.completelyPositive 2 (Matrix.vecMulVec w (star w))
    (Matrix.posSemidef_vecMulVec_self_star w)
  let f : Fin m ⊕ Fin m → Fin 2 × Fin m := Sum.elim (fun i => (0, i)) (fun i => (1, i))
  have hH : (Matrix.fromBlocks A X Y B).PosSemidef := by
    convert hC.submatrix f using 1
    ext (i | i) (j | j) <;>
      simp [f, ChannelAmplification, w, A, B, X, Y, Matrix.vecMulVec_apply] <;> rfl
  have hXY : Xᴴ = Y := (Matrix.isHermitian_fromBlocks_iff.mp hH.isHermitian).2.1
  have htrA : A.trace = 1 := by
    rw [show A = T.map (Matrix.vecMulVec u (star u)) from rfl, T.tracePreserving]
    simpa [Matrix.trace, Matrix.vecMulVec, Complex.star_def, Complex.mul_conj,
      ← Complex.ofReal_sum] using congrArg Complex.ofReal hu
  have htrB : B.trace = 1 := by
    rw [show B = T.map (Matrix.vecMulVec v (star v)) from rfl, T.tracePreserving]
    simpa [Matrix.trace, Matrix.vecMulVec, Complex.star_def, Complex.mul_conj,
      ← Complex.ofReal_sum] using congrArg Complex.ofReal hv
  obtain ⟨U, hU⟩ := (lemma34_variational X).1
  have hUU : U.val * U.valᴴ = 1 := by
    have h := U.property.2
    ext i j
    by_cases hij : i = j <;>
      simpa [Matrix.star_eq_conjTranspose, Matrix.one_apply, hij] using
        congrArg (fun A : Operator m => A i j) h
  let R : Matrix (Fin m) (Fin m ⊕ Fin m) ℂ := Matrix.fromCols 1 (-U.valᴴ)
  have hR := (hH.mul_mul_conjTranspose_same R).trace_nonneg
  have hR' : 0 ≤ (A - U.valᴴ * Y - X * U.val + U.valᴴ * B * U.val).trace := by
    convert hR using 1
    congr 1
    simp only [R, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows,
      Matrix.conjTranspose_one, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, Matrix.one_mul, Matrix.mul_one,
      neg_mul, mul_neg, Matrix.add_mul]
    abel
  have hcycle : (U.valᴴ * B * U.val).trace = B.trace := by
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  have hcross : (U.valᴴ * Y).trace.re = (X * U.val).trace.re := by
    rw [← hXY, ← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose]
    simp
  have hr : 0 ≤ (A - U.valᴴ * Y - X * U.val + U.valᴴ * B * U.val).trace.re := hR'.1
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
    htrA, htrB, hcycle, Complex.one_re, hcross] at hr
  change SchattenOne X ≤ 1
  linarith

/-- **Lemma 38**: every quantum channel `T : QuantumChannel m m` satisfies
`InducedTraceNorm T.map ≤ 1` and contracts `SchattenOne` on Hermitian operators. -/
theorem lemma38 {m : ℕ} (T : QuantumChannel m m) :
    InducedTraceNorm T.map ≤ 1 ∧
      ∀ M : Operator m, M.IsHermitian → SchattenOne (T.map M) ≤ SchattenOne M := by
  refine ⟨?_, ?_⟩
  · exact inducedTraceNorm_le_of_rankOne T.map zero_le_one (channel_rankOne_le T)
  · intro M hM
    rw [schattenOne_eq_traceNorm, schattenOne_eq_traceNorm]
    exact Qatlib.Concepts.ReferenceError.DensityToRaw.channel_hermitian_trace_contraction
      T hM

/-! ## Lemma 39 — connecting trace norm and the σ-norm -/

/-- The weighted (`σ`-)norm square `|M|_σ^2 = Re tr(σ^{1/2} Mᴴ σ^{1/2} M)`. -/
noncomputable def sigmaSq {n : ℕ} (σ M : QOp n) : ℝ :=
  (Matrix.trace (CFC.sqrt σ * (Mᴴ * (CFC.sqrt σ * M)))).re

/-- The weighted (`σ`-)norm `|M|_σ = √(|M|_σ^2)`. -/
noncomputable def sigmaNorm {n : ℕ} (σ M : QOp n) : ℝ :=
  Real.sqrt (sigmaSq σ M)

set_option maxHeartbeats 2000000 in
/-- **Lemma 39**: for Hermitian `σ` with `1 ≤ σ` and every `n`-qubit operator `M`,
`|M|_1^2 ≤ 2^n |M|_σ^2`. -/
theorem lemma39 {n : ℕ} (σ M : QOp n) (hσ : σ.IsHermitian) (hσI : 1 ≤ σ) :
    SchattenOne M ^ 2 ≤ (2 : ℝ) ^ n * (sigmaNorm σ M) ^ 2 := by
  have trace_prod_nonneg (A B : QOp n) (hA : A.PosSemidef) (hB : B.PosSemidef) :
      0 ≤ (Matrix.trace (A * B)).re := by
    have hroot : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
    have hp := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
    rw [hroot.eq, Matrix.trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self A hA.nonneg] at hp
    exact (Complex.nonneg_iff.mp hp).1
  have hσpos : σ.PosSemidef :=
    ⟨hσ, ((show 0 ≤ σ from zero_le_one.trans hσI).posSemidef).2⟩
  have hS : (CFC.sqrt σ).PosSemidef := by
    rw [CFC.sqrt_eq_real_sqrt σ hσpos.nonneg,
      cfcₙ_eq_cfc (by fun_prop) (by simp), hσ.cfc_eq,
      Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change 0 ≤ (Real.sqrt (hσ.eigenvalues i) : ℂ)
    exact_mod_cast Real.sqrt_nonneg (hσ.eigenvalues i)
  have hSI : (1 : QOp n) ≤ CFC.sqrt σ := by
    simpa only [CFC.sqrt_one] using CFC.monotone_sqrt hσI
  have hD : (CFC.sqrt σ - 1).PosSemidef := (sub_nonneg.mpr hSI).posSemidef
  have hfirst := trace_prod_nonneg (CFC.sqrt σ)
    (Mᴴ * (CFC.sqrt σ - 1) * M) hS (hD.conjTranspose_mul_mul_same M)
  have hsecond := trace_prod_nonneg (CFC.sqrt σ - 1) (Mᴴ * M) hD
    (Matrix.posSemidef_conjTranspose_mul_self M)
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.trace_sub, Complex.sub_re, Matrix.mul_assoc] at hfirst hsecond
  have hweighted : (Matrix.trace (Mᴴ * M)).re ≤ sigmaSq σ M := by
    unfold sigmaSq
    linarith
  have hgram : 0 ≤ (Matrix.trace (Mᴴ * M)).re :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self M).trace_nonneg).1
  have hnorm : (sigmaNorm σ M) ^ 2 = sigmaSq σ M :=
    Real.sq_sqrt (hgram.trans hweighted)
  have htrace : (Matrix.trace (Mᴴ * M)).re =
      ∑ i, (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i := by
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues
      (Matrix.isHermitian_conjTranspose_mul_self M)]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    change (Complex.ofReal ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)).re = _
    rfl
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (2 ^ n)))
    (fun _ => (1 : ℝ))
    (fun i => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M _)]
    at hcs
  rw [schattenOne_eq_traceNorm,
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.traceNorm_eq_sum_sqrt_gram]
  change (∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)) ^ 2 ≤ _
  rw [hnorm]
  calc
    _ ≤ (2 ^ n : ℕ) * (Matrix.trace (Mᴴ * M)).re := by
      rw [htrace]
      exact hcs
    _ ≤ (2 : ℝ) ^ n * sigmaSq σ M := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        mul_le_mul_of_nonneg_left hweighted (show 0 ≤ (2 ^ n : ℝ) by positivity)

end Qatlib.Papers.MetropWeak24.SamplerImpl.NormTheory
