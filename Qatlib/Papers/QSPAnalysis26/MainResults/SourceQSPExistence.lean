/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Topology.Sequences

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Signal Processing Phase Existence and Real-Target Completion

This module establishes the polynomial existence and real-target completion results
for quantum signal processing (Theorem 3.1 and Corollary 3.2), expressed in the
division-free response convention where `(P, Q)` satisfies `CompletedPair d P Q`.

## Main statements

* `theorem3_1_qsp_existence`: phase-factor existence from `CompletedPair` hypotheses.
* `responsePairNorm_eval_real`: pointwise unitarity `|P(x)|^2 + (1 - x^2)|Q(x)|^2 = 1` on `[-1, 1]`.
* `corollary3_2_of_strict`: real-target completion for strictly bounded parity polynomials.
* `corollary3_2_real_target`: full non-strict real-target completion for `|f(x)| <= 1` on `[-1, 1]`.

## References

* [Lin, 2026][Lin2026QSPAnalysis], Theorem 3.1 and Corollary 3.2, p. 4.
-/

set_option autoImplicit false
noncomputable section

open Polynomial

namespace Qatlib.Papers.QSPAnalysis26.MainResults.SourceQSPExistence

open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- Theorem 3.1: QSP phase-sequence existence for a polynomial pair `(P, Q)` satisfying
the degree, parity, and polynomial normalization conditions `P * P_bar + (1 - X^2) * Q * Q_bar = 1`. -/
theorem theorem3_1_qsp_existence {d : ℕ} (P Q : Polynomial ℂ)
    (hdegP : P.degree ≤ (d : WithBot ℕ))
    (hdegQ : Q.degree < (d : WithBot ℕ))
    (hparP : HasResponseParity d P)
    (hparQ : HasResponseParity (d + 1) Q)
    (hnorm : responsePairNorm P Q = 1) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = d ∧ responseP base zs = P ∧ responseQ base zs = Q := by
  exact completedPair_iff_response.mp
    ⟨hdegP, hdegQ, hparP, hparQ, hnorm⟩

/-- Pointwise evaluation of the polynomial normalization identity: if
`responsePairNorm P Q = 1`, then `|P(x)|^2 + (1 - x^2) |Q(x)|^2 = 1` for all `x ∈ [-1, 1]`. -/
theorem responsePairNorm_eval_real {P Q : Polynomial ℂ}
    (hnorm : responsePairNorm P Q = 1) {x : ℝ} (_hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Complex.normSq (P.eval (x : ℂ)) + (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) = 1 := by
  have h1 := conjugatePolynomial_eval_real P x
  have h2 := conjugatePolynomial_eval_real Q x
  have he := congrArg (Polynomial.eval (x : ℂ)) hnorm
  simp only [responsePairNorm, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, h1, h2] at he
  have hp : P.eval (x : ℂ) * star (P.eval (x : ℂ)) =
      ((Complex.normSq (P.eval (x : ℂ)) : ℝ) : ℂ) := by
    simpa using Complex.mul_conj (P.eval (x : ℂ))
  have hq : Q.eval (x : ℂ) * star (Q.eval (x : ℂ)) =
      ((Complex.normSq (Q.eval (x : ℂ)) : ℝ) : ℂ) := by
    simpa using Complex.mul_conj (Q.eval (x : ℂ))
  have hQ : (1 - (x : ℂ) ^ 2) * Q.eval (x : ℂ) * star (Q.eval (x : ℂ)) =
      (((1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) : ℝ) : ℂ) := by
    rw [mul_assoc, hq]
    push_cast
    ring
  rw [hp, hQ] at he
  have heR := congrArg Complex.re he
  have hpow : ((x : ℂ) ^ 2).re = x ^ 2 := by
    rw [show (x : ℂ) ^ 2 = ((x ^ 2 : ℝ) : ℂ) from (Complex.ofReal_pow x 2).symm]
    exact Complex.ofReal_re (x ^ 2)
  simpa [hpow] using heR

/-- Corollary 3.2 (strictly bounded case): a real polynomial `f` of degree at most `d`,
parity `d mod 2`, and `|f(x)| < 1` on `[-1, 1]` admits a completed QSP pair `(P, Q)`
with `Re(P(x)) = f(x)`. -/
theorem corollary3_2_of_strict {d : ℕ} {f : Polynomial ℝ}
    (hfdeg : f.degree ≤ (d : WithBot ℕ))
    (hfpar : HasRealParity d f)
    (hfbdd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f.eval x| < 1) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      ∀ x : ℝ, (P.eval (x : ℂ)).re = f.eval x := by
  obtain ⟨P, Q, hpair, _hpoly, hre⟩ :=
    exists_completedPair_of_strict hfdeg hfpar hfbdd
  exact ⟨P, Q, hpair, hre⟩

/-- At a fixed input, both responses depend continuously on the finitely many phase parameters. -/
private theorem continuous_response_eval {T : Type*} [TopologicalSpace T]
    (d : ℕ) (x : ℂ) (base : T → ℂ) (zs : T → Fin d → ℂ)
    (hb : Continuous base) (hz : ∀ i, Continuous (fun t => zs t i)) :
    Continuous (fun t => (responseP (base t) (List.ofFn (zs t))).eval x) ∧
      Continuous (fun t => (responseQ (base t) (List.ofFn (zs t))).eval x) := by
  induction d with
  | zero => simpa using And.intro hb (continuous_const : Continuous (fun _ : T => (0 : ℂ)))
  | succ d ih =>
    obtain ⟨hp, hq⟩ := ih (fun t i => zs t i.succ) (fun i => hz i.succ)
    simp only [List.ofFn_succ, responseP_cons, responseQ_cons, eval_mul, eval_add,
      eval_sub, eval_C, eval_X, eval_one, eval_pow]
    exact ⟨(hz 0).mul ((continuous_const.mul hp).add (continuous_const.mul hq)),
      (hz 0).star.mul (hp.sub (continuous_const.mul hq))⟩

/-- Corollary 3.2: a real polynomial `f` of degree at most `d` (`d ≥ 1`), parity `d mod 2`,
and `|f(x)| ≤ 1` on `[-1, 1]` is the real part of `P` for a completed QSP pair `(P, Q)`. -/
theorem corollary3_2_real_target {d : ℕ} (hd : 1 ≤ d) {f : Polynomial ℝ}
    (hfdeg : f.degree ≤ (d : WithBot ℕ))
    (hfpar : HasRealParity d f)
    (hfbdd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f.eval x| ≤ 1) :
    ∃ P Q : Polynomial ℂ, CompletedPair d P Q ∧
      ∀ x : ℝ, (P.eval (x : ℂ)).re = f.eval x := by
  classical
  let r (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) + d)
  have hr (n : ℕ) : 0 ≤ r n ∧ r n < 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd' : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact ⟨div_nonneg hn (by positivity), (div_lt_one (by positivity)).mpr (by linarith)⟩
  have hrlim : Filter.Tendsto r Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (d : ℝ)
  have hcircle (z : ℂ) (hz : IsPhase z) : z ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    have hh := IsPhase.normSq hz
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg z]
  -- Synthesize the strict contractions in a fixed compact space of phase parameters.
  have happrox (n : ℕ) : ∃ a : Circle × (Fin d → Circle),
      ∀ x : ℝ,
        ((responseP (a.1 : ℂ) (List.ofFn (fun i => (a.2 i : ℂ)))).eval (x : ℂ)).re =
          r n * f.eval x := by
    have hdeg : (C (r n) * f).degree ≤ (d : WithBot ℕ) :=
      degree_le_of_natDegree_le ((natDegree_C_mul_le _ _).trans
        (natDegree_le_of_degree_le hfdeg))
    have hpar : HasRealParity d (C (r n) * f) := by
      change f.comp (-X) = C ((-1 : ℝ) ^ d) * f at hfpar
      simp only [HasRealParity, mul_comp, C_comp, hfpar]
      ring
    have hbdd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(C (r n) * f).eval x| < 1 := by
      intro x hx
      simp only [eval_mul, eval_C, abs_mul, abs_of_nonneg (hr n).1]
      exact (mul_le_mul_of_nonneg_left (hfbdd x hx) (hr n).1).trans_lt
        (by simpa using (hr n).2)
    obtain ⟨P, Q, hpair, hre⟩ := corollary3_2_of_strict hdeg hpar hbdd
    obtain ⟨base, zs, hb, hzs, hlen, hP, _hQ⟩ := exists_response_of_completedPair hpair
    subst d
    let v : Fin zs.length → Circle := fun i => ⟨zs.get i, hcircle _ (hzs _ (List.get_mem ..))⟩
    refine ⟨(⟨base, hcircle base hb⟩, v), ?_⟩
    intro x
    have hv : List.ofFn (fun i => (v i : ℂ)) = zs := List.ofFn_get zs
    change ((responseP base (List.ofFn (fun i => (v i : ℂ)))).eval (x : ℂ)).re = _
    rw [hv, hP, hre]
    simp only [eval_mul, eval_C]
  choose a ha using happrox
  obtain ⟨aLim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq a
  have hphase (z : Circle) : IsPhase (z : ℂ) := isPhase_iff_normSq.mpr z.normSq_coe
  let zs := List.ofFn (fun i => (aLim.2 i : ℂ))
  have hzs : ∀ z ∈ zs, IsPhase z := by
    simp only [zs, List.forall_mem_ofFn_iff]
    exact fun i => hphase (aLim.2 i)
  refine ⟨responseP (aLim.1 : ℂ) zs, responseQ (aLim.1 : ℂ) zs,
    ?_, ?_⟩
  · simpa only [zs, List.length_ofFn] using completedPair_response (hphase aLim.1) zs hzs
  · intro x
    -- The same phase subsequence gives the required limit at every real input.
    have hc := (continuous_response_eval d (x : ℂ)
      (fun t : Circle × (Fin d → Circle) => (t.1 : ℂ))
      (fun t i => (t.2 i : ℂ)) (by fun_prop) (by intro i; fun_prop)).1
    have heval := (Complex.continuous_re.comp hc).continuousAt.tendsto.comp hlim
    have htarget := (hrlim.comp hφ.tendsto_atTop).mul_const (f.eval x)
    simp only [one_mul] at htarget
    exact tendsto_nhds_unique heval (htarget.congr (fun n => (ha (φ n) x).symm))

end Qatlib.Papers.QSPAnalysis26.MainResults.SourceQSPExistence
