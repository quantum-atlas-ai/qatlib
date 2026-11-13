/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedStat
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxTransfer
import Qatlib.Concepts.QsvtCore.PolyApprox.EvenIntervalSOS

/-!
# Real polynomial completion and sufficiency

This module completes an even polynomial `A` and an odd polynomial `Qt` satisfying the weighted
bound `A(x)^2 + (1 - x^2) * Qt(x)^2 ≤ 1` on `[-1, 1]`. The theorem `lcRealCompletion` expresses
the remaining polynomial as `b^2 + (1 - X^2) * c^2`, with even `b`, odd `c`, and controlled
degrees.

The completed pair is then synthesized into complex response phases and transferred to the
repository amplitude `lcRepoAmp`. The resulting theorem `achievableSufficiencyCore` supplies the
polynomial sufficiency step for the quantum signal processing setting of [LowChuang2017], with
positive even degree and explicit endpoint rotations.

## Main statements

* `map_eval_ofReal` relates complex evaluation of a mapped real polynomial to real evaluation.
* `lcRealCompletion` constructs the parity-preserving weighted sum-of-squares completion.
* `achievableSufficiencyCore` realizes the prescribed real and imaginary polynomial components
  using `lcRepoAmp`.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.QsVtMain

set_option autoImplicit false
set_option maxHeartbeats 800000

open Polynomial
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib

namespace Qatlib.Concepts.QspSimulation.Achievability

/-- An even power `2 * m` of real `-1` equals one. -/
private theorem neg_one_pow_even_real {m : ℕ} : (-1 : ℝ) ^ (2 * m) = 1 :=
  (even_two_mul m).neg_one_pow

/-- An odd power `2 * m + 1` of real `-1` equals `-1`. -/
private theorem neg_one_pow_odd_real {m : ℕ} : (-1 : ℝ) ^ (2 * m + 1) = -1 :=
  (odd_two_mul_add_one m).neg_one_pow

/-- An even power `2 * m` of complex `-1` equals one. -/
private theorem neg_one_pow_even_complex {m : ℕ} : (-1 : ℂ) ^ (2 * m) = 1 :=
  (even_two_mul m).neg_one_pow

/-- An odd power `2 * m + 1` of complex `-1` equals `-1`. -/
private theorem neg_one_pow_odd_complex {m : ℕ} : (-1 : ℂ) ^ (2 * m + 1) = -1 :=
  (odd_two_mul_add_one m).neg_one_pow

/-- Composing a constant complex polynomial with any complex polynomial leaves the constant
polynomial unchanged. -/
theorem lcC_comp (z : ℂ) (p : Polynomial ℂ) :
    (Polynomial.C z).comp p = Polynomial.C z := by
  simp [Polynomial.comp]

/-- Mapping a real polynomial to complex coefficients commutes with composition by `-X`. -/
private theorem comp_negX_map_real (p : Polynomial ℝ) :
    (p.map Complex.ofRealHom).comp (-(X : Polynomial ℂ))
      = (p.comp (-(X : Polynomial ℝ))).map Complex.ofRealHom := by
  have hX : (-(X : Polynomial ℝ)).map Complex.ofRealHom
      = -(X : Polynomial ℂ) := by
    rw [Polynomial.map_neg, Polynomial.map_X]
  rw [← hX, ← Polynomial.map_comp]

/-- Evaluating the complex coefficient map of a real polynomial at a real argument equals the
complex embedding of its real evaluation. -/
theorem map_eval_ofReal (p : Polynomial ℝ) (x : ℝ) :
    (p.map Complex.ofRealHom).eval ((x : ℝ) : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map,
    show ((x : ℝ) : ℂ) = Complex.ofRealHom x from rfl, Polynomial.eval₂_hom]
  exact Complex.ofRealHom_eq_coe (p.eval x)

/-- A real polynomial mapped to complex coefficients is fixed by coefficientwise conjugation. -/
private theorem conj_map_real (p : Polynomial ℝ) :
    conjugatePolynomial (p.map Complex.ofRealHom) = p.map Complex.ofRealHom := by
  have hring : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext r
    exact lcStar_ofReal r
  simp only [conjugatePolynomial, Polynomial.map_map]
  rw [hring]

/-- Applying `lcExp` to the argument of a unit-modulus complex number recovers that number. -/
private theorem lcExp_arg_of_isPhase {z : ℂ}
    (hz : Qatlib.Concepts.PhaseGeometry.Phase.IsPhase z) : lcExp z.arg = z := by
  rw [lcExp_eq_anglePhase]
  exact Qatlib.Concepts.QsvtCore.QsVtMain.anglePhase_arg_of_isPhase hz

/-- If a real polynomial has natural degree at most `n`, its square has natural degree at most
`2 * n`. -/
private theorem natDegree_sq_le {p : Polynomial ℝ} {n : ℕ} (h : p.natDegree ≤ n) :
    (p ^ 2).natDegree ≤ 2 * n := by
  have := Polynomial.natDegree_pow_le (p := p) (n := 2)
  omega

/-- For positive even `d`, the stated parity, degree, and interval bounds complete `1 - A^2 - (1
- X^2) * Qt^2` as `b^2 + (1 - X^2) * c^2`. The completion has even `b` of degree at most `d`
and odd `c` that is zero or satisfies `c.degree + 1 ≤ d`. -/
theorem lcRealCompletion (d : ℕ) (A Qt : Polynomial ℝ) (hd : Even d) (hp : 0 < d)
    (hAeven : A.comp (-X) = A) (hQtodd : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (d : WithBot ℕ)) (hQtdeg : Qt.degree < (d : WithBot ℕ))
    (hcond : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1) :
    ∃ b c : Polynomial ℝ,
      1 - A ^ 2 - (1 - X ^ 2) * Qt ^ 2 = b ^ 2 + (1 - X ^ 2) * c ^ 2 ∧
      b.degree ≤ (d : WithBot ℕ) ∧ (c = 0 ∨ c.degree + 1 ≤ (d : WithBot ℕ)) ∧
      b.comp (-X) = b ∧ c.comp (-X) = -c := by
  obtain ⟨m, hm⟩ := hd
  have hd2 : d = 2 * m := by omega
  have hd1 : 1 ≤ d := by omega

  have hrpar : HasRealParity 0 (1 - A ^ 2 - (1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2) := by
    show (1 - A ^ 2 - (1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2).comp (-X)
        = Polynomial.C ((-1 : ℝ) ^ 0) * (1 - A ^ 2 - (1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2)
    rw [pow_zero, Polynomial.C_1, one_mul]
    simp only [sub_comp, one_comp, pow_comp, X_comp, mul_comp, hAeven, hQtodd, neg_sq]
  have hrdeg : (1 - A ^ 2 - (1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2).degree
      ≤ ((2 * d : ℕ) : WithBot ℕ) := by
    apply Polynomial.degree_le_of_natDegree_le
    have hnA : A.natDegree ≤ d := Polynomial.natDegree_le_of_degree_le hAdeg
    have hnQ : Qt.natDegree ≤ d - 1 := by
      by_cases hz : Qt = 0
      · subst hz
        simp only [Polynomial.natDegree_zero]
        omega
      · rw [Polynomial.degree_eq_natDegree hz] at hQtdeg
        have : Qt.natDegree < d := by exact_mod_cast hQtdeg
        omega
    have h1 : (1 - A ^ 2).natDegree ≤ 2 * d := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      have hA2 : (A ^ 2).natDegree ≤ 2 * d := natDegree_sq_le hnA
      simp only [Polynomial.natDegree_one]
      omega
    have h2 : ((1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2).natDegree ≤ 2 * d := by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      have hX : ((1 - (X : Polynomial ℝ) ^ 2)).natDegree ≤ 2 := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        simp only [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]
        omega
      have hQ2 : (Qt ^ 2).natDegree ≤ 2 * (d - 1) := natDegree_sq_le hnQ
      omega
    have h3 := Polynomial.natDegree_sub_le (1 - A ^ 2)
      ((1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2)
    omega
  have hrnn : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (1 - A ^ 2 - (1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2).eval x := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have h := hcond x (Set.mem_Icc.mpr ⟨hx1, hx2⟩)
    rw [show (1 : ℝ) - x * x = 1 - x ^ 2 from by ring,
      show A.eval x * A.eval x = A.eval x ^ 2 from by ring,
      show Qt.eval x * Qt.eval x = Qt.eval x ^ 2 from by ring] at h
    simp only [eval_sub, eval_mul, eval_pow, eval_one, eval_X]
    linarith

  obtain ⟨b, c, hsos, hbdeg, hcdeg, hbpar, hcpar⟩ :=
    Qatlib.Concepts.QsvtCore.PolyApprox.even_interval_sos_with_source_parities
      (1 - A ^ 2 - (1 - (X : Polynomial ℝ) ^ 2) * Qt ^ 2) d hrpar hrdeg hrnn
  have hbeven : b.comp (-X) = b := by
    have h1 : (-1 : ℝ) ^ d = 1 := by rw [hd2]; exact neg_one_pow_even_real
    have h : b.comp (-X) = Polynomial.C ((-1 : ℝ) ^ d) * b := hbpar
    rwa [h1, Polynomial.C_1, one_mul] at h
  have hcoddd : c.comp (-X) = -c := by
    have h1 : (-1 : ℝ) ^ (d + 1) = -1 := by rw [hd2]; exact neg_one_pow_odd_real
    have h : c.comp (-X) = Polynomial.C ((-1 : ℝ) ^ (d + 1)) * c := hcpar
    rwa [h1, Polynomial.C_neg, Polynomial.C_1, neg_one_mul] at h
  exact ⟨b, c, hsos, hbdeg, hcdeg, hbeven, hcoddd⟩

/-- An even `A` and odd `Qt` satisfying the stated degree and weighted interval bounds are
realized by `lcRepoAmp` with endpoint rotations and a phase list whose length plus one is
`d`. The amplitude is `A(x) + Complex.I * sqrt (1 - x * x) * Qt(x)` on `[-1, 1]`,
interpreted using `realEval`. -/
theorem achievableSufficiencyCore (d : ℕ) (A Qt : Polynomial ℝ) (hd : Even d) (hp : 0 < d)
    (hAeven : A.comp (-X) = A) (hQtodd : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (d : WithBot ℕ)) (hQtdeg : Qt.degree < (d : WithBot ℕ))
    (hcond : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1) :
    ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = d ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        lcRepoAmp γ₀ γ₁ psis x =
          realEval A (Complex.ofReal x)
          + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt (Complex.ofReal x) := by
  obtain ⟨b, c, hsos, hbdeg, hcdeg, hbeven, hcoddd⟩ :=
    lcRealCompletion d A Qt hd hp hAeven hQtodd hAdeg hQtdeg hcond
  obtain ⟨m, hm⟩ := hd
  have hd2 : d = 2 * m := by omega
  have hd1 : 1 ≤ d := by omega

  have hI2C : (Polynomial.C (Complex.I) * Polynomial.C (Complex.I) : Polynomial ℂ) = -1 := by
    rw [← Polynomial.C_mul, Complex.I_mul_I]
    simp
  have hSOSc : (1 : Polynomial ℂ) - (A.map Complex.ofRealHom) ^ 2
        - (1 - (X : Polynomial ℂ) ^ 2) * (Qt.map Complex.ofRealHom) ^ 2
      = (b.map Complex.ofRealHom) ^ 2
        + (1 - (X : Polynomial ℂ) ^ 2) * (c.map Complex.ofRealHom) ^ 2 := by
    have h := congrArg (fun p : Polynomial ℝ => p.map Complex.ofRealHom) hsos
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X] at h
    exact h
  have hnorm : responsePairNorm
      (A.map Complex.ofRealHom + Polynomial.C (Complex.I) * (b.map Complex.ofRealHom))
      (Qt.map Complex.ofRealHom + Polynomial.C (Complex.I) * (c.map Complex.ofRealHom)) = 1 := by
    simp only [responsePairNorm, conjugatePolynomial_add, conjugatePolynomial_mul,
      conjugatePolynomial_C, conj_map_real, lcStar_I, Polynomial.C_neg, Polynomial.C_1,
      neg_mul]
    linear_combination -hSOSc
      - ((b.map Complex.ofRealHom) ^ 2 + (1 - (X : Polynomial ℂ) ^ 2)
          * (c.map Complex.ofRealHom) ^ 2) * hI2C
  have hEven1c : (-1 : ℂ) ^ d = 1 := by rw [hd2]; exact neg_one_pow_even_complex
  have hOdd1c : (-1 : ℂ) ^ (d + 1) = -1 := by rw [hd2]; exact neg_one_pow_odd_complex
  have hPcpar : HasResponseParity d
      (A.map Complex.ofRealHom + Polynomial.C (Complex.I) * (b.map Complex.ofRealHom)) := by
    show (A.map Complex.ofRealHom + Polynomial.C (Complex.I) * (b.map Complex.ofRealHom)).comp
        (-(X : Polynomial ℂ))
      = Polynomial.C ((-1 : ℂ) ^ d)
        * (A.map Complex.ofRealHom + Polynomial.C (Complex.I) * (b.map Complex.ofRealHom))
    rw [hEven1c, Polynomial.C_1, one_mul]
    simp only [add_comp, mul_comp, lcC_comp, comp_negX_map_real, hAeven, hbeven]
  have hQcpar : HasResponseParity (d + 1)
      (Qt.map Complex.ofRealHom + Polynomial.C (Complex.I) * (c.map Complex.ofRealHom)) := by
    show (Qt.map Complex.ofRealHom + Polynomial.C (Complex.I) * (c.map Complex.ofRealHom)).comp
        (-(X : Polynomial ℂ))
      = Polynomial.C ((-1 : ℂ) ^ (d + 1))
        * (Qt.map Complex.ofRealHom + Polynomial.C (Complex.I) * (c.map Complex.ofRealHom))
    rw [hOdd1c, Polynomial.C_neg, Polynomial.C_1, neg_one_mul]
    simp only [add_comp, mul_comp, lcC_comp, comp_negX_map_real, hQtodd, hcoddd,
      neg_mul, Polynomial.map_neg]
    ring
  have hPdeg : (A.map Complex.ofRealHom
      + Polynomial.C (Complex.I) * (b.map Complex.ofRealHom)).degree
      ≤ (d : WithBot ℕ) := by
    refine (Polynomial.degree_add_le _ _).trans (max_le ?_ ?_)
    · rw [Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective]
      exact hAdeg
    · rw [Polynomial.degree_C_mul (by norm_num : (Complex.I : ℂ) ≠ 0),
        Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective]
      exact hbdeg
  have hQdeg : (Qt.map Complex.ofRealHom
      + Polynomial.C (Complex.I) * (c.map Complex.ofRealHom)).degree
      < (d : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · rw [Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective]
      exact hQtdeg
    · rw [Polynomial.degree_C_mul (by norm_num : (Complex.I : ℂ) ≠ 0),
        Polynomial.degree_map_eq_of_injective Complex.ofRealHom.injective]
      rcases hcdeg with h0 | h1
      · subst h0
        simp only [Polynomial.map_zero, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe d
      · rcases eq_or_ne c 0 with hz | hz
        · subst hz
          simp only [Polynomial.map_zero, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe d
        · rw [Polynomial.degree_eq_natDegree hz]
          have h1' := h1
          rw [Polynomial.degree_eq_natDegree hz] at h1'
          have h2 : c.natDegree + 1 ≤ d := by exact_mod_cast h1'
          exact_mod_cast (show c.natDegree < d by omega)

  have hpair : CompletedPair d
      (A.map Complex.ofRealHom + Polynomial.C (Complex.I) * (b.map Complex.ofRealHom))
      (Qt.map Complex.ofRealHom + Polynomial.C (Complex.I) * (c.map Complex.ofRealHom)) :=
    ⟨hPdeg, hQdeg, hPcpar, hQcpar, hnorm⟩
  obtain ⟨base, zs, hbase, hzs, hlen, hPczs, hQczs⟩ :=
    exists_response_of_completedPair hpair

  obtain ⟨z0, zs', rfl⟩ : ∃ z0 zs', zs = z0 :: zs' := by
    cases zs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons w ws => exact ⟨w, ws, rfl⟩
  have hlen3 : zs'.length + 1 = d := by simpa using! hlen
  have hmap : ((z0.arg :: zs'.map Complex.arg) : List ℝ).map lcExp = z0 :: zs' := by
    have hz0 : Qatlib.Concepts.PhaseGeometry.Phase.IsPhase z0 := hzs z0 (by simp)
    have htail : (zs'.map Complex.arg).map lcExp = zs' := by
      have hu : ∀ w ∈ zs', lcExp (Complex.arg w) = w :=
        fun w hw => lcExp_arg_of_isPhase (hzs w (List.mem_cons_of_mem z0 hw))
      rw [List.map_map]
      exact (List.map_congr_left fun w hw => hu w hw).trans (List.map_id _)
    rw [List.map_cons, lcExp_arg_of_isPhase hz0]
    exact congrArg (z0 :: ·) htail
  refine ⟨Real.pi / 2 - z0.arg,
    -base.arg - (((z0.arg :: zs'.map Complex.arg) : List ℝ).length : ℝ) * (Real.pi / 2),
    (z0.arg :: zs'.map Complex.arg).tail.map (fun b => Real.pi / 2 - b), ?_, ?_⟩
  · simp only [List.tail_cons, List.length_map]
    omega
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    rw [lcRepoAmp_of_response z0.arg (zs'.map Complex.arg) base.arg x hx1 hx2,
      lcExp_arg_of_isPhase hbase, hmap, hPczs, hQczs]
    have hPeval : (A.map Complex.ofRealHom
        + Polynomial.C (Complex.I) * (b.map Complex.ofRealHom)).eval ((x : ℝ) : ℂ)
        = ((A.eval x : ℝ) : ℂ) + Complex.I * ((b.eval x : ℝ) : ℂ) := by
      simp only [eval_add, eval_mul, eval_C, map_eval_ofReal]
    have hQeval : (Qt.map Complex.ofRealHom
        + Polynomial.C (Complex.I) * (c.map Complex.ofRealHom)).eval ((x : ℝ) : ℂ)
        = ((Qt.eval x : ℝ) : ℂ) + Complex.I * ((c.eval x : ℝ) : ℂ) := by
      simp only [eval_add, eval_mul, eval_C, map_eval_ofReal]
    rw [hPeval, hQeval]
    simp only [Complex.add_re, Complex.I_mul_re, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, add_zero, realEval, map_eval_ofReal, ← pow_two]
end Qatlib.Concepts.QspSimulation.Achievability
