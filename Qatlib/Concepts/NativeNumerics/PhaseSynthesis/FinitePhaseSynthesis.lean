/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseGrid
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed

/-!
# Finite rational phase synthesis

This module searches finite Gaussian-rational phase grids for a polynomial response with a
certified rational coefficient score. The construction concerns quantum signal processing
polynomial transformations as in [GilyenSuLowWiebe2019].

For a real target of degree at most `d`, the required parity, and magnitude at most one on
`[-1,1]`, positive tolerance ensures that `finitePhaseSynthesis` returns unit phases whose real
response approximates the target uniformly. The result also records exact search and
response-work counters.

## Main statements

* `phase_grid_actual_search_sound_complete`: Finite-grid enumeration and the search correctness
  and cost invariants.
* `accepted_score_accuracy`: An accepted score bounds the uniform response error.
* `finite_rational_phase_synthesis_terminates`: Existence of a successful synthesis result with
  unit phases, accuracy, and work counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Qatlib.Concepts.LocalMachine.LocalTransport

namespace Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.PhaseGeometry.Phase Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Enumerates all length-`d` words with entries in `List.range N`. -/
def gridWords (N : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | d+1 => (List.range N).flatMap (fun j => (gridWords N d).map (List.cons j))
/-- Decodes a grid word into a base phase from its head and a phase list from its tail, using
`gone` for out-of-range lookups. -/
def decodeGridWord (points : List GaussianRat) (w : List ℕ) : PhaseData :=
  ⟨points.getD (w.headD 0) gone,w.tail.map (fun j => points.getD j gone)⟩
/-- The optional accepted phase data and counts of tested words, response rounds, and
coefficient visits from a grid search. -/
structure SearchResult where
  value : Option PhaseData
  tested : ℕ
  responseRounds : ℕ
  coefficientVisits : ℕ

/-- Searches grid words in order and returns the first decoded phase packet whose rational score
is at most `tol`, accumulating work counters until success or exhaustion. -/
def findGridWord (p : List ℚ) (d : ℕ) (tol : ℚ) (points : List GaussianRat) :
    List (List ℕ) → SearchResult
  | [] => ⟨none,0,0,0⟩
  | w::tail =>
    let data := decodeGridWord points w
    let q := scoreData p d data
    if q.1.1 ≤ tol then ⟨some data,1,q.1.2,q.2⟩ else
      let r := findGridWord p d tol points tail
      ⟨r.value,r.tested+1,r.responseRounds+q.1.2,r.coefficientVisits+q.2⟩
/-- The base-two ceiling logarithm of the denominator of the rational tolerance. -/
def phaseToleranceBits (eps : ℚ) : ℕ := Nat.clog 2 eps.den
/-- The grid exponent `k + Nat.clog 2 (32 * phaseConstant d)` used for degree `d` and precision
`k`. -/
def phaseGridBits (d k : ℕ) : ℕ := k+Nat.clog 2 (32*phaseConstant d)
/-- The dyadic phase backend precision chosen from `k`, `phaseGridBits d k`, and the coefficient
stability constant. -/
def phaseBackendBits (d k : ℕ) : ℕ := k+phaseGridBits d k+Nat.clog 2 (4*phaseConstant d)
/-- The optional synthesized phase data and counters for backend calls, table multiplications,
tested candidates, response rounds, and coefficient visits. -/
structure SynthesisResult where
  value : Option PhaseData
  backendCalls : ℕ
  tableMultiplications : ℕ
  tested : ℕ
  responseRounds : ℕ
  coefficientVisits : ℕ

/-- Tests the all-one phase packet first, then searches a numerically generated finite phase
grid if necessary, returning an optional result and all accumulated work counters. -/
def finitePhaseSynthesis (p : List ℚ) (d : ℕ) (eps : ℚ) : SynthesisResult :=
  let k := phaseToleranceBits eps
  let tol := (1/2:ℚ)^k
  let initial : PhaseData := ⟨gone,List.replicate d gone⟩
  let q0 := scoreData p d initial
  if q0.1.1 ≤ tol then ⟨some initial,0,0,1,q0.1.2,q0.2⟩ else
    let r := phaseGridBits d k
    let q := phaseBackendBits d k
    let N := 2^r
    let table := phaseTable (numericalDyadicPhase r false q) N
    let result := findGridWord p d tol table.1 (gridWords N (d+1))
    ⟨result.value,1,table.2,result.tested+1,result.responseRounds+q0.1.2,
      result.coefficientVisits+q0.2⟩
/-- The real polynomial whose coefficient list is `p`, with zero coefficients beyond the list. -/
noncomputable def realTarget (p : List ℚ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range p.length, C ((p.getD i 0:ℚ):ℝ)*X^i

/-- There are exactly `N^n` grid words of length `n`. -/
theorem gridWords_length (N n : ℕ) : (gridWords N n).length = N^n := by
  induction n with
  | zero => simp [gridWords]
  | succ n ih => simp [gridWords,List.length_flatMap,ih,pow_succ,Nat.mul_comm]

/-- A word belongs to `gridWords N n` exactly when it has length `n` and all entries are less
than `N`. -/
theorem gridWords_mem (N n : ℕ) (w : List ℕ) : w ∈ gridWords N n ↔ w.length = n ∧ ∀ j ∈ w,j < N := by
  induction n generalizing w with
  | zero => cases w <;> simp [gridWords]
  | succ n ih =>
    cases w with
    | nil => simp [gridWords,List.mem_flatMap,List.mem_map]
    | cons j js => simp [gridWords,List.mem_flatMap,List.mem_map,ih,and_left_comm,and_assoc]

/-- Decoding a word of length `d+1` produces exactly `d` non-base phases. -/
theorem decodeGridWord_length (points : List GaussianRat) (w : List ℕ) (d : ℕ) (hw : w.length = d+1) :
    (decodeGridWord points w).phases.length = d := by simp [decodeGridWord,List.length_tail,hw]

/-- Scoring phase data performs one response round per phase and visits exactly `d+1`
coefficients. -/
theorem scoreData_counts (p : List ℚ) (d : ℕ) (data : PhaseData) :
    (scoreData p d data).1.2 = data.phases.length ∧ (scoreData p d data).2 = d+1 := by
  have h := (gaussian_response_native_coefficients data.base data.phases).2.2.2 p d
  exact ⟨h.1,h.2.1⟩

/-- The grid search satisfies the stated work-count bounds, every returned packet comes from an
acceptable word of phase length `d`, and the search succeeds whenever an acceptable word
exists. -/
theorem findGridWord_spec (p : List ℚ) (d : ℕ) (tol : ℚ) (points : List GaussianRat)
    (words : List (List ℕ)) (hw : ∀ w ∈ words,w.length = d+1) :
    let result := findGridWord p d tol points words
    result.tested ≤ words.length ∧ result.responseRounds = result.tested*d ∧
    result.coefficientVisits = result.tested*(d+1) ∧
    (∀ data : PhaseData,result.value = some data →
      (∃ w ∈ words,decodeGridWord points w = data) ∧ data.phases.length = d ∧ (scoreData p d data).1.1 ≤ tol) ∧
    ((∃ w ∈ words,(scoreData p d (decodeGridWord points w)).1.1 ≤ tol) → result.value ≠ none) := by
  induction words with
  | nil => simp [findGridWord]
  | cons w words ih =>
    have hlen := hw w List.mem_cons_self
    have htail : ∀ a ∈ words,a.length = d+1 := fun a ha => hw a (List.mem_cons_of_mem w ha)
    have hi := ih htail
    have hl := decodeGridWord_length points w d hlen
    have hc := scoreData_counts p d (decodeGridWord points w)
    rw [hl] at hc
    (try dsimp only)
    unfold findGridWord
    by_cases hs : (scoreData p d (decodeGridWord points w)).1.1 ≤ tol
    · simp only [hs,ite_true,hc.1,hc.2]
      refine ⟨by simp,by simp,by simp,?_,by simp⟩
      intro data hdata
      have he : decodeGridWord points w = data := Option.some.inj hdata
      subst data
      exact ⟨⟨w,List.mem_cons_self,rfl⟩,hl,hs⟩
    · simp only [hs,ite_false,hc.1,hc.2]
      refine ⟨by have hh := hi.1; simp only [List.length_cons]; omega,?_,?_,?_,?_⟩
      · rw [hi.2.1]; ring
      · rw [hi.2.2.1]; ring
      · intro data hdata
        obtain ⟨⟨a,ha,he⟩,hlen,hscore⟩ := hi.2.2.2.1 data hdata
        exact ⟨⟨a,List.mem_cons_of_mem w ha,he⟩,hlen,hscore⟩
      · rintro ⟨a,ha,hscore⟩
        rcases List.mem_cons.mp ha with he | ha
        · subst a; exact False.elim (hs hscore)
        · exact hi.2.2.2.2 ⟨a,ha,hscore⟩

/-- Grid enumeration has exactly `N^n` words with the stated membership criterion, and searching
length-`d+1` words is sound and complete for the score threshold with exact per-test work
counts. -/
theorem phase_grid_actual_search_sound_complete : ∀ (N n : ℕ), (gridWords N n).length=N^n ∧
  (∀ w : List ℕ, w ∈ gridWords N n ↔ w.length=n ∧ ∀ j ∈ w,j<N) ∧
  (∀ (p : List ℚ) (d : ℕ) (tol : ℚ) (points : List GaussianRat),
    points.length=N →
    let result := findGridWord p d tol points (gridWords N (d+1))
    result.tested ≤ N^(d+1) ∧ result.responseRounds=result.tested*d ∧
    result.coefficientVisits=result.tested*(d+1) ∧
    (∀ data : PhaseData, result.value=some data →
      (∃ w ∈ gridWords N (d+1),decodeGridWord points w=data) ∧
      data.phases.length=d ∧ (scoreData p d data).1.1 ≤ tol) ∧
    ((∃ w ∈ gridWords N (d+1), (scoreData p d (decodeGridWord points w)).1.1 ≤ tol) → result.value ≠ none)) := by
  intro N n
  refine ⟨gridWords_length N n,gridWords_mem N n,?_⟩
  intro p d tol points _hpoints
  have h := findGridWord_spec p d tol points (gridWords N (d+1))
    (fun w hw => ((gridWords_mem N (d+1) w).mp hw).1)
  simpa only [gridWords_length] using h

/-- The coefficient at `i` of `realTarget p` is the real cast of `p.getD i 0`. -/
theorem realTarget_coeff (p : List ℚ) (i : ℕ) : (realTarget p).coeff i = ((p.getD i 0:ℚ):ℝ) := by
  simp only [realTarget]
  by_cases hi : i < p.length
  · simp [hi]
  · have he : p.getD i 0 = 0 := List.getD_eq_default p 0 (by omega)
    simp [hi]

/-- For positive rational `eps`, the dyadic threshold determined by `phaseToleranceBits eps` is
at most `eps`. -/
theorem phaseTolerance_le (eps : ℚ) (heps : 0 < eps) : (1/2:ℚ)^phaseToleranceBits eps ≤ eps := by
  have hden : (0:ℚ) < eps.den := by exact_mod_cast eps.den_pos
  have hnum : (1:ℚ) ≤ eps.num := by
    exact_mod_cast (show (1:ℤ) ≤ eps.num by have h := Rat.num_pos.mpr heps; omega)
  have hk : eps.den ≤ 2^phaseToleranceBits eps := Nat.le_pow_clog (by decide) eps.den
  have hpow : (eps.den:ℚ) ≤ (2:ℚ)^phaseToleranceBits eps := by exact_mod_cast hk
  have ht : (1/2:ℚ)^phaseToleranceBits eps = 1/(2:ℚ)^phaseToleranceBits eps := by
    rw [one_div,inv_pow,inv_eq_one_div]
  calc
    _ = _ := ht
    _ ≤ 1/(eps.den:ℚ) := one_div_le_one_div_of_le hden hpow
    _ ≤ (eps.num:ℚ)/(eps.den:ℚ) := div_le_div_of_nonneg_right hnum hden.le
    _ = eps := Rat.num_div_den eps

/-- A degree bound of `d` for `realTarget p` implies its natural degree is at most `d`. -/
theorem target_natDegree_le (p : List ℚ) (d : ℕ) (hp : (realTarget p).degree ≤ (d:WithBot ℕ)) :
    (realTarget p).natDegree ≤ d := by
  by_cases hz : realTarget p = 0
  · simp [hz]
  · rw [Polynomial.degree_eq_natDegree hz] at hp
    exact_mod_cast hp

/-- For a target of degree at most `d` and `d` phases, the rational score bounds the real
response error at every point of `[-1,1]`. -/
theorem scoreData_uniform_error (p : List ℚ) (d : ℕ) (data : PhaseData)
    (hlen : data.phases.length = d) (hdegree : (realTarget p).degree ≤ (d:WithBot ℕ))
    (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re-
      (realTarget p).eval x| ≤ ((scoreData p d data).1.1:ℝ) := by
  let P := responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)
  have hdP : P.natDegree < d+1 := by
    have h :=
        (response_degree (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).1
    simp only [List.length_map,hlen] at h
    dsimp [P]
    omega
  have hdT : (realTarget p).natDegree < d+1 := by have h := target_natDegree_le p d hdegree; omega
  have heval : (P.eval (x:ℂ)).re-(realTarget p).eval x =
      ∑ i ∈ Finset.range (d+1), ((P.coeff i).re-((p.getD i 0:ℚ):ℝ))*x^i := by
    rw [Polynomial.eval_eq_sum_range' hdP,Polynomial.eval_eq_sum_range' hdT,Complex.re_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,realTarget_coeff]
    ring
  have hscore := (gaussian_response_native_coefficients data.base data.phases).2.2.2 p d
  change |(P.eval (x:ℂ)).re-(realTarget p).eval x| ≤ _
  rw [heval,hscore.2.2]
  calc
    _ ≤ ∑ i ∈ Finset.range (d+1), |((P.coeff i).re-((p.getD i 0:ℚ):ℝ))*x^i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_pow]
      have hb : |x|^i ≤ 1 := pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
      exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_one _)

/-- At an index within a list's length, looking up in its mapped list equals mapping the
original lookup, regardless of the lookup defaults. -/
theorem mapped_getD_valid {A B : Type} (f : A → B) (w : List A) (a : A) (b : B) (i : ℕ) (hi : i < w.length) :
    (w.map f).getD i b = f (w.getD i a) := by
  rw [List.getD_eq_getElem (w.map f) b (by simpa using hi),List.getD_eq_getElem w a hi]
  simp

/-- A finite grid covering unit phases within `eta` supplies a same-length index word
approximating every entry of a given unit-phase list. -/
theorem phase_indices_cover (points : List GaussianRat) (N : ℕ) (eta : ℝ)
    (hcover : ∀ v : ℂ,‖v‖ = 1 → ∃ j : ℕ,j < N ∧ ‖gaussianRatComplex (points.getD j gone)-v‖ ≤ eta)
    (zs : List ℂ) (hz : ∀ z ∈ zs,IsPhase z) :
    ∃ w : List ℕ,w.length = zs.length ∧ (∀ j ∈ w,j < N) ∧
      (∀ i < zs.length,‖gaussianRatComplex (points.getD (w.getD i 0) gone)-zs.getD i 1‖ ≤ eta) := by
  induction zs with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | cons z zs ih =>
    obtain ⟨j,hj,he⟩ := hcover z (phase_norm_one z (hz z List.mem_cons_self))
    obtain ⟨w,hlen,hw,ht⟩ := ih (fun a ha => hz a (List.mem_cons_of_mem z ha))
    refine ⟨j::w,by simp [hlen],?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with h | h
      · simpa only [h] using hj
      · exact hw a h
    · intro i hi
      cases i with
      | zero => simpa using he
      | succ i => simpa using ht i (by simpa using hi)

/-- A unit phase grid covering the circle within `eta` contains a word whose decoded base and
phase list are unit and approximate the given packet entrywise within `eta`. -/
theorem phase_comparison_word (points : List GaussianRat) (N : ℕ) (eta : ℝ)
    (hunit : ∀ j < N,‖gaussianRatComplex (points.getD j gone)‖ = 1)
    (hcover : ∀ v : ℂ,‖v‖ = 1 → ∃ j : ℕ,j < N ∧ ‖gaussianRatComplex (points.getD j gone)-v‖ ≤ eta)
    (base : ℂ) (zs : List ℂ) (hb : IsPhase base) (hz : ∀ z ∈ zs,IsPhase z) :
    ∃ w ∈ gridWords N (zs.length+1),
      let data := decodeGridWord points w
      data.phases.length = zs.length ∧ ‖gaussianRatComplex data.base‖ = 1 ∧
      (∀ z ∈ data.phases,‖gaussianRatComplex z‖ = 1) ∧
      ‖gaussianRatComplex data.base-base‖ ≤ eta ∧
      (∀ i < zs.length,‖(data.phases.map gaussianRatComplex).getD i 1-zs.getD i 1‖ ≤ eta) := by
  obtain ⟨j,hj,he⟩ := hcover base (phase_norm_one base hb)
  obtain ⟨w,hlen,hw,hs⟩ := phase_indices_cover points N eta hcover zs hz
  refine ⟨j::w,(gridWords_mem N (zs.length+1) _).mpr ⟨by simp [hlen],?_⟩,?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with h | h
    · simpa only [h] using hj
    · exact hw a h
  · dsimp only [decodeGridWord,List.headD_cons,List.tail_cons]
    refine ⟨by simp [hlen],hunit j hj,?_,he,?_⟩
    · intro z hz
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
      exact hunit a (hw a ha)
    · intro i hi
      have hiw : i < w.length := by omega
      rw [List.map_map]
      simp only [Function.comp_def]
      rw [mapped_getD_valid (fun a => gaussianRatComplex (points.getD a gone)) w 0 1 i hiw]
      exact hs i hi

/-- The coefficient stability constant `phaseConstant d` is positive. -/
theorem phaseConstant_pos (d : ℕ) : 0 < phaseConstant d := by unfold phaseConstant; positivity

/-- The chosen grid and backend precisions make the phase coverage error at most `(1/2)^k / (2 *
phaseConstant d)`. -/
theorem phase_grid_budget (d k : ℕ) :
    8/(2^phaseGridBits d k:ℕ)+((2^phaseGridBits d k:ℕ):ℝ)*((2:ℝ)⁻¹)^phaseBackendBits d k ≤
      (1/2:ℝ)^k/(2*(phaseConstant d:ℝ)) := by
  let a := Nat.clog 2 (32*phaseConstant d)
  let b := Nat.clog 2 (4*phaseConstant d)
  have hC : (0:ℝ) < phaseConstant d := by exact_mod_cast phaseConstant_pos d
  have ha : 32*(phaseConstant d:ℝ) ≤ (2:ℝ)^a := by
    exact_mod_cast (Nat.le_pow_clog (by decide : 1 < 2) (32*phaseConstant d))
  have hb : 4*(phaseConstant d:ℝ) ≤ (2:ℝ)^b := by
    exact_mod_cast (Nat.le_pow_clog (by decide : 1 < 2) (4*phaseConstant d))
  have hp : (0:ℝ) < (2:ℝ)^k := by positivity
  have ht : (1/2:ℝ)^k = 1/(2:ℝ)^k := by rw [one_div,inv_pow,inv_eq_one_div]
  have hA : 8/(2:ℝ)^(k+a) ≤ (1/2:ℝ)^k/(4*(phaseConstant d:ℝ)) := by
    rw [ht,pow_add,div_div,div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_left ha hp.le
    nlinarith
  have he : (2:ℝ)^(k+a)*((2:ℝ)⁻¹)^(k+(k+a)+b) = 1/((2:ℝ)^k*(2:ℝ)^b) := by
    rw [inv_pow,inv_eq_one_div]
    simp only [pow_add]
    field_simp
  have hB : (2:ℝ)^(k+a)*((2:ℝ)⁻¹)^(k+(k+a)+b) ≤ (1/2:ℝ)^k/(4*(phaseConstant d:ℝ)) := by
    rw [he,ht,div_div]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hb hp.le
  change 8/(2^(k+a):ℕ)+((2^(k+a):ℕ):ℝ)*((2:ℝ)⁻¹)^(k+(k+a)+b) ≤ _
  push_cast
  exact (add_le_add hA hB).trans_eq (by ring)

/-- If a response plus its coefficient conjugate is twice the real target, each real response
coefficient equals the corresponding rational target coefficient cast to ℝ. -/
theorem comparison_real_coeff (p : List ℚ) (base : ℂ) (zs : List ℂ)
    (he : responseP base zs+conjugatePolynomial (responseP base zs) = C (2:ℂ)*(realTarget p).map Complex.ofRealHom)
    (i : ℕ) : ((responseP base zs).coeff i).re = ((p.getD i 0:ℚ):ℝ) := by
  have h := congrArg (fun P : Polynomial ℂ => (P.coeff i).re) he
  simp only [Polynomial.coeff_add,conjugatePolynomial,Polynomial.coeff_map,Polynomial.coeff_C_mul,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.ofRealHom_eq_coe,realTarget_coeff] at h
  norm_num at h
  change ((responseP base zs).coeff i).re+((responseP base zs).coeff i).re = 2*((p.getD i 0:ℚ):ℝ) at h
  linarith

/-- When a comparison response has the target's real coefficients, the candidate's rational
score is bounded by its coefficient-norm distance from that response through degree `d`. -/
theorem scoreData_comparison_le (p : List ℚ) (d : ℕ) (data : PhaseData) (base : ℂ) (zs : List ℂ)
    (hc : ∀ i,((responseP base zs).coeff i).re = ((p.getD i 0:ℚ):ℝ)) :
    ((scoreData p d data).1.1:ℝ) ≤
      ∑ i ∈ Finset.range (d+1),‖(responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).coeff i-
        (responseP base zs).coeff i‖ := by
  rw [((gaussian_response_native_coefficients data.base data.phases).2.2.2 p d).2.2]
  apply Finset.sum_le_sum
  intro i hi
  rw [← hc i,← Complex.sub_re]
  exact Complex.abs_re_le_norm _

/-- A target satisfying the degree, parity, and interval magnitude bounds has an acceptable word
on the chosen actual phase grid at score threshold `(1/2)^k`. -/
theorem synthesis_grid_acceptable (p : List ℚ) (d k : ℕ)
    (hpdeg : (realTarget p).degree ≤ (d:WithBot ℕ))
    (hparity : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p))
    (hbound : ∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget p).eval x| ≤ 1) :
    let r := phaseGridBits d k
    let q := phaseBackendBits d k
    let points := (phaseTable (numericalDyadicPhase r false q) (2^r)).1
    ∃ w ∈ gridWords (2^r) (d+1),(scoreData p d (decodeGridWord points w)).1.1 ≤ (1/2:ℚ)^k := by
  (try dsimp only)
  obtain ⟨base,zs,hbase,hzs,hlen,hcoeff,hreal⟩ :=
      Qatlib.Concepts.QsvtCore.LinearSystems.exists_phases_of_bounded hpdeg hparity hbound
  have hgrid := phase_grid_actual_cover_and_table_cost (phaseGridBits d k) (phaseBackendBits d k)
  let r := phaseGridBits d k
  let q := phaseBackendBits d k
  let N := 2^r
  let points := (phaseTable (numericalDyadicPhase r false q) N).1
  let eta : ℝ := 8/(N:ℝ)+(N:ℝ)*((2:ℝ)⁻¹)^q
  obtain ⟨w,hw,hd,hu,hphase,hbaseclose,hclose⟩ := phase_comparison_word points N eta
    (fun j hj => (hgrid.2.2.1 j hj).2) hgrid.2.2.2 base zs hbase hzs
  let data := decodeGridWord points w
  have hlenData : data.phases.length = d := hd.trans hlen
  have hPbase : IsPhase (gaussianRatComplex data.base) :=
      isPhase_iff_normSq.mpr (by rw [Complex.normSq_eq_norm_sq,hu]; norm_num)
  have hPphases : ∀ z ∈ data.phases.map gaussianRatComplex,IsPhase z := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact isPhase_iff_normSq.mpr (by rw [Complex.normSq_eq_norm_sq,hphase a ha]; norm_num)
  have hlip := response_coefficients_derived_lipschitz d (gaussianRatComplex data.base) base
    (data.phases.map gaussianRatComplex) zs eta (by simp [hlenData]) hlen hPbase hbase hPphases hzs
    (by dsimp [eta]; positivity) hbaseclose (by simpa only [hlen] using hclose)
  have hscore :=
      (scoreData_comparison_le p d data base zs (comparison_real_coeff p base zs hcoeff)).trans hlip
  have hC : (0:ℝ) < phaseConstant d := by exact_mod_cast phaseConstant_pos d
  have hbudget : eta ≤ (1/2:ℝ)^k/(2*(phaseConstant d:ℝ)) := phase_grid_budget d k
  have hmass := mul_le_mul_of_nonneg_left hbudget hC.le
  have hc : (phaseConstant d:ℝ)*((1/2:ℝ)^k/(2*(phaseConstant d:ℝ))) = (1/2:ℝ)^k/2 := by field_simp
  rw [hc] at hmass
  refine ⟨w,by simpa only [hlen] using hw,?_⟩
  have ht0 : 0 ≤ (1/2:ℝ)^k := by positivity
  have hh : ((scoreData p d data).1.1:ℝ) ≤ (1/2:ℝ)^k := by linarith
  change (scoreData p d data).1.1 ≤ (1/2:ℚ)^k
  apply (Rat.cast_le (K:=ℝ)).mp
  simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh

/-- Decoding a valid grid word from unit table entries produces a unit base and unit phase
entries. -/
theorem decodeGridWord_units (points : List GaussianRat) (N d : ℕ) (w : List ℕ)
    (hw : w ∈ gridWords N (d+1)) (hu : ∀ j < N,‖gaussianRatComplex (points.getD j gone)‖ = 1) :
    ‖gaussianRatComplex (decodeGridWord points w).base‖ = 1 ∧
      ∀ z ∈ (decodeGridWord points w).phases,‖gaussianRatComplex z‖ = 1 := by
  have hm := (gridWords_mem N (d+1) w).mp hw
  cases w with
  | nil => simp at hm
  | cons j js =>
    refine ⟨hu j (hm.2 j List.mem_cons_self),?_⟩
    intro z hz
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
    exact hu i (hm.2 i (List.mem_cons_of_mem j hi))

/-- For positive `eps`, a degree-`d` target and length-`d` packet with accepted dyadic score
have real response error at most `eps` uniformly on `[-1,1]`. -/
theorem accepted_score_accuracy (p : List ℚ) (d : ℕ) (eps : ℚ) (data : PhaseData)
    (heps : 0 < eps) (hp : (realTarget p).degree ≤ (d:WithBot ℕ)) (hlen : data.phases.length = d)
    (hs : (scoreData p d data).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps) :
    ∀ x ∈ Set.Icc (-1:ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re-
        (realTarget p).eval x| ≤ (eps:ℝ) := by
  intro x hx
  have hscore : ((scoreData p d data).1.1:ℝ) ≤ (eps:ℝ) :=
      Rat.cast_le.mpr (hs.trans (phaseTolerance_le eps heps))
  exact (scoreData_uniform_error p d data hlen hp x hx).trans hscore

/-- For a target satisfying the degree, parity, and interval magnitude bounds and positive
`eps`, finite synthesis returns `d` unit phases and a unit base with uniform real response
error at most `eps`, together with the stated score and work-count guarantees. -/
theorem finite_rational_phase_synthesis_terminates : ∀ (p : List ℚ) (d : ℕ) (eps : ℚ), 0<eps →
  (realTarget p).degree ≤ (d:WithBot ℕ) →
  Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) →
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget p).eval x| ≤ 1) →
  let result := finitePhaseSynthesis p d eps
  let k := phaseToleranceBits eps
  let N := 2^phaseGridBits d k
  ∃ data : PhaseData, result.value=some data ∧ data.phases.length=d ∧
    ‖gaussianRatComplex data.base‖=1 ∧ (∀ z ∈ data.phases,‖gaussianRatComplex z‖=1) ∧
    (scoreData p d data).1.1 ≤ (1/2:ℚ)^k ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re-
        (realTarget p).eval x| ≤ (eps:ℝ)) ∧
    1 ≤ result.tested ∧ result.tested ≤ 1+N^(d+1) ∧
    result.responseRounds=result.tested*d ∧ result.coefficientVisits=result.tested*(d+1) ∧
    (result.backendCalls=0 ∧ result.tableMultiplications=0 ∨
      result.backendCalls=1 ∧ result.tableMultiplications=N-1)
 := by
  intro p d eps heps hp hpar hbound
  (try dsimp only)
  let k := phaseToleranceBits eps
  let r := phaseGridBits d k
  let q := phaseBackendBits d k
  let N := 2^r
  let initial : PhaseData := ⟨gone,List.replicate d gone⟩
  have hlen0 : initial.phases.length = d := by simp [initial]
  have hcount0 := scoreData_counts p d initial
  rw [hlen0] at hcount0
  by_cases hs : (scoreData p d initial).1.1 ≤ (1/2:ℚ)^k
  · refine ⟨initial,?_,hlen0,by simp [initial],by simp [initial],hs,
      accepted_score_accuracy p d eps initial heps hp hlen0 hs,?_,?_,?_,?_,Or.inl ⟨?_,?_⟩⟩
    all_goals simp only [finitePhaseSynthesis]
    all_goals simp only [show (scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,
      ite_true]
    all_goals simp [initial,scoreData, (responseData_semantics gone (List.replicate d gone)).2.2,
      (scoreLoop_semantics p (responseData gone (List.replicate d gone)).1.1 (d+1)).1]
  · let points := (phaseTable (numericalDyadicPhase r false q) N).1
    let result := findGridWord p d ((1/2:ℚ)^k) points (gridWords N (d+1))
    have htable := phase_grid_actual_cover_and_table_cost r q
    have hsearch :=
        (phase_grid_actual_search_sound_complete N (d+1)).2.2 p d ((1/2:ℚ)^k) points htable.1
    have haccept := synthesis_grid_acceptable p d k hp hpar hbound
    have hnotnone : result.value ≠ none := hsearch.2.2.2.2 haccept
    cases hv : result.value with
    | none => exact False.elim (hnotnone hv)
    | some data =>
      obtain ⟨⟨w,hw,hd⟩,hlen,hscore⟩ := hsearch.2.2.2.1 data hv
      have hu := decodeGridWord_units points N d w hw (fun j hj => (htable.2.2.1 j hj).2)
      rw [hd] at hu
      refine ⟨data,?_,hlen,hu.1,hu.2,hscore,
        accepted_score_accuracy p d eps data heps hp hlen hscore,?_,?_,?_,?_,Or.inr ⟨?_,?_⟩⟩
      · unfold finitePhaseSynthesis
        simp only [show ¬(scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,ite_false]
        exact hv
      · unfold finitePhaseSynthesis
        simp only [show ¬(scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,ite_false]
        omega
      · unfold finitePhaseSynthesis
        simp only [show ¬(scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,ite_false]
        have hc := hsearch.1
        change result.tested ≤ N^(d+1) at hc
        change result.tested+1 ≤ 1+N^(d+1)
        omega
      · unfold finitePhaseSynthesis
        simp only [show ¬(scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,ite_false]
        change result.responseRounds+(scoreData p d initial).1.2 = (result.tested+1)*d
        rw [hsearch.2.1,hcount0.1]
        ring
      · unfold finitePhaseSynthesis
        simp only [show ¬(scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,ite_false]
        change result.coefficientVisits+(scoreData p d initial).2 = (result.tested+1)*(d+1)
        rw [hsearch.2.2.1,hcount0.2]
        ring
      · unfold finitePhaseSynthesis
        simp only [show ¬(scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,ite_false]
      · unfold finitePhaseSynthesis
        simp only [show ¬(scoreData p d ⟨gone,List.replicate d gone⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps from hs,ite_false]
        exact htable.2.1

end Qatlib.Concepts.NativeNumerics.PhaseSynthesis
