/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachineDefs
import Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
import Qatlib.Concepts.LocalMachine.LocalTransport.MatrixRepresentationBridges

/-!
# Local machine transport and precision bounds

This module relates locally well-formed quantum Turing rules to `LocalQTM` structures and
collects validity, encoding, and resource properties of uniform finite gate words. It also
bounds acceptance-weight error caused by entrywise gate approximations, in the quantum
complexity framework of [BernsteinVazirani1997].

The concrete `fourierRule` is shown to fail local well-formedness, with its halt-state
transition described explicitly. Recursive Fourier sampling definitions are accompanied by
counted evaluation and a polynomial bound for the time schedule.

## Main statements

* `precision_probability_error`: bound the acceptance error of finite-precision gate products.
* `g3`: collect local-machine transport and uniform gate-word properties.
* `fourierRule_not_localWellformed`: the specified Fourier transition rule fails local
  well-formedness.
* `rfsTimeSchedule_polynomial`: bound the recursive schedule polynomially in `2^l + 1`.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
open Matrix Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqp
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformBqpDefs
open Qatlib.Foundations.StandardDefs.WindowSim
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Word factors within operator distance `δ` of contractions satisfy the stated product norm
bounds and accumulated product error bound. -/
private theorem approximate_word_bounds {α I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (cs : List α) (A B : α → Matrix I I ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hB : ∀ c ∈ cs, ‖B c‖ ≤ 1) (hE : ∀ c ∈ cs, ‖A c - B c‖ ≤ δ) :
    ‖(cs.map A).prod‖ ≤ (1 + δ)^cs.length ∧
      ‖(cs.map B).prod‖ ≤ 1 ∧
      ‖(cs.map A).prod - (cs.map B).prod‖ ≤ cs.length * δ * (1 + δ)^cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hBc := hB c List.mem_cons_self
    have hEc := hE c List.mem_cons_self
    have hAc : ‖A c‖ ≤ 1 + δ :=
      (norm_le_norm_add_norm_sub' (A c) (B c)).trans (add_le_add hBc hEc)
    obtain ⟨hAp, hBp, hEp⟩ := ih (fun d hd => hB d (List.mem_cons_of_mem c hd))
      (fun d hd => hE d (List.mem_cons_of_mem c hd))
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hM : 0 ≤ 1 + δ := by linarith
    have hp : 1 ≤ (1 + δ)^(cs.length + 1) := one_le_pow₀ (by linarith)
    refine ⟨?_, ?_, ?_⟩
    · calc
        ‖A c * (cs.map A).prod‖ ≤ ‖A c‖ * ‖(cs.map A).prod‖ := norm_mul_le _ _
        _ ≤ (1 + δ) * (1 + δ)^cs.length := mul_le_mul hAc hAp (norm_nonneg _) hM
        _ = (1 + δ)^(cs.length + 1) := (pow_succ' _ _).symm
    · exact (norm_mul_le _ _).trans
        (by nlinarith [norm_nonneg (B c), norm_nonneg ((cs.map B).prod)])
    · have heq : A c * (cs.map A).prod - B c * (cs.map B).prod =
          A c * ((cs.map A).prod - (cs.map B).prod) + (A c - B c) * (cs.map B).prod := by
        noncomm_ring
      rw [heq]
      calc
        _ ≤ ‖A c‖ * ‖(cs.map A).prod - (cs.map B).prod‖ +
            ‖A c - B c‖ * ‖(cs.map B).prod‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        _ ≤ (1 + δ) * ((cs.length : ℝ) * δ * (1 + δ)^cs.length) + δ := by
          have h1 := mul_le_mul hAc hEp (norm_nonneg _) hM
          have h2 := mul_le_mul hEc hBp (norm_nonneg _) hδ
          simpa using! add_le_add h1 h2
        _ = (cs.length : ℝ) * δ * (1 + δ)^(cs.length + 1) + δ := by
          rw [pow_succ]
          ring
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hp hδ]

/-- A matrix on `q` qubits with all entries bounded in norm by `δ` has operator norm at most
`2^q * δ`. -/
private theorem entry_error_operator_bound (q : ℕ) (A : Matrix (Reg q) (Reg q) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hA : ∀ i j, ‖A i j‖ ≤ δ) :
    ‖A‖ ≤ ((2 ^ q : ℕ) : ℝ) * δ := by
  have h := (spectral_operator_norm_le_frobenius A).trans
    (Qatlib.Concepts.LocalMachine.LocalTransport.spectralFrobenius_le_entry_bound A δ hδ hA)
  have hc : Fintype.card (Reg q) = 2 ^ q := by simp [Reg]
  rw [hc, Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg _)] at h
  exact h

/-- Running a finite-code circuit with identity oracle equals applying the reverse product of
its gate matrices. -/
private theorem finiteCode_run_product (q : ℕ) (gs : List FiniteGateCode) (ψ : QState (Reg q)) :
    Run (1 : Matrix (Reg q) (Reg q) ℂ) (finiteCodeCircuit q gs) ψ =
      ((gs.map (finiteCodeMatrix q)).reverse.prod) *ᵥ ψ := by
  induction gs generalizing ψ with
  | nil => simp [finiteCodeCircuit]
  | cons g gs ih =>
    change Run 1 (finiteCodeCircuit q gs) (ApplyGate (finiteCodeMatrix q g) ψ) = _
    rw [ih]
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      ApplyGate, Matrix.mulVec_mulVec]

/-- An entrywise precision guarantee for a gate occurring in the word yields operator error at
most `2^q * 2^(-P.lam)`. -/
private theorem precision_operator_error (q : ℕ) (gs : List FiniteGateCode)
    (P : PrecisionGateApprox q gs) (g : FiniteGateCode) (hg : g ∈ gs) :
    ‖P.approx g - finiteCodeMatrix q g‖ ≤
      ((2 ^ q : ℕ) : ℝ) * (2 : ℝ)^(-(P.lam : ℤ)) := by
  apply entry_error_operator_bound q _ _ (by positivity)
  exact P.entryClose g hg

/-- For a legal finite gate word, the absolute difference between approximate and exact
acceptance weights is bounded by `acceptProbPrecisionBound`. -/
theorem precision_probability_error (q : ℕ) (gs : List FiniteGateCode)
    (x : Reg q) (P : PrecisionGateApprox q gs) (hlegal : finiteWordLegal q gs = true) :
    |P.acceptProb x - uniformBqpAcceptProb q gs x| ≤ acceptProbPrecisionBound q P.lam gs := by
  let δ : ℝ := ((2 ^ q : ℕ) : ℝ) * (2 : ℝ)^(-(P.lam : ℤ))
  have hδ : 0 ≤ δ := by positivity
  let A := (gs.map P.approx).reverse.prod
  let B := (gs.map (finiteCodeMatrix q)).reverse.prod
  have hB : ∀ g ∈ gs.reverse, ‖finiteCodeMatrix q g‖ ≤ 1 := by
    intro g hg
    exact l2_norm_unitary_le_one (finiteCodeMatrix_unitary q g
      (List.all_eq_true.mp hlegal g (List.mem_reverse.mp hg)))
  have hE : ∀ g ∈ gs.reverse, ‖P.approx g - finiteCodeMatrix q g‖ ≤ δ := by
    intro g hg
    exact precision_operator_error q gs P g (List.mem_reverse.mp hg)
  have hb := approximate_word_bounds gs.reverse P.approx (finiteCodeMatrix q) δ hδ hB hE
  simp only [List.map_reverse, List.length_reverse] at hb
  have hA : ‖A‖ ≤ (1 + δ)^gs.length := hb.1
  have hAB : ‖A - B‖ ≤ gs.length * δ * (1 + δ)^gs.length := hb.2.2
  have hket : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket x)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket x)
  have hn : ‖toEuclidean_fromVec (uniformBqpRun q gs x)‖ = 1 := by
    apply (normalized_iff_norm_toEuclidean_fromVec _).mp
    exact normalized_run (1 : Matrix (Reg q) (Reg q) ℂ) (one_mem _)
      (finiteCodeCircuit q gs) ((finite_gate_description_rejection_unitarity_and_counts q gs).2 hlegal).1
      (normalized_ket x)
  have hrun : uniformBqpRun q gs x = B *ᵥ Qatlib.Foundations.PureStateMath.Ket x :=
      finiteCode_run_product q gs (Qatlib.Foundations.PureStateMath.Ket x)
  have hap : ‖toEuclidean_fromVec (P.run x)‖ ≤ (1 + δ)^gs.length := by
    have h :=
        Matrix.l2_opNorm_mulVec A
        (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket x))
    change ‖toEuclidean_fromVec
        (A *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ ≤ ‖A‖ * ‖toEuclidean_fromVec
        (Qatlib.Foundations.PureStateMath.Ket x)‖ at h
    rw [hket, mul_one] at h
    exact h.trans hA
  have hdiff : ‖toEuclidean_fromVec (P.run x - uniformBqpRun q gs x)‖ ≤
      gs.length * δ * (1 + δ)^gs.length := by
    have h :=
        Matrix.l2_opNorm_mulVec (A - B)
        (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket x))
    change ‖toEuclidean_fromVec
        ((A - B) *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ ≤ ‖A - B‖ * ‖toEuclidean_fromVec
        (Qatlib.Foundations.PureStateMath.Ket x)‖ at h
    rw [hket, mul_one] at h
    rw [hrun]
    change ‖toEuclidean_fromVec
        (A *ᵥ Qatlib.Foundations.PureStateMath.Ket x - B *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ ≤ _
    rw [← Matrix.sub_mulVec]
    exact h.trans hAB
  have hm : 1 ≤ (1 + δ)^gs.length := one_le_pow₀ (by linarith)
  have hmass := measureProb_sub_le_l2 (P.run x) (uniformBqpRun q gs x) (uniformBqpOutputEvent q)
  rw [hn] at hmass
  calc
    _ ≤ (‖toEuclidean_fromVec (P.run x)‖ + 1) *
        ‖toEuclidean_fromVec (P.run x - uniformBqpRun q gs x)‖ := hmass
    _ ≤ (2 * (1 + δ)^gs.length) * (gs.length * δ * (1 + δ)^gs.length) := by
      apply mul_le_mul (by linarith) hdiff (norm_nonneg _)
      positivity
    _ = _ := by
      unfold acceptProbPrecisionBound
      dsimp [δ]
      rw [Nat.mul_comm 2 gs.length, pow_mul]
      ring

/-- Collect the equivalence between local rule well-formedness and matching `LocalQTM` data,
together with uniform generator validity, resource and encoding properties,
finite-digit-to-dyadic backend premises, and finite-precision acceptance estimates. -/
theorem g3 :

  (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (R : QtmRule Q A) (h : R.LocalWellformed),
    (R.toLocal h).blank = R.blank ∧ (R.toLocal h).start = R.start ∧
      (R.toLocal h).step = R.step ∧ QtmRule.ofLocal (R.toLocal h) = R) ∧

  (∀ (Q A : Type) [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
      (R : QtmRule Q A),
    R.LocalWellformed ↔
      ∃ M : LocalQTM Q A,
        M.blank = R.blank ∧ M.start = R.start ∧ M.step = R.step) ∧

  (∀ (g : UniformBqpGenerator) (n : ℕ),
    uniformBqpGeneratorValid g → generatorWellformed g ∧
      (∃ (q : ℕ) (gs : List FiniteGateCode),
        uniformBqpGeneratedAt g n = some (q, gs) ∧
          finiteWordLegal q gs = true ∧
          gs.length ≤ uniformBqpWordBound g n ∧
          q ≤ uniformBqpSpaceBound g n ∧
          decodeUniformBqpWord (encodeUniformBqpWord q gs) = some (q, gs))) ∧

  ((∀ (q : ℕ) (gs : List FiniteGateCode), finiteWordLegal q gs = true →
      decodeUniformBqpWord (encodeUniformBqpWord q gs) = some (q, gs)) ∧
    (∀ (q q' : ℕ) (gs gs' : List FiniteGateCode),
      finiteWordLegal q gs = true → finiteWordLegal q' gs' = true →
      encodeUniformBqpWord q gs = encodeUniformBqpWord q' gs' →
        q = q' ∧ gs = gs')) ∧

  (∀ (q : ℕ) (gs : List FiniteGateCode),
    finiteDigitBackendPremise (q, gs) →
      ∀ lam : ℕ, dyadicBackendPremise lam (q, gs)) ∧

  ((∀ (q : ℕ) (gs : List FiniteGateCode) (x : Reg q),
      finiteWordLegal q gs = true →
        0 ≤ uniformBqpAcceptProb q gs x ∧ uniformBqpAcceptProb q gs x ≤ 1) ∧
    (∀ (q : ℕ) (gs : List FiniteGateCode) (x : Reg q)
        (P : PrecisionGateApprox q gs),
      finiteWordLegal q gs = true →
        |P.acceptProb x - uniformBqpAcceptProb q gs x|
          ≤ acceptProbPrecisionBound q P.lam gs))
 := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · intro Q A _ _ _ _ R h
    refine ⟨rfl, rfl, rfl, ?_⟩
    cases R
    rfl
  · intro Q A _ _ _ _ R
    constructor
    · intro h
      exact ⟨R.toLocal h, rfl, rfl, rfl⟩
    · rintro ⟨M, _, _, hstep⟩
      unfold QtmRule.LocalWellformed
      rw [← hstep]
      exact ⟨M.wf_norm, M.wf_sameCell, M.wf_rightStay, M.wf_stayLeft, M.wf_rightLeft⟩
  · intro g n h
    obtain ⟨q, gs, hgen, hlegal, _, _, hlen, hspace, _, _⟩ :=
      generatorValid_per_length_ledgers h n
    exact ⟨generatorValid_implies_generatorWellformed h, q, gs, hgen, hlegal, hlen, hspace,
      decode_encodeUniformBqpWord q gs⟩
  · intro q gs _
    exact decode_encodeUniformBqpWord q gs
  · intro q q' gs gs' _ _ h
    have heq := congrArg decodeUniformBqpWord h
    rw [decode_encodeUniformBqpWord, decode_encodeUniformBqpWord] at heq
    exact Prod.mk.inj (Option.some.inj heq)
  · intro q gs h lam
    exact dyadicBackendPremise_of_legal h.1 lam
  · intro q gs x hlegal
    refine ⟨measureProb_nonneg _ _, measureProb_le_one ?_ _⟩
    exact normalized_run (1 : Matrix (Reg q) (Reg q) ℂ) (one_mem _) (finiteCodeCircuit q gs)
      ((finite_gate_description_rejection_unitarity_and_counts q gs).2 hlegal).1
      (normalized_ket x)
  · exact precision_probability_error

/-- The transition rule `fourierRule` does not satisfy `QtmRule.LocalWellformed`. -/
theorem fourierRule_not_localWellformed : ¬ fourierRule.LocalWellformed := by
  intro h
  have hc := h.2.2.2.2 FourierState.qb FourierSymbol.bit0 FourierState.qa
    FourierSymbol.bit0 FourierSymbol.bit0 FourierSymbol.bit0
  have hterm (q' : FourierState) :
      fourierRule.step FourierState.qb FourierSymbol.bit0 QtmMove.right q' FourierSymbol.bit0 *
        star (fourierRule.step FourierState.qa FourierSymbol.bit0 QtmMove.left q' FourierSymbol.bit0) =
          if q' = FourierState.qb then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0 := by
    cases q' <;> simp [fourierRule, fourierH]
  simp_rw [hterm] at hc
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
  apply (inv_ne_zero (show ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 from ?_)) hc
  exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)).ne'

/-- From `qf`, the Fourier rule moves right to `q0`, preserves the scanned symbol, and has zero
amplitude for every other transition. -/
theorem fourierRule_halt_reset (a : FourierSymbol) :
    fourierRule.step FourierState.qf a QtmMove.right FourierState.q0 a = 1 ∧
      ∀ (d : QtmMove) (q' : FourierState) (b : FourierSymbol),
        (d, q', b) ≠ (QtmMove.right, FourierState.q0, a) →
          fourierRule.step FourierState.qf a d q' b = 0 := by
  refine ⟨by simp [fourierRule], ?_⟩
  intro d q' b h
  dsimp [fourierRule]
  split_ifs with hc
  · obtain ⟨rfl, rfl, rfl⟩ := hc
    exact (h rfl).elim
  · rfl

/-- Counted recursive Fourier sampling evaluation returns `rfsValueOf` and the exact count
`rfsNodeCount`. -/
theorem rfsRecoverCounted_spec (f : RfsQuery → Bool) (l : ℕ) (x : RfsQuery) :
    (rfsRecoverCounted f l x).1 = rfsValueOf f l x ∧
      (rfsRecoverCounted f l x).2 = rfsNodeCount l := by
  induction l generalizing x with
  | zero => exact ⟨rfl, rfl⟩
  | succ l ih =>
    refine ⟨rfl, ?_⟩
    change 1 + ∑ y : Reg (rfsKeyLen (l + 1)),
      (rfsRecoverCounted f l (rfsChild x y)).2 = rfsNodeCount (l + 1)
    simp_rw [(ih _).2]
    simp [rfsNodeCount]

/-- For any coefficients `c` and `d`, the recursive time schedule is bounded by a polynomial in
`2^l + 1`. -/
theorem rfsTimeSchedule_polynomial (c d : ℕ) :
    ∃ c' d' : ℕ, ∀ l : ℕ, rfsTimeSchedule c d l ≤ c' * (2^l + 1)^d' := by
  have hlin : ∀ l : ℕ, l + 2 ≤ 2^(l + 1) := by
    intro l
    induction l with
    | zero => decide
    | succ l ih =>
      calc
        l + 1 + 2 ≤ 2 * (l + 2) := by omega
        _ ≤ 2 * 2^(l + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2^((l + 1) + 1) := by rw [pow_succ]; omega
  let C := c * 2^d + 1
  let A := 2^(d + 3)
  have hA : 8 ≤ A := by dsimp [A]; rw [pow_add]; have h := (Nat.one_le_two_pow : 1 ≤ 2^d); omega
  have hsmall : 2^d ≤ A := by
    dsimp [A]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hgrowth : ∀ l : ℕ, rfsTimeSchedule c d l ≤ C * A^l := by
    intro l
    induction l with
    | zero => simp [rfsTimeSchedule, C]
    | succ l ih =>
      have hterm : c * (l + 2)^d ≤ C * A^l := by
        calc
          c * (l + 2)^d ≤ c * (2^(l + 1))^d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (hlin l) d)
          _ = (c * 2^d) * (2^d)^l := by rw [pow_succ, mul_pow, ← pow_mul, Nat.mul_comm l d, pow_mul]; ring
          _ ≤ C * A^l := Nat.mul_le_mul (by dsimp [C]; omega) (Nat.pow_le_pow_left hsmall l)
      calc
        rfsTimeSchedule c d (l + 1) = c * (l + 2)^d + 4 * rfsTimeSchedule c d l := rfl
        _ ≤ C * A^l + 4 * (C * A^l) := Nat.add_le_add hterm (Nat.mul_le_mul_left 4 ih)
        _ = 5 * (C * A^l) := by ring
        _ ≤ A * (C * A^l) := Nat.mul_le_mul_right _ (by omega)
        _ = C * A^(l + 1) := by rw [pow_succ]; ring
  refine ⟨C, d + 3, fun l => (hgrowth l).trans ?_⟩
  have he : A^l = (2^l)^(d + 3) := by dsimp [A]; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [he]
  exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) _)

end Qatlib.Concepts.LocalMachine.LocalTransport.LocalMachine
