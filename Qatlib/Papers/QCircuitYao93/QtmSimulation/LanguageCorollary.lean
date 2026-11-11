/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCircuitYao93.QtmSimulation.PolynomialPhi3
import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3Encoding

/-!
# Acceptance preservation for compiled circuit families

The module defines acceptance mass for window configurations and for their encoded register
states. Injectivity of the configuration encodings allows
`registerAcceptMass_eq_windowAcceptMass` to transfer acceptance probabilities through the
elementary circuit compilation.

`corollary2_language_circuit_family` obtains circuit families of polynomial length from the
stated polynomial-time window acceptance and rejection bounds, preserving the strict two-thirds
and one-third thresholds at positive input lengths. See [Yao1993].

## Main statements

* `registerAcceptMass_eq_windowAcceptMass`: preserves acceptance mass under compilation.
* `corollary2_language_circuit_family`: constructs elementary circuit families with the given
  language thresholds.

## References

* [Yao, 1993][Yao1993]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.LanguageCorollary

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Papers.QCircuitYao93.QtmSimulation.PolynomialPhi3

/-- The sum of Born probabilities of window configurations whose control state belongs to `Acc`. -/
def windowAcceptMass {t : ℕ} {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (Acc : Set Q) [DecidablePred Acc]
    (ψ : QState (WindowCfg t Q A)) : ℝ :=
  ∑ c : WindowCfg t Q A, if Acc c.state then BornProb ψ c else 0

/-- The sum of register-state Born probabilities at the encodings of window configurations whose
control state belongs to `Acc`. -/
def registerAcceptMass {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (t b : ℕ) (e : CellState Q A → Reg b) (Acc : Set Q)
    [DecidablePred Acc] (ψ : QState (Reg ((2*t+1)*b+3))) : ℝ :=
  ∑ c : WindowCfg t Q A,
    if Acc c.state then BornProb ψ (qtmPhi3Basis t b e (windowEncode c)) else 0

/-- The acceptance mass of a configuration basis state is one if its control state lies in
`Acc`, and zero otherwise. -/
theorem windowAcceptMass_ket {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (Acc : Set Q) [DecidablePred Acc] {t : ℕ} (ψ : WindowCfg t Q A) :
    windowAcceptMass Acc (Ket ψ) = if Acc ψ.state then 1 else 0 := by
  classical
  unfold windowAcceptMass
  rw [Finset.sum_eq_single ψ]
  · simp [bornProb_ket]
  · intro b _ hb
    simp [bornProb_ket, hb]
  · intro h
    exact absurd (Finset.mem_univ ψ) h

/-- Equality after extending registers along an injective wire map implies equality of the
original registers. -/
theorem knownWireExtend_inj {a b : ℕ} (e : Fin a ↪ Fin b) {x y : Reg a}
    (h : knownWireExtend e x = knownWireExtend e y) : x = y := by
  funext i
  have hi := congrFun h (e i)
  simpa using! hi

/-- An injective cell code induces an injective code on window registers. -/
theorem qtmWindowBasisCode_injective {Q A : Type} (t b : ℕ) (e : CellState Q A → Reg b)
    (he : Function.Injective e) :
    Function.Injective (qtmWindowBasisCode t b e) := by
  intro r r' h
  funext i
  apply he
  funext j
  have hi := congrFun h (finProdFinEquiv (m := 2*t+1) (n := b) (i, j))
  simpa [qtmWindowBasisCode] using! hi

/-- The encoding of window configurations into cell registers is injective. -/
theorem windowEncode_injective {t : ℕ} {Q A : Type} :
    Function.Injective (windowEncode (t := t) (Q := Q) (A := A)) := by
  intro c c' hcode
  have hhead : c.head = c'.head := by
    by_contra hne
    have hsame := congrFun hcode c.head
    have h1 : (windowEncode c c.head).1 = 1 := by simp [windowEncode]
    have h2 : (windowEncode c' c.head).1 = 0 := by
      simp [windowEncode, hne]
    rw [hsame] at h1
    have hone : (1 : Fin 3) = 0 := h1.symm.trans h2
    exact absurd hone (by decide)
  have hstate : c.state = c'.state := by
    have hsame := congrFun hcode c.head
    have h1 : (windowEncode c c.head).2.1 = some c.state := by simp [windowEncode]
    have h2 : (windowEncode c' c.head).2.1 = some c'.state := by
      simp [windowEncode, hhead]
    rw [hsame] at h1
    exact Option.some.inj (h1.symm.trans h2)
  have htape : c.tape = c'.tape := by
    funext j
    have key := congrArg (fun r => r.2.2) (congrFun hcode j)
    by_cases hj : j = c.head
    · have hj' : j = c'.head := hj.trans hhead
      simpa [windowEncode, hj, hj', hhead] using! key
    · have hj' : ¬ (j = c'.head) := by
        intro h; exact hj (h.trans hhead.symm)
      simpa [windowEncode, hj, hj', hhead] using! key
  cases c with
  | mk ch cs ct =>
  cases c' with
  | mk ch' cs' ct' =>
  simp only [WindowCfg.mk.injEq]
  exact ⟨hhead, hstate, htape⟩

/-- When the cell state space fits in `b` bits, the chosen finite cell code gives an injective
elementary-register encoding of window configurations. -/
theorem qtmPhi3Basis_encoded_injective {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (t b : ℕ) (hb : Fintype.card (CellState Q A) ≤ 2^b) :
    Function.Injective
      (fun c : WindowCfg t Q A =>
        qtmPhi3Basis t b (finiteBasisCode (CellState Q A) b hb) (windowEncode c)) := by
  intro c c' h
  have hcode : windowEncode c = windowEncode c' :=
    qtmWindowBasisCode_injective t b _
      (finiteBasisCode_injective hb) (knownWireExtend_inj _ h)
  exact windowEncode_injective hcode

/-- The compiled polynomial-time circuit has exactly the same acceptance mass on the encoded
input as the corresponding window QTM evolution. -/
theorem registerAcceptMass_eq_windowAcceptMass {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (b n c k : ℕ)
    (hb : Fintype.card (CellState Q A) ≤ 2^b) (hn : 0 < n) (hc : 0 < c) (hk : 0 < k)
    (Acc : Set Q) [DecidablePred Acc] (x : Fin n → A) :
    registerAcceptMass (c*(n+1)^k) b (finiteBasisCode (CellState Q A) b hb) Acc
        (Run (1 : Matrix (Reg ((2*(c*(n+1)^k)+1)*b+3))
              (Reg ((2*(c*(n+1)^k)+1)*b+3)) ℂ)
          (phi3Compile
            (corollary2_elementary_polynomial_circuit M b n c k hb hn hc hk).choose)
          (qtmPhi3State (c*(n+1)^k) b (finiteBasisCode (CellState Q A) b hb)
            (Ket (windowEncode (initWindowCfg M n x))))) =
      windowAcceptMass (t := c*(n+1)^k) Acc ((windowStep M)^(c*(n+1)^k) *ᵥ
        Ket (initWindowCfg M n x)) := by
  classical
  have hsem := (Classical.choose_spec
    (corollary2_elementary_polynomial_circuit M b n c k hb hn hc hk)).2.2.2.2
  unfold registerAcceptMass windowAcceptMass
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases hw : Acc w.state
  · simp only [hw, if_true]
    exact (hsem x w).2.2.2
  · simp only [hw, if_false]

/-- The stated polynomial-time window acceptance and rejection bounds yield a family of unitary
elementary circuits with no queries and the displayed polynomial length bound, preserving
those thresholds for positive input lengths. This is a language-level form of the corollary
after Theorem 2 of [Yao1993]. -/
theorem corollary2_language_circuit_family {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : LocalQTM Q A) (Acc : Set Q) [DecidablePred Acc]
    (L : (n : ℕ) → Set (Fin n → A)) (b c k : ℕ)
    (hb : Fintype.card (CellState Q A) ≤ 2^b) (hc : 0 < c) (hk : 0 < k)
    (haccept : ∀ (n : ℕ) (x : Fin n → A), x ∈ L n →
      (2:ℝ)/3 < windowAcceptMass (t := c*(n+1)^k) Acc
        ((windowStep M)^(c*(n+1)^k) *ᵥ Ket (initWindowCfg M n x)))
    (hreject : ∀ (n : ℕ) (x : Fin n → A), x ∉ L n →
      windowAcceptMass (t := c*(n+1)^k) Acc
        ((windowStep M)^(c*(n+1)^k) *ᵥ Ket (initWindowCfg M n x)) < (1:ℝ)/3) :
    ∃ C : ∀ n : ℕ, List (Phi3Gate ((2*(c*(n+1)^k)+1)*b+3)),
      (∀ n, IsUnitaryCircuit (phi3Compile (C n))) ∧
      (∀ n, QueryCount (phi3Compile (C n)) = 0) ∧
      (∀ n, (C n).length ≤
        3 * (phi3PaddingBudget (3*b) + phi3PaddingBudget b) * (c*(n+1)^k)^2) ∧
      (∀ (n : ℕ) (_hn : 0 < n) (x : Fin n → A),
        (x ∈ L n →
          (2:ℝ)/3 < registerAcceptMass (c*(n+1)^k) b
            (finiteBasisCode (CellState Q A) b hb) Acc
            (Run (1 : Matrix (Reg ((2*(c*(n+1)^k)+1)*b+3))
                (Reg ((2*(c*(n+1)^k)+1)*b+3)) ℂ)
              (phi3Compile (C n))
              (qtmPhi3State (c*(n+1)^k) b (finiteBasisCode (CellState Q A) b hb)
                (Ket (windowEncode (initWindowCfg M n x)))))) ∧
        (x ∉ L n →
          registerAcceptMass (c*(n+1)^k) b
            (finiteBasisCode (CellState Q A) b hb) Acc
            (Run (1 : Matrix (Reg ((2*(c*(n+1)^k)+1)*b+3))
                (Reg ((2*(c*(n+1)^k)+1)*b+3)) ℂ)
              (phi3Compile (C n))
              (qtmPhi3State (c*(n+1)^k) b (finiteBasisCode (CellState Q A) b hb)
                (Ket (windowEncode (initWindowCfg M n x))))) < (1:ℝ)/3)) := by
  classical

  let C : ∀ n : ℕ, List (Phi3Gate ((2*(c*(n+1)^k)+1)*b+3)) := fun n =>
    if hn : 0 < n then
      (corollary2_elementary_polynomial_circuit M b n c k hb hn hc hk).choose
    else []
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only [C]
    split_ifs with hn
    · exact (corollary2_elementary_polynomial_circuit M b n c k hb hn hc hk).choose_spec.1
    · simp [phi3Compile]
  · intro n
    dsimp only [C]
    split_ifs with hn
    · exact (corollary2_elementary_polynomial_circuit M b n c k hb hn hc hk).choose_spec.2.1
    · simp [phi3Compile]
  · intro n
    dsimp only [C]
    split_ifs with hn
    · exact (corollary2_elementary_polynomial_circuit M b n c k hb hn hc hk).choose_spec.2.2.2.1
    · simp
  · intro n hn x
    have hC : C n
        = (corollary2_elementary_polynomial_circuit M b n c k hb hn hc hk).choose := by
      simp only [C, dif_pos hn]
    have hm := registerAcceptMass_eq_windowAcceptMass M b n c k hb hn hc hk Acc x
    rw [hC, hm]
    exact ⟨haccept n x, hreject n x⟩

end Qatlib.Papers.QCircuitYao93.QtmSimulation.LanguageCorollary
