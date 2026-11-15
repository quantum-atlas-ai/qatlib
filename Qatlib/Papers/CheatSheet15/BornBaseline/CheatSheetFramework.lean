/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
public import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.CheatSheet15.BornBaseline

def toSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def forrK {N : ℕ} [Fintype (Fin N)] (k : ℕ) (H : Matrix (Fin N) (Fin N) ℝ)
    (z : Fin k → Fin N → Bool) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin k → Fin N,
    (∏ j : Fin k, toSign (z j (i j))) *
      (∏ j : Fin k, if h : (j : ℕ) + 1 < k then H (i j) (i ⟨(j : ℕ) + 1, h⟩) else 1)

noncomputable def forrTotal {N : ℕ} [Fintype (Fin N)] (k : ℕ) (δ : ℝ) (H : Matrix (Fin N) (Fin N) ℝ)
    (z : Fin k → Fin N → Bool) : Bool := decide (δ ≤ forrK k H z)

def forrPromise {N : ℕ} [Fintype (Fin N)] (k : ℕ) (δ : ℝ) (H : Matrix (Fin N) (Fin N) ℝ)
    (z : Fin k → Fin N → Bool) : Prop :=
  δ ≤ forrK k H z ∨ |forrK k H z| ≤ δ / 2

def SolvesTotalTree {Q : Type} [Fintype Q] (f : (Q → Bool) → Bool)
    (program : PMF (BoolQueryTree Q Bool)) (ε : ℝ) : Prop :=
  ∀ z : Q → Bool, 1 - ε ≤
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb program z (fun b => b = f z)).toReal

noncomputable def TreeAcceptExpect {Q : Type} [Fintype Q] (program : PMF (BoolQueryTree Q Bool))
    (D : PMF (Q → Bool)) : ℝ :=
  ∑' z : Q → Bool,
    (D z).toReal * (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb program z (fun b => b = true)).toReal

noncomputable def DistAdvantage {Q : Type} [Fintype Q] (program : PMF (BoolQueryTree Q Bool))
    (D₀ D₁ : PMF (Q → Bool)) : ℝ :=
  |TreeAcceptExpect program D₀ - TreeAcceptExpect program D₁|

def queriesOf {Q : Type} {Output : Type} (o : Q → Bool) :
    BoolQueryTree Q Output → List Q
  | .halt _ => []
  | .ask q onFalse onTrue =>
      if o q then q :: queriesOf o onTrue else q :: queriesOf o onFalse

def IsCertifying (M κ : ℕ) (hκ : 0 < κ) (dom : (Fin M → Bool) → Prop)
    (g : (Fin M → Bool) → Bool) (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool) : Prop :=
  (∀ x y, φ x y = true → dom x ∧ y ⟨0, hκ⟩ = g x)
    ∧ (∀ x, dom x → ∃ y, φ x y = true)
    ∧ (∀ x, φ x (fun _ => false) = false)

def sheetIndex {c : ℕ} (b : Fin c → Bool) : Fin (2 ^ c) :=
  ⟨∑ j : Fin c, if b j then 2 ^ (j : ℕ) else 0,
    by
      have le_sum_two_pow {c : ℕ} (f : Fin c → ℕ)
          (h : ∀ j : Fin c, f j ≤ 2 ^ (j : ℕ)) : ∑ j : Fin c, f j < 2 ^ c := by
        induction c with
        | zero => simp
        | succ c ih =>
            have hprev : ∑ j : Fin c, f j.castSucc < 2 ^ c :=
              ih (fun j => f j.castSucc) fun j => h j.castSucc
            have hlast : f (Fin.last c) ≤ 2 ^ c := h _
            have hpow : (2 : ℕ) ^ (c + 1) = 2 ^ c + 2 ^ c := by
              rw [Nat.pow_succ]; omega
            rw [Fin.sum_univ_castSucc f, hpow]
            omega
      exact le_sum_two_pow _ fun j => by by_cases hb : b j <;> simp [hb]⟩

abbrev CheatSheetIndex (c M κ : ℕ) : Type :=
  (Fin c × Fin M) ⊕ (Fin (2 ^ c) × Fin c × Fin κ)

def cheatBlock {c M κ : ℕ} (z : CheatSheetIndex c M κ → Bool) (i : Fin c) : Fin M → Bool :=
  fun j => z (Sum.inl (i, j))

def cheatCert {c M κ : ℕ} (z : CheatSheetIndex c M κ → Bool) (ℓ : Fin (2 ^ c)) (i : Fin c) :
    Fin κ → Bool := fun j => z (Sum.inr (ℓ, i, j))

def cheatSheetFun {c M κ : ℕ} (g : (Fin M → Bool) → Bool)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (z : CheatSheetIndex c M κ → Bool) : Bool :=
  decide (∀ i : Fin c,
    φ (cheatBlock z i) (cheatCert z (sheetIndex fun i' => g (cheatBlock z i')) i) = true)

end Qatlib.Papers.CheatSheet15.BornBaseline
