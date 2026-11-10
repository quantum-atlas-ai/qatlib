/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib

noncomputable def directTransitionMass (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) (hist : List (Reg n))
    (x : Reg n) : ℝ :=
  1 / (TOQueryCountS C : ℝ) *
    ((sQueryStates (forrPhaseOracleS n (regOfList n hist) W) (forrPhaseOracleU n U W) C ψ).map
      (fun φ => sQueryBornMass n W φ x)).sum

noncomputable def cumDirectSuccess (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) :
    ℕ → List (Reg n) → ℝ
  | 0, _ => 1
  | v + 1, hist =>
      ∑ x : Reg n,
        (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0) *
          cumDirectSuccess n W S U C ψ v (x :: hist)

noncomputable def cumulativeSamplerSuccess (n q : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (v : ℕ) : ℝ :=
  1 / (Fintype.card (Fin q → Bool) : ℝ) *
    ∑ w, cumDirectSuccess n W S U C (ψfam w) v []

def Theorem6_2CumulativeSampler : Prop :=
  ∀ (n q t v : ℕ) (W : Type) [Fintype W] [DecidableEq W] (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)),
    IsUnitaryTOCircuit C →
    (∀ w, Normalized (ψfam w)) →
    TOQueryCountS C ≤ t →
    TOQueryCountU C ≤ t →
    (∀ hist : List (Reg n), hist.Nodup → (∀ x ∈ hist, S x) → hist.length ≤ v →
      ∀ w', MeasureProb
          (TORun (forrPhaseOracleS n (regOfList n hist) W) (forrPhaseOracleU n U W) C
            (ψfam w')) E ≤
        1 / 3) →
    (∃ w₀, 2 / 3 ≤
        MeasureProb
          (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w₀)) E) →
    cumulativeSamplerSuccess n q W S U C ψfam v ≥
        1 / (2 ^ q : ℝ) * (1 / (36 * (t : ℝ) ^ 2)) ^ v ∧
    ∀ hist : List (Reg n),
      TOQueryCountS (hardcodeS (forrPhaseOracleS n (regOfList n hist) W) C) = 0 ∧
      TOQueryCountU (hardcodeS (forrPhaseOracleS n (regOfList n hist) W) C) = TOQueryCountU C

end Qatlib.Concepts.QmaCompleteness.WitnessSampler
