/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.QuantizerCert.EffectiveCeilQuantizerLawStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.RandCompile.EffectiveInput

open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

def ceilQuantizerCertRat {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (k : ℕ) : Prop :=
  (2*(L : ℚ)*((M : ℚ)+1))*((2 : ℚ)⁻¹)^k ≤ ∑ j, q j k

instance {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (k : ℕ) :
    Decidable (ceilQuantizerCertRat M q k) :=
  inferInstanceAs (Decidable
    ((2*(L : ℚ)*((M : ℚ)+1))*((2 : ℚ)⁻¹)^k ≤ ∑ j, q j k))

def certSearch {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) : ℕ → Option ℕ
  | 0 => if ceilQuantizerCertRat M q 0 then some 0 else none
  | fuel + 1 =>
    match certSearch M q fuel with
    | some k => some k
    | none =>
      if ceilQuantizerCertRat M q (fuel + 1) then some (fuel + 1) else none

def certSearchReads (L k : ℕ) : ℕ := L*(k+1)

def EffectiveQuantizerCertSearch : Prop :=
  ∀ (L M : ℕ) (h : Fin L → ℝ) (q : Fin L → ℕ → ℚ),
    (∀ j, RatLowerOracle (h j) (q j)) → 0 < ∑ j, h j → 0 < M →
    (∃ fuel : ℕ,
        certSearch M q fuel = some (effectiveQuantizerPrecision M q) ∧
        effectiveQuantizerPrecision M q ≤
          Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j)))) ∧
    (∀ (fuel k : ℕ), certSearch M q fuel = some k →
      ceilQuantizerCert M q k ∧
      (∀ k' : ℕ, k' < k → ¬ ceilQuantizerCert M q k') ∧
      certSearchReads L k = L*(k+1)) ∧
    (∀ (fuel : ℕ) (q' : Fin L → ℕ → ℚ),
      (∀ (j : Fin L) (k' : ℕ), k' ≤ fuel → q' j k' = q j k') →
      certSearch M q' fuel = certSearch M q fuel)

end Qatlib.Concepts.RandCompile.EffectiveInput
