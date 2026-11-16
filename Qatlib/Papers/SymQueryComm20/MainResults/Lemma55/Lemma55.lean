/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymQueryComm20.MainResults.Lemma54

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SymQueryComm20.MainResults.Lemma55

open Qatlib.Papers.SymQueryComm20.MainResults.SourceModel
open Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

/-- Theorem 2.19's balanced-discrepancy lower-bound premise, isolated as an explicit bridge hypothesis. -/
def BdiscLowerBound (P : ComplexityProfile) (β : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (n j k : ℕ) (r : Cube n → Bool) (G : Cube j → Cube k → Bool),
      0 < bdisc G → bdisc G < 1 →
      8 * Real.exp 1 * (n : ℝ) / (approxDeg r : ℝ)
        ≤ (1 / bdisc G) ^ (1 - β) →
      c * ((approxDeg r : ℝ) * log2 (1 / bdisc G))
        ≤ (P.QccStar n (Fin j) (Fin k) (composeWord r G) : ℝ)

/-- Lemma 5.5 (p. 26): under the bounded-discrepancy and degree conditions,

`Q^{cc,*}((r ∘̃ h_G) ∘ AND₂) = Ω(deg̃(r) log(1/bdisc(G)))` and
`Q^{cc,*}((r ∘̃ h_G) ∘ XOR₂) = Ω(deg̃(r) log(1/bdisc(G)))`. -/
theorem lemma5_5_from_bdisc (P : ComplexityProfile) (β : ℝ) (_hβ0 : 0 < β)
    (_hβ1 : β < 1) (hbase : BdiscLowerBound P β) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n l m : ℕ) (r : Cube n → Bool) (G : Cube l → Cube m → Bool),
      0 < bdisc G → bdisc G < 1 →
      8 * Real.exp 1 * (n : ℝ) / (approxDeg r : ℝ)
        ≤ (1 / bdisc G) ^ (1 - β) →
      c * ((approxDeg r : ℝ) * log2 (1 / bdisc G))
        ≤ (P.QccStar n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
            (composeWithInner (hadamardCompose r G) and2) : ℝ) ∧
      c * ((approxDeg r : ℝ) * log2 (1 / bdisc G))
        ≤ (P.QccStar n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
            (composeWithInner (hadamardCompose r G) xor2) : ℝ) := by
  obtain ⟨c, hc, H⟩ :=
    hbase
  refine ⟨c, hc, fun n l m r G hpos hlt hcond => ⟨?_, ?_⟩⟩
  · have h1 := H n l m r G hpos hlt hcond
    have h2 : P.QccStar n (Fin l) (Fin m) (composeWord r G)
        ≤ P.QccStar n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
            (composeWithInner (hadamardCompose r G) and2) :=
      Qatlib.Papers.SymQueryComm20.MainResults.Lemma5_4.lemma5_4_qcc_and
        P n l m r G
    exact le_trans h1 (by exact_mod_cast h2)
  · have h1 := H n l m r G hpos hlt hcond
    have h2 : P.QccStar n (Fin l) (Fin m) (composeWord r G)
        ≤ P.QccStar n (Cube l ⊕ Cube m) (Cube l ⊕ Cube m)
            (composeWithInner (hadamardCompose r G) xor2) :=
      Qatlib.Papers.SymQueryComm20.MainResults.Lemma5_4.lemma5_4_qcc_xor
        P n l m r G
    exact le_trans h1 (by exact_mod_cast h2)


end Qatlib.Papers.SymQueryComm20.MainResults.Lemma55
