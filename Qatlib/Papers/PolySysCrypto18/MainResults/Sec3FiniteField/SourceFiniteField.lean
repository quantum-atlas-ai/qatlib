/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions.SourceTheta
public import Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions.SourceMQ

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults.Sec3FiniteField
open Qatlib.Papers.PolySysCrypto18.MainResults
open Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions

/-- The map `θ_{p−1}` read in `ZMod p` (equation (5)). -/
def thetaMod (p b : ℕ) (B : Fin (Nat.log2 b + 1) → Bool) : ZMod p :=
  ((theta b (fun i => (B i).toNat) : ℕ) : ZMod p)

/-- The Boolean chart `Π₁ (X_bit) = (θ_{p−1}(X₁), …, θ_{p−1}(X_n))` of Lemma 3.1
(equation (5), p.7). -/
def Pi1 (p n : ℕ) (X : Fin n → (Fin (Nat.log2 (p - 1) + 1) → Bool)) : Fin n → ZMod p :=
  fun i => thetaMod p (p - 1) (X i)

/-- The chart `Π₂ (X_bit, U_bit) = Π₁ (X_bit)` of Lemma 3.2. -/
def Pi2 (p n : ℕ)
    (XU : (Fin n → (Fin (Nat.log2 (p - 1) + 1) → Bool)) ×
          (Fin n → (Fin (Nat.log2 (p - 1) + 1) → Bool))) : Fin n → ZMod p :=
  Pi1 p n XU.1

/-- Numerical ledger for the proposed Boolean coordinate count. Its equality to the variable count of a constructed polynomial system is a separate obligation. -/
def xBitCount (p n : ℕ) : ℕ := n * (Nat.log2 (p - 1) + 1)

/-- Numerical ledger for the proposed Boolean expansion sparseness. No transformed polynomial support is constructed by this definition. -/
def bSparseness (p TF : ℕ) : ℕ := TF * (Nat.log2 (p - 1) + 1) ^ 2

/-- Every solution vector of the supplied system has a coordinatewise Boolean preimage under `Pi1`. This proves surjectivity of the coordinate chart; it does not construct the transformed Boolean polynomial system or prove preservation of its equations. -/
theorem lemma_3_1_surjective {p n : ℕ} (hp : 2 ≤ p) (F : System p n) :
    ∀ Y ∈ F.solutions,
      ∃ X : Fin n → (Fin (Nat.log2 (p - 1) + 1) → Bool), Pi1 p n X = Y := by
  have : NeZero p := ⟨by omega⟩
  intro Y _
  have hp1 : 0 < p - 1 := by omega
  have hchoice : ∀ i, ∃ B : Fin (Nat.log2 (p - 1) + 1) → Bool,
      theta (p - 1) (fun j => (B j).toNat) = (Y i).val := by
    intro i
    have hlt : (Y i).val < p := ZMod.val_lt (Y i)
    exact theta_surjective hp1 (Y i).val (by omega)
  choose B hB using hchoice
  refine ⟨B, ?_⟩
  funext i
  simp only [Pi1, thetaMod]
  rw [hB i]
  exact ZMod.natCast_zmod_val (Y i)

/-- Adding an unused Boolean word to the coordinate chart preserves the existence of a preimage for each supplied solution vector. No equations for the auxiliary word or complex polynomial reduction are asserted. -/
theorem lemma_3_2_surjective {p n : ℕ} (hp : 2 ≤ p) (F : System p n) :
    ∀ Y ∈ F.solutions, ∃ XU, Pi2 p n XU = Y := by
  intro Y hY
  obtain ⟨X, hX⟩ := lemma_3_1_surjective hp F Y hY
  exact ⟨(X, X), hX⟩

end Qatlib.Papers.PolySysCrypto18.MainResults.Sec3FiniteField
