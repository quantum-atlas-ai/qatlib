/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.FieldTheory.Finiteness
public import Qatlib.Concepts.ErrorCorrection.CssBuild.Classical
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder

@[expose] public section

/-!
# Exact rank certificates for binary check matrices

The verified Boolean echelon algorithm counts free columns. Its computed pivot kernel is the
kernel of the original matrix. The kernel cardinality determines its dimension, which connects
the computation to matrix rank and to the encoded-qubit count of a CSS code.
-/

namespace Qatlib.Concepts.CodeCert.RankCert

set_option autoImplicit false

open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open scoped Matrix

/-- Compute rank by counting the nonfree columns of the verified Boolean echelon form. -/
def rankGF2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  let samples : Fin m → _ := fun i => (regBooleanEquiv n).symm (A i)
  n - (booleanFreeColumns (booleanEchelonRun (List.ofFn samples)).pivots).length

/-- The Boolean free-column computation returns the rank of the original matrix over GF(2). -/
theorem rankGF2_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    rankGF2 A = A.rank := by
  classical
  let samples := fun i : Fin m => (regBooleanEquiv n).symm (A i)
  let piv := (booleanEchelonRun (List.ofFn samples)).pivots
  let c : ClCode (Fin n) (Fin m) := ⟨A⟩
  have hech : IsBooleanEchelon piv := (boolean_gaussian_actual_echelon (List.ofFn samples)).1
  have hmem (x : BooleanVec n) : x ∈ booleanPivotKernel piv ↔ x ∈ codeWords c := by
    rw [show booleanPivotKernel piv =
      booleanSampleCandidate (fun i => regBooleanEquiv n (samples i)) from
        boolean_gaussian_record_kernel samples, mem_booleanSampleCandidate, mem_words]
    simp only [samples, Equiv.apply_symm_apply]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  let e : ↥(booleanPivotKernel piv) ≃ ↥(codeWords c) :=
    Equiv.subtypeEquivProp (funext fun x => propext (hmem x))
  have hcard : Fintype.card ↥(codeWords c) = 2 ^ codeDim c := by
    simpa only [ZMod.card, codeDim] using
      (Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥(codeWords c)))
  have hdim : (booleanKernelBasis piv).length = codeDim c :=
    (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)))
      ((booleanPivotKernel_card_eq_two_pow piv hech).symm.trans
        ((Fintype.card_congr e).trans hcard))
  have hfree : (booleanKernelBasis piv).length = (booleanFreeColumns piv).length :=
    ((boolean_gaussian_kernel_basis piv hech).2.2.2).trans
      (length_booleanFreeColumns piv).symm
  have hrank := dim_add_rank c
  change codeDim c + A.rank = Fintype.card (Fin n) at hrank
  rw [Fintype.card_fin] at hrank
  change n - (booleanFreeColumns piv).length = A.rank
  omega

/-- Check a proposed rank using explicit enumerations of the finite row and column indices. -/
def checkRank {ι κ : Type*} {m n : ℕ} (rows : κ ≃ Fin m) (cols : ι ≃ Fin n)
    (A : Matrix κ ι (ZMod 2)) (r : ℕ) : Bool :=
  decide (rankGF2 (A.reindex rows cols) = r)

/-- Checking the proposed rank succeeds exactly when it is the rank of the original matrix. -/
theorem checkRank_iff {ι κ : Type*} [Fintype ι] {m n : ℕ}
    (rows : κ ≃ Fin m) (cols : ι ≃ Fin n) (A : Matrix κ ι (ZMod 2)) (r : ℕ) :
    checkRank rows cols A r = true ↔ A.rank = r := by
  rw [checkRank, decide_eq_true_eq, rankGF2_eq, Matrix.rank_reindex]

/-- The two accepted check ranks certify the exact number of logical qubits. -/
theorem encoded_eq {ι κX κZ : Type*} [Fintype ι] {mX mZ n : ℕ}
    (rowsX : κX ≃ Fin mX) (rowsZ : κZ ≃ Fin mZ) (cols : ι ≃ Fin n)
    (c : CssData ι κX κZ) (rX rZ : ℕ)
    (hX : checkRank rowsX cols c.hX rX = true)
    (hZ : checkRank rowsZ cols c.hZ rZ = true) :
    c.encodedQubits = Fintype.card ι - rX - rZ := by
  rw [CssData.encodedQubits, (checkRank_iff rowsX cols c.hX rX).mp hX,
    (checkRank_iff rowsZ cols c.hZ rZ).mp hZ]

end Qatlib.Concepts.CodeCert.RankCert
