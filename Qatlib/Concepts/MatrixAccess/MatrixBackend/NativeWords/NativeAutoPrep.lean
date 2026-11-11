/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativePivotSelection
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.NativeWeightSourceOps
import Mathlib.Data.Nat.Size

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
/-! Automatic source allocation and lowest-set-bit pivots. No caller pivot,
capacity or pool-budget correctness premise is needed for this constructor.
Scalar Circle tables and their approximation quality remain separate. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped Classical

/-- Construction for native Label Width in the native auto prep model. -/
def nativeLabelWidth (n : ℕ) : ℕ := Nat.size n
/-- Construction for native Pool Width in the native auto prep model. -/
def nativePoolWidth (n : ℕ) : ℕ := nativeLabelWidth n-2

/-- The finite native construction `nativeLabelCapacity` satisfies the displayed exact coordinate or algebraic relation. -/
theorem nativeLabelCapacity (n : ℕ) : n+1≤2^(nativeLabelWidth n) := Nat.lt_size_self n

/-- The selected pivot or finite scan satisfies the displayed exact bit and minimality condition. -/
theorem nativeLabelWidth_minimal (n m : ℕ) : nativeLabelWidth n ≤ m ↔ n+1 ≤ 2^m := by
  rw [nativeLabelWidth, Nat.size_le]
  omega

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem nativeAllocatedWidth_bound (n : ℕ) :
    weightWidth (nativeLabelWidth n) (nativePoolWidth n) ≤ 2*nativeLabelWidth n+2 := by
  unfold weightWidth nativePoolWidth
  omega

/-- Construction for auto Native Prep Ops in the native auto prep model. -/
def autoNativePrepOps (n : ℕ) (rs : List (Fin n × Circle)) :
    List (NativeKnown.Gate (weightWidth (nativeLabelWidth n) (nativePoolWidth n))) :=
  let v := weightNativeVOps (nativeLabelWidth n) (nativePoolWidth n) n (nativeLabelCapacity n)
    (sourcePivots (nativeLabelWidth n) n (nativeLabelCapacity n)) rs
  NativeKnown.adjointWord v ++ weightNativeMiddleOps (nativeLabelWidth n) (nativePoolWidth n) ++ v

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem autoNativePrepOps_legal (n : ℕ) (rs : List (Fin n × Circle)) : NativeKnown.wordLegal (autoNativePrepOps n rs) :=
  weightNativePrepOps_legal _ _ _ _ _ _ (Nat.le_refl _)

/-- The concrete generated program passes its stated finite legality check. -/
theorem autoNativePrepOps_check (n : ℕ) (rs : List (Fin n × Circle)) :
    NativeKnown.wordLegalCheck (autoNativePrepOps n rs)=true :=
  (NativeKnown.wordLegalCheck_iff _).mpr (autoNativePrepOps_legal n rs)

/-- The actual native program gives the displayed projected unitary encoding. -/
theorem autoNativePrepOps_encoding (n : ℕ) (rs : List (Fin n × Circle)) :
    ProjectedUnitaryEncoding (tableHouseholder rs)
      (reflectionProgramMatrix (NativeKnown.wordCompile (autoNativePrepOps n rs)))
      (weightFrame (nativeLabelWidth n) (nativePoolWidth n) *
        sourceLabelFrame (nativeLabelWidth n) n (nativeLabelCapacity n))
      (weightFrame (nativeLabelWidth n) (nativePoolWidth n) *
        sourceLabelFrame (nativeLabelWidth n) n (nativeLabelCapacity n)) := by
  exact weightNativePrepOps_encoding _ _ _ _ _ _ (Nat.le_refl _)
    (fun r _ => sourcePivots_bit _ _ _ r.1)

/-- The actual native inverse or adjoint satisfies the displayed operator identity. -/
theorem autoNativePrepOps_inverse (n : ℕ) (rs : List (Fin n × Circle)) :
    reflectionProgramMatrix (NativeKnown.wordCompile (NativeKnown.adjointWord (autoNativePrepOps n rs))) =
      (reflectionProgramMatrix (NativeKnown.wordCompile (autoNativePrepOps n rs)))ᴴ :=
  NativeKnown.wordCompile_adjoint _ (autoNativePrepOps_legal n rs)

/-- The compiled known preparation uses no unknown-oracle queries. -/
theorem autoNativePrepOps_queries (n : ℕ) (rs : List (Fin n × Circle)) :
    QueryCount (reflectionCompile (NativeKnown.wordCompile (autoNativePrepOps n rs)))=0 :=
  queryCount_reflectionCompile _

/-- Construction for pivot Table Tests in the native auto prep model. -/
def pivotTableTests (m n : ℕ) (h : n+1≤2^m) (rs : List (Fin n × Circle)) : ℕ :=
  (rs.map (fun r => pivotScanTests (List.finRange m) (sourceLabelBits m n h (some r.1)))).sum

/-- The actual finite construction obeys the displayed quantitative bound with its parameter guards. -/
theorem pivotTableTests_bound (m n : ℕ) (h : n+1≤2^m) (rs : List (Fin n × Circle)) :
    pivotTableTests m n h rs ≤ rs.length*m := by
  induction rs with
  | nil => simp [pivotTableTests]
  | cons r rs ih =>
    have hh : pivotScanTests (List.finRange m) (sourceLabelBits m n h (some r.1)) ≤ m :=
      by simpa using pivotScanTests_le_length (List.finRange m) (sourceLabelBits m n h (some r.1))
    simp only [pivotTableTests, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    change pivotScanTests (List.finRange m) (sourceLabelBits m n h (some r.1)) +
      pivotTableTests m n h rs ≤ rs.length*m+m
    omega

end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
