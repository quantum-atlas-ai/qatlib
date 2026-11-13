/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeLocality

/-!
# Local boundary and clock-pair penalty encodings

This module proves that the integer tables for boundary and clock-pair penalties depend only on
their specified sites. Interpreting these tables as dyadic complex matrices recovers the
physical input, output, and weighted clock-pair penalties.

The results connect finite local tables to the boundary terms in the circuit-to-Hamiltonian
construction of [KitaevShenVyalyi2002].

## Main statements

* `boundaryTerm_value`: The boundary table represents the reindexed physical input or output
  penalty.
* `clockPairTerm_value`: The clock-pair table represents the weighted physical clock-pair
  penalty.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib  Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped Classical
set_option autoImplicit false
noncomputable section

/-- A diagonal entry rule invariant under masking to `S` can be reconstructed from its masked
entries when the outside registers agree, and takes the default value otherwise. -/
theorem diagonal_entries {N : ℕ} {T : Type} (z : T)
    (S : Finset (Fin N)) (f : Reg N → T)
    (hf : ∀x, f x = f (fill S (mask S x))) (x y : Reg N) :
    (if regEq x y then f x else z) =
      if outside S x = outside S y then
        (if regEq (fill S (mask S x)) (fill S (mask S y))
          then f (fill S (mask S x)) else z) else z := by
  by_cases hout : outside S x = outside S y
  · rw [if_pos hout]
    have he := eq_fill_iff S x y hout
    by_cases hxy : x = y
    · have hfilled := he.mp hxy
      simp only [if_pos ((regEq_true_iff x y).mpr hxy),
        if_pos ((regEq_true_iff _ _).mpr hfilled)]
      exact hf x
    · have hfilled : fill S (mask S x) ≠ fill S (mask S y) :=
        fun h => hxy (he.mpr h)
      simp only [if_neg (fun h => hxy ((regEq_true_iff x y).mp h)),
        if_neg (fun h => hfilled ((regEq_true_iff _ _).mp h))]
  · have hxy : x ≠ y := by
      intro h
      subst y
      exact hout rfl
    simp only [if_neg hout, if_neg (fun h => hxy ((regEq_true_iff x y).mp h))]

/-- Tests the output-boundary condition when `last` is true and the input-boundary condition
otherwise, using the designated work bit and clock endpoint. -/
def boundaryGuard (m n : ℕ) (last : Bool) (j : Fin n) (x : Reg (m+n)) : Bool :=
  let p := flattenEquiv m n x
  if last then nativeBit p.1 m && !p.2 j else !nativeBit p.1 1 && p.2 j

/-- The executable clock-bit function agrees with the physical clock-bit function. -/
theorem nativeBit_eq_bit {m : ℕ} (c : Clock m) (k : ℕ) : nativeBit c k = bit c k := rfl

/-- The designated work-qubit site belongs to the boundary support. -/
theorem boundary_work_mem (m n : ℕ) (last : Bool) (j : Fin n) :
    j.natAdd m ∈ boundarySites m n last j := by
  simp [boundarySites]

/-- Masking and filling the boundary support preserves the designated work bit. -/
theorem boundary_fill_work (m n : ℕ) (last : Bool) (j : Fin n) (x : Reg (m+n)) :
    (flattenEquiv m n (fill (boundarySites m n last j)
      (mask (boundarySites m n last j) x))).2 j = (flattenEquiv m n x).2 j := by
  change fill (boundarySites m n last j) (mask (boundarySites m n last j) x)
    (j.natAdd m) = x (j.natAdd m)
  exact fill_mask_on _ _ _ (boundary_work_mem m n last j)

/-- For a nonempty clock, masking and filling the boundary support preserves the selected first
or last clock bit. -/
theorem boundary_fill_clock (m n : ℕ) (last : Bool) (j : Fin n)
    (hm : 0 < m) (x : Reg (m+n)) :
    (flattenEquiv m n (fill (boundarySites m n last j)
      (mask (boundarySites m n last j) x))).1
        (if last then (⟨m-1,by omega⟩ : Fin m) else ⟨0,hm⟩) =
    (flattenEquiv m n x).1
        (if last then (⟨m-1,by omega⟩ : Fin m) else ⟨0,hm⟩) := by
  change fill (boundarySites m n last j) (mask (boundarySites m n last j) x)
    ((if last then (⟨m-1,by omega⟩ : Fin m) else ⟨0,hm⟩).castAdd n) = _
  exact fill_mask_on _ _ _ (by simp [boundarySites, hm])

/-- The boundary guard is unchanged by masking and filling its boundary support. -/
theorem boundaryGuard_fill (m n : ℕ) (last : Bool) (j : Fin n) (x : Reg (m+n)) :
    boundaryGuard m n last j x =
      boundaryGuard m n last j (fill (boundarySites m n last j)
        (mask (boundarySites m n last j) x)) := by
  have hw := boundary_fill_work m n last j x
  by_cases hm : 0 < m
  · have hc := boundary_fill_clock m n last j hm x
    cases last with
    | false =>
        have he :
            nativeBit (flattenEquiv m n (fill (boundarySites m n false j)
              (mask (boundarySites m n false j) x))).1 1 =
            nativeBit (flattenEquiv m n x).1 1 := by
          simpa [nativeBit, show 1 ≤ m by omega] using hc
        simp only [boundaryGuard, Bool.false_eq_true, if_false]
        rw [he, hw]
    | true =>
        have he :
            nativeBit (flattenEquiv m n (fill (boundarySites m n true j)
              (mask (boundarySites m n true j) x))).1 m =
            nativeBit (flattenEquiv m n x).1 m := by
          simpa [nativeBit, ne_of_gt hm] using hc
        simp only [boundaryGuard, if_true]
        rw [he, hw]
  · have hm0 : m = 0 := by omega
    subst m
    cases last <;> simp [boundaryGuard, nativeBit, hw]

/-- The boundary coefficient is diagonal, with diagonal value `2^(b + 1)` when the boundary
guard holds and zero otherwise. -/
theorem boundaryCoeff_diag (m n b : ℕ) (last : Bool) (j : Fin n) (x y : Reg (m+n)) :
    boundaryCoeff m n b last j x y =
      if regEq x y then (if boundaryGuard m n last j x then (2 : ℤ)^(b+1) else 0) else 0 := by
  simp only [boundaryCoeff, boundaryGuard, Bool.and_eq_true, ite_and]

/-- A boundary coefficient is recovered from its masked local entries when the outside registers
agree, and is zero otherwise. -/
theorem boundaryCoeff_entries (m n b : ℕ) (last : Bool) (j : Fin n) (x y : Reg (m+n)) :
    boundaryCoeff m n b last j x y =
      if outside (boundarySites m n last j) x = outside (boundarySites m n last j) y
      then boundaryCoeff m n b last j
        (fill (boundarySites m n last j) (mask (boundarySites m n last j) x))
        (fill (boundarySites m n last j) (mask (boundarySites m n last j) y)) else 0 := by
  have hf : ∀z : Reg (m+n),
      (if boundaryGuard m n last j z then (2 : ℤ)^(b+1) else 0) =
      (if boundaryGuard m n last j (fill (boundarySites m n last j)
        (mask (boundarySites m n last j) z)) then (2 : ℤ)^(b+1) else 0) := by
    intro z
    rw [boundaryGuard_fill m n last j z]
  simpa only [boundaryCoeff_diag] using
    diagonal_entries (0 : ℤ) (boundarySites m n last j) _ hf x y

/-- Reindexing the tensor product of clock and work diagonal matrices gives the diagonal product
of their values under `flattenEquiv`. -/
theorem flatten_tensor_diagonal (m n : ℕ) (f : Clock m → ℂ) (g : Reg n → ℂ)
    (x y : Reg (m+n)) :
    Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
      (TensorGate (Matrix.diagonal f) (Matrix.diagonal g)) x y =
      if x = y then f (flattenEquiv m n x).1 * g (flattenEquiv m n x).2 else 0 := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    TensorGate, Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_apply,
    (flattenEquiv m n).injective.eq_iff]

/-- Selects the physical output penalty when `last` is true and the physical input penalty
otherwise. -/
noncomputable def boundaryTarget (m n : ℕ) (last : Bool) (j : Fin n) :
    Matrix (Clock m×Reg n) (Clock m×Reg n) ℂ :=
  if last then physicalOutput j else physicalInput j

/-- The flattened boundary target is the diagonal indicator of the boundary guard. -/
theorem boundaryTarget_entries (m n : ℕ) (last : Bool) (j : Fin n) (x y : Reg (m+n)) :
    Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
      (boundaryTarget m n last j) x y =
      if regEq x y && boundaryGuard m n last j x then (1 : ℂ) else 0 := by
  cases last with
  | false =>
      change Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
        (TensorGate (Matrix.diagonal (fun c : Clock m => if atStart c then (1:ℂ) else 0))
          (Matrix.diagonal (fun z : Reg n => if z j then (1:ℂ) else 0))) x y = _
      rw [flatten_tensor_diagonal]
      by_cases hxy : x = y
      · subst y
        cases hc : bit (flattenEquiv m n x).1 1 <;>
          cases hw : (flattenEquiv m n x).2 j <;>
          simp [boundaryGuard, regEq_true_iff, nativeBit_eq_bit, atStart, hc, hw]
      · simp [hxy, regEq_true_iff]
  | true =>
      change Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
        (TensorGate (Matrix.diagonal (fun c : Clock m => if atEnd c then (1:ℂ) else 0))
          (Matrix.diagonal (fun z : Reg n => if z j then (0:ℂ) else 1))) x y = _
      rw [flatten_tensor_diagonal]
      by_cases hxy : x = y
      · subst y
        cases hc : bit (flattenEquiv m n x).1 m <;>
          cases hw : (flattenEquiv m n x).2 j <;>
          simp [boundaryGuard, regEq_true_iff, nativeBit_eq_bit, atEnd, hc, hw]
      · simp [hxy, regEq_true_iff]

/-- Interpreting the boundary integer coefficient at width `b + 1` gives the corresponding entry
of the flattened physical boundary target. -/
theorem boundaryCoeff_interpret (m n b : ℕ) (last : Bool) (j : Fin n)
    (x y : Reg (m+n)) :
    dyadicValue (b+1) (boundaryCoeff m n b last j x y) 0 =
      Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
        (boundaryTarget m n last j) x y := by
  rw [boundaryTarget_entries]
  change dyadicValue (b+1)
    (if regEq x y && boundaryGuard m n last j x then (2:ℤ)^(b+1) else 0) 0 = _
  split_ifs <;> simp only [dyadic_one, dyadic_zero]

/-- Each entry of the interpreted boundary term is the dyadic value of its boundary coefficient
at width `b + 1`. -/
theorem boundaryTerm_value_entry (m n b : ℕ) (last : Bool) (j : Fin n)
    (x y : Reg (m+n)) :
    value (b+1) (boundaryTerm m n b last j) x y =
      dyadicValue (b+1) (boundaryCoeff m n b last j x y) 0 := by
  change partitionLift (split (boundarySites m n last j))
    (fun u v => dyadicValue (b+1)
      (boundaryCoeff m n b last j (fill (boundarySites m n last j) u)
        (fill (boundarySites m n last j) v)) 0) x y = _
  rw [partitionLift_apply]
  have he := boundaryCoeff_entries m n b last j x y
  by_cases hout : outside (boundarySites m n last j) x = outside (boundarySites m n last j) y
  · rw [if_pos hout]
    rw [if_pos hout] at he
    exact congrArg (fun z : ℤ => dyadicValue (b+1) z 0) he.symm
  · rw [if_neg hout]
    rw [if_neg hout] at he
    rw [he, dyadic_zero]

/-- The boundary term at width `b + 1` represents the flattened physical input or output
penalty. -/
theorem boundaryTerm_value (m n b : ℕ) (last : Bool) (j : Fin n) :
    value (b+1) (boundaryTerm m n b last j) =
      Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
        (boundaryTarget m n last j) := by
  ext x y
  rw [boundaryTerm_value_entry]
  exact boundaryCoeff_interpret m n b last j x y

/-- The support consisting of the two specified clock sites in the flattened clock-work
register. -/
def pairSites {m : ℕ} (n : ℕ) (i j : Fin m) : Finset (Fin (m+n)) :=
  {i.castAdd n, j.castAdd n}

/-- Tests that `i < j` and the selected clock bits have the forbidden pattern false at `i` and
true at `j`. -/
def pairGuard {m : ℕ} (n : ℕ) (i j : Fin m) (x : Reg (m+n)) : Bool :=
  decide (i < j) && !x (i.castAdd n) && x (j.castAdd n)

/-- The diagonal integer coefficient `J * 2^(b + 1)` on the forbidden clock-pair pattern, and
zero elsewhere. -/
def pairCoeff {m : ℕ} (n b J : ℕ) (i j : Fin m) (x y : Reg (m+n)) : ℤ :=
  if regEq x y && decide (i < j) && !x (i.castAdd n) && x (j.castAdd n)
  then (J:ℤ)*(2:ℤ)^(b+1) else 0

/-- Masking and filling the two clock-pair sites preserves the pair guard. -/
theorem pairGuard_fill {m : ℕ} (n : ℕ) (i j : Fin m) (x : Reg (m+n)) :
    pairGuard n i j x = pairGuard n i j
      (fill (pairSites n i j) (mask (pairSites n i j) x)) := by
  have hi := fill_mask_on (pairSites n i j) x (i.castAdd n) (by simp [pairSites])
  have hj := fill_mask_on (pairSites n i j) x (j.castAdd n) (by simp [pairSites])
  simp only [pairGuard, hi, hj]

/-- Expresses the clock-pair coefficient as a diagonal rule controlled by the pair guard. -/
theorem pairCoeff_diag {m : ℕ} (n b J : ℕ) (i j : Fin m) (x y : Reg (m+n)) :
    pairCoeff n b J i j x y =
      if regEq x y then (if pairGuard n i j x then (J:ℤ)*(2:ℤ)^(b+1) else 0) else 0 := by
  simp only [pairCoeff, pairGuard, Bool.and_eq_true, and_assoc, ite_and]

/-- The clock-pair coefficient is recovered from its masked local entries when outside registers
agree, and vanishes otherwise. -/
theorem pairCoeff_entries {m : ℕ} (n b J : ℕ) (i j : Fin m) (x y : Reg (m+n)) :
    pairCoeff n b J i j x y =
      if outside (pairSites n i j) x = outside (pairSites n i j) y then
        pairCoeff n b J i j (fill (pairSites n i j) (mask (pairSites n i j) x))
          (fill (pairSites n i j) (mask (pairSites n i j) y)) else 0 := by
  have hf : ∀z : Reg (m+n),
      (if pairGuard n i j z then (J:ℤ)*(2:ℤ)^(b+1) else 0) =
      (if pairGuard n i j (fill (pairSites n i j) (mask (pairSites n i j) z))
        then (J:ℤ)*(2:ℤ)^(b+1) else 0) := by
    intro z
    rw [pairGuard_fill n i j z]
  simpa only [pairCoeff_diag] using
    diagonal_entries (0 : ℤ) (pairSites n i j) _ hf x y

/-- A real dyadic coefficient `J * 2^b` at width `b` represents the complex natural number `J`. -/
theorem dyadic_nat_multiple (b J : ℕ) :
    dyadicValue b ((J:ℤ)*(2:ℤ)^b) 0 = (J:ℂ) := by
  simp [dyadicValue]

/-- The flattened clock-pair penalty weighted by `J` has diagonal value `J` on the pair guard
and zero elsewhere. -/
theorem pairTarget_entries {m : ℕ} (n J : ℕ) (i j : Fin m) (x y : Reg (m+n)) :
    Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
      ((J:ℂ) • TensorGate (pairPenalty i j) (1:Matrix (Reg n) (Reg n) ℂ)) x y =
      if regEq x y && pairGuard n i j x then (J:ℂ) else 0 := by
  have hI : (1:Matrix (Reg n) (Reg n) ℂ) = Matrix.diagonal (fun _ => (1:ℂ)) := by
    exact Matrix.diagonal_one.symm
  change (J:ℂ) * (Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
    (TensorGate (pairPenalty i j) (1:Matrix (Reg n) (Reg n) ℂ)) x y) = _
  rw [hI]
  change (J:ℂ) * (Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
    (TensorGate (Matrix.diagonal (fun c : Clock m =>
      if i < j ∧ c i=false ∧ c j=true then (1:ℂ) else 0))
      (Matrix.diagonal (fun _ : Reg n => (1:ℂ)))) x y) = _
  rw [flatten_tensor_diagonal]
  by_cases hxy : x = y
  · subst y
    by_cases hij : i < j <;>
      cases hi : x (i.castAdd n) <;>
      cases hj : x (j.castAdd n) <;>
      simp [hij,pairGuard,regEq_true_iff,flattenEquiv,Fin.appendEquiv,hi,hj]
  · simp [hxy, regEq_true_iff]

/-- The dyadic clock-pair coefficient at width `b + 1` equals the corresponding entry of the
flattened weighted clock-pair penalty. -/
theorem pairCoeff_interpret {m : ℕ} (n b J : ℕ) (i j : Fin m) (x y : Reg (m+n)) :
    dyadicValue (b+1) (pairCoeff n b J i j x y) 0 =
      Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
        ((J:ℂ) • TensorGate (pairPenalty i j) (1:Matrix (Reg n) (Reg n) ℂ)) x y := by
  rw [pairTarget_entries]
  simp only [pairCoeff, pairGuard, Bool.and_assoc]
  split_ifs <;> simp only [dyadic_nat_multiple, dyadic_zero]

/-- Each entry of the interpreted clock-pair term is the dyadic value of the corresponding pair
coefficient. -/
theorem clockPairTerm_value_entry {m : ℕ} (n b J : ℕ) (i j : Fin m) (x y : Reg (m+n)) :
    value (b+1) (clockPairTerm m n b J i j) x y =
      dyadicValue (b+1) (pairCoeff n b J i j x y) 0 := by
  change partitionLift (split (pairSites n i j))
    (fun u v => dyadicValue (b+1)
      (pairCoeff n b J i j (fill (pairSites n i j) u) (fill (pairSites n i j) v)) 0) x y = _
  rw [partitionLift_apply]
  have he := pairCoeff_entries n b J i j x y
  by_cases hout : outside (pairSites n i j) x = outside (pairSites n i j) y
  · rw [if_pos hout]
    rw [if_pos hout] at he
    exact congrArg (fun z : ℤ => dyadicValue (b+1) z 0) he.symm
  · rw [if_neg hout]
    rw [if_neg hout] at he
    rw [he, dyadic_zero]

/-- The clock-pair term at width `b + 1` represents the flattened clock-pair penalty weighted by
`J`. -/
theorem clockPairTerm_value {m : ℕ} (n b J : ℕ) (i j : Fin m) :
    value (b+1) (clockPairTerm m n b J i j) =
      Matrix.reindex (flattenEquiv m n).symm (flattenEquiv m n).symm
        ((J:ℂ) • TensorGate (pairPenalty i j) (1:Matrix (Reg n) (Reg n) ℂ)) := by
  ext x y
  rw [clockPairTerm_value_entry]
  exact pairCoeff_interpret n b J i j x y

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
