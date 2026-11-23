module

public import Qatlib.Papers.PottsPartEval07.CodeStructure.FrobeniusOrbits
public import Qatlib.Papers.PottsPartEval07.ClassMembership.ParityCheck

@[expose] public section

/-!
# Concrete consumers for the Potts class tally and parity-check dual

The orbit tally is instantiated at `N = 7`, `q = 2` with the invariant indicator of the orbit
`{1, 2, 4}`. Over `ZMod 3` the parity-check identity uses a nonzero two-by-two block,
and a concrete coordinate checks the negative sign in the parity-check encoder. The
positive- and zero-weight trace-code tallies are also instantiated over `ZMod 3`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.Papers.PottsPartEval07.FrobeniusMembership

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.CodeStructure
open Qatlib.Papers.PottsPartEval07.ClassMembership
open Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
open Qatlib.Papers.PottsPartEval07.ExactRecovery
open Qatlib.Papers.PottsPartEval07.CodeStructure

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-! ## Frobenius orbit tally at `N = 7` and `q = 2` -/

/-- Coprimality of the concrete Frobenius multiplier. -/
theorem coprimeTwoSeven : Nat.Coprime 2 7 := by norm_num

/-- The indicator of the Frobenius orbit `{1, 2, 4}` modulo seven. -/
def orbitSeven : ZMod 7 → ℕ := fun x => if x = 1 ∨ x = 2 ∨ x = 4 then 1 else 0

/-- The concrete indicator is invariant under multiplication by two. -/
theorem orbitSeven_invariant : ∀ x, orbitSeven ((2 : ZMod 7) * x) = orbitSeven x := by
  decide

/-- The indicator marks exactly three residues. -/
theorem orbitSeven_card :
    (Finset.univ.filter (fun x : ZMod 7 => orbitSeven x = 1)).card = 3 := by
  decide

/-- The top-level tally instantiated at the concrete seven-element orbit. -/
theorem frobenius_tally_seven :
    (Finset.univ.filter (fun x : ZMod 7 => orbitSeven x = 1)).card =
      ∑ r ∈ Finset.univ.image (fun x => orbitRep coprimeTwoSeven x),
        if orbitSeven r = 1 then (frobeniusOrbit coprimeTwoSeven r).card else 0 :=
  frobenius_weight_tally coprimeTwoSeven orbitSeven orbitSeven_invariant 1

/-- The representative sum evaluates to the three marked residues. -/
theorem frobenius_tally_seven_numeric :
    (∑ r ∈ Finset.univ.image (fun x => orbitRep coprimeTwoSeven x),
        if orbitSeven r = 1 then (frobeniusOrbit coprimeTwoSeven r).card else 0) = 3 := by
  rw [← frobenius_tally_seven]
  exact orbitSeven_card

/-- The length-two multiplicity tally instantiated at the concrete orbit. -/
theorem frobenius_code_tally_seven :
    (Finset.univ.filter (fun p : ZMod 7 × Fin 2 => orbitSeven p.1 = 1)).card =
      2 * ∑ r ∈ Finset.univ.image (fun x => orbitRep coprimeTwoSeven x),
        if orbitSeven r = 1 then (frobeniusOrbit coprimeTwoSeven r).card else 0 :=
  frobenius_code_weight_tally coprimeTwoSeven 2 orbitSeven orbitSeven_invariant 1

/-- The concrete length-two multiplicity is six. -/
theorem frobenius_code_tally_seven_numeric :
    (Finset.univ.filter (fun p : ZMod 7 × Fin 2 => orbitSeven p.1 = 1)).card = 6 := by
  rw [frobenius_code_tally_seven, frobenius_tally_seven_numeric]

/-! ## Parity-check dual at `q = 3` -/

/-- A nonzero two-by-two block over `ZMod 3`. -/
def blockThree : Fin 2 → Fin 2 → ZMod 3 :=
  fun a b => if a = 0 then 1 else if b = 0 then 1 else 0

/-- The explicit parity-check construction generates the dual code. -/
theorem parityCheck_dual_three :
    parityCheckCode blockThree = dualCode (systematicCode blockThree) :=
  parityCheckCode_eq_dualCode blockThree

/-- The parity-check block has the full rank two. -/
theorem parityCheck_finrank_three :
    Module.finrank (ZMod 3) (parityCheckCode blockThree) = 2 := by
  simpa using finrank_parityCheckCode (q := 3) blockThree

/-- A nonzero information word and a parity word used in the orthogonality check. -/
def informationWord : Fin 2 → ZMod 3 := fun a => if a = 0 then 1 else 0

/-- A nonzero parity word used in the orthogonality check. -/
def parityWord : Fin 2 → ZMod 3 := fun b => if b = 0 then 1 else 0

/-- The first parity-check coordinate is minus one in characteristic three. -/
theorem parityCheck_first_coordinate :
    parityCheckEncode blockThree parityWord (Sum.inl 0) = 2 := by
  change (-∑ b, blockThree 0 b * parityWord b) = 2
  rw [Fin.sum_univ_two]
  decide

/-- The concrete systematic and parity-check words are orthogonal. -/
theorem systematic_parityCheck_orthogonal :
    dot (systematicEncode blockThree informationWord)
      (parityCheckEncode blockThree parityWord) = 0 :=
  dot_systematic_parityCheck blockThree informationWord parityWord

/-- The concrete parity-check word belongs to the dual code. -/
theorem parityCheck_mem_dual_three :
    parityCheckEncode blockThree parityWord ∈ dualCode (systematicCode blockThree) := by
  rw [← parityCheck_dual_three]
  exact LinearMap.mem_range_self _ _

/-! ## Trace-code tallies at characteristic three -/

local instance : NeZero (ringChar (ZMod 3)) := by
  rw [ZMod.ringChar_zmod_n]
  infer_instance

local instance : Algebra (ZMod (ringChar (ZMod 3))) (ZMod 3) := by
  have h : ringChar (ZMod 3) = 3 := ZMod.ringChar_zmod_n 3
  exact h.symm ▸ (inferInstance : Algebra (ZMod 3) (ZMod 3))

/-- The length-one trace code uses the coordinate multiplier one. -/
def traceCoordinate : Fin 1 → ZMod 3 := fun _ => 1

/-- One spans the prime field over itself. -/
theorem traceCoordinate_span :
    Submodule.span (ZMod (ringChar (ZMod 3))) (Set.range traceCoordinate) = ⊤ := by
  apply top_unique
  intro x _
  have hone := Submodule.subset_span (R := ZMod (ringChar (ZMod 3)))
    (show (1 : ZMod 3) ∈ Set.range traceCoordinate from ⟨0, rfl⟩)
  simpa [nsmul_eq_mul, ZMod.natCast_zmod_val] using
    (Submodule.span (ZMod (ringChar (ZMod 3))) (Set.range traceCoordinate)).nsmul_mem hone x.val

/-- The two nonzero trace parameters occupy separate length-one shift orbits. -/
def traceOrbitsThree : TraceOrbits traceCoordinate 2 (Fintype.card (Fin 1)) := by
  refine
    { enumerate := (Equiv.optionCongr (Equiv.prodUnique (Fin 2) (Fin 1))).trans
        ((finSuccEquiv 2).symm.trans (ZMod.finEquiv 3).toEquiv)
      at_zero := rfl
      representative := fun i => ZMod.finEquiv 3 i.succ
      multiplier := fun _ => 1
      coordinate := fun _ => Equiv.refl _
      decode := ?_
      shift := by simp [traceCoordinate] }
  intro i j
  change ZMod.finEquiv 3 i.succ = ZMod.finEquiv 3 i.succ * 1
  simp

/-- The length-one trace code satisfies the Frobenius tally at positive weight one. -/
theorem traceCode_positive_weight_three :
    let index := (ZMod.finEquiv 2).toEquiv.symm
    let h : Nat.Coprime (ringChar (ZMod 3)) 2 := by
      rw [ZMod.ringChar_zmod_n]
      decide
    (Finset.univ.filter (fun c : traceCode traceCoordinate => hammingWeight c.val = 1)).card =
      Fintype.card (Fin 1) * ∑ r ∈ Finset.univ.image (fun x => orbitRep h x),
        if hammingWeight (traceWord traceCoordinate (traceOrbitsThree.representative (index r))) = 1
        then (frobeniusOrbit h r).card else 0 := by
  dsimp only
  refine traceCode_frobenius_weight_tally _ _ _ traceCoordinate_span traceOrbitsThree ?_ 1
    (by decide)
  intro x
  have hmul : (ringChar (ZMod 3) : ZMod 2) = 1 := by
    rw [ZMod.ringChar_zmod_n]
    decide
  rw [hmul, one_mul]

/-- The zero word is the unique weight-zero word of the concrete trace code. -/
theorem traceCode_zero_weight_three :
    (Finset.univ.filter (fun c : traceCode (id : ZMod 3 → ZMod 3) =>
      hammingWeight c.val = 0)).card = 1 :=
  traceCode_zero_weight_card (g := id)

end QatlibTests.Papers.PottsPartEval07.FrobeniusMembership
