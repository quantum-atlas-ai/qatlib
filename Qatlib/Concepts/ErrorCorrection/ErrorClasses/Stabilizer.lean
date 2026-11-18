/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstructionDefs
import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

/-!
# General signed-stabilizer distance and syndrome certificates

Weight, syndrome and span for arbitrary signed Pauli generator families,
with the minimum-distance certificate interface mirroring the classical
and CSS components. Everything here is stated at the binary symplectic
level, so phases track separately through the phase group.
-/

namespace Qatlib.Concepts.ErrorCorrection.ErrorClasses

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.ExactRank

/-- The Pauli weight counts non-identity letters; Y counts once per site. -/
def pauliWt {n : ℕ} (p : PauliElem n) : ℕ :=
  (Finset.univ.filter fun i => p.word i ≠ Pauli1.I).card

/-- The symplectic weight counts positions with a nonzero letter bit-pair. -/
def sympWt {n : ℕ} (v : BooleanVec n × BooleanVec n) : ℕ :=
  (Finset.univ.filter fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0).card

/-- Pauli weight agrees with symplectic weight on the symplectic vector. -/
theorem pauliWt_symp {n : ℕ} (p : PauliElem n) :
    pauliWt p = sympWt (symplecticX p.word, symplecticZ p.word) := by
  simp only [pauliWt, sympWt]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h : p.word i with a | a | a | a <;> simp [symplecticX, symplecticZ, h]

/-- The symplectic coordinates determine a Pauli word letter by letter. -/
theorem symp_word_inj {n : ℕ} {w w' : PauliWord n}
    (hx : symplecticX w = symplecticX w') (hz : symplecticZ w = symplecticZ w') :
    w = w' := by
  funext i
  have hxi := congrFun hx i
  have hzi := congrFun hz i
  rcases hw : w i with a | a | a | a <;> rcases hw' : w' i with b | b | b | b <;>
    simp [symplecticX, symplecticZ, hw, hw'] at hxi hzi ⊢

/-- The syndrome of a symplectic vector against a finite generator family. -/
def genSyn {n k : ℕ} (gs : Fin k → PauliElem n)
    (v : BooleanVec n × BooleanVec n) : Fin k → ZMod 2 :=
  fun i => symplecticForm v (symplecticX (gs i).word, symplecticZ (gs i).word)

/-- The binary span of the generators' symplectic vectors. -/
def sympSpan {n k : ℕ} (gs : Fin k → PauliElem n) :
    Submodule (ZMod 2) (BooleanVec n × BooleanVec n) :=
  Submodule.span (ZMod 2)
    (Set.range fun i : Fin k => (symplecticX (gs i).word, symplecticZ (gs i).word))

/-- Membership in the generator span is an explicit finite combination. -/
theorem mem_sympSpan_iff {n k : ℕ} (gs : Fin k → PauliElem n)
    (v : BooleanVec n × BooleanVec n) :
    v ∈ sympSpan gs ↔ ∃ c : Fin k → ZMod 2,
      ∑ i, c i • (symplecticX (gs i).word, symplecticZ (gs i).word) = v :=
  Submodule.mem_span_range_iff_exists_fun (R := ZMod 2)
    (v := fun i : Fin k => (symplecticX (gs i).word, symplecticZ (gs i).word)) (x := v)

/-- The error-label quotient by the signed generator span. -/
abbrev StabEquiv {n k : ℕ} (gs : Fin k → PauliElem n) :=
  (BooleanVec n × BooleanVec n) ⧸ sympSpan gs

/-- Two labels define the same error class exactly when their difference is a stabilizer. -/
theorem stab_equiv_eq {n k : ℕ} (gs : Fin k → PauliElem n)
    (v w : BooleanVec n × BooleanVec n) :
    (Submodule.Quotient.mk v : StabEquiv gs) = Submodule.Quotient.mk w ↔
      v - w ∈ sympSpan gs :=
  Submodule.Quotient.eq (sympSpan gs)

/-- The stabilizer distance: least symplectic weight with zero syndrome
outside the generator span. -/
noncomputable def stabDist {n k : ℕ} (gs : Fin k → PauliElem n) : ℕ∞ :=
  sInf {w : ℕ∞ | ∃ v, genSyn gs v = 0 ∧ v ∉ sympSpan gs ∧ (sympWt v : ℕ∞) = w}

/-- Any zero-syndrome non-span vector bounds the distance from above. -/
theorem stab_dist_le {n k : ℕ} (gs : Fin k → PauliElem n)
    {v : BooleanVec n × BooleanVec n} (hs : genSyn gs v = 0)
    (hn : v ∉ sympSpan gs) : stabDist gs ≤ (sympWt v : ℕ∞) :=
  sInf_le ⟨v, hs, hn, rfl⟩

/-- A lower bound excludes all low-weight zero-syndrome non-span vectors. -/
theorem stab_dist_ge_iff {n k : ℕ} (gs : Fin k → PauliElem n) (d : ℕ) :
    (d : ℕ∞) ≤ stabDist gs ↔
      ∀ v, genSyn gs v = 0 → sympWt v < d → v ∈ sympSpan gs := by
  rw [stabDist, le_sInf_iff]
  constructor
  · intro h v hs hw
    by_contra hmem
    exact absurd (by exact_mod_cast h _ ⟨v, hs, hmem, rfl⟩) (by omega)
  · rintro h w ⟨v, hs, hn, rfl⟩
    by_contra hlt
    have hlt' : sympWt v < d := by exact_mod_cast not_le.mp hlt
    exact absurd (h v hs hlt') hn

end Qatlib.Concepts.ErrorCorrection.ErrorClasses
