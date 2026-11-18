/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.ErrorClasses.Stabilizer
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.AffineStabilizerStateBridge
public import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

@[expose] public section

/-!
# Recovery for general signed-stabilizer tableaux

A decoder acts on binary symplectic labels, while errors and corrections act on
states through their genuine signed Pauli operators. Joint syndrome projectors
are ordered products of positive and negative generator branches. A residual in
the generator row space is lifted to a signed stabilizer, proving fixed-Pauli
pure-state density recovery without asserting arbitrary-noise correction or a
dynamic extraction circuit.
-/

namespace Qatlib.Concepts.ErrorCorrection.Recovery

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open scoped Matrix

/-- The phase-zero signed Pauli operator associated with a binary label. -/
def labelPauli {n : ℕ} (v : BooleanVec n × BooleanVec n) : PauliElem n :=
  (pauliRow v.1 v.2 0).decode

/-- The binary coordinates of a phase-zero label are the label itself. -/
theorem label_symp {n : ℕ} (v : BooleanVec n × BooleanVec n) :
    (symplecticX (labelPauli v).word, symplecticZ (labelPauli v).word) = v := by
  exact symplecticVec_pauliRow v.1 v.2 0

/-- The packed symplectic vector of a phase-zero label is the label itself. -/
theorem label_vec {n : ℕ} (v : BooleanVec n × BooleanVec n) :
    symplecticVec (labelPauli v).word = v := label_symp v

/-- Syndrome against the decoded rows of a signed tableau. -/
def tabSyn {n k : ℕ} (t : Tableau n k) (v : BooleanVec n × BooleanVec n) : Fin k → ZMod 2 :=
  genSyn (fun a => (t a).decode) v

/-- A syndrome-dependent correction program for a general stabilizer tableau. -/
structure StabProg {n k : ℕ} (t : Tableau n k) where
  corr : (Fin k → ZMod 2) → BooleanVec n × BooleanVec n

/-- The correction followed by the input error, at the binary label level. -/
def stabRes {n k : ℕ} {t : Tableau n k} (prog : StabProg t)
    (v : BooleanVec n × BooleanVec n) : BooleanVec n × BooleanVec n :=
  prog.corr (tabSyn t v) + v

/-- Bounded errors have a stabilizer residual after applying the actual decoder. -/
def StabCorrects {n k : ℕ} {t : Tableau n k} (prog : StabProg t) (r : ℕ) : Prop :=
  ∀ v, sympWt v ≤ r → stabRes prog v ∈ sympSpan (fun a => (t a).decode)

/-- The signed generator selecting the positive or negative syndrome branch. -/
def synGen {n k : ℕ} (t : Tableau n k) (η : Fin k → ZMod 2) (a : Fin k) : PauliElem n :=
  if η a = 0 then (t a).decode else negPauliElem (t a).decode

/-- Signed generators in row order for a joint syndrome projector. -/
def synGens {n k : ℕ} (t : Tableau n k) (η : Fin k → ZMod 2) : List (PauliElem n) :=
  (List.finRange k).map (synGen t η)

/-- Membership in the signed generator list is membership in the row family. -/
theorem mem_synGens {n k : ℕ} (t : Tableau n k) (η : Fin k → ZMod 2) (h : PauliElem n) :
    h ∈ synGens t η ↔ ∃ a, synGen t η a = h := by
  rw [synGens, List.mem_map]
  constructor
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, List.mem_finRange a, rfl⟩

/-- A signed branch generator acts by the generator or its negative. -/
theorem op_synGen {n k : ℕ} (t : Tableau n k) (η : Fin k → ZMod 2) (a : Fin k) :
    op (synGen t η a) = if η a = 0 then op (t a).decode else -op (t a).decode := by
  by_cases ha : η a = 0 <;> simp [synGen, ha, op_negPauliElem]

/-- Signed branch generators inherit Hermitian consistency from the tableau. -/
theorem syn_cons {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (η : Fin k → ZMod 2) : CommutingHermitianPaulis (synGens t η) := by
  constructor
  · intro h hh
    obtain ⟨a, rfl⟩ := (mem_synGens t η h).mp hh
    by_cases ha : η a = 0
    · simpa [synGen, ha] using ht.1 a
    · simpa [synGen, ha] using negPauliElem_hermitian (t a).decode (ht.1 a)
  · intro h hh g hg
    obtain ⟨a, rfl⟩ := (mem_synGens t η h).mp hh
    obtain ⟨b, rfl⟩ := (mem_synGens t η g).mp hg
    by_cases ha : η a = 0 <;> by_cases hb : η b = 0 <;>
      simp [op_synGen, ha, hb, ht.2 a b]

/-- The joint projector onto a specified tableau syndrome. -/
noncomputable def synProj {n k : ℕ} (t : Tableau n k) (η : Fin k → ZMod 2) :
    Matrix (Reg n) (Reg n) ℂ :=
  stabilizerProjector (synGens t η)

/-- A zero-syndrome generator commutes with the error label. -/
theorem gen_comm {n k : ℕ} (t : Tableau n k) (v : BooleanVec n × BooleanVec n)
    (a : Fin k) (hs : tabSyn t v a = 0) :
    op (t a).decode * op (labelPauli v) = op (labelPauli v) * op (t a).decode := by
  have hf : symplecticForm (symplecticVec (t a).decode.word) v = 0 := by
    rw [symplecticForm_comm]
    exact hs
  rw [op_mul_comm_symplectic, label_symp]
  rw [show (symplecticX (t a).decode.word, symplecticZ (t a).decode.word)
    = symplecticVec (t a).decode.word from rfl, hf]
  simp

/-- A nonzero-syndrome generator anticommutes with the error label. -/
theorem gen_anti {n k : ℕ} (t : Tableau n k) (v : BooleanVec n × BooleanVec n)
    (a : Fin k) (hs : tabSyn t v a ≠ 0) :
    op (t a).decode * op (labelPauli v) = -(op (labelPauli v) * op (t a).decode) := by
  have hc : tabSyn t v a = 0 ∨ tabSyn t v a = 1 := by
    have hall : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact hall _
  have hs1 : tabSyn t v a = 1 := by
    rcases hc with h0 | h1
    · exact absurd h0 hs
    · exact h1
  have hf : symplecticForm (symplecticVec (t a).decode.word) v = 1 := by
    rw [symplecticForm_comm]
    exact hs1
  rw [op_mul_comm_symplectic, label_symp]
  rw [show (symplecticX (t a).decode.word, symplecticZ (t a).decode.word)
    = symplecticVec (t a).decode.word from rfl, hf]
  rw [ZMod.val_one 2]
  norm_num

/-- A commuting generator stabilizes the corrupted code vector. -/
theorem gen_fix {n k : ℕ} (t : Tableau n k) (v : BooleanVec n × BooleanVec n)
    (a : Fin k) (hs : tabSyn t v a = 0) (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    op (t a).decode *ᵥ (op (labelPauli v) *ᵥ ψ) = op (labelPauli v) *ᵥ ψ := by
  rw [Matrix.mulVec_mulVec, gen_comm t v a hs, ← Matrix.mulVec_mulVec,
    (mem_codeSpace_iff t ψ).mp hψ a]

/-- An anticommuting generator negates the corrupted code vector. -/
theorem gen_neg {n k : ℕ} (t : Tableau n k) (v : BooleanVec n × BooleanVec n)
    (a : Fin k) (hs : tabSyn t v a ≠ 0) (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    op (t a).decode *ᵥ (op (labelPauli v) *ᵥ ψ) = -(op (labelPauli v) *ᵥ ψ) := by
  rw [Matrix.mulVec_mulVec, gen_anti t v a hs, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
    (mem_codeSpace_iff t ψ).mp hψ a]

/-- The signed generator for the true branch fixes the corrupted code vector. -/
theorem synGen_fix {n k : ℕ} (t : Tableau n k) (v : BooleanVec n × BooleanVec n)
    (η : Fin k → ZMod 2) (a : Fin k) (he : η a = tabSyn t v a)
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    op (synGen t η a) *ᵥ (op (labelPauli v) *ᵥ ψ) = op (labelPauli v) *ᵥ ψ := by
  by_cases ha : η a = 0
  · have hs : tabSyn t v a = 0 := by rw [← he]; exact ha
    simpa [op_synGen, ha] using gen_fix t v a hs ψ hψ
  · have hs : tabSyn t v a ≠ 0 := by
      intro hz
      apply ha
      rw [he, hz]
    rw [op_synGen]
    simp only [ha, ↓reduceIte, Matrix.neg_mulVec, gen_neg t v a hs ψ hψ, neg_neg]

/-- The signed generator for a wrong branch negates the corrupted code vector. -/
theorem synGen_neg {n k : ℕ} (t : Tableau n k) (v : BooleanVec n × BooleanVec n)
    (η : Fin k → ZMod 2) (a : Fin k) (he : η a ≠ tabSyn t v a)
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    op (synGen t η a) *ᵥ (op (labelPauli v) *ᵥ ψ) = -(op (labelPauli v) *ᵥ ψ) := by
  by_cases ha : η a = 0
  · have hs : tabSyn t v a ≠ 0 := by
      intro hz
      apply he
      rw [ha, hz]
    simpa [op_synGen, ha] using gen_neg t v a hs ψ hψ
  · have hs : tabSyn t v a = 0 := by
      have hc : tabSyn t v a = 0 ∨ tabSyn t v a = 1 := by
        have hall : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
        exact hall _
      rcases hc with h0 | h1
      · exact h0
      · exfalso
        apply he
        rw [h1]
        have ha1 : η a = 1 := by
          have hall : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
          rcases hall (η a) with h0 | h1'
          · exact absurd h0 ha
          · exact h1'
        exact ha1
    rw [op_synGen]
    simp only [ha, ↓reduceIte, Matrix.neg_mulVec, gen_fix t v a hs ψ hψ]

/-- The true joint syndrome projector fixes the corrupted code vector. -/
theorem synProj_true {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (v : BooleanVec n × BooleanVec n) (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    synProj t (tabSyn t v) *ᵥ (op (labelPauli v) *ᵥ ψ) = op (labelPauli v) *ᵥ ψ := by
  apply (projectorAux_mulVec_iff (synGens t (tabSyn t v))
    (syn_cons t ht (tabSyn t v)).1 (syn_cons t ht (tabSyn t v)).2 _).mpr
  intro h hh
  obtain ⟨a, rfl⟩ := (mem_synGens t (tabSyn t v) h).mp hh
  exact synGen_fix t v (tabSyn t v) a rfl ψ hψ

/-- Every other joint syndrome projector annihilates the corrupted code vector. -/
theorem synProj_other {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (v : BooleanVec n × BooleanVec n) (η : Fin k → ZMod 2) (hη : η ≠ tabSyn t v)
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    synProj t η *ᵥ (op (labelPauli v) *ᵥ ψ) = 0 := by
  have hex : ∃ a, η a ≠ tabSyn t v a := by
    by_contra hn
    apply hη
    funext a
    by_contra ha
    exact hn ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hex
  have hm : synGen t η a ∈ synGens t η := (mem_synGens t η _).mpr ⟨a, rfl⟩
  have hmul := projectorAux_mul_gen (synGens t η) (syn_cons t ht η).1
    (syn_cons t ht η).2 (synGen t η a) hm
  have hc := projectorAux_comm (synGen t η a) (synGens t η)
    (fun g hg => (syn_cons t ht η).2 (synGen t η a) hm g hg)
  have hPm : synProj t η * op (synGen t η a) = synProj t η := by
    change projectorAux (synGens t η) * op (synGen t η a) = projectorAux (synGens t η)
    rw [← hc, hmul]
  have hv : synProj t η *ᵥ (op (synGen t η a) *ᵥ (op (labelPauli v) *ᵥ ψ))
      = synProj t η *ᵥ (op (labelPauli v) *ᵥ ψ) := by
    rw [Matrix.mulVec_mulVec, hPm]
  rw [synGen_neg t v η a ha ψ hψ, Matrix.mulVec_neg] at hv
  have h2 := congrArg (fun y => y + synProj t η *ᵥ (op (labelPauli v) *ᵥ ψ)) hv
  simp only [neg_add_cancel] at h2
  have htwo : (2 : ℂ) • (synProj t η *ᵥ (op (labelPauli v) *ᵥ ψ)) = 0 := by
    simpa [two_smul] using h2.symm
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The joint syndrome projector is Hermitian. -/
theorem synProj_star {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (η : Fin k → ZMod 2) : (synProj t η)ᴴ = synProj t η := by
  exact projectorAux_star (synGens t η) (syn_cons t ht η)

/-- Conjugating an outer product by a matrix gives the outer product of its action. -/
theorem out_mul {I : Type*} [Fintype I]
    (M : Matrix I I ℂ) (ψ : QState I) :
    M * outerProduct ψ * Mᴴ = outerProduct (M *ᵥ ψ) := by
  classical
  ext a b
  have hL : (M * outerProduct ψ * Mᴴ) a b =
      ∑ k : I, ∑ l : I, (M a k * ψ k) * (star (M b l) * star (ψ l)) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, outerProduct,
      Matrix.of_apply, Complex.star_def, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  have hR : outerProduct (M *ᵥ ψ) a b =
      (∑ k, M a k * ψ k) * (∑ l, star (M b l) * star (ψ l)) := by
    simp only [outerProduct, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Complex.star_def, map_sum, map_mul]
  have key : (∑ k : I, ∑ l : I, (M a k * ψ k) * (star (M b l) * star (ψ l))) =
      (∑ k, M a k * ψ k) * (∑ l, star (M b l) * star (ψ l)) :=
    (Fintype.sum_mul_sum _ _).symm
  exact hL.trans (key.trans hR.symm)

/-- A Hermitian matrix can be used on both sides of an outer product. -/
theorem out_herm {I : Type*} [Fintype I]
    (P : Matrix I I ℂ) (hH : P.IsHermitian) (ψ : QState I) :
    P * outerProduct ψ * P = outerProduct (P *ᵥ ψ) := by
  have h := out_mul P ψ
  rw [hH.eq] at h
  exact h

/-- Scaling a vector scales its outer product by the squared complex modulus. -/
theorem out_smul {I : Type*} (z : ℂ) (ψ : QState I) :
    outerProduct (z • ψ) = (z * star z) • outerProduct ψ := by
  ext a b
  simp only [outerProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Complex.star_def, map_mul, Matrix.smul_apply]
  ring

/-- The outer product of the zero vector is the zero matrix. -/
theorem out_zero {I : Type*} : outerProduct (0 : QState I) = 0 := by
  ext a b
  simp [outerProduct]

/-- The general signed-stabilizer recovery channel. -/
noncomputable def stabRecCh {n k : ℕ} (t : Tableau n k) (prog : StabProg t)
    (ρ : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ η : Fin k → ZMod 2,
    op (labelPauli (prog.corr η)) * (synProj t η * ρ * (synProj t η)ᴴ) *
      (op (labelPauli (prog.corr η)))ᴴ

/-- The recovery channel acts termwise on a pure-state density matrix. -/
theorem stabCh_out {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (prog : StabProg t) (w : QState (Reg n)) :
    stabRecCh t prog (outerProduct w) =
      ∑ η : Fin k → ZMod 2,
        outerProduct (op (labelPauli (prog.corr η)) *ᵥ (synProj t η *ᵥ w)) := by
  classical
  unfold stabRecCh
  apply Finset.sum_congr rfl
  intro η _
  have hH : (synProj t η).IsHermitian := synProj_star t ht η
  rw [hH.eq, out_herm (synProj t η) hH, out_mul]

/-- The binary generator span is exactly the tableau row space. -/
theorem span_to_row {n k : ℕ} (t : Tableau n k) :
    sympSpan (fun a => (t a).decode) = tableauRowSpace t := by
  unfold sympSpan tableauRowSpace
  change Submodule.span (ZMod 2) (Set.range (rowSympVec t)) = _
  congr 1
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rowEquiv t a, symplecticVecOfFn_rowEquiv t a⟩
  · rintro ⟨j, rfl⟩
    refine ⟨(rowEquiv t).symm j, ?_⟩
    rw [← symplecticVecOfFn_rowEquiv t ((rowEquiv t).symm j)]
    simp

/-- Pauli elements with the same symplectic word have equal pure-state densities. -/
theorem out_same {n : ℕ} {p q : PauliElem n}
    (h : symplecticVec p.word = symplecticVec q.word) (ψ : QState (Reg n)) :
    outerProduct (op p *ᵥ ψ) =
      outerProduct (op q *ᵥ ψ) := by
  have hw : p.word = q.word := symplecticVec_injective h
  simp only [op, hw]
  simp only [Matrix.smul_mulVec]
  rw [out_smul, out_smul]
  have ha : (Complex.I ^ p.phase.val : ℂ) * star (Complex.I ^ p.phase.val : ℂ) = 1 := by
    rw [mul_comm]
    exact star_I_pow_mul_self p.phase.val
  have hb : (Complex.I ^ q.phase.val : ℂ) * star (Complex.I ^ q.phase.val : ℂ) = 1 := by
    rw [mul_comm]
    exact star_I_pow_mul_self q.phase.val
  rw [ha, hb]

/-- A stabilizer residual restores the pure-state density after its fixed Pauli error. -/
theorem stab_recovers {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t)
    (v : BooleanVec n × BooleanVec n)
    (hres : stabRes prog v ∈ sympSpan (fun a => (t a).decode))
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    stabRecCh t prog (outerProduct (op (labelPauli v) *ᵥ ψ)) =
      outerProduct ψ := by
  classical
  rw [stabCh_out t ht, Finset.sum_eq_single (tabSyn t v)]
  · rw [synProj_true t ht v ψ hψ, Matrix.mulVec_mulVec, ← op_mul]
    let w : tableauRowSpace t := ⟨stabRes prog v, by rwa [← span_to_row]⟩
    have hfix := tableauLift_fixes t hind ψ hψ w
    have hsame : symplecticVec
        ((labelPauli (prog.corr (tabSyn t v))).mul (labelPauli v)).word =
        symplecticVec (tableauLift t hind w).word := by
      rw [pauliElem_mul_word, symplecticVec_mul, label_vec, label_vec,
        tableauLift_symplecticVec]
      rfl
    exact (out_same hsame ψ).trans (by rw [hfix])
  · intro η _ hη
    rw [synProj_other t ht v η hη ψ hψ, Matrix.mulVec_zero, out_zero]
  · simp

/-- A signed Pauli error differs from its binary label only by an irrelevant global phase. -/
theorem stab_rec_signed {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t)
    (e : PauliElem n)
    (hres : stabRes prog (symplecticVec e.word) ∈ sympSpan (fun a => (t a).decode))
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    stabRecCh t prog (outerProduct (op e *ᵥ ψ)) =
      outerProduct ψ := by
  have hsame : symplecticVec e.word =
      symplecticVec (labelPauli (symplecticVec e.word)).word := by
    exact (label_symp (symplecticVec e.word)).symm
  rw [out_same hsame ψ]
  exact stab_recovers t ht hind prog (symplecticVec e.word) hres ψ hψ

end Qatlib.Concepts.ErrorCorrection.Recovery
