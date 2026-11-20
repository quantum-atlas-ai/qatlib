/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.Recovery.Stabilizer
public import Qatlib.Concepts.ErrorCorrection.Recovery.Kraus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Coherent correction in a signed stabilizer branch

The ordinary signed decoder acts by one scalar on the entire code in each corrected
syndrome branch. The scalar is zero for an incorrect syndrome and a global phase for the
correct syndrome. This form retains the coherences needed for the linear space of errors.
-/

namespace Qatlib.Concepts.ErrorCorrection.Recovery

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

/-- The correction operator after a specified joint syndrome projection. -/
noncomputable def stabBranch {n k : ℕ} (t : Tableau n k) (prog : StabProg t)
    (η : Fin k → ZMod 2) : Matrix (Reg n) (Reg n) ℂ :=
  op (labelPauli (prog.corr η)) * synProj t η

/-- Pauli operators with the same word differ by a scalar independent of the input. -/
private theorem word_phase {n : ℕ} {p q : PauliElem n} (h : p.word = q.word) :
    op p = ((Complex.I ^ p.phase.val : ℂ) * star (Complex.I ^ q.phase.val)) • op q := by
  simp only [op, h, smul_smul, mul_assoc, star_I_pow_mul_self, mul_one]

/-- A stabilizer decoder residual gives a common scalar on every code vector in each branch. -/
theorem signed_scalar {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t)
    (v : BooleanVec n × BooleanVec n)
    (hres : stabRes prog v ∈ sympSpan (fun a => (t a).decode))
    (η : Fin k → ZMod 2) :
    ∃ a : ℂ, ∀ ψ : QState (Reg n), ψ ∈ codeSpace t →
      stabBranch t prog η *ᵥ (op (labelPauli v) *ᵥ ψ) = a • ψ := by
  by_cases he : η = tabSyn t v
  · subst η
    let p := (labelPauli (prog.corr (tabSyn t v))).mul (labelPauli v)
    let w : tableauRowSpace t := ⟨stabRes prog v, by rwa [← span_to_row]⟩
    let q := tableauLift t hind w
    have hw : p.word = q.word := by
      apply symplecticVec_injective
      change symplecticVec ((labelPauli (prog.corr (tabSyn t v))).mul (labelPauli v)).word =
        symplecticVec (tableauLift t hind w).word
      rw [pauliElem_mul_word, symplecticVec_mul, label_vec, label_vec,
        tableauLift_symplecticVec]
      rfl
    refine ⟨(Complex.I ^ p.phase.val : ℂ) * star (Complex.I ^ q.phase.val), ?_⟩
    intro ψ hψ
    rw [stabBranch, ← Matrix.mulVec_mulVec, synProj_true t ht v ψ hψ,
      Matrix.mulVec_mulVec, ← op_mul]
    change op p *ᵥ ψ = _
    rw [word_phase hw, Matrix.smul_mulVec]
    rw [show op q *ᵥ ψ = ψ from tableauLift_fixes t hind ψ hψ w]
  · refine ⟨0, ?_⟩
    intro ψ hψ
    rw [stabBranch, ← Matrix.mulVec_mulVec, synProj_other t ht v η he ψ hψ,
      Matrix.mulVec_zero, zero_smul]

/-- For an encoding matrix with columns in the code, the corrected error branch is a scalar
multiple of the entire encoding. -/
theorem signed_columns {n k : ℕ} {L : Type*} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t)
    (v : BooleanVec n × BooleanVec n)
    (hres : stabRes prog v ∈ sympSpan (fun a => (t a).decode))
    (η : Fin k → ZMod 2) (V : Matrix (Reg n) L ℂ)
    (hV : ∀ j, (fun i => V i j) ∈ codeSpace t) :
    ∃ a : ℂ, stabBranch t prog η * op (labelPauli v) * V = a • V := by
  obtain ⟨a, ha⟩ := signed_scalar t ht hind prog v hres η
  refine ⟨a, Matrix.ext fun i j => ?_⟩
  have h := ha (fun b => V b j) (hV j)
  rw [Matrix.mulVec_mulVec] at h
  exact congrFun h i

/-- The two effects of the binary measurement of a signed generator. -/
noncomputable def generatorHalf {n : ℕ} (g : PauliElem n) (b : ZMod 2) :
    Matrix (Reg n) (Reg n) ℂ :=
  (2⁻¹ : ℂ) • (1 + if b = 0 then op g else -op g)

/-- The two signed effects of each generator sum to the identity. -/
private theorem half_total {n : ℕ} (g : PauliElem n) :
    ∑ b : ZMod 2, generatorHalf g b = 1 := by
  let e := (ZMod.finEquiv 2).toEquiv
  have h : (∑ b : ZMod 2, generatorHalf g b) = ∑ b : Fin 2, generatorHalf g (e b) := by
    apply Fintype.sum_equiv e.symm
    intro b
    rw [Equiv.apply_symm_apply]
  rw [h, Fin.sum_univ_two]
  have hzero : e 0 = 0 := map_zero (ZMod.finEquiv 2)
  have hone : e 1 = 1 := map_one (ZMod.finEquiv 2)
  rw [hzero, hone]
  unfold generatorHalf
  rw [ite_eq_left (show (0 : ZMod 2) = 0 from rfl),
    ite_eq_right (by decide : (1 : ZMod 2) ≠ 0)]
  rw [← smul_add]
  have hcancel : ((1 : Matrix (Reg n) (Reg n) ℂ) + op g) + (1 + -op g) =
      (2 : ℂ) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
    rw [two_smul]
    abel
  rw [hcancel, smul_smul]
  norm_num

/-- Splitting off the first syndrome bit splits off the first projector factor. -/
private theorem proj_cons {n k : ℕ} (t : Tableau n (k + 1)) (η : Fin (k + 1) → ZMod 2) :
    synProj t η = generatorHalf (t 0).decode (η 0) *
      synProj (fun i : Fin k => t i.succ) (fun i => η i.succ) := by
  change projectorAux ((List.finRange (k + 1)).map (synGen t η)) = _
  rw [List.finRange_succ, List.map_cons, projectorAux_cons, ← Matrix.smul_mul,
    op_synGen, List.map_map]
  rfl

/-- Summing all branches of the ordered signed measurement gives the identity. -/
theorem signedProj_sum {n k : ℕ} (t : Tableau n k) : ∑ η, synProj t η = 1 := by
  induction k with
  | zero =>
    let : Unique (Fin 0 → ZMod 2) :=
      ⟨⟨fun i => Fin.elim0 i⟩, fun _ => funext fun i => Fin.elim0 i⟩
    simp [synProj, stabilizerProjector, synGens, projectorAux]
  | succ k ih =>
    let tail : Tableau n k := fun i => t i.succ
    calc
      _ = ∑ p : ZMod 2 × (Fin k → ZMod 2),
          generatorHalf (t 0).decode p.1 * synProj tail p.2 := by
        apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => ZMod 2)).symm
        intro η
        exact proj_cons t η
      _ = 1 := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Matrix.mul_sum, ih tail, mul_one]
        exact half_total _

/-- For a consistent tableau, a corrected syndrome branch has the original syndrome effect. -/
private theorem stab_effect {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (prog : StabProg t) (η : Fin k → ZMod 2) :
    (stabBranch t prog η)ᴴ * stabBranch t prog η = synProj t η := by
  let U := op (labelPauli (prog.corr η))
  let P := synProj t η
  have hU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp (op_unitary (labelPauli (prog.corr η)))
    rwa [Matrix.star_eq_conjTranspose] at h
  have hP : P * P = P := projectorAux_mul_self (synGens t η) (syn_cons t ht η)
  change (U * P)ᴴ * (U * P) = P
  calc
    _ = Pᴴ * ((Uᴴ * U) * P) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hU, one_mul, show Pᴴ = P from synProj_star t ht η, hP]

/-- Reindex the code embedding from Boolean registers into the public channel basis. -/
noncomputable def regEncoding {n l : ℕ} (V : Matrix (Reg n) (Fin l) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin l) ℂ :=
  Matrix.reindexLinearEquiv ℂ ℂ (bitVecEquiv n) (Equiv.refl (Fin l)) V

/-- A finite-dimensional code space admits an orthonormal encoding with a column for each
basis vector, also isometric after reindexing to the channel basis. -/
theorem exists_regEnc {n k l : ℕ} (t : Tableau n k)
    (hl : Module.finrank ℂ (codeSpace t) = l) :
    ∃ V : Matrix (Reg n) (Fin l) ℂ,
      (∀ j, (fun i => V i j) ∈ codeSpace t) ∧ (regEncoding V)ᴴ * regEncoding V = 1 := by
  classical
  let e := (WithLp.linearEquiv 2 ℂ (Reg n → ℂ)).symm
  let S := (codeSpace t).map e.toLinearMap
  have hdim : Module.finrank ℂ S = l := (e.finrank_map_eq _).trans hl
  let b := (stdOrthonormalBasis ℂ S).reindex (finCongr hdim)
  let V : Matrix (Reg n) (Fin l) ℂ := fun i j => e.symm (b j).val i
  have hV (j : Fin l) : (fun i => V i j) ∈ codeSpace t := by
    obtain ⟨x, hx, he⟩ := (b j).property
    change e.symm (b j).val ∈ codeSpace t
    rw [← he]
    exact hx
  have hGram : Vᴴ * V = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hinner : (∑ a, star ((b i).val a) * (b j).val a) = inner ℂ (b i) (b j) := by
      change (∑ a, star ((b i).val a) * (b j).val a) =
        ∑ a, (b j).val a * star ((b i).val a)
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    change (∑ a, star ((b i).val a) * (b j).val a) = (1 : Matrix (Fin l) (Fin l) ℂ) i j
    simpa only [Matrix.one_apply] using hinner.trans (b.inner_eq_ite i j)
  refine ⟨V, hV, ?_⟩
  let r := bitVecEquiv n
  let f := Equiv.refl (Fin l)
  change (Matrix.reindexLinearEquiv ℂ ℂ r f V)ᴴ *
    Matrix.reindexLinearEquiv ℂ ℂ r f V = 1
  have hstar : (Matrix.reindexLinearEquiv ℂ ℂ r f V)ᴴ =
      Matrix.reindexLinearEquiv ℂ ℂ f r Vᴴ := Matrix.conjTranspose_reindex r f V
  rw [hstar, Matrix.reindexLinearEquiv_mul, hGram, Matrix.reindexLinearEquiv_one]

/-- The finite signed recovery branches in the public channel basis. -/
noncomputable def regRecovery {n k : ℕ} (t : Tableau n k) (prog : StabProg t)
    (i : Fin (Fintype.card (Fin k → ZMod 2))) : Operator (2 ^ n) :=
  Matrix.reindexLinearEquiv ℂ ℂ (bitVecEquiv n) (bitVecEquiv n)
    (stabBranch t prog ((Fintype.equivFin (Fin k → ZMod 2)).symm i))

/-- The actual signed recovery branches form a complete Kraus family. -/
theorem regRec_complete {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (prog : StabProg t) : KrausComplete (regRecovery t prog) := by
  let e := bitVecEquiv n
  let T := Matrix.reindexAlgEquiv ℂ ℂ e
  let s := Fintype.equivFin (Fin k → ZMod 2)
  have hstar (M : Matrix (Reg n) (Reg n) ℂ) : (T M)ᴴ = T Mᴴ :=
    Matrix.conjTranspose_reindex e e M
  unfold KrausComplete
  calc
    _ = ∑ η, T (synProj t η) := by
      symm
      apply Fintype.sum_equiv s
      intro η
      have hreg : regRecovery t prog (s η) = T (stabBranch t prog η) := by
        simp only [regRecovery, s, Equiv.symm_apply_apply]
        rfl
      rw [hreg, hstar, ← map_mul, stab_effect t ht prog η]
    _ = 1 := by rw [← map_sum, signedProj_sum, map_one]

/-- Applying the finite Kraus family is the public signed recovery channel after register
reindexing. -/
theorem regRec_map {n k : ℕ} (t : Tableau n k) (prog : StabProg t)
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    let T := Matrix.reindexAlgEquiv ℂ ℂ (bitVecEquiv n)
    krausMap (regRecovery t prog) (T ρ) = T (stabRecCh t prog ρ) := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ (bitVecEquiv n)
  let s := Fintype.equivFin (Fin k → ZMod 2)
  have hstar (M : Matrix (Reg n) (Reg n) ℂ) : (T M)ᴴ = T Mᴴ :=
    Matrix.conjTranspose_reindex _ _ M
  change krausMap (regRecovery t prog) (T ρ) = T (stabRecCh t prog ρ)
  simp only [krausMap, LinearMap.sum_apply, conjBranch_apply, stabRecCh, map_sum]
  symm
  apply Fintype.sum_equiv s
  intro η
  have hreg : regRecovery t prog (s η) = T (stabBranch t prog η) := by
    simp only [regRecovery, s, Equiv.symm_apply_apply]
    rfl
  rw [hreg, hstar, ← map_mul, ← map_mul]
  congr 1
  simp only [stabBranch, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The error operator in the public channel basis for a fixed binary Pauli label. -/
noncomputable def regError {n : ℕ} (v : BooleanVec n × BooleanVec n) : Operator (2 ^ n) :=
  Matrix.reindexLinearEquiv ℂ ℂ (bitVecEquiv n) (bitVecEquiv n) (op (labelPauli v))

/-- An error with a stabilizer residual belongs to the channel's correctable linear space. -/
theorem signed_correct {n k l : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t)
    (v : BooleanVec n × BooleanVec n)
    (hres : stabRes prog v ∈ sympSpan (fun a => (t a).decode))
    (V : Matrix (Reg n) (Fin l) ℂ) (hV : ∀ j, (fun i => V i j) ∈ codeSpace t) :
    regError v ∈ correctable (regEncoding V) (regRecovery t prog) := by
  rw [mem_correctable]
  intro i
  obtain ⟨a, ha⟩ := signed_columns t ht hind prog v hres
    ((Fintype.equivFin (Fin k → ZMod 2)).symm i) V hV
  refine ⟨a, ?_⟩
  rw [regRecovery, regError, regEncoding, Matrix.reindexLinearEquiv_mul,
    Matrix.reindexLinearEquiv_mul, ha, map_smul]

/-- The span of the bounded Pauli errors is correctable under the ordinary decoder contract. -/
theorem signed_span {n k l : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t) (r : ℕ)
    (hp : StabCorrects prog r)
    (V : Matrix (Reg n) (Fin l) ℂ) (hV : ∀ j, (fun i => V i j) ∈ codeSpace t) :
    Submodule.span ℂ {A | ∃ v, sympWt v ≤ r ∧ A = regError v} ≤
      correctable (regEncoding V) (regRecovery t prog) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact signed_correct t ht hind prog v (hp v hv) V hV

/-- The signed decoder corrects complete noise built from its bounded Pauli span, including
on arbitrary operators encoded together with a finite reference system. -/
theorem signed_ref {n k l q ref : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t) (r : ℕ)
    (hp : StabCorrects prog r)
    (V : Matrix (Reg n) (Fin l) ℂ) (hV : ∀ j, (fun i => V i j) ∈ codeSpace t)
    (hIso : (regEncoding V)ᴴ * regEncoding V = 1)
    (K : Fin q → Operator (2 ^ n)) (hK : KrausComplete K)
    (hspan : ∀ i, K i ∈ Submodule.span ℂ {A | ∃ v, sympWt v ≤ r ∧ A = regError v})
    (A : Matrix (Fin l × Fin ref) (Fin l × Fin ref) ℂ) :
    tensorLeft (krausMap (regRecovery t prog))
      (tensorLeft (krausMap K) (tensorLeft (conjBranch (regEncoding V)) A)) =
        tensorLeft (conjBranch (regEncoding V)) A :=
  recovers_ref (regEncoding V) hIso (regRecovery t prog) (regRec_complete t ht prog) K hK
    (fun i => signed_span t ht hind prog r hp V hV (hspan i)) A

end Qatlib.Concepts.ErrorCorrection.Recovery
