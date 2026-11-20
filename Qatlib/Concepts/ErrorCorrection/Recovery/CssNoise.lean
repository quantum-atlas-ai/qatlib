/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
public import Qatlib.Concepts.ErrorCorrection.Recovery.Kraus

@[expose] public section

/-!
# Complete CSS recovery for coherent error spaces

The existing CSS recovery program supplies the actual Kraus branches. The proof uses the
CSS decoder's stabilizer-residual contract and works with redundant checks.
-/

namespace Qatlib.Concepts.ErrorCorrection.Recovery

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
  [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]

/-- The two consecutive Pauli factors acting on CSS coordinates. -/
noncomputable def cssError (e : PauliLabel ι) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  cssPauliX e.1 * cssPauliZ e.2

/-- A CSS recovery branch measures the joint syndrome and applies the prescribed correction. -/
noncomputable def cssBranch (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  cssError (prog.corr η) * cssSyndromeProjector c η

/-- The scalar action of a CSS correction branch is uniform over the code space. -/
private theorem css_scalar (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (e : PauliLabel ι) (he : IsStabilizerLabel c (residualLabel prog e))
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    ∃ a : ℂ, ∀ ψ : QState (ι → ZMod 2), ψ ∈ cssCodespace c →
      cssBranch c prog η *ᵥ (cssError e *ᵥ ψ) = a • ψ := by
  by_cases h : η = pauliSyndrome c e
  · subst η
    let r := prog.corr (pauliSyndrome c e)
    refine ⟨phaseOfBit (bitDot r.2 e.1), ?_⟩
    intro ψ hψ
    simp only [cssBranch, cssError]
    rw [← Matrix.mulVec_mulVec,
      syndromeProjector_fixes_pauli c e ψ hψ, Matrix.mulVec_mulVec, cssPauliXZ_mul,
      Matrix.smul_mulVec]
    have hfix := isStabilizerLabel_fixes c he ψ hψ
    have hr : (cssPauliX (r.1 + e.1) * cssPauliZ (r.2 + e.2)) *ᵥ ψ = ψ := by
      simpa only [residualLabel, residualFromObserved, add_comm] using! hfix
    exact congrArg (fun v => phaseOfBit (bitDot r.2 e.1) • v) hr
  · refine ⟨0, ?_⟩
    intro ψ hψ
    simp only [cssBranch, cssError]
    rw [← Matrix.mulVec_mulVec,
      syndromeProjector_other_pauli c e ψ hψ η h, Matrix.mulVec_zero, zero_smul]

/-- The effect of a corrected CSS branch remains the joint syndrome projection. -/
private theorem css_effect (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    (cssBranch c prog η)ᴴ * cssBranch c prog η = cssSyndromeProjector c η := by
  let e := prog.corr η
  let X := cssPauliX e.1
  let Z := cssPauliZ e.2
  let P := cssSyndromeProjector c η
  have hU : (X * Z)ᴴ * (X * Z) = 1 := by
    rw [Matrix.conjTranspose_mul, (cssPauliX_isHermitian e.1).eq,
      (cssPauliZ_isHermitian e.2).eq]
    calc
      Z * X * (X * Z) = Z * ((X * X) * Z) := by simp only [mul_assoc]
      _ = 1 := by rw [show X * X = 1 from cssPauliX_self_mul _, one_mul, cssPauliZ_self_mul]
  change (X * Z * P)ᴴ * (X * Z * P) = P
  calc
    _ = Pᴴ * (((X * Z)ᴴ * (X * Z)) * P) := by
      simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = P := by
      rw [hU, one_mul, show Pᴴ = P from (cssSyndromeProjector_isHermitian c η).eq]
      rw [cssSyndromeProjector_mul, ite_eq_left rfl]

/-- The matrix of a CSS embedding in the finite channel basis. -/
noncomputable def cssEmbedding {l : ℕ} (V : Matrix (ι → ZMod 2) (Fin l) ℂ) :
    Matrix (Fin (Fintype.card (ι → ZMod 2))) (Fin l) ℂ :=
  Matrix.reindexLinearEquiv ℂ ℂ (Fintype.equivFin (ι → ZMod 2)) (Equiv.refl _) V

omit [Fintype κX] [Fintype κZ] [DecidableEq κX] [DecidableEq κZ] in
/-- An orthonormal CSS encoding with logical basis reindexed by a finite ordinal is isometric
in the channel basis. -/
theorem cssEmbedding_iso {k l : ℕ} {c : CssData ι κX κZ} (enc : CssEncoding c k)
    (e : Fin l ≃ (Fin k → ZMod 2)) :
    let V : Matrix (ι → ZMod 2) (Fin l) ℂ := fun x j => enc.enc (e j) x
    (cssEmbedding V)ᴴ * cssEmbedding V = 1 := by
  let V : Matrix (ι → ZMod 2) (Fin l) ℂ := fun x j => enc.enc (e j) x
  have hGram : Vᴴ * V = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    change coeffInner (enc.enc (e i)) (enc.enc (e j)) = (1 : Matrix (Fin l) (Fin l) ℂ) i j
    simpa only [Matrix.one_apply, e.apply_eq_iff_eq] using enc.orthonormal (e i) (e j)
  let r := Fintype.equivFin (ι → ZMod 2)
  let f := Equiv.refl (Fin l)
  change (Matrix.reindexLinearEquiv ℂ ℂ r f V)ᴴ *
    Matrix.reindexLinearEquiv ℂ ℂ r f V = 1
  have hstar : (Matrix.reindexLinearEquiv ℂ ℂ r f V)ᴴ =
      Matrix.reindexLinearEquiv ℂ ℂ f r Vᴴ := Matrix.conjTranspose_reindex r f V
  rw [hstar, Matrix.reindexLinearEquiv_mul, hGram, Matrix.reindexLinearEquiv_one]

/-- The operator of a Pauli label in the finite CSS channel basis. -/
noncomputable def cssIndexed (e : PauliLabel ι) : Operator (Fintype.card (ι → ZMod 2)) :=
  Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (ι → ZMod 2)) (cssError e)

/-- The finite Kraus enumeration of the actual CSS recovery branches. -/
noncomputable def cssKraus (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (i : Fin (Fintype.card ((κX → ZMod 2) × (κZ → ZMod 2)))) :
    Operator (Fintype.card (ι → ZMod 2)) :=
  Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (ι → ZMod 2))
    (cssBranch c prog ((Fintype.equivFin ((κX → ZMod 2) × (κZ → ZMod 2))).symm i))

/-- The CSS recovery branches form a complete Kraus family. -/
theorem cssKraus_comp (c : CssData ι κX κZ) (prog : RecoveryProgram c) :
    KrausComplete (cssKraus c prog) := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (ι → ZMod 2))
  let s := Fintype.equivFin ((κX → ZMod 2) × (κZ → ZMod 2))
  have hstar (M : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) : (T M)ᴴ = T Mᴴ :=
    Matrix.conjTranspose_reindex _ _ M
  unfold KrausComplete
  calc
    _ = ∑ η, T (cssSyndromeProjector c η) := by
      symm
      apply Fintype.sum_equiv s
      intro η
      have hK : cssKraus c prog (s η) = T (cssBranch c prog η) := by
        simp only [cssKraus, s, Equiv.symm_apply_apply]
        rfl
      rw [hK, hstar, ← map_mul, css_effect c prog η]
    _ = 1 := by rw [← map_sum, cssSyndromeProjector_sum, map_one]

/-- The actual CSS Kraus map agrees with the public recovery channel on every operator. -/
theorem cssKraus_map (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (ρ : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) :
    let T := Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (ι → ZMod 2))
    krausMap (cssKraus c prog) (T ρ) = T (recoveryChannel c prog ρ) := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (ι → ZMod 2))
  let s := Fintype.equivFin ((κX → ZMod 2) × (κZ → ZMod 2))
  have hstar (M : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) : (T M)ᴴ = T Mᴴ :=
    Matrix.conjTranspose_reindex _ _ M
  change krausMap (cssKraus c prog) (T ρ) = T (recoveryChannel c prog ρ)
  simp only [krausMap, LinearMap.sum_apply, conjBranch_apply, recoveryChannel, map_sum]
  symm
  apply Fintype.sum_equiv s
  intro η
  have hK : cssKraus c prog (s η) = T (cssBranch c prog η) := by
    simp only [cssKraus, s, Equiv.symm_apply_apply]
    rfl
  rw [hK, hstar, ← map_mul, ← map_mul]
  congr 1
  simp only [cssBranch, cssError, Matrix.conjTranspose_mul,
    (cssSyndromeProjector_isHermitian c η).eq, mul_assoc]

/-- The complex span of the low-weight Pauli errors is correctable whenever the CSS decoder
corrects their labels. -/
theorem cssError_span {l : ℕ} (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (r : ℕ) (hprog : CorrectsUpTo prog r) (V : Matrix (ι → ZMod 2) (Fin l) ℂ)
    (hV : ∀ j, (fun i => V i j) ∈ cssCodespace c) :
    Submodule.span ℂ {A | ∃ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ r ∧ A = cssIndexed e} ≤
      correctable (cssEmbedding V) (cssKraus c prog) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨e, he, rfl⟩
  apply (mem_correctable (cssEmbedding V) (cssKraus c prog) (cssIndexed e)).2
  intro i
  let η := (Fintype.equivFin ((κX → ZMod 2) × (κZ → ZMod 2))).symm i
  obtain ⟨a, ha⟩ := css_scalar c prog e (hprog e he) η
  have hcol : cssBranch c prog η * cssError e * V = a • V := by
    refine Matrix.ext fun x j => ?_
    have h := ha (fun z => V z j) (hV j)
    rw [Matrix.mulVec_mulVec] at h
    exact congrFun h x
  refine ⟨a, ?_⟩
  change (Matrix.reindexLinearEquiv ℂ ℂ _ _ (cssBranch c prog η)) *
    (Matrix.reindexLinearEquiv ℂ ℂ _ _ (cssError e)) * cssEmbedding V = _
  rw [cssEmbedding, Matrix.reindexLinearEquiv_mul,
    Matrix.reindexLinearEquiv_mul, hcol, map_smul]

/-- A CSS decoder corrects complete Kraus noise in its bounded Pauli span on all encoded
operators, jointly with any finite reference system. -/
theorem css_ref {l q ref : ℕ} (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (r : ℕ) (hprog : CorrectsUpTo prog r) (V : Matrix (ι → ZMod 2) (Fin l) ℂ)
    (hV : ∀ j, (fun i => V i j) ∈ cssCodespace c)
    (hIso : (cssEmbedding V)ᴴ * cssEmbedding V = 1)
    (K : Fin q → Operator (Fintype.card (ι → ZMod 2))) (hK : KrausComplete K)
    (hspan : ∀ i, K i ∈ Submodule.span ℂ
      {A | ∃ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ r ∧ A = cssIndexed e})
    (A : Matrix (Fin l × Fin ref) (Fin l × Fin ref) ℂ) :
    tensorLeft (krausMap (cssKraus c prog))
      (tensorLeft (krausMap K) (tensorLeft (conjBranch (cssEmbedding V)) A)) =
        tensorLeft (conjBranch (cssEmbedding V)) A :=
  recovers_ref (cssEmbedding V) hIso (cssKraus c prog) (cssKraus_comp c prog) K hK
    (fun i => cssError_span c prog r hprog V hV (hspan i)) A

end Qatlib.Concepts.ErrorCorrection.Recovery
