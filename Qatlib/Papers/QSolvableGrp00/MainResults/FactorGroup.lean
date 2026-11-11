/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform

/-!
# Abelian factor groups and Fourier annihilators

This module formalizes the character and group structure statements underlying the abelian
factor group computation in Section 4.2 of [Watrous2001]. The equivalence
`fourierAnnihilatorEquiv` identifies the kernel annihilator with the character group of the
image; the module also proves the uniform Fourier outcome law on that annihilator and supplies
finite generating sets and prime power cyclic decompositions.

## Main statements

* `fourierAnnihilatorEquiv`: Identifies the kernel annihilator with the character group of the
  image.
* `fig2OutcomeProb_eq_of_mem`: Computes the uniform Fourier probability on the annihilator.
* `finite_abelian_primePower_decomposition`: Decomposes a finite abelian group into prime power
  cyclic factors.

## References

* [Watrous, 2001][Watrous2001]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Papers.QSolvableGrp00.MainResults.FactorGroup

section Annihilator

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
  (f : A →+ B)

/-- A character in the kernel annihilator has equal values at two elements whose difference lies
in the kernel. -/
theorem annihilator_apply_eq_of_sub_mem_ker (χ : AddChar A ℂ)
    (hχ : χ ∈ characterAnnihilator f.ker) {a b : A} (h : a - b ∈ f.ker) :
    χ a = χ b := by
  have h1 : χ (a - b) = 1 := (mem_characterAnnihilator f.ker χ).mp hχ ⟨a - b, h⟩
  rw [AddChar.map_sub_eq_div] at h1
  have hb : χ b ≠ 0 := by
    intro hzero
    have h2 : χ b * χ (-b) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hzero, zero_mul] at h2
    exact zero_ne_one h2
  exact (div_eq_one_iff_eq hb).mp h1

/-- A character in the kernel annihilator is constant on fibers of f. -/
theorem annihilator_apply_eq_of_apply_eq (χ : AddChar A ℂ)
    (hχ : χ ∈ characterAnnihilator f.ker) {a b : A} (hab : f a = f b) :
    χ a = χ b := by
  apply annihilator_apply_eq_of_sub_mem_ker f χ hχ
  rw [AddMonoidHom.mem_ker, map_sub, hab, sub_self]

/-- The additive homomorphism f with codomain restricted to its range. -/
def qRange : A →+ f.range where
  toFun a := ⟨f a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f a b)

/-- The additive homomorphism taking a character of the range of f to its pullback along
`qRange`. -/
def precompHom : AddChar f.range ℂ →+ AddChar A ℂ where
  toFun ψ := ψ.compAddMonoidHom (qRange f)
  map_zero' := by ext a; simp
  map_add' ψ φ := by ext a; simp

/-- Pulls back range characters to characters in the annihilator of the kernel. -/
def rangeCharToAnnihilator : AddChar f.range ℂ →+ ↥(characterAnnihilator f.ker) where
  toFun ψ := ⟨precompHom f ψ, by
    rw [mem_characterAnnihilator]
    intro h
    change ψ (qRange f h.1) = 1
    have hz : qRange f h.1 = 0 := by
      apply Subtype.ext
      exact (AddMonoidHom.mem_ker).mpr h.2
    rw [hz, AddChar.map_zero_eq_one]⟩
  map_zero' := Subtype.ext (map_zero (precompHom f))
  map_add' ψ φ := Subtype.ext (map_add (precompHom f) ψ φ)

/-- Evaluating a pulled back range character at a gives the original character evaluated at
`qRange` f a. -/
@[simp] theorem rangeCharToAnnihilator_apply (ψ : AddChar f.range ℂ) (a : A) :
    (rangeCharToAnnihilator f ψ).1 a = ψ (qRange f a) := rfl

/-- Pullback from range characters to the kernel annihilator is injective. -/
theorem rangeCharToAnnihilator_injective :
    Function.Injective (rangeCharToAnnihilator f) := by
  intro ψ φ h
  refine AddChar.ext _ _ fun y => ?_
  rcases AddMonoidHom.mem_range.mp y.2 with ⟨a, ha⟩
  have h1 : (rangeCharToAnnihilator f ψ).1 a = (rangeCharToAnnihilator f φ).1 a :=
    congrArg (fun χ : ↥(characterAnnihilator f.ker) => (χ.1 : AddChar A ℂ) a) h
  rw [rangeCharToAnnihilator_apply, rangeCharToAnnihilator_apply] at h1
  have hq : qRange f a = y := Subtype.ext ha
  rw [hq] at h1
  exact h1

/-- The cardinalities of the kernel annihilator and the kernel multiply to the cardinality of A. -/
theorem annihilator_card_mul_ker_card :
    Nat.card ↥(characterAnnihilator f.ker) * Nat.card ↥f.ker = Nat.card A := by
  have h := card_characterAnnihilator (H := f.ker)
  simp only [Fintype.card_eq_nat_card] at h
  exact h

/-- The kernel annihilator and the range of f have equal natural cardinalities. See
[Watrous2001]. -/
theorem natCard_annihilator_eq_card_range :
    Nat.card ↥(characterAnnihilator f.ker) = Nat.card ↥f.range := by
  have hrange : Nat.card ↥f.range * Nat.card ↥f.ker = Nat.card A := by
    have h1 := AddSubgroup.card_mul_index f.ker
    rw [AddSubgroup.index_ker f] at h1
    rw [Nat.mul_comm (Nat.card ↥f.range) (Nat.card ↥f.ker)]
    exact h1
  haveI : Nonempty A := ⟨0⟩
  haveI : Nonempty ↥f.ker := ⟨⟨0, (AddMonoidHom.mem_ker).mpr (map_zero f)⟩⟩
  have hkpos : 0 < Nat.card ↥f.ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hkpos
    (by rw [annihilator_card_mul_ker_card f, hrange])

/-- The kernel annihilator and the range of f have equal `Fintype` cardinalities. -/
theorem card_annihilator_eq_card_range :
    Fintype.card ↥(characterAnnihilator f.ker) = Fintype.card ↥f.range := by
  simp only [Fintype.card_eq_nat_card]
  exact natCard_annihilator_eq_card_range f

/-- Every character in the kernel annihilator is the pullback of a character of the range. -/
theorem rangeCharToAnnihilator_surjective :
    Function.Surjective (rangeCharToAnnihilator f) := by
  by_contra hsurj
  have hlt := Fintype.card_lt_of_injective_not_surjective (rangeCharToAnnihilator f)
    (rangeCharToAnnihilator_injective f) hsurj
  have hAcard : Fintype.card (AddChar f.range ℂ) = Fintype.card ↥f.range := AddChar.card_eq
  have hanncard : Fintype.card ↥(characterAnnihilator f.ker) = Fintype.card ↥f.range :=
    card_annihilator_eq_card_range f
  rw [hAcard, hanncard] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The additive equivalence from the kernel annihilator to the character group of the range,
inverse to character pullback. See [Watrous2001]. -/
noncomputable def fourierAnnihilatorEquiv :
    ↥(characterAnnihilator f.ker) ≃+ AddChar f.range ℂ :=
  (AddEquiv.ofBijective (rangeCharToAnnihilator f)
    ⟨rangeCharToAnnihilator_injective f, rangeCharToAnnihilator_surjective f⟩).symm

end Annihilator

section FactorMap

variable {G : Type*} [Group G]

/-- The ordered product of the generators raised to the natural representatives of the supplied
modular exponents. -/
def factorExponentProduct {k N : ℕ} (gens : Fin k → G) (a : Fin k → ZMod N) : G :=
  (List.ofFn (fun j : Fin k => gens j ^ (a j).val)).prod

/-- For a homomorphism agreeing with the generator exponent product in G/H, kernel membership is
equivalent to the exponent product lying in H. -/
theorem factorMap_ker_iff {k N : ℕ} [NeZero N] {H : Subgroup G} [H.Normal]
    (gens : Fin k → G) (f : (Fin k → ZMod N) →+ Additive (G ⧸ H))
    (hf : ∀ a, (f a).toMul
      = (QuotientGroup.mk (factorExponentProduct gens a) : G ⧸ H)) :
    ∀ a : Fin k → ZMod N, a ∈ f.ker ↔ factorExponentProduct gens a ∈ H := by
  intro a
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (f a).toMul = (1 : G ⧸ H) := by rw [h]; rfl
    rw [hf a] at h1
    exact (QuotientGroup.eq_one_iff (factorExponentProduct gens a)).mp h1
  · intro h
    have h1 : (QuotientGroup.mk (factorExponentProduct gens a) : G ⧸ H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h
    have h2 : (f a).toMul = (1 : G ⧸ H) := by rw [hf a]; exact h1
    have h3 : (0 : Additive (G ⧸ H)).toMul = 1 := rfl
    exact Additive.toMul.injective (by rw [h3]; exact h2)

end FactorMap

section Figure2

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
  (f : A →+ B)

/-- The Born probability of a character after the abelian Fourier transform of the kernel coset
state at zero. -/
noncomputable def fig2OutcomeProb (χ : AddChar A ℂ) : ℝ :=
  BornProb (abelianQFT (abelianCosetState f.ker 0)) χ

/-- A character in the kernel annihilator has Fourier outcome probability equal to the
reciprocal of the annihilator cardinality. See [Watrous2001]. -/
theorem fig2OutcomeProb_eq_of_mem (χ : AddChar A ℂ)
    (hχ : χ ∈ characterAnnihilator f.ker) :
    fig2OutcomeProb f χ =
      ((Nat.card ↥(characterAnnihilator f.ker) : ℝ))⁻¹ := by
  classical
  haveI : Nonempty A := ⟨0⟩
  haveI : Nonempty ↥f.ker :=
    ⟨⟨0, (AddMonoidHom.mem_ker).mpr (map_zero f)⟩⟩
  haveI : Nonempty ↥(characterAnnihilator f.ker) :=
    ⟨⟨0, by rw [mem_characterAnnihilator]; intro h; simp⟩⟩
  rw [fig2OutcomeProb, bornProb_abelianQFT_cosetState, if_pos hχ]
  simp only [Fintype.card_eq_nat_card]
  have hcards : (Nat.card ↥(characterAnnihilator f.ker) : ℝ) * (Nat.card ↥f.ker : ℝ)
      = (Nat.card A : ℝ) := by
    exact_mod_cast annihilator_card_mul_ker_card f
  have hannpos : 0 < Nat.card ↥(characterAnnihilator f.ker) := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hannR : (Nat.card ↥(characterAnnihilator f.ker) : ℝ) ≠ 0 := by
    exact_mod_cast hannpos.ne'
  have hAR : (Nat.card A : ℝ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hk : (Nat.card ↥f.ker : ℝ)
      = (Nat.card A : ℝ) / (Nat.card ↥(characterAnnihilator f.ker) : ℝ) := by
    rw [eq_div_iff hannR]
    rw [mul_comm]
    exact hcards
  rw [hk, div_eq_mul_inv, div_eq_mul_inv]
  rw [mul_assoc]
  rw [mul_comm ((Nat.card ↥(characterAnnihilator f.ker) : ℝ)⁻¹) ((Nat.card A : ℝ)⁻¹)]
  rw [← mul_assoc, mul_inv_cancel₀ hAR, one_mul]

/-- A character outside the kernel annihilator has Fourier outcome probability zero. See
[Watrous2001]. -/
theorem fig2OutcomeProb_eq_of_not_mem (χ : AddChar A ℂ)
    (hχ : χ ∉ characterAnnihilator f.ker) :
    fig2OutcomeProb f χ = 0 := by
  rw [fig2OutcomeProb, bornProb_abelianQFT_cosetState, if_neg hχ]

end Figure2

section Sampling

/-- The additive homomorphism reducing each integer coordinate modulo N. -/
def castPiHom (k N : ℕ) : (Fin k → ℤ) →+ (Fin k → ZMod N) where
  toFun v i := (v i : ZMod N)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

/-- For nonzero N, every additive subgroup of k copies of `ZMod N` has a generating finite set
of cardinality at most k. See [Watrous2001]. -/
theorem addSubgroup_fin_generated_by_k {k N : ℕ} [NeZero N]
    (S : AddSubgroup (Fin k → ZMod N)) :
    ∃ T : Finset (Fin k → ZMod N), T.card ≤ k ∧
      AddSubgroup.closure (T : Set (Fin k → ZMod N)) = S := by
  classical
  let π := castPiHom k N
  have hπ : Function.Surjective π := by
    intro v
    refine ⟨fun i => (v i).val, ?_⟩
    funext i
    show (((v i).val : ℤ) : ZMod N) = v i
    simpa using ZMod.natCast_zmod_val (v i)
  let S' := S.comap π
  have hS' : S'.map π = S := AddSubgroup.map_comap_eq_self_of_surjective hπ S
  let Nsub : Submodule ℤ (Fin k → ℤ) := AddSubgroup.toIntSubmodule S'
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin k)) Nsub
  have hNsub_add : Nsub.toAddSubgroup = S' := by
    have h1 : AddSubgroup.toIntSubmodule.symm Nsub = S' := by
      show AddSubgroup.toIntSubmodule.symm (AddSubgroup.toIntSubmodule S') = S'
      exact OrderIso.symm_apply_apply _ _
    rw [← AddSubgroup.toIntSubmodule_symm]
    exact h1
  have hfin : n ≤ k := by
    have h1 : Module.finrank ℤ ↥Nsub = n := by
      rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
    have h2 : Module.finrank ℤ ↥Nsub ≤ Module.finrank ℤ (Fin k → ℤ) := Submodule.finrank_le Nsub
    rw [Module.finrank_pi, Fintype.card_fin] at h2
    omega
  let gens : Finset (Fin k → ℤ) :=
    Finset.univ.image (fun i : Fin n => ((bN i : ↥Nsub) : Fin k → ℤ))
  have hgens_card : gens.card ≤ k := by
    have h1 : gens.card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => ((bN i : ↥Nsub) : Fin k → ℤ))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hgens_span : AddSubgroup.closure (gens : Set (Fin k → ℤ)) = S' := by
    rw [le_antisymm_iff]
    constructor
    · rw [AddSubgroup.closure_le]
      intro x hx
      simp only [gens, Finset.coe_image, Finset.coe_univ, Set.mem_image, Set.mem_univ,
        true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      have h2 : ((bN i : ↥Nsub) : Fin k → ℤ) ∈ Nsub.toAddSubgroup := (bN i).2
      simpa [hNsub_add] using h2
    · intro x hx
      have hxN : x ∈ Nsub := by simpa [hNsub_add] using! hx
      have hspan : (⟨x, hxN⟩ : ↥Nsub) ∈ Submodule.span ℤ (Set.range bN) := by
        rw [bN.span_eq]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hspan
      obtain ⟨c, hc⟩ := hspan
      have hx_eq : (∑ i, c i • ((bN i : ↥Nsub) : Fin k → ℤ)) = x := by
        have := congrArg (Subtype.val) hc
        simpa using this
      have hmem : ∀ i : Fin n, ((bN i : ↥Nsub) : Fin k → ℤ) ∈
          AddSubgroup.closure (gens : Set (Fin k → ℤ)) := fun i =>
        AddSubgroup.subset_closure (by simp [gens])
      have hsum : (∑ i, c i • ((bN i : ↥Nsub) : Fin k → ℤ)) ∈
          AddSubgroup.closure (gens : Set (Fin k → ℤ)) :=
        AddSubgroup.sum_mem _ (t := Finset.univ)
          (fun i _ => AddSubgroup.zsmul_mem _ (hmem i) (c i))
      rwa [hx_eq] at hsum
  have hmap : AddSubgroup.map π (AddSubgroup.closure (gens : Set (Fin k → ℤ)))
      = AddSubgroup.closure
          (((gens.image π : Finset (Fin k → ZMod N)) : Set (Fin k → ZMod N))) := by
    rw [le_antisymm_iff]
    constructor
    · rw [AddSubgroup.map_le_iff_le_comap, AddSubgroup.closure_le]
      intro g hg
      change π g ∈ AddSubgroup.closure
        ((gens.image π : Finset (Fin k → ZMod N)) : Set (Fin k → ZMod N))
      exact AddSubgroup.subset_closure (by
        rw [Finset.coe_image]
        exact Set.mem_image_of_mem π hg)
    · rw [AddSubgroup.closure_le]
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      exact AddSubgroup.mem_map_of_mem π (AddSubgroup.subset_closure hg)
  refine ⟨gens.image π, ?_, ?_⟩
  · have h1 : (gens.image π).card ≤ gens.card := Finset.card_image_le
    omega
  · rw [← hmap, hgens_span]
    exact hS'

/-- The subgroup of modular vectors whose coordinate pairing vanishes on every element of the
kernel of f. -/
def perpSubgroup {k N : ℕ} {B : Type*} [AddCommGroup B]
    (f : (Fin k → ZMod N) →+ B) : AddSubgroup (Fin k → ZMod N) where
  carrier := {b | ∀ a ∈ f.ker, ∑ j : Fin k, a j * b j = 0}
  zero_mem' := by
    intro a _
    simp
  add_mem' := by
    intro b c hb hc a ha
    have hsum : (∑ j : Fin k, a j * (b j + c j))
        = (∑ j : Fin k, a j * b j) + (∑ j : Fin k, a j * c j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_add])
    simp only [Pi.add_apply]
    rw [hsum, hb a ha, hc a ha, add_zero]
  neg_mem' := by
    intro b hb a ha
    have hsum : (∑ j : Fin k, a j * (-b j)) = -(∑ j : Fin k, a j * b j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_neg])
    simp only [Pi.neg_apply]
    rw [hsum, hb a ha, neg_zero]

/-- For nonzero N, the kernel orthogonal subgroup has a generating finite set of cardinality at
most k. See [Watrous2001]. -/
theorem perpSubgroup_generated_by_k {k N : ℕ} [NeZero N] {B : Type*} [AddCommGroup B]
    (f : (Fin k → ZMod N) →+ B) :
    ∃ T : Finset (Fin k → ZMod N), T.card ≤ k ∧
      AddSubgroup.closure (T : Set (Fin k → ZMod N)) = perpSubgroup f :=
  addSubgroup_fin_generated_by_k (perpSubgroup f)

end Sampling

section Decomposition

/-- The additive equivalence on dependent function groups induced by reindexing along an
equivalence. -/
def piAddEquivOfEquiv {ι ι' : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)]
    (e : ι' ≃ ι) : (∀ i : ι, P i) ≃+ (∀ j : ι', P (e j)) where
  toFun := Equiv.piCongrLeft' P e.symm
  invFun := (Equiv.piCongrLeft' P e.symm).symm
  left_inv := (Equiv.piCongrLeft' P e.symm).left_inv
  right_inv := (Equiv.piCongrLeft' P e.symm).right_inv
  map_add' _ _ := by funext j; rfl

/-- The additive equivalence between iterated dependent functions and functions indexed by the
corresponding sigma type. -/
def piSigmaAddEquiv {ι : Type*} {α : ι → Type*} {β : ∀ i, α i → Type*}
    [∀ i j, AddCommGroup (β i j)] :
    ((i : ι) → (j : α i) → β i j) ≃+ ((x : Sigma α) → β x.1 x.2) where
  toFun f x := f x.1 x.2
  invFun f i j := f ⟨i, j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Every finite abelian group is additively equivalent to a finite product of cyclic groups of
positive prime power orders. See [Watrous2001]. -/
theorem finite_abelian_primePower_decomposition (M : Type*) [AddCommGroup M] [Fintype M] :
    ∃ (m : ℕ) (q : Fin m → ℕ),
      (∀ j, ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ q j = p ^ e) ∧
        Nonempty (M ≃+ (∀ j : Fin m, ZMod (q j))) := by
  classical

  obtain ⟨ι, hι, n, hn1, ⟨φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' M
  have hn0 : ∀ i, n i ≠ 0 := fun i => by have := hn1 i; omega

  let I := Sigma fun i : ι => (n i).primeFactors
  let q' : I → ℕ := fun x => x.2.1 ^ (n x.1).factorization x.2.1

  have hcyc : Nonempty (M ≃+ (∀ i : ι, ZMod (n i))) :=
    ⟨φ.trans (DirectSum.addEquivProd (fun i => ZMod (n i)))⟩
  obtain ⟨ψ₁⟩ := hcyc
  have hsplit : (∀ i : ι, ZMod (n i)) ≃+
      (∀ i : ι, ∀ p : (n i).primeFactors,
        ZMod (p.1 ^ (n i).factorization p.1)) :=
    AddEquiv.piCongrRight fun i => (ZMod.equivPi (n := n i) (hn0 i)).toAddEquiv
  let ψ₂ : ((i : ι) → (p : (n i).primeFactors) →
        ZMod (p.1 ^ (n i).factorization p.1)) ≃+ ((x : I) → ZMod (q' x)) :=
    piSigmaAddEquiv
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let ψ₃ : ((x : I) → ZMod (q' x)) ≃+
      ((j : Fin (Fintype.card I)) → ZMod (q' (eI.symm j))) :=
    piAddEquivOfEquiv (fun x : I => ZMod (q' x)) eI.symm
  refine ⟨Fintype.card I, fun j => q' (eI.symm j), ?_, ⟨ψ₁.trans (hsplit.trans (ψ₂.trans ψ₃))⟩⟩

  rintro j
  rcases hx : eI.symm j with ⟨i, p, hp_mem⟩
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hepos : 0 < (n i).factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
  refine ⟨p, (n i).factorization p, hp, hepos, ?_⟩
  show q' (eI.symm j) = p ^ (n i).factorization p
  rw [hx]

/-- Chooses a finite family of positive prime power cyclic orders and an additive equivalence
realizing a finite abelian group as their product. -/
theorem abelian_structure_exists (M : Type*) [AddCommGroup M] [Fintype M] :
    ∃ (m : ℕ) (q : Fin m → ℕ) (θ : M ≃+ (∀ j : Fin m, ZMod (q j))),
      ∀ j, ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ q j = p ^ e := by
  obtain ⟨m, q, hq, ⟨θ⟩⟩ := finite_abelian_primePower_decomposition M
  exact ⟨m, q, θ, hq⟩

end Decomposition

end Qatlib.Papers.QSolvableGrp00.MainResults.FactorGroup
