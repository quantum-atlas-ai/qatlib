/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly05.MainResults.KauffmanStateSum
import Mathlib.Algebra.FreeAlgebra
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPoly05.MainResults.TemperleyLieb

open FreeAlgebra

abbrev TLGen (n : ℕ) := Fin (n - 1)

variable {n : ℕ} {d : ℂ}

def tlRelSet (n : ℕ) (d : ℂ) : Set (FreeAlgebra ℂ (TLGen n)) :=
  {x |
    (∃ i j : TLGen n, i.val + 2 ≤ j.val ∧
        x = ι ℂ i * ι ℂ j - ι ℂ j * ι ℂ i) ∨
    (∃ i j : TLGen n, j.val = i.val + 1 ∧
        x = ι ℂ i * ι ℂ j * ι ℂ i - ι ℂ i) ∨
    (∃ i j : TLGen n, j.val = i.val + 1 ∧
        x = ι ℂ j * ι ℂ i * ι ℂ j - ι ℂ j) ∨
    (∃ i : TLGen n, x = ι ℂ i * ι ℂ i - algebraMap ℂ (FreeAlgebra ℂ (TLGen n)) d * ι ℂ i)}

abbrev tlCon (n : ℕ) (d : ℂ) : RingCon (FreeAlgebra ℂ (TLGen n)) :=
  ringConGen fun a b => a - b ∈ tlRelSet n d

abbrev TLAlg (n : ℕ) (d : ℂ) : Type := (tlCon n d).Quotient

def TLAlg.gen (n : ℕ) (d : ℂ) (i : TLGen n) : TLAlg n d :=
  (tlCon n d).mk' (ι ℂ i)

theorem tl_rel_commute (n : ℕ) (d : ℂ) {i j : TLGen n} (hij : i.val + 2 ≤ j.val) :
    tlCon n d (ι ℂ i * ι ℂ j) (ι ℂ j * ι ℂ i) :=
  RingConGen.Rel.of _ _ (Or.inl ⟨i, j, hij, rfl⟩)

theorem tl_rel_braid (n : ℕ) (d : ℂ) {i j : TLGen n} (hij : j.val = i.val + 1) :
    tlCon n d (ι ℂ i * ι ℂ j * ι ℂ i) (ι ℂ i) :=
  RingConGen.Rel.of _ _ (Or.inr (Or.inl ⟨i, j, hij, rfl⟩))

theorem tl_rel_braid' (n : ℕ) (d : ℂ) {i j : TLGen n} (hij : j.val = i.val + 1) :
    tlCon n d (ι ℂ j * ι ℂ i * ι ℂ j) (ι ℂ j) :=
  RingConGen.Rel.of _ _ (Or.inr (Or.inr (Or.inl ⟨i, j, hij, rfl⟩)))

theorem tl_rel_quadratic (n : ℕ) (d : ℂ) (i : TLGen n) :
    tlCon n d (ι ℂ i * ι ℂ i) (algebraMap ℂ (FreeAlgebra ℂ (TLGen n)) d * ι ℂ i) :=
  RingConGen.Rel.of _ _ (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))

structure KauffmanGeometry (n : ℕ) (D : Type*) where

  unit : D

  stack : D → D → D

  loops : D → D → ℕ

  capcup : Fin (n - 1) → D

  unit_stack : ∀ u, stack unit u = u ∧ loops unit u = 0

  stack_unit : ∀ u, stack u unit = u ∧ loops u unit = 0

  stack_assoc : ∀ u v w, stack (stack u v) w = stack u (stack v w)

  loops_assoc : ∀ u v w, loops (stack u v) w + loops u v =
    loops u (stack v w) + loops v w

def gTLRelSet {D : Type*} (n : ℕ) (d : ℂ) (geo : KauffmanGeometry n D) :
    Set (FreeAlgebra ℂ D) :=
  {x |
    (∃ u v : D, x = ι ℂ u * ι ℂ v -
      algebraMap ℂ (FreeAlgebra ℂ D) (d ^ geo.loops u v) * ι ℂ (geo.stack u v)) ∨
    x = ι ℂ geo.unit - 1}

abbrev gTLCon {D : Type*} (n : ℕ) (d : ℂ) (geo : KauffmanGeometry n D) :
    RingCon (FreeAlgebra ℂ D) :=
  ringConGen fun a b => a - b ∈ gTLRelSet n d geo

abbrev gTLAlg {D : Type*} (n : ℕ) (d : ℂ) (geo : KauffmanGeometry n D) :=
  (gTLCon n d geo).Quotient

def gTLAlg.gen {D : Type*} (n : ℕ) (d : ℂ) (geo : KauffmanGeometry n D) (u : D) :
    gTLAlg n d geo :=
  (gTLCon n d geo).mk' (ι ℂ u)

def SatisfiesTL {A : Type*} [Ring A] [Algebra ℂ A] (d : ℂ) {n : ℕ}
    (x : TLGen n → A) : Prop :=
  (∀ i j : TLGen n, i.val + 2 ≤ j.val → x i * x j = x j * x i) ∧
  (∀ i j : TLGen n, j.val = i.val + 1 → x i * x j * x i = x i) ∧
  (∀ i j : TLGen n, j.val = i.val + 1 → x j * x i * x j = x j) ∧
  (∀ i : TLGen n, x i * x i = algebraMap ℂ A d * x i)

def freeLift {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (x : TLGen n → A) :
    FreeAlgebra ℂ (TLGen n) →ₐ[ℂ] A :=
  FreeAlgebra.lift ℂ x

theorem freeLift_ι {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (x : TLGen n → A)
    (i : TLGen n) : freeLift x (ι ℂ i) = x i :=
  FreeAlgebra.lift_ι_apply x i

theorem freeLift_mem_zero {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {d : ℂ}
    {x : TLGen n → A} (hx : SatisfiesTL d x) {y : FreeAlgebra ℂ (TLGen n)}
    (hy : y ∈ tlRelSet n d) : freeLift x y = 0 := by
  rcases hy with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩
  · simp only [map_sub, map_mul, freeLift_ι]
    exact sub_eq_zero.mpr (hx.1 i j hij)
  · simp only [map_sub, map_mul, freeLift_ι]
    exact sub_eq_zero.mpr (hx.2.1 i j hij)
  · simp only [map_sub, map_mul, freeLift_ι]
    exact sub_eq_zero.mpr (hx.2.2.1 i j hij)
  · simp only [map_sub, map_mul, freeLift_ι, AlgHom.commutes]
    exact sub_eq_zero.mpr (hx.2.2.2 i)

theorem tlCon_le_ker {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {d : ℂ}
    {x : TLGen n → A} (hx : SatisfiesTL d x) :
    tlCon n d ≤ RingCon.ker (freeLift x).toRingHom := by
  refine RingCon.ringConGen_le.mpr ?_
  intro a b hab
  rw [RingCon.ker_apply]
  have h : freeLift x a - freeLift x b = 0 := by
    have h0 : freeLift x (a - b) = 0 := freeLift_mem_zero hx hab
    rwa [map_sub] at h0
  exact sub_eq_zero.mp h

def tlLift {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {d : ℂ} (x : TLGen n → A)
    (hx : SatisfiesTL d x) : TLAlg n d →+* A :=
  (tlCon n d).lift (freeLift x).toRingHom (tlCon_le_ker hx)

theorem tlLift_gen {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {d : ℂ}
    {x : TLGen n → A} (hx : SatisfiesTL d x) (i : TLGen n) :
    tlLift x hx (TLAlg.gen n d i) = x i := by
  show (tlCon n d).lift (freeLift x).toRingHom (tlCon_le_ker hx)
      ((tlCon n d).mk' (ι ℂ i)) = x i
  rw [RingCon.lift_mk']
  exact freeLift_ι x i

theorem tlLift_unique {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {d : ℂ}
    {x : TLGen n → A} (hx : SatisfiesTL d x) (g : TLAlg n d →+* A)
    (Hg : g.comp (tlCon n d).mk' = (freeLift x).toRingHom) : g = tlLift x hx :=
  (tlCon n d).lift_unique (tlCon_le_ker hx) g Hg

def psi {D : Type*} (geo : KauffmanGeometry n D) {d : ℂ}
    (hc : SatisfiesTL (A := FreeAlgebra ℂ D) d (fun i => ι ℂ (geo.capcup i))) :
    TLAlg n d →+* gTLAlg n d geo :=
  (gTLCon n d geo).mk'.comp (tlLift (fun i => ι ℂ (geo.capcup i)) hc)

theorem psi_gen {D : Type*} (geo : KauffmanGeometry n D) {d : ℂ}
    (hc : SatisfiesTL (A := FreeAlgebra ℂ D) d (fun i => ι ℂ (geo.capcup i)))
    (i : TLGen n) :
    psi geo hc (TLAlg.gen n d i) = gTLAlg.gen n d geo (geo.capcup i) := by
  rw [psi, RingHom.comp_apply, tlLift_gen]
  rfl

theorem psi_range_le {D : Type*} (geo : KauffmanGeometry n D) {d : ℂ}
    (hc : SatisfiesTL (A := FreeAlgebra ℂ D) d (fun i => ι ℂ (geo.capcup i))) :
    Subring.closure (Set.range (fun i : TLGen n => gTLAlg.gen n d geo (geo.capcup i))) ≤
      (psi geo hc).range := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨TLAlg.gen n d i, psi_gen geo hc i⟩

theorem psi_surjective {D : Type*} (geo : KauffmanGeometry n D) {d : ℂ}
    (hc : SatisfiesTL (A := FreeAlgebra ℂ D) d (fun i => ι ℂ (geo.capcup i)))
    (hgen : Subring.closure (Set.range (fun i : TLGen n => gTLAlg.gen n d geo (geo.capcup i)))
      = ⊤) :
    Function.Surjective (psi geo hc) := by
  rw [← RingHom.range_eq_top]
  refine le_antisymm le_top ?_
  rw [← hgen]
  exact psi_range_le geo hc

theorem psi_injective_of_retraction {D : Type*} (geo : KauffmanGeometry n D) {d : ℂ}
    (hc : SatisfiesTL (A := FreeAlgebra ℂ D) d (fun i => ι ℂ (geo.capcup i)))
    (ρ : gTLAlg n d geo →+* TLAlg n d) (hρ : ∀ x, ρ (psi geo hc x) = x) :
    Function.Injective (psi geo hc) :=
  Function.LeftInverse.injective hρ

theorem theorem21_capcup_isomorphism {D : Type*} (geo : KauffmanGeometry n D) {d : ℂ}
    (hc : SatisfiesTL (A := FreeAlgebra ℂ D) d (fun i => ι ℂ (geo.capcup i)))
    (hbij : Function.Bijective (psi geo hc)) :
    ∃ e : TLAlg n d ≃+* gTLAlg n d geo,
      ∀ i : TLGen n, e (TLAlg.gen n d i) = gTLAlg.gen n d geo (geo.capcup i) :=
  ⟨RingEquiv.ofBijective (psi geo hc) hbij, fun i => by
    rw [RingEquiv.ofBijective_apply]
    exact psi_gen geo hc i⟩

theorem theorem21_apply_gen {D : Type*} (geo : KauffmanGeometry n D) {d : ℂ}
    (hc : SatisfiesTL (A := FreeAlgebra ℂ D) d (fun i => ι ℂ (geo.capcup i)))
    (hbij : Function.Bijective (psi geo hc)) (i : TLGen n) :
    (theorem21_capcup_isomorphism geo hc hbij).choose (TLAlg.gen n d i) =
      gTLAlg.gen n d geo (geo.capcup i) :=
  (theorem21_capcup_isomorphism geo hc hbij).choose_spec i

theorem tlAlg_gen_satisfies (n : ℕ) (d : ℂ) :
    SatisfiesTL (A := TLAlg n d) d (TLAlg.gen n d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h := (RingCon.eq (c := tlCon n d)).mpr (tl_rel_commute n d hij)
    simpa only [TLAlg.gen, map_mul] using! h
  · intro i j hij
    have h := (RingCon.eq (c := tlCon n d)).mpr (tl_rel_braid n d hij)
    simpa only [TLAlg.gen, map_mul] using! h
  · intro i j hij
    have h := (RingCon.eq (c := tlCon n d)).mpr (tl_rel_braid' n d hij)
    simpa only [TLAlg.gen, map_mul] using! h
  · intro i
    have h := (RingCon.eq (c := tlCon n d)).mpr (tl_rel_quadratic n d i)
    simp only [TLAlg.gen, RingCon.coe_mk'] at h ⊢
    rw [← RingCon.coe_mul, h, RingCon.coe_mul]
    simp

end Qatlib.Papers.JonesPoly05.MainResults.TemperleyLieb
