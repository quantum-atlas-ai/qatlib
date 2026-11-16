/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section


/-! # Genuine permutation fibers of mode assignments

Demand: the actual coefficient-to-second-quantization bridge of LinearOptics10.
The finite fiber equivalences are rederived from private mathematical helpers
in locked Qatlib9eb6a0d BosonDistributionNormalizationThec. No private mangled
constant is invoked, and no permanent/coefficient equality is a premise.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Nat
namespace Qatlib.Concepts.BosonFock.BosonOperators.PermFibers

/-- The function counting how many particle positions are assigned to each mode. -/
def counts {m n : ℕ} (f : Fin n → Fin m) : Fin m → ℕ :=
  fun i => ∑ j : Fin n, if f j = i then 1 else 0


/-- Permuting the positions of a mode assignment preserves its occupation counts. -/
theorem countsPerm {m n : ℕ} (f : Fin n → Fin m) (σ : Equiv.Perm (Fin n)) :
    counts (fun j => f (σ j)) = counts f := by
  funext i
  simp only [counts]
  exact Fintype.sum_equiv σ (fun j => if f (σ j) = i then (1 : ℕ) else 0)
    (fun j => if f j = i then (1 : ℕ) else 0) (fun _ => rfl)


/-- Pointwise equivalent predicates give finite subtypes of the same cardinality. -/
theorem subtypeCard {α : Type*} (p q : α → Prop)
    [Fintype { x // p x }] [Fintype { x // q x }] (h : ∀ a, p a ↔ q a) :
    Fintype.card { x // p x } = Fintype.card { x // q x } := by
  classical
  exact Fintype.card_congr
    (Equiv.ofBijective (fun x : { x // p x } => (⟨(x : α), (h _).1 x.2⟩ : { x // q x }))
      ⟨fun x y hxy => Subtype.ext (by simpa using hxy),
        fun y => ⟨⟨(y : α), (h _).2 y.2⟩, Subtype.ext (by simp)⟩⟩)


/-- The cardinality of a predicate filter of the finite universe equals the cardinality of its
subtype. -/
theorem filterCard {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Fintype.card { x // p x } := by
  classical
  rw [subtypeCard p (fun x => x ∈ Finset.univ.filter p) (fun a => by simp),
    Fintype.card_coe]


/-- The fiber of an assignment at a mode has cardinality equal to its occupation count. -/
theorem fiberCard {m n : ℕ} (f : Fin n → Fin m) (i : Fin m) :
    Fintype.card { j : Fin n // f j = i } = counts f i := by
  classical
  rw [← filterCard (fun j => f j = i), Finset.card_filter]
  rfl


/-- An equivalence between finite types identifies the number of equivalences between them with
the number of permutations of the source. -/
theorem equivCard {α β : Type*}
    [Fintype (α ≃ β)] [Fintype (Equiv.Perm α)] (e : α ≃ β) :
    Fintype.card (α ≃ β) = Fintype.card (Equiv.Perm α) := by
  exact Fintype.card_congr
    (⟨fun φ : α ≃ β => φ.trans e.symm, fun ψ : α ≃ α => ψ.trans e,
      fun φ => Equiv.ext fun a => by simp,
      fun ψ => Equiv.ext fun a => by simp⟩ : (α ≃ β) ≃ Equiv.Perm α)


/-- If two assignments have equal occupations, the number of permutations relating them is the
product of their mode-count factorials. -/
theorem permCardEq {m n : ℕ} (f g : Fin n → Fin m) (h : counts f = counts g) :
    Fintype.card { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j } = ∏ i, (counts f i)! := by
  classical
  have hkey : ∀ (π : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}))
      (a : Fin n), Equiv.ofFiberEquiv π a
      = ((π (g a)) (⟨a, rfl⟩ : {j : Fin n // g j = g a}) : Fin n) := by
    intro π a
    simp
    rfl
  have hinj : ∀ π π' : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}),
      Equiv.ofFiberEquiv π = Equiv.ofFiberEquiv π' → π = π' := by
    intro π π' heq
    funext i
    ext x
    have htr : ∀ (πx : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i})),
        ((πx i) x : Fin n)
          = ((πx (g (x : Fin n))) (⟨(x : Fin n), rfl⟩ :
              {j : Fin n // g j = g (x : Fin n)}) : Fin n) := by
      intro πx
      cases x with
      | mk a ha => subst ha; rfl
    rw [htr π, htr π', ← hkey π (x : Fin n), ← hkey π' (x : Fin n)]
    exact congrArg (fun z : Fin n => (z : ℕ)) (Equiv.ext_iff.mp heq (x : Fin n))
  have hsurj : ∀ τ : { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j },
      ∃ π : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}),
        Equiv.ofFiberEquiv π = (τ : Equiv.Perm (Fin n)) := by
    intro τ
    set hblock : ∀ i : Fin m, ({j : Fin n // g j = i} ≃ {j : Fin n // f j = i}) := fun i =>
      Equiv.ofBijective
        (fun x : {j : Fin n // g j = i} =>
          (⟨(τ : Equiv.Perm (Fin n)) (x : Fin n), by
            have h1 := τ.2 (x : Fin n)
            rw [x.2] at h1
            exact h1⟩ : {j : Fin n // f j = i}))
        ⟨fun x y hxy =>
            Subtype.ext ((τ : Equiv.Perm (Fin n)).injective (by simpa using hxy)),
          fun y =>
            ⟨(⟨(τ : Equiv.Perm (Fin n)).symm (y : Fin n), by
                have h2 := τ.2 ((τ : Equiv.Perm (Fin n)).symm (y : Fin n))
                rw [Equiv.apply_symm_apply] at h2
                exact h2.symm.trans y.2⟩ : {j : Fin n // g j = i}),
              Subtype.ext (Equiv.apply_symm_apply _ _)⟩⟩
    refine ⟨hblock, ?_⟩
    refine (Equiv.ext fun a => ?_)
    show (Equiv.ofFiberEquiv hblock) a = ((τ : Equiv.Perm (Fin n)) a : Fin n)
    rw [hkey hblock a]
    rfl
  have hbij : (∀ i : Fin m, {j : Fin n // g j = i} ≃ {j : Fin n // f j = i}) ≃
      { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j } :=
    Equiv.ofBijective
      (fun π => ⟨Equiv.ofFiberEquiv π, fun j => Equiv.ofFiberEquiv_map π j⟩)
      ⟨fun π π' hpp => hinj π π' (congrArg Subtype.val hpp),
        fun τ => let ⟨π, hπ⟩ := hsurj τ; ⟨π, Subtype.ext hπ⟩⟩
  rw [Fintype.card_congr hbij.symm, Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hce : Fintype.card {j : Fin n // g j = i} = Fintype.card {j : Fin n // f j = i} := by
    rw [fiberCard, fiberCard, ← h]
  have e₀ : {j : Fin n // g j = i} ≃ {j : Fin n // f j = i} := Fintype.equivOfCardEq hce
  rw [equivCard e₀, Fintype.card_perm, fiberCard g i, ← h]


/-- The number of permutations relating two mode assignments is the occupation factorial product
when their counts agree, and zero otherwise. -/
theorem permCard {m n : ℕ} (f g : Fin n → Fin m) :
    Fintype.card { τ : Equiv.Perm (Fin n) // ∀ j, f (τ j) = g j }
      = if counts f = counts g then ∏ i, (counts f i)! else 0 := by
  classical
  by_cases h : counts f = counts g
  · rw [ite_eq_left h, permCardEq f g h]
  · rw [ite_eq_right h, Fintype.card_eq_zero_iff]
    refine ⟨fun τ => h ?_⟩
    have h1 := τ.2
    have h2 : (fun j => f ((τ : Equiv.Perm (Fin n)) j)) = g := funext fun j => h1 j
    exact (countsPerm f (τ : Equiv.Perm (Fin n))).symm.trans (by rw [h2])


/-- The sum over permutations of a fixed mode assignment equals its occupation factorial product
times the sum over assignments with matching counts. -/
theorem sumCompose {m n : ℕ} (f₀ : Fin n → Fin m) (Φ : (Fin n → Fin m) → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), Φ (fun j => f₀ (σ j))
      = (∏ i, (counts f₀ i)! : ℕ) * ∑ g : Fin n → Fin m,
          (if counts g = counts f₀ then (1 : ℕ) else 0) * Φ g := by
  classical
  have hphi : ∀ (F : Fin n → Fin m) (σ : Equiv.Perm (Fin n)),
      (fun j => f₀ (σ j)) = F → Φ (fun j => f₀ (σ j)) = Φ F := by
    intro F σ h
    rw [h]
  rw [← Finset.sum_fiberwise_of_maps_to
      (t := (Finset.univ : Finset (Fin n → Fin m)))
      (g := fun σ : Equiv.Perm (Fin n) => fun j => f₀ (σ j))
      (fun σ _ => Finset.mem_univ _)
      (f := fun σ : Equiv.Perm (Fin n) => Φ (fun j => f₀ (σ j)))]
  have hterm : ∀ F : Fin n → Fin m,
      (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), Φ (fun j => f₀ (σ j)))
        = (↑(if counts F = counts f₀ then (1 : ℕ) else 0) * Φ F) *
          ↑(∏ i, (counts f₀ i)! : ℕ) := by
    intro F
    have hone : (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), Φ F)
        = (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), (1 : ℂ)) * Φ F := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => (one_mul _).symm
    have hone2 : (∑ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)), (1 : ℂ))
        = ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          (fun j => f₀ (σ j)) = F)).card : ℂ) := by
      rw [Finset.sum_const, Nat.smul_one_eq_cast]
    rw [Finset.sum_congr rfl
        (fun σ hσ => hphi F σ (by simpa [Finset.mem_filter] using hσ)),
      hone, hone2, filterCard,
      subtypeCard (fun τ : Equiv.Perm (Fin n) => (fun j => f₀ (τ j)) = F)
        (fun τ : Equiv.Perm (Fin n) => ∀ j, f₀ (τ j) = F j)
        (fun τ => funext_iff),
      permCard f₀ F]
    by_cases h : counts f₀ = counts F
    · rw [ite_eq_left h, ite_eq_left h.symm, Nat.cast_one, one_mul]; ring
    · rw [ite_eq_right h, ite_eq_right (fun hc => h hc.symm), Nat.cast_zero, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun F _ => hterm F), ← Finset.sum_mul]
  exact mul_comm _ _


end Qatlib.Concepts.BosonFock.BosonOperators.PermFibers
