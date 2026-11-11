/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# SuperchannelAlgebra — the free-operation algebra of Definitions 2.1 and Lemma 2.4

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1.

This file models Section 2.2 at the level of *equations between supermaps*:

* complete dephasing `Δ_X`, `Δ_C` are idempotent maps (`Δ ∘ Δ = Δ`, Eq. (8));
* `S` is an `n`-input superchannel acting on a tuple of channels;
* `IsMISCGen` is Eq. (11) `Δ_C ∘ P ∘ Δ_X = P ∘ Δ_X`, p. 6;
* `IsDISCGen` is Eq. (12) `Δ_C ∘ P = P ∘ Δ_X`, p. 6.

The predicates are stated for an arbitrary input interface family `I`, so that the
same definition applies to the outer superchannel (inputs the intermediate
`A_k`) and to a componentwise composition `S ∘ (Φ_1, …, Φ_n)` (inputs `X_k`).

Everything here is the operational equation level; the Choi-operator
translation of Proposition 2.2 is not formalised (see
`Foundations/SourceProp22Choi.lean` for the modelling boundary).

The two genuinely algebraic facts used in the rest of the paper are proved in
full: classicality preservation (Lemma 2.3, p. 7) and closure under
componentwise composition (Lemma 2.4, p. 8).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

variable {n : ℕ} {Out : Type*}

/-- Complete dephasing data for an `n`-input channel-transformation setting.

`XChan k` is the type of channels at input slot `k` *before* the simulator,
`AChan k` the type after a single-input simulator, and `Out` the type of output
channels.  Each dephasing is idempotent, matching `Δ_X ∘ Δ_X = Δ_X` for complete
dephasing (`D_X^2 = D_X`, Section 2.2, p. 6). -/
structure FreeData (XChan AChan : Fin n → Type*) (Out : Type*) where
  /-- Input dephasing on the `k`-th channel interface. -/
  dX : ∀ k, XChan k → XChan k
  /-- Dephasing on the `k`-th intermediate interface used by the outer map. -/
  dA : ∀ k, AChan k → AChan k
  /-- Output dephasing. -/
  dC : Out → Out
  dX_idem : ∀ k x, dX k (dX k x) = dX k x
  dA_idem : ∀ k a, dA k (dA k a) = dA k a
  dC_idem : ∀ c, dC (dC c) = dC c

/-- Definition 2.1, Eq. (11), p. 6 (MISC, multi-input form) for an arbitrary
input interface family `I`: `Δ_C ∘ P ∘ Δ_I = P ∘ Δ_I`. -/
abbrev IsMISCGen {n : ℕ} {I : Fin n → Type*} (dI : ∀ k, I k → I k) (dC : Out → Out)
    (P : (∀ k, I k) → Out) : Prop :=
  ∀ (a : ∀ k, I k), dC (P (fun k => dI k (a k))) = P (fun k => dI k (a k))

/-- Definition 2.1, Eq. (12), p. 6 (DISC, multi-input form):
`Δ_C ∘ P = P ∘ Δ_I`. -/
abbrev IsDISCGen {n : ℕ} {I : Fin n → Type*} (dI : ∀ k, I k → I k) (dC : Out → Out)
    (P : (∀ k, I k) → Out) : Prop :=
  ∀ (a : ∀ k, I k), dC (P a) = P (fun k => dI k (a k))

/-- MISC for a superchannel acting on the intermediate `A` interfaces. -/
abbrev IsMISC {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out) (S : (∀ k, AChan k) → Out) : Prop :=
  IsMISCGen F.dA F.dC S

/-- DISC for a superchannel acting on the intermediate `A` interfaces. -/
abbrev IsDISC {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out) (S : (∀ k, AChan k) → Out) : Prop :=
  IsDISCGen F.dA F.dC S

/-- One-input MISC condition for a simulator `Φ_k : X_k → A_k`
(`Δ_{A_k} ∘ Φ_k ∘ Δ_{X_k} = Φ_k ∘ Δ_{X_k}`, the one-input instance of Eq. (11)). -/
def IsMISC1 {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out) (k : Fin n) (Φ : XChan k → AChan k) : Prop :=
  ∀ x, F.dA k (Φ (F.dX k x)) = Φ (F.dX k x)

/-- One-input DISC condition for a simulator `Φ_k : X_k → A_k`. -/
def IsDISC1 {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out) (k : Fin n) (Φ : XChan k → AChan k) : Prop :=
  ∀ x, F.dA k (Φ x) = Φ (F.dX k x)

/-- Componentwise composition `S ∘ (Φ_1, …, Φ_n)`, Eq. (28), p. 8. -/
def comp {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k) :
    (∀ k, XChan k) → Out :=
  fun x => S (fun k => Φ k (x k))

/-- Proposition 2.2, Eq. (21), p. 7: every DISC superchannel is MISC. -/
theorem disc_isMISCGen {n : ℕ} {I : Fin n → Type*} {Out : Type*}
    (dI : ∀ k, I k → I k) (dC : Out → Out) (P : (∀ k, I k) → Out)
    (hidem : ∀ k a, dI k (dI k a) = dI k a)
    (h : IsDISCGen dI dC P) : IsMISCGen dI dC P := by
  intro a
  have h' := h (fun k => dI k (a k))
  have hidem' : (fun k => dI k (dI k (a k))) = (fun k => dI k (a k)) := by
    funext k
    exact hidem k (a k)
  simpa [hidem'] using h'

/-- Proposition 2.2, Eq. (21), p. 7: every DISC superchannel is MISC. -/
theorem disc_isMISC {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out) (S : (∀ k, AChan k) → Out)
    (h : IsDISC F S) : IsMISC F S :=
  disc_isMISCGen F.dA F.dC S F.dA_idem h

/-- Lemma 2.3, p. 7: a multi-input MISC superchannel sends a tuple of classical
channels (fixed by input dephasing) to a classical output (fixed by `Δ_C`). -/
theorem misc_preserves_classical {n : ℕ} {I : Fin n → Type*} {Out : Type*}
    (dI : ∀ k, I k → I k) (dC : Out → Out) (P : (∀ k, I k) → Out)
    (h : IsMISCGen dI dC P)
    (a : ∀ k, I k) (ha : ∀ k, dI k (a k) = a k) :
    dC (P a) = P a := by
  have h' := h a
  have hfun : (fun k => dI k (a k)) = a := by
    funext k
    exact ha k
  rw [hfun] at h'
  exact h'

/-- Lemma 2.4 (MISC half), p. 8: if `S` and every single-input simulator `Φ_k` are
MISC, the componentwise composition `S ∘ (Φ_1,…,Φ_n)` is MISC. -/
theorem comp_misc {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out)
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (hS : IsMISC F S) (hΦ : ∀ k, IsMISC1 F k (Φ k)) :
    IsMISCGen F.dX F.dC (comp S Φ) := by
  intro x
  have hΦ' : (fun k => F.dA k (Φ k (F.dX k (x k)))) = (fun k => Φ k (F.dX k (x k))) := by
    funext k
    exact hΦ k (x k)
  have hS' := hS (fun k => Φ k (F.dX k (x k)))
  simpa [comp, hΦ'] using hS'

/-- Lemma 2.4 (DISC half), p. 8: if `S` and every single-input simulator `Φ_k` are
DISC, the componentwise composition `S ∘ (Φ_1,…,Φ_n)` is DISC. -/
theorem comp_disc {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out)
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (hS : IsDISC F S) (hΦ : ∀ k, IsDISC1 F k (Φ k)) :
    IsDISCGen F.dX F.dC (comp S Φ) := by
  intro x
  have hΦ' : (fun k => F.dA k (Φ k (x k))) = (fun k => Φ k (F.dX k (x k))) := by
    funext k
    exact hΦ k (x k)
  have hS' := hS (fun k => Φ k (x k))
  simpa [comp, hΦ'] using hS'

/-- The composition is *pointwise* the stated higher-order map, Eq. (98), p. 18:
`PS(E_1,…,E_n) = S(Φ_1(E_1),…,Φ_n(E_n))`.  This is definitional. -/
theorem comp_apply {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (x : ∀ k, XChan k) :
    comp S Φ x = S (fun k => Φ k (x k)) := rfl

/-! ## Optimal-error comparison (Eq. (101), p. 18)

The transformation error is an infimum of `½ ‖S(N) − M‖_⋄` over the free
strategies.  Once every general-process output on the fixed resource tuple is
matched by a parallel output with the same value, the three infima coincide.
This is the order-theoretic content of Theorem 5.2's final display.
-/

/-- If every element of `B` is dominated (in error) by an element of `A` and
`A ⊆ B`, then the infimal errors coincide. -/
theorem sInf_image_eq_of_dominated {α β : Type*} [ConditionallyCompleteLinearOrder β]
    {A B : Set α} {f : α → β}
    (hAne : A.Nonempty) (hBdd : BddBelow (f '' B))
    (hsub : A ⊆ B) (hdom : ∀ b ∈ B, ∃ a ∈ A, f a ≤ f b) :
    sInf (f '' A) = sInf (f '' B) := by
  have hbddA : BddBelow (f '' A) := hBdd.mono (Set.image_mono hsub)
  apply le_antisymm
  · -- `sInf (f '' A) ≤ sInf (f '' B)`
    apply le_csInf
    · exact (hAne.image f).mono (Set.image_mono hsub)
    · intro b hb
      obtain ⟨b', hb', rfl⟩ := hb
      obtain ⟨a, haA, hle⟩ := hdom b' hb'
      exact le_trans (csInf_le hbddA ⟨a, haA, rfl⟩) hle
  · -- `sInf (f '' B) ≤ sInf (f '' A)`
    exact csInf_le_csInf hBdd (hAne.image f) (Set.image_mono hsub)

end Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra
