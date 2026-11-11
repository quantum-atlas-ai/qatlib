/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma24Closure — Lemma 2.4 (closure under componentwise composition)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Lemma 2.4, p. 8
(txt lines 365-385).

**Statement.**  Let `S : A_1 ⋯ A_n → C` be an `n`-input higher-order map and let
`Φ_k : X_k → A_k` be single-input superchannels.  For the componentwise
composition `P := S ∘ (Φ_1, …, Φ_n)` (Eq. (28)):

* if `S` and every `Φ_k` are MISC, then `P` is MISC;
* if `S` and every `Φ_k` are DISC, then `P` is DISC.

**Paper proof.**  MISC half: `Φ_k ∘ Δ_{X_k} = Δ_{A_k} ∘ Φ_k ∘ Δ_{X_k}`
(Eq. (29)); substituting into `P ∘ Δ_X` and using the MISC condition of `S` at
the tuple `(Φ_k ∘ Δ_{X_k})` gives `P ∘ Δ_X = Δ_C ∘ P ∘ Δ_X` (Eq. (30)).
DISC half: `Δ_{A_k} ∘ Φ_k = Φ_k ∘ Δ_{X_k}` (Eq. (31)) and the DISC condition of
`S` give `Δ_C ∘ P = P ∘ Δ_X` (Eq. (32)).

Both directions are proved in full below from the operational equations of
Definition 2.1; no Choi calculus is required.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

/-- Fixed arXiv:2609.08639v1, Lemma 2.4 (MISC half), p. 8: the componentwise
composition `S ∘ (Φ_1,…,Φ_n)` of MISC maps is MISC. -/
theorem source_lemma_24_closure_misc
    {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out)
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (hS : IsMISC F S) (hΦ : ∀ k, IsMISC1 F k (Φ k)) :
    IsMISCGen F.dX F.dC (comp S Φ) :=
  comp_misc F S Φ hS hΦ

/-- Fixed arXiv:2609.08639v1, Lemma 2.4 (DISC half), p. 8: the componentwise
composition `S ∘ (Φ_1,…,Φ_n)` of DISC maps is DISC. -/
theorem source_lemma_24_closure_disc
    {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out)
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (hS : IsDISC F S) (hΦ : ∀ k, IsDISC1 F k (Φ k)) :
    IsDISCGen F.dX F.dC (comp S Φ) :=
  comp_disc F S Φ hS hΦ

/-- Fixed arXiv:2609.08639v1, Lemma 2.4, p. 8: both free classes are closed
under componentwise composition. -/
theorem source_lemma_24_closure
    {n : ℕ} {XChan AChan : Fin n → Type*} {Out : Type*}
    (F : FreeData XChan AChan Out)
    (S : (∀ k, AChan k) → Out) (Φ : ∀ k, XChan k → AChan k)
    (hS_misc : IsMISC F S) (hΦ_misc : ∀ k, IsMISC1 F k (Φ k))
    (hS_disc : IsDISC F S) (hΦ_disc : ∀ k, IsDISC1 F k (Φ k)) :
    IsMISCGen F.dX F.dC (comp S Φ) ∧ IsDISCGen F.dX F.dC (comp S Φ) :=
  ⟨source_lemma_24_closure_misc F S Φ hS_misc hΦ_misc,
   source_lemma_24_closure_disc F S Φ hS_disc hΦ_disc⟩

end Qatlib.Papers.CausalHier26.MiscHierarchy.Foundations
