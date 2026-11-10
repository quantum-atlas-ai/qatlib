/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WeightEnum07.MainResults.Theorem9
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeightEnum07.MainResults

open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def hammingWeight {n : ℕ} (w : Fin n → F) : ℕ := Nat.card {i : Fin n // w i ≠ 0}

lemma hammingWeight_comp_perm {n : ℕ} (e : Equiv.Perm (Fin n)) (w : Fin n → F) :
    hammingWeight (fun i => w (e i)) = hammingWeight w := by
  unfold hammingWeight
  exact Nat.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

lemma traceWord_mul_pow_eq_comp
    [Finite E] (α : E) (hα : α ≠ 0) (n N : ℕ) (hN : 0 < N)
    (hord : orderOf (Units.mk0 α hα) = n * N) (τ : E) (d : Fin n) :
    traceWord (F := F) α N n (τ * α ^ (d.val * N)) =
      fun i => traceWord (F := F) α N n τ (finCycle d i) := by
  funext i
  simp only [traceWord]

  have hcongr : ((i.val + d.val) % n) * N ≡ (i.val + d.val) * N [MOD n * N] :=
    (Nat.mod_modEq (i.val + d.val) n).mul_right' N
  have hfin : ((finCycle d i : Fin n) : ℕ) * N = ((i.val + d.val) % n) * N := by
    rw [finCycle_apply]
    simp [Fin.add_def]
  have hexp : α ^ (d.val * N + i.val * N) = α ^ (((finCycle d i : Fin n) : ℕ) * N) := by
    have hu : (Units.mk0 α hα) ^ (d.val * N + i.val * N) =
        (Units.mk0 α hα) ^ (((finCycle d i : Fin n) : ℕ) * N) := by
      have hmod : d.val * N + i.val * N ≡ ((finCycle d i : Fin n) : ℕ) * N [MOD n * N] := by
        rw [hfin]
        simpa [Nat.add_comm, Nat.mul_add, Nat.add_mul] using hcongr.symm
      exact (isOfFinOrder_of_finite (Units.mk0 α hα)).pow_eq_pow_iff_modEq.mpr
        (by simpa [hord] using hmod)
    have := congrArg (fun z : Eˣ => (z : E)) hu
    simpa [Units.val_pow_eq_pow_val, Units.val_mk0] using this
  rw [mul_assoc, ← pow_add, hexp]

lemma hammingWeight_traceWord_mul_pow
    [Finite E] (α : E) (hα : α ≠ 0) (n N : ℕ) (hN : 0 < N)
    (hord : orderOf (Units.mk0 α hα) = n * N) (τ : E) (d : Fin n) :
    hammingWeight (traceWord (F := F) α N n (τ * α ^ (d.val * N))) =
      hammingWeight (traceWord (F := F) α N n τ) := by
  rw [traceWord_mul_pow_eq_comp α hα n N hN hord τ d]
  exact hammingWeight_comp_perm (finCycle d) _

lemma mul_pow_inj
    [Finite E] (α : E) (hα : α ≠ 0) (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (hord : orderOf (Units.mk0 α hα) = n * N)
    {τ : E} (hτ : τ ≠ 0) {d d' : Fin n}
    (h : τ * α ^ (d.val * N) = τ * α ^ (d'.val * N)) : d = d' := by
  have hαpow : α ^ (d.val * N) = α ^ (d'.val * N) := mul_left_cancel₀ hτ h
  have hu : (Units.mk0 α hα) ^ (d.val * N) = (Units.mk0 α hα) ^ (d'.val * N) := by
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Units.val_mk0] using hαpow
  have hmod : d.val * N % (n * N) = d'.val * N % (n * N) := by
    have := (isOfFinOrder_of_finite (Units.mk0 α hα)).pow_inj_mod.mp hu
    simpa [hord] using this
  have hd : d.val * N < n * N := Nat.mul_lt_mul_of_pos_right d.isLt hN
  have hd' : d'.val * N < n * N := Nat.mul_lt_mul_of_pos_right d'.isLt hN
  rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] at hmod
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hN hmod)

def weightSpectrum [Fintype E] [DecidableEq E] (α : E) (N n : ℕ) : Finset ℕ :=
  Finset.univ.image (fun τ : {τ : E // τ ≠ 0} =>
    hammingWeight (traceWord (F := F) α N n τ))

theorem proposition1_weight_bound
    [Fintype F] [Fintype E] [DecidableEq E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (α : E) (hα : α ≠ 0) (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (hmul : n * N = Nat.card E - 1)
    (hord : orderOf (Units.mk0 α hα) = n * N)
    (hmin : ∀ j, 0 < j → j < Module.finrank F E → ¬ n ∣ Nat.card F ^ j - 1) :
    (weightSpectrum (F := F) α N n).card ≤ (Nat.card E - 1) / n := by
  classical
  haveI : Finite Eˣ := Finite.of_injective (Units.val) Units.val_injective
  set W : Finset ℕ := weightSpectrum (F := F) α N n with hW

  have hmem : ∀ m ∈ W, ∃ τ : {τ : E // τ ≠ 0}, hammingWeight (traceWord (F := F) α N n τ) = m := by
    intro m hm
    rw [hW, weightSpectrum, Finset.mem_image] at hm
    obtain ⟨τ, -, hτ⟩ := hm
    exact ⟨τ, hτ⟩
  let rep : {m // m ∈ W} → {τ : E // τ ≠ 0} := fun m => Classical.choose (hmem m.1 m.2)
  have rep_spec : ∀ m : {m // m ∈ W},
      hammingWeight (traceWord (F := F) α N n (rep m)) = m.1 :=
    fun m => Classical.choose_spec (hmem m.1 m.2)

  let Φ : {m // m ∈ W} × Fin n → {τ : E // τ ≠ 0} := fun p =>
    ⟨(rep p.1 : E) * α ^ (p.2.val * N),
      mul_ne_zero (rep p.1).2 (pow_ne_zero _ hα)⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨m, d⟩ ⟨m', d'⟩ h
    have hval : (rep m : E) * α ^ (d.val * N) = (rep m' : E) * α ^ (d'.val * N) := by
      simpa [Φ] using congrArg (fun z : {τ : E // τ ≠ 0} => (z : E)) h
    have hm_eq : m.1 = m'.1 := by
      calc m.1 = hammingWeight (traceWord (F := F) α N n (rep m)) := (rep_spec m).symm
        _ = hammingWeight (traceWord (F := F) α N n ((rep m : E) * α ^ (d.val * N))) :=
            (hammingWeight_traceWord_mul_pow α hα n N hN hord (rep m) d).symm
        _ = hammingWeight (traceWord (F := F) α N n ((rep m' : E) * α ^ (d'.val * N))) := by
            rw [hval]
        _ = hammingWeight (traceWord (F := F) α N n (rep m')) :=
            hammingWeight_traceWord_mul_pow α hα n N hN hord (rep m') d'
        _ = m'.1 := rep_spec m'
    have hmm : m = m' := Subtype.ext hm_eq
    subst hmm
    have hdd : d = d' := mul_pow_inj α hα n N hn hN hord (rep m).2 hval
    subst hdd
    rfl

  have hcard_dom : Fintype.card ({m // m ∈ W} × Fin n) = W.card * n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  have hcard_cod : Fintype.card {τ : E // τ ≠ 0} = Nat.card E - 1 := by
    have h := Fintype.card_subtype_compl (fun τ : E => τ ≠ 0)
    have hone : Fintype.card {τ : E // ¬ τ ≠ 0} = 1 := by
      have : Fintype.card {τ : E // τ = 0} = 1 := Fintype.card_subtype_eq 0
      simpa only [not_not] using this
    rw [hone] at h
    rw [Nat.card_eq_fintype_card]
    omega
  have hcard : W.card * n ≤ Nat.card E - 1 := by
    have hle : Fintype.card ({m // m ∈ W} × Fin n) ≤ Fintype.card {τ : E // τ ≠ 0} :=
      Fintype.card_le_of_injective Φ hinj
    rwa [hcard_dom, hcard_cod] at hle
  exact (Nat.le_div_iff_mul_le hn).mpr (by simpa [Nat.mul_comm] using hcard)

end Qatlib.Papers.WeightEnum07.MainResults
