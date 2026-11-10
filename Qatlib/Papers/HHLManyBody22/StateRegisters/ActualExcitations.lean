/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.StateRegisters.QubitCount
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.HHLManyBody22.StateRegisters

abbrev SingleExcitation (h p : ℕ) := Fin h×Fin p

abbrev RawSD (h p : ℕ) := Sum (SingleExcitation h p)
  (SingleExcitation h p×SingleExcitation h p)

theorem rawSD_card (h p : ℕ) : Fintype.card (RawSD h p)=h*p+(h*p)^2 := by
  simp [RawSD,SingleExcitation,Fintype.card_sum,Fintype.card_prod,pow_two]

theorem excitation_manifold_card (h p : ℕ) (S : Finset (RawSD h p)) :
    Fintype.card S≤h*p+(h*p)^2 := by
  rw [Fintype.card_coe]
  exact (Finset.card_le_univ S).trans_eq (rawSD_card h p)

def excitationEncode {h p : ℕ} (S : Finset (RawSD h p)) :
    S→Fin (2^stateRegisterQubits (Fintype.card S)) :=
  fun x => ⟨(Fintype.equivFin S x).val,
    (Fintype.equivFin S x).isLt.trans_le (stateRegisterQubits_le_iff.mp le_rfl)⟩

def excitationDecode {h p : ℕ} (S : Finset (RawSD h p))
    (z : Fin (2^stateRegisterQubits (Fintype.card S))) : Option S :=
  if hz : z.val<Fintype.card S then some ((Fintype.equivFin S).symm ⟨z.val,hz⟩) else none

theorem excitation_decode_encode {h p : ℕ} (S : Finset (RawSD h p)) (x : S) :
    excitationDecode S (excitationEncode S x)=some x := by
  have hx : (Fintype.equivFin S x).val<S.card := by simpa using (Fintype.equivFin S x).isLt
  simp [excitationDecode,excitationEncode,hx]

theorem excitationEncode_injective {h p : ℕ} (S : Finset (RawSD h p)) :
    Function.Injective (excitationEncode S) := by
  intro x y hxy
  have h := congrArg (excitationDecode S) hxy
  simpa only [excitation_decode_encode,Option.some.injEq] using h

theorem excitation_encoding_minimal {h p : ℕ} (S : Finset (RawSD h p))
    (r : ℕ) (f : S→Fin (2^r)) (hf : Function.Injective f) :
    stateRegisterQubits (Fintype.card S)≤r := by
  apply stateRegisterQubits_le_iff.mpr
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem orbital_le_binary_predecessor (h : ℕ) (hh : 0<h) : h≤2^(h-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  simp only [Nat.succ_sub_one]
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 0<2^n := by positivity
    omega

theorem actual_sd_capacity (h p : ℕ) (hh : 0<h) (hp : 0<p) :
    h*p+(h*p)^2≤2^(2*(h+p)-3) := by
  have hh' := orbital_le_binary_predecessor h hh
  have hp' := orbital_le_binary_predecessor p hp
  have he : h-1+(p-1)=h+p-2 := by omega
  have hb : h*p≤2^(h+p-2) := by
    calc
      _ ≤ 2^(h-1)*2^(p-1) := Nat.mul_le_mul hh' hp'
      _ = _ := by rw [← pow_add,he]
  have hm : 0<2^(h+p-2) := by positivity
  have hs : (h*p)^2≤(2^(h+p-2))^2 := Nat.pow_le_pow_left hb 2
  have he' : 2*(h+p)-3=2*(h+p-2)+1 := by omega
  have heq : 2^(2*(h+p-2))=(2^(h+p-2))^2 := by rw [← pow_mul,Nat.mul_comm]
  rw [he',pow_add,pow_one,heq]
  nlinarith

theorem actual_excitation_state_advantage (h p : ℕ) (hh : 0<h) (hp : 0<p)
    (S : Finset (RawSD h p)) :
    stateRegisterQubits (Fintype.card S)<qpeStateQubits (2*(h+p)) := by
  have hdim : Fintype.card S≤2^(2*(h+p)-1) :=
    (excitation_manifold_card h p S).trans ((actual_sd_capacity h p hh hp).trans
      (Nat.pow_le_pow_right (by norm_num : 0<2) (by omega)))
  exact hhlQubits_lt_qpeQubits (by omega) hdim

end Qatlib.Papers.HHLManyBody22.StateRegisters
