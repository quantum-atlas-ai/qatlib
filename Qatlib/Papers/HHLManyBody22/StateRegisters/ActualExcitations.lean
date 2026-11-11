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

/-!
# Finite encodings of excitation manifolds

`SingleExcitation` and `RawSD` model occupied-to-virtual substitutions and ordered single/double
excitation indices. Their cardinalities bound any selected finite excitation manifold, which
`excitationEncode` embeds into a binary register with a partial inverse `excitationDecode`.

The encoding is injective and uses the least possible register size. For positive occupied and
virtual orbital counts, `actual_excitation_state_advantage` proves a strict state-register
saving relative to one qubit per spin orbital, formalizing the comparison in [BaskaranEtAl2023].

## Main statements

* `rawSD_card`: counts the raw single and ordered double indices.
* `excitation_encoding_minimal`: bounds below the size of every injective binary encoding.
* `actual_excitation_state_advantage`: compares the selected excitation register with the
  spin-orbital register.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.HHLManyBody22.StateRegisters

/-- An occupied-to-virtual substitution, represented by a pair in `Fin h × Fin p`. -/
abbrev SingleExcitation (h p : ℕ) := Fin h×Fin p

/-- The disjoint union of single substitutions and ordered pairs of substitutions, without
imposing excitation symmetry constraints. -/
abbrev RawSD (h p : ℕ) := Sum (SingleExcitation h p)
  (SingleExcitation h p×SingleExcitation h p)

/-- The raw single and ordered double excitation indices have cardinality `h * p + (h * p) ^ 2`,
as in the spatial index count of [BaskaranEtAl2023]. -/
theorem rawSD_card (h p : ℕ) : Fintype.card (RawSD h p)=h*p+(h*p)^2 := by
  simp [RawSD,SingleExcitation,Fintype.card_sum,Fintype.card_prod,pow_two]

/-- Every finite subset of the raw single/double excitation indices has cardinality at most `h *
p + (h * p) ^ 2`. -/
theorem excitation_manifold_card (h p : ℕ) (S : Finset (RawSD h p)) :
    Fintype.card S≤h*p+(h*p)^2 := by
  rw [Fintype.card_coe]
  exact (Finset.card_le_univ S).trans_eq (rawSD_card h p)

/-- Encodes a selected excitation into a binary register of size `stateRegisterQubits
(Fintype.card S)` using a finite enumeration of `S`. -/
def excitationEncode {h p : ℕ} (S : Finset (RawSD h p)) :
    S→Fin (2^stateRegisterQubits (Fintype.card S)) :=
  fun x => ⟨(Fintype.equivFin S x).val,
    (Fintype.equivFin S x).isLt.trans_le (stateRegisterQubits_le_iff.mp le_rfl)⟩

/-- Decodes a register index to the corresponding selected excitation, returning `none` for
indices beyond the enumeration of `S`. -/
def excitationDecode {h p : ℕ} (S : Finset (RawSD h p))
    (z : Fin (2^stateRegisterQubits (Fintype.card S))) : Option S :=
  if hz : z.val<Fintype.card S then some ((Fintype.equivFin S).symm ⟨z.val,hz⟩) else none

/-- Decoding the encoding of a selected excitation returns that excitation, giving an exact
finite register representation for the excitation manifold in [BaskaranEtAl2023]. -/
theorem excitation_decode_encode {h p : ℕ} (S : Finset (RawSD h p)) (x : S) :
    excitationDecode S (excitationEncode S x)=some x := by
  have hx : (Fintype.equivFin S x).val<S.card := by simpa using (Fintype.equivFin S x).isLt
  simp [excitationDecode,excitationEncode,hx]

/-- Distinct selected excitations have distinct register encodings. -/
theorem excitationEncode_injective {h p : ℕ} (S : Finset (RawSD h p)) :
    Function.Injective (excitationEncode S) := by
  intro x y hxy
  have h := congrArg (excitationDecode S) hxy
  simpa only [excitation_decode_encode,Option.some.injEq] using h

/-- Every injective encoding of `S` into an `r`-qubit register requires at least
`stateRegisterQubits (Fintype.card S)` qubits, supporting the state-register count in
[BaskaranEtAl2023]. -/
theorem excitation_encoding_minimal {h p : ℕ} (S : Finset (RawSD h p))
    (r : ℕ) (f : S→Fin (2^r)) (hf : Function.Injective f) :
    stateRegisterQubits (Fintype.card S)≤r := by
  apply stateRegisterQubits_le_iff.mpr
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- For every positive natural number `h`, the bound `h ≤ 2 ^ (h - 1)` holds. -/
theorem orbital_le_binary_predecessor (h : ℕ) (hh : 0<h) : h≤2^(h-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  simp only [Nat.succ_sub_one]
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 0<2^n := by positivity
    omega

/-- For positive occupied and virtual orbital counts, the raw single/double excitation count is
at most `2 ^ (2 * (h + p) - 3)`. -/
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

/-- For positive occupied and virtual orbital counts, every selected raw single/double
excitation manifold uses strictly fewer state qubits than the `2 * (h + p)`-spin-orbital
register. This is the state-register comparison of [Baskaran et al., Section III
F][BaskaranEtAl2023]. -/
theorem actual_excitation_state_advantage (h p : ℕ) (hh : 0<h) (hp : 0<p)
    (S : Finset (RawSD h p)) :
    stateRegisterQubits (Fintype.card S)<qpeStateQubits (2*(h+p)) := by
  have hdim : Fintype.card S≤2^(2*(h+p)-1) :=
    (excitation_manifold_card h p S).trans ((actual_sd_capacity h p hh hp).trans
      (Nat.pow_le_pow_right (by norm_num : 0<2) (by omega)))
  exact hhlQubits_lt_qpeQubits (by omega) hdim

end Qatlib.Papers.HHLManyBody22.StateRegisters
