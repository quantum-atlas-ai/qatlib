/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalCircuits.LocalGateCosts.LocalGateDefs
import Qatlib.Foundations.BornMetrics.FiniteStats.Defs
import Mathlib.Data.ENat.Lattice
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.FiniteStats
open scoped BigOperators Matrix.Norms.L2Operator NNReal
namespace Qatlib.Concepts.LocalCircuits.LocalGateCosts

theorem prefixMap_bitVec (n l : ℕ) (hl : l ≤ n) (x : Reg n) :
    prefixMap n l hl (bitVecEquiv n x) =
      bitVecEquiv l (fun j => x (Fin.castLE hl j)) := by
  induction n generalizing l with
  | zero =>
    have h : l = 0 := by omega
    subst l
    haveI : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n ih =>
    by_cases h : l = n + 1
    · subst l
      have hf : (fun j => x (Fin.castLE hl j)) = x := by
        funext j
        rfl
      rw [hf]
      apply Fin.ext
      simp [prefixMap]
    · have hle : l ≤ n := by omega
      apply Fin.ext
      change (bitVecEquiv (n + 1) x).val / 2 ^ (n + 1 - l) = _
      have hden : 2 ^ (n + 1 - l) = 2 * 2 ^ (n - l) := by
        rw [show n + 1 - l = (n - l) + 1 by omega]
        exact Nat.pow_succ'
      rw [hden, ← Nat.div_div_eq_div_mul]
      have hhalf : (bitVecEquiv (n + 1) x).val / 2 = (bitVecEquiv n (Fin.init x)).val := by
        have he := bitVec_value_succ n x
        have hb := (boolEquivFin2 (x (Fin.last n))).isLt
        omega
      rw [hhalf]
      have he := congrArg Fin.val (ih l hle (Fin.init x))
      have hf : (fun j : Fin l => (Fin.init x) (Fin.castLE hle j)) =
          (fun j : Fin l => x (Fin.castLE hl j)) := by
        funext j
        rfl
      rw [hf] at he
      exact he

def repBy (g n b : ℕ) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {U | ∃ word : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
    word.length = b ∧ (∀ G ∈ word, G ∈ gateSet g n) ∧ word.prod = U}

theorem repBy_mul {g n b c : ℕ}
    {U V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hU : U ∈ repBy g n b) (hV : V ∈ repBy g n c) : U * V ∈ repBy g n (b + c) := by
  obtain ⟨us, hu, hlu, heu⟩ := hU
  obtain ⟨vs, hv, hlv, hev⟩ := hV
  refine ⟨us ++ vs, by simp [hu, hv], ?_, ?_⟩
  · intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact hlu G hG
    · exact hlv G hG
  · rw [List.prod_append, heu, hev]

theorem repBy_mono {g n b c : ℕ} (hbc : b ≤ c) : repBy g n b ⊆ repBy g n c := by
  rintro U ⟨word, hlen, hlegal, he⟩
  refine ⟨word ++ List.replicate (c - b) 1, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, hlen]
    omega
  · intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact hlegal G hG
    · obtain rfl := (List.mem_replicate.mp hG).2
      exact one_mem_gateSet g n
  · simp [List.prod_append, he]

theorem repBy_unitary {g n b : ℕ}
    {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hU : U ∈ repBy g n b) :
    U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  obtain ⟨word, hlen, hlegal, rfl⟩ := hU
  clear hlen
  induction word with
  | nil => exact Submonoid.one_mem _
  | cons G word ih =>
    rw [List.prod_cons]
    exact Submonoid.mul_mem _ (gateSet_unitary (hlegal G (by simp)))
      (ih (fun H hH => hlegal H (by simp [hH])))

theorem repBy_zero_width_offdiagonal {n b : ℕ}
    {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hU : U ∈ repBy 0 n b)
    (i j : Fin (2 ^ n)) (hij : i ≠ j) : U i j = 0 := by
  obtain ⟨word, _, hlegal, rfl⟩ := hU
  exact zero_width_product_offdiagonal word hlegal i j hij

def basisFrame (n k : ℕ) : Fin k → Fin (2 ^ n) → ℂ :=
  fun i a => if a.val = i.val then 1 else 0

def bComplexity (g n k : ℕ) (u v : Fin k → Fin (2 ^ n) → ℂ) : ℕ∞ :=
  sInf ((fun b : ℕ => (b : ℕ∞)) ''
    {b : ℕ | ∃ U ∈ repBy g n b, ∀ i, U *ᵥ u i = v i})

def bMax (g n k : ℕ) : ℕ∞ :=
  sSup {b : ℕ∞ | ∃ v : Fin k → Fin (2 ^ n) → ℂ,
    Orthonormal (2 ^ n) k v ∧ b = bComplexity g n k (basisFrame n k) v}

theorem bComplexity_le_program (g n k b : ℕ) (u v : Fin k → Fin (2 ^ n) → ℂ)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ repBy g n b) (huv : ∀ i, U *ᵥ u i = v i) :
    bComplexity g n k u v ≤ (b : ℕ∞) := by
  exact sInf_le ⟨b, ⟨U, hU, huv⟩, rfl⟩

theorem bComplexity_eq_top (g n k : ℕ) (u v : Fin k → Fin (2 ^ n) → ℂ)
    (h : ∀ b : ℕ, ¬ ∃ U ∈ repBy g n b, ∀ i, U *ᵥ u i = v i) :
    bComplexity g n k u v = ⊤ := by
  have hempty : {b : ℕ | ∃ U ∈ repBy g n b, ∀ i, U *ᵥ u i = v i} = ∅ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact h b
  simp only [bComplexity, hempty, Set.image_empty, sInf_empty]

theorem zero_width_flip_infinite :
    bComplexity 0 1 1 (basisFrame 1 1) (fun _ => ket (1 : Fin 2)) = ⊤ := by
  apply bComplexity_eq_top
  intro b
  rintro ⟨U, hU, hmap⟩
  have h := congrFun (hmap (0 : Fin 1)) (1 : Fin 2)
  have hz := repBy_zero_width_offdiagonal hU (1 : Fin 2) (0 : Fin 2) (by decide)
  simp [Matrix.mulVec, dotProduct, basisFrame, ket, hz] at h

def phaseGate (n : ℕ) (w : ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal (fun b => if b = 0 then Complex.exp (Complex.I * (w : ℂ)) else 1)

def bIstar (g n : ℕ) : ℕ∞ :=
  sInf ((fun b : ℕ => (b : ℕ∞)) '' {b : ℕ | ∀ w : ℝ, phaseGate n w ∈ repBy g n b})

end Qatlib.Concepts.LocalCircuits.LocalGateCosts
