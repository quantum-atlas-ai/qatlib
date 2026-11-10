/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Basic

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def FunDistLE (f g : E → E) (ε : ℝ) : Prop := ∀ x, ‖f x - g x‖ ≤ ε * ‖x‖

theorem FunDistLE.mono {f g : E → E} {ε ε' : ℝ} (h : FunDistLE f g ε) (hle : ε ≤ ε') :
    FunDistLE f g ε' := by
  intro x
  exact (h x).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg x))

theorem FunDistLE.add {f g h : E → E} {ε₁ ε₂ : ℝ}
    (h₁ : FunDistLE f g ε₁) (h₂ : FunDistLE g h ε₂) : FunDistLE f h (ε₁ + ε₂) := by
  intro x
  calc
    ‖f x - h x‖ = ‖(f x - g x) + (g x - h x)‖ := by abel_nf
    _ ≤ ‖f x - g x‖ + ‖g x - h x‖ := norm_add_le _ _
    _ ≤ ε₁ * ‖x‖ + ε₂ * ‖x‖ := add_le_add (h₁ x) (h₂ x)
    _ = (ε₁ + ε₂) * ‖x‖ := by ring

def evalWord {ι : Type*} (ρ : ι → E → E) (w : List ι) (x : E) : E :=
  w.foldr (fun i acc => ρ i acc) x

@[simp]
theorem evalWord_nil {ι : Type*} (ρ : ι → E → E) (x : E) :
    evalWord ρ ([] : List ι) x = x := rfl

@[simp]
theorem evalWord_cons {ι : Type*} (ρ : ι → E → E) (i : ι) (w : List ι) (x : E) :
    evalWord ρ (i :: w) x = ρ i (evalWord ρ w x) := rfl

theorem norm_evalWord {ι : Type*} (ρ : ι → E ≃ₗᵢ[ℂ] E) (w : List ι) (x : E) :
    ‖evalWord (fun i => (ρ i : E → E)) w x‖ = ‖x‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [evalWord_cons]
    rw [(ρ i).norm_map, ih]

theorem evalWord_approx {ι : Type*} (ρ ρ' : ι → E ≃ₗᵢ[ℂ] E) (η : ℝ) (hη : 0 ≤ η)
    (h : ∀ i, FunDistLE (ρ i) (ρ' i) η) (w : List ι) :
    FunDistLE (evalWord (fun i => (ρ i : E → E)) w)
      (evalWord (fun i => (ρ' i : E → E)) w) (w.length * η) := by
  intro x
  induction w with
  | nil =>
    simp [evalWord]
  | cons i w ih =>

    have hsplit :
        (ρ i (evalWord (fun j => (ρ j : E → E)) w x) -
          ρ' i (evalWord (fun j => (ρ' j : E → E)) w x)) =
        ((ρ i (evalWord (fun j => (ρ j : E → E)) w x) -
            ρ i (evalWord (fun j => (ρ' j : E → E)) w x)) +
          (ρ i (evalWord (fun j => (ρ' j : E → E)) w x) -
            ρ' i (evalWord (fun j => (ρ' j : E → E)) w x))) := by
      abel
    rw [evalWord_cons, evalWord_cons, hsplit]
    have hhead : ‖ρ i (evalWord (fun j => (ρ j : E → E)) w x) -
        ρ i (evalWord (fun j => (ρ' j : E → E)) w x)‖ ≤ w.length * η * ‖x‖ := by
      have := ih
      calc
        ‖ρ i (evalWord (fun j => (ρ j : E → E)) w x) -
            ρ i (evalWord (fun j => (ρ' j : E → E)) w x)‖
            = ‖evalWord (fun j => (ρ j : E → E)) w x -
                evalWord (fun j => (ρ' j : E → E)) w x‖ := by
              rw [← (ρ i).map_sub, (ρ i).norm_map]
        _ ≤ w.length * η * ‖x‖ := this
    have htail : ‖ρ i (evalWord (fun j => (ρ' j : E → E)) w x) -
        ρ' i (evalWord (fun j => (ρ' j : E → E)) w x)‖ ≤ η * ‖x‖ := by
      have := h i (evalWord (fun j => (ρ' j : E → E)) w x)
      rwa [norm_evalWord] at this
    have hnorm : ‖x‖ ≥ 0 := norm_nonneg x
    calc
      ‖(ρ i (evalWord (fun j => (ρ j : E → E)) w x) -
            ρ i (evalWord (fun j => (ρ' j : E → E)) w x)) +
          (ρ i (evalWord (fun j => (ρ' j : E → E)) w x) -
            ρ' i (evalWord (fun j => (ρ' j : E → E)) w x))‖
          ≤ ‖ρ i (evalWord (fun j => (ρ j : E → E)) w x) -
              ρ i (evalWord (fun j => (ρ' j : E → E)) w x)‖ +
            ‖ρ i (evalWord (fun j => (ρ' j : E → E)) w x) -
              ρ' i (evalWord (fun j => (ρ' j : E → E)) w x)‖ := norm_add_le _ _
      _ ≤ w.length * η * ‖x‖ + η * ‖x‖ := add_le_add hhead htail
      _ = (w.length + 1) * η * ‖x‖ := by ring
      _ = ((i :: w).length : ℝ) * η * ‖x‖ := by simp [List.length_cons]

theorem claim31_error_accumulation {ι : Type*} (ρ ρ' : ι → E ≃ₗᵢ[ℂ] E) (ε : ℝ)
    (hε : 0 < ε) (L : ℕ) (hL : 0 < L)
    (h : ∀ i, FunDistLE (ρ i) (ρ' i) (ε / L)) (w : List ι) (hw : w.length = L) (x : E) :
    ‖evalWord (fun i => (ρ i : E → E)) w x -
        evalWord (fun i => (ρ' i : E → E)) w x‖ ≤ ε * ‖x‖ := by
  have hη : 0 ≤ ε / L := le_of_lt (div_pos hε (by exact_mod_cast hL))
  have hmain := evalWord_approx ρ ρ' (ε / L) hη h w x
  rw [hw] at hmain
  have hmul : (L : ℝ) * (ε / L) = ε := by
    field_simp
  rw [hmul] at hmain
  exact hmain

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
