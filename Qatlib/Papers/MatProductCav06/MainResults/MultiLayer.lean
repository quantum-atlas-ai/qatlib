/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProductCav06.MainResults.SequentialDefs

/-!
# Layers of local gates and bond dimensions

`applyLocal` contracts a two-site matrix with amplitudes on cyclic neighboring sites, and
`applyLayer` applies these operations in site order. `InLayerClass` starts from computational
basis states; the module proves identity layer closure, bond dimension formulas, and bond
dimension one representations at depth zero. See [SchoenEtAl2007] for the sequential generation
setting.

## Main statements

* `layerBondDim_succ`: multiplicative recurrence for positive layer counts.
* `layer_class_succ`: inclusion of each layer class in the next.
* `layer_zero_mps`: depth zero states have bond dimension one.

## References

* [Schoen et al., 2007][SchoenEtAl2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.MatProductCav06.MainResults

/-- The cyclic successor of a site in a nonempty chain. -/
def nextSite {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩

/-- Applies the two-site matrix `g` at `i` and its cyclic successor by summing over their input
indices. -/
def applyLocal {n d : ℕ} (hn : 0 < n) (i : Fin n)
    (g : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (ψ : (Fin n → Fin d) → ℂ) :
    (Fin n → Fin d) → ℂ :=
  fun x => ∑ uv : Fin d × Fin d,
    g (x i, x (nextSite hn i)) uv *
      ψ (fun j => if j = i then uv.1 else if j = nextSite hn i then uv.2 else x j)

/-- Applies the local matrices successively in the order of the finite site list. -/
def applyLayer {n d : ℕ} (hn : 0 < n)
    (g : Fin n → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ψ : (Fin n → Fin d) → ℂ) : (Fin n → Fin d) → ℂ :=
  (List.ofFn (fun i : Fin n => i)).foldl (fun ψ i => applyLocal hn i (g i) ψ) ψ

/-- The recursively defined class starting from computational basis states and adding ordered
layers of matrices satisfying `gᴴ * g = 1`. -/
def InLayerClass (n d : ℕ) (hn : 0 < n) : ℕ → ((Fin n → Fin d) → ℂ) → Prop
  | 0, ψ => ∃ w : Fin n → Fin d, ψ = basisState w
  | m + 1, ψ => ∃ φ, InLayerClass n d hn m φ ∧
      ∃ g : Fin n → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
        (∀ i, (g i)ᴴ * (g i) = 1) ∧ ψ = applyLayer hn g φ

/-- The bond dimension expression `d ^ (2 * m - 1)`, with subtraction in the natural numbers. -/
def layerBondDim (d m : ℕ) : ℕ :=
  d ^ (2 * m - 1)

/-- The bond dimension expression for one layer equals `d`. -/
theorem layerBondDim_one (d : ℕ) : layerBondDim d 1 = d := by
  simp [layerBondDim]

/-- For `m ≥ 1`, increasing the layer count multiplies `layerBondDim` by `d ^ 2`. See
[SchoenEtAl2007]. -/
theorem layerBondDim_succ {d m : ℕ} (hm : 1 ≤ m) :
    layerBondDim d (m + 1) = d ^ 2 * layerBondDim d m := by
  unfold layerBondDim
  have h : 2 * (m + 1) - 1 = (2 * m - 1) + 2 := by omega
  rw [h, pow_add]
  ring

/-- For qubits, `layerBondDim 2 m` equals `2 ^ (2 * m - 1)`. -/
theorem layerBondDim_qubit (m : ℕ) : layerBondDim 2 m = 2 ^ (2 * m - 1) :=
  rfl

/-- For `d ≥ 2` and `m ≥ 1`, the bond dimension expression strictly increases when the layer
count increases by one. See [SchoenEtAl2007]. -/
theorem layerBondDim_strictMono {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) :
    layerBondDim d m < layerBondDim d (m + 1) := by
  unfold layerBondDim
  exact Nat.pow_lt_pow_right (by omega) (by omega)

/-- Applying the identity two-site matrix leaves the amplitude function unchanged. -/
theorem applyLocal_one {n d : ℕ} (hn : 0 < n) (i : Fin n)
    (ψ : (Fin n → Fin d) → ℂ) :
    applyLocal hn i (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ψ = ψ := by
  classical
  funext x
  rw [applyLocal]
  simp only [Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (x i)]
  · rw [Finset.sum_eq_single (x (nextSite hn i))]
    · have hsub :
          (fun j => if j = i then x i
            else if j = nextSite hn i then x (nextSite hn i) else x j) = x := by
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · by_cases hjn : j = nextSite hn i
          · subst hjn
            by_cases h3 : nextSite hn i = i
            · rw [h3]; simp
            · simp [h3]
          · simp [hji, hjn]
      rw [hsub]
      simp
    · intro uv2 _ huv2
      have hne : x (nextSite hn i) ≠ uv2 := fun h => huv2 h.symm
      simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro uv1 _ huv1
    have hne : x i ≠ uv1 := fun h => huv1 h.symm
    simp [hne]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- Folding identity local operations over any list of sites leaves the amplitude function
unchanged. -/
theorem foldl_applyLocal_one {n d : ℕ} (hn : 0 < n) (l : List (Fin n))
    (ψ : (Fin n → Fin d) → ℂ) :
    l.foldl (fun (ψ : (Fin n → Fin d) → ℂ) (i : Fin n) => applyLocal hn i 1 ψ) ψ = ψ := by
  induction l generalizing ψ with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    exact (ih (applyLocal hn a 1 ψ)).trans (applyLocal_one hn a ψ)

/-- A layer consisting entirely of identity matrices leaves the amplitude function unchanged. -/
theorem applyLayer_one {n d : ℕ} (hn : 0 < n) (ψ : (Fin n → Fin d) → ℂ) :
    applyLayer hn (fun _ => (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) ψ = ψ := by
  unfold applyLayer
  show (List.ofFn (fun i : Fin n => i)).foldl
    (fun (ψ : (Fin n → Fin d) → ℂ) (i : Fin n) =>
      applyLocal hn i (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ψ) ψ = ψ
  exact foldl_applyLocal_one hn _ ψ

/-- Every member of the `m`-layer class belongs to the `(m + 1)`-layer class. See
[SchoenEtAl2007]. -/
theorem layer_class_succ {n d m : ℕ} (hn : 0 < n) {ψ : (Fin n → Fin d) → ℂ}
    (h : InLayerClass n d hn m ψ) : InLayerClass n d hn (m + 1) ψ := by
  refine ⟨ψ, h, fun _ => 1, fun _ => ?_, (applyLayer_one hn ψ).symm⟩
  simp

/-- Every state in the zero-layer class belongs to the matrix product class with bond dimension
one. See [SchoenEtAl2007]. -/
theorem layer_zero_mps {n d : ℕ} (hn : 0 < n) {ψ : (Fin n → Fin d) → ℂ}
    (h : InLayerClass n d hn 0 ψ) : InMpsClass n d 1 ψ := by
  rcases h with ⟨w, rfl⟩
  exact basisState_mps w

/-- Every state in the zero-layer class belongs to the deterministic sequential class with bond
dimension one. See [SchoenEtAl2007]. -/
theorem layer_zero_det {n d : ℕ} (hn : 0 < n) {ψ : (Fin n → Fin d) → ℂ}
    (h : InLayerClass n d hn 0 ψ) : InDetSequentialClass n d 1 ψ := by
  rcases h with ⟨w, rfl⟩
  exact basisState_det w

end Qatlib.Papers.MatProductCav06.MainResults
