/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

namespace Qatlib.Concepts.CodingDecoding.CssTesters

open Matrix Filter

open scoped Classical BigOperators ENNReal

noncomputable def blockWeight {F α κ : Type} [Zero F] [Fintype κ] [Fintype α] [DecidableEq α]
    (part : κ → α) (x : κ → F) : ℕ :=
  (Finset.univ.filter fun a : α => ∃ i, part i = a ∧ x i ≠ 0).card

noncomputable def blockDist {F α κ : Type} [Zero F] [Sub F] [Fintype κ] [Fintype α]
    [DecidableEq α] (part : κ → α) (x : κ → F) (S : Set (κ → F)) : ℕ∞ :=
  sInf {w : ℕ∞ | ∃ y ∈ S, (blockWeight part (fun i => x i - y i) : ℕ∞) = w}

noncomputable def binaryMatrix {F : Type} [Field F] [Algebra (ZMod 2) F] (s : ℕ)
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (A : Matrix κ' κ F) : Matrix (κ' × Fin s) (κ × Fin s) (ZMod 2) :=
  fun p q => e (A p.1 q.1 • e.symm (Pi.single q.2 1)) p.2

noncomputable def elementarySym (t : ℕ) (n : Fin t → ℕ) (j : ℕ) : ℕ :=
  if j ≤ t then
    (Finset.univ.filter fun s : Finset (Fin t) => s.card = j).sum fun s => s.prod n
  else 0

noncomputable def elementarySymR (t : ℕ) (S : Fin t → ℝ) (j : ℕ) : ℝ :=
  if j ≤ t then
    (Finset.univ.filter fun s : Finset (Fin t) => s.card = j).sum fun s => s.prod S
  else 0

noncomputable def muIB {t : ℕ} (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ) (i : Fin t) (b : Fin 2) : ℝ :=
  (m i b : ℝ) / (n i : ℝ)

noncomputable def sIB {t : ℕ} (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ) (i : Fin t) : ℝ :=
  muIB n m i 0 + muIB n m i 1

noncomputable def pIB {t : ℕ} (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ) (i : Fin t) : ℝ :=
  min (muIB n m i 0) (muIB n m i 1)

noncomputable def qIB {t : ℕ} (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ) (i : Fin t) : ℝ :=
  1 - max (muIB n m i 0) (muIB n m i 1)

noncomputable def scriptB (t j : ℕ) (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ) : ℝ :=
  (Finset.univ.filter fun s : Finset (Fin t) => s.card = j).sum fun s =>
    Finset.univ.prod fun i : Fin t => if i ∈ s then qIB n m i else pIB n m i

noncomputable def gammaK (t k : ℕ) (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ) : ℝ :=
  (-1 : ℝ) ^ k * Finset.univ.prod (fun i : Fin t => sIB n m i - 1) -
    ∑ j ∈ Finset.range (t + 1),
      if j % 2 = k % 2 ∧ j ≠ k then scriptB t j n m else 0

end Qatlib.Concepts.CodingDecoding.CssTesters
