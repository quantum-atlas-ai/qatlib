/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.Proposition19CyclicSymmetryStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- The cyclic input, query-index, and output shifts define a BSS symmetry of the ordered-search
instance. -/
theorem proposition19CyclicSymmetry : Proposition19CyclicSymmetry := by
  intro n _hn

  have subR : ∀ a c : ℤ, ((a % ((2 * n : ℕ) : ℤ)) - c) % ((2 * n : ℕ) : ℤ)
      = (a - c) % ((2 * n : ℕ) : ℤ) := fun a c =>
    Int.ModEq.eq (Int.ModEq.sub (Int.mod_modEq a _) (Int.ModEq.refl c))
  have subL : ∀ a c : ℤ, (a - (c % ((2 * n : ℕ) : ℤ))) % ((2 * n : ℕ) : ℤ)
      = (a - c) % ((2 * n : ℕ) : ℤ) := fun a c =>
    Int.ModEq.eq (Int.ModEq.sub (Int.ModEq.refl a) (Int.mod_modEq c _))
  have addM : ∀ c : ℤ, (c + ((2 * n : ℕ) : ℤ)) % ((2 * n : ℕ) : ℤ)
      = c % ((2 * n : ℕ) : ℤ) := by
    intro c
    rw [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]

  have key : ∀ (y i : Fin (2 * n)),
      ospBit n y ((finShiftEquiv (2 * n)).symm i)
        = ospBit n (finShiftEquiv (2 * n) y) i := by
    intro y i
    have hsymm : (((finShiftEquiv (2 * n)).symm i : Fin (2 * n)) : ℕ)
        = ((i : ℕ) + (2 * n - 1)) % (2 * n) := rfl
    have hT : ((finShiftEquiv (2 * n) y : Fin (2 * n)) : ℕ)
        = ((y : ℕ) + 1) % (2 * n) := rfl
    have eX : (((((i : ℕ) + (2 * n - 1)) % (2 * n) : ℕ) : ℤ))
        = ((((i : ℕ) + (2 * n - 1) : ℕ) : ℤ)) % ((2 * n : ℕ) : ℤ) :=
      Int.natCast_mod _ _
    have eY : (((((y : ℕ) + 1) % (2 * n) : ℕ) : ℤ))
        = ((((y : ℕ) + 1 : ℕ) : ℤ)) % ((2 * n : ℕ) : ℤ) :=
      Int.natCast_mod _ _
    have hcastX : ((((i : ℕ) + (2 * n - 1) : ℕ) : ℤ)) = (i : ℤ) + ((2 * n : ℕ) : ℤ) - 1 := by
      push_cast
      omega
    have hcastY : ((((y : ℕ) + 1 : ℕ) : ℤ)) = (y : ℤ) + 1 := by
      push_cast
      ring
    have hres : (((((i : ℕ) + (2 * n - 1)) % (2 * n) : ℕ) : ℤ) - (y : ℤ))
          % ((2 * n : ℕ) : ℤ)
        = ((i : ℤ) - ((((y : ℕ) + 1) % (2 * n) : ℕ) : ℤ)) % ((2 * n : ℕ) : ℤ) := by
      rw [eX, subR, hcastX,
        show ((i : ℤ) + ((2 * n : ℕ) : ℤ) - 1 - (y : ℤ))
          = ((i : ℤ) - (y : ℤ) - 1) + ((2 * n : ℕ) : ℤ) from by ring, addM]
      rw [eY, subL, hcastY,
        show ((i : ℤ) - ((y : ℤ) + 1)) = ((i : ℤ) - (y : ℤ) - 1) from by ring]
    simp only [ospBit, decide_eq_decide]
    rw [hsymm, hT]
    exact iff_of_eq (congrArg (fun z : ℤ => z < (n : ℤ)) hres)
  refine ⟨?_, ?_⟩
  · intro i x x'
    simp only [bssE, Matrix.of_apply]
    rw [key x i, key x' i]
  · intro x
    apply Fin.val_injective
    show (((x : ℕ) % n + 1) % n) = ((((x : ℕ) + 1) % (2 * n)) % n)
    rw [Nat.mod_add_mod, Nat.mod_mod_of_dvd _ (by norm_num : n ∣ 2 * n)]
