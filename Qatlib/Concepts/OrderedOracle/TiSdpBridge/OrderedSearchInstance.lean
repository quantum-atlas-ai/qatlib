/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.BSSSdp

set_option autoImplicit false

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

def finShiftEquiv (N : ℕ) [NeZero N] : Fin N ≃ Fin N where
  toFun i := ⟨(i + 1) % N, Nat.mod_lt _ (NeZero.pos _)⟩
  invFun i := ⟨(i + (N - 1)) % N, Nat.mod_lt _ (NeZero.pos _)⟩
  left_inv i := by
    have hN : 0 < N := NeZero.pos N
    have hi : (i : ℕ) < N := i.isLt
    apply Fin.val_injective
    show (((i : ℕ) + 1) % N + (N - 1)) % N = (i : ℕ)
    rcases Nat.lt_or_ge ((i : ℕ) + 1) N with h | h
    · rw [Nat.mod_eq_of_lt h, show (i : ℕ) + 1 + (N - 1) = (i : ℕ) + N by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · rw [show (i : ℕ) + 1 = N by omega, Nat.mod_self, Nat.zero_add,
        show N - 1 = (i : ℕ) by omega, Nat.mod_eq_of_lt hi]
  right_inv i := by
    have hN : 0 < N := NeZero.pos N
    have hi : (i : ℕ) < N := i.isLt
    apply Fin.val_injective
    show (((i : ℕ) + (N - 1)) % N + 1) % N = (i : ℕ)
    rcases Nat.eq_zero_or_pos ((i : ℕ)) with h0 | h0
    · have hm : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
      rw [h0, Nat.zero_add, hm, show N - 1 + 1 = N by omega, Nat.mod_self]
    · have hm : (((i : ℕ) - 1) + N) % N = ((i : ℕ) - 1) % N := Nat.add_mod_right _ N
      have hm2 : ((i : ℕ) - 1) % N = (i : ℕ) - 1 := Nat.mod_eq_of_lt (by omega)
      rw [show (i : ℕ) + (N - 1) = ((i : ℕ) - 1) + N by omega, hm, hm2,
        show ((i : ℕ) - 1) + 1 = (i : ℕ) by omega, Nat.mod_eq_of_lt hi]

def ospBit (n : ℕ) [NeZero n] (j i : Fin (2 * n)) : Bool :=
  decide (((i : ℤ) - (j : ℤ)) % (2 * n) < (n : ℤ))

def ospFun (n : ℕ) [NeZero n] : Fin (2 * n) → Fin n := fun j => ⟨(j : ℕ) % n, by
  have : 0 < n := NeZero.pos n
  exact Nat.mod_lt _ this⟩

def ospInvariantFamily (n : ℕ) [NeZero n]
    (M : Fin (2 * n) → ℕ → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (N : ℕ → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (Γ : Fin n → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : Prop :=
  (∀ i t x x', M i t (finShiftEquiv (2 * n) x) (finShiftEquiv (2 * n) x')
      = M ((finShiftEquiv (2 * n)).symm i) t x x') ∧
  (∀ t x x', N t (finShiftEquiv (2 * n) x) (finShiftEquiv (2 * n) x') = N t x x') ∧
  (∀ y x x', Γ y (finShiftEquiv (2 * n) x) (finShiftEquiv (2 * n) x')
      = Γ ((finShiftEquiv n).symm y) x x')

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
