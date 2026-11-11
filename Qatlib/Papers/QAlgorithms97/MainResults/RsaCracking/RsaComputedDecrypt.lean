/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.RsaCracking
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Units

/-!
# RSA computed decryption from a recovered order (Appendix A)

Paper: R. Cleve, A. Ekert, C. Macchiavello, M. Mosca, *Quantum Algorithms
Revisited*, arXiv:quant-ph/9708016 (fixed PDF `quant-ph_9708016.pdf`).

The promoted module `Qatlib.Papers.QAlgorithms97.MainResults.RsaCracking`
formalises the conditional group-theoretic core: if `e` is coprime to
`φ(N)` and `C = P^e`, then `ord(C) = ord(P)`, and any `d` with
`d·e ≡ 1 (mod ord(P))` decrypts `C` back to `P`.

This module adds the actually-computed decoder: the inverse exponent is
produced by ZMod inversion (implemented by the extended Euclidean
algorithm), its congruence is proved including the order-one case, and once
the ciphertext's exact order is recovered the computed decoder returns the
plaintext.  The decoder's bit-time and the quantum order-finding backend are
separate obligations.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAlgorithms97.MainResults.RsaCracking

open Qatlib.Papers.QAlgorithms97.MainResults.RsaCracking

/-- The natural inverse exponent actually computed by the extended Euclidean ZMod inversion algorithm. -/
def rsaInverseExponent (e r : ℕ) : ℕ := ((e : ZMod r)⁻¹).val

/-- The computed inverse satisfies the required congruence, including the order-one case. -/
theorem rsaInverseExponent_congruence (e r : ℕ) (h : Nat.Coprime e r) :
    rsaInverseExponent e r * e ≡ 1 [MOD r] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa only [rsaInverseExponent, Nat.cast_mul, Nat.cast_one] using ZMod.val_inv_mul h

/-- The classical decoder uses the ciphertext and its supplied recovered order, without factoring N. -/
def rsaDecryptFromOrder {N : ℕ} [NeZero N] (C : (ZMod N)ˣ) (e r : ℕ) : (ZMod N)ˣ :=
  C ^ rsaInverseExponent e r

/-- Once the ciphertext's exact order is recovered, the actual Euclidean decoder returns the plaintext. -/
theorem rsa_computed_decryption {N e : ℕ} [NeZero N] (P : (ZMod N)ˣ)
    (he : Nat.Coprime e (Nat.totient N)) :
    rsaDecryptFromOrder (P ^ e) e (orderOf (P ^ e)) = P := by
  rw [rsaDecryptFromOrder, rsa_order_pow_eq P he]
  apply rsa_recover_plaintext
  apply rsaInverseExponent_congruence
  apply he.of_dvd_right
  rw [← ZMod.card_units_eq_totient N]
  exact orderOf_dvd_card

end Qatlib.Papers.QAlgorithms97.MainResults.RsaCracking
