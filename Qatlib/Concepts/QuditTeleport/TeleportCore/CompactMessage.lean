/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation

@[expose] public section

/-!
# Joint fixed-width encoding of the qudit teleportation outcome

A pair of classical outcomes in an `n`-dimensional protocol is one
label among `n²` choices. Encoding the joint label avoids rounding the
two component widths separately. Decoding restores the exact branch
label used by the existing teleportation protocol.
-/

set_option autoImplicit false

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QuditTeleport.TeleportCore

/-- Encode the joint outcome in the ceiling of the binary logarithm of
the number of possible labels. -/
def quditCompactMessage (n : ℕ) (o : Fin n × Fin n) : List Bool :=
  quditEncode (Nat.clog 2 (n * n)) (quditOutcomeEquiv n o).val

/-- Decode a message of the prescribed width, rejecting unused labels
and packets of any other length. -/
def quditCompactDecode (n : ℕ) (bits : List Bool) : Option (Fin n × Fin n) :=
  if bits.length = Nat.clog 2 (n * n) then
    let label := quditDecodeNat bits
    if h : label < n * n then some ((quditOutcomeEquiv n).symm ⟨label, h⟩) else none
  else none

/-- The joint packet has the prescribed width and decodes to the exact
measurement outcome. -/
theorem qudit_compact_message_decode (n : ℕ) (o : Fin n × Fin n) :
    (quditCompactMessage n o).length = Nat.clog 2 (n * n) ∧
    quditCompactDecode n (quditCompactMessage n o) = some o := by
  have hlen : (quditCompactMessage n o).length = Nat.clog 2 (n * n) := by
    simp [quditCompactMessage, quditEncode]
  have hcapacity : n * n ≤ 2 ^ Nat.clog 2 (n * n) :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
  let label := quditOutcomeEquiv n o
  have hroundtrip : quditDecodeNat (quditCompactMessage n o) = label.val :=
    quditDecodeNat_exact _ _ (label.isLt.trans_le hcapacity)
  refine ⟨hlen, ?_⟩
  simp only [quditCompactDecode, hlen, ite_true, hroundtrip, label.isLt, dite_true]
  exact congrArg some ((quditOutcomeEquiv n).symm_apply_apply o)

/-- The joint label is never wider than the concatenation of two
individually rounded indices. -/
theorem qudit_compact_width_le (n : ℕ) :
    Nat.clog 2 (n * n) ≤ 2 * Nat.clog 2 n := by
  have hn : n ≤ 2 ^ Nat.clog 2 n :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  rw [two_mul, pow_add]
  exact Nat.mul_le_mul hn hn

end Qatlib.Concepts.QuditTeleport.TeleportCore
