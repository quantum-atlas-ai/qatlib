/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsom13.GiCost
import Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryWords
set_option warningAsError false

namespace Qatlib.Papers.GraphIsom13.BinaryEncoding
set_option autoImplicit false
noncomputable section
open Qatlib.Papers.GraphIsom13.GiCost
open Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryWords

abbrev Bits (N : ℕ) := Fin (N * encBits N) → Bool

def splitEquiv (N : ℕ) : Bits N ≃ (Fin N → Fin (encBits N) → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def parseEquiv (N : ℕ) : Bits N ≃ IntStr N :=
  (splitEquiv N).trans (Equiv.piCongrRight fun _ => blockEquiv (encBits N))

theorem split_address (N : ℕ) (b : Bits N) (i : Fin N) (j : Fin (encBits N)) :
    splitEquiv N b i j = b (finProdFinEquiv (i,j)) := rfl

theorem parse_value (N : ℕ) (b : Bits N) (i : Fin N) :
    (parseEquiv N b i).val = ∑ j : Fin (encBits N),
      bitValue (b (finProdFinEquiv (i,j))) * 2^j.val := blockEquiv_value _ _

theorem parse_bijective (N : ℕ) : Function.Bijective (parseEquiv N) := (parseEquiv N).bijective

def bitCost {N : ℕ} (G G' : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (b : Bits N) : ℕ := cost G G' (parseEquiv N b)

theorem bitCost_zero_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    (∃ b : Bits N, bitCost G G' b = 0) ↔ Nonempty (G ≃g G') := by
  rw [← gi_cop_zero_iff G G']
  constructor
  · rintro ⟨b,hb⟩; exact ⟨parseEquiv N b,hb⟩
  · rintro ⟨s,hs⟩
    exact ⟨(parseEquiv N).symm s,by simpa [bitCost] using hs⟩
end
end Qatlib.Papers.GraphIsom13.BinaryEncoding
