/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

def TriorthogonalLogicalPaulis : Prop :=
  ∀ (m n k : ℕ) (D : TriorthogonalData m n k) (a b : Fin k) (β γ : F1024),
    (∀ w ∈ triDual (triG D),
      quditXVec (β • D.G (Fin.castLE D.hk a)) * quditZVec w
        = quditZVec w * quditXVec (β • D.G (Fin.castLE D.hk a)))
    ∧ (∀ v ∈ triG0 D,
      quditZVec (γ • triGhat D a) * quditXVec v
        = quditXVec v * quditZVec (γ • triGhat D a))
    ∧ (quditXVec (β • D.G (Fin.castLE D.hk a)) * quditZVec (γ • triGhat D b)
        = qPhase (f1024Trace (β * γ) * if a = b then 1 else 0)
            • (quditZVec (γ • triGhat D b)
                * quditXVec (β • D.G (Fin.castLE D.hk a))))

end Qatlib.Papers.MagicDistill24.Triorthogonal
