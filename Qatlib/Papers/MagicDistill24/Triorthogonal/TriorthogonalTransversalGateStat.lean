/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

def TriorthogonalTransversalGate : Prop :=
  ∀ (m n k : ℕ) (D : TriorthogonalData m n k) (u : Fin k → F1024),
    tensorDiagGate u1SeventhPhase *ᵥ triCodeword D u
      = Complex.exp (Complex.I * Real.pi * ((f1024Trace (∑ a, u a ^ 7)).val : ℝ))
          • triCodeword D u

end Qatlib.Papers.MagicDistill24.Triorthogonal
