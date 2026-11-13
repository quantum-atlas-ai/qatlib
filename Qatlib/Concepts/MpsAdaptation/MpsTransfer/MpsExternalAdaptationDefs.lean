/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkCoreDefs

/-!
# MPS words and mixed-transfer matrices

`word` forms the ordered matrix product associated with a physical word, `T` defines a local
mixed-transfer matrix on paired bond indices, and `transferWord` multiplies these local matrices
in site order.

The module also defines scalar, Bell, product-state, zero, and diagonal tensor examples for
subsequent overlap calculations. For the matrix product state framework, see
[PerezGarciaEtAl2007].

## Main statements

* `word`: The site-ordered product of matrices chosen by a physical word.
* `T`: The local sum of conjugate-left and right tensor entries on paired bonds.
* `transferWord`: The ordered product of the local mixed-transfer matrices.

## References

* [Perez-Garcia et al., 2007][PerezGarciaEtAl2007]
-/

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs

/-- The site-ordered product of the matrices selected by a physical word. -/
noncomputable def word {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i : Fin n => A i (x i)).prod

/-- The local mixed-transfer matrix on paired bond indices, summing conjugated entries of `A`
times entries of `B` over the physical index. -/
noncomputable def T {n d D : ℕ} (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (i : Fin n) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.of fun p q => ∑ s : Fin d, star (A i s p.1 q.1) * B i s p.2 q.2

/-- The site-ordered product of the local mixed-transfer matrices. -/
noncomputable def transferWord {n d D : ℕ} (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  (List.ofFn fun i : Fin n => T A B i).prod

/-- A scalar tensor family with one physical symbol and constant entry `1 + Complex.I`. -/
def plusISite (n : ℕ) : Fin n → Fin 1 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => Matrix.of fun _ _ => 1 + Complex.I

/-- A two-site binary tensor family whose open-boundary contraction represents the unnormalized
Bell vector. -/
def bellSite : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i s => Matrix.of fun l r =>
    if i.val = 0 then (if l = 0 ∧ r = s then (1 : ℂ) else 0)
    else (if r = 0 ∧ l = s then (1 : ℂ) else 0)

/-- A two-site scalar tensor family supported on the zero physical symbol at each site. -/
def phiSite : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ j => Matrix.of fun _ _ => if j.val = 0 then (1 : ℂ) else 0

/-- A two-site scalar tensor family supported on the one physical symbol at each site. -/
def psiSite : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ j => Matrix.of fun _ _ => if j.val = 1 then (1 : ℂ) else 0

/-- A one-site scalar tensor with entry `Complex.I`. -/
def iSite : Fin 1 → Fin 1 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => Matrix.of fun _ _ => Complex.I

/-- A one-site scalar tensor with entry one. -/
def oneSite : Fin 1 → Fin 1 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => Matrix.of fun _ _ => 1

/-- The identically zero tensor family with the specified site, physical, and bond dimensions. -/
def zeroSite (n d D : ℕ) : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun _ _ => 0

/-- A one-site tensor with one physical symbol and bond matrix having diagonal entries one and
two. -/
def diagSite : Fin 1 → Fin 1 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ _ => Matrix.of fun l r =>
    if l = r then (if l.val = 0 then (1 : ℂ) else 2) else 0

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs
