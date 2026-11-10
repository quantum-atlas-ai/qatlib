/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkCoreDefs
set_option warningAsError false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs

noncomputable def word {n d D : ℕ} (A : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (x : Fin n → Fin d) : Matrix (Fin D) (Fin D) ℂ :=
  (List.ofFn fun i : Fin n => A i (x i)).prod

noncomputable def T {n d D : ℕ} (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (i : Fin n) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.of fun p q => ∑ s : Fin d, star (A i s p.1 q.1) * B i s p.2 q.2

noncomputable def transferWord {n d D : ℕ} (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  (List.ofFn fun i : Fin n => T A B i).prod

def plusISite (n : ℕ) : Fin n → Fin 1 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => Matrix.of fun _ _ => 1 + Complex.I

def bellSite : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i s => Matrix.of fun l r =>
    if i.val = 0 then (if l = 0 ∧ r = s then (1 : ℂ) else 0)
    else (if r = 0 ∧ l = s then (1 : ℂ) else 0)

def phiSite : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ j => Matrix.of fun _ _ => if j.val = 0 then (1 : ℂ) else 0

def psiSite : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ j => Matrix.of fun _ _ => if j.val = 1 then (1 : ℂ) else 0

def iSite : Fin 1 → Fin 1 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => Matrix.of fun _ _ => Complex.I

def oneSite : Fin 1 → Fin 1 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => Matrix.of fun _ _ => 1

def zeroSite (n d D : ℕ) : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun _ _ => 0

def diagSite : Fin 1 → Fin 1 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ _ => Matrix.of fun l r =>
    if l = r then (if l.val = 0 then (1 : ℂ) else 2) else 0

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.MpsExternalAdaptationDefs
