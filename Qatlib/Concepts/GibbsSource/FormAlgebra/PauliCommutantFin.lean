/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.FormAlgebra.PauliCommutant
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section


/-! Transport of the Pauli common-commutant theorem to a finite matrix index.
The register equivalence is explicit, with no kernel or target-gap premise. -/
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib

namespace Qatlib.Concepts.GibbsSource.FormAlgebra

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def regIndexEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → ZMod 2) ≃ Fin (Fintype.card (ι → ZMod 2)) :=
  Fintype.equivFin _

/-- A finitely indexed matrix commuting with all reindexed single-site Pauli X and Z matrices is
a scalar multiple of the identity. -/
theorem singleSitePauli_commutant_scalar_fin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Z : Matrix (Fin (Fintype.card (ι → ZMod 2))) (Fin (Fintype.card (ι → ZMod 2))) ℂ}
    (hX : ∀ i, Z * (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv ι)) (cssPauliX (Pi.single i 1))
        = (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv ι)) (cssPauliX (Pi.single i 1)) * Z)
    (hZ : ∀ i, Z * (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv ι)) (cssPauliZ (Pi.single i 1))
        = (Matrix.reindexAlgEquiv ℂ ℂ (regIndexEquiv ι)) (cssPauliZ (Pi.single i 1)) * Z) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin (Fintype.card (ι → ZMod 2)))
      (Fin (Fintype.card (ι → ZMod 2))) ℂ) := by
  classical
  set e : (ι → ZMod 2) ≃ Fin (Fintype.card (ι → ZMod 2)) := regIndexEquiv ι with he
  set Y : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ := (Matrix.reindexAlgEquiv ℂ ℂ e).symm Z with hY
  have hX' : ∀ i, Y * cssPauliX (Pi.single i 1) = cssPauliX (Pi.single i 1) * Y := by
    intro i
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e).symm (hX i)
    simpa [hY, map_mul] using h
  have hZ' : ∀ i, Y * cssPauliZ (Pi.single i 1) = cssPauliZ (Pi.single i 1) * Y := by
    intro i
    have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e).symm (hZ i)
    simpa [hY, map_mul] using h
  obtain ⟨c, hc⟩ := singleSitePauli_commutant_scalar hX' hZ'
  refine ⟨c, ?_⟩
  have h := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) hc
  simpa [hY, map_mul, map_smul, map_one] using h

/-- The number of binary registers on `ι` is two to the power of the cardinality of `ι`. -/
theorem card_regIndexEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Fintype.card (ι → ZMod 2) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun]
  congr 1

end Qatlib.Concepts.GibbsSource.FormAlgebra
