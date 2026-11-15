/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.BinaryConversionSoundness
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
public import Qatlib.Concepts.CodingDecoding.CssTesters.FieldBinaryMatrix

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.BinaryConversionSoundness
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

namespace Qatlib.Concepts.CodingDecoding.FamilyAssembly

open Matrix

open scoped Classical BigOperators ENNReal

/-- Under the stated chain-complex, dimension, distance, soundness, and sparsity assumptions,
binary conversion yields a CSS code satisfying the explicit parameter bounds. -/
theorem abstractParameterGuarantee :
    ∀ (t k s : ℕ) (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ)
      (K ρ lam ℒ 𝒬 : ℝ)
      (F : Type) [Field F] [Algebra (ZMod 2) F] [Module.Free (ZMod 2) F]
      [Fintype F] [Module.Finite (ZMod 2) F],
      4 ≤ t → 2 ≤ k → k + 2 ≤ t → 0 < s →
      (∀ i : Fin t, 2 ≤ n i) → (∀ i : Fin t, ∀ b : Fin 2, 0 < m i b ∧ m i b < n i) →
      1 ≤ K → 0 < ρ ∧ ρ ≤ 1 → 0 ≤ lam ∧ lam < 1 →
      0 < ℒ → 0 < 𝒬 →
      0 < gammaK t k n m → lam * ℒ < 1 → 0 < (1 - lam * ℒ) / 𝒬 →
      ∀ (V : ℕ) (κPrev κ κNext α : Type)
        [Fintype κPrev] [Fintype κ] [Fintype κNext] [Fintype α]
        [DecidableEq κPrev] [DecidableEq κ] [DecidableEq κNext] [DecidableEq α]
        (δPrev : Matrix κ κPrev F) (δ : Matrix κNext κ F)
        (part : κ → α) (partNext : κNext → α) (partPrev : κPrev → α)
        (μc μh εc εh : ℝ) (wF : ℕ),
        0 < V →
        δ * δPrev = 0 →
        (Fintype.card κ : ℝ) = (V : ℝ) * (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
          elementarySymR t (fun i => sIB n m i) (t - k) →
        (V : ℝ) * (Finset.univ.prod fun i : Fin t => (n i : ℝ)) * gammaK t k n m ≤
          (Fintype.card κ : ℝ) - (Matrix.rank δ : ℝ) - (Matrix.rank δPrev : ℝ) →
        0 < Fintype.card κ → 0 < Fintype.card κPrev + Fintype.card κNext →
        (∀ a : α, (Finset.univ.filter fun i : κ => part i = a).card ≤
          (Finset.univ.sup fun i : Fin t => n i) ^ (t - k)) →
        wF = max (2 * (k + 1)) (t - k + 1) *
          (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1) →
        (∀ i : κ, (Finset.univ.filter fun c : κNext => δ c i ≠ 0).card ≤ wF) →
        (∀ c : κNext, (Finset.univ.filter fun i : κ => δ c i ≠ 0).card ≤ wF) →
        (∀ j : κPrev, (Finset.univ.filter fun i : κ => δPrev i j ≠ 0).card ≤ wF) →
        (∀ i : κ, (Finset.univ.filter fun j : κPrev => δPrev i j ≠ 0).card ≤ wF) →
        0 < μc → 0 < μh → 0 < εc → 0 < εh →
        (∀ x : κ → F, δ *ᵥ x = 0 → x ∉ LinearMap.range (Matrix.mulVecLin δPrev) →
          (μc : ℝ) ≤ (blockWeight part x : ℝ)) →
        (∀ y : κ → F, (δPrevᵀ : Matrix κPrev κ F) *ᵥ y = (0 : κPrev → F) →
          y ∉ LinearMap.range (Matrix.mulVecLin (δᵀ : Matrix κ κNext F)) →
          (μh : ℝ) ≤ (blockWeight part y : ℝ)) →
        (∀ x : κ → F,
          (εc : ℝ) *
            ((blockDist part x (LinearMap.ker (Matrix.mulVecLin δ))).toNat : ℝ) ≤
            (blockWeight partNext (δ *ᵥ x) : ℝ)) →
        (∀ y : κ → F,
          (εh : ℝ) *
            ((blockDist part y
              (LinearMap.ker (Matrix.mulVecLin (δPrevᵀ : Matrix κPrev κ F)))).toNat : ℝ) ≤
            (blockWeight partPrev ((δPrevᵀ : Matrix κPrev κ F) *ᵥ y) : ℝ)) →
        ∀ (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)),
          let HX : Matrix (κNext × Fin s) (κ × Fin s) (ZMod 2) := binaryMatrix s e δ
          let HZ : Matrix (κPrev × Fin s) (κ × Fin s) (ZMod 2) :=
            (binaryMatrix s e δPrev)ᵀ
          ∃ (hcompat : HX * HZᵀ = 0),
            let c : CssData (κ × Fin s) (κNext × Fin s) (κPrev × Fin s) :=
              { hX := HX, hZ := HZ, hcompat := hcompat }
            c.numQubits = s * Fintype.card κ ∧
            ((gammaK t k n m /
                (elementarySymR t (fun i => sIB n m i) (t - k) : ℝ)) : ℝ) ≤
              (c.rate : ℝ) ∧
            ((Nat.ceil (min μc μh) : ℕ) : ℕ∞) ≤ cssDistance c ∧
            cssHasSoundnessAtLeast c
              ((Fintype.card κ : ℝ) * min εc εh /
                ((s : ℝ) * (Finset.univ.sup fun i : Fin t => n i : ℕ) ^ (t - k) *
                  ((Fintype.card κPrev + Fintype.card κNext : ℕ) : ℝ))) ∧
            c.checkWeight ≤ s * wF ∧
            c.qubitIncidence ≤ 2 * s * wF := by
  intro t k s n m K ρ lam ℒ 𝒬 F _ _ _ _ _ _ _ _ hs hn hm hK hρ hlam hℒ h𝒬 hΓ hlamℒ hdiv
    V κPrev κ κNext α _ _ _ _ _ _ _ _ δPrev δ part partNext partPrev μc μh εc εh wF
    hV hδ hcardκ hrank hκpos hκpn hM2 hwFeq hwF1 hwF2 hwF3 hwF4 hμc hμh hεc hεh
    hμc' hμh' hεc' hεh' e
  classical
  have hfinrank : Module.finrank (ZMod 2) F = s := by
    rw [e.finrank_eq]
    simp
  have hcardF : Fintype.card F = 2 ^ s := by
    rw [Fintype.card_congr e.toEquiv]
    simp [Fintype.card_pi, ZMod.card]
  obtain ⟨hcompat, hnum, henc, hdist, hsnd, hchk, hinc⟩ :=
    binaryConversionSoundness s F hs hfinrank hcardF
      κPrev κ κNext α δ δPrev hδ part partNext partPrev μc μh εc εh wF
      ((Finset.univ.sup fun i : Fin t => n i) ^ (t - k)) hμc hμh hεc hεh hM2 hκpos hκpn
      hμc' hμh' hεc' hεh' ⟨hwF1, hwF2, hwF3, hwF4⟩ e
  have hσeq : ((s : ℝ) * ((Finset.univ.sup fun i : Fin t => n i : ℕ) : ℝ) ^ (t - k) *
        ((Fintype.card κPrev + Fintype.card κNext : ℕ) : ℝ)) =
      ((s : ℝ) * (((Finset.univ.sup fun i : Fin t => n i) ^ (t - k) : ℕ) : ℝ) *
        ((Fintype.card κPrev : ℝ) + (Fintype.card κNext : ℝ))) := by
    push_cast
    ring
  rw [hσeq]
  refine ⟨hcompat, hnum, ?_, hdist, hsnd, hchk, hinc⟩
  set P := (Finset.univ.prod fun i : Fin t => (n i : ℝ)) with hPdef
  set E := elementarySymR t (fun i => sIB n m i) (t - k) with hEdef
  have hVℝ : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hV
  have hPpos : 0 < P := by
    refine Finset.prod_pos fun i _ => ?_
    exact_mod_cast Nat.lt_of_lt_of_le (by omega) (hn i)
  have hckpos : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast hκpos
  have hEpos : 0 < E := by
    by_contra hE'
    have hle : E ≤ 0 := le_of_not_gt hE'
    have h1 : (V : ℝ) * P * E ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hVℝ.le hPpos.le) hle
    rw [← hcardκ] at h1
    exact absurd h1 (not_le.2 hckpos)
  have hdiffpos : 0 < (Fintype.card κ : ℝ) - (Matrix.rank δ : ℝ) -
      (Matrix.rank δPrev : ℝ) :=
    (mul_pos (mul_pos hVℝ hPpos) hΓ).trans_le hrank
  have hlt : Matrix.rank δ + Matrix.rank δPrev < Fintype.card κ := by
    by_contra hc
    push Not at hc
    have h2 : (Fintype.card κ : ℝ) ≤ (Matrix.rank δ : ℝ) + (Matrix.rank δPrev : ℝ) := by
      exact_mod_cast hc
    linarith
  have hsubcast : ((Fintype.card κ - Matrix.rank δ - Matrix.rank δPrev : ℕ) : ℝ) =
      (Fintype.card κ : ℝ) - (Matrix.rank δ : ℝ) - (Matrix.rank δPrev : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp only [CssData.rate]
  rw [henc, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [hsubcast]
  have hckpos' : 0 < (Fintype.card κ : ℝ) * (s : ℝ) :=
    mul_pos hckpos (by exact_mod_cast hs)
  rw [div_le_div_iff₀ hEpos hckpos']
  calc gammaK t k n m * ((Fintype.card κ : ℝ) * (s : ℝ))
      = ((s : ℝ) * ((V : ℝ) * P * gammaK t k n m)) * E := by
          rw [hcardκ]
          ring
    _ ≤ ((s : ℝ) * ((Fintype.card κ : ℝ) - (Matrix.rank δ : ℝ) - (Matrix.rank δPrev : ℝ))) * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrank (Nat.cast_nonneg s))
            hEpos.le

end Qatlib.Concepts.CodingDecoding.FamilyAssembly
