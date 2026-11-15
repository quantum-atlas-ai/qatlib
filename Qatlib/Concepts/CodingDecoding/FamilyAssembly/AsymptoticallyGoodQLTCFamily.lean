/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.FamilyAssembly.AbstractParameterGuarantee

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

open Qatlib.Concepts.CodingDecoding.CssTesters Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.BinaryConversionSoundness
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester


namespace Qatlib.Concepts.CodingDecoding.FamilyAssembly

open Matrix Filter

open scoped Classical BigOperators ENNReal

/-- A CSS soundness guarantee remains valid when its lower bound is decreased. -/
theorem cssHasSoundnessAtLeast_mono' {ι κX κZ : Type*} [Fintype ι] [Fintype κX]
    [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]
    (c : CssData ι κX κZ) {σ σ' : ℝ} (hσ : σ ≤ σ')
    (h : cssHasSoundnessAtLeast c σ') : cssHasSoundnessAtLeast c σ := by
  classical
  rw [cssHasSoundnessAtLeast_iff] at h ⊢
  intro η
  refine le_trans ?_ (h η)
  have hnn : (0 : ℝ) ≤ ((cssSyndromeWeight c η.1 η.2).toNat : ℝ) :=
    Nat.cast_nonneg _
  by_cases hN : Fintype.card ι = 0
  · simp [hN]
  · have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
      have hcard := Nat.pos_of_ne_zero hN
      exact_mod_cast hcard
    have hd : σ / (Fintype.card ι : ℝ) ≤ σ' / (Fintype.card ι : ℝ) := by
      rw [div_le_div_iff₀ hNpos hNpos]
      exact mul_le_mul_of_nonneg_right hσ (le_of_lt hNpos)
    exact mul_le_mul_of_nonneg_right hd hnn

/-- Compatible check matrices whose rank sum is below the number of coordinates admit a
nontrivial logical vector in the stated kernel modulo range. -/
theorem exists_logical_of_rank_add_lt {ι κX κZ : Type*} [Fintype ι] [Fintype κX]
    [Fintype κZ] {hX : Matrix κX ι (ZMod 2)} {hZ : Matrix κZ ι (ZMod 2)}
    (hcompat : hX * hZᵀ = 0) (h : Matrix.rank hX + Matrix.rank hZ < Fintype.card ι) :
    ∃ z : ι → ZMod 2, hX *ᵥ z = 0 ∧ z ∉ LinearMap.range (Matrix.mulVecLin hZᵀ) := by
  classical
  have hsub : LinearMap.range (Matrix.mulVecLin hZᵀ) ≤
      LinearMap.ker (Matrix.mulVecLin hX) := by
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    rw [Matrix.mulVecLin_apply] at hy
    rw [← hy, Matrix.mulVec_mulVec, hcompat, Matrix.zero_mulVec]
  have hfrX : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin hX))
      = Matrix.rank hX := rfl
  have hfrZ' : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin hZᵀ))
      = Matrix.rank hZ := by
    have h1 : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin hZᵀ))
        = Matrix.rank (hZᵀ) := rfl
    rw [h1, Matrix.rank_transpose]
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin hX))
      = Fintype.card ι - Matrix.rank hX := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin hX)
    rw [Module.finrank_fintype_fun_eq_card, hfrX] at hrk
    omega
  have hne : LinearMap.range (Matrix.mulVecLin hZᵀ) ≠
      LinearMap.ker (Matrix.mulVecLin hX) := by
    intro heq
    rw [← heq, hfrZ'] at hker
    omega
  obtain ⟨z, hzk, hzr⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hsub hne)
  refine ⟨z, ?_, hzr⟩
  rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hzk

/-- A CSS code with positive rate has finite distance. -/
theorem cssDistance_lt_top_of_pos_rate {ι κX κZ : Type*} [Fintype ι] [Fintype κX]
    [Fintype κZ] [DecidableEq ι] (c : CssData ι κX κZ)
    (h : (0 : ℝ) < ((c.rate : ℚ) : ℝ)) : cssDistance c < ⊤ := by
  classical
  have hEpos : 0 < c.encodedQubits := by
    by_contra hcon
    push Not at hcon
    have hE0 : c.encodedQubits = 0 := by omega
    have h0 : ((c.rate : ℚ) : ℝ) = 0 := by
      unfold CssData.rate
      simp [hE0]
    rw [h0] at h
    exact absurd h (by norm_num)
  have hrk := cssRank_add_le c
  have hlt : Matrix.rank c.hX + Matrix.rank c.hZ < Fintype.card ι := by
    have hE1 : 1 ≤ c.encodedQubits := by omega
    unfold CssData.encodedQubits at hE1
    omega
  have hcompat' : c.hZ * c.hXᵀ = 0 := by
    have ht := congrArg Matrix.transpose c.hcompat
    simpa [Matrix.transpose_mul] using ht
  obtain ⟨z, hz1, hz2⟩ := exists_logical_of_rank_add_lt c.hcompat hlt
  obtain ⟨x, hx1, hx2⟩ := exists_logical_of_rank_add_lt hcompat' (by omega)
  have hmem : (bitWeight z : ℕ∞) ∈
      {w : ℕ∞ | ∃ z : ι → ZMod 2, c.hX *ᵥ z = 0 ∧
        z ∉ LinearMap.range (Matrix.mulVecLin c.hZᵀ) ∧ (bitWeight z : ℕ∞) = w} :=
    Set.mem_ofPred_eq.mpr ⟨z, hz1, hz2, rfl⟩
  exact lt_of_le_of_lt
    (le_trans (min_le_left _ _) (sInf_le hmem)) (ENat.natCast_lt_top _)

/-- Binary conversion of consecutive differentials with zero product gives compatible CSS check
matrices. -/
private theorem compatAt {κPrev κ κNext : Type} [Fintype κPrev] [Fintype κ]
    [Fintype κNext] [DecidableEq κPrev] [DecidableEq κ] [DecidableEq κNext]
    {F : Type} [Field F] [Algebra (ZMod 2) F] [Module.Free (ZMod 2) F] [Fintype F]
    [Module.Finite (ZMod 2) F] {s : ℕ} (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2))
    (δPrev : Matrix κ κPrev F) (δ : Matrix κNext κ F)
    (hδ : δ * δPrev = 0) :
    (binaryMatrix s e δ) * ((binaryMatrix s e δPrev)ᵀ)ᵀ = 0 := by
  rw [Matrix.transpose_transpose]
  exact binaryMatrix_mul_eq_zero e δ δPrev hδ

/-- The binary CSS construction has soundness at least any value below the stated converted
soundness bound. -/
private theorem soundnessStep
    (t k s : ℕ) (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ) (K ρ lam ℒ 𝒬 : ℝ)
    (F : Type) (hF : Field F) (hFA : Algebra (ZMod 2) F)
    (hFFree : Module.Free (ZMod 2) F) (hFFin : Fintype F)
    (hFMod : Module.Finite (ZMod 2) F)
    (ht : 4 ≤ t) (h2k : 2 ≤ k) (hkt : k + 2 ≤ t) (hs : 0 < s)
    (hn : ∀ i : Fin t, 2 ≤ n i) (hm : ∀ i : Fin t, ∀ b : Fin 2, 0 < m i b ∧ m i b < n i)
    (hK : 1 ≤ K) (hρ : 0 < ρ ∧ ρ ≤ 1) (hlam : 0 ≤ lam ∧ lam < 1) (hℒ : 0 < ℒ)
    (h𝒬 : 0 < 𝒬) (hΓ : 0 < gammaK t k n m) (hlamℒ : lam * ℒ < 1)
    (hdiv : 0 < (1 - lam * ℒ) / 𝒬)
    (Vν : ℕ) (κP κ κN α : Type)
    [FP : Fintype κP] [FM : Fintype κ] [FN : Fintype κN] [FA : Fintype α]
    [DP : DecidableEq κP] [DM : DecidableEq κ] [DN : DecidableEq κN]
    [DA : DecidableEq α]
    (δP : Matrix κ κP F) (δ : Matrix κN κ F) (part : κ → α) (pN : κN → α)
    (pP : κP → α) (μc μh εc εh : ℝ) (wF : ℕ)
    (hV : 0 < Vν) (hδ : δ * δP = 0)
    (hcard : (Fintype.card κ : ℝ) = (Vν : ℝ) *
      (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
        elementarySymR t (fun i => sIB n m i) (t - k))
    (hrank : (Vν : ℝ) * (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
        gammaK t k n m ≤
      (Fintype.card κ : ℝ) - (Matrix.rank δ : ℝ) - (Matrix.rank δP : ℝ))
    (hκpos : 0 < Fintype.card κ) (hκpn : 0 < Fintype.card κP + Fintype.card κN)
    (hM2 : ∀ a : α, (Finset.univ.filter fun i : κ => part i = a).card ≤
      (Finset.univ.sup fun i : Fin t => n i) ^ (t - k))
    (hwF : wF = max (2 * (k + 1)) (t - k + 1) *
      (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1))
    (hwF1 : ∀ i : κ, (Finset.univ.filter fun c : κN => δ c i ≠ 0).card ≤ wF)
    (hwF2 : ∀ c : κN, (Finset.univ.filter fun i : κ => δ c i ≠ 0).card ≤ wF)
    (hwF3 : ∀ j : κP, (Finset.univ.filter fun i : κ => δP i j ≠ 0).card ≤ wF)
    (hwF4 : ∀ i : κ, (Finset.univ.filter fun j : κP => δP i j ≠ 0).card ≤ wF)
    (hμc : 0 < μc) (hμh : 0 < μh) (hεc : 0 < εc) (hεh : 0 < εh)
    (hμc' : ∀ x : κ → F, δ *ᵥ x = 0 → x ∉ LinearMap.range (Matrix.mulVecLin δP) →
      (μc : ℝ) ≤ (blockWeight part x : ℝ))
    (hμh' : ∀ y : κ → F, (δPᵀ : Matrix κP κ F) *ᵥ y = (0 : κP → F) →
      y ∉ LinearMap.range (Matrix.mulVecLin (δᵀ : Matrix κ κN F)) →
      (μh : ℝ) ≤ (blockWeight part y : ℝ))
    (hεc' : ∀ x : κ → F,
      (εc : ℝ) *
        ((blockDist part x (LinearMap.ker (Matrix.mulVecLin δ))).toNat : ℝ) ≤
      (blockWeight pN (δ *ᵥ x) : ℝ))
    (hεh' : ∀ y : κ → F,
      (εh : ℝ) *
        ((blockDist part y (LinearMap.ker (Matrix.mulVecLin (δPᵀ : Matrix κP κ F)))).toNat : ℝ) ≤
      (blockWeight pP ((δPᵀ : Matrix κP κ F) *ᵥ y) : ℝ))
    (e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (σ₀ : ℝ)
    (hσ : σ₀ ≤ (Fintype.card κ : ℝ) * min εc εh /
      ((s : ℝ) * (Finset.univ.sup fun i : Fin t => n i : ℕ) ^ (t - k) *
        ((Fintype.card κP + Fintype.card κN : ℕ) : ℝ))) :
    @cssHasSoundnessAtLeast (κ × Fin s) (κN × Fin s) (κP × Fin s)
      (@instFintypeProd κ (Fin s) FM (Fin.fintype s))
      (@instFintypeProd κN (Fin s) FN (Fin.fintype s))
      (@instFintypeProd κP (Fin s) FP (Fin.fintype s))
      (fun a b => @instDecidableEqProd κ (Fin s) DM (instDecidableEqFin s) a b)
      (fun a b => @instDecidableEqProd κN (Fin s) DN (instDecidableEqFin s) a b)
      (fun a b => @instDecidableEqProd κP (Fin s) DP (instDecidableEqFin s) a b)
      (@CssData.mk (κ × Fin s) (κN × Fin s) (κP × Fin s)
        (@instFintypeProd κ (Fin s) FM (Fin.fintype s))
        (binaryMatrix s e δ) ((binaryMatrix s e δP)ᵀ)
        (@compatAt κP κ κN FP FM FN DP DM DN F hF hFA hFFree hFFin hFMod s e
          δP δ hδ)) σ₀ := by
  let Fιv : Fintype (κ × Fin s) :=
    @instFintypeProd κ (Fin s) FM (Fin.fintype s)
  let FκXv : Fintype (κN × Fin s) :=
    @instFintypeProd κN (Fin s) FN (Fin.fintype s)
  let FκZv : Fintype (κP × Fin s) :=
    @instFintypeProd κP (Fin s) FP (Fin.fintype s)
  let Dιv : DecidableEq (κ × Fin s) :=
    fun a b => @instDecidableEqProd κ (Fin s) DM (instDecidableEqFin s) a b
  obtain ⟨hcompν, hnum, hrate, hdist, hsnd, hcw, hqi⟩ :=
    @abstractParameterGuarantee t k s n m K ρ lam ℒ 𝒬 F hF hFA hFFree hFFin hFMod
      ht h2k hkt hs hn hm hK hρ hlam hℒ h𝒬 hΓ hlamℒ hdiv
      Vν κP κ κN α FP FM FN FA DP DM DN DA δP δ part pN pP μc μh εc εh wF
      hV hδ hcard hrank hκpos hκpn hM2 hwF hwF1 hwF2 hwF3 hwF4
      hμc hμh hεc hεh hμc' hμh' hεc' hεh' e
  obtain ⟨c₄, hc₄⟩ :
      ∃ c₄ : CssData (κ × Fin s) (κN × Fin s) (κP × Fin s),
        c₄ = (@CssData.mk (κ × Fin s) (κN × Fin s) (κP × Fin s)
          (@instFintypeProd κ (Fin s) FM (Fin.fintype s))
          (binaryMatrix s e δ) ((binaryMatrix s e δP)ᵀ) hcompν) :=
    ⟨_, rfl⟩
  rw [← hc₄] at hsnd
  have hceq2 :
      (@CssData.mk (κ × Fin s) (κN × Fin s) (κP × Fin s)
        (@instFintypeProd κ (Fin s) FM (Fin.fintype s))
        (binaryMatrix s e δ) ((binaryMatrix s e δP)ᵀ)
        (@compatAt κP κ κN FP FM FN DP DM DN F hF hFA hFFree hFFin hFMod s e
          δP δ hδ)) = c₄ := by
    rw [hc₄]
  rw [hceq2]
  exact cssHasSoundnessAtLeast_mono' c₄ hσ hsnd

set_option maxHeartbeats 1000000 in

/-- A growing family of chain complexes satisfying the stated uniform parameter bounds yields
CSS codes with positive rate, relative distance, and soundness and uniformly bounded
locality. -/
theorem asymptoticallyGoodQLTCFamily :
    ∀ (t k : ℕ), 4 ≤ t → 2 ≤ k → k + 2 ≤ t →
    ∀ (s : ℕ) (n : Fin t → ℕ) (m : Fin t → Fin 2 → ℕ)
      (K ρ lam ℒ 𝒬 : ℝ) (F : Type)
      [Field F] [Algebra (ZMod 2) F] [Module.Free (ZMod 2) F]
      [Fintype F] [Module.Finite (ZMod 2) F],
      0 < s →
      (∀ i : Fin t, 2 ≤ n i) → (∀ i : Fin t, ∀ b : Fin 2, 0 < m i b ∧ m i b < n i) →
      1 ≤ K → 0 < ρ ∧ ρ ≤ 1 → 0 ≤ lam ∧ lam < 1 → 0 < ℒ → 0 < 𝒬 →
      0 < gammaK t k n m → lam * ℒ < 1 → 0 < (1 - lam * ℒ) / 𝒬 →
      ∀ (_e : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V : ℕ → ℕ),
      StrictMono V → Tendsto V atTop atTop →
      ∀ (A : ℕ), 0 < A →
        ((A : ℝ) = (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
            elementarySymR t (fun i => sIB n m i) (t - k)) →
        ∀ (Δ₀ σ₀ : ℝ), 0 < Δ₀ → 0 < σ₀ →
          (∀ ν : ℕ,
            ∃ (κPrev κ κNext α : Type)
              (Fprev : Fintype κPrev) (Fmid : Fintype κ) (Fnext : Fintype κNext)
              (Fα : Fintype α)
              (Dprev : DecidableEq κPrev) (Dmid : DecidableEq κ)
              (Dnext : DecidableEq κNext) (Dα : DecidableEq α)
              (δPrev : Matrix κ κPrev F) (δ : Matrix κNext κ F)
              (part : κ → α) (partNext : κNext → α) (partPrev : κPrev → α)
              (μc μh εc εh : ℝ) (wF : ℕ),
            letI := Fprev; letI := Fmid; letI := Fnext; letI := Fα
            letI := Dprev; letI := Dmid; letI := Dnext; letI := Dα
            Fintype.card κ = V ν * A ∧
              δ * δPrev = 0 ∧
              (V ν : ℝ) * (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
                  gammaK t k n m ≤
                (Fintype.card κ : ℝ) - (Matrix.rank δ : ℝ) - (Matrix.rank δPrev : ℝ) ∧
              0 < Fintype.card κ ∧ 0 < Fintype.card κPrev + Fintype.card κNext ∧
              (∀ a : α, (Finset.univ.filter fun i : κ => part i = a).card ≤
                (Finset.univ.sup fun i : Fin t => n i) ^ (t - k)) ∧
              wF = max (2 * (k + 1)) (t - k + 1) *
                (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1) ∧
              (∀ i : κ, (Finset.univ.filter fun c : κNext => δ c i ≠ 0).card ≤ wF) ∧
              (∀ c : κNext, (Finset.univ.filter fun i : κ => δ c i ≠ 0).card ≤ wF) ∧
              (∀ j : κPrev, (Finset.univ.filter fun i : κ => δPrev i j ≠ 0).card ≤ wF) ∧
              (∀ i : κ, (Finset.univ.filter fun j : κPrev => δPrev i j ≠ 0).card ≤ wF) ∧
              0 < μc ∧ 0 < μh ∧ 0 < εc ∧ 0 < εh ∧
              (∀ x : κ → F, δ *ᵥ x = 0 → x ∉ LinearMap.range (Matrix.mulVecLin δPrev) →
                (μc : ℝ) ≤ (blockWeight part x : ℝ)) ∧
              (∀ y : κ → F, (δPrevᵀ : Matrix κPrev κ F) *ᵥ y = (0 : κPrev → F) →
                y ∉ LinearMap.range (Matrix.mulVecLin (δᵀ : Matrix κ κNext F)) →
                (μh : ℝ) ≤ (blockWeight part y : ℝ)) ∧
              (∀ x : κ → F,
                (εc : ℝ) *
                  ((blockDist part x (LinearMap.ker (Matrix.mulVecLin δ))).toNat : ℝ) ≤
                  (blockWeight partNext (δ *ᵥ x) : ℝ)) ∧
              (∀ y : κ → F,
                (εh : ℝ) *
                  ((blockDist part y
                    (LinearMap.ker (Matrix.mulVecLin (δPrevᵀ : Matrix κPrev κ F)))).toNat : ℝ) ≤
                (blockWeight partPrev ((δPrevᵀ : Matrix κPrev κ F) *ᵥ y) : ℝ)) ∧
              (Δ₀ * ((s * Fintype.card κ : ℕ) : ℝ) ≤ min μc μh) ∧
              (σ₀ ≤ (Fintype.card κ : ℝ) * min εc εh /
                ((s : ℝ) * (Finset.univ.sup fun i : Fin t => n i : ℕ) ^ (t - k) *
                  ((Fintype.card κPrev + Fintype.card κNext : ℕ) : ℝ)))) →
        ∃ (R Δ σ : ℝ) (w : ℕ), 0 < R ∧ 0 < Δ ∧ 0 < σ ∧
          ∃ (N : ℕ → ℕ) (ι κX κZ : ℕ → Type)
            (Fι : ∀ ν, Fintype (ι ν)) (FκX : ∀ ν, Fintype (κX ν)) (FκZ : ∀ ν, Fintype (κZ ν))
            (Dι : ∀ ν, DecidableEq (ι ν)) (DκX : ∀ ν, DecidableEq (κX ν))
            (DκZ : ∀ ν, DecidableEq (κZ ν))
            (c : ∀ ν, CssData (ι ν) (κX ν) (κZ ν)),
            StrictMono N ∧ Tendsto N atTop atTop ∧
            ∀ ν, letI := Fι ν; letI := FκX ν; letI := FκZ ν
              letI := Dι ν; letI := DκX ν; letI := DκZ ν
              Fintype.card (ι ν) = N ν ∧
              R ≤ ((c ν).rate : ℝ) ∧
              (Δ * (N ν : ℝ)) ≤ ((cssDistance (c ν)).toNat : ℝ) ∧
              cssHasSoundnessAtLeast (c ν) σ ∧
              (c ν).checkWeight ≤ w ∧
              (c ν).qubitIncidence ≤ w := by
  intro t k ht h2k hkt s n m K ρ lam ℒ 𝒬 F hF hFA hFFree hFFin hFMod
    hs hn hm hK hρ hlam hℒ h𝒬 hΓ hlamℒ hdiv e V hVmono hVtend A hA hAe Δ₀ σ₀ hΔ₀ hσ₀ hfam
  classical
  choose κP κ κN α FP FM FN FA DP DM DN DA δP δ part pN pP μc μh εc εh wF
    hcard hδ hrank hκpos hκpn hM2 hwF hwF1 hwF2 hwF3 hwF4 hμc hμh hεc hεh
    hμc' hμh' hεc' hεh' hΔsys hσsnd using hfam
  obtain ⟨f, hfmono, hfVmono⟩ := strictMono_subseq_of_tendsto_atTop hVtend

  have hprodpos : (0 : ℝ) < Finset.univ.prod fun i : Fin t => (n i : ℝ) := by
    refine Finset.prod_pos fun i _ => ?_
    have h1 : (0 : ℕ) < n i := by
      have := hn i
      omega
    exact_mod_cast h1
  have heSRpos : (0 : ℝ) < elementarySymR t (fun i => sIB n m i) (t - k) := by
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    by_contra hcon
    push Not at hcon
    have hnonpos : (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
        elementarySymR t (fun i => sIB n m i) (t - k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hprodpos.le hcon
    rw [← hAe] at hnonpos
    linarith
  have hcardf : ∀ ν, @Fintype.card (κ (f ν)) (FM (f ν)) = V (f ν) * A := fun ν => hcard (f ν)
  have hVpos : ∀ ν, 0 < V (f ν) := by
    intro ν
    by_contra hcon
    push Not at hcon
    have hV0 : V (f ν) = 0 := by omega
    have hc := hcardf ν
    rw [hV0, Nat.zero_mul] at hc
    have hp := hκpos (f ν)
    omega
  have hdimℝ : ∀ ν, ((@Fintype.card (κ (f ν)) (FM (f ν)) : ℕ) : ℝ) =
      (V (f ν) : ℝ) * (Finset.univ.prod fun i : Fin t => (n i : ℝ)) *
        elementarySymR t (fun i => sIB n m i) (t - k) := by
    intro ν
    rw [hcardf ν, Nat.cast_mul, hAe, mul_assoc]
  refine ⟨gammaK t k n m / elementarySymR t (fun i => sIB n m i) (t - k), Δ₀, σ₀,
    2 * s * (max (2 * (k + 1)) (t - k + 1) *
      (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1)),
    div_pos hΓ heSRpos, hΔ₀, hσ₀, ?_⟩
  refine ⟨fun ν => s * @Fintype.card (κ (f ν)) (FM (f ν)),
    fun ν => κ (f ν) × Fin s,
    fun ν => κN (f ν) × Fin s,
    fun ν => κP (f ν) × Fin s,
    fun ν => @instFintypeProd (κ (f ν)) (Fin s) (FM (f ν))
      (Fin.fintype s),
    fun ν => @instFintypeProd (κN (f ν)) (Fin s) (FN (f ν))
      (Fin.fintype s),
    fun ν => @instFintypeProd (κP (f ν)) (Fin s) (FP (f ν))
      (Fin.fintype s),
    fun ν a b => @instDecidableEqProd (κ (f ν)) (Fin s) (DM (f ν))
      (instDecidableEqFin s) a b,
    fun ν a b => @instDecidableEqProd (κN (f ν)) (Fin s) (DN (f ν))
      (instDecidableEqFin s) a b,
    fun ν a b => @instDecidableEqProd (κP (f ν)) (Fin s) (DP (f ν))
      (instDecidableEqFin s) a b,
    fun ν => @CssData.mk (κ (f ν) × Fin s) (κN (f ν) × Fin s) (κP (f ν) × Fin s)
      (@instFintypeProd (κ (f ν)) (Fin s) (FM (f ν))
        (Fin.fintype s))
      (binaryMatrix s e (δ (f ν))) ((binaryMatrix s e (δP (f ν)))ᵀ)
      (@compatAt (κP (f ν)) (κ (f ν)) (κN (f ν)) (FP (f ν)) (FM (f ν)) (FN (f ν))
        (DP (f ν)) (DM (f ν)) (DN (f ν)) F hF hFA hFFree hFFin hFMod s e
        (δP (f ν)) (δ (f ν)) (hδ (f ν))),
    ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : f a < f b := hfmono hab
    have h2 : V (f a) < V (f b) := hfVmono hab
    have h3 : V (f a) * A < V (f b) * A := Nat.mul_lt_mul_of_pos_right h2 hA
    show s * @Fintype.card (κ (f a)) (FM (f a)) <
      s * @Fintype.card (κ (f b)) (FM (f b))
    rw [hcardf a, hcardf b]
    exact Nat.mul_lt_mul_of_pos_left h3 hs
  · have hle : ∀ ν : ℕ, ν ≤ V (f ν) := by
      intro ν
      induction ν with
      | zero => exact Nat.zero_le _
      | succ j ih =>
        have h1 : j < j + 1 := Nat.lt_succ_self j
        have h3 : V (f j) < V (f (j + 1)) := hfVmono h1
        omega
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a ha => ?_⟩
    have h1 := hle a
    have h2 : V (f a) ≤ V (f a) * A := Nat.le_mul_of_pos_right _ hA
    have h3 : V (f a) * A ≤ s * (V (f a) * A) := Nat.le_mul_of_pos_left _ hs
    show b ≤ s * @Fintype.card (κ (f a)) (FM (f a))
    rw [hcardf a]
    omega
  · intro ν
    let Fιv : Fintype (κ (f ν) × Fin s) :=
      @instFintypeProd (κ (f ν)) (Fin s) (FM (f ν)) (Fin.fintype s)
    let FκXv : Fintype (κN (f ν) × Fin s) :=
      @instFintypeProd (κN (f ν)) (Fin s) (FN (f ν)) (Fin.fintype s)
    let FκZv : Fintype (κP (f ν) × Fin s) :=
      @instFintypeProd (κP (f ν)) (Fin s) (FP (f ν)) (Fin.fintype s)
    let Dιv : DecidableEq (κ (f ν) × Fin s) :=
      fun a b => @instDecidableEqProd (κ (f ν)) (Fin s) (DM (f ν))
        (instDecidableEqFin s) a b
    obtain ⟨hcompν, hnum, hrate, hdist, hsnd, hcw, hqi⟩ :=
      @abstractParameterGuarantee t k s n m K ρ lam ℒ 𝒬 F hF hFA hFFree hFFin hFMod
        ht h2k hkt hs hn hm hK hρ hlam hℒ h𝒬 hΓ hlamℒ hdiv
        (V (f ν)) (κP (f ν)) (κ (f ν)) (κN (f ν)) (α (f ν))
        (FP (f ν)) (FM (f ν)) (FN (f ν)) (FA (f ν))
        (DP (f ν)) (DM (f ν)) (DN (f ν)) (DA (f ν))
        (δP (f ν)) (δ (f ν)) (part (f ν)) (pN (f ν)) (pP (f ν))
        (μc (f ν)) (μh (f ν)) (εc (f ν)) (εh (f ν)) (wF (f ν))
        (hVpos ν) (hδ (f ν)) (hdimℝ ν) (hrank (f ν)) (hκpos (f ν)) (hκpn (f ν))
        (hM2 (f ν)) (hwF (f ν)) (hwF1 (f ν)) (hwF2 (f ν)) (hwF3 (f ν)) (hwF4 (f ν))
        (hμc (f ν)) (hμh (f ν)) (hεc (f ν)) (hεh (f ν))
        (hμc' (f ν)) (hμh' (f ν)) (hεc' (f ν)) (hεh' (f ν)) e
    obtain ⟨c₄, hc₄⟩ :
        ∃ c₄ : CssData (κ (f ν) × Fin s) (κN (f ν) × Fin s) (κP (f ν) × Fin s),
          c₄ = (@CssData.mk (κ (f ν) × Fin s) (κN (f ν) × Fin s) (κP (f ν) × Fin s)
            (@instFintypeProd (κ (f ν)) (Fin s) (FM (f ν))
              (Fin.fintype s))
            (binaryMatrix s e (δ (f ν))) ((binaryMatrix s e (δP (f ν)))ᵀ) hcompν) :=
      ⟨_, rfl⟩
    rw [← hc₄] at hnum hrate hdist hsnd hcw hqi
    have hceq2 :
        (@CssData.mk (κ (f ν) × Fin s) (κN (f ν) × Fin s) (κP (f ν) × Fin s)
          (@instFintypeProd (κ (f ν)) (Fin s) (FM (f ν))
            (Fin.fintype s))
          (binaryMatrix s e (δ (f ν))) ((binaryMatrix s e (δP (f ν)))ᵀ)
          (@compatAt (κP (f ν)) (κ (f ν)) (κN (f ν)) (FP (f ν)) (FM (f ν)) (FN (f ν))
            (DP (f ν)) (DM (f ν)) (DN (f ν)) F hF hFA hFFree hFFin hFMod s e
            (δP (f ν)) (δ (f ν)) (hδ (f ν)))) = c₄ := by
      rw [hc₄]
    simp only []
    rw [hceq2]
    rw [hwF (f ν)] at hcw hqi
    refine ⟨hnum, hrate, ?_, ?_, ?_, hqi⟩
    · have hRpos : (0 : ℝ) <
          gammaK t k n m / elementarySymR t (fun i => sIB n m i) (t - k) :=
        div_pos hΓ heSRpos
      have hfin := cssDistance_lt_top_of_pos_rate c₄
        (by exact lt_of_lt_of_le hRpos hrate)
      have htoNat : ((cssDistance c₄).toNat : ℕ∞) = cssDistance c₄ :=
        ENat.natCast_toNat hfin.ne
      have hceil : Nat.ceil (min (μc (f ν)) (μh (f ν))) ≤
          (cssDistance c₄).toNat := by
        rw [← htoNat] at hdist
        exact ENat.natCast_le_natCast.mp hdist
      have hmin : Δ₀ * ((s * @Fintype.card (κ (f ν)) (FM (f ν)) : ℕ) : ℝ) ≤
          min (μc (f ν)) (μh (f ν)) := hΔsys (f ν)
      have hs2 : (min (μc (f ν)) (μh (f ν)) : ℝ) ≤
          ((Nat.ceil (min (μc (f ν)) (μh (f ν))) : ℕ) : ℝ) :=
        Nat.le_ceil _
      have hs3 : ((Nat.ceil (min (μc (f ν)) (μh (f ν))) : ℕ) : ℝ) ≤
          (((cssDistance c₄).toNat : ℕ) : ℝ) :=
        Nat.cast_le.mpr hceil
      exact le_trans (le_trans hmin hs2) hs3
    · rw [← hceq2]
      exact @soundnessStep t k s n m K ρ lam ℒ 𝒬 F hF hFA hFFree hFFin hFMod
        ht h2k hkt hs hn hm hK hρ hlam hℒ h𝒬 hΓ hlamℒ hdiv
        (V (f ν)) (κP (f ν)) (κ (f ν)) (κN (f ν)) (α (f ν))
        (FP (f ν)) (FM (f ν)) (FN (f ν)) (FA (f ν))
        (DP (f ν)) (DM (f ν)) (DN (f ν)) (DA (f ν))
        (δP (f ν)) (δ (f ν)) (part (f ν)) (pN (f ν)) (pP (f ν))
        (μc (f ν)) (μh (f ν)) (εc (f ν)) (εh (f ν)) (wF (f ν))
        (hVpos ν) (hδ (f ν)) (hdimℝ ν) (hrank (f ν)) (hκpos (f ν)) (hκpn (f ν))
        (hM2 (f ν)) (hwF (f ν)) (hwF1 (f ν)) (hwF2 (f ν)) (hwF3 (f ν)) (hwF4 (f ν))
        (hμc (f ν)) (hμh (f ν)) (hεc (f ν)) (hεh (f ν))
        (hμc' (f ν)) (hμh' (f ν)) (hεc' (f ν)) (hεh' (f ν))
        e σ₀ (hσsnd (f ν))
    · have h2s : s * (max (2 * (k + 1)) (t - k + 1) *
          (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1)) ≤
          2 * s * (max (2 * (k + 1)) (t - k + 1) *
            (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1)) := by
        have hle1 : s * (max (2 * (k + 1)) (t - k + 1) *
            (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1)) ≤
            2 * (s * (max (2 * (k + 1)) (t - k + 1) *
              (Finset.univ.sup fun i : Fin t => n i) ^ (t - k + 1))) :=
          Nat.le_mul_of_pos_left _ two_pos
        exact hle1.trans_eq (Nat.mul_assoc _ _ _).symm
      exact le_trans hcw h2s

end Qatlib.Concepts.CodingDecoding.FamilyAssembly
