module

public import BlockBand.Transmission.PassiveCovariance.WordCat

/-!
# The self-energy operator as block traces; the centred self-energy

* `sdiag_eq_selfEnergy`: `S[M] = selfEnergy b ⟨M₁₁⟩ ⟨M₂₂⟩` (`sdiag` is `selfEnergy` at
  the block traces of `M`).
* `selfEnergy_sub`, `selfEnergy_conjTranspose`, `selfEnergy_eq_smul`
  (`= m₁ diag(dOne) + m₂ diag(dTwo)`).
* `blkTr_gSide`: `⟨(𝒢ᴴ)_{qq}⟩ = conj⟨𝒢_{qq}⟩`.
* `sbarSide_eq`: `S̄ = selfEnergy b E⟨𝔊₁₁⟩ E⟨𝔊₂₂⟩` for both sides; hence `S[𝔊] - S̄` is
  `selfEnergy` of the **centred** block traces (`sdiag_sub_sbarSide`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem trace_blkAt (M : LayerMat W) (q : Fin 2) :
    (blkAt M q q).trace = ∑ y, M (siteOf q y) (siteOf q y) := by
  simp [Matrix.trace, blkAt]

theorem siteOf_zero (x : Fin W) : siteOf 0 x = phys x := rfl

theorem siteOf_one (x : Fin W) : siteOf 1 x = port x := by simp [siteOf]

/-- `S[M] = selfEnergy b ⟨M₁₁⟩ ⟨M₂₂⟩`. -/
theorem sdiag_eq_selfEnergy {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (M : LayerMat W) :
    sdiag b M = selfEnergy b (SourceMixing.blkTr M 0) (SourceMixing.blkTr M 1) := by
  have hg' : ((gueVar W b : ℝ≥0) : ℝ) = (1 - 2 * b) / W :=
    Real.coe_toNNReal _ (div_nonneg (by linarith) (Nat.cast_nonneg W))
  have hn' : ((ginVar W b : ℝ≥0) : ℝ) = b / W := Real.coe_toNNReal _ (div_nonneg hb0 (Nat.cast_nonneg W))
  have hg : ((gueVar W b : ℝ≥0) : ℂ) = (W : ℂ)⁻¹ * ((1 - 2 * b : ℝ) : ℂ) := by
    rw [show ((gueVar W b : ℝ≥0) : ℂ) = (((gueVar W b : ℝ≥0) : ℝ) : ℂ) from rfl, hg']
    push_cast; ring
  have hn : ((ginVar W b : ℝ≥0) : ℂ) = (W : ℂ)⁻¹ * (b : ℂ) := by
    rw [show ((ginVar W b : ℝ≥0) : ℂ) = (((ginVar W b : ℝ≥0) : ℝ) : ℂ) from rfl, hn']
    push_cast; ring
  rw [sdiag, selfEnergy]
  congr 1
  funext α
  simp only [SourceMixing.blkTr, trace_blkAt, siteOf_zero, siteOf_one]
  rcases α with ⟨i, x⟩ | ⟨i, x⟩ <;> obtain rfl : i = 0 := Subsingleton.elim i 0
  · rw [show (Sum.inl (0, x) : LayerSite W .oneBlockOnePort) = phys x from rfl, sum_siteVar_phys]
    simp only [Sum.elim_inl, hg, hn, ← Finset.mul_sum]
    ring
  · rw [show (Sum.inr (0, x) : LayerSite W .oneBlockOnePort) = port x from rfl, sum_siteVar_port]
    simp only [Sum.elim_inr, hn, ← Finset.mul_sum]
    ring

theorem selfEnergy_sub (b : ℝ) (m₁ m₂ n₁ n₂ : ℂ) :
    (selfEnergy b m₁ m₂ : LayerMat W) - selfEnergy b n₁ n₂ = selfEnergy b (m₁ - n₁) (m₂ - n₂) := by
  rw [selfEnergy, selfEnergy, selfEnergy]
  rw [diagonal_sub]
  congr 1; funext α; rcases α with α | α <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> ring

theorem selfEnergy_conjTranspose (b : ℝ) (m₁ m₂ : ℂ) :
    (selfEnergy b m₁ m₂ : LayerMat W)ᴴ = selfEnergy b (conj m₁) (conj m₂) := by
  rw [selfEnergy, selfEnergy, diagonal_conjTranspose]
  congr 1; funext α; rcases α with α | α <;> simp

theorem selfEnergy_eq_smul (b : ℝ) (m₁ m₂ : ℂ) :
    (selfEnergy b m₁ m₂ : LayerMat W) =
      m₁ • diagonal (SourceMixing.dOne b) + m₂ • diagonal (SourceMixing.dTwo b) := by
  rw [SourceMixing.selfEnergy_eq, ← diagonal_smul, ← diagonal_smul, diagonal_add]
  congr 1; funext α; simp [mul_comm]

theorem blkTr_conjTranspose (M : LayerMat W) (q : Fin 2) :
    SourceMixing.blkTr Mᴴ q = conj (SourceMixing.blkTr M q) := by
  rw [SourceMixing.blkTr, SourceMixing.blkTr, blkAt_conjTranspose, trace_conjTranspose, map_mul,
    map_inv₀, map_natCast]
  rfl

theorem blkTr_gSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) (q : Fin 2)
    (ω : LayerSample W .oneBlockOnePort) :
    SourceMixing.blkTr (gSide b E X adj ω) q =
      if adj then conj (SourceMixing.blkTr (gRes b E X ω) q) else SourceMixing.blkTr (gRes b E X ω) q := by
  cases adj
  · rfl
  · exact blkTr_conjTranspose _ q

/-- **`S̄` as block-trace means**, both sides. -/
theorem sbarSide_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) :
    sbarSide b E X adj = selfEnergy b
      (∫ ω, SourceMixing.blkTr (gSide b E X adj ω) 0 ∂layerLaw W b .oneBlockOnePort)
      (∫ ω, SourceMixing.blkTr (gSide b E X adj ω) 1 ∂layerLaw W b .oneBlockOnePort) := by
  have hm0 : meanTr b E X 0 = ∫ ω, SourceMixing.blkTr (gRes b E X ω) 0 ∂layerLaw W b .oneBlockOnePort := by
    simp only [meanTr, SourceMixing.trLetter_zero_eq]
  have hm3 : meanTr b E X 3 = ∫ ω, SourceMixing.blkTr (gRes b E X ω) 1 ∂layerLaw W b .oneBlockOnePort := by
    simp only [meanTr, SourceMixing.trLetter_three_eq]
  cases adj
  · show selfEnergy b (meanTr b E X 0) (meanTr b E X 3) = _
    rw [hm0, hm3]; rfl
  · show (selfEnergy b (meanTr b E X 0) (meanTr b E X 3))ᴴ = _
    rw [selfEnergy_conjTranspose, hm0, hm3]
    simp only [blkTr_gSide, ↓reduceIte]
    rw [integral_conj, integral_conj]

/-- **The centred self-energy**: `S[𝔊] - S̄ = selfEnergy b (⟨𝔊₁₁⟩ - E⟨𝔊₁₁⟩) (⟨𝔊₂₂⟩ - E⟨𝔊₂₂⟩)`. -/
theorem sdiag_sub_sbarSide {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) (E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) (ω : LayerSample W .oneBlockOnePort) :
    sdiag b (gSide b E X adj ω) - sbarSide b E X adj = selfEnergy b
      (SourceMixing.blkTr (gSide b E X adj ω) 0 -
        ∫ ω', SourceMixing.blkTr (gSide b E X adj ω') 0 ∂layerLaw W b .oneBlockOnePort)
      (SourceMixing.blkTr (gSide b E X adj ω) 1 -
        ∫ ω', SourceMixing.blkTr (gSide b E X adj ω') 1 ∂layerLaw W b .oneBlockOnePort) := by
  rw [sdiag_eq_selfEnergy hb0 hb, sbarSide_eq, selfEnergy_sub]

end BlockBand.Transmission.PassiveCovariance
