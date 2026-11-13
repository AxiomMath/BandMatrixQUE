module

public import BlockBand.SourceProcess.ContractingWords.IdProjFluct

/-!
# `SepFluctIdProj` and the word step from the contracting separators only

The fluctuation bound for the separators `σ = I` and `σ = P` holds, so the word step needs only
the bounds for the contracting separators.

* **`sepFluctIdProj_holds hGA hLp : SepFluctIdProj`**;
* **`wordStepMean_of'`**, **`wordStepFluct_of'`**: `wordStepMean_of`/`wordStepFluct_of` with
  `SepMeanIdProj`, `SepFluctIdProj` discharged; the other hypotheses are
  `SeparatorMeanUniform` and `SeparatorFluctUniform` (proved as
  `CompleteSourceGapBulk.separatorMeanUniform_holds` and
  `CompleteSourceGapBulk.separatorFluctUniform_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem arith_le {c Ct s m a b a' b' : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ m) (ha' : 0 ≤ a')
    (hb' : 0 ≤ b') (ha : a' ≤ a) (hb : b' ≤ b) (hc : c ≤ Ct) (hCt : 0 ≤ Ct) :
    c * s * a' * b' ≤ Ct * (s + m) * a * b := by
  have h1 : c * s * a' * b' ≤ Ct * s * a' * b' := by
    have := mul_nonneg (mul_nonneg hs ha') hb'
    nlinarith
  have h2 : Ct * s * a' * b' ≤ Ct * s * a * b := by
    have := mul_nonneg hCt hs
    have h3 : a' * b' ≤ a * b := mul_le_mul ha hb hb' (ha'.trans ha)
    nlinarith
  have h4 : Ct * s * a * b ≤ Ct * (s + m) * a * b := by
    have := mul_nonneg (mul_nonneg hCt hm) (mul_nonneg (ha'.trans ha) (hb'.trans hb))
    nlinarith
  linarith

theorem arith_off {K d m Ct s a b : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hdm : d ≤ m) (hKt : K / d ≤ Ct)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) : K * a * b ≤ Ct * (s + m) * a * b := by
  have h1 : K ≤ Ct * m := by
    have : K = K / d * d := by field_simp
    rw [this]
    exact mul_le_mul hKt hdm hd.le ((div_nonneg hK hd.le).trans hKt)
  have hCt : 0 ≤ Ct := (div_nonneg hK hd.le).trans hKt
  have h2 : Ct * m ≤ Ct * (s + m) := mul_le_mul_of_nonneg_left (by linarith) hCt
  have hab := mul_nonneg ha hb
  nlinarith

/-- **`SepFluctIdProj`** from the input hypotheses. -/
theorem sepFluctIdProj_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    SepFluctIdProj := by
  intro b hb0 hb κ hκ Q hQ
  obtain ⟨d₀, hd₀, hFS⟩ := (FullSource.fullSourceEstimates_holds hGA hLp).fluct b hb0 hb κ hκ
  obtain ⟨C₁, W₁, hC₁⟩ := hFS Q hQ
  obtain ⟨K, W₂, hK, hKb⟩ := crude_fluct hGA hb0 hb hκ hQ
  obtain ⟨C₂, W₃, hC₂⟩ :=
    (BlockBand.Transmission.PassiveLayer.passiveBounds_holds hGA hLp).bilinear b hb0 hb κ hκ Q hQ
  obtain ⟨μ, W₄, -, hB⟩ := fresh_basic hGA hb0 hb hκ
  have hm0 : 0 < min 1 d₀ := lt_min one_pos hd₀
  set Ct := max C₁ 0 + K / min 1 d₀ + max C₂ 0
  have hKd : 0 ≤ K / min 1 d₀ := div_nonneg hK hm0.le
  have hCt : 0 ≤ Ct := by positivity
  refine ⟨Ct, max (max W₁ W₂) (max W₃ (max W₄ 1)), hCt, fun W hW E hE XX hXX σ hσ u v => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW₃, hW₄, hW1⟩ := hW
  set δ := jetDistance0 b E (nearSchur (boundaryZ b E) XX)
  have hδ : 0 ≤ δ := norm_nonneg _
  have hm : 0 ≤ min 1 δ := le_min zero_le_one hδ
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hs : 0 ≤ 1 / Real.sqrt W := by positivity
  have hu := vecNorm_nonneg u
  have hv := vecNorm_nonneg v
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · -- `σ = I`
    by_cases hδd : δ ≤ d₀
    · have e : (fun ω => bilinear u (transportedSep b E XX .id ω -
          matrixExpect (freshLaw W b) (transportedSep b E XX .id)) v) = fun ω =>
          bilinear u (wardNoise b E XX ω - matrixExpect (freshLaw W b) (wardNoise b E XX)) v :=
        funext (bilinear_id (hB W hW₄ E hE XX hXX .id).1 u v)
      rw [e]
      refine (hC₁ W hW₁ E hE XX hXX hδd u v).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_eq_mul_one_div]
      have h2 : 0 ≤ max C₂ 0 := le_max_right _ _
      exact arith_le hs hm hu hv le_rfl le_rfl ((le_max_left _ _).trans (by linarith)) hCt
    · refine (hKb W hW₂ E hE XX hXX .id u v).trans (ENNReal.ofReal_le_ofReal ?_)
      have hdm : min 1 d₀ ≤ min 1 δ := min_le_min le_rfl (le_of_lt (not_le.mp hδd))
      have hmax : 0 ≤ max C₁ 0 + max C₂ 0 := by positivity
      exact arith_off hK hm0 hdm (by linarith) hs hu hv
  · -- `σ = P`
    have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
    have h12 := BlockBand.Transmission.PathScalar.bulk_bounds hκ hE
    have hY := FullSource.nearSchur_passive hη hXX
    have e : (fun ω => bilinear u (transportedSep b E XX .proj ω -
        matrixExpect (freshLaw W b) (transportedSep b E XX .proj)) v) = fun ω =>
        bilinear (nearSel W *ᵥ u) (freshU b E (nearSchur (boundaryZ b E) XX) ω -
          matrixExpect (freshLaw W b) (freshU b E (nearSchur (boundaryZ b E) XX)))
          (nearSel W *ᵥ v) :=
      funext (bilinear_proj b E XX u v)
    rw [e]
    refine ((hC₂ W hW₃ E hE (boundaryZ b E)
      (BlockBand.Transmission.PassiveLayer.boundaryZ_mem_paramDisk (by linarith) h12.1 h12.2)
      _ hY (nearSel W *ᵥ u) (nearSel W *ᵥ v)).1.trans
      (ENNReal.ofReal_le_ofReal ?_))
    rw [div_eq_mul_one_div]
    have hmax : 0 ≤ max C₁ 0 + K / min 1 d₀ := by positivity
    exact arith_le hs hm (vecNorm_nonneg _) (vecNorm_nonneg _)
      (FullSource.vecNorm_nearSel_mulVec_le u) (FullSource.vecNorm_nearSel_mulVec_le v)
      ((le_max_left _ _).trans (by linarith)) hCt

/-- **`WordStepMean`** from the input hypotheses and the contracting-separator bounds
`SeparatorMeanUniform`, `SeparatorFluctUniform`. -/
theorem wordStepMean_of' (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hSep : SeparatorMeanUniform)
    (hSepF : SeparatorFluctUniform) : WordStepMean :=
  wordStepMean_of hMT hGA hLp hSR hSep hSepF (sepMeanIdProj_holds hGA hLp)
    (sepFluctIdProj_holds hGA hLp)

/-- **`WordStepFluct`** from the input hypotheses and the contracting-separator bounds
`SeparatorMeanUniform`, `SeparatorFluctUniform`. -/
theorem wordStepFluct_of' (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hSep : SeparatorMeanUniform)
    (hSepF : SeparatorFluctUniform) : WordStepFluct :=
  wordStepFluct_of hMT hGA hLp hSR hSep hSepF (sepMeanIdProj_holds hGA hLp)
    (sepFluctIdProj_holds hGA hLp)

end BlockBand.SourceProcess.ContractingWords
