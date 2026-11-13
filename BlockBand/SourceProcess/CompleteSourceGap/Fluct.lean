module

public import BlockBand.SourceProcess.CompleteSourceGap.Mean
public import BlockBand.Transmission.SourceMixing.Fluctuation

/-!
# `CompleteSourceGapStatement.fluctuation`, and the assembled statement

`fluctuation_holds` proves the fluctuation clause separator by separator:
* separators `P𝕊`, `𝕊*P`: `x*(U - EU)y = (ι*x)*(Γ - EΓ)(ι*𝕊y)` and `GapLetterFluctuation`;
* separators `P𝕊P`, `P𝕊*P`: `x*(U - EU)y = -2iη (ι*x)*(F - EF)(ι*y)`, `F = Lf₊L*`, and
  `SourceMixing.oneStepFluctuation_holds` (second clause; the same lemma supplies the centered
  bilinear bound);
* **`completeSourceGap_of`**: `CompleteSourceGapStatement` from `GaussianAbsorptionContract`,
  `GaussianLpGradient` and the two one-port hypotheses `GapLetterMean`, `GapLetterFluctuation`
  (proved as `gapLetterMean_holds`, `gapLetterFluctuation_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

theorem ofReal_bound_mono {C a a' c c' : ℝ} (s : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haa : a ≤ a') (hcc : c ≤ c') :
    ENNReal.ofReal (C * s * a * c) ≤ ENNReal.ofReal (max C 0 * s * a' * c') := by
  apply ENNReal.ofReal_le_ofReal
  have h1 : C * s * a * c ≤ max C 0 * s * a * c := by
    have := mul_nonneg (mul_nonneg hs ha) hc
    nlinarith [le_max_left C 0]
  refine h1.trans ?_
  have hm : 0 ≤ max C 0 * s := mul_nonneg (le_max_right _ _) hs
  calc max C 0 * s * a * c ≤ max C 0 * s * a' * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haa hm) hc
    _ ≤ max C 0 * s * a' * c' := mul_le_mul_of_nonneg_left hcc (mul_nonneg hm (ha.trans haa))

theorem eLpNorm_star_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℂ)
    (p : ℝ≥0∞) : eLpNorm (fun ω => star (f ω)) p μ = eLpNorm f p μ := by
  have h : ∀ x, ‖star (f x)‖ₑ = ‖f x‖ₑ := fun x => by simp [enorm]
  have hiff : AEStronglyMeasurable (fun ω => star (f ω)) μ ↔ AEStronglyMeasurable f μ :=
    ⟨fun h => h.star.congr (Filter.Eventually.of_forall fun ω => by simp), fun h => h.star⟩
  simp only [eLpNorm, eLpNorm', eLpNormEssSup, h]
  by_cases hf : AEStronglyMeasurable f μ
  · simp only [hf, hiff.mpr hf, ↓reduceIte]
  · simp only [hf, mt hiff.mp hf, ↓reduceIte]

theorem bilinear_smul {n : Type*} [Fintype n] (c : ℂ) (u v : n → ℂ) (M : Matrix n n ℂ) :
    bilinear u (c • M) v = c * bilinear u M v := by
  simp only [bilinear, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **`CompleteSourceGapStatement.fluctuation`**. -/
theorem fluctuation_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hF : GapLetterFluctuation) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ : Separator, σ.unconj + σ.conj = 1 → ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (transportedSep b E XX σ ω -
            matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) := by
  intro b hb0 hb E hE1 hE2 p hp
  obtain ⟨C₁, W₁, h1⟩ := hF b hb0 hb E hE1 hE2 p hp
  obtain ⟨C₂, W₂, h2⟩ :=
    BlockBand.Transmission.SourceMixing.oneStepFluctuation_holds hGA hLp b hb0 hb E hE1 hE2 p hp
  obtain ⟨W₃, hI⟩ := integrable_gapLetter hGA hb0 hb hE1 hE2
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  set c : ℂ := (2 * Complex.I) * (etaZ b E : ℂ)
  have hc : ‖-c‖ = 2 * etaZ b E := by simp [c, Complex.norm_real, abs_of_pos hη]
  set K := max C₁ 0 + 2 * etaZ b E * max C₂ 0
  have hK1 : max C₁ 0 ≤ K := by simp only [K]; have := le_max_right C₂ 0; nlinarith
  refine ⟨K, max (max W₁ W₂) (max W₃ 1), fun W hW XX hXX σ hσ => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right (le_of_max_le_right hW)
  set X := nearSchur (boundaryZ b E) XX
  have hY : (passiveY X).PosSemidef := nearSchur_passive hη hXX
  have hs : 0 ≤ 1 / Real.sqrt W := by positivity
  have hdiv : ∀ C' a c' : ℝ, C' / Real.sqrt W * a * c' = C' * (1 / Real.sqrt W) * a * c' := by
    intro C' a c'; ring
  -- `P𝕊`
  have caseS : ∀ u v : Fin 2 × Fin W → ℂ,
      eLpNorm (fun ω => bilinear u (transportedSep b E XX .projS ω -
          matrixExpect (freshLaw W b) (transportedSep b E XX .projS)) v) (ENNReal.ofReal p)
          (freshLaw W b) ≤ ENNReal.ofReal (K / Real.sqrt W * vecNorm u * vecNorm v) := by
    intro u v
    set T := nearSel W * twoPortScattering b E XX
    have hT : ‖T‖ ≤ 1 := (norm_nearSel_mul_le _).trans (norm_scat_le b E hXX hη)
    have hEU : matrixExpect (freshLaw W b) (transportedSep b E XX .projS) =
        (nearSel W)ᴴ * matrixExpect (freshLaw W b) (gapLetter b E X) * T := by
      rw [FullSourceCovariance.matrixExpect_congr_ae (ae_transportedSep_projS hb0 hb hE1 hE2 hW1 hXX),
        matrixExpect_rect _ _ _ (hI W (le_of_max_le_left (le_of_max_le_right hW)) X hY)]
    rw [hEU]
    have hae : ∀ᵐ ω ∂freshLaw W b, bilinear u (transportedSep b E XX .projS ω -
        (nearSel W)ᴴ * matrixExpect (freshLaw W b) (gapLetter b E X) * T) v =
        bilinear (nearSel W *ᵥ u) (gapLetter b E X ω -
          matrixExpect (freshLaw W b) (gapLetter b E X)) (T *ᵥ v) := by
      filter_upwards [ae_transportedSep_projS hb0 hb hE1 hE2 hW1 hXX] with ω hω
      rw [hω, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_assoc, bilinear_sandwich']
    rw [eLpNorm_congr_ae hae]
    refine (h1 W (le_of_max_le_left (le_of_max_le_left hW)) X hY _ _).trans ?_
    rw [hdiv, hdiv]
    refine (ofReal_bound_mono (c' := vecNorm v) _ hs
      (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _)
      (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _) (vecNorm_nearSel_mulVec_le u)
      ((vecNorm_mulVec_le' T v).trans (mul_le_of_le_one_left
        (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v) hT))).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have := mul_nonneg (mul_nonneg hs (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg u))
      (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v)
    nlinarith
  -- `P𝕊P`
  have caseSP : ∀ u v : Fin 2 × Fin W → ℂ,
      eLpNorm (fun ω => bilinear u (transportedSep b E XX .projSProj ω -
          matrixExpect (freshLaw W b) (transportedSep b E XX .projSProj)) v) (ENNReal.ofReal p)
          (freshLaw W b) ≤ ENNReal.ofReal (K / Real.sqrt W * vecNorm u * vecNorm v) := by
    intro u v
    have hEU : matrixExpect (freshLaw W b) (transportedSep b E XX .projSProj) =
        (-c) • ((nearSel W)ᴴ * matrixExpect (freshLaw W b) (freshTransportedF b E X) *
          nearSel W) := by
      rw [FullSourceCovariance.matrixExpect_congr_ae
        (ae_transportedSep_projSProj hb0 hb hE1 hE2 hW1 hXX), matrixExpect_smul, matrixExpect_lift]
    rw [hEU]
    have hae : ∀ᵐ ω ∂freshLaw W b, bilinear u (transportedSep b E XX .projSProj ω -
        (-c) • ((nearSel W)ᴴ * matrixExpect (freshLaw W b) (freshTransportedF b E X) *
          nearSel W)) v =
        (-c) * bilinear (nearSel W *ᵥ u) (freshTransportedF b E X ω -
          matrixExpect (freshLaw W b) (freshTransportedF b E X)) (nearSel W *ᵥ v) := by
      filter_upwards [ae_transportedSep_projSProj hb0 hb hE1 hE2 hW1 hXX] with ω hω
      rw [hω, ← smul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_assoc, bilinear_smul,
        bilinear_sandwich']
    rw [eLpNorm_congr_ae hae]
    rw [show (fun ω => -c * bilinear (nearSel W *ᵥ u) (freshTransportedF b E X ω -
        matrixExpect (freshLaw W b) (freshTransportedF b E X)) (nearSel W *ᵥ v)) =
        (-c) • (fun ω => bilinear (nearSel W *ᵥ u) (freshTransportedF b E X ω -
        matrixExpect (freshLaw W b) (freshTransportedF b E X)) (nearSel W *ᵥ v)) from rfl,
      eLpNorm_const_smul, ← ofReal_norm, hc]
    have hb2 := (h2 W (le_of_max_le_right (le_of_max_le_left hW)) X hY
      (nearSel W *ᵥ u) (nearSel W *ᵥ v)).2
    calc ENNReal.ofReal (2 * etaZ b E) * eLpNorm _ (ENNReal.ofReal p) (freshLaw W b)
        ≤ ENNReal.ofReal (2 * etaZ b E) * ENNReal.ofReal (max C₂ 0 * (1 / Real.sqrt W) *
            vecNorm u * vecNorm v) := by
          gcongr
          refine hb2.trans ?_
          rw [hdiv]
          exact ofReal_bound_mono _ hs (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _) (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg _)
            (vecNorm_nearSel_mulVec_le u) (vecNorm_nearSel_mulVec_le v)
      _ ≤ ENNReal.ofReal (K / Real.sqrt W * vecNorm u * vecNorm v) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h0 := mul_nonneg (mul_nonneg hs (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg u)) (BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg v)
          have : 2 * etaZ b E * max C₂ 0 ≤ K := by simp only [K]; have := le_max_right C₁ 0; linarith
          rw [hdiv]
          nlinarith [mul_nonneg (le_max_right C₂ 0) h0]
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · exact caseS
  · intro u v
    rw [show transportedSep b E XX .sStarProj =
      fun ω => (transportedSep b E XX .projS ω)ᴴ from funext (transportedSep_sStarProj b E XX),
      matrixExpect_conjTranspose]
    simp only [← conjTranspose_sub, bilinear_conjTranspose, eLpNorm_star_eq]
    rw [mul_right_comm]
    exact caseS v u
  · exact caseSP
  · intro u v
    rw [show transportedSep b E XX .projSStarProj =
      fun ω => (transportedSep b E XX .projSProj ω)ᴴ from
        funext (transportedSep_projSStarProj b E XX), matrixExpect_conjTranspose]
    simp only [← conjTranspose_sub, bilinear_conjTranspose, eLpNorm_star_eq]
    rw [mul_right_comm]
    exact caseSP v u

/-- **The complete source gap** from the Gaussian inputs (`GaussianAbsorptionContract`,
`GaussianLpGradient`) and the two open one-port nodes `GapLetterMean`, `GapLetterFluctuation`. -/
theorem completeSourceGap_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hM : GapLetterMean) (hF : GapLetterFluctuation) : CompleteSourceGapStatement :=
  ⟨mean_holds hGA hLp hM, fluctuation_holds hGA hLp hF⟩

end BlockBand.SourceProcess.CompleteSourceGap
