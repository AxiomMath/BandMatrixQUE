module

public import BlockBand.SourceProcess.CompleteSourceGap.GapFlucGrad
public import BlockBand.SourceProcess.CompleteSourceGap.Mean

/-!
# Fluctuation of the gap letter

`gapLetterFluctuation_holds` proves `GapLetterFluctuation` from `GaussianAbsorptionContract` and
`GaussianLpGradient`. Law `freshLaw W b`; vectors `x, y`; the constants depend on `b, E, p` only,
uniformly in `W ≥ W₀`, passive `X` (no norm bound) and `x, y`. The proof is the one of
`deltaFluctuation_holds`, for `φ = x*Γy = x*(Kι₁𝒢P₂𝒢ι₁*K)y` (`bilinear_gapLetter`). At `X - iε` the Gaussian `L^p` inequality and `grad_gap_reg` give
`‖φ_ε - Eφ_ε‖_p ≤ C₀√p·√(12/W)‖x‖‖y‖·C_Λ` (`gap_centered_reg`, `gWeight_mom`: the passive moments
at `4p`, `‖A‖, ‖B‖ ∈ L^{4p}`, Hölder); then `ε = 1/(n+1) → 0` by the Fatou lemma
`eLpNorm_centered_le_of_tendsto` (a.e. convergence where the layer matrix at `X` is invertible;
means bounded by `C_Λ(‖K‖ + 1)‖x‖‖y‖`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PassiveCovariance (vecNorm_nonneg norm_bilinear_le LayerMat)
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator NNReal ENNReal

variable {W : ℕ}

/-- **`‖gWeight‖_p ≤ C_Λ`**, uniformly over passive inputs (passive moments at `4p`). -/
theorem gWeight_mom (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        MomBd (freshLaw W b) (gWeight E w X) p C ∧
        MomBd (freshLaw W b) (fun ω => (‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * ‖layerAt E w X ω‖) p C := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C', W₀, hm⟩ := moments_holds hGA b hb0 hb κ hκ (4 * p) (by linarith)
  obtain ⟨CA, hCA0, hCA⟩ := blockA_mom hb (p := 4 * p) (by linarith)
  obtain ⟨CB, hCB0, hCB⟩ := bondB_mom hb0 (p := 4 * p) (by linarith)
  set Cm := max C' 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  set CL := 2 * ((Cm + Cm) * Cm * (1 + Cm * (5 + CA + CB)))
  refine ⟨max CL ((Cm + Cm) * Cm), max W₀ 1, le_max_of_le_right (by positivity),
    fun W hW E hE w hw X hY => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  obtain ⟨-, hg, hk, hl⟩ := hm W (le_of_max_le_left hW) E hE w hw X hY
  obtain ⟨hgM, hkM, hlM⟩ := letter_momBd (b := b) ⟨hg, hk, hl⟩
  have hkl : MomBd (freshLaw W b) (fun ω => ‖kG11 E w X ω‖ + ‖lAt E w X ω‖) (2 * (2 * p))
      (Cm + Cm) := by
    rw [show 2 * (2 * p) = 4 * p by ring]
    exact hkM.add (by linarith) hlM hCm hCm
  have hgM4 : MomBd (freshLaw W b) (fun ω => ‖layerAt E w X ω‖) (2 * (2 * p)) Cm := by
    rw [show 2 * (2 * p) = 4 * p by ring]; exact hgM
  have hklg := MomBd.mul (by positivity : (0 : ℝ) < 2 * p) hkl hgM4 (by positivity)
  have h5 : MomBd (freshLaw W b) (fun _ => (5 : ℝ)) (4 * p) 5 := by
    simpa using MomBd.const (μ := freshLaw W b) (5 : ℝ) (4 * p) (by positivity)
  have hP : MomBd (freshLaw W b) (fun ω => 5 + ‖ω.1 0‖ + ‖ω.2 0 0‖) (2 * (2 * p))
      (5 + CA + CB) := by
    rw [show 2 * (2 * p) = 4 * p by ring]
    exact (h5.add (by linarith) (hCA W hW1) (by norm_num) hCA0).add (by linarith) (hCB W hW1)
      (by positivity) hCB0
  have hgP := MomBd.mul (by positivity : (0 : ℝ) < 2 * p) hgM4 hP hCm
  have h1 : MomBd (freshLaw W b) (fun _ => (1 : ℝ)) (2 * p) 1 := by
    simpa using MomBd.const (μ := freshLaw W b) (1 : ℝ) (2 * p) (by positivity)
  have h1P := h1.add (by linarith) hgP zero_le_one (by positivity)
  have hprod := (hklg.mul hp0 h1P (by positivity)).const_mul (c := 2) (by norm_num)
  refine ⟨hprod.of_le (le_max_left _ _), ?_⟩
  exact (hklg.exponent_mono (by linarith)).of_le (le_max_right _ _)

/-- `|φ| ≤ (‖K𝒢₁₁‖ + ‖L‖)‖𝒢‖‖ι₁*K‖‖x‖‖y‖`. -/
theorem norm_gapLayer_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖gapLayer E w X x y ω‖ ≤ (‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * ‖layerAt E w X ω‖ *
      (‖qK w X‖ * vecNorm x * vecNorm y) := by
  set G := layerAt E w X ω
  have h1 := norm_bilinear_le x (pK w X * (G * pTwo W * G) * qK w X) y
  have hP2 : ‖pTwo W‖ ≤ 1 := norm_pTwo_le
  have hPG := norm_pK_mul_le E w X ω
  have hG := norm_nonneg G
  have hQ := norm_nonneg (qK w X)
  have e : pK w X * (G * pTwo W * G) * qK w X = (pK w X * G) * pTwo W * G * qK w X := by
    simp only [Matrix.mul_assoc]
  have h2 : ‖pK w X * (G * pTwo W * G) * qK w X‖ ≤
      (‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * ‖G‖ * ‖qK w X‖ := by
    rw [e]
    refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ hQ)
    refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ hG)
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    have := norm_nonneg (pK w X * G)
    nlinarith
  have hx := vecNorm_nonneg x
  have hy := vecNorm_nonneg y
  calc ‖gapLayer E w X x y ω‖
      ≤ vecNorm x * ‖pK w X * (G * pTwo W * G) * qK w X‖ * vecNorm y := h1
    _ ≤ vecNorm x * ((‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * ‖G‖ * ‖qK w X‖) * vecNorm y := by gcongr
    _ = _ := by ring

theorem tendsto_gapLayer_reg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    Tendsto (fun n : ℕ => gapLayer E w (regX X (epsN n)) x y ω) atTop
      (𝓝 (gapLayer E w X x y ω)) := by
  have hQ : Tendsto (fun n : ℕ => qK w (regX X (epsN n))) atTop (𝓝 (qK w X)) := by
    have hK : Tendsto (fun n : ℕ => w • (1 : Matrix (Fin W) (Fin W) ℂ) - regX X (epsN n)) atTop
        (𝓝 (w • 1 - X)) := tendsto_const_nhds.sub (tendsto_regX_eps X)
    exact tendsto_mul2 tendsto_const_nhds hK
  have hG := tendsto_layerAt_reg E w X ω hu
  have hH := tendsto_mul2 (tendsto_mul2 hG (tendsto_const_nhds (x := pTwo W))) hG
  have hPGQ := tendsto_mul2 (tendsto_mul2 (tendsto_pK_reg w X) hH) hQ
  have hb : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear x M y :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact (hb.tendsto _).comp hPGQ

/-- **`GapLetterFluctuation`**, from `GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem gapLetterFluctuation_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : GapLetterFluctuation := by
  intro b hb0 hb E hE1 hE2 p hp
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := mem_bulkInterval_min E
  obtain ⟨C₀, hC₀, hLp'⟩ := hLp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨CL, W₀, hCL, hmom⟩ := gWeight_mom hGA hb0 hb hκ hp
  obtain ⟨W₁, hint⟩ := integrable_gapLetter hGA hb0 hb hE1 hE2
  obtain ⟨_, W₂, hdet⟩ := moments_holds hGA b hb0 hb _ hκ 1 le_rfl
  refine ⟨2 * (C₀ * Real.sqrt p) * Real.sqrt 12 * CL, max (max W₀ W₁) (max W₂ 1), ?_⟩
  intro W hW X hY x y
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW1⟩, hW2, hWone⟩ := hW
  set z := boundaryZ b E
  have hz : z ∈ paramDisk b E := BlockBand.Transmission.PassiveLayer.boundaryZ_mem_paramDisk (by linarith) hE1 hE2
  obtain ⟨hwim, hw3, -, -⟩ := disk_bounds hb0 hb hκ hE hz
  have hη₀ : 0 < (1 - b) * min (2 + E) (2 - E) / 4 := by
    have : 0 < 1 - b := by linarith
    positivity
  have hzim : 0 < z.im := lt_of_lt_of_le hη₀ hwim
  have hw5 : ‖z‖ + |E| ≤ 5 := by
    have : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  set μ := freshLaw W b
  have hx := vecNorm_nonneg x
  have hy := vecNorm_nonneg y
  -- integrability and means at every passive input
  have hpass : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      MemLp (gapLayer E z X' x y) (ENNReal.ofReal p) μ ∧
        ‖∫ ω, gapLayer E z X' x y ω ∂μ‖ ≤ CL * (‖qK z X'‖ * vecNorm x * vecNorm y) := by
    intro X' hY'
    have hkl := ((hmom W hW0 E hE z hz X' hY').2).const_mul
      (c := ‖qK z X'‖ * vecNorm x * vecNorm y) (by positivity)
    have hd : eLpNorm (gapLayer E z X' x y) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (‖qK z X'‖ * vecNorm x * vecNorm y * CL) :=
      (eLpNorm_mono_ae_real (measurable_gapLayer E z X' x y).aestronglyMeasurable
        (ae_of_all _ fun ω => (norm_gapLayer_le E z X' x y ω).trans (le_of_eq (by ring)))).trans
        hkl.2
    have hM : MemLp (gapLayer E z X' x y) (ENNReal.ofReal p) μ :=
      lt_of_le_of_lt hd ENNReal.ofReal_lt_top
    refine ⟨hM, ?_⟩
    have h1 := (enorm_integral_le_eLpNorm hp1 hM.aestronglyMeasurable).trans hd
    rw [← ofReal_norm] at h1
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    linarith
  obtain ⟨hMem, -⟩ := hpass X hY
  set k := Real.sqrt (3 * (4 / W)) * (vecNorm x * vecNorm y)
  have hk0 : 0 ≤ k := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hx hy)
  set B := ENNReal.ofReal (C₀ * Real.sqrt p) * (ENNReal.ofReal k * ENNReal.ofReal CL)
  have hfix : ∀ n, eLpNorm (fun ω => gapLayer E z (regX X (epsN n)) x y ω -
      ∫ ω', gapLayer E z (regX X (epsN n)) x y ω' ∂μ) (ENNReal.ofReal p) μ ≤ B := by
    intro n
    have hYn := regX_posSemidef hY (epsN_pos n).le
    exact (gap_centered_reg hLp' hb0 hb hWone E hzim hw5 hY (epsN_pos n) hp x y
      (hpass _ hYn).1).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl
        ((hmom W hW0 E hE z hz _ hYn).1.2)))
  have hmean : ∀ n, ‖∫ ω', gapLayer E z (regX X (epsN n)) x y ω' ∂μ‖ ≤
      CL * ((‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1) * vecNorm x * vecNorm y) := by
    intro n
    refine ((hpass _ (regX_posSemidef hY (epsN_pos n).le)).2).trans ?_
    have hq := (norm_qK_le z (regX X (epsN n))).trans (norm_K_regX_le z X (epsN_pos n).le)
    have he : epsN n ≤ 1 := by
      unfold epsN; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    gcongr; linarith
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => gapLayer E z (regX X (epsN n)) x y ω)
      atTop (𝓝 (gapLayer E z X x y ω)) := by
    filter_upwards [(hdet W hW2 E hE z hz X hY).1] with ω hω
    exact tendsto_gapLayer_reg E z X x y ω ((isUnit_iff_isUnit_det _).mpr hω)
  have hF := eLpNorm_centered_le_of_tendsto hp1
    (fun n => (measurable_gapLayer E z _ x y).aestronglyMeasurable)
    (measurable_gapLayer E z X x y).aestronglyMeasurable (hMem.integrable hp1) hlim hmean hfix
  have hid : (fun ω => bilinear x (gapLetter b E X ω - matrixExpect μ (gapLetter b E X)) y) =
      fun ω => gapLayer E z X x y ω - ∫ ω', gapLayer E z X x y ω' ∂μ := by
    funext ω
    rw [bilinear_sub_matrixExpect _ (hint W hW1 X hY)]
    simp only [bilinear_gapLetter]
    rfl
  rw [hid]
  refine hF.trans (le_of_eq ?_)
  have hs : Real.sqrt (3 * (4 / (W : ℝ))) = Real.sqrt 12 / Real.sqrt W := by
    rw [show 3 * (4 / (W : ℝ)) = 12 / W by ring, Real.sqrt_div' _ (Nat.cast_nonneg W)]
  simp only [B]
  rw [← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  simp only [k, hs]
  ring

end BlockBand.SourceProcess.CompleteSourceGap
