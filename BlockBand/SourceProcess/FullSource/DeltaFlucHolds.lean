module

public import BlockBand.SourceProcess.FullSource.DeltaFlucReg

/-!
# The fluctuation bound `DeltaFluctuation`

`deltaFluctuation_holds`: for passive inputs, the centered bilinear forms `x*(Δ - EΔ)y` have `L^p`
norm at most `C_p W^{-1/2}‖x‖‖y‖`, under `GaussianAbsorptionContract` and `GaussianLpGradient`. Law
`freshLaw W b`; the constants depend on `b, κ, p` only, uniformly in `W ≥ W₀`, `E ∈ bulkInterval κ`,
passive `X` (no norm bound) and `x, y`. Proof: `x*(Δ - EΔ)y = φ - Eφ` with `φ = x*K𝒢₁₁Ky` (`K`
deterministic). At `X - iε` the Gaussian `L^p` inequality and `grad_d_reg` give
`‖φ_ε - Eφ_ε‖_p ≤ C₀√p·√(12/W)‖x‖‖y‖·C_Λ` (`d_centered_reg`, `dWeight_mom`); then `ε = 1/(n+1) → 0`
with the Fatou lemma `eLpNorm_centered_le_of_tendsto` (a.e. convergence where the layer matrix at
`X` is invertible; means bounded by `C_Λ(‖K‖ + 1)‖x‖‖y‖`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance (vecNorm_nonneg norm_bilinear_le)
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator NNReal ENNReal

variable {W : ℕ}

theorem tendsto_regX_eps (X : Matrix (Fin W) (Fin W) ℂ) :
    Tendsto (fun n : ℕ => regX X (epsN n)) atTop (𝓝 X) := by
  have := (tendsto_const_nhds (x := X)).sub
    (tendsto_epsN_I.smul_const (1 : Matrix (Fin W) (Fin W) ℂ))
  simpa [regX] using this

theorem tendsto_mul2 {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    {Pn : ℕ → Matrix a b ℂ} {Gn : ℕ → Matrix b c ℂ} {P : Matrix a b ℂ} {G : Matrix b c ℂ}
    (hP : Tendsto Pn atTop (𝓝 P)) (hG : Tendsto Gn atTop (𝓝 G)) :
    Tendsto (fun n => Pn n * Gn n) atTop (𝓝 (P * G)) := by
  have h : Continuous fun t : Matrix a b ℂ × Matrix b c ℂ => t.1 * t.2 :=
    continuous_fst.matrix_mul continuous_snd
  have h2 := (h.tendsto (P, G)).comp (hP.prodMk_nhds hG)
  exact h2

theorem tendsto_dLayer_reg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    Tendsto (fun n : ℕ => dLayer E w (regX X (epsN n)) x y ω) atTop (𝓝 (dLayer E w X x y ω)) := by
  have hQ : Tendsto (fun n : ℕ => qK w (regX X (epsN n))) atTop (𝓝 (qK w X)) := by
    have hK : Tendsto (fun n : ℕ => w • (1 : Matrix (Fin W) (Fin W) ℂ) - regX X (epsN n)) atTop
        (𝓝 (w • 1 - X)) := tendsto_const_nhds.sub (tendsto_regX_eps X)
    exact tendsto_mul2 tendsto_const_nhds hK
  have hPGQ := tendsto_mul2 (tendsto_mul2 (tendsto_pK_reg w X) (tendsto_layerAt_reg E w X ω hu)) hQ
  have hb : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear x M y :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact (hb.tendsto _).comp hPGQ

theorem norm_qK_le (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ‖qK w X‖ ≤ ‖w • 1 - X‖ := by
  have h1 : ‖(iota1 W)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact norm_iota1_le
  have h2 := Matrix.l2_opNorm_mul (iota1 W)ᴴ (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)
  rw [qK]
  nlinarith [norm_nonneg (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X), norm_nonneg (iota1 W)ᴴ]

theorem norm_K_regX_le (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖w • 1 - regX X ε‖ ≤ ‖w • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + ε := by
  rw [regX, show w • (1 : Matrix (Fin W) (Fin W) ℂ) - (X - ((ε : ℂ) * Complex.I) • 1) =
    (w • 1 - X) + ((ε : ℂ) * Complex.I) • 1 by abel]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
  exact mul_le_of_le_one_right hε BlockBand.Transmission.PassiveCovariance.norm_one_matrix_le

/-- `|φ| ≤ (‖K𝒢₁₁‖ + ‖L‖)‖K‖‖x‖‖y‖`. -/
theorem norm_dLayer_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖dLayer E w X x y ω‖ ≤
      (‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * (‖qK w X‖ * vecNorm x * vecNorm y) := by
  have h1 := norm_bilinear_le x (pK w X * layerAt E w X ω * qK w X) y
  have h2 : ‖pK w X * layerAt E w X ω * qK w X‖ ≤
      (‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * ‖qK w X‖ :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (norm_pK_mul_le E w X ω) (norm_nonneg _))
  have hx := vecNorm_nonneg x
  have hy := vecNorm_nonneg y
  calc ‖dLayer E w X x y ω‖ ≤ vecNorm x * ‖pK w X * layerAt E w X ω * qK w X‖ * vecNorm y := h1
    _ ≤ vecNorm x * ((‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * ‖qK w X‖) * vecNorm y := by gcongr
    _ = _ := by ring

/-- `x*Δy = φ - x*Ky`. -/
theorem bilinear_freshDelta (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    bilinear x (freshDelta b E X ω) y =
      dLayer E (boundaryZ b E) X x y ω - bilinear x (boundaryZ b E • 1 - X) y := by
  rw [freshDelta_eq, kgk_eq, dLayer, bilinear, bilinear, bilinear, sub_mulVec, dotProduct_sub]

/-- **`DeltaFluctuation`** from `GaussianAbsorptionContract` and `GaussianLpGradient`. -/
theorem deltaFluctuation_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    DeltaFluctuation := by
  intro b hb0 hb κ hκ
  refine ⟨1, one_pos, fun p hp => ?_⟩
  obtain ⟨C₀, hC₀, hLp'⟩ := hLp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨CL, W₀, hCL, hmom⟩ := dWeight_mom hGA hb0 hb hκ hp
  obtain ⟨_, W₁, _, hint⟩ := delta_integrable hGA b hb0 hb κ hκ
  obtain ⟨_, W₂, hdet⟩ := moments_holds hGA b hb0 hb κ hκ 1 le_rfl
  refine ⟨2 * (C₀ * Real.sqrt p) * Real.sqrt 12 * CL, max (max W₀ W₁) (max W₂ 1), ?_⟩
  intro W hW E hE X hY _ x y
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW1⟩, hW2, hWone⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  set z := boundaryZ b E
  have hz : z ∈ paramDisk b E := boundaryZ_mem_paramDisk (by linarith) hE1 hE2
  obtain ⟨hwim, hw3, -, -⟩ := disk_bounds hb0 hb hκ hE hz
  have hη₀ : 0 < (1 - b) * κ / 4 := by
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
      MemLp (dLayer E z X' x y) (ENNReal.ofReal p) μ ∧
        ‖∫ ω, dLayer E z X' x y ω ∂μ‖ ≤ CL * (‖qK z X'‖ * vecNorm x * vecNorm y) := by
    intro X' hY'
    have hkl := ((hmom W hW0 E hE z hz X' hY').2).const_mul (c := ‖qK z X'‖ * vecNorm x * vecNorm y)
      (by positivity)
    have hd : eLpNorm (dLayer E z X' x y) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (‖qK z X'‖ * vecNorm x * vecNorm y * CL) :=
      (eLpNorm_mono_ae_real (measurable_dLayer E z X' x y).aestronglyMeasurable
        (ae_of_all _ fun ω => (norm_dLayer_le E z X' x y ω).trans (le_of_eq (by ring)))).trans hkl.2
    have hM : MemLp (dLayer E z X' x y) (ENNReal.ofReal p) μ :=
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
  have hfix : ∀ n, eLpNorm (fun ω => dLayer E z (regX X (epsN n)) x y ω -
      ∫ ω', dLayer E z (regX X (epsN n)) x y ω' ∂μ) (ENNReal.ofReal p) μ ≤ B := by
    intro n
    have hYn := regX_posSemidef hY (epsN_pos n).le
    exact (d_centered_reg hLp' hb0 hb hWone E hzim hw5 hY (epsN_pos n) hp x y
      (hpass _ hYn).1).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl
        ((hmom W hW0 E hE z hz _ hYn).1.2)))
  have hmean : ∀ n, ‖∫ ω', dLayer E z (regX X (epsN n)) x y ω' ∂μ‖ ≤
      CL * ((‖z • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ + 1) * vecNorm x * vecNorm y) := by
    intro n
    refine ((hpass _ (regX_posSemidef hY (epsN_pos n).le)).2).trans ?_
    have hq := (norm_qK_le z (regX X (epsN n))).trans (norm_K_regX_le z X (epsN_pos n).le)
    have he : epsN n ≤ 1 := by
      unfold epsN; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    gcongr; linarith
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => dLayer E z (regX X (epsN n)) x y ω)
      atTop (𝓝 (dLayer E z X x y ω)) := by
    filter_upwards [(hdet W hW2 E hE z hz X hY).1] with ω hω
    exact tendsto_dLayer_reg E z X x y ω ((isUnit_iff_isUnit_det _).mpr hω)
  have hF := eLpNorm_centered_le_of_tendsto hp1
    (fun n => (measurable_dLayer E z _ x y).aestronglyMeasurable)
    (measurable_dLayer E z X x y).aestronglyMeasurable (hMem.integrable hp1) hlim hmean hfix
  have hid : (fun ω => bilinear x (freshDelta b E X ω - matrixExpect μ (freshDelta b E X)) y) =
      fun ω => dLayer E z X x y ω - ∫ ω', dLayer E z X x y ω' ∂μ := by
    funext ω
    rw [bilinear_sub_matrixExpect _ (hint W hW1 E hE X hY).1]
    simp only [bilinear_freshDelta]
    rw [integral_sub (hMem.integrable hp1) (integrable_const _), integral_const]
    simp [z]
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

end BlockBand.SourceProcess.FullSource
