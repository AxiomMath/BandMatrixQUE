module

public import BlockBand.SourceProcess.FullSource.DeltaFlucHolds

/-!
# `L^p` fluctuations of `Δ` at every passive input

`deltaFluctuation_all`: for every passive `X` (not only on the scalar domain), the centered
bilinear forms `x*(Δ - EΔ)y` have `L^p` norm at most `C_p W^{-1/2}‖x‖‖y‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PassiveCovariance (vecNorm_nonneg norm_bilinear_le)
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator NNReal ENNReal

variable {W : ℕ}

/-- **`L^p` fluctuation of `x*Δy` for every passive `X`** (as in `deltaFluctuation_holds`). -/
theorem deltaFluctuation_all (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ x y : Fin W → ℂ,
        eLpNorm (fun ω => bilinear x (freshDelta b E X ω -
            matrixExpect (freshLaw W b) (freshDelta b E X)) y) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm x * vecNorm y) := by
  intro b hb0 hb κ hκ p hp
  obtain ⟨C₀, hC₀, hLp'⟩ := hLp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨CL, W₀, hCL, hmom⟩ := dWeight_mom hGA hb0 hb hκ hp
  obtain ⟨_, W₁, _, hint⟩ := delta_integrable hGA b hb0 hb κ hκ
  obtain ⟨_, W₂, hdet⟩ := moments_holds hGA b hb0 hb κ hκ 1 le_rfl
  refine ⟨2 * (C₀ * Real.sqrt p) * Real.sqrt 12 * CL, max (max W₀ W₁) (max W₂ 1), ?_⟩
  intro W hW E hE X hY x y
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW1⟩, hW2, hWone⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  set z := boundaryZ b E
  have hz : z ∈ paramDisk b E := FullSource.boundaryZ_mem_paramDisk (by linarith) hE1 hE2
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

end BlockBand.SourceProcess.FullSourceCovariance
