module

public import BlockBand.SourceProcess.PhysApprox.B3MomK

/-!
# The per-step fourth moment of one raw `𝒦` step

On old entries the complex source update is `𝒦₊ − 𝒦 = V*ιΔι*𝕊V`; its centered increment has
`L^p` size `C_p Tr M_pr/√W` and mean size `C(δ₀ + W⁻²) Tr M_pr`. This file proves the case `p = 4`.

The shared per-step lemma of the `B3Four*` files. One growth step `l → l + 1` changes an old raw
tag form by `a*Δc` (`RawTag.RawUpdate`), `a = ι*𝒰*ξ`, `c = ι*𝕊𝒰*ξ'`, `Δ` the fresh layer.
* `Four.lintegral_bilinear_four_le` (abstract): conditionally on the past,
  `E_f|a*Δc|⁴ ≤ 8(|a*(EΔ)c|⁴ + s⁴)` when `‖a*(Δ − EΔ)c‖_{L⁴} ≤ s`.
* **`Four.lintegral_stepIncr_le`** (from the contract hypotheses): uniformly in bulk `E`,
  `1 ≤ l ≤ TW`, the birth indices and the tag laws, `E|a*Δ_l c|⁴ ≤ C/W²`. The inputs are the
  one-layer bounds `RawTag.delta_fresh_bounds` (`‖EΔ‖ ≤ C_m(δ₀ + W⁻¹)`, fluctuation
  `C_f(W^{-1/2} + δ₀)`), the length-uniform `‖δ₀(X_l)‖_{L¹⁶} ≤ C_δ/W`
  (`DeltaZeroLengthUniform`) and the frame moments `RawTag.momBd_frame`. Pointwise the step is
  `≤ C W^{-1/2}(1 + √W δ₀)|a||c|`, and `1 + √W δ₀` has bounded moments.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Four

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.LengthUniform BlockBand.SourceProcess.RawTag
open scoped Matrix ENNReal ComplexOrder Matrix.Norms.L2Operator

/-! ## The abstract conditional fourth moment of one step -/

theorem ofReal_sq_pow_two_one (z : ℂ) : ENNReal.ofReal ((‖z‖ ^ 2) ^ (2 * 1)) = ‖z‖ₑ ^ 4 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← pow_mul]

/-- **The abstract step**: for a past `p ~ μP` and a fresh `f ~ μF`,
`E|a*D c|⁴ ≤ E_p 8(|a*(E_f D)c|⁴ + s⁴)` when `‖a*(D − E_f D)c‖_{L⁴(μF)} ≤ s`. -/
theorem lintegral_bilinear_four_le {P F : Type*} [MeasurableSpace P] [MeasurableSpace F]
    (μP : Measure P) [SFinite μP] (μF : Measure F) [IsProbabilityMeasure μF] {W : ℕ}
    (a c : P → Fin W → ℂ) (D : P → F → Matrix (Fin W) (Fin W) ℂ)
    (hΦ : AEMeasurable (fun z : P × F => ‖bilinear (a z.1) (D z.1 z.2) (c z.1)‖ₑ ^ 4)
      (μP.prod μF))
    (hI : ∀ᵐ p ∂μP, ∀ i j, Integrable (fun f => D p f i j) μF)
    (s : P → ℝ) (hs0 : ∀ p, 0 ≤ s p)
    (hs : ∀ᵐ p ∂μP, eLpNorm (fun f => bilinear (a p) (D p f - matrixExpect μF (D p)) (c p))
      (ENNReal.ofReal 4) μF ≤ ENNReal.ofReal (s p)) :
    ∫⁻ z, ‖bilinear (a z.1) (D z.1 z.2) (c z.1)‖ₑ ^ 4 ∂(μP.prod μF) ≤
      ∫⁻ p, 8 * (‖bilinear (a p) (matrixExpect μF (D p)) (c p)‖ₑ ^ 4 +
        ENNReal.ofReal (s p ^ 4)) ∂μP := by
  rw [lintegral_prod _ hΦ]
  refine lintegral_mono_ae ?_
  filter_upwards [hI, hs] with p hIp hsp
  set M := matrixExpect μF (D p)
  set u := bilinear (a p) M (c p)
  set d : F → ℂ := fun f => bilinear (a p) (D p f - M) (c p)
  have hdecomp : ∀ f, bilinear (a p) (D p f) (c p) = u + d f := by
    intro f; simp only [u, d, bilinear_sub_mid]; ring
  have hDM : ∀ i j, Integrable (fun f => (D p f - M) i j) μF := fun i j =>
    (hIp i j).sub (integrable_const _)
  have hdi : Integrable d μF :=
    BlockBand.SourceProcess.FullSource.integrable_bilinear (fun f => D p f - M) hDM (a p) (c p)
  have hd4 : ∫⁻ f, ‖d f‖ₑ ^ 4 ∂μF ≤ ENNReal.ofReal (s p ^ 4) := by
    have h := lintegral_pow_le_of_eLpNorm hdi.aestronglyMeasurable (m := 1) le_rfl (hs0 p)
      (by simpa using hsp)
    simp_rw [ofReal_sq_pow_two_one] at h
    simpa using h
  simp_rw [hdecomp]
  calc ∫⁻ f, ‖u + d f‖ₑ ^ 4 ∂μF ≤ ∫⁻ f, 8 * (‖u‖ₑ ^ 4 + ‖d f‖ₑ ^ 4) ∂μF :=
        lintegral_mono fun f => (pow_le_pow_left₀ zero_le (enorm_add_le _ _) 4).trans
          (add_pow_four_le _ _)
    _ = 8 * (‖u‖ₑ ^ 4 + ∫⁻ f, ‖d f‖ₑ ^ 4 ∂μF) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ 8 * (‖u‖ₑ ^ 4 + ENNReal.ofReal (s p ^ 4)) := by gcongr

/-! ## The step on the growth path -/

variable {W : ℕ}

/-- The moment bound of `(1 + √W δ₀)|a||c|` at exponent `4`. -/
theorem momBd_stepWeight {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} [IsProbabilityMeasure ν]
    {b E : ℝ} {l β₁ β₂ : ℕ} {g₁ g₂ : Γ → Fin W → ℂ} (hW : (1 : ℝ) ≤ W) {Cδ A : ℝ}
    (hCδ : 0 ≤ Cδ) (hA : 0 ≤ A)
    (hδ : MomBd ((growthPathLaw W b).prod ν)
      (fun w => jetDistance0 b E (pathX b E W l w.1)) 16 (Cδ / W))
    (ha : MomBd ((growthPathLaw W b).prod ν)
      (fun w => vecNorm (nearL b E W l β₁ w.1 (g₁ w.2))) 16 A)
    (hc : MomBd ((growthPathLaw W b).prod ν)
      (fun w => vecNorm (nearR b E W l β₂ w.1 (g₂ w.2))) 16 A) :
    MomBd ((growthPathLaw W b).prod ν)
      (fun w => (1 + Real.sqrt W * jetDistance0 b E (pathX b E W l w.1)) *
        vecNorm (nearL b E W l β₁ w.1 (g₁ w.2)) * vecNorm (nearR b E W l β₂ w.1 (g₂ w.2)))
      4 ((Cδ + 1) * A * A) := by
  set μΩ := (growthPathLaw W b).prod ν
  have hW0 : (0 : ℝ) < W := by linarith
  have hsW : Real.sqrt W ≤ W := by
    rw [Real.sqrt_le_left hW0.le]; nlinarith
  have h1 : MomBd μΩ (fun w => Real.sqrt W * jetDistance0 b E (pathX b E W l w.1)) 16 Cδ := by
    refine (hδ.const_mul (c := Real.sqrt W) (Real.sqrt_nonneg _)).of_le ?_
    rw [mul_div_assoc', div_le_iff₀ hW0]; nlinarith [mul_le_mul_of_nonneg_left hsW hCδ]
  have h2 := (MomBd.const (μ := μΩ) (1 : ℝ) 16 (by norm_num)).add (by norm_num) h1
    (abs_nonneg _) hCδ
  rw [abs_one, add_comm (1 : ℝ) Cδ] at h2
  have e16 : (2 : ℝ) * 8 = 16 := by norm_num
  have e8 : (2 : ℝ) * 4 = 8 := by norm_num
  rw [← e16] at h2 ha
  have h3 := h2.mul (by norm_num) ha (by linarith)
  rw [← e8] at h3
  have hc8 := hc.exponent_mono (show (8 : ℝ) ≤ 16 by norm_num)
  rw [← e8] at hc8
  exact h3.mul (by norm_num) hc8 (by positivity)

/-- **The per-step fourth moment of one raw step** (at `p = 4`): uniformly in
bulk `E`, `1 ≤ l ≤ TW`, old birth indices `β₁, β₂ < l` and circular tag laws,
`E|(ι*𝒰*ξ)*Δ_l(ι*𝕊𝒰*ξ')|⁴ ≤ C/W²`. -/
theorem lintegral_stepIncr_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hFS : FullSourceMomentsEnergyUniformContract) (hδ : DeltaZeroLengthUniform)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (T : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ (Γ : Type) [MeasurableSpace Γ] (ν : Measure Γ) [IsProbabilityMeasure ν]
      (g₁ g₂ : Γ → Fin W → ℂ), Measurable g₁ → Measurable g₂ →
      ν.map g₁ = circularVectorLaw (Fin W) → ν.map g₂ = circularVectorLaw (Fin W) →
      ∀ l β₁ β₂ : ℕ, 1 ≤ l → β₁ < l → β₂ < l → (l : ℝ) ≤ T * W →
        ∫⁻ w, ‖bilinear (nearL b E W l β₁ w.1 (g₁ w.2)) (stepDelta b E W l w.1)
            (nearR b E W l β₂ w.1 (g₂ w.2))‖ₑ ^ 4 ∂((growthPathLaw W b).prod ν) ≤
          ENNReal.ofReal (C / (W : ℝ) ^ 2) := by
  obtain ⟨Cm, Cf, W₁, hCm, hCf, hdf⟩ := delta_fresh_bounds hGA hLp b hb0 hb κ hκ 4 (by norm_num)
  obtain ⟨A, Wf, hA, hfr⟩ := momBd_frame hFS hb0 hb hκ T (r := 16) (by norm_num)
  obtain ⟨Cδ, hCδ, hδT⟩ := hδ b hb0 hb κ 16 hκ (by norm_num)
  obtain ⟨Wδ, hδW⟩ := hδT T
  set B := (Cδ + 1) * A * A
  have hB : 0 ≤ B := by positivity
  set c₀ := 8 * (Cm ^ 4 + Cf ^ 4)
  have hc₀ : 0 ≤ c₀ := by positivity
  refine ⟨c₀ * B ^ 4, max (max W₁ Wf) (max Wδ 1), by positivity,
    fun W hW E hE Γ _ ν _ g₁ g₂ hg₁ hg₂ hl₁ hl₂ l β₁ β₂ hl hβ₁ hβ₂ hlT => ?_⟩
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hW)
  have hWf : Wf ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)
  have hWδ : Wδ ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hE' := hE
  obtain ⟨hE1, hE2⟩ := hE'
  have hκ2 : κ ≤ 2 := by linarith
  have hEl : -2 < E := by linarith
  have hEr : E < 2 := by linarith
  have hb1 : b < 1 := by linarith
  -- the moment inputs
  have hδl : MomBd ((growthPathLaw W b).prod ν)
      (fun w => jetDistance0 b E (pathX b E W l w.1)) 16 (Cδ / W) :=
    MomBd.comp_fst (ν := ν) ⟨((measurable_jetDistance0 (W := W) b E).comp
      (BlockBand.Transmission.PathJet.measurable_pathX b E l)).aestronglyMeasurable,
      hδW W hWδ E hE l hl hlT⟩
  have ha := momBd_nearL_of_frame hg₁ (hfr W hWf E hE l β₁ hβ₁ hlT Γ ν g₁ hg₁ hl₁)
  have hc := momBd_nearR_of_frame hg₂ (hfr W hWf E hE l β₂ hβ₂ hlT Γ ν g₂ hg₂ hl₂)
  have hZ := momBd_stepWeight hWr hCδ hA hδl ha hc
  -- the past/fresh split
  set μΩ := (growthPathLaw W b).prod ν
  set μP := (pastLaw W l b).prod ν
  set π : GrowthPath W × Γ → PastSample W l × Γ := fun w => (pastCoords W l w.1, w.2)
  set φ : GrowthPath W × Γ → LayerSample W .oneBlockOnePort := fun w => freshSample W l w.1
  have hπ : Measurable π := ((measurable_pastCoords W l).comp measurable_fst).prodMk measurable_snd
  have hφ : Measurable φ := (measurable_freshSample W l).comp measurable_fst
  have hmap : μΩ.map (fun w => (π w, φ w)) = μP.prod (freshLaw W b) := map_past_tag_fresh W l b ν
  have hmapπ : μΩ.map π = μP := by
    have := congrArg (fun μ => μ.map Prod.fst) hmap
    rw [Measure.map_map measurable_fst (hπ.prodMk hφ), Measure.map_fst_prod, measure_univ,
      one_smul] at this
    exact this
  have hext := measurable_extendPast (W := W) l
  set Xp : PastSample W l × Γ → Matrix (Fin W) (Fin W) ℂ := fun p => pathX b E W l (extendPast p.1)
  set ap : PastSample W l × Γ → Fin W → ℂ := fun p => nearL b E W l β₁ (extendPast p.1) (g₁ p.2)
  set cp : PastSample W l × Γ → Fin W → ℂ := fun p => nearR b E W l β₂ (extendPast p.1) (g₂ p.2)
  set D : PastSample W l × Γ → LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
    fun p f => freshDelta b E (Xp p) f
  have hXp : Measurable Xp :=
    (BlockBand.Transmission.PathJet.measurable_pathX b E l).comp (hext.comp measurable_fst)
  have hap : Measurable ap := measurable_nearL b E l β₁ (hext.comp measurable_fst)
    (hg₁.comp measurable_snd)
  have hcp : Measurable cp := measurable_nearR b E l β₂ (hext.comp measurable_fst)
    (hg₂.comp measurable_snd)
  have hDm : Measurable fun z : (PastSample W l × Γ) × LayerSample W .oneBlockOnePort =>
      D z.1 z.2 :=
    BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E (hXp.comp measurable_fst)
      measurable_snd
  have ea : ∀ w, ap (π w) = nearL b E W l β₁ w.1 (g₁ w.2) := fun w =>
    nearL_extendPast b E l β₁ w.1 _
  have ec : ∀ w, cp (π w) = nearR b E W l β₂ w.1 (g₂ w.2) := fun w =>
    nearR_extendPast b E l β₂ w.1 _
  have eX : ∀ w, Xp (π w) = pathX b E W l w.1 := fun w => pathX_extendPast b E l w.1
  have hpas : ∀ᵐ p ∂μP, (passiveY (Xp p)).PosSemidef := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := pastLaw W l b) (ν := ν)).ae
      (ae_pastLaw_hermitian W l b)
    filter_upwards [h] with p hp
    exact passiveY_pathX_extendPast hb1 hEl hEr hp
  set G : (PastSample W l × Γ) × LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun z =>
    ‖bilinear (ap z.1) (D z.1 z.2) (cp z.1)‖ₑ ^ 4
  have hGm : Measurable G :=
    (measurable_bilinear_jt (hap.comp measurable_fst) hDm (hcp.comp measurable_fst)).enorm.pow_const
      4
  set δp : PastSample W l × Γ → ℝ := fun p => jetDistance0 b E (Xp p)
  set s : PastSample W l × Γ → ℝ := fun p =>
    Cf * ((Real.sqrt W)⁻¹ + δp p) * vecNorm (ap p) * vecNorm (cp p)
  have hs0 : ∀ p, 0 ≤ s p := fun p => by
    have := vecNorm_nonneg (ap p); have := vecNorm_nonneg (cp p)
    have : 0 ≤ δp p := norm_nonneg _
    positivity
  have hstep := lintegral_bilinear_four_le μP (freshLaw W b) ap cp D hGm.aemeasurable
    (hpas.mono fun p hp => (hdf W hW₁ E hE _ hp).1) s hs0
    (hpas.mono fun p hp => by
      have := (hdf W hW₁ E hE _ hp).2.2 (ap p) (cp p)
      simpa using this)
  -- the weight on the past
  set Zp : PastSample W l × Γ → ℝ := fun p =>
    (1 + Real.sqrt W * δp p) * vecNorm (ap p) * vecNorm (cp p)
  have hZp0 : ∀ p, 0 ≤ Zp p := fun p => by
    have := vecNorm_nonneg (ap p); have := vecNorm_nonneg (cp p)
    have : 0 ≤ δp p := norm_nonneg _
    positivity
  have hsqW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hsq4 : Real.sqrt W ^ 4 = (W : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hW0.le]
  have hpt : ∀ᵐ p ∂μP, 8 * (‖bilinear (ap p) (matrixExpect (freshLaw W b) (D p)) (cp p)‖ₑ ^ 4 +
      ENNReal.ofReal (s p ^ 4)) ≤ ENNReal.ofReal (c₀ / (W : ℝ) ^ 2 * Zp p ^ 4) := by
    filter_upwards [hpas] with p hp
    have hδ0 : 0 ≤ δp p := norm_nonneg _
    have hna := vecNorm_nonneg (ap p)
    have hnc := vecNorm_nonneg (cp p)
    have hinv : (W : ℝ)⁻¹ ≤ (Real.sqrt W)⁻¹ := by
      refine inv_anti₀ hsqW ?_
      rw [Real.sqrt_le_left hW0.le]; nlinarith
    have hZs : ((Real.sqrt W)⁻¹ + δp p) * vecNorm (ap p) * vecNorm (cp p) =
        Zp p / Real.sqrt W := by
      simp only [Zp]; field_simp
    have hu : ‖bilinear (ap p) (matrixExpect (freshLaw W b) (D p)) (cp p)‖ ≤
        Cm * (Zp p / Real.sqrt W) := by
      refine (norm_bilinear_le _ _ _).trans ?_
      have hm := (hdf W hW₁ E hE _ hp).2.1
      rw [← hZs]
      calc vecNorm (ap p) * ‖matrixExpect (freshLaw W b) (D p)‖ * vecNorm (cp p)
          ≤ vecNorm (ap p) * (Cm * (δp p + (W : ℝ)⁻¹)) * vecNorm (cp p) := by gcongr
        _ ≤ vecNorm (ap p) * (Cm * ((Real.sqrt W)⁻¹ + δp p)) * vecNorm (cp p) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by linarith) hCm) hna) hnc
        _ = _ := by ring
    have hss : s p = Cf * (Zp p / Real.sqrt W) := by
      rw [← hZs]; simp only [s]; ring
    have hu4 : ‖bilinear (ap p) (matrixExpect (freshLaw W b) (D p)) (cp p)‖ₑ ^ 4 ≤
        ENNReal.ofReal ((Cm * (Zp p / Real.sqrt W)) ^ 4) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hu 4)
    have hZ0 := hZp0 p
    calc 8 * (‖bilinear (ap p) (matrixExpect (freshLaw W b) (D p)) (cp p)‖ₑ ^ 4 +
          ENNReal.ofReal (s p ^ 4))
        ≤ 8 * (ENNReal.ofReal ((Cm * (Zp p / Real.sqrt W)) ^ 4) +
            ENNReal.ofReal ((Cf * (Zp p / Real.sqrt W)) ^ 4)) := by
          rw [hss]; gcongr
      _ = ENNReal.ofReal (c₀ / (W : ℝ) ^ 2 * Zp p ^ 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          rw [mul_pow, mul_pow, div_pow, hsq4]
          simp only [c₀]; ring
  have hZpm : Measurable fun p => ENNReal.ofReal (c₀ / (W : ℝ) ^ 2 * Zp p ^ 4) := by
    have : Measurable δp := (measurable_jetDistance0 (W := W) b E).comp hXp
    simp only [Zp, vecNorm]
    fun_prop
  calc ∫⁻ w, ‖bilinear (nearL b E W l β₁ w.1 (g₁ w.2)) (stepDelta b E W l w.1)
          (nearR b E W l β₂ w.1 (g₂ w.2))‖ₑ ^ 4 ∂μΩ
      = ∫⁻ w, G (π w, φ w) ∂μΩ := by
        refine lintegral_congr fun w => ?_
        simp only [G, D, ea, ec, eX, stepDelta, φ]
    _ = ∫⁻ z, G z ∂(μP.prod (freshLaw W b)) := by
        rw [← hmap, lintegral_map hGm (hπ.prodMk hφ)]
    _ ≤ _ := hstep
    _ ≤ ∫⁻ p, ENNReal.ofReal (c₀ / (W : ℝ) ^ 2 * Zp p ^ 4) ∂μP := lintegral_mono_ae hpt
    _ = ∫⁻ w, ENNReal.ofReal (c₀ / (W : ℝ) ^ 2 * Zp (π w) ^ 4) ∂μΩ := by
        rw [← hmapπ, lintegral_map hZpm hπ]
    _ = ENNReal.ofReal (c₀ / (W : ℝ) ^ 2) *
          ∫⁻ w, ENNReal.ofReal (((1 + Real.sqrt W * jetDistance0 b E (pathX b E W l w.1)) *
            vecNorm (nearL b E W l β₁ w.1 (g₁ w.2)) *
            vecNorm (nearR b E W l β₂ w.1 (g₂ w.2))) ^ 4) ∂μΩ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun w => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        simp only [Zp, δp, ea, ec, eX]
    _ ≤ ENNReal.ofReal (c₀ / (W : ℝ) ^ 2) * ENNReal.ofReal (B ^ 4) := by
        gcongr
        refine lintegral_pow_le_of_momBd' (n := 4) (by norm_num) (by exact_mod_cast hZ) hB
          fun w => ?_
        have := vecNorm_nonneg (nearL b E W l β₁ w.1 (g₁ w.2))
        have := vecNorm_nonneg (nearR b E W l β₂ w.1 (g₂ w.2))
        have : 0 ≤ jetDistance0 b E (pathX b E W l w.1) := norm_nonneg _
        positivity
    _ = ENNReal.ofReal (c₀ * B ^ 4 / (W : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end BlockBand.SourceProcess.PhysApprox.B3.Four
