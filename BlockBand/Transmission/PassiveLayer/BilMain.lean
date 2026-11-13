module

public import BlockBand.Transmission.PassiveLayer.BilAux

/-!
# The `bilinear` clause of the passive bounds lemma

`bilinear_holds (hGA : Layers.GaussianAbsorptionContract) (hLp : Inputs.GaussianLpGradient)`
proves the field `PassiveBoundsStatement.bilinear`: for `p ≥ 1` there are `C, W₀` with
`‖u*(U - EU)v‖_p ≤ C W^{-1/2}‖u‖‖v‖` for `U = LL*` and `U = L(R₊ - c₀)L*`, uniformly in
`W ≥ W₀`, `E ∈ bulkInterval κ`, `w ∈ paramDisk b E`, passive `X`, vectors `u, v`.

Proof: `psi_centered`. For `ε_n = 1/(n+1)` the input `X - iε_n` is passive and the
functional is `C¹` in the Gaussian coordinates; the `L^p` gradient inequality and
`grad_psi_reg` give `‖ψ_n - Eψ_n‖_p ≤ C₀√p·√(12/W)·3‖u‖‖v‖·‖psiWeight‖_p`. The weight has
moments uniform in passive inputs (`moments_holds`, `weight_moms`). Then `ε_n ↓ 0`
(`tendsto_psiLayer_reg`) with Fatou for centered norms (`BilFatou`). The identifications
`u*LL*v = ψ` (everywhere) and `u*L(R₊ - c₀)L*v = ψ` (a.s., `RPlus`) and
`bilinear_sub_matrixExpect` finish the proof.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal

open BlockBand.Transmission

variable {W : ℕ}

theorem norm_rMap_le {n : Type} [Fintype n] [DecidableEq n] {θ : ℂ} (hθ : ‖θ‖ ≤ 1)
    {P : Matrix n n ℂ} (hP : ‖P‖ ≤ 1) (Γ G : Matrix n n ℂ) : ‖rMap θ P Γ G‖ ≤ ‖G‖ + ‖Γ‖ := by
  have hPn := norm_nonneg P
  have hg := norm_nonneg G
  have h1 : ‖P * G‖ ≤ ‖G‖ := (Matrix.l2_opNorm_mul _ _).trans (by nlinarith)
  have hPGP : ‖P * G * P‖ ≤ ‖G‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (by nlinarith [norm_nonneg (P * G)])
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  rw [norm_smul]
  nlinarith [norm_nonneg θ, norm_nonneg (P * G * P)]

/-- Letter moments at a passive input packaged as `MomBd`. -/
theorem letter_momBd {b : ℝ} {W : ℕ} {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ} {q C : ℝ}
    (h : eLpNorm (fun ω => ‖layerAt E w X ω‖) (ENNReal.ofReal q) (freshLaw W b) ≤ ENNReal.ofReal C ∧
      eLpNorm (fun ω => ‖kG11 E w X ω‖) (ENNReal.ofReal q) (freshLaw W b) ≤ ENNReal.ofReal C ∧
      eLpNorm (fun ω => ‖lAt E w X ω‖) (ENNReal.ofReal q) (freshLaw W b) ≤ ENNReal.ofReal C) :
    MomBd (freshLaw W b) (fun ω => ‖layerAt E w X ω‖) q (max C 0) ∧
      MomBd (freshLaw W b) (fun ω => ‖kG11 E w X ω‖) q (max C 0) ∧
      MomBd (freshLaw W b) (fun ω => ‖lAt E w X ω‖) q (max C 0) := by
  refine ⟨⟨(continuous_norm.measurable.comp (measurable_layerAt E w X)).aestronglyMeasurable,
    h.1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩,
    ⟨(continuous_norm.measurable.comp (measurable_kG11 E w X)).aestronglyMeasurable,
    h.2.1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩,
    ⟨(continuous_norm.measurable.comp (measurable_lAt E w X)).aestronglyMeasurable,
    h.2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩⟩

theorem measurable_psiLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (u v : Fin W → ℂ)
    (θ : ℂ) (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Measurable (psiLayer E w X u v θ Γ) :=
  ((continuous_psiMap θ (pTwo W) Γ).comp (continuous_const.prodMk
    (continuous_const.prodMk continuous_id))).measurable.comp (measurable_layerAt E w X)

/-- `ψ` and its gradient weight are dominated by the moment polynomials. -/
theorem psi_dominated (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (u v : Fin W → ℂ)
    {θ : ℂ} (hθ : ‖θ‖ ≤ 1)
    {Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ} {γ : ℝ}
    (hΓ : ‖Γ‖ ≤ γ) (ω : LayerSample W .oneBlockOnePort) :
    ‖psiLayer E w X u v θ Γ ω‖ ≤ (vecNorm u * vecNorm v) *
        (((‖kG11 E w X ω‖ + ‖lAt E w X ω‖) * (‖kG11 E w X ω‖ + ‖lAt E w X ω‖)) *
          (‖layerAt E w X ω‖ + γ)) ∧
      ‖psiWeight E w X Γ ω‖ ≤ ((‖kG11 E w X ω‖ + ‖lAt E w X ω‖) *
        (‖kG11 E w X ω‖ + ‖lAt E w X ω‖)) * (‖layerAt E w X ω‖ * (‖layerAt E w X ω‖ + γ)) := by
  have hq := norm_pK_mul_le E w X ω
  have hR := norm_rMap_le hθ norm_pTwo_le Γ (layerAt E w X ω)
  have hψ := norm_psiMap_le (pK w X) (layerAt E w X ω) (pTwo W) Γ θ u v
  have hΓ0 := norm_nonneg Γ
  have hq0 := norm_nonneg (pK w X * layerAt E w X ω)
  have hg := norm_nonneg (layerAt E w X ω)
  have hk := norm_nonneg (kG11 E w X ω)
  have hl := norm_nonneg (lAt E w X ω)
  have huv : 0 ≤ vecNorm u * vecNorm v := mul_nonneg (vecNorm_nonneg u) (vecNorm_nonneg v)
  have hψ' : ‖psiLayer E w X u v θ Γ ω‖ ≤ ‖pK w X * layerAt E w X ω‖ ^ 2 *
      ‖rMap θ (pTwo W) Γ (layerAt E w X ω)‖ * (vecNorm u * vecNorm v) := hψ
  have hrn := norm_nonneg (rMap θ (pTwo W) Γ (layerAt E w X ω))
  rw [psiWeight]
  generalize ‖pK w X * layerAt E w X ω‖ = q at *
  generalize ‖layerAt E w X ω‖ = g at *
  generalize ‖kG11 E w X ω‖ = k at *
  generalize ‖lAt E w X ω‖ = l at *
  generalize ‖rMap θ (pTwo W) Γ (layerAt E w X ω)‖ = r at *
  generalize ‖Γ‖ = c at *
  generalize vecNorm u * vecNorm v = U at *
  generalize ‖psiLayer E w X u v θ Γ ω‖ = F at *
  have hsq : q ^ 2 ≤ (k + l) * (k + l) := by nlinarith
  constructor
  · have h1 : q ^ 2 * r ≤ (k + l) * (k + l) * (g + γ) :=
      mul_le_mul hsq (by linarith) hrn (by positivity)
    nlinarith
  · rw [Real.norm_of_nonneg (by positivity)]
    have h2 : g * (g + c) ≤ g * (g + γ) := by nlinarith
    have := mul_le_mul hsq h2 (by positivity) (by positivity)
    linarith [show q ^ 2 * g * (g + c) = q ^ 2 * (g * (g + c)) by ring]

/-- The body of `Inputs.GaussianLpGradient` with a fixed constant `C₀`. -/
def LpGradientBody (C₀ : ℝ) : Prop :=
  ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
    (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
      eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
          (gaussianProduct v) ≤
        ENNReal.ofReal (C₀ * Real.sqrt p) *
          eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v)

/-- **Centered `L^p` bound of the resolvent functional `ψ`**, uniformly in passive `X`. -/
theorem psi_centered (hGA : GaussianAbsorptionContract) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hLp : LpGradientBody C₀) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
      ∀ θ : ℂ, ‖θ‖ ≤ 1 →
      ∀ Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
        ‖Γ‖ ≤ 1 + 1 / ((1 - b) * κ) →
        MemLp (psiLayer E w X u v θ Γ) (ENNReal.ofReal p) (freshLaw W b) ∧
        eLpNorm (fun ω => psiLayer E w X u v θ Γ ω -
            ∫ ω', psiLayer E w X u v θ Γ ω' ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * (vecNorm u * vecNorm v)) := by
  set γ := 1 + 1 / ((1 - b) * κ)
  have h1b : 0 < 1 - b := by linarith
  have hγ : 0 ≤ γ := by positivity
  have hp0 : 0 < p := by linarith
  obtain ⟨Cm', W₀m, hm⟩ := moments_holds hGA b hb0 hb κ hκ (8 * p) (by linarith)
  set Cm := max Cm' 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  set CW := (2 * Cm) * (2 * Cm) * (Cm * (Cm + γ))
  set CQ := (2 * Cm) * (2 * Cm) * (Cm + γ)
  have hCW : 0 ≤ CW := by positivity
  have hCQ : 0 ≤ CQ := by positivity
  refine ⟨2 * (C₀ * Real.sqrt p) * (Real.sqrt 12 * 3) * CW, max W₀m 1, by positivity, ?_⟩
  intro W hW E hE w hw X hY u v θ hθ Γ hΓ
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hWm : W₀m ≤ W := le_of_max_le_left hW
  obtain ⟨hwim, -, -, -⟩ := disk_bounds hb0 hb hκ hE hw
  have hwpos : 0 < w.im := lt_of_lt_of_le (by positivity) hwim
  set U := vecNorm u * vecNorm v
  have hU : 0 ≤ U := mul_nonneg (vecNorm_nonneg u) (vecNorm_nonneg v)
  -- moments at any passive input
  have hpass : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      MemLp (psiLayer E w X' u v θ Γ) (ENNReal.ofReal p) (freshLaw W b) ∧
      eLpNorm (psiLayer E w X' u v θ Γ) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (U * CQ) ∧
      eLpNorm (psiWeight E w X' Γ) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal CW := by
    intro X' hY'
    obtain ⟨hg, hk, hl⟩ := letter_momBd (hm W hWm E hE w hw X' hY').2
    obtain ⟨hA1, hA2⟩ := weight_moms hp hCm hγ hg hk hl
    have hdom := fun ω => psi_dominated E w X' u v hθ hΓ ω
    have hψm := (measurable_psiLayer E w X' u v θ Γ).aestronglyMeasurable (μ := freshLaw W b)
    have hψ : eLpNorm (psiLayer E w X' u v θ Γ) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (U * CQ) :=
      (eLpNorm_mono_ae_real hψm (ae_of_all _ fun ω => (hdom ω).1)).trans (hA2.const_mul hU).2
    refine ⟨lt_of_le_of_lt hψ ENNReal.ofReal_lt_top, hψ, ?_⟩
    exact (eLpNorm_mono_ae_real (measurable_psiWeight E w X' Γ).aestronglyMeasurable
      (ae_of_all _ fun ω => (hdom ω).2)).trans hA1.2
  obtain ⟨hMem, -, -⟩ := hpass X hY
  set k := Real.sqrt (3 * (4 / W)) * 3 * U
  have hk : 0 ≤ k := by positivity
  set B := ENNReal.ofReal (C₀ * Real.sqrt p) * (ENNReal.ofReal k * ENNReal.ofReal CW)
  have hfix : ∀ n, eLpNorm (fun ω => psiLayer E w (regX X (epsN n)) u v θ Γ ω -
      ∫ ω', psiLayer E w (regX X (epsN n)) u v θ Γ ω' ∂freshLaw W b) (ENNReal.ofReal p)
        (freshLaw W b) ≤ B := by
    intro n
    have hYn := regX_posSemidef hY (epsN_pos n).le
    obtain ⟨hMn, -, hwn⟩ := hpass _ hYn
    exact (centered_reg_le hLp hb0 hb hW1 E hwpos hY (epsN_pos n) u v hθ Γ hp hMn).trans
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hwn))
  have hmean : ∀ n, ‖∫ ω', psiLayer E w (regX X (epsN n)) u v θ Γ ω' ∂freshLaw W b‖ ≤ U * CQ := by
    intro n
    obtain ⟨hMn, hn, -⟩ := hpass _ (regX_posSemidef hY (epsN_pos n).le)
    have h1 := (enorm_integral_le_eLpNorm (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by
      simpa using ENNReal.ofReal_le_ofReal hp) hMn.aestronglyMeasurable).trans hn
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hlim : ∀ᵐ ω ∂freshLaw W b, Tendsto (fun n => psiLayer E w (regX X (epsN n)) u v θ Γ ω)
      atTop (𝓝 (psiLayer E w X u v θ Γ ω)) := by
    filter_upwards [ae_good W hb0 hW1] with ω hω
    exact tendsto_psiLayer_reg E w X ω ((isUnit_iff_isUnit_det _).mpr
      (layer_schur E hwpos hY hω.1 hω.2).1) u v θ Γ
  have hF := eLpNorm_centered_le_of_tendsto (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by
      simpa using ENNReal.ofReal_le_ofReal hp)
    (fun n => (measurable_psiLayer E w _ u v θ Γ).aestronglyMeasurable)
    (measurable_psiLayer E w X u v θ Γ).aestronglyMeasurable
    (hMem.integrable (by simpa using ENNReal.ofReal_le_ofReal hp)) hlim hmean hfix
  refine ⟨hMem, hF.trans (le_of_eq ?_)⟩
  have hs : Real.sqrt (3 * (4 / (W : ℝ))) = Real.sqrt 12 / Real.sqrt W := by
    rw [show 3 * (4 / (W : ℝ)) = 12 / W by ring, Real.sqrt_div' _ (Nat.cast_nonneg W)]
  simp only [B]
  rw [← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_mul (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  simp only [k, hs]
  ring

/-- **The `bilinear` clause of the passive bounds lemma**, from `GaussianAbsorptionContract` and
`GaussianLpGradient` (explicit hypotheses). -/
theorem bilinear_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (uAt E w X ω - matrixExpect (freshLaw W b) (uAt E w X)) v)
            (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => bilinear u (transportedFAt b E w X ω -
            matrixExpect (freshLaw W b) (transportedFAt b E w X)) v)
            (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) := by
  intro b hb0 hb κ hκ p hp
  obtain ⟨C₀, hC₀, hLp'⟩ := hLp
  obtain ⟨C, W₀, -, h⟩ := psi_centered hGA hC₀ hLp' hb0 hb hκ hp
  have h1b : 0 < 1 - b := by linarith
  have hγ1 : (1 : ℝ) ≤ 1 + 1 / ((1 - b) * κ) := by
    have : 0 ≤ 1 / ((1 - b) * κ) := by positivity
    linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  refine ⟨C, max W₀ 1, fun W hW E hE w hw X hY u v => ?_⟩
  have hW0 : W₀ ≤ W := le_of_max_le_left hW
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  obtain ⟨hwim, -, -, -⟩ := disk_bounds hb0 hb hκ hE hw
  have hwpos : 0 < w.im := lt_of_lt_of_le (by positivity) hwim
  have hrw : C / Real.sqrt W * vecNorm u * vecNorm v = C / Real.sqrt W * (vecNorm u * vecNorm v) :=
    by ring
  rw [hrw]
  have hΓ1 : ‖pTwo W‖ ≤ 1 + 1 / ((1 - b) * κ) := norm_pTwo_le.trans hγ1
  have hΓ2 : ‖-cZero b E • pTwo W‖ ≤ 1 + 1 / ((1 - b) * κ) := by
    rw [norm_smul, norm_neg]
    have := norm_cZero_le hb hκ hE
    have : 0 ≤ 1 / ((1 - b) * κ) := by positivity
    nlinarith [norm_pTwo_le (W := W), norm_nonneg (cZero b E)]
  constructor
  · have hid : ∀ u' v' ω, bilinear u' (uAt E w X ω) v' = psiLayer E w X u' v' 0 (pTwo W) ω :=
      fun u' v' ω => bilinear_uAt_eq E w X ω u' v'
    have hint : ∀ x y, Integrable (fun ω => uAt E w X ω x y) (freshLaw W b) := by
      intro x y
      have := ((h W hW0 E hE w hw X hY (Pi.single x 1) (Pi.single y 1) 0 (by simp) _ hΓ1).1).integrable
        hp1
      refine this.congr (ae_of_all _ fun ω => ?_)
      rw [← hid, bilinear_single]
    simp only [bilinear_sub_matrixExpect _ hint, hid]
    exact (h W hW0 E hE w hw X hY u v 0 (by simp) _ hΓ1).2
  · have hR : ∀ᵐ ω ∂freshLaw W b, ∀ u' v' : Fin W → ℂ,
        bilinear u' (transportedFAt b E w X ω) v' =
          psiLayer E w X u' v' 1 (-cZero b E • pTwo W) ω := by
      filter_upwards [ae_g22_eq_Rplus hb0 hb hW1 E hwpos hY] with ω hω u' v'
      exact bilinear_transportedFAt_eq b E w X ω u' v' hω.symm
    have hint : ∀ x y, Integrable (fun ω => transportedFAt b E w X ω x y) (freshLaw W b) := by
      intro x y
      have := ((h W hW0 E hE w hw X hY (Pi.single x 1) (Pi.single y 1) 1 (by simp) _ hΓ2).1).integrable
        hp1
      refine this.congr ?_
      filter_upwards [hR] with ω hω
      rw [← hω, bilinear_single]
    simp only [bilinear_sub_matrixExpect _ hint]
    have hF : (fun ω => bilinear u (transportedFAt b E w X ω) v -
        ∫ ω', bilinear u (transportedFAt b E w X ω') v ∂freshLaw W b) =ᵐ[freshLaw W b]
        fun ω => psiLayer E w X u v 1 (-cZero b E • pTwo W) ω -
          ∫ ω', psiLayer E w X u v 1 (-cZero b E • pTwo W) ω' ∂freshLaw W b := by
      have hi : ∫ ω', bilinear u (transportedFAt b E w X ω') v ∂freshLaw W b =
          ∫ ω', psiLayer E w X u v 1 (-cZero b E • pTwo W) ω' ∂freshLaw W b :=
        integral_congr_ae (by filter_upwards [hR] with ω hω; exact hω u v)
      filter_upwards [hR] with ω hω
      rw [hi, hω u v]
    rw [eLpNorm_congr_ae hF]
    exact (h W hW0 E hE w hw X hY u v 1 (by simp) _ hΓ2).2

end BlockBand.Transmission.PassiveLayer
