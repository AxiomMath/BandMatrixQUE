module

public import BlockBand.SourceProcess.SmallLeak.GrowthCrude
public import BlockBand.SourceProcess.FullSource.WeightedStep
public import BlockBand.SourceProcess.FullSource.WeightAlgebra
public import BlockBand.SourceProcess.FullSource.MomentStep

/-!
# The weighted one-layer step of the omitted flux

This is the analogue of `current_layer_step` for the omitted flux.

With `t = fluxAt`, `t₊ = max(fluxNext, 0)`, `E t₊ ≤ (1 + L(δ + W⁻¹))t` (`flux_fresh_mean`),
`t₊ ≤ (1 + ‖Δ‖/(2η))² t` (`fluxNext_le`) and the fresh scalar error `ξ`:
`E[(1 + K(ρδ + C_m/W² + ξ))t₊] ≤ (1 + α/W)(1 + Kδ)t` (`flux_weighted_step`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveLayer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- The rate of the weighted flux step. -/
def alphaG (K Cm La Cf C4 : ℝ) : ℝ :=
  K * Cm + La + K * La + La * (K * Cm) + K * Cm * La + K * (Cf ^ 2 + C4) / 2

theorem alphaG_nonneg {K Cm La Cf C4 : ℝ} (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (hLa : 0 ≤ La)
    (hC4 : 0 ≤ C4) : 0 ≤ alphaG K Cm La Cf C4 := by
  unfold alphaG; positivity

/-- **The weighted one-layer step of the omitted flux.** -/
theorem flux_weighted_step {b E : ℝ} (hη : 0 < etaZ b E)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) (hW : (1 : ℝ) ≤ W)
    (hΔ : ∀ x y, Integrable (fun f => freshDelta b E (nearSchur (boundaryZ b E) XX) f x y)
      (freshLaw W b))
    (hmeasΔ : Measurable (freshDelta b E (nearSchur (boundaryZ b E) XX)))
    {La : ℝ} (hLa : 0 ≤ La)
    (hmean : ‖matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))‖ /
      etaZ b E ≤ La * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + (W : ℝ)⁻¹))
    {C4 : ℝ} (hC4 : 0 ≤ C4)
    (h4i : Integrable (fun f => (1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ /
      (2 * etaZ b E)) ^ 4) (freshLaw W b))
    (h4 : ∫ f, (1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ / (2 * etaZ b E)) ^ 4
      ∂freshLaw W b ≤ C4)
    (hpos : ∀ᵐ f ∂freshLaw W b, 0 ≤ fluxNext b E XX A f)
    {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hξ : eLpNorm (freshXi b E (nearSchur (boundaryZ b E) XX)) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (Cf / W))
    {K ρ Cm d : ℝ} (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hCm : 0 ≤ Cm)
    (hKL : La ≤ K * (1 - ρ) / 2) (hd1 : d ≤ 1) (hρLd : ρ * La * d ≤ (1 - ρ) / 2)
    (hδ : jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d) :
    ∫⁻ f, ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
        Cm / (W : ℝ) ^ 2 + freshXi b E (nearSchur (boundaryZ b E) XX) f)) *
        max (fluxNext b E XX A f) 0) ∂freshLaw W b ≤
      ENNReal.ofReal ((1 + alphaG K Cm La Cf C4 / W) *
        ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) XX)) * fluxAt b E XX A)) := by
  set μ := freshLaw W b
  set δ := jetDistance0 b E (nearSchur (boundaryZ b E) XX)
  set ξ := freshXi b E (nearSchur (boundaryZ b E) XX)
  set t := fluxAt b E XX A
  set Δ := freshDelta b E (nearSchur (boundaryZ b E) XX)
  set tp : LayerSample W .oneBlockOnePort → ℝ := fun f => max (fluxNext b E XX A f) 0
  set D : LayerSample W .oneBlockOnePort → ℝ := fun f => (1 + ‖Δ f‖ / (2 * etaZ b E)) ^ 2
  have hW0 : (0 : ℝ) < W := by linarith
  have ht : 0 ≤ t := fluxAt_nonneg b E XX hA
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have htp : ∀ f, 0 ≤ tp f := fun f => le_max_right _ _
  have hD0 : ∀ f, 0 ≤ D f := fun f => sq_nonneg _
  have hcrude : ∀ f, tp f ≤ D f * t := fun f =>
    max_le (fluxNext_le hη hXX hA f) (mul_nonneg (hD0 f) ht)
  have hmtp : Measurable tp := (measurable_fluxNext b E XX A).max measurable_const
  have hmD : Measurable D :=
    ((measurable_const.add (hmeasΔ.norm.div_const _)).pow_const 2)
  -- integrability
  have hDi : Integrable D μ := by
    refine Integrable.mono' ((integrable_const 1).add h4i) hmD.aestronglyMeasurable
      (Filter.Eventually.of_forall fun f => ?_)
    rw [Real.norm_of_nonneg (hD0 f)]
    have hy : ∀ y : ℝ, y ^ 2 ≤ 1 + y ^ 4 := fun y => by nlinarith [sq_nonneg (y ^ 2 - 1)]
    exact hy _
  have hi1 : Integrable tp μ :=
    Integrable.mono' (hDi.mul_const t) hmtp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun f => by
        rw [Real.norm_of_nonneg (htp f)]; exact hcrude f)
  have hsq : ∀ f, tp f ^ 2 ≤ (1 + ‖Δ f‖ / (2 * etaZ b E)) ^ 4 * t ^ 2 := fun f => by
    have := pow_le_pow_left₀ (htp f) (hcrude f) 2
    calc tp f ^ 2 ≤ (D f * t) ^ 2 := this
      _ = _ := by simp only [D]; ring
  have hi2 : Integrable (fun f => tp f ^ 2) μ :=
    Integrable.mono' (h4i.mul_const (t ^ 2)) (hmtp.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun f => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hsq f)
  have hb2 : ∫ f, tp f ^ 2 ∂μ ≤ C4 * t ^ 2 := by
    refine (integral_mono hi2 (h4i.mul_const (t ^ 2)) hsq).trans ?_
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  -- the first moment
  have hb1 : ∫ f, tp f ∂μ ≤ t * (1 + La * (δ + (W : ℝ)⁻¹)) := by
    have e : ∫ f, tp f ∂μ = ∫ f, fluxNext b E XX A f ∂μ :=
      integral_congr_ae (hpos.mono fun f h => max_eq_left h)
    have hm : ∫ f, fluxNext b E XX A f ∂μ ≤
        (1 + ‖matrixExpect μ Δ‖ / etaZ b E) * t := flux_fresh_mean hη hXX hA hΔ
    rw [e]
    refine hm.trans ?_
    rw [mul_comm t]
    exact mul_le_mul_of_nonneg_right (by linarith) ht
  -- the fresh scalar error
  obtain ⟨hiξ, hbξ⟩ := integral_abs_pow_le (ν := μ) (f := ξ) (n := 2) (by norm_num)
    (div_nonneg hCf hW0.le) ⟨(measurable_freshXi b E _).aestronglyMeasurable, by exact_mod_cast hξ⟩
  have hsqξ : (fun f => |ξ f| ^ 2) = fun f => ξ f ^ 2 := by funext f; exact sq_abs _
  rw [hsqξ] at hiξ hbξ
  set A₀ := 1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2)
  have hA0 : 0 ≤ A₀ := by positivity
  rcases ht.eq_or_lt with h0 | hpos'
  · have hz : ∀ f, tp f = 0 := fun f =>
      le_antisymm ((hcrude f).trans (by rw [← h0, mul_zero])) (htp f)
    have : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f)) =
        fun _ => 0 := by funext f; rw [hz f, mul_zero, ENNReal.ofReal_zero]
    show ∫⁻ f, ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f) ∂μ ≤ _
    rw [this, lintegral_zero]; exact bot_le
  have hl : 0 < (W : ℝ) * t := mul_pos hW0 hpos'
  have hint_eq : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f)) =
      fun f => ENNReal.ofReal ((A₀ + K * ξ f) * tp f ^ 1) := by
    funext f; congr 1; simp only [A₀, pow_one]; ring
  show ∫⁻ f, ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f) ∂μ ≤ _
  rw [hint_eq]
  refine (lintegral_weighted_le (n := 1) hA0 hK hl htp hmtp (by simpa using hi1) hiξ
    (by simpa using hi2) (by simpa using hb1) hbξ (by simpa using hb2) (by positivity)
    (sq_nonneg _) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the arithmetic
  have hAle : A₀ ≤ 1 + K * ρ * δ + K * Cm / W := by
    have : Cm / (W : ℝ) ^ 2 ≤ Cm / W := div_le_div_of_nonneg_left hCm hW0 (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_left this hK
    have e : A₀ = 1 + K * ρ * δ + K * (Cm / (W : ℝ) ^ 2) := by simp only [A₀]; ring
    have e2 : K * (Cm / W) = K * Cm / W := by ring
    linarith
  have hΛ : 1 + La * (δ + (W : ℝ)⁻¹) = 1 + La * δ + La / W := by ring
  have hab := weight_absorb (K := K) (ρ := ρ) (L := La) (d := d) (δ := δ) (a₁ := K * Cm)
    (a₂ := La) (e := K * (Cf ^ 2 + C4) / 2) (W := (W : ℝ)) hK hρ0 hρ1 hLa hKL hd1 hρLd hδ0 hδ
    (mul_nonneg hK hCm) hLa (by positivity) hW
  have h1 : A₀ * (1 + La * (δ + (W : ℝ)⁻¹)) ≤ (1 + K * ρ * δ + K * Cm / W) *
      (1 + La * δ + La / W) := by
    rw [hΛ]; exact mul_le_mul_of_nonneg_right hAle (by positivity)
  have hcross : K / 2 * ((W : ℝ) * t * (Cf / W) ^ 2 + C4 * t ^ 2 / ((W : ℝ) * t)) =
      K * (Cf ^ 2 + C4) / 2 / W * t := by
    field_simp
  rw [hcross]
  have e : alphaG K Cm La Cf C4 = K * Cm + La + K * La + La * (K * Cm) + K * Cm * La +
      K * (Cf ^ 2 + C4) / 2 := rfl
  rw [e]
  have key : A₀ * (1 + La * (δ + (W : ℝ)⁻¹)) + K * (Cf ^ 2 + C4) / 2 / W ≤
      (1 + K * δ) * (1 + (K * Cm + La + K * La + La * (K * Cm) + K * Cm * La +
        K * (Cf ^ 2 + C4) / 2) / W) := by
    have : K * (Cf ^ 2 + C4) / 2 / W = K * (Cf ^ 2 + C4) / 2 / W := rfl
    linarith
  nlinarith [mul_le_mul_of_nonneg_right key ht]

end BlockBand.SourceProcess.SmallLeak
