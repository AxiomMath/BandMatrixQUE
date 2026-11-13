module

public import BlockBand.SourceProcess.FullSource.WeightedStep
public import BlockBand.Transmission.PassiveCovariance.Step3

/-!
# The first-moment weighted layer step of a positive carrier

The lemma `weighted_layer_step` is written for the exponents `n ≥ 2`; here is the exponent `n = 1`
for an arbitrary deterministic `Y ⪰ 0` (`Y = SᴴS`, as in `tagPlus`): with `h₊ = W⁻¹Re Tr(NᴴYN)`,
`E h₊ = h + W⁻¹Re Tr(Y E𝓔) ≤ (1 + c)h`, `c = C_a(δ + W⁻²)`, and the fresh cross term
`ξh₊ ≤ (Whξ² + h₊²/(Wh))/2` with `E h₊² ≤ C_N⁴h²`. The weight `1 + Kδ` absorbs `c` (`weight_absorb`
with `L = C_a`):
`E[(1 + K(ρδ + C_m/W² + ξ))h₊] ≤ (1 + α₁/W)(1 + Kδ)h` (`current_layer_step`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- The transported carrier mass `h₊ = W⁻¹Re Tr(NᴴYN)`. -/
def carPlus (b E : ℝ) (XX Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (f : LayerSample W .oneBlockOnePort) : ℝ :=
  (W : ℝ)⁻¹ * ((freshTransport b E XX f)ᴴ * Y * freshTransport b E XX f).trace.re

theorem carPlus_factor (b E : ℝ) (XX S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (f : LayerSample W .oneBlockOnePort) : carPlus b E XX (Sᴴ * S) f = tagPlus b E XX S f := by
  rw [carPlus, tagPlus, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem carPlus_nonneg (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : Y.PosSemidef)
    (f : LayerSample W .oneBlockOnePort) : 0 ≤ carPlus b E XX Y f := by
  obtain ⟨S, rfl⟩ := exists_conjTranspose_mul_self hY
  rw [carPlus_factor]; exact tagPlus_nonneg _ _ _ _ _

/-- The rate `α₁` of the first-moment step. -/
def alphaOne (K Cm Ca Cf CN : ℝ) : ℝ :=
  K * Cm + Ca + K * Ca + Ca * (K * Cm) + K * Cm * Ca + K * (Cf ^ 2 + CN ^ (2 * (2 * 1))) / 2

theorem alphaOne_nonneg {K Cm Ca Cf CN : ℝ} (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (hCa : 0 ≤ Ca)
    (hCN : 0 ≤ CN) : 0 ≤ alphaOne K Cm Ca Cf CN := by
  unfold alphaOne; positivity

/-- **The first-moment weighted layer step of a positive carrier.** -/
theorem current_layer_step {b E : ℝ} (XX Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hY : Y.PosSemidef) (hW : (1 : ℝ) ≤ W)
    {Ca C₂ CN₂ CN Cf Cm K ρ d : ℝ} (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂)
    (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm) (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hKL : Ca ≤ K * (1 - ρ) / 2) (hd1 : d ≤ 1) (hρLd : ρ * Ca * d ≤ (1 - ρ) / 2)
    (hδ : jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d)
    (hmean : ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤
      Ca * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2))
    (hfl₂ : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal (C₂ / Real.sqrt W * vecNorm u * vecNorm v))
    (hN₂ : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) ≤ ENNReal.ofReal CN₂)
    (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * (2 * 1) : ℕ) : ℝ))
      (freshLaw W b) ≤ ENNReal.ofReal CN)
    (hξ : eLpNorm (freshXi b E (nearSchur (boundaryZ b E) XX)) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (Cf / W)) :
    ∫⁻ f, ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
        Cm / (W : ℝ) ^ 2 + freshXi b E (nearSchur (boundaryZ b E) XX) f)) *
        carPlus b E XX Y f) ∂freshLaw W b ≤
      ENNReal.ofReal ((1 + alphaOne K Cm Ca Cf CN / W) *
        ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) XX)) *
          ((W : ℝ)⁻¹ * Y.trace.re))) := by
  obtain ⟨S, rfl⟩ := exists_conjTranspose_mul_self hY
  simp only [carPlus_factor]
  set μ := freshLaw W b
  set δ := jetDistance0 b E (nearSchur (boundaryZ b E) XX)
  set ξ := freshXi b E (nearSchur (boundaryZ b E) XX)
  set t := (W : ℝ)⁻¹ * (Sᴴ * S).trace.re
  set tp := tagPlus b E XX S
  have hW0 : (0 : ℝ) < W := by linarith
  have hw : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hT := trace_factor_re_nonneg S
  have ht : 0 ≤ t := mul_nonneg hw hT
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have htp : ∀ f, 0 ≤ tp f := tagPlus_nonneg b E XX S
  set A := 1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2)
  have hA0 : 0 ≤ A := by positivity
  set c := Ca * (δ + ((W : ℝ)⁻¹) ^ 2)
  have hc0 : 0 ≤ c := by positivity
  -- the first moment: `E t₊ ≤ t(1 + c)`
  have hN₂' : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * 1 : ℕ) : ℝ)) μ ≤
      ENNReal.ofReal (max CN₂ 0) :=
    (by simpa using hN₂ : eLpNorm (fun ω => ‖freshTransport b E XX ω‖)
      (ENNReal.ofReal ((2 * 1 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal CN₂).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  obtain ⟨hi1', -⟩ := tagStep_crude_moment (b := b) (E := E) XX S (q := 1) le_rfl
    (le_max_right _ _) hN₂'
  have hi1 : Integrable tp μ := by simpa using hi1'
  have hmw : Measurable fun ω => wardNoise b E XX ω :=
    measurable_wardNoise_comp b E measurable_const measurable_id
  obtain ⟨-, -, habs, -⟩ := trace_noise (ν := μ) (wardNoise b E XX) hmw
    (integrable_wardNoise_entry (b := b) (E := E) XX hN₂) S hmean (q := 2) (by norm_num)
    (by positivity : 0 ≤ C₂ / Real.sqrt W) hfl₂
  set y : LayerSample W .oneBlockOnePort → ℝ := fun ω => (Sᴴ * S * wardNoise b E XX ω).trace.re
  have htpy : ∀ f, tp f = t + (W : ℝ)⁻¹ * y f := fun f => tagPlus_eq b E XX S f
  have hiy : Integrable (fun f => (W : ℝ)⁻¹ * y f) μ :=
    (hi1.sub (integrable_const t)).congr (Filter.Eventually.of_forall fun f => by
      show tp f - t = _; rw [htpy f]; ring)
  have hb1 : ∫ f, tp f ^ 1 ∂μ ≤ t ^ 1 * (1 + c) := by
    simp only [pow_one]
    have hI : ∫ f, (t + (W : ℝ)⁻¹ * y f) ∂μ = t + (W : ℝ)⁻¹ * ∫ f, y f ∂μ := by
      rw [integral_add (integrable_const t) hiy, integral_const_mul (W : ℝ)⁻¹ y, integral_const]
      simp
    rw [show (fun f => tp f) = fun f => t + (W : ℝ)⁻¹ * y f from funext htpy, hI]
    have : (W : ℝ)⁻¹ * ∫ f, y f ∂μ ≤ (W : ℝ)⁻¹ * (c * (Sᴴ * S).trace.re) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans habs) hw
    nlinarith
  -- the second moment and the fresh scalar error
  obtain ⟨hi2, hb2⟩ := tagStep_crude_moment (b := b) (E := E) XX S (q := 2) (by norm_num) hCN hN
  have hmtp : Measurable tp := measurable_tagPlus b E XX S
  have hmξ : Measurable ξ := measurable_freshXi b E _
  obtain ⟨hiξ, hbξ⟩ := integral_abs_pow_le (ν := μ) (f := ξ) (n := 2) (by norm_num)
    (div_nonneg hCf hW0.le) ⟨hmξ.aestronglyMeasurable, by exact_mod_cast hξ⟩
  have hsqξ : (fun f => |ξ f| ^ 2) = fun f => ξ f ^ 2 := by funext f; exact sq_abs _
  rw [hsqξ] at hiξ hbξ
  -- the one-step factor
  have hWinv : ((W : ℝ)⁻¹) ^ 2 ≤ 1 / W := by
    rw [inv_pow, ← one_div]; exact one_div_le_one_div_of_le hW0 (by nlinarith)
  have hΛ : 1 + c ≤ 1 + Ca * δ + Ca / W := by
    have := mul_le_mul_of_nonneg_left hWinv hCa
    simp only [c]; rw [mul_add]; linarith [show Ca * (1 / W) = Ca / W by ring]
  have hAle : A ≤ 1 + K * ρ * δ + K * Cm / W := by
    have : Cm / (W : ℝ) ^ 2 ≤ Cm / W := div_le_div_of_nonneg_left hCm hW0 (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_left this hK
    have e : A = 1 + K * ρ * δ + K * (Cm / (W : ℝ) ^ 2) := by simp only [A]; ring
    have e2 : K * (Cm / W) = K * Cm / W := by ring
    linarith
  have hfinal : A * (1 + c) + K * (Cf ^ 2 + CN ^ (2 * (2 * 1))) / 2 / W ≤
      (1 + K * δ) * (1 + alphaOne K Cm Ca Cf CN / W) := by
    have h1 : A * (1 + c) ≤ (1 + K * ρ * δ + K * Cm / W) * (1 + Ca * δ + Ca / W) :=
      mul_le_mul hAle hΛ (by positivity)
        (by have := mul_nonneg (mul_nonneg hK hρ0) hδ0; positivity)
    have h2 := weight_absorb (K := K) (ρ := ρ) (L := Ca) (d := d) (δ := δ)
      (a₁ := K * Cm) (a₂ := Ca) (e := K * (Cf ^ 2 + CN ^ (2 * (2 * 1))) / 2)
      (W := (W : ℝ)) hK hρ0 hρ1 hCa hKL hd1 hρLd hδ0 hδ (mul_nonneg hK hCm) hCa
      (div_nonneg (mul_nonneg hK (add_nonneg (sq_nonneg Cf) (pow_nonneg hCN _))) (by norm_num))
      hW
    have e : alphaOne K Cm Ca Cf CN = K * Cm + Ca + K * Ca + Ca * (K * Cm) + K * Cm * Ca +
        K * (Cf ^ 2 + CN ^ (2 * (2 * 1))) / 2 := rfl
    rw [e]
    linarith
  rcases ht.eq_or_lt with h0 | hpos
  · have hz : ∀ f, tp f = 0 := fun f => le_antisymm
      ((tagStep_crude b E XX S f).trans
        (by rw [show (W : ℝ)⁻¹ * (Sᴴ * S).trace.re = 0 from h0.symm, mul_zero])) (htp f)
    have : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f)) =
        fun _ => 0 := by
      funext f; rw [hz f, mul_zero, ENNReal.ofReal_zero]
    rw [this, lintegral_zero]
    exact bot_le
  have hl : 0 < (W : ℝ) * t ^ 1 := mul_pos hW0 (pow_pos hpos 1)
  have hint_eq : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f)) =
      fun f => ENNReal.ofReal ((A + K * ξ f) * tp f ^ 1) := by
    funext f; congr 1; simp only [A, pow_one]; ring
  rw [hint_eq]
  have hi2' : Integrable (fun f => tp f ^ (2 * 1)) μ := hi2
  have hb2' : ∫ f, tp f ^ (2 * 1) ∂μ ≤ CN ^ (2 * (2 * 1)) * t ^ (2 * 1) := hb2
  refine (lintegral_weighted_le (n := 1) hA0 hK hl htp hmtp (by simpa using hi1) hiξ hi2' hb1 hbξ
    hb2' (by positivity) (sq_nonneg _)
    (mul_nonneg (pow_nonneg hCN _) (pow_nonneg ht _))).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := weighted_layer_real (n := 1) hW0 hpos hfinal
  have e : (1 + alphaOne K Cm Ca Cf CN / W) * ((1 + K * δ) * t) =
      (1 + K * δ) * (1 + alphaOne K Cm Ca Cf CN / W) * t ^ 1 := by ring
  rw [e]
  exact h

end BlockBand.SourceProcess.FullSourceStops
