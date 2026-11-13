module

public import BlockBand.SourceProcess.FullSource.SqLayer
public import BlockBand.SourceProcess.FullSource.WeightedStep

/-!
# The weighted one-layer step of the tag square (deterministic old state)

At a deterministic Hermitian `𝕏` with `δ = δ₀(nearSchur z 𝕏) ≤ d`, a deterministic tag factor
`S`, `h = W⁻¹Re Tr Y²` and `t = W⁻¹Re Tr Y`:
`E[(1 + K(ρδ + C_m/W² + ξ)) h₊] ≤ (1 + α/W)(1 + Kδ)h + D t²` (`sq_weighted_layer_step`), with
`D = 2C₂²(1 + K(ρ + C_m))`. The additive `t²` is the paper's `C(s² + s + 1)` for a tag.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ} {m : Type*} [Fintype m]

/-- The `δ`-coefficient of the square step. -/
def lsq (Ca : ℝ) : ℝ := (2 + 4 * Ca) * Ca

/-- The rate of the weighted square step. -/
def alphaSq (K Cm Ca Cf CN : ℝ) : ℝ :=
  K * Cm + lsq Ca + K * lsq Ca + lsq Ca * (K * Cm) + K * Cm * lsq Ca +
    K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2

/-- The additive constant of the weighted square step. -/
def dsq (K Cm C₂ ρ : ℝ) : ℝ := 2 * C₂ ^ 2 * (1 + K * (ρ + Cm))

theorem lsq_nonneg {Ca : ℝ} (hCa : 0 ≤ Ca) : 0 ≤ lsq Ca := by unfold lsq; positivity

theorem alphaSq_nonneg {K Cm Ca Cf CN : ℝ} (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (hCa : 0 ≤ Ca)
    (hCN : 0 ≤ CN) :
    0 ≤ alphaSq K Cm Ca Cf CN := by
  have := lsq_nonneg hCa; unfold alphaSq; positivity

/-- **The weighted one-layer step of the tag square.** -/
theorem sq_weighted_layer_step {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) (hW : (1 : ℝ) ≤ W)
    {Ca C₂ CN₂ CN Cf Cm K ρ d : ℝ} (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂)
    (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm) (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hKL : lsq Ca ≤ K * (1 - ρ) / 2) (hd1 : d ≤ 1) (hρLd : ρ * lsq Ca * d ≤ (1 - ρ) / 2)
    (hδ : jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d)
    (hmean : ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤
      Ca * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2))
    (hfl₂ : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal (C₂ / Real.sqrt W * vecNorm u * vecNorm v))
    (hN₂ : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) ≤ ENNReal.ofReal CN₂)
    (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * (2 * 2) : ℕ) : ℝ))
      (freshLaw W b) ≤ ENNReal.ofReal CN)
    (hξ : eLpNorm (freshXi b E (nearSchur (boundaryZ b E) XX)) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (Cf / W)) :
    ∫⁻ f, ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
        Cm / (W : ℝ) ^ 2 + freshXi b E (nearSchur (boundaryZ b E) XX) f)) *
        sqPlus b E XX S f) ∂freshLaw W b ≤
      ENNReal.ofReal ((1 + alphaSq K Cm Ca Cf CN / W) *
        ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) XX)) * sqOf W S) +
        dsq K Cm C₂ ρ * ((W : ℝ)⁻¹ * (Sᴴ * S).trace.re) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
  obtain ⟨hi1, hb1⟩ := sqStep_moment XX S (by positivity : 0 ≤ C₂ / Real.sqrt W) hmean hfl₂
    (by simpa using hN₂)
  obtain ⟨hi2, hb2⟩ := sqStep_crude_moment (b := b) (E := E) XX S hCN hN
  have hb1' : ∫ f, sqPlus b E XX S f ∂freshLaw W b ≤
      (1 + 2 * (Ca * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2)) +
        2 * (Ca * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2)) ^ 2) *
        sqOf W S + 2 * C₂ ^ 2 * ((W : ℝ)⁻¹ * (Sᴴ * S).trace.re) ^ 2 := by
    refine hb1.trans (le_of_eq ?_)
    have e : (C₂ / Real.sqrt W) ^ 2 = C₂ ^ 2 / W := by rw [div_pow, hsq]
    rw [e]; field_simp
  set μ := freshLaw W b
  set δ := jetDistance0 b E (nearSchur (boundaryZ b E) XX)
  set ξ := freshXi b E (nearSchur (boundaryZ b E) XX)
  set h := sqOf W S
  set t := (W : ℝ)⁻¹ * (Sᴴ * S).trace.re
  set tp := sqPlus b E XX S
  have hh : 0 ≤ h := sqOf_nonneg W S
  have ht : 0 ≤ t := mul_nonneg (by positivity) (trace_factor_re_nonneg S)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδ1 : δ ≤ 1 := hδ.trans hd1
  have htp : ∀ f, 0 ≤ tp f := fun f => sqOf_nonneg _ _
  set A := 1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2)
  have hA0 : 0 ≤ A := by positivity
  set c := Ca * (δ + ((W : ℝ)⁻¹) ^ 2)
  have hc0 : 0 ≤ c := by positivity
  have hWinv : ((W : ℝ)⁻¹) ^ 2 ≤ 1 / W := by
    rw [inv_pow, ← one_div]; exact one_div_le_one_div_of_le hW0 (le_self_pow₀ hW (by norm_num))
  have hWinv1 : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := hWinv.trans (by rw [div_le_one hW0]; exact hW)
  -- the one-step factor
  have hcle : c ≤ 2 * Ca := by nlinarith
  have hΛ : 1 + 2 * c + 2 * c ^ 2 ≤ 1 + lsq Ca * δ + lsq Ca / W := by
    have h1 : 2 * c ^ 2 ≤ 4 * Ca * c := by nlinarith
    have hcW : c ≤ Ca * δ + Ca / W := by
      have := mul_le_mul_of_nonneg_left hWinv hCa
      simp only [c]; rw [mul_add]; linarith [show Ca * (1 / W) = Ca / W by ring]
    have h2 := mul_le_mul_of_nonneg_left hcW (by positivity : (0 : ℝ) ≤ 2 + 4 * Ca)
    have e : lsq Ca * δ + lsq Ca / W = (2 + 4 * Ca) * (Ca * δ + Ca / W) := by
      simp only [lsq]; ring
    linarith [e, h1, h2]
  have hAle : A ≤ 1 + K * ρ * δ + K * Cm / W := by
    have : Cm / (W : ℝ) ^ 2 ≤ Cm / W :=
      div_le_div_of_nonneg_left hCm hW0 (le_self_pow₀ hW (by norm_num))
    have h2 := mul_le_mul_of_nonneg_left this hK
    have e : A = 1 + K * ρ * δ + K * (Cm / (W : ℝ) ^ 2) := by simp only [A]; ring
    have e2 : K * (Cm / W) = K * Cm / W := by ring
    linarith
  have hAmax : A ≤ 1 + K * (ρ + Cm) := by
    have h1 : Cm / (W : ℝ) ^ 2 ≤ Cm := div_le_self hCm (one_le_pow₀ hW)
    have h2 : ρ * δ ≤ ρ := mul_le_of_le_one_right hρ0 hδ1
    have h3 : ρ * δ + Cm / (W : ℝ) ^ 2 ≤ ρ + Cm := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hK
    simp only [A]; linarith only [h4]
  -- the final real inequality
  have hfinal : A * (1 + 2 * c + 2 * c ^ 2) + K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2 / W ≤
      (1 + K * δ) * (1 + alphaSq K Cm Ca Cf CN / W) := by
    have hΛ0 : 0 ≤ 1 + 2 * c + 2 * c ^ 2 := by positivity
    have h1 : A * (1 + 2 * c + 2 * c ^ 2) ≤
        (1 + K * ρ * δ + K * Cm / W) * (1 + lsq Ca * δ + lsq Ca / W) :=
      mul_le_mul hAle hΛ hΛ0 (by have := mul_nonneg (mul_nonneg hK hρ0) hδ0; positivity)
    have h2 := weight_absorb (K := K) (ρ := ρ) (L := lsq Ca) (d := d) (δ := δ)
      (a₁ := K * Cm) (a₂ := lsq Ca) (e := K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2)
      (W := (W : ℝ)) hK hρ0 hρ1 (lsq_nonneg hCa) hKL hd1 hρLd hδ0 hδ (mul_nonneg hK hCm)
      (lsq_nonneg hCa) (div_nonneg (mul_nonneg hK (add_nonneg (sq_nonneg Cf)
        (pow_nonneg hCN _))) (by norm_num)) hW
    have e : alphaSq K Cm Ca Cf CN = K * Cm + lsq Ca + K * lsq Ca + lsq Ca * (K * Cm) +
        K * Cm * lsq Ca + K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2 := rfl
    rw [e]
    have e3 : K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2 / W =
        K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2 / W := rfl
    linarith only [h1, h2, e3]
  have hD : A * (2 * C₂ ^ 2 * t ^ 2) ≤ dsq K Cm C₂ ρ * t ^ 2 := by
    have := mul_le_mul_of_nonneg_right hAmax (by positivity : (0 : ℝ) ≤ 2 * C₂ ^ 2 * t ^ 2)
    refine this.trans (le_of_eq ?_)
    simp only [dsq]; ring
  have hint_eq : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) *
      tp f)) = fun f => ENNReal.ofReal ((A + K * ξ f) * tp f ^ 1) := by
    funext f; congr 1; simp only [A, pow_one]; ring
  rcases hh.eq_or_lt with h0 | hpos
  · have hz : ∀ f, tp f = 0 := fun f => le_antisymm
      ((sqStep_crude b E XX S f).trans (by rw [show sqOf W S = 0 from h0.symm, mul_zero]))
      (htp f)
    have : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f)) =
        fun _ => 0 := by
      funext f; rw [hz f, mul_zero, ENNReal.ofReal_zero]
    rw [this, lintegral_zero]
    exact bot_le
  have hl : 0 < (W : ℝ) * h := mul_pos hW0 hpos
  have hmtp : Measurable tp := measurable_sqPlus b E XX S
  have hmξ : Measurable ξ := measurable_freshXi b E _
  obtain ⟨hiξ, hbξ⟩ := integral_abs_pow_le (ν := μ) (f := ξ) (n := 2) (by norm_num)
    (div_nonneg hCf hW0.le) ⟨hmξ.aestronglyMeasurable, by exact_mod_cast hξ⟩
  have hsqξ : (fun f => |ξ f| ^ 2) = fun f => ξ f ^ 2 := by funext f; exact sq_abs _
  rw [hsqξ] at hiξ hbξ
  rw [hint_eq]
  have hB₁ : 0 ≤ (1 + 2 * c + 2 * c ^ 2) * h + 2 * C₂ ^ 2 * t ^ 2 := by positivity
  refine (lintegral_weighted_le (n := 1) hA0 hK hl htp hmtp (by simpa using hi1) hiξ
    (by simpa using hi2) (by simpa using hb1') hbξ (by simpa using hb2) hB₁ (sq_nonneg _)
    (mul_nonneg (pow_nonneg hCN _) (sq_nonneg h))).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the closing arithmetic
  have e1 : K / 2 * (W * h * (Cf / W) ^ 2 + CN ^ (2 * (2 * 2)) * h ^ 2 / (W * h)) =
      K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2 / W * h := by
    field_simp
  rw [e1]
  have h3 := mul_le_mul_of_nonneg_right hfinal hh
  calc A * ((1 + 2 * c + 2 * c ^ 2) * h + 2 * C₂ ^ 2 * t ^ 2) +
        K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2 / W * h
      = (A * (1 + 2 * c + 2 * c ^ 2) + K * (Cf ^ 2 + CN ^ (2 * (2 * 2))) / 2 / W) * h +
          A * (2 * C₂ ^ 2 * t ^ 2) := by ring
    _ ≤ (1 + K * δ) * (1 + alphaSq K Cm Ca Cf CN / W) * h + dsq K Cm C₂ ρ * t ^ 2 :=
        add_le_add h3 hD
    _ = _ := by ring

end BlockBand.SourceProcess.FullSource
