module

public import BlockBand.SourceProcess.FullSource.LayerStep
public import BlockBand.SourceProcess.FullSource.WeightAlgebra
public import BlockBand.Transmission.PathScalar.Holds

/-!
# The weighted one-layer step of a tag (deterministic old state)

At a deterministic Hermitian `𝕏` with `δ = δ₀(nearSchur z 𝕏) ≤ d` and a deterministic tag factor
`S`: with the fresh scalar error `ξ` (`‖ξ‖₂ ≤ C_f/W`) and the mean-step constant `C_m`,
`E[(1 + K(ρδ + C_m/W² + ξ)) t₊^n] ≤ (1 + α/W)(1 + Kδ) t^n` (`weighted_layer_step`). The
fresh cross term is paid by `ξt₊^n ≤ (Wt^nξ² + t₊^{2n}/(Wt^n))/2` and the crude
`E t₊^{2n} ≤ C_N^{4n} t^{2n}` (`tagStep_crude_moment`), i.e. the paper's Cauchy–Schwarz
`E_j|ξ₊|s₊^p ≤ C_p(s^p+1)/W`.
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

theorem measurable_tagPlus (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) : Measurable (tagPlus b E XX S) := by
  have hmN : Measurable fun ω => freshTransport b E XX ω :=
    measurable_freshTransport_comp b E measurable_const measurable_id
  have hSN : Measurable fun ω => S * freshTransport b E XX ω :=
    measurable_matrix_mul' measurable_const hmN
  have := measurable_matrix_mul' (measurable_matrix_conjTranspose' hSN) hSN
  unfold tagPlus
  simp only [Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Complex.measurable_re.comp
    (Finset.measurable_sum _ fun i _ => this.eval_matrix))

/-- **Crude moments of the transported tag**: `E t₊^q ≤ C_N^{2q} t^q` from `‖‖N‖‖_{2q} ≤ C_N`. -/
theorem tagStep_crude_moment {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) {q : ℕ} (hq : 1 ≤ q) {CN : ℝ} (hCN : 0 ≤ CN)
    (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * q : ℕ) : ℝ))
      (freshLaw W b) ≤ ENNReal.ofReal CN) :
    Integrable (fun ω => tagPlus b E XX S ω ^ q) (freshLaw W b) ∧
      ∫ ω, tagPlus b E XX S ω ^ q ∂freshLaw W b ≤
        CN ^ (2 * q) * ((W : ℝ)⁻¹ * (Sᴴ * S).trace.re) ^ q := by
  set t := (W : ℝ)⁻¹ * (Sᴴ * S).trace.re
  have ht : 0 ≤ t := mul_nonneg (by positivity) (trace_factor_re_nonneg S)
  have hmN : Measurable fun ω => freshTransport b E XX ω :=
    measurable_freshTransport_comp b E measurable_const measurable_id
  obtain ⟨hi, hb⟩ := integral_abs_pow_le (ν := freshLaw W b) (f := fun ω => ‖freshTransport b E XX ω‖)
    (n := 2 * q) (by omega) hCN ⟨hmN.norm.aestronglyMeasurable, hN⟩
  have hmt : Measurable fun ω => tagPlus b E XX S ω := by
    have hSN : Measurable fun ω => S * freshTransport b E XX ω :=
      measurable_matrix_mul' measurable_const hmN
    have := measurable_matrix_mul' (measurable_matrix_conjTranspose' hSN) hSN
    simp only [tagPlus, Matrix.trace, Matrix.diag]
    exact measurable_const.mul (Complex.measurable_re.comp
      (Finset.measurable_sum _ fun i _ => this.eval_matrix))
  have hle : ∀ ω, tagPlus b E XX S ω ^ q ≤ |‖freshTransport b E XX ω‖| ^ (2 * q) * t ^ q := by
    intro ω
    rw [abs_of_nonneg (norm_nonneg _), pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (tagPlus_nonneg _ _ _ _ _) (tagStep_crude b E XX S ω) q
  have hint : Integrable (fun ω => tagPlus b E XX S ω ^ q) (freshLaw W b) :=
    (hi.mul_const _).mono' (hmt.pow_const q).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (tagPlus_nonneg _ _ _ _ _) q)]
        exact hle ω)
  refine ⟨hint, (integral_mono hint (hi.mul_const _) hle).trans ?_⟩
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right hb (pow_nonneg ht q)

/-- The fresh scalar error `ξ = |W⁻¹Tr R₊ - E W⁻¹Tr R₊|` at a deterministic old `X`. -/
def freshXi (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (f : LayerSample W .oneBlockOnePort) : ℝ :=
  ‖freshPortTrace b E X f - ∫ f', freshPortTrace b E X f' ∂freshLaw W b‖

theorem measurable_freshXi (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (freshXi b E X) :=
  ((measurable_freshPortTrace_comp b E measurable_const measurable_id).sub
    measurable_const).norm

/-- `ξy ≤ (λξ² + y²/λ)/2`. -/
theorem mul_le_amgm {ξ y l : ℝ} (hl : 0 < l) : ξ * y ≤ (l * ξ ^ 2 + y ^ 2 / l) / 2 := by
  have h : (l * ξ ^ 2 + y ^ 2 / l) / 2 - ξ * y = (l * ξ - y) ^ 2 / (2 * l) := by
    field_simp; ring
  have : 0 ≤ (l * ξ - y) ^ 2 / (2 * l) := by positivity
  linarith

/-- The `δ`-coefficient `L` of the one-step factor. -/
def lcoef (Ca : ℝ) (n : ℕ) : ℝ := (n + 2 ^ n * (2 * (2 * Ca) + 2 ^ n * (2 * Ca) ^ (n - 1))) * Ca

/-- The `1/W`-coefficient `a₂` of the one-step factor. -/
def acoef (Ca C₂ Cn : ℝ) (n : ℕ) : ℝ :=
  lcoef Ca n + 2 ^ n * (2 * C₂ ^ 2 + 2 ^ n * Cn ^ (n - 2) * Cn ^ 2)

/-- The rate `α` of the weighted step. -/
def alphaW (K Cm Ca C₂ Cn Cf CN : ℝ) (n : ℕ) : ℝ :=
  K * Cm + acoef Ca C₂ Cn n + K * acoef Ca C₂ Cn n + lcoef Ca n * (K * Cm) +
    K * Cm * acoef Ca C₂ Cn n + K * (Cf ^ 2 + CN ^ (2 * (2 * n))) / 2

theorem lcoef_nonneg {Ca : ℝ} (hCa : 0 ≤ Ca) (n : ℕ) : 0 ≤ lcoef Ca n := by
  unfold lcoef; positivity

theorem acoef_nonneg {Ca C₂ Cn : ℝ} (hCa : 0 ≤ Ca) (hCn : 0 ≤ Cn) (n : ℕ) :
    0 ≤ acoef Ca C₂ Cn n := by
  unfold acoef; have := lcoef_nonneg hCa n; positivity

/-- The measure-theoretic half of the weighted step: split `(A + Kξ)t₊^n` and pay the cross
term by `ξt₊^n ≤ (lξ² + t₊^{2n}/l)/2`. -/
theorem lintegral_weighted_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {tp ξ : Ω → ℝ}
    {A K l : ℝ} {n : ℕ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hl : 0 < l) (htp : ∀ f, 0 ≤ tp f)
    (hmtp : Measurable tp)
    (hi1 : Integrable (fun f => tp f ^ n) μ) (hiξ : Integrable (fun f => ξ f ^ 2) μ)
    (hi2 : Integrable (fun f => tp f ^ (2 * n)) μ) {B₁ Bξ B₂ : ℝ}
    (hb1 : ∫ f, tp f ^ n ∂μ ≤ B₁) (hbξ : ∫ f, ξ f ^ 2 ∂μ ≤ Bξ)
    (hb2 : ∫ f, tp f ^ (2 * n) ∂μ ≤ B₂) (hB₁ : 0 ≤ B₁) (hBξ : 0 ≤ Bξ) (hB₂ : 0 ≤ B₂) :
    ∫⁻ f, ENNReal.ofReal ((A + K * ξ f) * tp f ^ n) ∂μ ≤
      ENNReal.ofReal (A * B₁ + K / 2 * (l * Bξ + B₂ / l)) := by
  have hK2 : 0 ≤ K / 2 := by linarith
  have hnn : ∀ f, 0 ≤ K / 2 * (l * ξ f ^ 2 + tp f ^ (2 * n) / l) := fun f =>
    mul_nonneg hK2 (add_nonneg (mul_nonneg hl.le (sq_nonneg _))
      (div_nonneg (pow_nonneg (htp f) _) hl.le))
  have hsplit : ∀ f, ENNReal.ofReal ((A + K * ξ f) * tp f ^ n) ≤
      ENNReal.ofReal (A * tp f ^ n) +
        ENNReal.ofReal (K / 2 * (l * ξ f ^ 2 + tp f ^ (2 * n) / l)) := by
    intro f
    rw [← ENNReal.ofReal_add (mul_nonneg hA (pow_nonneg (htp f) n)) (hnn f)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := mul_le_amgm (ξ := ξ f) (y := tp f ^ n) hl
    rw [← pow_mul, mul_comm n 2] at h
    have := mul_le_mul_of_nonneg_left h hK
    nlinarith
  have hI1 : Integrable (fun f => A * tp f ^ n) μ := hi1.const_mul A
  have hI2 : Integrable (fun f => K / 2 * (l * ξ f ^ 2 + tp f ^ (2 * n) / l)) μ :=
    ((hiξ.const_mul l).add (hi2.div_const l)).const_mul _
  calc ∫⁻ f, ENNReal.ofReal ((A + K * ξ f) * tp f ^ n) ∂μ
      ≤ ∫⁻ f, (ENNReal.ofReal (A * tp f ^ n) +
          ENNReal.ofReal (K / 2 * (l * ξ f ^ 2 + tp f ^ (2 * n) / l))) ∂μ :=
        lintegral_mono hsplit
    _ = ENNReal.ofReal (∫ f, A * tp f ^ n ∂μ) +
          ENNReal.ofReal (∫ f, K / 2 * (l * ξ f ^ 2 + tp f ^ (2 * n) / l) ∂μ) := by
        rw [lintegral_add_left (show Measurable fun f => ENNReal.ofReal (A * tp f ^ n) from
          (measurable_const.mul (hmtp.pow_const n)).ennreal_ofReal),
          ofReal_integral_eq_lintegral_ofReal hI1 (Filter.Eventually.of_forall fun f =>
            mul_nonneg hA (pow_nonneg (htp f) n)),
          ofReal_integral_eq_lintegral_ofReal hI2 (Filter.Eventually.of_forall hnn)]
    _ ≤ ENNReal.ofReal (A * B₁) + ENNReal.ofReal (K / 2 * (l * Bξ + B₂ / l)) := by
        refine add_le_add (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
        · rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hb1 hA
        · rw [integral_const_mul, integral_add (hiξ.const_mul l) (hi2.div_const l),
            integral_const_mul, integral_div]
          refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hbξ hl.le)
            (div_le_div_of_nonneg_right hb2 hl.le)) hK2
    _ = ENNReal.ofReal (A * B₁ + K / 2 * (l * Bξ + B₂ / l)) :=
        (ENNReal.ofReal_add (mul_nonneg hA hB₁) (mul_nonneg hK2 (add_nonneg
          (mul_nonneg hl.le hBξ) (div_nonneg hB₂ hl.le)))).symm

/-- The arithmetic closing the weighted step, with `l = Wt^n`. -/
theorem weighted_layer_real {W t A Λ K Cf CN F : ℝ} {n : ℕ} (hW : 0 < W) (ht : 0 < t)
    (hfinal : A * Λ + K * (Cf ^ 2 + CN ^ (2 * (2 * n))) / 2 / W ≤ F) :
    A * (t ^ n * Λ) + K / 2 * (W * t ^ n * (Cf / W) ^ 2 +
        CN ^ (2 * (2 * n)) * t ^ (2 * n) / (W * t ^ n)) ≤ F * t ^ n := by
  have htn : 0 < t ^ n := pow_pos ht n
  have e : A * (t ^ n * Λ) + K / 2 * (W * t ^ n * (Cf / W) ^ 2 +
      CN ^ (2 * (2 * n)) * t ^ (2 * n) / (W * t ^ n)) =
      (A * Λ + K * (Cf ^ 2 + CN ^ (2 * (2 * n))) / 2 / W) * t ^ n := by
    rw [mul_comm 2 n, pow_mul']; field_simp; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hfinal htn.le

/-- **The weighted one-layer step of a tag**. -/
theorem weighted_layer_step {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) {n : ℕ} (hn : 2 ≤ n) (hW : (1 : ℝ) ≤ W)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d : ℝ} (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn)
    (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm) (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hKL : lcoef Ca n ≤ K * (1 - ρ) / 2) (hd1 : d ≤ 1) (hρLd : ρ * lcoef Ca n * d ≤ (1 - ρ) / 2)
    (hδ : jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d)
    (hmean : ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤
      Ca * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2))
    (hfl₂ : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal (C₂ / Real.sqrt W * vecNorm u * vecNorm v))
    (hfln : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal n) (freshLaw W b) ≤
        ENNReal.ofReal (Cn / Real.sqrt W * vecNorm u * vecNorm v))
    (hN₂ : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) ≤ ENNReal.ofReal CN₂)
    (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * (2 * n) : ℕ) : ℝ))
      (freshLaw W b) ≤ ENNReal.ofReal CN)
    (hξ : eLpNorm (freshXi b E (nearSchur (boundaryZ b E) XX)) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (Cf / W)) :
    ∫⁻ f, ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
        Cm / (W : ℝ) ^ 2 + freshXi b E (nearSchur (boundaryZ b E) XX) f)) *
        tagPlus b E XX S f ^ n) ∂freshLaw W b ≤
      ENNReal.ofReal ((1 + alphaW K Cm Ca C₂ Cn Cf CN n / W) *
        ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) XX)) *
          ((W : ℝ)⁻¹ * (Sᴴ * S).trace.re) ^ n)) := by
  set μ := freshLaw W b
  set δ := jetDistance0 b E (nearSchur (boundaryZ b E) XX)
  set ξ := freshXi b E (nearSchur (boundaryZ b E) XX)
  set t := (W : ℝ)⁻¹ * (Sᴴ * S).trace.re
  set tp := tagPlus b E XX S
  have hW0 : (0 : ℝ) < W := by linarith
  have ht : 0 ≤ t := mul_nonneg (by positivity) (trace_factor_re_nonneg S)
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have htp : ∀ f, 0 ≤ tp f := tagPlus_nonneg b E XX S
  have hξ0 : ∀ f, 0 ≤ ξ f := fun f => norm_nonneg _
  have hsq : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0.le
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  set A := 1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2)
  have hA0 : 0 ≤ A := by positivity
  -- the moment step
  set c := Ca * (δ + ((W : ℝ)⁻¹) ^ 2)
  have hc0 : 0 ≤ c := by positivity
  have hfl₂' : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect μ (wardNoise b E XX)) v) (ENNReal.ofReal 2) μ ≤
        ENNReal.ofReal (C₂ / Real.sqrt W * vecNorm u * vecNorm v) := hfl₂
  obtain ⟨hi1, hb1⟩ := tagStep_moment XX S hc0 (by positivity : 0 ≤ C₂ / Real.sqrt W)
    (by positivity : 0 ≤ Cn / Real.sqrt W) hn hmean hfl₂' hfln (by simpa using hN₂)
  obtain ⟨hi2, hb2⟩ := tagStep_crude_moment (b := b) (E := E) XX S (q := 2 * n) (by omega) hCN hN
  -- the one-step factor
  set Λ := 1 + n * c + 2 ^ n * ((c + C₂ / Real.sqrt W) ^ 2 + (c + Cn / Real.sqrt W) ^ n)
  have hWinv : ((W : ℝ)⁻¹) ^ 2 ≤ 1 / W := by
    rw [inv_pow, ← one_div]; exact one_div_le_one_div_of_le hW0 (by nlinarith)
  have hcle : c ≤ 2 * Ca := by
    have : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := hWinv.trans (by rw [div_le_one hW0]; exact hW)
    have : δ ≤ 1 := hδ.trans hd1
    nlinarith
  have hΛ : Λ ≤ 1 + lcoef Ca n * δ + acoef Ca C₂ Cn n / W := by
    have h1 := lam_bound (σ₂ := C₂ / Real.sqrt W) hc0 hcle (by positivity : 0 ≤ Cn / Real.sqrt W)
      (div_le_self hCn hsW) hn
    have e₂ : (C₂ / Real.sqrt W) ^ 2 = C₂ ^ 2 / W := by rw [div_pow, hsq]
    have eₙ : (Cn / Real.sqrt W) ^ 2 = Cn ^ 2 / W := by rw [div_pow, hsq]
    rw [e₂, eₙ] at h1
    have hcW : c ≤ Ca * δ + Ca / W := by
      have := mul_le_mul_of_nonneg_left hWinv hCa
      simp only [c]; rw [mul_add]; linarith [show Ca * (1 / W) = Ca / W by ring]
    have hB : 0 ≤ (n + 2 ^ n * (2 * (2 * Ca) + 2 ^ n * (2 * Ca) ^ (n - 1)) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hcW hB
    have e3 : 2 ^ n * (2 * (C₂ ^ 2 / W) + 2 ^ n * Cn ^ (n - 2) * (Cn ^ 2 / W)) =
        2 ^ n * (2 * C₂ ^ 2 + 2 ^ n * Cn ^ (n - 2) * Cn ^ 2) / W := by field_simp
    rw [e3] at h1
    simp only [lcoef, acoef]
    have e4 : (n + 2 ^ n * (2 * (2 * Ca) + 2 ^ n * (2 * Ca) ^ (n - 1)) : ℝ) * (Ca * δ + Ca / W) =
        (n + 2 ^ n * (2 * (2 * Ca) + 2 ^ n * (2 * Ca) ^ (n - 1))) * Ca * δ +
          (n + 2 ^ n * (2 * (2 * Ca) + 2 ^ n * (2 * Ca) ^ (n - 1))) * Ca / W := by ring
    have e5 : ((n + 2 ^ n * (2 * (2 * Ca) + 2 ^ n * (2 * Ca) ^ (n - 1))) * Ca +
        2 ^ n * (2 * C₂ ^ 2 + 2 ^ n * Cn ^ (n - 2) * Cn ^ 2)) / W =
        (n + 2 ^ n * (2 * (2 * Ca) + 2 ^ n * (2 * Ca) ^ (n - 1))) * Ca / W +
          2 ^ n * (2 * C₂ ^ 2 + 2 ^ n * Cn ^ (n - 2) * Cn ^ 2) / W := by ring
    rw [e5]
    linarith
  have hAle : A ≤ 1 + K * ρ * δ + K * Cm / W := by
    have : Cm / (W : ℝ) ^ 2 ≤ Cm / W := div_le_div_of_nonneg_left hCm hW0 (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_left this hK
    have e : A = 1 + K * ρ * δ + K * (Cm / (W : ℝ) ^ 2) := by simp only [A]; ring
    have e2 : K * (Cm / W) = K * Cm / W := by ring
    linarith
  -- the final real inequality
  have hfinal : A * Λ + K * (Cf ^ 2 + CN ^ (2 * (2 * n))) / 2 / W ≤
      (1 + K * δ) * (1 + alphaW K Cm Ca C₂ Cn Cf CN n / W) := by
    have hΛ0 : 0 ≤ Λ := by positivity
    have h1 : A * Λ ≤ (1 + K * ρ * δ + K * Cm / W) * (1 + lcoef Ca n * δ + acoef Ca C₂ Cn n / W) :=
      mul_le_mul hAle hΛ hΛ0 (by have := mul_nonneg (mul_nonneg hK hρ0) hδ0; positivity)
    have h2 := weight_absorb (K := K) (ρ := ρ) (L := lcoef Ca n) (d := d) (δ := δ)
      (a₁ := K * Cm) (a₂ := acoef Ca C₂ Cn n) (e := K * (Cf ^ 2 + CN ^ (2 * (2 * n))) / 2)
      (W := (W : ℝ)) hK hρ0 hρ1 (lcoef_nonneg hCa n) hKL hd1 hρLd hδ0 hδ (mul_nonneg hK hCm)
      (acoef_nonneg hCa hCn n) (by have := mul_nonneg hK (add_nonneg (sq_nonneg Cf)
        (pow_nonneg hCN (2 * (2 * n)))); linarith) hW
    have e : alphaW K Cm Ca C₂ Cn Cf CN n = K * Cm + acoef Ca C₂ Cn n + K * acoef Ca C₂ Cn n +
        lcoef Ca n * (K * Cm) + K * Cm * acoef Ca C₂ Cn n +
        K * (Cf ^ 2 + CN ^ (2 * (2 * n))) / 2 := rfl
    rw [e]
    linarith
  rcases ht.eq_or_lt with h0 | hpos
  · have hz : ∀ f, tp f = 0 := fun f => le_antisymm
      ((tagStep_crude b E XX S f).trans
        (by rw [show (W : ℝ)⁻¹ * (Sᴴ * S).trace.re = 0 from h0.symm, mul_zero])) (htp f)
    have : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) * tp f ^ n)) =
        fun _ => 0 := by
      funext f; rw [hz f, zero_pow (by omega), mul_zero, ENNReal.ofReal_zero]
    rw [this, lintegral_zero]
    exact bot_le
  have hl : 0 < (W : ℝ) * t ^ n := mul_pos hW0 (pow_pos hpos n)
  have hmtp : Measurable tp := measurable_tagPlus b E XX S
  have hmξ : Measurable ξ := measurable_freshXi b E _
  obtain ⟨hiξ, hbξ⟩ := integral_abs_pow_le (ν := μ) (f := ξ) (n := 2) (by norm_num)
    (div_nonneg hCf hW0.le) ⟨hmξ.aestronglyMeasurable, by exact_mod_cast hξ⟩
  have hsqξ : (fun f => |ξ f| ^ 2) = fun f => ξ f ^ 2 := by funext f; exact sq_abs _
  rw [hsqξ] at hiξ hbξ
  have hint_eq : (fun f => ENNReal.ofReal ((1 + K * (ρ * δ + Cm / (W : ℝ) ^ 2 + ξ f)) *
      tp f ^ n)) = fun f => ENNReal.ofReal ((A + K * ξ f) * tp f ^ n) := by
    funext f; congr 1; simp only [A]; ring
  rw [hint_eq]
  have hΛ0 : 0 ≤ Λ := by positivity
  refine (lintegral_weighted_le hA0 hK hl htp hmtp hi1 hiξ hi2 hb1 hbξ hb2
    (mul_nonneg (pow_nonneg ht n) hΛ0) (sq_nonneg _)
    (mul_nonneg (pow_nonneg hCN _) (pow_nonneg ht _))).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := weighted_layer_real (n := n) hW0 hpos hfinal
  have e : (1 + alphaW K Cm Ca C₂ Cn Cf CN n / W) * ((1 + K * δ) * t ^ n) =
      (1 + K * δ) * (1 + alphaW K Cm Ca C₂ Cn Cf CN n / W) * t ^ n := by ring
  rw [e]
  exact h

end BlockBand.SourceProcess.FullSource
