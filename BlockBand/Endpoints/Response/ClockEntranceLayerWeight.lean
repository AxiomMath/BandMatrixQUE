module

public import BlockBand.Endpoints.Response.ClockEntranceLayerPassive
public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The weight step and `ClockFractionalOneLayer` from the logistic inequality

Part of the clock fractional-entrance lemma: multiply by the scalar weight `1 + K_pδ_{0,+}`. Its
predictable contraction absorbs the `C_pδ₀H_p` term; the centered jet correlation costs
`C_pH_p/W`, since `H_{p,+} ≤ ‖L‖^{2p}H_p`. The negative term is retained.

* `cel_lintegral_sq_le`, `cel_cross_le` — **the centered jet correlation**
  `E_ν|ξ₊|‖L‖^{2p} ≤ (B² + 1 + C₄)/(2W)` from `‖ξ₊‖_{L²(ν)} ≤ B/W` (`OnePortJetContraction` at
  `r = 2`) and `E_ν‖L‖⁴ ≤ C₄` (`OnePortOperatorMoments` at `r = 2`), by AM–GM at scale `W`
  (no measurability of `H_{p,+}` needed).
* `cel_weight_real` — the scalar bookkeeping with `K(1-ρ) = 2C` and `Kd ≤ 1`.
* `cel_weighted_det` — the deterministic weighted one-layer inequality at fixed passive `X`
  and `A ⪰ 0`.
* `clockFractionalOneLayer_of_logistic` — `ClockFractionalOneLayer` from `ClockLayerLogistic`,
  `OnePortOperatorMoments`, `OnePortJetContraction` and `TransmissionLawContract` (only the
  existence of the stationary jet, `jetGap`). Uses the a.s. passivity of `pathX`
  (`cel_pathX_passive`) and the positivity of the clock (`ce_nearClock_posSemidef`).
* `clockFractionalOneLayer_of_jensenGap`, `clockFractionalEntrance_of_jensenGap` — the chain
  down to the isolated `ClockLayerJensenGap`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.Inputs

variable {W : ℕ}

/-- The fresh one-port layer law is a probability measure. -/
theorem cel_isProbabilityMeasure_freshLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (freshLaw W b) := by
  have i1 : ∀ _ : Fin 1, IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure
      (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) := fun _ => passDeriv_isProbabilityMeasure_gue _ _
  have i2 : ∀ _ : Fin 1, ∀ _ : Fin 1, IsProbabilityMeasure
      (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) :=
    fun _ _ => passDeriv_isProbabilityMeasure_ginibre _ _ _
  unfold freshLaw layerLaw
  exact inferInstance

/-- `‖ξ‖_{L²} ≤ B` gives `∫⁻ ξ² ≤ B²`. -/
theorem cel_lintegral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {ξ : α → ℝ} {B : ℝ}
    (hξ : AEStronglyMeasurable ξ μ) (hB : 0 ≤ B) (h : eLpNorm ξ 2 μ ≤ ENNReal.ofReal B) :
    ∫⁻ x, ENNReal.ofReal (ξ x ^ 2) ∂μ ≤ ENNReal.ofReal (B ^ 2) := by
  have e1 : ∀ x, ENNReal.ofReal (ξ x ^ 2) = ‖ξ x‖ₑ ^ (2 : ℝ) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs]
  simp_rw [e1]
  calc ∫⁻ x, ‖ξ x‖ₑ ^ (2 : ℝ) ∂μ = eLpNorm' ξ 2 μ ^ (2 : ℝ) :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)
    _ = eLpNorm ξ 2 μ ^ (2 : ℝ) := by
        rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top] <;> first | exact hξ | norm_num
    _ ≤ ENNReal.ofReal B ^ (2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (B ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB (by norm_num), Real.rpow_two]

/-- **The centered jet correlation**: for a fluctuation `ξ`
with `‖ξ‖_{L²(μ)} ≤ B/w` and `g ≥ 0` with `∫ g⁴ ≤ C₄` (`g = ‖L‖`), `0 ≤ p ≤ 1`,
`∫ |ξ| g^{2p} ≤ (B² + 1 + C₄)/(2w)` (AM–GM at scale `w`; only `ξ` needs measurability). -/
theorem cel_cross_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {ξ g : α → ℝ} (hξ : AEStronglyMeasurable ξ μ) {B C₄ w p : ℝ} (hw : 0 < w) (hB : 0 ≤ B)
    (hC₄ : 0 ≤ C₄) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hg : ∀ x, 0 ≤ g x)
    (hξ2 : eLpNorm ξ 2 μ ≤ ENNReal.ofReal (B / w))
    (hg4 : ∫⁻ x, ENNReal.ofReal (g x ^ 4) ∂μ ≤ ENNReal.ofReal C₄) :
    ∫⁻ x, ENNReal.ofReal (|ξ x| * g x ^ (2 * p)) ∂μ ≤ ENNReal.ofReal ((B ^ 2 + (1 + C₄)) / (2 * w)) := by
  have hpt : ∀ x, ENNReal.ofReal (|ξ x| * g x ^ (2 * p)) ≤
      ENNReal.ofReal (w / 2) * ENNReal.ofReal (ξ x ^ 2) +
        ENNReal.ofReal (1 / (2 * w)) * (1 + ENNReal.ofReal (g x ^ 4)) := by
    intro x
    set f := g x ^ (2 * p)
    have hf2 : f ^ 2 ≤ 1 + g x ^ 4 := by
      have e : f ^ 2 = g x ^ (4 * p) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hg x)]; norm_num; ring_nf
      rw [e]
      rcases le_total (g x) 1 with h1 | h1
      · have := Real.rpow_le_one (hg x) h1 (by linarith : 0 ≤ 4 * p)
        nlinarith [pow_nonneg (hg x) 4]
      · have := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num; linarith : 4 * p ≤ ((4 : ℕ) : ℝ))
        rw [Real.rpow_natCast] at this
        linarith
    have key : w / 2 * ξ x ^ 2 + f ^ 2 / (2 * w) - |ξ x| * f = (w * |ξ x| - f) ^ 2 / (2 * w) := by
      rw [← sq_abs (ξ x)]; field_simp; ring
    have hreal : |ξ x| * f ≤ w / 2 * ξ x ^ 2 + 1 / (2 * w) * (1 + g x ^ 4) := by
      have h1 : 0 ≤ (w * |ξ x| - f) ^ 2 / (2 * w) := by positivity
      have h2 : f ^ 2 / (2 * w) ≤ 1 / (2 * w) * (1 + g x ^ 4) := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_left hf2 (by positivity)
      linarith
    calc ENNReal.ofReal (|ξ x| * f)
        ≤ ENNReal.ofReal (w / 2 * ξ x ^ 2 + 1 / (2 * w) * (1 + g x ^ 4)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal (w / 2 * ξ x ^ 2) + ENNReal.ofReal (1 / (2 * w) * (1 + g x ^ 4)) :=
          ENNReal.ofReal_add_le
      _ ≤ _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          gcongr
          exact ENNReal.ofReal_add_le.trans (by rw [ENNReal.ofReal_one])
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (w / 2) * ENNReal.ofReal (ξ x ^ 2)) μ :=
    (ENNReal.measurable_ofReal.comp_aemeasurable (hξ.aemeasurable.pow_const 2)).const_mul _
  have hsq := cel_lintegral_sq_le hξ (div_nonneg hB hw.le) hξ2
  calc ∫⁻ x, ENNReal.ofReal (|ξ x| * g x ^ (2 * p)) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (w / 2) * ENNReal.ofReal (ξ x ^ 2) +
          ENNReal.ofReal (1 / (2 * w)) * (1 + ENNReal.ofReal (g x ^ 4))) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (w / 2) * ∫⁻ x, ENNReal.ofReal (ξ x ^ 2) ∂μ +
          ENNReal.ofReal (1 / (2 * w)) * (1 + ∫⁻ x, ENNReal.ofReal (g x ^ 4) ∂μ) := by
        rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (w / 2) * ENNReal.ofReal ((B / w) ^ 2) +
          ENNReal.ofReal (1 / (2 * w)) * (1 + ENNReal.ofReal C₄) := by gcongr
    _ = ENNReal.ofReal ((B ^ 2 + (1 + C₄)) / (2 * w)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hC₄,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp

/-- **Scalar bookkeeping of the weight step**: with `K(1-ρ) ≥ 2C`, `Kd ≤ 1`,
`0 ≤ δ ≤ d`, `0 ≤ u ≤ 1` (`u = 1/W`), `M = 1 + K(ρδ + C_c u²)`, `m = 1 + Cδ + Cu²`,
`M m H + M (C u) F + K H (B u/2) ≤ (1 + C'u)(1 + Kδ)H + C'u F`. -/
theorem cel_weight_real {K ρ CL Cc d δ H F Bx u : ℝ} (hK0 : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hCL : 0 ≤ CL) (hCc : 0 ≤ Cc) (hδ0 : 0 ≤ δ) (hδd : δ ≤ d) (hdK : K * d ≤ 1)
    (hK : K * ρ + 2 * CL ≤ K) (hH : 0 ≤ H) (hF : 0 ≤ F) (hBx : 0 ≤ Bx) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    (1 + K * (ρ * δ + Cc * u ^ 2)) * ((1 + CL * δ + CL * u ^ 2) * H) +
        (1 + K * (ρ * δ + Cc * u ^ 2)) * (CL * u * F) + K * H * (Bx * u / 2) ≤
      (1 + ((1 + K * (ρ * d + Cc)) * CL + (K * Cc * (1 + CL * d + CL) + CL * (1 + K * d)) +
          K * Bx / 2) * u) * ((1 + K * δ) * H) +
        ((1 + K * (ρ * d + Cc)) * CL + (K * Cc * (1 + CL * d + CL) + CL * (1 + K * d)) +
          K * Bx / 2) * u * F := by
  set CM := 1 + K * (ρ * d + Cc)
  set C₂ := K * Cc * (1 + CL * d + CL) + CL * (1 + K * d)
  set M := 1 + K * (ρ * δ + Cc * u ^ 2)
  set m := 1 + CL * δ + CL * u ^ 2
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hu2' : u ^ 2 ≤ 1 := hu2.trans hu1
  have hd0 : 0 ≤ d := hδ0.trans hδd
  have hρδ : ρ * δ ≤ ρ * d := mul_le_mul_of_nonneg_left hδd hρ0
  have hM1 : M ≤ CM := by
    have : Cc * u ^ 2 ≤ Cc := by nlinarith
    have : K * (ρ * δ + Cc * u ^ 2) ≤ K * (ρ * d + Cc) := mul_le_mul_of_nonneg_left (by linarith) hK0
    simp only [M, CM]; linarith
  set a := K * ρ * δ
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    have : K * ρ * δ ≤ K * d := by
      have : ρ * δ ≤ d := (mul_le_of_le_one_left hδ0 hρ1).trans hδd
      calc K * ρ * δ = K * (ρ * δ) := by ring
        _ ≤ K * d := mul_le_mul_of_nonneg_left this hK0
    linarith
  have hMm : M * m ≤ 1 + K * δ + C₂ * u := by
    have e : M * m = (1 + a) * (1 + CL * δ) + K * Cc * u ^ 2 * (1 + CL * δ + CL * u ^ 2) +
        (1 + a) * (CL * u ^ 2) := by simp only [M, m, a]; ring
    have h1 : (1 + a) * (1 + CL * δ) ≤ 1 + K * δ := by
      have : a * (CL * δ) ≤ CL * δ := by
        have : 0 ≤ CL * δ := by positivity
        nlinarith
      have : a + 2 * CL * δ ≤ K * δ := by
        have := mul_le_mul_of_nonneg_right hK hδ0
        simp only [a]; nlinarith
      nlinarith
    have h2 : K * Cc * u ^ 2 * (1 + CL * δ + CL * u ^ 2) ≤ K * Cc * (1 + CL * d + CL) * u := by
      have hKC : 0 ≤ K * Cc := by positivity
      have hin : 1 + CL * δ + CL * u ^ 2 ≤ 1 + CL * d + CL := by
        have := mul_le_mul_of_nonneg_left hδd hCL
        have := mul_le_mul_of_nonneg_left hu2' hCL
        linarith
      have hpos : 0 ≤ 1 + CL * δ + CL * u ^ 2 := by positivity
      calc K * Cc * u ^ 2 * (1 + CL * δ + CL * u ^ 2)
          ≤ K * Cc * u * (1 + CL * δ + CL * u ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 hKC) hpos
        _ ≤ K * Cc * u * (1 + CL * d + CL) := mul_le_mul_of_nonneg_left hin (by positivity)
        _ = K * Cc * (1 + CL * d + CL) * u := by ring
    have h3 : (1 + a) * (CL * u ^ 2) ≤ CL * (1 + K * d) * u := by
      have hKd : a ≤ K * d := by
        have : ρ * δ ≤ d := (mul_le_of_le_one_left hδ0 hρ1).trans hδd
        calc a = K * (ρ * δ) := by simp only [a]; ring
          _ ≤ K * d := mul_le_mul_of_nonneg_left this hK0
      calc (1 + a) * (CL * u ^ 2) ≤ (1 + K * d) * (CL * u) :=
            mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hu2 hCL) (by positivity)
              (by positivity)
        _ = CL * (1 + K * d) * u := by ring
    rw [e]; simp only [C₂]; linarith
  have hMpos : 0 ≤ M := by positivity
  have hF1 : M * (CL * u * F) ≤ CM * CL * u * F := by
    have : M * (CL * u * F) ≤ CM * (CL * u * F) :=
      mul_le_mul_of_nonneg_right hM1 (by positivity)
    linarith [show CM * (CL * u * F) = CM * CL * u * F by ring]
  have hKδ : 0 ≤ K * δ := by positivity
  have hmain : M * (m * H) + K * H * (Bx * u / 2) ≤ (1 + K * δ) * H + (C₂ + K * Bx / 2) * u * H := by
    have := mul_le_mul_of_nonneg_right hMm hH
    nlinarith
  have hC0 : 0 ≤ (C₂ + K * Bx / 2) * u * H := by positivity
  have hfin : (1 + K * δ) * H + (C₂ + K * Bx / 2) * u * H ≤
      (1 + (CM * CL + C₂ + K * Bx / 2) * u) * ((1 + K * δ) * H) := by
    have h1 : 0 ≤ CM * CL * u * ((1 + K * δ) * H) := by positivity
    have h2 : (C₂ + K * Bx / 2) * u * H ≤ (C₂ + K * Bx / 2) * u * ((1 + K * δ) * H) := by
      have : H ≤ (1 + K * δ) * H := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  have hF2 : CM * CL * u * F ≤ (CM * CL + C₂ + K * Bx / 2) * u * F := by
    have : CM * CL ≤ CM * CL + C₂ + K * Bx / 2 := by
      have : 0 ≤ C₂ := by positivity
      have : 0 ≤ K * Bx / 2 := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hu0) hF
  linarith

/-- **The deterministic weighted one-layer inequality** at fixed passive `X` and `A ⪰ 0`: from
the logistic inequality, the contraction `δ_{0,+} ≤ ρδ₀ + C_c/W² + |ξ|`
(`OnePortJetContraction`), `‖ξ‖_{L²} ≤ C_c√2/W` and `E‖L‖⁴ ≤ C₄` (`OnePortOperatorMoments`),
`E_ν[(1 + Kδ_{0,+})H_{p,+}] + (c/W)H_p²/γ^p ≤ (1 + C'/W)(1 + Kδ₀)H_p + (C'/W)|g|^{2(1-p)}γ^p`. -/
theorem cel_weighted_det {b E p K ρ Cc CL cL C₄ d C' : ℝ} {X A : Matrix (Fin W) (Fin W) ℂ}
    (hp : 0 < p) (hp1 : p < 1) (hA : A.PosSemidef) (hW1 : (1 : ℝ) ≤ W)
    (hK0 : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hCc : 0 ≤ Cc) (hCL : 0 ≤ CL) (hC₄ : 0 ≤ C₄)
    (hK : K * ρ + 2 * CL ≤ K) (hδd : jetDistance0 b E X ≤ d) (hdK : K * d ≤ 1)
    {ξ : LayerSample W .oneBlockOnePort → ℝ} (hξm : AEStronglyMeasurable ξ (freshLaw W b))
    (hξ : ∀ᵐ ν ∂freshLaw W b,
      cec_freshJet0 b E X ν ≤ ρ * jetDistance0 b E X + Cc / (W : ℝ) ^ 2 + |ξ ν|)
    (hξ2 : eLpNorm ξ 2 (freshLaw W b) ≤ ENNReal.ofReal (Cc * Real.sqrt 2 / W))
    (hL4 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 4) ∂freshLaw W b ≤ ENNReal.ofReal C₄)
    (hlog : ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
          ∂freshLaw W b +
        ENNReal.ofReal (cL / W) * ENNReal.ofReal (fracTrace p A ^ 2 / A.trace.re ^ p) ≤
      ENNReal.ofReal ((1 + CL * jetDistance0 b E X + CL / (W : ℝ) ^ 2) * fracTrace p A) +
        ENNReal.ofReal (CL / W) * ENNReal.ofReal
          (|conductanceOf (passiveTransmission b E X)| ^ (2 * (1 - p)) * A.trace.re ^ p))
    (hC' : C' = (1 + K * (ρ * d + Cc)) * CL + (K * Cc * (1 + CL * d + CL) + CL * (1 + K * d)) +
      K * ((Cc * Real.sqrt 2) ^ 2 + (1 + C₄)) / 2) :
    ∫⁻ ν, ENNReal.ofReal (cec_oneLayerValue K b E p X A ν) ∂freshLaw W b +
        ENNReal.ofReal (cL / W) * ENNReal.ofReal (fracTrace p A ^ 2 / A.trace.re ^ p) ≤
      ENNReal.ofReal (1 + C' / W) * ENNReal.ofReal ((1 + K * jetDistance0 b E X) * fracTrace p A) +
        ENNReal.ofReal (C' / W) * ENNReal.ofReal
          (|conductanceOf (passiveTransmission b E X)| ^ (2 * (1 - p)) * A.trace.re ^ p) := by
  have := cel_isProbabilityMeasure_freshLaw W b
  set δ := jetDistance0 b E X
  set H := fracTrace p A
  set Q := fracTrace p A ^ 2 / A.trace.re ^ p
  set F := |conductanceOf (passiveTransmission b E X)| ^ (2 * (1 - p)) * A.trace.re ^ p
  set Bx := (Cc * Real.sqrt 2) ^ 2 + (1 + C₄)
  set L := freshL b E X
  have hW0 : (0 : ℝ) < W := by linarith
  set u := (W : ℝ)⁻¹
  have hu0 : 0 ≤ u := inv_nonneg.mpr hW0.le
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hW1
  have eW : ∀ x : ℝ, x / W = x * u := fun x => div_eq_mul_inv _ _
  have eW2 : ∀ x : ℝ, x / (W : ℝ) ^ 2 = x * u ^ 2 := fun x => by
    rw [div_eq_mul_inv, inv_pow]
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hH0 : 0 ≤ H := fracTrace_nonneg p A
  have hγ0 : 0 ≤ A.trace.re := (Complex.le_def.mp hA.trace_nonneg).1
  have hF0 : 0 ≤ F := mul_nonneg (by positivity) (Real.rpow_nonneg hγ0 _)
  have hQ0 : 0 ≤ Q := div_nonneg (sq_nonneg _) (Real.rpow_nonneg hγ0 _)
  have hBx : 0 ≤ Bx := by positivity
  set M := 1 + K * (ρ * δ + Cc * u ^ 2)
  have hM0 : 0 ≤ M := by positivity
  have hM1 : 1 ≤ M := by
    have : 0 ≤ K * (ρ * δ + Cc * u ^ 2) := by positivity
    linarith
  -- the cross term
  have hfm : Measurable fun ν => ‖L ν‖ ^ (2 * p) :=
    (continuous_norm.measurable.comp (cel_measurable_freshL b E X)).pow_const _
  have hcross := cel_cross_le hξm hW0 (mul_nonneg hCc (Real.sqrt_nonneg 2)) hC₄ hp.le hp1.le
    (fun ν => norm_nonneg (L ν)) hξ2 hL4
  -- pointwise weight step
  have hpt : ∀ᵐ ν ∂freshLaw W b, ENNReal.ofReal (cec_oneLayerValue K b E p X A ν) ≤
      ENNReal.ofReal M * ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν)) +
        ENNReal.ofReal (K * H) * ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * p)) := by
    filter_upwards [hξ] with ν hν
    have hHp : fracTrace p ((L ν)ᴴ * A * L ν) ≤ ‖L ν‖ ^ (2 * p) * H :=
      fracTrace_conjTranspose_mul_mul_le_of_norm_le hA (L ν) (norm_nonneg _) le_rfl hp.le
    have hHp0 : 0 ≤ fracTrace p ((L ν)ᴴ * A * L ν) := fracTrace_nonneg _ _
    rw [eW2] at hν
    have hreal : (1 + K * cec_freshJet0 b E X ν) * fracTrace p ((L ν)ᴴ * A * L ν) ≤
        M * fracTrace p ((L ν)ᴴ * A * L ν) + K * H * (|ξ ν| * ‖L ν‖ ^ (2 * p)) := by
      have h1 : (1 + K * cec_freshJet0 b E X ν) * fracTrace p ((L ν)ᴴ * A * L ν) ≤
          (M + K * |ξ ν|) * fracTrace p ((L ν)ᴴ * A * L ν) := by
        refine mul_le_mul_of_nonneg_right ?_ hHp0
        have := mul_le_mul_of_nonneg_left hν hK0
        simp only [M]; linarith
      have h2 : K * |ξ ν| * fracTrace p ((L ν)ᴴ * A * L ν) ≤
          K * |ξ ν| * (‖L ν‖ ^ (2 * p) * H) :=
        mul_le_mul_of_nonneg_left hHp (by positivity)
      nlinarith
    unfold cec_oneLayerValue
    rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul (by positivity)]
    exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le
  have hmeas : AEMeasurable (fun ν => ENNReal.ofReal (K * H) *
      ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * p))) (freshLaw W b) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hξm.aemeasurable).mul
        hfm.aemeasurable)).const_mul _
  have hint : ∫⁻ ν, ENNReal.ofReal (cec_oneLayerValue K b E p X A ν) ∂freshLaw W b ≤
      ENNReal.ofReal M * ∫⁻ ν, ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν)) ∂freshLaw W b +
        ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) := by
    calc _ ≤ ∫⁻ ν, (ENNReal.ofReal M * ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν)) +
          ENNReal.ofReal (K * H) * ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * p))) ∂freshLaw W b :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal M * ∫⁻ ν, ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν)) ∂freshLaw W b +
          ENNReal.ofReal (K * H) *
            ∫⁻ ν, ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * p)) ∂freshLaw W b := by
          rw [lintegral_add_right' _ hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by gcongr
  set I := ∫⁻ ν, ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν)) ∂freshLaw W b
  rw [eW2, eW CL] at hlog
  have hreal := cel_weight_real (F := F) hK0 hρ0 hρ1 hCL hCc hδ0 hδd hdK hK hH0 hF0 hBx hu0 hu1
  rw [← hC'] at hreal
  have hcQ : ENNReal.ofReal (cL / W) * ENNReal.ofReal Q ≤
      ENNReal.ofReal M * (ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) := by
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal M := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hM1
    calc _ = 1 * (ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) := (one_mul _).symm
      _ ≤ _ := by gcongr
  calc ∫⁻ ν, ENNReal.ofReal (cec_oneLayerValue K b E p X A ν) ∂freshLaw W b +
        ENNReal.ofReal (cL / W) * ENNReal.ofReal Q
      ≤ ENNReal.ofReal M * I + ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) +
          ENNReal.ofReal M * (ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) := add_le_add hint hcQ
    _ = ENNReal.ofReal M * (I + ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) +
          ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) := by
        rw [mul_add]; ring
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal ((1 + CL * δ + CL * u ^ 2) * H) +
          ENNReal.ofReal (CL * u) * ENNReal.ofReal F) +
          ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) := by gcongr
    _ = ENNReal.ofReal (M * ((1 + CL * δ + CL * u ^ 2) * H) + M * (CL * u * F) +
          K * H * (Bx * u / 2)) := by
        have e3 : Bx / (2 * W) = Bx * u / 2 := by simp only [u]; field_simp
        have h1 : 0 ≤ (1 + CL * δ + CL * u ^ 2) * H := by positivity
        have h2 : 0 ≤ CL * u * F := by positivity
        rw [e3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add h1 h2,
          ← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((1 + C' * u) * ((1 + K * δ) * H) + C' * u * F) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (1 + C' / W) * ENNReal.ofReal ((1 + K * δ) * H) +
          ENNReal.ofReal (C' / W) * ENNReal.ofReal F := by
        have hC'0 : 0 ≤ C' := by
          rw [hC']
          have := mul_nonneg hK0 hBx
          have : 0 ≤ (1 + K * (ρ * d + Cc)) * CL := by
            have : 0 ≤ d := hδ0.trans hδd
            positivity
          have : 0 ≤ K * Cc * (1 + CL * d + CL) + CL * (1 + K * d) := by
            have : 0 ≤ d := hδ0.trans hδd
            positivity
          linarith
        have hCu : 0 ≤ C' * u := mul_nonneg hC'0 hu0
        rw [eW, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 + C' * u),
          ← ENNReal.ofReal_mul hCu]
        exact ENNReal.ofReal_add_le

/-- **`ClockFractionalOneLayer` from the deterministic logistic inequality.** Hypotheses:
`TransmissionLawContract` (only `jetGap`: a stationary jet exists), `ClockLayerLogistic`,
`OnePortOperatorMoments` (at `r = 2`) and `OnePortJetContraction` (at `r = 2`). The weight is
`K = 2C/(1-ρ)`, the jet radius `d ≤ 1/(K+1)`, and the slack `e = 0`. The passivity of `pathX` is
`cel_pathX_passive` (Hermitian blocks, a.s.), the positivity of the clock
`ce_nearClock_posSemidef`. -/
theorem clockFractionalOneLayer_of_logistic (hTL : TransmissionLawContract)
    (hLog : ClockLayerLogistic) (hb : OnePortOperatorMoments) (hc : OnePortJetContraction) :
    ClockFractionalOneLayer := by
  intro b hb0 hb' E hE hE' p hp hp' s₀ s₂ hs₀ hs₀₂
  obtain ⟨s, hs⟩ := (hTL.jetGap b hb0 hb' E hE hE').1
  obtain ⟨CL, cL, dL, WL, hCL, hcL, hdL, hLogW⟩ := hLog b hb0 hb' E hE hE' p hp hp' s hs
  obtain ⟨db, hdb, hbr⟩ := hb b hb0 hb' E hE hE' s hs
  obtain ⟨C₄, Wb, hb4⟩ := hbr 2
  obtain ⟨ρ, Cc, a, dc, Wc, hρ0, hρ1, hCc, ha, hdc, hcW⟩ := hc b hb0 hb' E hE hE' s hs
  set K := 2 * CL / (1 - ρ) with hKdef
  have h1ρ : 0 < 1 - ρ := by linarith
  have hK0 : 0 ≤ K := div_nonneg (by linarith) h1ρ.le
  have hK : K * ρ + 2 * CL ≤ K := by
    have : K * (1 - ρ) = 2 * CL := by rw [hKdef]; field_simp
    nlinarith
  set d := min (min dL db) (min dc (1 / (K + 1)))
  have hd0 : 0 < d := lt_min (lt_min hdL hdb) (lt_min hdc (by positivity))
  have hdK : K * d ≤ 1 := by
    have h1 : d ≤ 1 / (K + 1) := (min_le_right _ _).trans (min_le_right _ _)
    calc K * d ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  set C₄' := max C₄ 0
  set C' := (1 + K * (ρ * d + Cc)) * CL + (K * Cc * (1 + CL * d + CL) + CL * (1 + K * d)) +
    K * ((Cc * Real.sqrt 2) ^ 2 + (1 + C₄')) / 2 with hC'
  have hC'0 : 0 ≤ C' := by positivity
  refine ⟨K, C', cL, d, s, hK0, hC'0, hcL, hd0, hs, fun t₁ R q hq => ?_⟩
  refine ⟨fun _ => 0, by simp, max (max WL Wb) (max Wc (⌈2 / a⌉₊ + 1)),
    fun W hW j _ _ => ?_⟩
  filter_upwards [ae_growthPath_isHermitian W b] with ω hω hD
  have hWL : WL ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWb : Wb ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWa : (⌈2 / a⌉₊ + 1 : ℕ) ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hWa' : ((⌈2 / a⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hWa
  have hW1 : (1 : ℝ) ≤ W := by
    have : (0 : ℝ) ≤ ⌈2 / a⌉₊ := Nat.cast_nonneg _
    push_cast at hWa'; linarith
  have h2a : 2 ≤ a * W := by
    have h1 := Nat.le_ceil (2 / a)
    push_cast at hWa'
    have : 2 / a ≤ W := by linarith
    rwa [div_le_iff₀ ha, mul_comm] at this
  obtain ⟨hD1, hD2, hD3⟩ := hD
  have hXd : cel_InJetDomain b E s d (pathX b E W j ω) :=
    ⟨cel_pathX_passive (by linarith) hE hE' j hω, hD1, hD2, hD3⟩
  have hA := ce_nearClock_posSemidef b E W j hq.2.2.2.1.1 ω
  have hdLd : d ≤ dL := (min_le_left _ _).trans (min_le_left _ _)
  have hdbd : d ≤ db := (min_le_left _ _).trans (min_le_right _ _)
  have hdcd : d ≤ dc := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨ξ, hξm, hξ, hξr⟩ := hcW W hWc _ (hXd.mono hdcd)
  have hξ2 : eLpNorm ξ 2 (freshLaw W b) ≤ ENNReal.ofReal (Cc * Real.sqrt 2 / W) := by
    have := hξr 2 (by norm_num) h2a
    rwa [ENNReal.ofReal_ofNat] at this
  have hL4 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E (pathX b E W j ω) ν‖ ^ 4) ∂freshLaw W b ≤
      ENNReal.ofReal C₄' :=
    (hb4 W hWb _ (hXd.mono hdbd)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hlog := hLogW W hWL _ (hXd.mono hdLd) _ hA
  have key := cel_weighted_det hp hp' hA hW1 hK0 hρ0 hρ1.le hCc hCL (le_max_right _ _) hK
    hXd.2.1 hdK hξm hξ hξ2 hL4 hlog hC'
  simp only [ENNReal.ofReal_zero, add_zero]
  exact key

/-- **`ClockFractionalOneLayer` from the isolated Jensen gap**: compose
`clockLayerLogistic_of_jensenGap` with `clockFractionalOneLayer_of_logistic`. Hypotheses:
`TransmissionLawContract` (existence of the stationary jet), the isolated `ClockLayerJensenGap`,
and `OnePortPassiveMean`, `OnePortOperatorMoments`, `OnePortJetContraction`. -/
theorem clockFractionalOneLayer_of_jensenGap (hTL : TransmissionLawContract)
    (hJ : ClockLayerJensenGap) (ha : OnePortPassiveMean) (hb : OnePortOperatorMoments)
    (hc : OnePortJetContraction) : ClockFractionalOneLayer :=
  clockFractionalOneLayer_of_logistic hTL (clockLayerLogistic_of_jensenGap hJ ha) hb hc

/-- **`ClockFractionalEntranceContract` from the isolated Jensen gap** (through
`clockFractionalEntrance_of_oneLayer`). Hypotheses: `EdgeClockMomentsContract`,
`TransmissionLengthUniformContract`, `ConditionalBlockGUECount`, `TransmissionLawContract`; the
isolated `ClockLayerJensenGap`; `OnePortPassiveMean`, `OnePortOperatorMoments`,
`OnePortJetContraction`. -/
theorem clockFractionalEntrance_of_jensenGap (hECM : EdgeClockMomentsContract)
    (hTLU : BlockBand.Internal.Contracts.TransmissionUniform.TransmissionLengthUniformContract)
    (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hJ : ClockLayerJensenGap) (ha : OnePortPassiveMean) (hb : OnePortOperatorMoments)
    (hc : OnePortJetContraction) : ClockFractionalEntranceContract :=
  clockFractionalEntrance_of_oneLayer hECM hTLU hCount
    (clockFractionalOneLayer_of_jensenGap hTL hJ ha hb hc)

end BlockBand.Endpoints
