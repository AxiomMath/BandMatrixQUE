module

public import BlockBand.Endpoints.Response.RemoteHigherChainLayer
public import BlockBand.Endpoints.Response.ClockEntranceLayerWeight

/-!
# The weighted higher one-layer clock inequality

Part of the remote higher-moment theorem: use the same linear scalar weight as for the clock
entrance; its correlation costs `CH^r/W`, since `H_+^r ≤ ‖L‖^{2pr}H^r`. The `r`-analogue of
`ClockEntranceLayerWeight`.

* `rhc_oneLayerValue` — the one-layer integrand `(1 + Kδ_{0,+}) H_p(L*AL)^r`.
* `rhc_weight_real` — the scalar bookkeeping with a `C_L u` (instead of `C_L u²`) term.
* `rhc_weighted_det` — the deterministic weighted inequality at fixed passive `X`, `A ⪰ 0`.
* `ClockHigherOneLayer` — the conditional weighted one-layer inequality along the path, pointwise
  in the old path on the jet domain (the `r`-analogue of `ClockFractionalOneLayer`); proved in
  `clockHigherOneLayer_of` from `ClockLayerHigherLogistic`, `OnePortOperatorMoments`,
  `OnePortJetContraction` and `TransmissionLawContract` (existence of the stationary jet).
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

/-- The higher one-layer integrand `(1 + K δ_{0,+}) H_p(L*AL)^r`, `L = freshL b E X ν`. -/
def rhc_oneLayerValue (K b E p r : ℝ) (X A : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) : ℝ :=
  (1 + K * cec_freshJet0 b E X ν) * fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) ^ r

/-- The weight constant `C'' = C' + (1 + K(ρd + C_c)) C_L` of `rhc_weight_real`. -/
def rhc_weightC (K ρ CL Cc d Bx : ℝ) : ℝ :=
  (1 + K * (ρ * d + Cc)) * CL + (K * Cc * (1 + CL * d + CL) + CL * (1 + K * d)) + K * Bx / 2 +
    (1 + K * (ρ * d + Cc)) * CL

/-- **Scalar bookkeeping of the higher weight step**: as `cel_weight_real`, with the bracket
`1 + C_Lδ + C_L u` of `ClockLayerHigherLogistic`. -/
theorem rhc_weight_real {K ρ CL Cc d δ H F Bx u : ℝ} (hK0 : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hCL : 0 ≤ CL) (hCc : 0 ≤ Cc) (hδ0 : 0 ≤ δ) (hδd : δ ≤ d) (hdK : K * d ≤ 1)
    (hK : K * ρ + 2 * CL ≤ K) (hH : 0 ≤ H) (hF : 0 ≤ F) (hBx : 0 ≤ Bx) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    (1 + K * (ρ * δ + Cc * u ^ 2)) * ((1 + CL * δ + CL * u) * H) +
        (1 + K * (ρ * δ + Cc * u ^ 2)) * (CL * u * F) + K * H * (Bx * u / 2) ≤
      (1 + rhc_weightC K ρ CL Cc d Bx * u) * ((1 + K * δ) * H) +
        rhc_weightC K ρ CL Cc d Bx * u * F := by
  have h0 := cel_weight_real (F := F) hK0 hρ0 hρ1 hCL hCc hδ0 hδd hdK hK hH hF hBx hu0 hu1
  set CM := 1 + K * (ρ * d + Cc)
  set Mw := 1 + K * (ρ * δ + Cc * u ^ 2)
  have hu2 : u ^ 2 ≤ u := by rw [sq]; exact mul_le_of_le_one_left hu0 hu1
  have hd0 : 0 ≤ d := hδ0.trans hδd
  have hMw : Mw ≤ CM := by
    have : Cc * u ^ 2 ≤ Cc := mul_le_of_le_one_right hCc (hu2.trans hu1)
    have : ρ * δ ≤ ρ * d := mul_le_mul_of_nonneg_left hδd hρ0
    have : K * (ρ * δ + Cc * u ^ 2) ≤ K * (ρ * d + Cc) := mul_le_mul_of_nonneg_left (by linarith) hK0
    simp only [Mw, CM]; linarith
  have hMw0 : 0 ≤ Mw := by positivity
  have hext : Mw * (CL * (u - u ^ 2) * H) ≤ CM * CL * u * ((1 + K * δ) * H) := by
    have h1 : CL * (u - u ^ 2) * H ≤ CL * u * ((1 + K * δ) * H) := by
      have : u - u ^ 2 ≤ u := by nlinarith
      have h2 : H ≤ (1 + K * δ) * H := le_mul_of_one_le_left hH (by nlinarith)
      calc CL * (u - u ^ 2) * H ≤ CL * u * H :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hCL) hH
        _ ≤ CL * u * ((1 + K * δ) * H) := mul_le_mul_of_nonneg_left h2 (by positivity)
    calc Mw * (CL * (u - u ^ 2) * H) ≤ CM * (CL * (u - u ^ 2) * H) :=
          mul_le_mul_of_nonneg_right hMw (by have : 0 ≤ u - u ^ 2 := by linarith
                                             positivity)
      _ ≤ CM * (CL * u * ((1 + K * δ) * H)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CM * CL * u * ((1 + K * δ) * H) := by ring
  have e : Mw * ((1 + CL * δ + CL * u) * H) =
      Mw * ((1 + CL * δ + CL * u ^ 2) * H) + Mw * (CL * (u - u ^ 2) * H) := by ring
  have hF2 : 0 ≤ CM * CL * u * F := by
    have : 0 ≤ CM := by positivity
    positivity
  unfold rhc_weightC
  rw [e]
  nlinarith

/-- **The deterministic weighted higher one-layer inequality** at fixed passive `X`, `A ⪰ 0`: from
`ClockLayerHigherLogistic` at `(X, A)`, the contraction `δ_{0,+} ≤ ρδ₀ + C_c/W² + |ξ|`
(`OnePortJetContraction`), `‖ξ‖_{L²} ≤ C_c√2/W` and `E‖L‖⁴ ≤ C₄` (`OnePortOperatorMoments`), for
`pr ≤ 1`:
`E_ν[(1 + Kδ_{0,+})H_{p,+}^r] + (c/W)H^{r+1}/γ^p ≤ (1 + C'/W)(1 + Kδ₀)H^r + (C'/W) F_r`. -/
theorem rhc_weighted_det {b E p r K ρ Cc CL cL C₄ d : ℝ} {X A : Matrix (Fin W) (Fin W) ℂ}
    (hp : 0 < p) (hr : 1 ≤ r) (hpr : p * r ≤ 1) (hA : A.PosSemidef) (hW1 : (1 : ℝ) ≤ W)
    (hK0 : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hCc : 0 ≤ Cc) (hCL : 0 ≤ CL) (hC₄ : 0 ≤ C₄)
    (hK : K * ρ + 2 * CL ≤ K) (hδd : jetDistance0 b E X ≤ d) (hdK : K * d ≤ 1)
    {ξ : LayerSample W .oneBlockOnePort → ℝ} (hξm : AEStronglyMeasurable ξ (freshLaw W b))
    (hξ : ∀ᵐ ν ∂freshLaw W b,
      cec_freshJet0 b E X ν ≤ ρ * jetDistance0 b E X + Cc / (W : ℝ) ^ 2 + |ξ ν|)
    (hξ2 : eLpNorm ξ 2 (freshLaw W b) ≤ ENNReal.ofReal (Cc * Real.sqrt 2 / W))
    (hL4 : ∫⁻ ν, ENNReal.ofReal (‖freshL b E X ν‖ ^ 4) ∂freshLaw W b ≤ ENNReal.ofReal C₄)
    (hlog : ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν) ^ r)
          ∂freshLaw W b +
        ENNReal.ofReal (cL / W) * ENNReal.ofReal (fracTrace p A ^ (r + 1) / A.trace.re ^ p) ≤
      ENNReal.ofReal ((1 + CL * jetDistance0 b E X + CL / W) * fracTrace p A ^ r) +
        ENNReal.ofReal (CL / W) * ENNReal.ofReal
          (|conductanceOf (passiveTransmission b E X)| ^ ((r + 1) * (1 - p)) *
            A.trace.re ^ (p * r))) :
    ∫⁻ ν, ENNReal.ofReal (rhc_oneLayerValue K b E p r X A ν) ∂freshLaw W b +
        ENNReal.ofReal (cL / W) * ENNReal.ofReal (fracTrace p A ^ (r + 1) / A.trace.re ^ p) ≤
      ENNReal.ofReal (1 + rhc_weightC K ρ CL Cc d ((Cc * Real.sqrt 2) ^ 2 + (1 + C₄)) / W) *
          ENNReal.ofReal ((1 + K * jetDistance0 b E X) * fracTrace p A ^ r) +
        ENNReal.ofReal (rhc_weightC K ρ CL Cc d ((Cc * Real.sqrt 2) ^ 2 + (1 + C₄)) / W) *
          ENNReal.ofReal (|conductanceOf (passiveTransmission b E X)| ^ ((r + 1) * (1 - p)) *
            A.trace.re ^ (p * r)) := by
  have := cel_isProbabilityMeasure_freshLaw W b
  have hr0 : 0 < r := by linarith
  set δ := jetDistance0 b E X
  set H := fracTrace p A ^ r
  set Q := fracTrace p A ^ (r + 1) / A.trace.re ^ p
  set F := |conductanceOf (passiveTransmission b E X)| ^ ((r + 1) * (1 - p)) * A.trace.re ^ (p * r)
  set Bx := (Cc * Real.sqrt 2) ^ 2 + (1 + C₄)
  set C' := rhc_weightC K ρ CL Cc d Bx
  set L := freshL b E X
  have hW0 : (0 : ℝ) < W := by linarith
  set u := (W : ℝ)⁻¹
  have hu0 : 0 ≤ u := inv_nonneg.mpr hW0.le
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hW1
  have eW : ∀ x : ℝ, x / W = x * u := fun x => div_eq_mul_inv _ _
  have eW2 : ∀ x : ℝ, x / (W : ℝ) ^ 2 = x * u ^ 2 := fun x => by
    rw [div_eq_mul_inv, inv_pow]
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hH00 : 0 ≤ fracTrace p A := fracTrace_nonneg p A
  have hH0 : 0 ≤ H := Real.rpow_nonneg hH00 _
  have hγ0 : 0 ≤ A.trace.re := (Complex.le_def.mp hA.trace_nonneg).1
  have hF0 : 0 ≤ F := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hBx : 0 ≤ Bx := by positivity
  set M := 1 + K * (ρ * δ + Cc * u ^ 2)
  have hM0 : 0 ≤ M := by positivity
  have hM1 : 1 ≤ M := by
    have : 0 ≤ K * (ρ * δ + Cc * u ^ 2) := by positivity
    linarith
  have hfm : Measurable fun ν => ‖L ν‖ ^ (2 * (p * r)) :=
    (continuous_norm.measurable.comp (cel_measurable_freshL b E X)).pow_const _
  have hcross := cel_cross_le hξm hW0 (mul_nonneg hCc (Real.sqrt_nonneg 2)) hC₄
    (by positivity : 0 ≤ p * r) hpr (fun ν => norm_nonneg (L ν)) hξ2 hL4
  have hpt : ∀ᵐ ν ∂freshLaw W b, ENNReal.ofReal (rhc_oneLayerValue K b E p r X A ν) ≤
      ENNReal.ofReal M * ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν) ^ r) +
        ENNReal.ofReal (K * H) * ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * (p * r))) := by
    filter_upwards [hξ] with ν hν
    have hHp1 : fracTrace p ((L ν)ᴴ * A * L ν) ≤ ‖L ν‖ ^ (2 * p) * fracTrace p A :=
      fracTrace_conjTranspose_mul_mul_le_of_norm_le hA (L ν) (norm_nonneg _) le_rfl hp.le
    have hHp : fracTrace p ((L ν)ᴴ * A * L ν) ^ r ≤ ‖L ν‖ ^ (2 * (p * r)) * H := by
      calc fracTrace p ((L ν)ᴴ * A * L ν) ^ r ≤ (‖L ν‖ ^ (2 * p) * fracTrace p A) ^ r :=
            Real.rpow_le_rpow (fracTrace_nonneg _ _) hHp1 hr0.le
        _ = ‖L ν‖ ^ (2 * (p * r)) * H := by
            rw [Real.mul_rpow (by positivity) hH00, ← Real.rpow_mul (norm_nonneg _)]; ring_nf; rfl
    have hHp0 : 0 ≤ fracTrace p ((L ν)ᴴ * A * L ν) ^ r := Real.rpow_nonneg (fracTrace_nonneg _ _) _
    rw [eW2] at hν
    have hreal : (1 + K * cec_freshJet0 b E X ν) * fracTrace p ((L ν)ᴴ * A * L ν) ^ r ≤
        M * fracTrace p ((L ν)ᴴ * A * L ν) ^ r + K * H * (|ξ ν| * ‖L ν‖ ^ (2 * (p * r))) := by
      have h1 : (1 + K * cec_freshJet0 b E X ν) * fracTrace p ((L ν)ᴴ * A * L ν) ^ r ≤
          (M + K * |ξ ν|) * fracTrace p ((L ν)ᴴ * A * L ν) ^ r := by
        refine mul_le_mul_of_nonneg_right ?_ hHp0
        have := mul_le_mul_of_nonneg_left hν hK0
        simp only [M]; linarith
      have h2 : K * |ξ ν| * fracTrace p ((L ν)ᴴ * A * L ν) ^ r ≤
          K * |ξ ν| * (‖L ν‖ ^ (2 * (p * r)) * H) :=
        mul_le_mul_of_nonneg_left hHp (by positivity)
      nlinarith
    unfold rhc_oneLayerValue
    rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul (by positivity)]
    exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le
  have hmeas : AEMeasurable (fun ν => ENNReal.ofReal (K * H) *
      ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * (p * r)))) (freshLaw W b) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hξm.aemeasurable).mul
        hfm.aemeasurable)).const_mul _
  have hint : ∫⁻ ν, ENNReal.ofReal (rhc_oneLayerValue K b E p r X A ν) ∂freshLaw W b ≤
      ENNReal.ofReal M * ∫⁻ ν, ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν) ^ r) ∂freshLaw W b +
        ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) := by
    calc _ ≤ ∫⁻ ν, (ENNReal.ofReal M * ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν) ^ r) +
          ENNReal.ofReal (K * H) * ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * (p * r)))) ∂freshLaw W b :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal M * ∫⁻ ν, ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν) ^ r)
            ∂freshLaw W b + ENNReal.ofReal (K * H) *
            ∫⁻ ν, ENNReal.ofReal (|ξ ν| * ‖L ν‖ ^ (2 * (p * r))) ∂freshLaw W b := by
          rw [lintegral_add_right' _ hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by gcongr
  set I := ∫⁻ ν, ENNReal.ofReal (fracTrace p ((L ν)ᴴ * A * L ν) ^ r) ∂freshLaw W b
  rw [eW CL] at hlog
  have hreal := rhc_weight_real (F := F) hK0 hρ0 hρ1 hCL hCc hδ0 hδd hdK hK hH0 hF0 hBx hu0 hu1
  have hcQ : ENNReal.ofReal (cL / W) * ENNReal.ofReal Q ≤
      ENNReal.ofReal M * (ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) := by
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hM1
    calc _ = 1 * (ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) := (one_mul _).symm
      _ ≤ _ := by gcongr
  have hC'0 : 0 ≤ C' := by
    have hd0 : 0 ≤ d := hδ0.trans hδd
    simp only [C', rhc_weightC]; positivity
  calc ∫⁻ ν, ENNReal.ofReal (rhc_oneLayerValue K b E p r X A ν) ∂freshLaw W b +
        ENNReal.ofReal (cL / W) * ENNReal.ofReal Q
      ≤ ENNReal.ofReal M * I + ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) +
          ENNReal.ofReal M * (ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) := add_le_add hint hcQ
    _ = ENNReal.ofReal M * (I + ENNReal.ofReal (cL / W) * ENNReal.ofReal Q) +
          ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) := by
        rw [mul_add]; ring
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal ((1 + CL * δ + CL * u) * H) +
          ENNReal.ofReal (CL * u) * ENNReal.ofReal F) +
          ENNReal.ofReal (K * H) * ENNReal.ofReal (Bx / (2 * W)) := by gcongr
    _ = ENNReal.ofReal (M * ((1 + CL * δ + CL * u) * H) + M * (CL * u * F) +
          K * H * (Bx * u / 2)) := by
        have e3 : Bx / (2 * W) = Bx * u / 2 := by simp only [u]; field_simp
        have h1 : 0 ≤ (1 + CL * δ + CL * u) * H := by positivity
        have h2 : 0 ≤ CL * u * F := by positivity
        rw [e3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add h1 h2,
          ← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((1 + C' * u) * ((1 + K * δ) * H) + C' * u * F) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (1 + C' / W) * ENNReal.ofReal ((1 + K * δ) * H) +
          ENNReal.ofReal (C' / W) * ENNReal.ofReal F := by
        have hCu : 0 ≤ C' * u := mul_nonneg hC'0 hu0
        rw [eW, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 + C' * u),
          ← ENNReal.ofReal_mul hCu]
        exact ENNReal.ofReal_add_le

/-- **The conditional weighted higher one-layer inequality** (the `r`-analogue of
`ClockFractionalOneLayer`), pointwise in the old path: for `growthPathLaw`-a.e. old sample `ω` in
the scalar-jet domain `D_j`, with the old data `X_j = pathX j ω`, `A_j = nearClock j ω` held
fixed,
`E_ν[(1 + Kδ₀(X_+)) H_p(L*A_jL)^r] + (c/W) H_p^{r+1}/γ^p ≤ (1 + C/W)(1 + Kδ₀)H_p^r
  + (C/W) |g|^{(r+1)(1-p)} γ^{pr} + e(W)`.
Proved in `clockHigherOneLayer_of`. -/
def ClockHigherOneLayer : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 → ∀ s₀ s₂ : ℝ, 0 < s₀ → s₀ ≤ s₂ →
      ∃ (K C c d : ℝ) (s : ℂ), 0 ≤ K ∧ 0 ≤ C ∧ 0 < c ∧ 0 < d ∧ IsStationaryJet b E s ∧
        ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
          ∃ e : ℕ → ℝ, Tendsto (fun W : ℕ => (W : ℝ) ^ 2 * e W) atTop (𝓝 0) ∧
          ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, travelLength W t₁ R s₀ ≤ j →
            j < travelLength W t₁ R s₂ →
            ∀ᵐ ω ∂growthPathLaw W b, ω ∈ ce_jetDomain b E s d W j →
              ∫⁻ ν, ENNReal.ofReal (rhc_oneLayerValue K b E p r (pathX b E W j ω)
                  (nearClock b E W j q ω) ν) ∂freshLaw W b +
                ENNReal.ofReal (c / W) * ENNReal.ofReal
                  (ce_fracClock b E p W j q ω ^ (r + 1) / ce_clockTrace b E W j q ω ^ p) ≤
              ENNReal.ofReal (1 + C / W) *
                  ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r) +
                ENNReal.ofReal (C / W) * ENNReal.ofReal
                  (|pathConductance b E W j ω| ^ ((r + 1) * (1 - p)) *
                    ce_clockTrace b E W j q ω ^ (p * r)) + ENNReal.ofReal (e W)

/-- **`ClockHigherOneLayer` from the higher logistic inequality.** Hypotheses:
`TransmissionLawContract` (existence of the stationary jet), `ClockLayerHigherLogistic`,
`OnePortOperatorMoments` (`r = 2`) and `OnePortJetContraction` (`r = 2`). The weight is
`K = 2C/(1-ρ)`, the jet radius `≤ 1/(K+1)`, and the slack `e = 0`. -/
theorem clockHigherOneLayer_of (hTL : TransmissionLawContract) (hLog : ClockLayerHigherLogistic)
    (hb : OnePortOperatorMoments) (hc : OnePortJetContraction) : ClockHigherOneLayer := by
  intro b hb0 hb' E hE hE' p r hp hp' hr hpr s₀ s₂ hs₀ hs₀₂
  obtain ⟨s, hs⟩ := (hTL.jetGap b hb0 hb' E hE hE').1
  obtain ⟨CL, cL, dL, WL, hCL, hcL, hdL, hLogW⟩ := hLog b hb0 hb' E hE hE' p r hp hp' hr hpr s hs
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
  set C' := rhc_weightC K ρ CL Cc d ((Cc * Real.sqrt 2) ^ 2 + (1 + C₄')) with hC'
  have hC'0 : 0 ≤ C' := by
    have : 0 ≤ C₄' := le_max_right _ _
    simp only [hC', rhc_weightC]; positivity
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
  have key := rhc_weighted_det hp hr hpr.le hA hW1 hK0 hρ0 hρ1.le hCc hCL (le_max_right _ _) hK
    hXd.2.1 hdK hξm hξ hξ2 hL4 hlog
  simp only [ENNReal.ofReal_zero, add_zero]
  exact key

end BlockBand.Endpoints
