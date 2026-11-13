module

public import BlockBand.SourceProcess.PhysApprox.B3FourGram

/-!
# One fresh-layer step `u*Δ(X, F)v` under any law that splits past ⊗ fresh

Generic statements about one fresh-layer step. The law `μ` on
any sample space carries a "past" `π` and a fresh layer `φ` with `(π, φ)_*μ = μP ⊗ freshLaw`
(for the closed law this is `closedLaw_map_past_fresh`).
* `lintegral_bilinear_four_map`: the abstract conditional fourth moment
  `Four.lintegral_bilinear_four_le` transported along `(π, φ)`.
* `norm_bilinear_freshMean_le`: the fresh mean of `u*Δ(X)v` is at most
  `C_m C_f²(δ₀(X) + W⁻¹)` for passive `X` and `‖u‖, ‖v‖ ≤ C_f`.
* **`lintegral_bilinear_freshDelta_four_le`**: with past-measurable
  frames bounded by `C_f` and passive `X`, `E|u*Δ(X, φ)v|⁴ ≤ E_P[C C_f⁸(δ₀(X) + W^{-1/2})⁴]`,
  uniformly in the sample space, `W ≥ W₀` and the laws.
* `lintegral_jetWeight_le`: if moreover `E_P δ₀(X)⁴ ≤ C_δ/W²`, the bound is
  `8 C C_f⁸(C_δ⁺ + 1)/W²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.StepFresh

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

/-- **Four's abstract step along a past/fresh split**: if `(π, φ)_*μ = μP ⊗ μF`, then
`E_μ|a(π)*D(π, φ)c(π)|⁴ ≤ E_{μP} 8(|a*(E_F D)c|⁴ + s⁴)` when `‖a*(D − E_F D)c‖_{L⁴(μF)} ≤ s`. -/
theorem lintegral_bilinear_four_map {Ω P F : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    [MeasurableSpace F] (μ : Measure Ω) (μP : Measure P) [SFinite μP] (μF : Measure F)
    [IsProbabilityMeasure μF] {π : Ω → P} {φ : Ω → F} (hπ : Measurable π) (hφ : Measurable φ)
    (hmap : μ.map (fun y => (π y, φ y)) = μP.prod μF) {W : ℕ}
    (a c : P → Fin W → ℂ) (D : P → F → Matrix (Fin W) (Fin W) ℂ)
    (hΦ : Measurable fun z : P × F => ‖bilinear (a z.1) (D z.1 z.2) (c z.1)‖ₑ ^ 4)
    (hI : ∀ᵐ p ∂μP, ∀ i j, Integrable (fun f => D p f i j) μF)
    (s : P → ℝ) (hs0 : ∀ p, 0 ≤ s p)
    (hs : ∀ᵐ p ∂μP, eLpNorm (fun f => bilinear (a p) (D p f - matrixExpect μF (D p)) (c p))
      (ENNReal.ofReal 4) μF ≤ ENNReal.ofReal (s p)) :
    ∫⁻ y, ‖bilinear (a (π y)) (D (π y) (φ y)) (c (π y))‖ₑ ^ 4 ∂μ ≤
      ∫⁻ p, 8 * (‖bilinear (a p) (matrixExpect μF (D p)) (c p)‖ₑ ^ 4 +
        ENNReal.ofReal (s p ^ 4)) ∂μP := by
  calc ∫⁻ y, ‖bilinear (a (π y)) (D (π y) (φ y)) (c (π y))‖ₑ ^ 4 ∂μ
      = ∫⁻ z, ‖bilinear (a z.1) (D z.1 z.2) (c z.1)‖ₑ ^ 4 ∂(μP.prod μF) := by
        rw [← hmap, lintegral_map hΦ (hπ.prodMk hφ)]
    _ ≤ _ := Four.lintegral_bilinear_four_le μP μF a c D hΦ.aemeasurable hI s hs0 hs

theorem enorm_pow_four_le_ofReal {z : ℂ} {q : ℝ} (h : ‖z‖ ≤ q) :
    ‖z‖ₑ ^ 4 ≤ ENNReal.ofReal (q ^ 4) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 4)

theorem bulk_of_lt {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (2 + E) (2 - E) ∧ E ∈ bulkInterval (min (2 + E) (2 - E)) :=
  ⟨lt_min (by linarith) (by linarith),
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩⟩

/-- **The fresh mean of one step**: for passive `X` and frames
bounded by `C_f`, `|u*(E_FΔ(X))v| ≤ C_m C_f²(δ₀(X) + W⁻¹)`. -/
theorem norm_bilinear_freshMean_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ (Cm : ℝ) (W₀ : ℕ), 0 ≤ Cm ∧ ∀ W : ℕ, W₀ ≤ W → ∀ (X : Matrix (Fin W) (Fin W) ℂ)
      (u v : Fin W → ℂ) (Cf : ℝ), (passiveY X).PosSemidef → vecNorm u ≤ Cf → vecNorm v ≤ Cf →
        ‖bilinear u (matrixExpect (freshLaw W b) (freshDelta b E X)) v‖ ≤
          Cm * Cf ^ 2 * (jetDistance0 b E X + (W : ℝ)⁻¹) := by
  obtain ⟨hκ, hEκ⟩ := bulk_of_lt hE1 hE2
  obtain ⟨Cm, _, W₁, hCm, _, hD⟩ :=
    RawTag.delta_fresh_bounds hGA hLp b hb0 hb _ hκ 1 le_rfl
  refine ⟨Cm, W₁, hCm, fun W hW X u v Cf hX hu hv => ?_⟩
  have hu0 := vecNorm_nonneg u
  have hv0 := vecNorm_nonneg v
  have hCf : 0 ≤ Cf := hu0.trans hu
  have hδ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hm := (hD W hW E hEκ X hX).2.1
  have hB : 0 ≤ Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) :=
    mul_nonneg hCm (add_nonneg hδ (by positivity))
  refine (norm_bilinear_le u _ v).trans ?_
  calc vecNorm u * ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ * vecNorm v
      ≤ Cf * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹)) * Cf :=
        mul_le_mul (mul_le_mul hu hm (norm_nonneg _) hCf) hv hv0 (mul_nonneg hCf hB)
    _ = Cm * Cf ^ 2 * (jetDistance0 b E X + (W : ℝ)⁻¹) := by ring

/-- **The stopped fourth moment of one fresh step under a past/fresh split** (
at `p = 4`): uniformly in the sample space, the laws and `W ≥ W₀`, for past-measurable frames
bounded by `C_f` and a past-measurable input `X` that is passive `μP`-a.e.,
`E_μ|a(π)*Δ(X(π), φ)c(π)|⁴ ≤ E_{μP}[C C_f⁸(δ₀(X) + W^{-1/2})⁴]`. -/
theorem lintegral_bilinear_freshDelta_four_le (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ {Ω P : Type*} [MeasurableSpace Ω]
      [MeasurableSpace P] (μ : Measure Ω) (μP : Measure P) [SFinite μP] {π : Ω → P}
      {φ : Ω → LayerSample W .oneBlockOnePort}, Measurable π → Measurable φ →
      μ.map (fun y => (π y, φ y)) = μP.prod (freshLaw W b) →
      ∀ (a c : P → Fin W → ℂ) (X : P → Matrix (Fin W) (Fin W) ℂ) (Cf : ℝ),
      Measurable a → Measurable c → Measurable X → 0 ≤ Cf → (∀ p, vecNorm (a p) ≤ Cf) →
      (∀ p, vecNorm (c p) ≤ Cf) → (∀ᵐ p ∂μP, (passiveY (X p)).PosSemidef) →
        ∫⁻ y, ‖bilinear (a (π y)) (freshDelta b E (X (π y)) (φ y)) (c (π y))‖ₑ ^ 4 ∂μ ≤
          ∫⁻ p, ENNReal.ofReal (C * Cf ^ 8 *
            (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹) ^ 4) ∂μP := by
  obtain ⟨hκ, hEκ⟩ := bulk_of_lt hE1 hE2
  obtain ⟨Cm, Cfl, W₁, hCm, hCfl, hD⟩ :=
    RawTag.delta_fresh_bounds hGA hLp b hb0 hb _ hκ 4 (by norm_num)
  refine ⟨8 * (Cm ^ 4 + Cfl ^ 4), max W₁ 1, by positivity, fun W hW Ω P _ _ μ μP _ π φ hπ hφ
    hmap a c X Cf ha hc hX hCf hab hcb hpas => ?_⟩
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hsqW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hinv : (W : ℝ)⁻¹ ≤ (Real.sqrt W)⁻¹ := by
    refine inv_anti₀ hsqW ?_
    rw [Real.sqrt_le_left hW0.le]; nlinarith
  have hw : 0 ≤ (Real.sqrt W)⁻¹ := inv_nonneg.2 hsqW.le
  have hδ0 : ∀ p, 0 ≤ jetDistance0 b E (X p) := fun p => norm_nonneg _
  have hA : ∀ p, 0 ≤ Cfl * ((Real.sqrt W)⁻¹ + jetDistance0 b E (X p)) := fun p =>
    mul_nonneg hCfl (add_nonneg hw (hδ0 p))
  set s : P → ℝ := fun p => Cfl * ((Real.sqrt W)⁻¹ + jetDistance0 b E (X p)) * Cf * Cf
    with hs_def
  have hs0 : ∀ p, 0 ≤ s p := fun p => mul_nonneg (mul_nonneg (hA p) hCf) hCf
  have hDm : Measurable fun z : P × LayerSample W .oneBlockOnePort =>
      freshDelta b E (X z.1) z.2 :=
    FullSource.measurable_freshDelta_comp b E (hX.comp measurable_fst) measurable_snd
  have hΦ : Measurable fun z : P × LayerSample W .oneBlockOnePort =>
      ‖bilinear (a z.1) (freshDelta b E (X z.1) z.2) (c z.1)‖ₑ ^ 4 :=
    (RawTag.measurable_bilinear_jt (ha.comp measurable_fst) hDm
      (hc.comp measurable_fst)).enorm.pow_const 4
  have hstep := lintegral_bilinear_four_map μ μP (freshLaw W b) hπ hφ hmap a c
    (fun p F => freshDelta b E (X p) F) hΦ
    (hpas.mono fun p hp => (hD W hW₁ E hEκ (X p) hp).1) s hs0
    (hpas.mono fun p hp => by
      refine ((hD W hW₁ E hEκ (X p) hp).2.2 (a p) (c p)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      calc Cfl * ((Real.sqrt W)⁻¹ + jetDistance0 b E (X p)) * vecNorm (a p) * vecNorm (c p)
          ≤ Cfl * ((Real.sqrt W)⁻¹ + jetDistance0 b E (X p)) * Cf * vecNorm (c p) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hab p) (hA p))
              (vecNorm_nonneg _)
        _ ≤ s p := mul_le_mul_of_nonneg_left (hcb p) (mul_nonneg (hA p) hCf))
  refine hstep.trans (lintegral_mono_ae ?_)
  filter_upwards [hpas] with p hp
  have hB : 0 ≤ Cm * (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹) :=
    mul_nonneg hCm (add_nonneg (hδ0 p) hw)
  have hmean : ‖bilinear (a p) (matrixExpect (freshLaw W b) (freshDelta b E (X p))) (c p)‖ ≤
      Cm * Cf ^ 2 * (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹) := by
    refine (norm_bilinear_le (a p) _ (c p)).trans ?_
    have hm := (hD W hW₁ E hEκ (X p) hp).2.1
    have hm' : ‖matrixExpect (freshLaw W b) (freshDelta b E (X p))‖ ≤
        Cm * (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹) :=
      hm.trans (mul_le_mul_of_nonneg_left (by linarith) hCm)
    calc vecNorm (a p) * ‖matrixExpect (freshLaw W b) (freshDelta b E (X p))‖ * vecNorm (c p)
        ≤ Cf * (Cm * (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹)) * Cf :=
          mul_le_mul (mul_le_mul (hab p) hm' (norm_nonneg _) hCf) (hcb p) (vecNorm_nonneg _)
            (mul_nonneg hCf hB)
      _ = Cm * Cf ^ 2 * (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹) := by ring
  have hm4 := enorm_pow_four_le_ofReal hmean
  calc 8 * (‖bilinear (a p) (matrixExpect (freshLaw W b) (freshDelta b E (X p))) (c p)‖ₑ ^ 4 +
        ENNReal.ofReal (s p ^ 4))
      ≤ 8 * (ENNReal.ofReal ((Cm * Cf ^ 2 * (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹)) ^ 4) +
          ENNReal.ofReal (s p ^ 4)) := by gcongr
    _ = ENNReal.ofReal (8 * (Cm ^ 4 + Cfl ^ 4) * Cf ^ 8 *
          (jetDistance0 b E (X p) + (Real.sqrt W)⁻¹) ^ 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        simp only [hs_def]
        ring

/-- **The jet weight**: if `E_P δ⁴ ≤ C_δ/W²` then `E_P[C C_f⁸(δ + W^{-1/2})⁴] ≤
8 C C_f⁸(C_δ⁺ + 1)/W²`. -/
theorem lintegral_jetWeight_le {P : Type*} [MeasurableSpace P] (μP : Measure P)
    [IsProbabilityMeasure μP] {W : ℕ} (hW : 1 ≤ W) {C Cf Cδ : ℝ} (hC : 0 ≤ C)
    (δ : P → ℝ) (hδ0 : ∀ p, 0 ≤ δ p)
    (hδ : ∫⁻ p, ENNReal.ofReal (δ p ^ 4) ∂μP ≤ ENNReal.ofReal (Cδ / (W : ℝ) ^ 2)) :
    ∫⁻ p, ENNReal.ofReal (C * Cf ^ 8 * (δ p + (Real.sqrt W)⁻¹) ^ 4) ∂μP ≤
      ENNReal.ofReal (8 * C * Cf ^ 8 * (max Cδ 0 + 1) / (W : ℝ) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hw4 : ((Real.sqrt W)⁻¹) ^ 4 = ((W : ℝ) ^ 2)⁻¹ := by
    rw [inv_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hW0.le]
  set K := 8 * C * Cf ^ 8
  have hK : 0 ≤ K := by positivity
  have hpt : ∀ p, ENNReal.ofReal (C * Cf ^ 8 * (δ p + (Real.sqrt W)⁻¹) ^ 4) ≤
      ENNReal.ofReal K * ENNReal.ofReal (δ p ^ 4) + ENNReal.ofReal (K / (W : ℝ) ^ 2) := by
    intro p
    rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by have := hδ0 p; positivity)
      (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := Four.add_pow_four_le_real (δ p) (Real.sqrt W)⁻¹
    rw [hw4] at h
    have hCC : 0 ≤ C * Cf ^ 8 := by positivity
    calc C * Cf ^ 8 * (δ p + (Real.sqrt W)⁻¹) ^ 4
        ≤ C * Cf ^ 8 * (8 * (δ p ^ 4 + ((W : ℝ) ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left h hCC
      _ = K * δ p ^ 4 + K / (W : ℝ) ^ 2 := by simp only [K]; ring
  have hδ' : ∫⁻ p, ENNReal.ofReal (δ p ^ 4) ∂μP ≤ ENNReal.ofReal (max Cδ 0 / (W : ℝ) ^ 2) :=
    hδ.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
  calc ∫⁻ p, ENNReal.ofReal (C * Cf ^ 8 * (δ p + (Real.sqrt W)⁻¹) ^ 4) ∂μP
      ≤ ∫⁻ p, (ENNReal.ofReal K * ENNReal.ofReal (δ p ^ 4) +
          ENNReal.ofReal (K / (W : ℝ) ^ 2)) ∂μP := lintegral_mono hpt
    _ = ENNReal.ofReal K * ∫⁻ p, ENNReal.ofReal (δ p ^ 4) ∂μP +
          ENNReal.ofReal (K / (W : ℝ) ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (max Cδ 0 / (W : ℝ) ^ 2) +
          ENNReal.ofReal (K / (W : ℝ) ^ 2) := by gcongr
    _ = ENNReal.ofReal (K * (max Cδ 0 + 1) / (W : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end BlockBand.SourceProcess.PhysApprox.B3.StepFresh
