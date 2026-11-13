module

public import BlockBand.Transmission.Generator.BrBulk
public import BlockBand.Transmission.Generator.LayerBulk

/-!
# The one-layer bracket, bulk-uniform: the theorem

**`bracket_layer_bulk hGA hLp hP`**: `b ∈ (0,1/2)`, `κ > 0`, `k, l` first; then `K ≥ 0, W₀`; for
`W ≥ W₀`, `E ∈ bulkInterval κ`, every stationary jet `s` at `E` and every passive `X`:
`|E[(Re Tr T(X₊)^{k+1} - Re Tr T^{k+1})(Re Tr T(X₊)^{l+1} - Re Tr T^{l+1})] -
B_{k+1,l+1}(P)/W| ≤ K·brY⁶/√W³`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PathScalar
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

theorem brK_nonneg {K L ck cl Cσ Cε CD Cb Cν : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hck : 0 ≤ ck)
    (hcl : 0 ≤ cl) (hCσ : 0 ≤ Cσ) (hCε : 0 ≤ Cε) (hCD : 0 ≤ CD) (hCb : 0 ≤ Cb) :
    0 ≤ brK K L ck cl Cσ Cε CD Cb Cν := by
  unfold brK; positivity

theorem br_hf_le {η H A s tt Y : ℝ} (hη1 : η ≤ 1) (hs0 : 0 < s) (hH0 : 0 ≤ H) (hA : 0 ≤ A)
    (htt : tt = s * (A + H)) (htY : tt ≤ Y) : 4 * η * H ≤ 4 * Y / s := by
  rw [le_div_iff₀ hs0]
  have h1 : s * H ≤ tt := by rw [htt]; exact mul_le_mul_of_nonneg_left (by linarith) hs0.le
  have h2 : η * (s * H) ≤ 1 * (s * H) := mul_le_mul_of_nonneg_right hη1 (by positivity)
  have e : 4 * η * H * s = 4 * (η * (s * H)) := by ring
  rw [e]; linarith

theorem br_eps_le {Cε Wr s δ d q cq g Y : ℝ} (hCε : 0 ≤ Cε) (hWr : 1 ≤ Wr) (hs2 : s ^ 2 = Wr)
    (hδ : Wr * δ ≤ Y) (hd : Wr * d ≤ Y) (hqg : q ≤ cq * g) (hcq : 0 ≤ cq) (hgY : g ≤ Y)
    (hY1 : 1 ≤ Y) :
    Cε * (Wr⁻¹ ^ 2 + Wr⁻¹ * (δ + d + q / Wr)) ≤ Cε * (3 + cq) * Y / s ^ 4 := by
  have hW0 : 0 < Wr := by linarith
  have e : Cε * (Wr⁻¹ ^ 2 + Wr⁻¹ * (δ + d + q / Wr)) = Cε * (1 + Wr * δ + Wr * d + q) / s ^ 4 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [mul_assoc Cε]
  refine mul_le_mul_of_nonneg_left ?_ hCε
  have : cq * g ≤ cq * Y := mul_le_mul_of_nonneg_left hgY hcq
  have e2 : (3 + cq) * Y = Y + Y + Y + cq * Y := by ring
  rw [e2]; linarith

theorem br_nu_le {Cu CD D cq Wr s δ q g Y : ℝ} (hCu : 0 ≤ Cu) (hWr : 1 ≤ Wr) (hs2 : s ^ 2 = Wr)
    (hδ : Wr * δ ≤ Y) (hqg : q ≤ cq * g) (hcq : 0 ≤ cq) (hg : 0 ≤ g) (hgY : g ≤ Y) (hY1 : 1 ≤ Y)
    (hD0 : 0 ≤ D) (hDC : D ≤ CD) :
    Cu * (δ + Wr⁻¹ ^ 2 + q / Wr) + D * g / (2 * Wr) ≤ (Cu * (2 + cq) + CD) * Y / s ^ 2 := by
  have hW0 : 0 < Wr := by linarith
  rw [hs2]
  have e1 : δ + Wr⁻¹ ^ 2 + q / Wr = (Wr * δ + Wr⁻¹ + q) / Wr := by field_simp
  have hWi1 : Wr⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWr
  have hcY : cq * g ≤ cq * Y := mul_le_mul_of_nonneg_left hgY hcq
  have a1 : Wr * δ + Wr⁻¹ + q ≤ (2 + cq) * Y := by
    have e2 : (2 + cq) * Y = Y + Y + cq * Y := by ring
    rw [e2]; linarith
  have a2 : D * g / (2 * Wr) ≤ CD * Y / Wr := by
    have hCD : 0 ≤ CD := hD0.trans hDC
    have : D * g ≤ CD * Y := mul_le_mul hDC hgY hg hCD
    calc D * g / (2 * Wr) ≤ D * g / Wr :=
          div_le_div_of_nonneg_left (by positivity) hW0 (by linarith)
      _ ≤ CD * Y / Wr := div_le_div_of_nonneg_right this hW0.le
  rw [e1]
  have a3 : Cu * ((Wr * δ + Wr⁻¹ + q) / Wr) ≤ Cu * ((2 + cq) * Y / Wr) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right a1 hW0.le) hCu
  have e2 : (Cu * (2 + cq) + CD) * Y / Wr = Cu * ((2 + cq) * Y / Wr) + CD * Y / Wr := by ring
  rw [e2]; linarith

/-- **The one-layer bracket, bulk-uniform.** -/
theorem bracket_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (k l : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef →
        |∫ ω, (((passiveTransmission b E (freshSchur E X ω)) ^ (k + 1)).trace.re -
              ((passiveTransmission b E X) ^ (k + 1)).trace.re) *
            (((passiveTransmission b E (freshSchur E X ω)) ^ (l + 1)).trace.re -
              ((passiveTransmission b E X) ^ (l + 1)).trace.re) ∂freshLaw W b -
          transmissionBracket (transportD0 b E) (k + 1) (l + 1)
            (fun m => ((passiveTransmission b E X) ^ m).trace.re) / W| ≤
        K * (brY b E s X ^ 6 / Real.sqrt W ^ 3) := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨C4, W4, hC4, hm4⟩ := hs_moment4_bulk hA hb0 hb hκ
  obtain ⟨Cu, Wu, hCu, hUB⟩ := ubarMean_bulk hA hb0 hb hκ
  obtain ⟨Cc, Wc, hcovB⟩ := CovarianceBulk.passiveCovarianceBulk_holds hGA hLp hP b hb0 hb κ hκ
  obtain ⟨Wi, hUi⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  obtain ⟨W2, hU2⟩ := freshU_sq_integrable_bulk hA hb0 hb hκ
  set ηL := etaLow b κ
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set cq := (4 * ηL)⁻¹
  have hcq : 0 ≤ cq := by positivity
  set CD := sigmaPlus b / (2 * ηL ^ 2)
  set Cσ := sigmaPlus b
  set Cε := max Cc 0
  have hσ0 : 0 ≤ Cσ := by
    simp only [Cσ, sigmaPlus, kPlus]; have : 0 ≤ (1 - b) ^ 2 := sq_nonneg _
    have e : 1 - 2 * b + b ^ 2 = (1 - b) ^ 2 := by ring
    rw [e]; positivity
  have hCD : 0 ≤ CD := by positivity
  set ck := ((k + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (k + 1))
  set cl := ((l + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (l + 1))
  set Cν := Cu * (2 + cq) + CD
  refine ⟨brK ((k + 1 : ℕ) : ℝ) ((l + 1 : ℕ) : ℝ) ck cl (2 * Cσ) (Cε * (3 + cq)) CD (C4 ^ 4) Cν,
    max (max (max W4 Wu) (max Wc Wi)) (max W2 1),
    brK_nonneg (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) hCD (by positivity), fun W hW E hE sj hsj X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW4, hWu⟩, hWc, hWi⟩, hW2, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hs2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWpos.le
  have hs1 : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hWr
  have hs0 : 0 < Real.sqrt W := by linarith
  have hT : (passiveTransmission b E X).PosSemidef :=
    passiveTransmission_posSemidef (by linarith) h1 h2 hX
  have ht1 : ∀ i, ts_lam hT i ≤ 1 :=
    ts_lam_le_one hT (one_sub_passiveTransmission_posSemidef b E X)
  set g := (passiveTransmission b E X).trace.re
  set δ := jetDistance0 b E X
  set d := jetDistance1 b E sj X
  set q := passiveMass b E X
  set tt := Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
      hsSandwich (passiveQ b E X) (passiveF b E X))
  have hg : 0 ≤ g := (mm_trace_posSemidef hT).1
  have hδ : 0 ≤ δ := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hq0 : 0 ≤ q := passiveMass_nonneg b E hX
  have hqg : q ≤ cq * g := mass_le_bulk (by linarith) hκ hE hX
  have htt : 0 ≤ tt := mul_nonneg hs0.le (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  obtain ⟨hY1, hgY, haY, htY, hdY, hagY⟩ := brY_ge hg (mul_nonneg hWpos.le hδ) htt
    (mul_nonneg hWpos.le hd)
  set Y := brY b E sj X
  have hYe : Y = (g + 1) * (W * δ + 1) * (tt + 1) * (W * d + 1) := rfl
  rw [← hYe] at hY1 hgY haY htY hdY hagY
  obtain ⟨hD0, hDC⟩ := transportD0_le_bulk hb0 (by linarith) hκ hE
  -- the inputs of `br_law`
  set U := freshU b E X
  set μ := freshLaw W b
  have hS := ae_norm_sand_freshU_le hb0 hb hW1 h1 h2 hX hT
  set ν := Cu * (δ + (W : ℝ)⁻¹ ^ 2 + q / W) + transportD0 b E * g / (2 * W)
  have hν : ‖matrixExpect μ U - 1‖ ≤ ν :=
    (norm_ubar_sub_one_le hb0 hb h1 h2 hD0 hX _).trans (by linarith [(hUB W hWu E hE X hX).1])
  obtain ⟨hh, hH4⟩ := hm4 W hW4 E hE X hX hT
  set εv := Cε * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (δ + d + q / W))
  have hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
        (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X) +
          crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1) +
        sigmaMinus b E sj / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X) +
        conj (sigmaMinus b E sj) / W *
          crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ)‖ ≤
      εv * fourNorm v₁ v₂ v₃ v₄ := fun v₁ v₂ v₃ v₄ => by
    refine (hcovB W hWc E hE sj hsj X hX v₁ v₂ v₃ v₄).trans ?_
    have hF := fourNorm_nonneg v₁ v₂ v₃ v₄
    have hA0 : 0 ≤ (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (δ + d + q / W) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0) hF
  have hlaw := br_law hT ht1 U (measurable_freshU b E X) (freshU_isHermitian b E X)
    (hUi W hWi E hE X hX)
    (fun i m => freshU_hp4 hT U (measurable_freshU b E X) (hU2 W hW2 E hE X hX) i i m m)
    hS hν hh hH4 (passiveF b E X) (transportD0 b E / (2 * W)) (sigmaMinus b E sj / W)
    (conj (sigmaMinus b E sj) / W) hcov hs0 k l
  obtain ⟨eI, eB⟩ := br_fresh_eq hb0 hb h1 h2 hW1 hX hT k l
  rw [eI, eB]
  refine hlaw.trans ?_
  -- the bookkeeping
  have hσm : ‖sigmaMinus b E sj‖ ≤ Cσ :=
    (LawClauses.norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hsj).le
  have hσn : ‖sigmaMinus b E sj / W‖ + ‖conj (sigmaMinus b E sj) / W‖ ≤
      2 * Cσ / Real.sqrt W ^ 2 := by
    rw [norm_div, norm_div, Complex.norm_natCast, Complex.norm_conj, hs2]
    have := div_le_div_of_nonneg_right hσm hWpos.le
    linarith [show 2 * Cσ / (W : ℝ) = Cσ / W + Cσ / W by ring]
  have hη0 := (PassiveCovariance.etaZ_pos b E (by linarith) h1 h2).le
  have hη1 := etaZ_le_one hb0 (by linarith) h1 h2
  have hfY : hsSandwich (passiveTransmission b E X) (passiveF b E X) ≤ 4 * Y / Real.sqrt W := by
    rw [hsSandwich_transmission_eq b E X hη0]
    exact br_hf_le hη1 hs0 (Real.sqrt_nonneg _) (norm_nonneg _) rfl htY
  have hε : εv ≤ Cε * (3 + cq) * Y / Real.sqrt W ^ 4 :=
    br_eps_le (le_max_right _ _) hWr hs2 haY hdY hqg hcq hgY hY1
  have hr : |transportD0 b E / (2 * W)| ≤ CD / Real.sqrt W ^ 2 := by
    rw [abs_of_nonneg (by positivity), hs2]
    calc transportD0 b E / (2 * W) ≤ transportD0 b E / W :=
          div_le_div_of_nonneg_left hD0 hWpos (by linarith)
      _ ≤ CD / W := div_le_div_of_nonneg_right hDC hWpos.le
  have hH : (C4 / Real.sqrt W * g) ^ 4 ≤ C4 ^ 4 * Y ^ 4 / Real.sqrt W ^ 4 := by
    rw [show C4 / Real.sqrt W * g = C4 * g / Real.sqrt W by ring, div_pow, mul_pow]
    gcongr
  have hν0 : 0 ≤ ν := by positivity
  have hνY : ν ≤ Cν * Y / Real.sqrt W ^ 2 :=
    br_nu_le hCu hWr hs2 haY hqg hcq hg hgY hY1 hD0 hDC
  exact br_rhs_le (by positivity) (by positivity) (by positivity) (by positivity) hs1 hY1 hg hgY
    (Real.sqrt_nonneg _) hfY hσn hε hr hH hν0 hνY (by positivity) (by positivity) hCD
    (by positivity) (by positivity)

end BlockBand.Transmission.Generator
