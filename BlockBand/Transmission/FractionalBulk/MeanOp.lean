module

public import BlockBand.Transmission.LengthUniform.BulkMassMean

/-!
# The quadratic form of `E[LL*]`, uniformly on the bulk

Law `freshLaw W b`, deterministic passive `X`, `E ∈ bulkInterval κ`, `e = δ₀ + W⁻²`; hypothesis
`PassiveBoundsStatement`.

**`meanForm_bulk hA`**: there are `C, d, W₀` (depending on `b, κ` only) such that for `W ≥ W₀`,
`E ∈ bulkInterval κ`, passive `X` with `δ₀(X) ≤ d` and every unit vector `v`,
`Re v*E[LL*]v ≤ 1 + C(δ₀ + W⁻²)`.

This is the part of the passive cancelled-mean bound that the fractional bound uses
(`E(P_{p,+}|F) ≤ (1 + C_pδ₀ + C_pW⁻²)P_p - …`): the operator form of the inequality, not its
`q/W` refinement. Proof (with the bulk estimates, as in `massMean_strict_bulk`):
`E[LL*] = s₁ KM(KM)* + O(W⁻²)` (`freshU_mean_bulk`), `‖KM - 1‖ ≤ Cₘe` (`mm_matched0_bulk`),
`Re s₁ ≤ (bh Im ζ + ε)/(bhη + k_h u/W) ≤ 1 + K₁e` (`mm_sre`, `|Im ζ - η| ≤ Cₘe`). Strictly passive
`X` first; then every passive `X` at half the radius, by the `regX` limit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Re(s r) = Re s · r` for real `r`. -/
theorem re_mul_ofReal' (s : ℂ) (r : ℝ) : (s * r).re = s.re * r := by simp

/-- **Scalar step**: `Re s₁ ≤ 1 + (Cₘ/η_L + 2A/(bη_L)) e` from `mm_sre`'s bound. -/
theorem sre_bound {sr b h η ηL ι ε u W Cm e A : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hhlo : 1 / 2 ≤ h) (hηL : 0 < ηL) (hηLη : ηL ≤ η) (hu : 0 ≤ u) (hW : 0 < W)
    (hεle : ε ≤ A * e) (hA : 0 ≤ A) (hCm : 0 ≤ Cm) (he0 : 0 ≤ e) (hι : ι ≤ η + Cm * e)
    (hsre : sr ≤ (b * h * ι + ε) / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W))) :
    sr ≤ 1 + (Cm / ηL + 2 * A / (b * ηL)) * e := by
  have hh0 : 0 ≤ h := by linarith
  have hη : 0 < η := lt_of_lt_of_le hηL hηLη
  have hk : 0 ≤ (1 - 2 * b) + b ^ 2 * h := by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity
  have hDen : b * h * η ≤ b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W) := by
    have : 0 ≤ ((1 - 2 * b) + b ^ 2 * h) * (u / W) := by positivity
    linarith
  have hbhη : 0 < b * h * η := by
    have : 0 < h := by linarith
    positivity
  have hK0 : 0 ≤ (Cm / ηL + 2 * A / (b * ηL)) * e := by positivity
  set Nm := b * h * ι + ε
  by_cases hN : Nm ≤ 0
  · have : Nm / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hN (hbhη.le.trans hDen)
    linarith
  push Not at hN
  have hstep : Nm / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) ≤ Nm / (b * h * η) :=
    div_le_div_of_nonneg_left hN.le hbhη hDen
  refine hsre.trans (hstep.trans ?_)
  rw [div_le_iff₀ hbhη]
  have hb1 : b * h * ι ≤ b * h * (η + Cm * e) := mul_le_mul_of_nonneg_left hι (by positivity)
  have hA1 : b * h * (Cm * e) ≤ b * h * η * (Cm / ηL * e) := by
    have : Cm * e ≤ η * (Cm / ηL * e) := by
      rw [show η * (Cm / ηL * e) = (η / ηL) * (Cm * e) by ring]
      exact le_mul_of_one_le_left (by positivity) ((one_le_div hηL).mpr hηLη)
    have h2 := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ b * h by positivity)
    linarith
  have hA2 : ε ≤ b * h * η * (2 * A / (b * ηL) * e) := by
    refine hεle.trans ?_
    have hbhη' : b * ηL / 2 ≤ b * h * η := by
      have : ηL / 2 ≤ h * η := by nlinarith
      nlinarith
    rw [show b * h * η * (2 * A / (b * ηL) * e) = (b * h * η) / (b * ηL / 2) * (A * e) by
      field_simp]
    exact le_mul_of_one_le_left (by positivity) ((one_le_div (by positivity)).mpr hbhη')
  have : (1 + (Cm / ηL + 2 * A / (b * ηL)) * e) * (b * h * η) = b * h * η +
      b * h * η * (Cm / ηL * e) + b * h * η * (2 * A / (b * ηL) * e) := by ring
  rw [this]
  nlinarith

/-- `(1 + Ke)(1 + Cₘe)² ≤ 1 + (K + (2Cₘ + Cₘ²)(1 + K))e` for `0 ≤ e ≤ 1`. -/
theorem poly_bound {K Cm e : ℝ} (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (1 + K * e) * (1 + Cm * e) ^ 2 ≤ 1 + (K + (2 * Cm + Cm ^ 2) * (1 + K)) * e := by
  have he2 : e ^ 2 ≤ e := by nlinarith
  have he3 : e ^ 3 ≤ e := by nlinarith
  have hCm2 : 0 ≤ Cm ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left he2 hCm2, mul_le_mul_of_nonneg_left he2 hK,
    mul_le_mul_of_nonneg_left he3 (mul_nonneg hK hCm2), mul_le_mul_of_nonneg_left he2
      (mul_nonneg hK hCm), mul_nonneg hK hCm, mul_le_mul_of_nonneg_left he2 hCm]

/-- **Quadratic-form step**: from `‖U - s·KM KM*‖ ≤ ε'`, `Re s ≤ 1 + Ke`, `‖KM‖ ≤ 1 + Cₘe`. -/
theorem form_bound {U KM : Matrix (Fin W) (Fin W) ℂ} {s : ℂ} {K Cm e ε' : ℝ}
    (hK : 0 ≤ 1 + K * e) (hKM : ‖KM‖ ≤ 1 + Cm * e) (hs : s.re ≤ 1 + K * e)
    (hU : ‖U - s • (KM * KMᴴ)‖ ≤ ε') {v : Fin W → ℂ} (hv : vecNorm v = 1) :
    (bilinear v U v).re ≤ (1 + K * e) * (1 + Cm * e) ^ 2 + ε' := by
  have hsplit : bilinear v U v = s * ((vecNorm (KMᴴ *ᵥ v) ^ 2 : ℝ) : ℂ) +
      bilinear v (U - s • (KM * KMᴴ)) v := by
    have e1 : bilinear v (s • (KM * KMᴴ)) v = s * ((vecNorm (KMᴴ *ᵥ v) ^ 2 : ℝ) : ℂ) := by
      simp only [bilinear, smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      have hs : star v ᵥ* KM = star (KMᴴ *ᵥ v) := by
        rw [star_mulVec, conjTranspose_conjTranspose]
      rw [← mulVec_mulVec, dotProduct_mulVec, hs]
      rw [vecNorm, Real.sq_sqrt (by positivity)]
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    have e2 : bilinear v (U - s • (KM * KMᴴ)) v = bilinear v U v -
        bilinear v (s • (KM * KMᴴ)) v := by
      simp only [bilinear, sub_mulVec, dotProduct_sub]
    rw [e2, e1]; ring
  have hr0 : 0 ≤ vecNorm (KMᴴ *ᵥ v) ^ 2 := by positivity
  have hr1 : vecNorm (KMᴴ *ᵥ v) ^ 2 ≤ (1 + Cm * e) ^ 2 := by
    have := vecNorm_mulVec_le KMᴴ v
    rw [hv, mul_one, l2_opNorm_conjTranspose] at this
    exact pow_le_pow_left₀ (vecNorm_nonneg _) (this.trans hKM) 2
  have hrest : (bilinear v (U - s • (KM * KMᴴ)) v).re ≤ ε' := by
    have := norm_bilinear_le v (U - s • (KM * KMᴴ)) v
    rw [hv, one_mul, mul_one] at this
    exact (Complex.re_le_norm _).trans (this.trans hU)
  rw [hsplit, Complex.add_re, re_mul_ofReal']
  have : s.re * vecNorm (KMᴴ *ᵥ v) ^ 2 ≤ (1 + K * e) * (1 + Cm * e) ^ 2 :=
    calc s.re * vecNorm (KMᴴ *ᵥ v) ^ 2 ≤ (1 + K * e) * vecNorm (KMᴴ *ᵥ v) ^ 2 :=
          mul_le_mul_of_nonneg_right hs hr0
      _ ≤ _ := mul_le_mul_of_nonneg_left hr1 hK
  linarith

/-- **Strictly passive inputs.** -/
theorem meanForm_strict_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C d₁ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 < d₁ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₁ →
      ∀ v : Fin W → ℂ, vecNorm v = 1 →
        (bilinear v (matrixExpect (freshLaw W b) (freshU b E X)) v).re ≤
          1 + C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨C2, W2, hC2, hS1⟩ := scalarS1_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hm0⟩ := mm_matched0_bulk hA hb0 hb hκ
  set d₁ := min d₀ (min (1 / (4 * Cm + 4)) (1 / 2))
  have hd₁ : 0 < d₁ := lt_min hd₀ (lt_min (by positivity) (by norm_num))
  have hd₁0 : d₁ ≤ d₀ := min_le_left _ _
  have hd₁m : d₁ ≤ 1 / (4 * Cm + 4) := (min_le_right _ _).trans (min_le_left _ _)
  have hd₁h : d₁ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set ηL := etaLow b κ with hηLdef
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set A := 3 * C2 + Cf * (2 * CD) with hAdef
  have hA0 : 0 ≤ A := by positivity
  set K₁ := Cm / ηL + 2 * A / (b * ηL) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨K₁ + (2 * Cm + Cm ^ 2) * (1 + K₁) + Cf, d₁,
    max (max (max Wf W2) (max WD Wm)) ⌈d₁⁻¹⌉₊, by positivity, hd₁,
    fun W hW E hE X hX hdom v hv => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hηLη : ηL ≤ etaZ b E := etaLow_le (by linarith) hκ hE
  have hz2 : ‖boundaryZ b E‖ ≤ 2 := bulk_norm_z hb0 hb hκ hE
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWf, hW2⟩, hWD, hWm⟩, hWd⟩ := hW
  obtain ⟨hKMn, hsn, hU⟩ := hF W hWf E hE X hX
  obtain ⟨hW1, -, -, -, -, -, hB0, hB1, hG, hzM, -⟩ := hD W hWD E hE X hX
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = jetDistance0 b E X := ⟨_, rfl⟩
  rw [← hδdef] at hdom ⊢
  obtain ⟨e, he⟩ : ∃ e, e = δ + (W : ℝ)⁻¹ ^ 2 := ⟨_, rfl⟩
  rw [← he]
  have hδ : 0 ≤ δ := by rw [hδdef]; exact norm_nonneg _
  have hWe : (W : ℝ)⁻¹ ^ 2 ≤ e := by rw [he]; linarith
  have hW2le : (W : ℝ)⁻¹ ^ 2 = 1 / (W : ℝ) ^ 2 := by rw [inv_pow, one_div]
  have hW2e : 1 / (W : ℝ) ^ 2 ≤ e := by rw [← hW2le]; exact hWe
  have hWinv : (W : ℝ)⁻¹ ≤ d₁ := by
    rw [inv_le_comm₀ hWpos hd₁]; exact (Nat.le_ceil _).trans (by exact_mod_cast hWd)
  have hWsq : (W : ℝ)⁻¹ ^ 2 ≤ d₁ := by
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1r
    nlinarith [inv_nonneg.mpr hWpos.le]
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he1 : e ≤ 1 := by rw [he]; linarith
  have hCme : Cm * e ≤ 1 / 2 := by
    have : e ≤ 2 / (4 * Cm + 4) := by
      rw [he]; have := hd₁m
      rw [show (2 : ℝ) / (4 * Cm + 4) = 2 * (1 / (4 * Cm + 4)) by ring]
      linarith
    calc Cm * e ≤ Cm * (2 / (4 * Cm + 4)) := mul_le_mul_of_nonneg_left this hCm
      _ ≤ 1 / 2 := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
  obtain ⟨hzζ, hKM1, hh1⟩ := hm0 W hWm E hE X hX (hδdef ▸ hdom.trans hd₁0)
  rw [← hδdef, ← he] at hzζ hKM1 hh1
  have hheq : hOf b E X - 1 = ((Complex.normSq (vOf b E X) - 1 : ℝ) : ℂ) := by
    simp only [hOf, Complex.mul_conj]; push_cast; ring
  have hh1' : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e := by
    rw [hheq, Complex.norm_real, Real.norm_eq_abs] at hh1; exact hh1
  have hιb : |(zetaX b E X).im| ≤ ‖boundaryZ b E‖ + 1 := by
    have h' : |(zetaX b E X).im| ≤ ‖zetaX b E X‖ := Complex.abs_im_le_norm _
    have h'' : ‖zetaX b E X‖ ≤ ‖boundaryZ b E‖ + ‖boundaryZ b E - zetaX b E X‖ := by
      have := norm_sub_le (boundaryZ b E) (boundaryZ b E - zetaX b E X)
      rwa [sub_sub_cancel] at this
    linarith [mul_le_of_le_one_right hCm he1]
  have hsre := mm_sre hW1 hb0 hb h1 h2 hX hC2 hCf hCD hG hB0 hB1 hzM (hS1 W hW2 E hE X hX).2.2
    hsn (hh1'.trans hCme) hιb hW2e
  have hhlo : 1 / 2 ≤ Complex.normSq (vOf b E X) := by
    have := neg_abs_le (Complex.normSq (vOf b E X) - 1); linarith
  have hu0 : 0 ≤ ((mOf b E X)ᴴ * passiveY X * mOf b E X).trace.re :=
    (mm_trace_posSemidef (hX.posSemidef.conjTranspose_mul_mul_same _)).1
  have hεle : ((‖boundaryZ b E‖ + 1) * C2 + Cf * (2 * CD)) * e ≤ A * e := by
    rw [hAdef]; gcongr; linarith
  have hιη : (zetaX b E X).im ≤ etaZ b E + Cm * e := by
    have : (zetaX b E X).im - etaZ b E = -(boundaryZ b E - zetaX b E X).im := by
      simp only [etaZ, Complex.sub_im]; ring
    have := (neg_le_abs ((boundaryZ b E - zetaX b E X).im)).trans
      ((Complex.abs_im_le_norm _).trans hzζ)
    linarith
  have hsre1 : (sOne b E X).re ≤ 1 + K₁ * e :=
    sre_bound hb0 hb hhlo hηL hηLη hu0 hWpos hεle hA0 hCm he0 hιη hsre
  have hKMle : ‖kmOf b E X‖ ≤ 1 + Cm * e := by
    have := norm_add_le (kmOf b E X - 1) 1
    rw [sub_add_cancel] at this
    have h1' : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := PassiveLayer.norm_one_le'
    linarith
  have hUe : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf * e := by
    refine hU.trans ?_
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hW2e hCf
  have hfb := form_bound (by positivity) hKMle hsre1 hUe hv
  have hpb := poly_bound hK₁0 hCm he0 he1
  have : 1 + (K₁ + (2 * Cm + Cm ^ 2) * (1 + K₁) + Cf) * e =
      1 + (K₁ + (2 * Cm + Cm ^ 2) * (1 + K₁)) * e + Cf * e := by ring
  rw [this]
  linarith

/-- **Every passive input**, at half the radius (`regX` limit). -/
theorem meanForm_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C d : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 < d ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDistance0 b E X ≤ d →
      ∀ v : Fin W → ℂ, vecNorm v = 1 →
        (bilinear v (matrixExpect (freshLaw W b) (freshU b E X)) v).re ≤
          1 + C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by
  obtain ⟨C, d₁, W₁, hC, hd₁, hS⟩ := meanForm_strict_bulk hA hb0 hb hκ
  obtain ⟨W₂, hT⟩ := mm_tendsto_EU_bulk hA hb0 hb hκ
  refine ⟨C, d₁ / 2, max W₁ W₂, hC, by positivity, fun W hW E hE X hX hdom v hv => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  set Xn := PassiveCovariance.regX X
  have tδ := tendsto_jet0_regX hb0 hb h1 h2 hX
  have tU := hT W (le_trans (le_max_right _ _) hW) E hE X hX
  have hL : Tendsto (fun n => (bilinear v (matrixExpect (freshLaw W b) (freshU b E (Xn n))) v).re)
      atTop (𝓝 ((bilinear v (matrixExpect (freshLaw W b) (freshU b E X)) v).re)) := by
    have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => (bilinear v M v).re := by
      unfold bilinear
      exact Complex.continuous_re.comp (continuous_const.dotProduct
        (continuous_id.matrix_mulVec continuous_const))
    exact (hc.tendsto _).comp tU
  have hR : Tendsto (fun n => 1 + C * (jetDistance0 b E (Xn n) + (W : ℝ)⁻¹ ^ 2)) atTop
      (𝓝 (1 + C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2))) :=
    tendsto_const_nhds.add ((tδ.add_const _).const_mul _)
  have hev : ∀ᶠ n in atTop, jetDistance0 b E (Xn n) ≤ d₁ := by
    have : jetDistance0 b E X < d₁ := by linarith
    exact (tδ.eventually (gt_mem_nhds this)).mono fun n hn => hn.le
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [hev] with n hn
  exact hS W (le_trans (le_max_left _ _) hW) E hE (Xn n) (passiveY_regX_posDef hX n) hn v hv

end BlockBand.Transmission.FractionalBulk
