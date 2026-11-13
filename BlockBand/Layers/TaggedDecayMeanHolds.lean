module

public import BlockBand.Layers.TaggedDecayMean

/-!
# `TdcLayerMean` holds: the differentiated mean equation of one untagged layer

`tdcLayerMean_holds (hcount) (hgrad) : TdcLayerMean`, with no further hypothesis.

The analytic inputs of `tdm_layer_system` (`BlockBand.Layers.TaggedDecayMean`) are instantiated
along the exactly linear Hermitian family `X(h) = X - hS`, `S = K*YK`:
a.s. invertibility and fourth moments (`gaussianAbsorption_holds`), the exact mean identity at
every `h` (`meanEquation_holds`), the covariance derivative (`tgtCurvedClause` of
`diffCovarianceFamily_holds'`, `‖·‖ ≤ C u/W` since `K⁻*SK⁻¹ = Y`), the comparison point
(`layerComparison_holds`), the one-letter covariance (`lct_cov_one_letter`); the closure is
`tdm_core` with the margin of `strictContraction_margin`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-- `K⁻* (K*YK) K⁻¹ = Y` for `K = tdcK b E X` (Hermitian `X`, `Im z_∂ > 0`). -/
theorem tdmH_Y_eq {W : ℕ} {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹)ᴴ *
        ((tdcK b E X)ᴴ * Y * tdcK b E X) *
      (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ = Y := by
  have h1 := tdc_K_mul_inv hz hX
  change ((tdcK b E X)⁻¹)ᴴ * ((tdcK b E X)ᴴ * Y * tdcK b E X) * (tdcK b E X)⁻¹ = Y
  have h2 : ((tdcK b E X)⁻¹)ᴴ * (tdcK b E X)ᴴ = 1 := by
    rw [← conjTranspose_mul, h1, conjTranspose_one]
  calc ((tdcK b E X)⁻¹)ᴴ * ((tdcK b E X)ᴴ * Y * tdcK b E X) * (tdcK b E X)⁻¹
      = (((tdcK b E X)⁻¹)ᴴ * (tdcK b E X)ᴴ) * Y * (tdcK b E X * (tdcK b E X)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = Y := by rw [h2, h1, Matrix.one_mul, Matrix.mul_one]

/-- `X - hS` is Hermitian for real `h` and Hermitian `S`. -/
theorem tdmH_sub_isHermitian {W : ℕ} {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (hS : S.IsHermitian) (h : ℝ) : (X - (h : ℂ) • S).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_sub, conjTranspose_smul, hX.eq, hS.eq, Complex.star_def, Complex.conj_ofReal]

/-- `h ↦ X - hS` has derivative `-S`. -/
theorem tdmH_hasDerivAt_family {W : ℕ} (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    HasDerivAt (fun h : ℝ => X - (h : ℂ) • S) (-S) 0 := by
  have h1 : HasDerivAt (fun h : ℝ => (h : ℂ) • S) S 0 := by
    have := (hasDerivAt_id (0 : ℝ)).smul_const S
    simpa [Complex.coe_smul] using this
  simpa using h1.const_sub X

/-- The final error arithmetic of `tdcLayerMean_holds`. -/
theorem tdmH_final_arith {q Dm Cc Cm Cb Cv d u W wn : ℝ} (hCc : 0 ≤ Cc) (hCm : 0 ≤ Cm)
    (hCb : 0 ≤ Cb) (hCv : 0 ≤ Cv) (hd : 0 ≤ d) (hu : 0 ≤ u) (hW1 : 1 ≤ W) (hwn : wn ≤ q * Dm +
      Cc * ((Cm * d + 2 * Cm / W ^ 2) + 6 * (Cb / W ^ 2)) * u + Cc * (6 * (Cv * u / W))) :
    wn ≤ q * Dm + Cc * (3 * Cm + 6 * Cb + 6 * Cv) * (d + 1 / W) * u := by
  have hW0 : 0 < W := by linarith
  have hW2 : 1 / W ^ 2 ≤ 1 / W := by
    rw [div_le_div_iff₀ (by positivity) hW0]; nlinarith
  have hinv : 0 ≤ 1 / W := by positivity
  have e1 : Cc * ((Cm * d + 2 * Cm / W ^ 2) + 6 * (Cb / W ^ 2)) * u + Cc * (6 * (Cv * u / W)) =
      Cc * u * (Cm * d + (2 * Cm + 6 * Cb) * (1 / W ^ 2) + 6 * Cv * (1 / W)) := by
    field_simp; ring
  have k1 : (2 * Cm + 6 * Cb) * (1 / W ^ 2) ≤ (2 * Cm + 6 * Cb) * (1 / W) :=
    mul_le_mul_of_nonneg_left hW2 (by positivity)
  have k2 : Cm * d + (2 * Cm + 6 * Cb) * (1 / W ^ 2) + 6 * Cv * (1 / W) ≤
      (3 * Cm + 6 * Cb + 6 * Cv) * (d + 1 / W) := by
    nlinarith [mul_nonneg hCm hinv, mul_nonneg hCb hd, mul_nonneg hCv hd, mul_nonneg hCm hd]
  have k3 := mul_le_mul_of_nonneg_left k2 (mul_nonneg hCc hu)
  calc wn ≤ q * Dm + (Cc * ((Cm * d + 2 * Cm / W ^ 2) + 6 * (Cb / W ^ 2)) * u +
        Cc * (6 * (Cv * u / W))) := by rw [← add_assoc]; exact hwn
    _ = q * Dm + Cc * u * (Cm * d + (2 * Cm + 6 * Cb) * (1 / W ^ 2) + 6 * Cv * (1 / W)) := by
        rw [e1]
    _ ≤ q * Dm + Cc * u * ((3 * Cm + 6 * Cb + 6 * Cv) * (d + 1 / W)) := by linarith
    _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **`TdcLayerMean`: the differentiated mean equation of one untagged layer** (from the proof
of the tagged decay bound: "`|E(d₊ | X, S)| ≤ q_*|d| + Cδu + Cu/W`").

*Law.* One fresh separate-port layer `layerLaw W b .separate` (`A_a ~ GUE_W(c/W)`, `c = 1 - 2b`,
bonds `Gin(b/W)`) at `z = z_∂(E)`, conditional on the deterministic Hermitian old input `X` and
the deterministic clock `Y ⪰ 0`; source `S = K*YK`, `K = z_∂ - X`.

*Objects.* `D_j(X₊, Y₊)` (`tdcD`) for the untagged step `X₊ = B*(A - E - X)⁻¹B`, `Y₊ = L*YL`
(`layerSchur`, `clkStep`), `D_i(X, Y) = W⁻¹ Tr P_i R S R` (`tdcMaxD`), `u = W⁻¹ Re Tr Y`
(`clkTrace`), `δ = d(X)` (`matchedDistance`).

*Norms.* Complex modulus of the Bochner mean; `ℓ²` operator norms in the proof.

*Quantifiers and uniformity.* `b ∈ (0, 1/2)`, `κ > 0` first; then `d₀ > 0`, `q ∈ [0, 1)`,
`C ≥ 0`, `W₀`; uniformly in `W ≥ W₀`, Hermitian `X` with `d(X) ≤ d₀` (no norm bound), `Y ⪰ 0`,
`E ∈ bulkInterval κ`, `j`: `|E D_j(X₊, Y₊)| ≤ q max_i |D_i(X, Y)| + C (d(X) + 1/W) u`. No limits.

*Proof.* `tdm_layer_system` (differentiation of the exact mean identity along `X - hS`, the
residual derivative of the differentiated-covariance lemma, `E D_j(X₊, Y₊) = -ẇ_j`) and the
deterministic closure `tdm_core` (`q = (b + g/4)/(b + g/2)`, `g = 1 - b - t`).

*Inputs.* `Inputs.ConditionalBlockGUECount`, `Inputs.GaussianLpGradient` through the
proved `gaussianAbsorption_holds`, `meanEquation_holds`, `lct_cov_one_letter`,
`layerComparison_holds`, `strictContraction_margin`, `diffCovarianceFamily_holds'`. -/
theorem tdcLayerMean_holds (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    TdcLayerMean := by
  intro b hb0 hb1 κ hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  have habs := BlockBand.Layers.gaussianAbsorption_holds hcount
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := habs b hb0 hb1 η₀ 3 hη₀
  obtain ⟨W₃, hmean⟩ := meanEquation_holds habs b hb0 hb1 η₀ 3 hη₀
  obtain ⟨Cb, W₄, hCb, hcov1⟩ := lct_cov_one_letter habs hb0 hb1 (M := 3) hη₀
  obtain ⟨Cv, W₂, hcurv⟩ := ((diffCovarianceFamily_holds' hcount hgrad) b hb0 hb1 κ hκ).1
  obtain ⟨dc, Cc0, Wc, hdc, hcomp⟩ := layerComparison_holds hcount b hb0 hb1 κ hκ
  obtain ⟨dm, t, hdm, ht, hmarg⟩ := strictContraction_margin b hb0 hb1 κ hκ
  obtain ⟨q, Cc, hq0, hq1, hCc, hcore⟩ := tdm_core hb0 hb1 ht hη₀
  set Θ := tdmTheta0 b t η₀ with hΘ
  have hΘ0 : 0 < Θ := tdmTheta0_pos ht hη₀
  set Cm := max Cc0 0 with hCm
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  set Cv' := max Cv 0 with hCv'
  have hCv'0 : 0 ≤ Cv' := le_max_right _ _
  set N : ℝ := 8 * (Cm + Cb + 1) / Θ with hN
  refine ⟨min (min dc dm) (Θ / (2 * (Cm + 1))), q, Cc * (3 * Cm + 6 * Cb + 6 * Cv'),
    max (max (max W₂ W₃) (max W₄ Wc)) (max ⌈4 / ε₁⌉₊ ⌈N⌉₊),
    lt_min (lt_min hdc hdm) (by positivity), hq0, hq1, by positivity, ?_⟩
  intro W hW hWW X Y hX hY E hE hd j
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hWW
  have hW4 : W₄ ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWe : ⌈4 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hWN : ⌈N⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hWW
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW4' : ((4 : ℕ) : ℝ) ≤ ε₁ * W := by
    have h1 : 4 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWe)
    rw [div_le_iff₀ hε₁] at h1; push_cast; linarith
  have hNW : N ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWN)
  have hinvW : 1 / (W : ℝ) ≤ Θ / (8 * (Cm + Cb + 1)) := by
    rw [div_le_div_iff₀ hWr (by positivity), one_mul]
    rw [hN, div_le_iff₀ hΘ0] at hNW
    linarith
  have hd0 : 0 ≤ matchedDistance b E X := clk_matchedDistance_nonneg b E X
  have hdc' : matchedDistance b E X ≤ dc := hd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdm' : matchedDistance b E X ≤ dm := hd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdΘ : matchedDistance b E X ≤ Θ / (2 * (Cm + 1)) := hd.trans (min_le_right _ _)
  obtain ⟨hzη, hzM, hE2⟩ := hbulk E hE
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη₀ hzη
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  set μ := layerLaw W b .separate with hμ
  set z := boundaryZ b E with hzdef
  set K := tdcK b E X with hK
  set S := Kᴴ * Y * K with hSdef
  have hS : S.PosSemidef := hY.conjTranspose_mul_mul_same K
  have hXh : ∀ h : ℝ, (X - (h : ℂ) • S).IsHermitian := tdmH_sub_isHermitian hX hS.isHermitian
  have hu0 : 0 ≤ clkTrace Y := clkTrace_nonneg hY
  -- the analytic inputs
  have hinv : ∀ h : ℝ, ∀ᵐ ω ∂μ, IsUnit (layerMatrix .separate E z (X - (h : ℂ) • S) ω).det :=
    fun h => (habs' W hW .separate _ (hXh h) E z hzη hzM).1
  have hmom : ∀ h : ℝ, Integrable (fun ω => ‖layerResolvent .separate E z
        (X - (h : ℂ) • S) ω‖ ^ 4) μ ∧
      ∫ ω, ‖layerResolvent .separate E z (X - (h : ℂ) • S) ω‖ ^ 4 ∂μ ≤ CA ^ 4 :=
    fun h => tcv_moment (m := 4) (by norm_num) hCA.le
      ((habs' W hW .separate _ (hXh h) E z hzη hzM).2 _ (by norm_num) hW4')
  have hmean' := fun h : ℝ => hmean W hW hW3 .separate (X - (h : ℂ) • S) (hXh h) E z hzη hzM
  have hcurv' : ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      HasDerivAt (fun h : ℝ => dcvCov μ
          (fun ω => (W : ℂ)⁻¹ * (D * layerResolvent .separate E z (X - (h : ℂ) • S) ω).trace)
          (fun ω => layerResolvent .separate E z (X - (h : ℂ) • S) ω))
        (dcvCovDir μ D (fun ω => layerResolvent .separate E z X ω) (dcvHat S)) 0 ∧
      ‖dcvCovDir μ D (fun ω => layerResolvent .separate E z X ω) (dcvHat S)‖ ≤
        Cv' * clkTrace Y / W := by
    intro D hD
    obtain ⟨h1, -, h3, h4⟩ := hcurv W hW hW2 X S hX hS E hE D hD (fun h : ℝ => X - (h : ℂ) • S) 1
      one_pos (by simp) (tdmH_hasDerivAt_family X S) (fun h _ => hXh h)
    refine ⟨h1, (h3.trans h4).trans ?_⟩
    have hYe := tdmH_Y_eq hz hX Y
    rw [hYe]
    have : (W : ℝ)⁻¹ * Y.trace.re = clkTrace Y := rfl
    rw [this]
    gcongr
    exact le_max_left _ _
  obtain ⟨⟨m, uu, -, -, hmu, hmeans⟩, -⟩ := hcomp W hW hWc X hX E hE hdc'
  have hcmp : ∀ i, ‖meqMeanA μ (layerResolvent .separate E z X) i - matchedA E‖ +
      ‖meqMeanP μ (layerResolvent .separate E z X) i - matchedA E‖ ≤
        Cm * matchedDistance b E X + 2 * Cm / (W : ℝ) ^ 2 := by
    intro i
    have h1 := (hmeans i).1
    have h2 := (hmeans i).2
    have h3 := hmu i
    have k1 : Cc0 * matchedDistance b E X ≤ Cm * matchedDistance b E X :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
    have k2 : Cc0 / (W : ℝ) ^ 2 ≤ Cm / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    have t1 := norm_sub_le_norm_sub_add_norm_sub
      (meqMeanA μ (layerResolvent .separate E z X) i) (m i) (matchedA E)
    have t2 := norm_sub_le_norm_sub_add_norm_sub
      (meqMeanP μ (layerResolvent .separate E z X) i) (uu i) (matchedA E)
    unfold meqMeanA at t1
    unfold meqMeanP at t2
    unfold meqMeanA meqMeanP
    have e2 : 2 * Cm / (W : ℝ) ^ 2 = Cm / (W : ℝ) ^ 2 + Cm / (W : ℝ) ^ 2 := by ring
    rw [e2]
    linarith
  have hcov : ∀ P Q : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖P‖ ≤ 1 →
      ‖Q‖ ≤ 1 → ‖meqCov μ (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent .separate E z X ω).trace)
        (fun ω => Q * layerResolvent .separate E z X ω)‖ ≤ Cb / (W : ℝ) ^ 2 :=
    fun P Q hP hQ => hcov1 W hW hW4 .separate X hX E z hzη hzM P Q hP hQ
  obtain ⟨gA, gP, v, w, rp, Gb, Gd, Res, Rd, hθ, hRes, hRd, hrp, hGb, hGd, hv, hport, hEw⟩ :=
    tdm_layer_system hW hb0 hb1 hE2 hz hX hY hinv hmom hmean' hcurv' hcmp hcov
  -- thresholds
  have hθΘ : Cm * matchedDistance b E X + 2 * Cm / (W : ℝ) ^ 2 ≤ Θ := by
    have k1 : Cm * matchedDistance b E X ≤ Θ / 2 := by
      have := mul_le_mul_of_nonneg_left hdΘ hCm0
      have e : Cm * (Θ / (2 * (Cm + 1))) = Θ / 2 * (Cm / (Cm + 1)) := by field_simp
      have hf : Cm / (Cm + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    have k2 : 2 * Cm / (W : ℝ) ^ 2 ≤ Θ / 2 := by
      have hW2 : 1 / (W : ℝ) ^ 2 ≤ 1 / W := by
        rw [div_le_div_iff₀ (by positivity) hWr]; nlinarith
      have hfrac : Θ / (8 * (Cm + Cb + 1)) * (Cm + Cb + 1) = Θ / 8 := by field_simp
      have : 2 * Cm / (W : ℝ) ^ 2 = 2 * Cm * (1 / (W : ℝ) ^ 2) := by ring
      rw [this]
      have h3 : 2 * Cm * (1 / (W : ℝ) ^ 2) ≤ 2 * (Cm + Cb + 1) * (Θ / (8 * (Cm + Cb + 1))) := by
        have := hW2.trans hinvW
        have hb0' : 0 ≤ 1 / (W : ℝ) ^ 2 := by positivity
        nlinarith
      nlinarith
    linarith
  have hρΘ : 6 * (Cb / (W : ℝ) ^ 2) ≤ Θ := by
    have hW2 : 1 / (W : ℝ) ^ 2 ≤ 1 / W := by
      rw [div_le_div_iff₀ (by positivity) hWr]; nlinarith
    have hfrac : Θ / (8 * (Cm + Cb + 1)) * (Cm + Cb + 1) = Θ / 8 := by field_simp
    have : 6 * (Cb / (W : ℝ) ^ 2) = 6 * Cb * (1 / (W : ℝ) ^ 2) := by ring
    rw [this]
    have := hW2.trans hinvW
    have hb0' : 0 ≤ 1 / (W : ℝ) ^ 2 := by positivity
    nlinarith
  have hw := hcore E hE2 hzη X Y hX hY (fun i => hmarg W hW X hX E hE hdm' i) gA gP v w rp Gb Gd
    Res Rd _ _ _ hθ hθΘ hRes hρΘ hRd hrp hGb hGd hv hport j
  rw [hEw j, norm_neg]
  exact tdmH_final_arith hCc hCm0 hCb hCv'0 hd0 hu0 hW1 hw

end BlockBand.Layers
