module

public import BlockBand.Layers.WeightedLayer
public import BlockBand.Layers.BUniformClockDet
public import BlockBand.Internal.Contracts.LayersBUniform

/-!
# The clock-mean identity, uniformly in `b`

This file proves the clock-mean identity of the weighted-layer lemma in the `b`-uniform form
`LayersBUniform.ClockMeanUniformContract`, from the uniform absorption clause
`habsU : LayersBUniform.GaussianAbsorptionUniformContract` alone.

Law: `layerLaw W b .separate` (one separate-port step, `A_a ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds
`Gin(b/W)`), conditional on the deterministic Hermitian two-port `X`; `z = z_∂(E) = boundaryZ b E`,
`K = z - X`, `L = K 𝒢₁₂`, `Y ⪰ 0`, `u = W⁻¹ Tr Y`. Domain: `E ∈ bulkInterval κ`,
`d(X) = matchedDistance b E X ≤ d_*`, `W ≥ W₀`. Norms: `ℓ²` operator norm; `L^p` under `layerLaw`.

Quantifier order (that of `ClockMeanUniformContract`): `β ∈ (0,1/4)`, `κ > 0`; then `d_* > 0`, `C`, `W₀`; then
uniformly in `b ∈ [β, 1/2 - β]`, `W ≥ W₀`, Hermitian `X`, `E`, `Y`.

Uniformity: every constant depends only on `(β, κ)` and on the uniform absorption constants
`(ε₁, C)` of `GaussianAbsorptionUniformContract` at `(β, η₀, M = 3)` with `η₀ ∈ {2βα₀, α₀/2}`
(`α₀ = α₀(κ)` of `cmp_bulk_setup`).

Proof: the chain `wl_clockMean` ← `wl_ward_core` ←
`layerComparison_holds` (`lct_means`, `cmp_comparison_branch`),
`wl_cov_weighted`, `wl_moment_setup`, `wl_bulk`, with each constant made explicit:
1. `bu_tcv_of`, `bu_cov_one_letter_of`, `bu_moment_setup_of`, `bu_cov_weighted_of`: the bodies of
   `traceCovariance_holds`, `lct_cov_one_letter`, `wl_moment_setup`, `wl_cov_weighted` at a fixed
   `b`, with the absorption constants as explicit hypotheses (proof copies);
2. `bu_means_sep`: the separate clause of `lct_means` with `ζ₀ = 2βα₀` (instead of `(1-2b)α₀`)
   and `C_η = 6C_v/(β w₁/2) + ζ₀⁻¹ C_v` (instead of `b`);
3. `bu_layerComparison_sep`: the separate clause of `layerComparison_holds`, with the
   deterministic part `bu_sepComparison` (`BUniformClockDet`);
4. `bu_moment_unif`, `bu_cov_weighted_unif` (moments `q = 2, 4` and the weighted covariance,
   uniform via `habsU`); `bu_ward_at` (the body of `wl_ward_core` at a fixed `b`, constants as
   hypotheses); `bu_ward_core`: `wl_ward_core` with `η₀ = α₀/2` (instead of `(1-b)α₀`);
5. `bu_clockMeanUniform_of`: the trace pairing of `wl_clockMean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Fixed-`b` lemmas with explicit absorption constants
-/

section Explicit

variable {W : ℕ} {b : ℝ} {σ : LayerShape}

/-- The absorption clause at a fixed `b` with explicit constants `ε₁, C`. -/
def buAbsAt (b η₀ M ε₁ C : ℝ) : Prop :=
  ∀ (W : ℕ), 0 < W → ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ),
    X.IsHermitian → ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
      ∀ p : ℝ, 1 ≤ p → p ≤ ε₁ * W →
        eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal p) (layerLaw W b σ) ≤
          ENNReal.ofReal C

/-- **`traceCovariance_holds` with explicit constants** (same proof as
`traceCovariance_holds`): at fixed `b`, from the absorption clause with `ε₁, C_A`,
the covariance bound holds with `C = tcvConst L K C_A` for `W ≥ ⌈(2L+2)/ε₁⌉`. -/
theorem bu_tcv_of (hb0 : 0 < b) (hb1 : b < 1 / 2) {η₀ M ε₁ CA : ℝ} (hη : 0 < η₀)
    (hε₁ : 0 < ε₁) (hCA : 0 < CA) (habs' : buAbsAt b η₀ M ε₁ CA) (L : ℕ) (K : ℝ) :
    ∀ (W : ℕ), 0 < W → ⌈(2 * L + 2 : ℝ) / ε₁⌉₊ ≤ W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ (ℓf ℓU : ℕ), ℓf ≤ L → ℓU ≤ L →
      ∀ (εf : Fin ℓf → Bool) (Df : Fin (ℓf + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
        (εU : Fin ℓU → Bool) (DU : Fin (ℓU + 1) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ),
        (∀ j, ‖Df j‖ ≤ K) → (∀ j, ‖DU j‖ ≤ K) →
        let μ := layerLaw W b σ
        let f : LayerSample W σ → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (wordEval εf Df (layerResolvent σ E z X ω)).trace
        let U : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ := fun ω =>
          wordEval εU DU (layerResolvent σ E z X ω)
        Integrable f μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
          (∀ x y, Integrable (fun ω => f ω * U ω x y) μ) ∧
          ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ ≤
            tcvConst L K CA / (W : ℝ) ^ 2 := by
  intro W hW hW₀ σ X hX E z hz hzM ℓf ℓU hℓf hℓU εf Df εU DU hDf hDU μ f U
  obtain ⟨hinv, hmom⟩ := habs' W hW σ X hX E z hz hzM
  have hK : 0 ≤ K := (norm_nonneg _).trans (hDf 0)
  have hz0 : 0 ≤ z.im := le_trans hη.le hz
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set μc := gaussianProduct (tflVar W b σ) with hμc
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μc.map Φ := tfl_layerLaw_eq_map W b σ
  -- moments and invertibility in the coordinates
  have hεW : (2 * L + 2 : ℝ) ≤ ε₁ * W := by
    have h1 : (2 * L + 2 : ℝ) / ε₁ ≤ W :=
      (Nat.le_ceil _).trans (by exact_mod_cast hW₀)
    rw [div_le_iff₀ hε₁] at h1
    linarith
  have hinvc : ∀ᵐ x ∂μc, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hGr : Measurable (fun x => layerResolvent σ E z X (Φ x)) :=
    (measurable_layerResolvent σ E z X).comp hΦ
  have hmomc : ∀ m : ℕ, 1 ≤ m → m ≤ ℓf + ℓU + 2 →
      Integrable (fun x => ‖layerResolvent σ E z X (Φ x)‖ ^ m) μc ∧
      ∫ x, ‖layerResolvent σ E z X (Φ x)‖ ^ m ∂μc ≤ CA ^ m := by
    intro m hm1 hmn
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmε : (m : ℝ) ≤ ε₁ * W := by
      have : (m : ℝ) ≤ 2 * L + 2 := by
        have : m ≤ 2 * L + 2 := by omega
        exact_mod_cast this
      linarith
    have h := hmom m hm1' hmε
    rw [hlaw, eLpNorm_map_measure (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable
      hΦ.aemeasurable] at h
    exact tcv_moment hm1 hCA.le h
  obtain ⟨hFi, hUi, hFUi, hbd⟩ :=
    tcv_core σ E z hW hb0 hb1 hX hz0 hK εf Df εU DU hDf hDU hinvc hmomc
  -- measurability on the layer
  have hFc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      tcvTr W σ (wordEval εf Df N)) :=
    (tcvTr W σ).continuous.comp (tcv_continuous_wordEval εf Df)
  have hUc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      wordEval εU DU N) := tcv_continuous_wordEval εU DU
  have hfm : Measurable f := hFc.measurable.comp (measurable_layerResolvent σ E z X)
  have hUm : Measurable U := hUc.measurable.comp (measurable_layerResolvent σ E z X)
  have hent : ∀ x y, Measurable (fun ω => U ω x y) := fun x y =>
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp hUm)
  refine ⟨?_, fun x y => ?_, fun x y => ?_, ?_⟩
  · change Integrable f (layerLaw W b σ)
    rw [hlaw, integrable_map_measure hfm.aestronglyMeasurable hΦ.aemeasurable]
    exact hFi
  · change Integrable (fun ω => U ω x y) (layerLaw W b σ)
    rw [hlaw, integrable_map_measure (hent x y).aestronglyMeasurable hΦ.aemeasurable]
    exact (tcvEntry W σ x y).integrable_comp hUi
  · change Integrable (fun ω => f ω * U ω x y) (layerLaw W b σ)
    have hfU : Measurable (fun ω => f ω * U ω x y) := hfm.mul (hent x y)
    rw [hlaw, integrable_map_measure hfU.aestronglyMeasurable hΦ.aemeasurable]
    exact (tcvEntry W σ x y).integrable_comp hFUi
  · change ‖matrixExpect (layerLaw W b σ) (fun ω => f ω • U ω) -
      (∫ ω, f ω ∂layerLaw W b σ) • matrixExpect (layerLaw W b σ) U‖ ≤ _
    have hfUm : Measurable (fun ω => f ω • U ω) := hfm.smul hUm
    rw [tcv_matrixExpect_eq hfUm hFUi, tcv_matrixExpect_eq hUm hUi, hlaw,
      integral_map hΦ.aemeasurable hfm.aestronglyMeasurable]
    refine hbd.trans ?_
    have hc := tcv_le_const (K := K) hCA.le hℓf hℓU
    rw [abs_of_nonneg hK] at hc
    calc 10 * ℓf * ℓU * K ^ (ℓf + ℓU + 2) / (W : ℝ) ^ 2 * (2 * (2 * CA) ^ (ℓf + ℓU + 2))
        = 10 * ℓf * ℓU * K ^ (ℓf + ℓU + 2) * (2 * (2 * CA) ^ (ℓf + ℓU + 2)) / (W : ℝ) ^ 2 := by
          ring
      _ ≤ tcvConst L K CA / (W : ℝ) ^ 2 := by gcongr

/-- **`lct_cov_one_letter` with explicit constants** (same proof as
`lct_cov_one_letter`): `‖Cov(W⁻¹Tr P𝒢, Q𝒢)‖ ≤ max(tcvConst 1 1 C_A, 0)/W²` for `W ≥ ⌈4/ε₁⌉`. -/
theorem bu_cov_one_letter_of (hb0 : 0 < b) (hb1 : b < 1 / 2) {η₀ M ε₁ CA : ℝ} (hη : 0 < η₀)
    (hε₁ : 0 < ε₁) (hCA : 0 < CA) (habs' : buAbsAt b η₀ M ε₁ CA) :
    ∀ W : ℕ, 0 < W → ⌈(4 : ℝ) / ε₁⌉₊ ≤ W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ P Q : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
        ‖meqCov (layerLaw W b σ)
            (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace)
            (fun ω => Q * layerResolvent σ E z X ω)‖ ≤ max (tcvConst 1 1 CA) 0 / (W : ℝ) ^ 2 := by
  have h := bu_tcv_of hb0 hb1 hη hε₁ hCA habs' 1 1
  intro W hW hWW σ X hX E z hz hzM P Q hP hQ
  have hWW' : ⌈(2 * ((1 : ℕ) : ℝ) + 2) / ε₁⌉₊ ≤ W := by
    rw [show (2 * ((1 : ℕ) : ℝ) + 2) = 4 by norm_num]; exact hWW
  have h1 := (h W hW hWW' σ X hX E z hz hzM 1 1 le_rfl le_rfl (fun _ => false) ![P, 1]
    (fun _ => false) ![Q, 1] (lct_norm_vec_two_le hP) (lct_norm_vec_two_le hQ)).2.2.2
  simp only [← meq_mul_eq_wordEval] at h1
  exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))

/-- **`wl_moment_setup` with explicit constants** (same proof as
`wl_moment_setup`): at fixed `b`, for `q ≥ 1` and `W ≥ max(⌈2q/ε₁⌉, ⌈2q⌉)`:
`‖F‖_{L^q} ≤ 1 + 6 wlLamConst C_A` and a.s. invertibility (`Im z ≥ η₀`, `|z| ≤ 3`). -/
theorem bu_moment_setup_of (hb0 : 0 < b) (hb1 : b < 1 / 2) {η₀ ε₁ CA : ℝ}
    (hε₁ : 0 < ε₁) (hCA : 0 < CA) (habs : buAbsAt b η₀ 3 ε₁ CA) {q : ℝ} (hq : 1 ≤ q) :
    ∀ W : ℕ, 0 < W → max ⌈2 * q / ε₁⌉₊ ⌈2 * q⌉₊ ≤ W → ∀ (σ : LayerShape)
      (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian → ∀ (E : ℝ) (z : ℂ),
      η₀ ≤ z.im → ‖z‖ ≤ 3 →
        (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
        eLpNorm (wlF E z X) (ENNReal.ofReal q) (layerLaw W b σ) ≤
          ENNReal.ofReal (1 + 6 * (wlLamConst * CA)) := by
  intro W hW hWW σ X hX E z hz hzM
  obtain ⟨hinv, hmom⟩ := habs W hW σ X hX E z hz hzM
  have hW1 : 2 * q ≤ ε₁ * W := by
    have h1 : 2 * q / ε₁ ≤ (W : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hWW)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hW2 : 2 * q ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hWW)
  have := bond_isProbabilityMeasure_layerLaw W b σ
  refine ⟨hinv, ?_⟩
  exact wl_eLpNorm_F_le (continuous_norm.measurable.comp wl_measurable_wlLam).aestronglyMeasurable
    (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable hq wlLamConst_pos.le hCA.le
    (wl_lam_eLpNorm_le_layer hb0 hb1 (by linarith) hW2) (hmom _ (by linarith) hW1)

/-- **`wl_cov_weighted` with explicit constants** (same proof as
`wl_cov_weighted`): at fixed `b`, from `‖F‖_{L^4} ≤ C₄` for `W ≥ W₀`:
`‖Cov(W⁻¹ Tr P𝒢, Q𝒢) 𝒦*‖ ≤ 160 C₄⁴/W²`. -/
theorem bu_cov_weighted_of (hb0 : 0 < b) (hb1 : b < 1 / 2) {η₀ : ℝ} (hη₀ : 0 < η₀)
    {C4 : ℝ} {W₀ : ℕ} (hC4 : 0 ≤ C4)
    (hmom : ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ (σ : LayerShape)
      (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian → ∀ (E : ℝ) (z : ℂ),
      η₀ ≤ z.im → ‖z‖ ≤ 3 →
        (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
        eLpNorm (wlF E z X) (ENNReal.ofReal 4) (layerLaw W b σ) ≤ ENNReal.ofReal C4) :
    ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ (σ : LayerShape)
      (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian → ∀ (E : ℝ) (z : ℂ),
      η₀ ≤ z.im → ‖z‖ ≤ 3 → |E| ≤ 2 →
      ∀ P Q : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
        ‖meqCov (layerLaw W b σ) (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace)
            (fun ω => Q * layerResolvent σ E z X ω) *
          wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ‖ ≤
          160 * C4 ^ 4 / (W : ℝ) ^ 2 := by
  intro W hW hWW σ X hX E z hz hzM hE P Q hP hQ
  obtain ⟨hinv, hF⟩ := hmom W hW hWW σ X hX E z hz hzM
  have hz0 : 0 ≤ z.im := hη₀.le.trans hz
  set μc := gaussianProduct (tflVar W b σ) with hμc
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μc.map Φ := tfl_layerLaw_eq_map W b σ
  have hinvc : ∀ᵐ x ∂μc, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  set Fc : (TflCoord W σ → ℝ) → ℝ := fun x => wlF E z X (Φ x) with hFc
  have hFcm : Measurable Fc := (wl_measurable_wlF E z X).comp hΦ
  have hFc0 : ∀ x, 0 ≤ Fc x := fun x => wlF_nonneg _ _ _ _
  have hFcL : eLpNorm (fun x => ‖Fc x‖) (ENNReal.ofReal ((4 : ℕ) : ℝ)) μc ≤ ENNReal.ofReal C4 := by
    have e : (fun x => ‖Fc x‖) = Fc := funext fun x => Real.norm_of_nonneg (hFc0 x)
    rw [e]
    have h1 : eLpNorm Fc (ENNReal.ofReal 4) μc =
        eLpNorm (wlF E z X) (ENNReal.ofReal 4) (layerLaw W b σ) := by
      rw [hlaw, eLpNorm_map_measure (wl_measurable_wlF E z X).aestronglyMeasurable
        hΦ.aemeasurable]
      rfl
    rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, h1]
    exact hF
  obtain ⟨hF4i, hF4b⟩ := tcv_moment (m := 4) (by norm_num) hC4 hFcL
  have e4 : (fun x => ‖Fc x‖ ^ 4) = fun x => Fc x ^ 4 :=
    funext fun x => by rw [Real.norm_of_nonneg (hFc0 x)]
  rw [e4] at hF4i hF4b
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hGrdef
  have hGrm : Measurable Gr := (measurable_layerResolvent σ E z X).comp hΦ
  have hGF : ∀ x, ‖Gr x‖ ≤ Fc x := fun x => by
    have hg0 := norm_nonneg (Gr x)
    have hl0 := norm_nonneg (wlLam (Φ x))
    change ‖Gr x‖ ≤ 1 + 6 * ((1 + ‖wlLam (Φ x)‖) * ‖Gr x‖)
    nlinarith
  have hdom : Integrable (fun x => 1 + Fc x ^ 4) μc := (integrable_const 1).add hF4i
  have hG1 : Integrable (fun x => ‖Gr x‖) μc :=
    Integrable.mono' hdom hGrm.norm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      have := hGF x; have := hFc0 x
      nlinarith [sq_nonneg (Fc x), sq_nonneg (Fc x ^ 2 - 1), sq_nonneg (Fc x - 1)])
  have hG2 : Integrable (fun x => ‖Gr x‖ ^ 2) μc :=
    Integrable.mono' hdom (hGrm.norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hGF x) 2
      have := hFc0 x
      nlinarith [sq_nonneg (Fc x ^ 2 - 1)])
  have hcore := wl_cov_weighted_core hW hb0 hb1 hX hz0 hE hzM P Q hP hQ hinvc hG1 hG2 hF4i hF4b
  -- transfer `meqCov` to the coordinates
  set f : LayerSample W σ → ℂ := fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace
    with hfdef
  set U : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun ω => Q * layerResolvent σ E z X ω with hUdef
  have hGm := measurable_layerResolvent σ E z X
  have hfm : Measurable f :=
    (continuous_const.mul ((continuous_const.matrix_mul continuous_id).matrix_trace)).measurable.comp
      hGm
  have hUm : Measurable U := (continuous_const.matrix_mul continuous_id).measurable.comp hGm
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hfU_le : ∀ x, ‖f (Φ x) • U (Φ x)‖ ≤ 4 * ‖Gr x‖ ^ 2 := fun x => by
    rw [norm_smul, sq]
    have h1 : ‖f (Φ x)‖ ≤ 4 * ‖Gr x‖ := by
      refine (tcv_tr_le σ hW (P * Gr x)).trans ?_
      gcongr
      calc ‖P * Gr x‖ ≤ ‖P‖ * ‖Gr x‖ := norm_mul_le _ _
        _ ≤ 1 * ‖Gr x‖ := by gcongr
        _ = ‖Gr x‖ := one_mul _
    have h2 : ‖U (Φ x)‖ ≤ ‖Gr x‖ := (norm_mul_le _ _).trans (by
      calc ‖Q‖ * ‖Gr x‖ ≤ 1 * ‖Gr x‖ := by gcongr
        _ = ‖Gr x‖ := one_mul _)
    calc ‖f (Φ x)‖ * ‖U (Φ x)‖ ≤ (4 * ‖Gr x‖) * ‖Gr x‖ :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 4 * (‖Gr x‖ * ‖Gr x‖) := by ring
  have hiFU : Integrable (fun x => f (Φ x) • U (Φ x)) μc :=
    Integrable.mono' (hG2.const_mul 4) ((hfm.smul hUm).comp hΦ).aestronglyMeasurable
      (ae_of_all _ hfU_le)
  have hiU : Integrable (fun x => U (Φ x)) μc :=
    Integrable.mono' hG1 (hUm.comp hΦ).aestronglyMeasurable (ae_of_all _ fun x =>
      (norm_mul_le _ _).trans (by
        calc ‖Q‖ * ‖Gr x‖ ≤ 1 * ‖Gr x‖ := by gcongr
          _ = ‖Gr x‖ := one_mul _))
  have hcov : meqCov (layerLaw W b σ) f U =
      (∫ x, tcvTr W σ (P * Gr x) • (Q * Gr x) ∂μc) -
        (∫ x, tcvTr W σ (P * Gr x) ∂μc) • (∫ x, Q * Gr x ∂μc) := by
    rw [meqCov, tcv_matrixExpect_eq (Y := fun ω => f ω • U ω) (hfm.smul hUm) hiFU, tcv_matrixExpect_eq hUm hiU, hlaw,
      integral_map hΦ.aemeasurable hfm.aestronglyMeasurable]
    rfl
  rw [hcov]
  exact hcore

end Explicit

/-!
## 2. The separate-port layer means, uniform in `b`
-/

/-- **Separate clause of `lct_means`, uniform in `b`** (proof adapted from
`lct_means`): `β ∈ (0,1/4)`, `κ > 0` first; then `K ≥ 0`, `C_η ≥ 0`, `W₁`;
uniformly in `b ∈ [β, 1/2 - β]`, `W ≥ W₁`, Hermitian `X`, `E ∈ bulkInterval κ`: `-Im ḡ_i ≥ 0`,
`|ḡ_i| ≤ K`, and `(ḡ, ū)` solves the separate-port equations up to residuals `≤ C_η W⁻²`.
Changes: `ζ₀ = 2βα₀ ≤ (1-2b)α₀`; absorption from `habsU` at `(β, ζ₀, 3)`;
`C_η = 6 C_v/(β w₁/2) + ζ₀⁻¹ C_v`. -/
theorem bu_means_sep (habsU : LayersBUniform.GaussianAbsorptionUniformContract) {β κ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1 / 4) (hκ : 0 < κ) :
    ∃ (K Cη : ℝ) (W₁ : ℕ), 0 ≤ K ∧ 0 ≤ Cη ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ W : ℕ, 0 < W → W₁ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      X.IsHermitian → ∀ E ∈ bulkInterval κ,
        (∀ i, 0 ≤ -(meqMeanA (layerLaw W b .separate)
            (layerResolvent .separate E (boundaryZ b E) X) i).im) ∧
          (∀ i, ‖meqMeanA (layerLaw W b .separate)
            (layerResolvent .separate E (boundaryZ b E) X) i‖ ≤ K) ∧
          ∃ r r' : Fin 2 → ℂ, ‖r‖ ≤ Cη / (W : ℝ) ^ 2 ∧ ‖r'‖ ≤ Cη / (W : ℝ) ^ 2 ∧
            ∀ i, meqMeanA (layerLaw W b .separate)
                (layerResolvent .separate E (boundaryZ b E) X) i =
                blockTrace (twoPortTop b E X
                  (meqMeanA (layerLaw W b .separate)
                    (layerResolvent .separate E (boundaryZ b E) X))
                  (meqMeanP (layerLaw W b .separate)
                    (layerResolvent .separate E (boundaryZ b E) X)))⁻¹ i + r i ∧
              meqMeanP (layerLaw W b .separate) (layerResolvent .separate E (boundaryZ b E) X) i =
                (boundaryZ b E - (b : ℂ) * meqMeanA (layerLaw W b .separate)
                  (layerResolvent .separate E (boundaryZ b E) X) i)⁻¹ + r' i := by
  obtain ⟨α₀, hα₀, hα₀1, hbulk⟩ := cmp_bulk_setup hκ
  set ζ₀ := 2 * β * α₀ with hζ₀def
  have hζ₀ : 0 < ζ₀ := by positivity
  obtain ⟨ε₁, Ca, hε₁, hCa, habs'⟩ := habsU β hβ0 hβ1 ζ₀ 3 hζ₀
  set Cv := max (tcvConst 1 1 Ca) 0 with hCvdef
  have hCv : 0 ≤ Cv := le_max_right _ _
  set Wc := ⌈(4 : ℝ) / ε₁⌉₊ with hWcdef
  set K := Ca with hKdef
  set w₁ := ζ₀ / (3 + K) ^ 2 with hw₁
  have hw₁0 : 0 < w₁ := by positivity
  set Cη := 6 * Cv / (β * (w₁ / 2)) + ζ₀⁻¹ * Cv with hCηdef
  have hCη1 : 0 ≤ 6 * Cv / (β * (w₁ / 2)) := by positivity
  have hCη2 : 0 ≤ ζ₀⁻¹ * Cv := by positivity
  obtain ⟨Ws, hWs⟩ := lct_small (ζ₀⁻¹ * Cv) (ε := w₁ / 2) (by positivity)
  refine ⟨K, Cη, max (max ⌈2 / ε₁⌉₊ Wc) Ws, hCa.le, by positivity, ?_⟩
  intro b hb W hW hWW X hX E hE
  have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb.1
  have hb1 : b < 1 / 2 := by linarith [hb.2]
  have hcov := bu_cov_one_letter_of hb0 hb1 hζ₀ hε₁ hCa (habs' b hb)
  have hWe : ⌈2 / ε₁⌉₊ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWW)
  have hWc : Wc ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWW)
  have hWs' : Ws ≤ W := (le_max_right _ _).trans hWW
  have hW2 : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWe)
    rw [div_le_iff₀ hε₁] at h1
    linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have h1b : 0 < 1 - b := by linarith
  have hzs : ζ₀ ≤ (boundaryZ b E).im := by
    rw [boundaryZ_im hEabs.le, hζ₀def]
    have := mul_le_mul_of_nonneg_left haim h1b.le
    nlinarith
  have hzs3 := norm_boundaryZ_le hb0.le (by linarith) hEabs.le
  have hz0s : 0 ≤ (boundaryZ b E).im := hζ₀.le.trans hzs
  have hB : 0 ≤ Cv / (W : ℝ) ^ 2 := by positivity
  have hsmall : ζ₀⁻¹ * (Cv / (W : ℝ) ^ 2) ≤ ζ₀ / (3 + K) ^ 2 / 2 := by
    rw [← mul_div_assoc]; exact hWs W hW hWs'
  have hr1 : 6 * (Cv / (W : ℝ) ^ 2) / (b * (ζ₀ / (3 + K) ^ 2 / 2)) ≤ Cη / (W : ℝ) ^ 2 := by
    rw [show 6 * (Cv / (W : ℝ) ^ 2) / (b * (ζ₀ / (3 + K) ^ 2 / 2)) =
      (6 * Cv / (b * (w₁ / 2))) / (W : ℝ) ^ 2 by rw [hw₁]; ring]
    have hbβ : 6 * Cv / (b * (w₁ / 2)) ≤ 6 * Cv / (β * (w₁ / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hb.1 (by positivity))
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hr2 : ζ₀⁻¹ * (Cv / (W : ℝ) ^ 2) ≤ Cη / (W : ℝ) ^ 2 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨hinv, hmom⟩ := habs' b hb W hW .separate X hX E (boundaryZ b E) hzs hzs3
  have hG2 := meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) hW2)
  have hKm : ∀ i, ‖meqMeanA (layerLaw W b .separate)
      (layerResolvent .separate E (boundaryZ b E) X) i‖ ≤ K := fun i =>
    lct_norm_meanA_le hCa.le (hmom 1 le_rfl (by linarith)) i
  obtain ⟨r, r', hr, hr', heq⟩ := lct_sep_residual hW hb0 hb1 hX hζ₀ hzs hzs3 hCa.le hB hinv
    hG2 hKm (fun P Q hP hQ => hcov W hW hWc .separate X hX E _ hzs hzs3 P Q hP hQ) hsmall
  refine ⟨fun i => ?_, hKm, r, r', hr.trans hr1, hr'.trans hr2, heq⟩
  have := lct_im_meanA_nonpos (σ := .separate) (b := b) E hz0s hX i
  linarith

/-- **Separate clause of `LayerComparisonContract`, uniform in `b`** (proof adapted from
`layerComparison_holds`): `β ∈ (0,1/4)`, `κ > 0` first;
then `d_* > 0`, `C`, `W₀`; uniformly in `b ∈ [β, 1/2-β]`, `W ≥ W₀`, Hermitian `X`,
`E ∈ bulkInterval κ` with `d(X) ≤ d_*`: the comparison solution `(m, u)` exists and the
layer means are within `C W⁻²` of it. -/
theorem bu_layerComparison_sep (habsU : LayersBUniform.GaussianAbsorptionUniformContract)
    {β κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1 / 4) (hκ : 0 < κ) :
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
        ∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
          (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
          (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ∀ i : Fin 2,
            ‖(∫ ω, physBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
                ∂layerLaw W b .separate) - m i‖ ≤ C / (W : ℝ) ^ 2 ∧
            ‖(∫ ω, portBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
                ∂layerLaw W b .separate) - u i‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨K, Cη, W₁, hK, hCη, hmeans⟩ := bu_means_sep habsU hβ0 hβ1 hκ
  obtain ⟨d₁, C, η₀, C'', hd₁, -, hη₀, hbr⟩ := bu_sepComparison hβ0 hβ1 hκ hK
  obtain ⟨Ws, hWs⟩ := lct_small Cη hη₀
  refine ⟨d₁, max C (C'' * Cη), max W₁ Ws, hd₁, ?_⟩
  intro b hb W hW hWW X hX E hE hd
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hη : Cη / (W : ℝ) ^ 2 ≤ η₀ := hWs W hW ((le_max_right _ _).trans hWW)
  have hη0 : 0 ≤ Cη / (W : ℝ) ^ 2 := by positivity
  have hCd : C * matchedDistance b E X ≤ max C (C'' * Cη) * matchedDistance b E X :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
  have hCW : C'' * (Cη / (W : ℝ) ^ 2) ≤ max C (C'' * Cη) / (W : ℝ) ^ 2 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨hpos, hKm, r, r', hr, hr', happ⟩ :=
    hmeans b hb W hW ((le_max_left _ _).trans hWW) X hX E hE
  obtain ⟨m, u, hsol, him, hclose, hbs⟩ := hbr b hb W hW X hX E hE hd
  refine ⟨m, u, hsol, him, fun i => (hclose i).trans hCd, fun i => ?_⟩
  have h := (hbs _ _ _ r r' hη0 hη hr hr' hpos hKm happ i).trans hCW
  exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans h,
    (le_add_of_nonneg_left (norm_nonneg _)).trans h⟩

/-!
## 3. The weighted Ward identity, uniform in `b`
-/

/-- Uniform bulk data: `Im z_∂ ≥ α₀/2`, `|z_∂| ≤ 3`, `|E| ≤ 2` on `bulkInterval κ`, for every
`b ∈ (0, 1/2]` (adapted from `wl_bulk`). -/
theorem bu_bulk {κ α₀ : ℝ} (hbulk0 : ∀ E ∈ bulkInterval κ,
      |E| < 2 ∧ ‖matchedA E‖ = 1 ∧ (matchedA E).im ≤ -α₀) (hα₀ : 0 < α₀) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b ≤ 1 / 2) :
    ∀ E ∈ bulkInterval κ,
      α₀ / 2 ≤ (boundaryZ b E).im ∧ ‖boundaryZ b E‖ ≤ 3 ∧ |E| ≤ 2 := by
  intro E hE
  obtain ⟨hE2, -, ha⟩ := hbulk0 E hE
  refine ⟨?_, norm_boundaryZ_le hb0.le (by linarith) hE2.le, hE2.le⟩
  rw [boundaryZ_im hE2.le]
  nlinarith

/-- **Weight-majorant moments, uniform in `b`** (`wl_moment_setup` with `habsU`): `β`, `η₀ > 0`,
`q ≥ 1` first; then `C, W₀`; uniformly in `b ∈ [β, 1/2-β]`, `W ≥ W₀`, every shape, Hermitian `X`,
`Im z ≥ η₀`, `|z| ≤ 3`: a.s. invertibility and `‖F‖_{L^q} ≤ C`. -/
theorem bu_moment_unif (habsU : LayersBUniform.GaussianAbsorptionUniformContract) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1 / 4) {η₀ : ℝ} (hη₀ : 0 < η₀) {q : ℝ} (hq : 1 ≤ q) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ 3 →
        (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
        eLpNorm (wlF E z X) (ENNReal.ofReal q) (layerLaw W b σ) ≤ ENNReal.ofReal C := by
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := habsU β hβ0 hβ1 η₀ 3 hη₀
  refine ⟨1 + 6 * (wlLamConst * CA), max ⌈2 * q / ε₁⌉₊ ⌈2 * q⌉₊, by
    have := wlLamConst_pos; positivity, fun b hb => ?_⟩
  have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb.1
  have hb1 : b < 1 / 2 := by linarith [hb.2]
  exact bu_moment_setup_of hb0 hb1 hε₁ hCA (habs' b hb) hq

/-- **Weighted one-letter covariance, uniform in `b`** (`wl_cov_weighted` with `habsU`). -/
theorem bu_cov_weighted_unif (habsU : LayersBUniform.GaussianAbsorptionUniformContract) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1 / 4) {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ 3 → |E| ≤ 2 →
      ∀ P Q : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
        ‖meqCov (layerLaw W b σ) (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace)
            (fun ω => Q * layerResolvent σ E z X ω) *
          wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C4, W₀, hC4, hmom⟩ := bu_moment_unif habsU hβ0 hβ1 hη₀ (q := 4) (by norm_num)
  refine ⟨160 * C4 ^ 4, W₀, by positivity, fun b hb => ?_⟩
  have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb.1
  have hb1 : b < 1 / 2 := by linarith [hb.2]
  exact bu_cov_weighted_of hb0 hb1 hη₀ hC4 (hmom b hb)

/-- **`wl_ward_core` at a fixed `b` with explicit constants** (same proof as
`wl_ward_core`; only the choice of the constants is moved to the
hypotheses): from the bulk data with `η₀`, the separate comparison clause with `d₁, C_c, W_c`,
the weighted covariance with `C_w, W_w`, the `L²` moments with `C₂, W₂` and `W_s` with
`max(C_c,0) W⁻² ≤ η₀/4`: for `W ≥ max(max W_c W_w, max W₂ W_s)` and
`d(X) ≤ min(d₁, η₀/(4(max(C_c,0)+1)))`, `‖E LL* - 1‖ ≤ (12 C' + 12 C_w)/η₀ (d(X) + W⁻²)`. -/
theorem bu_ward_at {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {η₀ : ℝ}
    (hη₀ : 0 < η₀)
    (hbulk : ∀ E ∈ bulkInterval κ,
      η₀ ≤ (boundaryZ b E).im ∧ ‖boundaryZ b E‖ ≤ 3 ∧ |E| ≤ 2)
    {d₁ Cc : ℝ} {Wc : ℕ}
    (hcmp : ∀ (W : ℕ), 0 < W → Wc ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      X.IsHermitian → ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ d₁ →
        ∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
          (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
          (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ Cc * matchedDistance b E X) ∧
          ∀ i : Fin 2,
            ‖(∫ ω, physBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
                ∂layerLaw W b .separate) - m i‖ ≤ Cc / (W : ℝ) ^ 2 ∧
            ‖(∫ ω, portBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) i
                ∂layerLaw W b .separate) - u i‖ ≤ Cc / (W : ℝ) ^ 2)
    {Cw : ℝ} {Ww : ℕ} (hCw : 0 ≤ Cw)
    (hcov : ∀ W : ℕ, 0 < W → Ww ≤ W → ∀ (σ : LayerShape)
      (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian → ∀ (E : ℝ) (z : ℂ),
      η₀ ≤ z.im → ‖z‖ ≤ 3 → |E| ≤ 2 →
      ∀ P Q : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
        ‖meqCov (layerLaw W b σ) (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent σ E z X ω).trace)
            (fun ω => Q * layerResolvent σ E z X ω) *
          wlKh (m := PortSite W σ) (z • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)ᴴ‖ ≤
          Cw / (W : ℝ) ^ 2)
    {C2 : ℝ} {W2 : ℕ}
    (hmom : ∀ W : ℕ, 0 < W → W2 ≤ W → ∀ (σ : LayerShape)
      (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian → ∀ (E : ℝ) (z : ℂ),
      η₀ ≤ z.im → ‖z‖ ≤ 3 →
        (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
        eLpNorm (wlF E z X) (ENNReal.ofReal 2) (layerLaw W b σ) ≤ ENNReal.ofReal C2)
    {Ws : ℕ} (hWs : ∀ W : ℕ, 0 < W → Ws ≤ W → max Cc 0 / (W : ℝ) ^ 2 ≤ η₀ / 4) :
    ∀ (W : ℕ), 0 < W → max (max Wc Ww) (max W2 Ws) ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ min d₁ (η₀ / (4 * (max Cc 0 + 1))) →
      Integrable (wlLL b E X) (layerLaw W b .separate) ∧
      ‖∫ ω, wlLL b E X ω ∂layerLaw W b .separate - 1‖ ≤
        (12 * max Cc 0 + 12 * Cw) / η₀ * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) := by
  set C' := max Cc 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  intro W hW hWW X hX E hE hd
  have hWc : Wc ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWW)
  have hWw : Ww ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWW)
  have hW2 : W2 ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWW)
  have hWs' : Ws ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hWW)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hz, hzM, hE2⟩ := hbulk E hE
  have hEabs : |E| < 2 := abs_lt_two_of_mem_bulkInterval hκ hE
  set z := boundaryZ b E with hzdef
  have hη : 0 < z.im := lt_of_lt_of_le hη₀ hz
  set μ := layerLaw W b .separate with hμ
  set 𝒢 := fun ω => layerResolvent .separate E z X ω with h𝒢
  have hGm : Measurable 𝒢 := measurable_layerResolvent .separate E z X
  obtain ⟨hinv, hF⟩ := hmom W hW hW2 .separate X hX E z hz hzM
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  -- integrability of `𝒢`
  set F := wlF (σ := .separate) E z X with hFdef
  have hFm : Measurable F := wl_measurable_wlF _ _ _
  have hFmem : MemLp F 2 μ := by
    have h1 : MemLp F (ENNReal.ofReal 2) μ := memLp_iff.mpr (lt_of_le_of_lt hF ENNReal.ofReal_lt_top)
    simpa using h1
  have hGF : ∀ ω, ‖𝒢 ω‖ ≤ F ω := fun ω => by
    have hg0 := norm_nonneg (𝒢 ω)
    have hl0 := norm_nonneg (wlLam ω)
    change ‖𝒢 ω‖ ≤ 1 + 6 * ((1 + ‖wlLam ω‖) * ‖𝒢 ω‖)
    nlinarith
  have hG2 : Integrable (fun ω => ‖layerResolvent .separate E z X ω‖ ^ 2) μ := by
    refine Integrable.mono' hFmem.integrable_sq ((hGm.norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGF ω) 2
  have hG1 : Integrable (fun ω => ‖𝒢 ω‖) μ := by
    have hd : Integrable (fun ω => 1 + ‖layerResolvent .separate E z X ω‖ ^ 2) μ :=
      (integrable_const (1 : ℝ)).add hG2
    refine Integrable.mono' hd hGm.norm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖𝒢 ω‖ ≤ 1 + ‖𝒢 ω‖ ^ 2
    nlinarith [sq_nonneg (‖𝒢 ω‖ - 1), norm_nonneg (𝒢 ω)]
  have hGi : Integrable 𝒢 μ := Integrable.mono' hG1 hGm.aestronglyMeasurable
    (ae_of_all _ fun _ => le_rfl)
  -- the mean equation and the top block
  have hme := meanEquation_of_moments hW hb0.le hb1.le .separate hX E hη.le hinv hG2
  have hblk := (meq_blocks hme).1
  rw [meq_resid_toBlocks11, meqTop_separate] at hblk
  set gA := meqMeanA μ (layerResolvent .separate E z X) with hgA
  set gP := meqMeanP μ (layerResolvent .separate E z X) with hgP
  set R := meqResidTop μ (1 - 2 * (b : ℂ)) b (layerResolvent .separate E z X) with hR
  set s : Fin 2 → ℂ := fun i => (1 - 2 * (b : ℂ)) * gA i + b * gP i with hs
  set T := cmpTopH E X - diagonal (cmpExt (W := W) s) with hT
  have hTeq : (-((E : ℂ) • (1 : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)) - X -
      diagonal (fun x : PhysSite W .separate => (1 - 2 * (b : ℂ)) * gA x.1 + b * gP x.1)) = T :=
    rfl
  rw [hTeq] at hblk
  -- the comparison solution and the scalar deviations
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  obtain ⟨m, u, -, -, hclose, hmeans⟩ := hcmp W hW hWc X hX E hE (hd.trans (min_le_left _ _))
  set a := matchedA E with ha
  set ε : ℝ := C' * matchedDistance b E X + C' / (W : ℝ) ^ 2 with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hgA : ∀ i, ‖gA i - a‖ ≤ ε := fun i => by
    have h1 := (hmeans i).1
    have h2 := hclose i
    have h3 : ‖m i - a‖ ≤ Cc * matchedDistance b E X := (le_add_of_nonneg_right
      (norm_nonneg _)).trans h2
    calc ‖gA i - a‖ ≤ ‖gA i - m i‖ + ‖m i - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Cc / (W : ℝ) ^ 2 + Cc * matchedDistance b E X := add_le_add h1 h3
      _ ≤ ε := by
          rw [hεdef]
          have : Cc / (W : ℝ) ^ 2 ≤ C' / (W : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left Cc 0) hd0]
  have hgP : ∀ i, ‖gP i - a‖ ≤ ε := fun i => by
    have h1 := (hmeans i).2
    have h2 := hclose i
    have h3 : ‖u i - a‖ ≤ Cc * matchedDistance b E X := (le_add_of_nonneg_left
      (norm_nonneg _)).trans h2
    calc ‖gP i - a‖ ≤ ‖gP i - u i‖ + ‖u i - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Cc / (W : ℝ) ^ 2 + Cc * matchedDistance b E X := add_le_add h1 h3
      _ ≤ ε := by
          rw [hεdef]
          have : Cc / (W : ℝ) ^ 2 ≤ C' / (W : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left Cc 0) hd0]
  have hcb : (0 : ℝ) ≤ 1 - 2 * b := by linarith
  have hsh : ∀ i, ‖z + E + s i‖ ≤ ε := fun i => by
    have hz' := boundaryZ_eq (b := b) hE2
    have e : z + E + s i = ((1 - 2 * b : ℝ) : ℂ) * (gA i - a) + (b : ℂ) * (gP i - a) := by
      rw [hzdef, hz', hs]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hcb,
      Real.norm_of_nonneg hb0.le]
    nlinarith [hgA i, hgP i, norm_nonneg (gA i - a), norm_nonneg (gP i - a)]
  have him : ∀ i, |-(s i).im - z.im| ≤ ε := fun i => by
    have hzi := boundaryZ_im (b := b) hE2
    have hsim : (s i).im = (1 - 2 * b) * (gA i).im + b * (gP i).im := by
      rw [hs]
      simp [Complex.mul_im]
    have e : -(s i).im - z.im = -((1 - 2 * b) * (gA i - a).im) - b * (gP i - a).im := by
      rw [hsim, hzdef, hzi, Complex.sub_im, Complex.sub_im]
      ring
    rw [e]
    have h1 := Complex.abs_im_le_norm (gA i - a)
    have h2 := Complex.abs_im_le_norm (gP i - a)
    have h3 := hgA i
    have h4 := hgP i
    rw [abs_le]
    constructor <;> nlinarith [abs_le.mp (h1.trans h3), abs_le.mp (h2.trans h4)]
  have hεη : ε ≤ z.im / 2 := by
    have h1 : C' * matchedDistance b E X ≤ η₀ / 4 := by
      have hd' : matchedDistance b E X ≤ η₀ / (4 * (C' + 1)) := hd.trans (min_le_right _ _)
      calc C' * matchedDistance b E X ≤ (C' + 1) * (η₀ / (4 * (C' + 1))) :=
            mul_le_mul (by linarith) hd' hd0 (by positivity)
        _ = η₀ / 4 := by field_simp
    have h2 := hWs W hW hWs'
    rw [hεdef]
    linarith
  obtain ⟨hTu, hdet⟩ := wl_ward_det hX s hη hε0 hεη hsh him R
  -- the expectation of `𝒢₁₁`
  have hEbar : (matrixExpect μ (layerResolvent .separate E z X)).toBlocks₁₁ = T⁻¹ * (1 + R) := by
    rw [← hblk, ← Matrix.mul_assoc, nonsing_inv_mul _ hTu, Matrix.one_mul]
  have hME : matrixExpect μ (layerResolvent .separate E z X) = ∫ ω, 𝒢 ω ∂μ :=
    meq_matrixExpect_eq hGi
  -- the Ward identity, pointwise and in mean
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X with hK
  set c : ℂ := Complex.I / (2 * z.im) with hc
  have hae : ∀ᵐ ω ∂μ, wlLL b E X ω =
      c • (K * (𝒢 ω).toBlocks₁₁ * Kᴴ - K * ((𝒢 ω).toBlocks₁₁)ᴴ * Kᴴ) := by
    filter_upwards [hinv, lct_ae_blocks_isHermitian W b .separate] with ω hω hA
    exact wl_ward_pointwise E hη.ne' hX ω hA hω K
  obtain ⟨hint, hval⟩ := wl_integral_ward hGi K c
  refine ⟨hint.congr (hae.mono fun ω h => h.symm), ?_⟩
  rw [integral_congr_ae hae, hval, ← hME, hEbar]
  refine hdet.trans ?_
  -- the weighted residual
  have hRK : ‖R * Kᴴ‖ ≤ 6 * (Cw / (W : ℝ) ^ 2) := by
    set S := ∑ a, (1 - 2 * (b : ℂ)) • meqCov μ
          (fun ω => physBlockTrace (layerResolvent .separate E z X ω) a)
          (fun ω => meqPhysProj a * layerResolvent .separate E z X ω) +
        ∑ a, ∑ j, ((b : ℂ) * meqInc .separate a j) •
          meqCov μ (fun ω => portBlockTrace (layerResolvent .separate E z X ω) j)
            (fun ω => meqPhysProj a * layerResolvent .separate E z X ω) with hSdef
    have hRS : R * Kᴴ = (S * wlKh (m := PortSite W .separate) Kᴴ).toBlocks₁₁ := by
      rw [wl_mul_Kh_toBlocks11]; rfl
    rw [hRS]
    refine (wl_norm_toBlocks11_le _).trans ?_
    have h := wl_resid_weighted_le μ hb0.le hb1.le (layerResolvent .separate E z X)
      (wlKh (m := PortSite W .separate) Kᴴ) (B := Cw / (W : ℝ) ^ 2)
      (fun a => by
        rw [lct_cov_phys_eq]
        exact hcov W hW hWw .separate X hX E z hz hzM hE2 _ _ (meq_norm_physProj_le a)
          (meq_norm_physProj_le a))
      (fun a j => by
        rw [lct_cov_port_eq]
        exact hcov W hW hWw .separate X hX E z hz hzM hE2 _ _ (meq_norm_portProj_le j)
          (meq_norm_physProj_le a))
    refine h.trans (le_of_eq ?_)
    norm_num
  have hd' := hd0
  calc 12 * ε / z.im + 2 * ‖R * Kᴴ‖ / z.im
      ≤ 12 * ε / η₀ + 2 * (6 * (Cw / (W : ℝ) ^ 2)) / η₀ := by
        gcongr
    _ = (12 * C' * matchedDistance b E X + 12 * C' / (W : ℝ) ^ 2 + 12 * Cw / (W : ℝ) ^ 2) / η₀ := by
        rw [hεdef]; ring
    _ ≤ (12 * C' + 12 * Cw) / η₀ * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) := by
        rw [div_mul_eq_mul_div]
        refine div_le_div_of_nonneg_right ?_ hη₀.le
        have h1 : 0 ≤ 12 * Cw * matchedDistance b E X := by positivity
        have e : (12 * C' + 12 * Cw) * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) =
            12 * C' * matchedDistance b E X + 12 * C' / (W : ℝ) ^ 2 + 12 * Cw / (W : ℝ) ^ 2 +
              12 * Cw * matchedDistance b E X := by ring
        rw [e]; linarith

/-- **The weighted Ward identity, Bochner form, uniform in `b`** (`wl_ward_core`
with uniform constants): `β ∈ (0,1/4)`, `κ > 0` first; then
`d_* > 0`, `C ≥ 0`, `W₀`; uniformly in `b ∈ [β, 1/2 - β]`, `W ≥ W₀`, Hermitian `X`,
`E ∈ bulkInterval κ` with `d(X) ≤ d_*`: `LL*` is integrable and
`‖E LL* - 1‖ ≤ C (d(X) + W⁻²)`. Constants: `η₀ = α₀/2` (instead of `(1-b)α₀`); comparison from
`bu_layerComparison_sep`; moments (`q = 2, 4`) and the weighted covariance from `habsU` at
`(β, α₀/2, 3)`. -/
theorem bu_ward_core (habsU : LayersBUniform.GaussianAbsorptionUniformContract) :
    ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 ≤ C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
    ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ dstar →
      Integrable (wlLL b E X) (layerLaw W b .separate) ∧
      ‖∫ ω, wlLL b E X ω ∂layerLaw W b .separate - 1‖ ≤
        C * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) := by
  intro β hβ0 hβ1 κ hκ
  obtain ⟨α₀, hα₀, -, hbulk0⟩ := cmp_bulk_setup hκ
  have hη₀ : 0 < α₀ / 2 := by positivity
  obtain ⟨d₁, Cc, Wc, hd₁, hcmpU⟩ := bu_layerComparison_sep habsU hβ0 hβ1 hκ
  obtain ⟨Cw, Ww, hCw, hcovU⟩ := bu_cov_weighted_unif habsU hβ0 hβ1 hη₀
  obtain ⟨C2, W2, -, hmomU⟩ := bu_moment_unif habsU hβ0 hβ1 hη₀ (q := 2) (by norm_num)
  obtain ⟨Ws, hWs⟩ := lct_small (max Cc 0) (ε := α₀ / 2 / 4) (by positivity)
  have hC'0 : 0 ≤ max Cc 0 := le_max_right _ _
  refine ⟨min d₁ (α₀ / 2 / (4 * (max Cc 0 + 1))), (12 * max Cc 0 + 12 * Cw) / (α₀ / 2),
    max (max Wc Ww) (max W2 Ws), lt_min hd₁ (by positivity), by positivity, ?_⟩
  intro b hb
  have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb.1
  have hb1 : b < 1 / 2 := by linarith [hb.2]
  exact bu_ward_at hb0 hb1 hκ hη₀ (bu_bulk hbulk0 hα₀ hb0 hb1.le) (hcmpU b hb) hCw
    (hcovU b hb) (hmomU b hb) hWs

/-!
## 4. The clock-mean identity, uniform in `b`
-/

/-- **`ClockMeanUniformContract`** (the clock-mean identity, uniformly in `b`), from the uniform
absorption clause alone; the trace pairing is that of `wl_clockMean`. -/
theorem bu_clockMeanUniform_of (habsU : LayersBUniform.GaussianAbsorptionUniformContract) :
    LayersBUniform.ClockMeanUniformContract := by
  intro β hβ0 hβ1 κ hκ
  obtain ⟨dstar, C, W₀, hd, hC, h⟩ := bu_ward_core habsU β hβ0 hβ1 κ hκ
  refine ⟨dstar, C, W₀, hd, ?_⟩
  intro b hb W hW hWW X hX E hE hdd Y hY μ K Lm u
  obtain ⟨hint, hb⟩ := h b hb W hW hWW X hX E hE hdd
  have hpt : ∀ ω, (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re = wlPairing Y (wlLL b E X ω) := by
    intro ω
    rw [wlPairing_apply]
    congr 2
    change ((Lm ω)ᴴ * Y * Lm ω).trace = (Y * (Lm ω * (Lm ω)ᴴ)).trace
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hfun : (fun ω => (W : ℝ)⁻¹ * ((Lm ω)ᴴ * Y * Lm ω).trace.re) =
      fun ω => wlPairing Y (wlLL b E X ω) := funext hpt
  rw [hfun]
  refine ⟨(wlPairing Y).integrable_comp hint, ?_⟩
  rw [(wlPairing Y).integral_comp_comm hint, wlPairing_apply]
  set N := ∫ ω, wlLL b E X ω ∂layerLaw W b .separate with hN
  have hTY := wl_trace_re_nonneg hY
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hΔ := wl_norm_trace_weight_le hY (N - 1)
  have e : (Y * N).trace = Y.trace + (Y * (N - 1)).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]; ring
  have hre : (Y * N).trace.re ≤ (1 + ‖N - 1‖) * Y.trace.re := by
    rw [e, Complex.add_re]
    have := Complex.re_le_norm (Y * (N - 1)).trace
    nlinarith
  have hbd : (1 + ‖N - 1‖) ≤ 1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2 := by
    have := hb
    have e2 : C * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) =
        C * matchedDistance b E X + C / (W : ℝ) ^ 2 := by ring
    linarith
  calc (W : ℝ)⁻¹ * (Y * N).trace.re ≤ (W : ℝ)⁻¹ * ((1 + ‖N - 1‖) * Y.trace.re) :=
        mul_le_mul_of_nonneg_left hre (by positivity)
    _ ≤ (W : ℝ)⁻¹ * ((1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2) * Y.trace.re) := by
        gcongr
    _ = (1 + C * matchedDistance b E X + C / (W : ℝ) ^ 2) * u := by ring

end BlockBand.Layers
