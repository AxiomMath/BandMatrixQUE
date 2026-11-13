module

public import BlockBand.Critical.Collar.Density.BondEvent
public import BlockBand.Critical.WeightedDensity.Relative
public import BlockBand.Critical.CommonPort.Moments

/-!
# The regular conditional bound `E_{A,B}[K_X T Σ_F(0) T* K_X*] ⪯ C I` (`PLAN.md` §2.3 steps 2–4)

*Law.* `layerLaw W b .common` (the end diagonals `A_j ~ GUE_W(c/W)` and the bonds `Gin(b/W)` of the
collar), `0 < b < 1/2`, `c = 1 - 2b`; deterministic Hermitian `X` (no norm bound); energies
`e ∈ bulkInterval κ`, `0 < κ < 2`.

**Main result** `lintegral_condCollarDensity_le`: there are `d_R > 0`, `C_R ≥ 0`, `W₀` such that for
`W ≥ W₀`, `e ∈ bulkInterval κ`, Hermitian `X` with `d(X) ≤ d_R` and every `q`,
`E_{A,B} q*K_X T Σ_F(0) T* K_X* q ≤ C_R ‖q‖²` (`condCollarDensity`, lintegral form).

Proof. Regular event `𝒢`: `A` Hermitian, `‖D⁻¹‖ ≤ W³`
(`layerLaw_collarTopBlock_inv_bad_le`), `Σ|B_xy|² ≤ W²` (`layerLaw_frobenius_bad_le`) and
`|W⁻¹Tr 𝒢_port - a| ≤ ε_cert` (`layerLaw_trace_bad_le`); `P(𝒢ᶜ) ≤ C_bad/W`. On `𝒢` with `D`
invertible, `F` is in the fresh class (`freshRegular_of_chi`, `norm_certificateChi_collarFW`,
`normBound_collarFW`, exponent `A = 6`), so `globalWeightedDensity_regular` (consumes
`FreshPalmContract`, `PointDensityContract`) and `quadForm_condCollarDensity_le` give
`≤ 2C_r ‖L*q‖²`. Always, `globalWeightedDensity_general` gives `≤ 2C_g√W ‖L*q‖² ≤
C_g‖q‖²(W + ‖L‖⁴)`. Then `CommonPortMeanContract.mean` (`E‖L*q‖² ≤ (γ + C(δ₀+1))‖q‖²`),
`CommonPortMeanContract.moments` (`E‖L‖⁴ ≤ C₄⁴`) and `W · P(𝒢ᶜ) ≤ C_bad`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## Operator-norm helpers
-/

theorem sumsq_mulVec_le_opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n ℂ) (x : n → ℂ) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  have h0 : 0 ≤ ∑ i, ‖x i‖ ^ 2 := by positivity
  have h1 : 0 ≤ ∑ i, ‖(A *ᵥ x) i‖ ^ 2 := by positivity
  simp at h
  have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt h1, mul_pow, Real.sq_sqrt h0] at this
  exact this

theorem quadForm_le_opNorm {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ)
    (q : m → ℂ) : quadForm M q ≤ ‖M‖ * ∑ i, ‖q i‖ ^ 2 := by
  have hre : quadForm M q ≤ ∑ i, ‖q i‖ * ‖(M *ᵥ q) i‖ := by
    unfold quadForm
    refine (Complex.re_le_norm _).trans ?_
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖q i‖) (fun i => ‖(M *ᵥ q) i‖)
  have hM := sumsq_mulVec_le_opNorm M q
  have h0 : 0 ≤ ∑ i, ‖q i‖ ^ 2 := by positivity
  have hs0 : 0 ≤ ∑ i, ‖q i‖ * ‖(M *ᵥ q) i‖ := by positivity
  have hsq : (∑ i, ‖q i‖ * ‖(M *ᵥ q) i‖) ^ 2 ≤ (‖M‖ * ∑ i, ‖q i‖ ^ 2) ^ 2 := by
    calc _ ≤ (∑ i, ‖q i‖ ^ 2) * ∑ i, ‖(M *ᵥ q) i‖ ^ 2 := hcs
      _ ≤ (∑ i, ‖q i‖ ^ 2) * (‖M‖ ^ 2 * ∑ i, ‖q i‖ ^ 2) := mul_le_mul_of_nonneg_left hM h0
      _ = (‖M‖ * ∑ i, ‖q i‖ ^ 2) ^ 2 := by ring
  have := (pow_le_pow_iff_left₀ hs0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  linarith

theorem sumsq_conjTranspose_mulVec_eq_quadForm {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (L : Matrix m n ℂ) (q : m → ℂ) :
    ∑ a, ‖(Lᴴ *ᵥ q) a‖ ^ 2 = quadForm (L * Lᴴ) q := by
  have h := quadForm_conjTranspose_mul_mul (Lᴴ) (1 : Matrix n n ℂ) q
  rw [conjTranspose_conjTranspose, Matrix.mul_one, quadForm_one] at h
  exact h.symm

theorem integrable_quadForm {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] {μ : Measure Ω}
    {U : Ω → Matrix m m ℂ} (hU : ∀ x y, Integrable (fun ω => U ω x y) μ) (q : m → ℂ) :
    Integrable (fun ω => quadForm (U ω) q) μ := by
  unfold quadForm
  have h : Integrable (fun ω => star q ⬝ᵥ (U ω *ᵥ q)) μ := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    exact integrable_finsetSum _ fun x _ => (integrable_finsetSum _ fun y _ =>
      (hU x y).mul_const (q y)).const_mul _
  exact h.re

theorem integral_quadForm {Ω m : Type*} [MeasurableSpace Ω] [Fintype m] {μ : Measure Ω}
    {U : Ω → Matrix m m ℂ} (hU : ∀ x y, Integrable (fun ω => U ω x y) μ) (q : m → ℂ) :
    ∫ ω, quadForm (U ω) q ∂μ = quadForm (matrixExpect μ U) q := by
  unfold quadForm
  have h : Integrable (fun ω => star q ⬝ᵥ (U ω *ᵥ q)) μ := by
    simp only [dotProduct, mulVec, Pi.star_apply]
    exact integrable_finsetSum _ fun x _ => (integrable_finsetSum _ fun y _ =>
      (hU x y).mul_const (q y)).const_mul _
  have hre : ∫ ω, (star q ⬝ᵥ (U ω *ᵥ q)).re ∂μ = (∫ ω, star q ⬝ᵥ (U ω *ᵥ q) ∂μ).re :=
    integral_re h
  rw [hre]
  congr 1
  simp only [dotProduct, mulVec, Pi.star_apply, matrixExpect, Matrix.of_apply]
  rw [integral_finsetSum _ fun x _ => (integrable_finsetSum _ fun y _ =>
      (hU x y).mul_const (q y)).const_mul _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun y _ => (hU x y).mul_const (q y)]
  congr 1
  exact Finset.sum_congr rfl fun y _ => integral_mul_const _ _

/-!
## Pointwise facts
-/

theorem condCollarDensity_eq_zero_of_not_isUnit {b e : ℝ}
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : LayerSample W .common}
    (hD : ¬ IsUnit (collarTopBlock e X ω).det) : condCollarDensity b e X ω = 0 := by
  have hT : collarTW e X ω = 0 := by
    have : (collarTopBlock e X ω)⁻¹ = 0 := nonsing_inv_apply_not_isUnit _ hD
    ext i j
    simp [collarTW, collarT, this]
  simp [condCollarDensity, hT]

theorem two_sqrt_mul_le (W x : ℝ) (hW : 0 ≤ W) : 2 * Real.sqrt W * x ≤ W + x ^ 2 := by
  have h := sq_nonneg (Real.sqrt W - x)
  have hs := Real.sq_sqrt hW
  nlinarith

theorem continuous_sumsq_conjTranspose_mulVec {m n : Type} [Fintype m] [Fintype n]
    (q : m → ℂ) : Continuous fun L : Matrix m n ℂ => ∑ a, ‖(Lᴴ *ᵥ q) a‖ ^ 2 := by
  have h : Continuous fun L : Matrix m n ℂ => Lᴴ *ᵥ q :=
    (continuous_id.matrix_conjTranspose).matrix_mulVec continuous_const
  exact continuous_finsetSum _ fun a _ => (continuous_norm.comp ((continuous_apply a).comp h)).pow 2

theorem lintegral_ofReal_pow_four_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 4) ∂μ ≤ ENNReal.ofReal (C ^ 4) := by
  rw [eLpNorm_eq_eLpNorm' (by simp) ENNReal.ofReal_ne_top hfm.aestronglyMeasurable,
    eLpNorm'_eq_lintegral_enorm] at h
  have h4 : (ENNReal.ofReal 4).toReal = 4 := by simp
  rw [h4] at h
  have hpt : ∀ ω, ‖f ω‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (f ω ^ 4) := fun ω => by
    rw [Real.enorm_of_nonneg (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) (by norm_num)]
    norm_cast
  simp_rw [hpt] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 4)
  rw [← ENNReal.rpow_mul, show (1 / 4 : ℝ) * 4 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)] at h'
  refine h'.trans (le_of_eq ?_)
  norm_cast

/-!
## The regular conditional bound
-/

set_option maxHeartbeats 1000000 in
/-- **Regular conditional bound**: `E_{A,B} q*K_X T Σ_F(0) T* K_X* q ≤ C_R‖q‖²`
for `W ≥ W₀`, `e ∈ bulkInterval κ`, Hermitian `X` with `d(X) ≤ d_R`. -/
theorem lintegral_condCollarDensity_le (hP : FreshPalmContract) (hPD : PointDensityContract)
    (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) :
    ∃ (dR CR : ℝ) (W₀ : ℕ), 0 < dR ∧ 0 ≤ CR ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ e ∈ bulkInterval κ, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        matchedDistance b e X ≤ dR → ∀ q : Fin 2 × Fin W → ℂ,
          ∫⁻ ω, ENNReal.ofReal (quadForm (matchedLeadK b e X * condCollarDensity b e X ω *
            (matchedLeadK b e X)ᴴ) q) ∂layerLaw W b .common ≤
            ENNReal.ofReal (CR * ∑ a, ‖q a‖ ^ 2) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hc1 : 1 - 2 * b < 1 := by linarith
  have hm4 : 0 < 4 - (2 - κ) ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ (by linarith)
  have hV : 0 < Real.sqrt (4 - (2 - κ) ^ 2) / 2 := by
    have := Real.sqrt_pos.2 hm4; positivity
  obtain ⟨εc, r, s₀, v₀, hεc, hK, hreg⟩ := freshRegular_of_chi hc hc1 hV
  obtain ⟨Cr, hCr0, hCr⟩ := globalWeightedDensity_regular hP hPD 6 (1 - 2 * b) r s₀ v₀ hK 1
  obtain ⟨Cg, hCg0, hCg⟩ := globalWeightedDensity_general hc 1
  obtain ⟨δ₀, Cm, Wm, hδ₀, hmean⟩ := hCM.mean b hb0 hb κ hκ
  obtain ⟨C4, W4, hmom⟩ := hCM.moments b hb0 hb κ hκ 4 (by norm_num)
  obtain ⟨dT, CT, WT, hdT, hCT, htr⟩ := layerLaw_trace_bad_le hTM source hb0 hb hκ hκ2 hεc
  obtain ⟨Cw, hCw, hweg⟩ := layerLaw_collarTopBlock_inv_bad_le source
  set γ : ℝ := commonPortGamma b
  set Cm' : ℝ := max Cm 0
  set C4' : ℝ := max C4 0
  have hCm' : 0 ≤ Cm' := le_max_right _ _
  have hC4' : 0 ≤ C4' := le_max_right _ _
  set Cbad : ℝ := 4 * Cw / Real.sqrt (1 - 2 * b) + 2 * b + CT
  have hCbad : 0 ≤ Cbad := by
    have := Real.sqrt_nonneg (1 - 2 * b)
    have : 0 ≤ 4 * Cw / Real.sqrt (1 - 2 * b) := by positivity
    linarith
  set CR : ℝ := 2 * Cr * (|γ| + Cm' * (δ₀ + 1)) + Cg * (Cbad + C4' ^ 4)
  have hCR : 0 ≤ CR := by positivity
  refine ⟨min δ₀ dT, CR, max (max Wm W4) (max WT 2), lt_min hδ₀ hdT, hCR, ?_⟩
  intro W hW hW₀ e he X hX hd q
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW2 : (2 : ℝ) ≤ W := by
    have : 2 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW₀)
    exact_mod_cast this
  have hWm : Wm ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hW4 : W4 ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hWT : WT ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW₀)
  have he2 : |e| < 2 := BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he
  have hdδ : matchedDistance b e X ≤ δ₀ := hd.trans (min_le_left _ _)
  have hdT' : matchedDistance b e X ≤ dT := hd.trans (min_le_right _ _)
  set μ := layerLaw W b .common
  set K := matchedLeadK b e X
  set Q : LayerSample W .common → ℝ := fun ω => ∑ a, ‖((commonPortL b e X ω)ᴴ *ᵥ q) a‖ ^ 2
    with hQ
  set nq : ℝ := ∑ a, ‖q a‖ ^ 2
  have hnq : 0 ≤ nq := by positivity
  -- the shift `w = c a`
  have hw_eq := collarShiftW_eq (b := b) he2.le
  have hwim : (collarShiftW b e).im < 0 := by
    rw [hw_eq]
    have := BlockBand.Layers.matchedA_im_neg he2
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hc this
  have hw1 : ‖collarShiftW b e‖ ≤ 1 := by
    rw [hw_eq, norm_mul, BlockBand.Layers.norm_matchedA he2.le, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    linarith
  -- the bad event
  set t : ℝ := ((W : ℝ) ^ 3)⁻¹
  have ht : 0 < t := by positivity
  set β : ℝ := (W : ℝ) ^ 2
  have hβ : 0 < β := by positivity
  set B1 : Set (LayerSample W .common) := {ω | ¬ ∀ j, (ω.1 j).IsHermitian}
  set B2 : Set (LayerSample W .common) := {ω | ¬ ∀ v, ∑ a,
    ‖((collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤ (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2}
  set B3 : Set (LayerSample W .common) :=
    {ω | β < ∑ x, ∑ y, ‖bondMatrix .common ω.2 x y‖ ^ 2}
  set B4 : Set (LayerSample W .common) :=
    {ω | εc < ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖}
  set Bad := B1 ∪ B2 ∪ B3 ∪ B4
  have hB1 : μ B1 = 0 := by
    have := BlockBand.Layers.lct_ae_blocks_isHermitian W b .common
    rwa [ae_iff] at this
  have hB2 : μ B2 ≤ ENNReal.ofReal (4 * Cw / Real.sqrt (1 - 2 * b) / W) := by
    refine (hweg W hW b hb e X hX t ht).trans (ENNReal.ofReal_le_ofReal ?_)
    have hs : 0 < Real.sqrt (1 - 2 * b) := Real.sqrt_pos.2 hc
    have h1 : Cw / Real.sqrt (1 - 2 * b) * (2 * W) * (t - -t) =
        4 * Cw / Real.sqrt (1 - 2 * b) / W / W := by
      simp only [t]; field_simp; ring
    rw [h1]
    have : 0 ≤ 4 * Cw / Real.sqrt (1 - 2 * b) / W := by positivity
    exact div_le_self this (by linarith)
  have hB3 : μ B3 ≤ ENNReal.ofReal (2 * b / W) := by
    refine (layerLaw_frobenius_bad_le W b hβ).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [β]; field_simp
  have hB4 : μ B4 ≤ ENNReal.ofReal (CT / W) := by
    refine (htr W hW hWT X hX e he hdT').trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_left hCT hWr (by nlinarith)
  have hBad : μ Bad ≤ ENNReal.ofReal (Cbad / W) := by
    have h1 := measure_union_le (μ := μ) (B1 ∪ B2 ∪ B3) B4
    have h2 := measure_union_le (μ := μ) (B1 ∪ B2) B3
    have h3 := measure_union_le (μ := μ) B1 B2
    rw [hB1, zero_add] at h3
    refine h1.trans ((add_le_add (h2.trans (add_le_add (h3.trans hB2) hB3)) hB4).trans
      (le_of_eq ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [Cbad]
    field_simp
  set T := toMeasurable μ Bad
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hBT : Bad ⊆ T := subset_toMeasurable _ _
  have hμT : μ T ≤ ENNReal.ofReal (Cbad / W) := by rw [measure_toMeasurable]; exact hBad
  -- measurability
  have hLm := BlockBand.Critical.CommonPort.measurable_commonPortL b e X
  have hQm : Measurable Q := (continuous_sumsq_conjTranspose_mulVec q).measurable.comp hLm
  have hnLm : Measurable fun ω => ‖commonPortL b e X ω‖ := continuous_norm.measurable.comp hLm
  have hL4m : Measurable fun ω => ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) :=
    ENNReal.measurable_ofReal.comp (hnLm.pow_const 4)
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (quadForm (K * condCollarDensity b e X ω * Kᴴ) q) ≤
      ENNReal.ofReal (2 * Cr * Q ω) + T.indicator (fun _ => ENNReal.ofReal (Cg * nq * W)) ω +
        ENNReal.ofReal (Cg * nq) * ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) := by
    filter_upwards [BlockBand.Layers.lct_ae_blocks_isHermitian W b .common] with ω hA
    have hF := collarFW_isHermitian e hX hA
    have hQ0 : 0 ≤ Q ω := by positivity
    by_cases hωT : ω ∈ T
    · have hS := (hCg W hW (collarFW e X ω) hF).2 (sigma (collarFW e X ω) (1 - 2 * b))
        (continuous_sigma _ _) (isMatrixSpectralDensity_sigma hW hF hc) 0
      simp only [Complex.ofReal_zero, Complex.ofReal_one] at hS
      have h := quadForm_condCollarDensity_le hX hA hwim hw1 (by positivity) hS q
      have hQL : Q ω ≤ ‖commonPortL b e X ω‖ ^ 2 * nq := by
        have := sumsq_mulVec_le_opNorm (commonPortL b e X ω)ᴴ q
        rwa [l2_opNorm_conjTranspose] at this
      have hamgm := two_sqrt_mul_le W (‖commonPortL b e X ω‖ ^ 2) hWr.le
      have hval : quadForm (K * condCollarDensity b e X ω * Kᴴ) q ≤
          Cg * nq * W + Cg * nq * ‖commonPortL b e X ω‖ ^ 4 := by
        have hsW := Real.sqrt_nonneg (W : ℝ)
        calc quadForm (K * condCollarDensity b e X ω * Kᴴ) q
            ≤ 2 * (Cg * Real.sqrt W) * Q ω := h
          _ ≤ 2 * (Cg * Real.sqrt W) * (‖commonPortL b e X ω‖ ^ 2 * nq) :=
              mul_le_mul_of_nonneg_left hQL (by positivity)
          _ = Cg * nq * (2 * Real.sqrt W * ‖commonPortL b e X ω‖ ^ 2) := by ring
          _ ≤ Cg * nq * (W + (‖commonPortL b e X ω‖ ^ 2) ^ 2) :=
              mul_le_mul_of_nonneg_left hamgm (by positivity)
          _ = Cg * nq * W + Cg * nq * ‖commonPortL b e X ω‖ ^ 4 := by ring
      rw [Set.indicator_of_mem hωT]
      calc ENNReal.ofReal (quadForm (K * condCollarDensity b e X ω * Kᴴ) q)
          ≤ ENNReal.ofReal (Cg * nq * W + Cg * nq * ‖commonPortL b e X ω‖ ^ 4) :=
            ENNReal.ofReal_le_ofReal hval
        _ = ENNReal.ofReal (Cg * nq * W) +
              ENNReal.ofReal (Cg * nq) * ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ _ := by
            rw [add_assoc]
            exact le_add_self
    · have hωB : ω ∉ Bad := fun h => hωT (hBT h)
      simp only [Bad, Set.mem_union, not_or] at hωB
      obtain ⟨⟨⟨-, hω2⟩, hω3⟩, hω4⟩ := hωB
      simp only [B2, B3, B4, Set.mem_ofPred_eq, not_not, not_lt] at hω2 hω3 hω4
      by_cases hD : IsUnit (collarTopBlock e X ω).det
      · have hA6 : |e| + β / t ≤ (W : ℝ) ^ (6 : ℝ) := by
          have h6 : (W : ℝ) ^ (6 : ℝ) = (W : ℝ) ^ (6 : ℕ) := by norm_cast
          have hβt : β / t = (W : ℝ) ^ 5 := by simp only [β, t]; field_simp
          rw [h6, hβt]
          have h5 : (2 : ℝ) ^ 5 ≤ (W : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hW2 5
          have : (W : ℝ) ^ 6 = W * W ^ 5 := by ring
          nlinarith [abs_nonneg e]
        have hnb := normBound_collarFW ht hβ.le hω2 hω3 hA6
        have hχ : ‖BlockBand.Palm.certificateChi (collarFW e X ω) (1 - 2 * b) 0 (star (matchedA e))‖ ≤ εc := by
          rw [norm_certificateChi_collarFW he2 hX hA hb hD]; exact hω4
        have hVμ : Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (star (matchedA e)).im := by
          have := BlockBand.Layers.matchedA_im_le_of_mem_bulkInterval he
          rw [Complex.star_def, Complex.conj_im]
          linarith
        have hμ1 : ‖star (matchedA e)‖ ≤ 1 := by
          rw [norm_star, BlockBand.Layers.norm_matchedA he2.le]
        have hFR := hreg W hW (collarFW e X ω) hF (star (matchedA e)) hVμ hμ1 hχ
        have hS := hCr W hW (collarFW e X ω) 0 ⟨hF, hnb, hFR⟩ (sigma (collarFW e X ω) (1 - 2 * b))
          (continuous_sigma _ _) (isMatrixSpectralDensity_sigma hW hF hc)
        simp only [Complex.ofReal_zero, Complex.ofReal_one] at hS
        have h := quadForm_condCollarDensity_le hX hA hwim hw1 hCr0 hS q
        calc ENNReal.ofReal (quadForm (K * condCollarDensity b e X ω * Kᴴ) q)
            ≤ ENNReal.ofReal (2 * Cr * Q ω) := ENNReal.ofReal_le_ofReal h
          _ ≤ _ := by rw [add_assoc]; exact le_self_add
      · rw [condCollarDensity_eq_zero_of_not_isUnit hD]
        simp [quadForm]
  -- integration
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_add_right _ (hL4m.const_mul _),
    lintegral_add_right _ (measurable_const.indicator hTm), lintegral_indicator_const hTm,
    lintegral_const_mul _ hL4m]
  -- the mean term
  obtain ⟨hint, hnorm⟩ := hmean W hW hWm X hX e he hdδ
  have hQeq : ∀ ω, Q ω = quadForm (commonPortLL b e X ω) q := fun ω =>
    sumsq_conjTranspose_mulVec_eq_quadForm _ q
  have hQi : Integrable Q μ := (integrable_quadForm hint q).congr
    (Eventually.of_forall fun ω => (hQeq ω).symm)
  have hQint : ∫ ω, Q ω ∂μ = quadForm (matrixExpect μ (commonPortLL b e X)) q := by
    rw [integral_congr_ae (Eventually.of_forall hQeq), integral_quadForm hint q]
  have hQle : ∫ ω, Q ω ∂μ ≤ (|γ| + Cm' * (δ₀ + 1)) * nq := by
    rw [hQint]
    set M := matrixExpect μ (commonPortLL b e X)
    have hsplit : quadForm M q =
        quadForm (M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) q +
          γ * nq := by
      rw [quadForm_sub, quadForm_real_smul, quadForm_one]; ring
    have h1 := quadForm_le_opNorm
      (M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) q
    have h2 : ‖M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤
        Cm' * (δ₀ + 1) := by
      refine hnorm.trans ?_
      have hd0 : 0 ≤ matchedDistance b e X := le_max_of_le_left (norm_nonneg _)
      have hW1 : 1 / (W : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      calc Cm * (matchedDistance b e X + 1 / (W : ℝ) ^ 2) ≤
          Cm' * (matchedDistance b e X + 1 / (W : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ Cm' * (δ₀ + 1) := mul_le_mul_of_nonneg_left (by linarith) hCm'
    have h3 : γ * nq ≤ |γ| * nq := mul_le_mul_of_nonneg_right (le_abs_self _) hnq
    have h4 := mul_le_mul_of_nonneg_right h2 hnq
    rw [hsplit]
    calc _ ≤ ‖M - ((γ : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ * nq + |γ| * nq :=
          add_le_add h1 h3
      _ ≤ Cm' * (δ₀ + 1) * nq + |γ| * nq := by linarith
      _ = (|γ| + Cm' * (δ₀ + 1)) * nq := by ring
  have hmeanL : ∫⁻ ω, ENNReal.ofReal (2 * Cr * Q ω) ∂μ ≤
      ENNReal.ofReal (2 * Cr * ((|γ| + Cm' * (δ₀ + 1)) * nq)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hQi.const_mul _)
      (Eventually.of_forall fun ω => by have : 0 ≤ Q ω := by positivity
                                        positivity), integral_const_mul]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hQle (by positivity))
  -- the exceptional terms
  have hT' : ENNReal.ofReal (Cg * nq * W) * μ T ≤ ENNReal.ofReal (Cg * nq * Cbad) := by
    have h1 : ENNReal.ofReal (Cg * nq * W) * μ T ≤
        ENNReal.ofReal (Cg * nq * W) * ENNReal.ofReal (Cbad / W) := by gcongr
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hmom4 := lintegral_ofReal_pow_four_le hnLm (fun ω => norm_nonneg _) hC4'
    (((hmom W hW hW4 X hX e he).1).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hL4 : ENNReal.ofReal (Cg * nq) * ∫⁻ ω, ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) ∂μ ≤
      ENNReal.ofReal (Cg * nq * C4' ^ 4) := by
    have h1 : ENNReal.ofReal (Cg * nq) * ∫⁻ ω, ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) ∂μ ≤
        ENNReal.ofReal (Cg * nq) * ENNReal.ofReal (C4' ^ 4) := by gcongr
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hA0 : 0 ≤ 2 * Cr * ((|γ| + Cm' * (δ₀ + 1)) * nq) :=
    mul_nonneg (mul_nonneg zero_le_two hCr0)
      (mul_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg hCm' (by linarith))) hnq)
  have hB0 : 0 ≤ Cg * nq * Cbad := mul_nonneg (mul_nonneg hCg0 hnq) hCbad
  have hC0 : 0 ≤ Cg * nq * C4' ^ 4 := mul_nonneg (mul_nonneg hCg0 hnq) (pow_nonneg hC4' 4)
  have hfin : ENNReal.ofReal (2 * Cr * ((|γ| + Cm' * (δ₀ + 1)) * nq)) +
      ENNReal.ofReal (Cg * nq * Cbad) + ENNReal.ofReal (Cg * nq * C4' ^ 4) =
        ENNReal.ofReal (CR * nq) := by
    rw [← ENNReal.ofReal_add hA0 hB0, ← ENNReal.ofReal_add (add_nonneg hA0 hB0) hC0]
    congr 1
    simp only [CR]
    ring
  exact (add_le_add (add_le_add hmeanL hT') hL4).trans (le_of_eq hfin)

end BlockBand.Critical.Collar.Density
