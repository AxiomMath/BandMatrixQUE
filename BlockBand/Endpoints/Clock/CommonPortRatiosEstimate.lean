module

public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Endpoints.Clock.CommonPortRatiosLaplace
public import BlockBand.Layers.LayerMeasurability
public import BlockBand.Layers.BondMoments

/-!
# The common-port Laplace estimate

Law: the common-port probe law `commonPortProbeLaw W b = layerLaw W b .common ⊗ CN(0, I_W)`
(fresh layer `ω`, probe `g`), conditional on a deterministic Hermitian old self-energy `X`;
the reference `h ~ CN(0, I_{2W})`.

Main statement `commonPort_laplace_estimate`: `b ∈ (0,1/2)` and `bulkInterval κ` first; then
`δ₀ > 0`, `C ≥ 0`, `W₀`; for `W ≥ W₀`, Hermitian `X`, `e ∈ bulkInterval κ` with
`δ = matchedDistance b e X ≤ δ₀`, and **every** positive semidefinite `F` on the two old ports:
`|E_{ω,g} exp(-(Lg)*F(Lg)) - E_h exp(-γ h*Fh)| ≤ C (δ + W⁻² + W^{-1/2}) Re Tr F`.
With `F = (aD + bC)/(γT)` this is the two-clock Laplace comparison; with `F = aY` it is the
common-port Laplace comparison, here with an explicit rate instead of `o(1)`.

Proof (a Gaussian duality argument instead of a log-determinant expansion): factor `F = BᴴB`; the Gaussian duality (`integral_exp_neg_quadForm_mulVec_eq`, Laplace identity
plus Sylvester) turns `E_g exp(-(Lg)*F(Lg))` into `E_h exp(-w*(LL*)w)`, `w = Bᴴh`, and
`E_h exp(-γ h*Fh)` into `E_h exp(-γ‖w‖²)`; then `|e^{-x} - e^{-y}| ≤ |x-y|` on `[0,∞)` and
the mean and `L²`-fluctuation clauses at `u = v = w` give
`E_ω|w*(LL*)w - γ‖w‖²| ≤ (C₁(δ+W⁻²) + C₂W^{-1/2})‖w‖²`, and `E_h‖w‖² = Tr BBᴴ = Tr F`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexOrder Matrix Matrix.Norms.L2Operator

/-!
## 1. Measurability and probability
-/

theorem commonPortRatios_isProbabilityMeasure_layerLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (layerLaw W b .common) :=
  BlockBand.Layers.bond_isProbabilityMeasure_layerLaw W b .common

theorem commonPortRatios_isProbabilityMeasure_probeLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (commonPortProbeLaw W b) := by
  have := commonPortRatios_isProbabilityMeasure_layerLaw W b
  unfold commonPortProbeLaw; infer_instance

/-- `ω ↦ L(ω)` is measurable. -/
theorem CommonPortRatios.measurable_commonPortL (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (fun ω : LayerSample W .common => commonPortL b e X ω) := by
  have hG : Measurable (fun ω : LayerSample W .common => commonPortResolvent b e X ω) :=
    BlockBand.Layers.measurable_layerResolvent (W := W) .common e (commonZ b e) X
  have hblk : Measurable (fun ω : LayerSample W .common =>
      (commonPortResolvent b e X ω).toBlocks₁₂) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact (measurable_pi_apply (Sum.inr j)).comp ((measurable_pi_apply (Sum.inl i)).comp hG)
  unfold commonPortL
  exact (Continuous.matrix_mul continuous_const continuous_id).measurable.comp hblk

/-- `ω ↦ L(ω)L(ω)*` is measurable. -/
theorem CommonPortRatios.measurable_commonPortLL (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (fun ω : LayerSample W .common => commonPortLL b e X ω) := by
  unfold commonPortLL
  exact (Continuous.matrix_mul continuous_id continuous_id.matrix_conjTranspose).measurable.comp
    (CommonPortRatios.measurable_commonPortL b e X)

/-- The probe `x ↦ L(x.1) x.2` is measurable. -/
theorem CommonPortRatios.measurable_commonPortProbe (b e : ℝ) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (fun x : LayerSample W .common × (Fin 1 × Fin W → ℂ) =>
      commonPortProbe b e X x) := by
  unfold commonPortProbe
  have hc : Continuous (fun p : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ × (Fin 1 × Fin W → ℂ) =>
      p.1 *ᵥ p.2) := Continuous.matrix_mulVec continuous_fst continuous_snd
  exact hc.measurable.comp (((CommonPortRatios.measurable_commonPortL b e X).comp measurable_fst).prodMk
    measurable_snd)

/-- `γ = (1-b)/(1-2b) > 0` for `b < 1/2`. -/
theorem CommonPortRatios.commonPortGamma_pos {b : ℝ} (hb1 : b < 1 / 2) : 0 < commonPortGamma b := by
  unfold commonPortGamma
  exact div_pos (by linarith) (by linarith)

/-!
## 2. Scalar and vector facts
-/

/-- `|e^{-x} - e^{-y}| ≤ |x - y|` for `x, y ≥ 0`. -/
theorem CommonPortRatios.abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have key : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → Real.exp (-s) - Real.exp (-t) ≤ t - s := by
    intro s t hs hst
    have h1 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : 1 - Real.exp (-(t - s)) ≤ t - s := by linarith [Real.add_one_le_exp (-(t - s))]
    have h3 : 0 ≤ 1 - Real.exp (-(t - s)) := by
      have : Real.exp (-(t - s)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have h4 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [h1]
    nlinarith [Real.exp_pos (-s)]
  rcases le_total x y with h | h
  · have hmono : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith [key hx h]
  · have hmono : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith [key hy h]

/-- `Re (c v)*F(c v) = c² Re v*Fv` for real `c`. -/
theorem CommonPortRatios.quadForm_real_smul {ι : Type*} [Fintype ι] (F : Matrix ι ι ℂ) (c : ℝ) (v : ι → ℂ) :
    quadForm F ((c : ℂ) • v) = c ^ 2 * quadForm F v := by
  unfold quadForm
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, Complex.star_def,
    Complex.conj_ofReal, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  ring

/-- `Re v*(P - Q)v = Re v*Pv - Re v*Qv`. -/
theorem CommonPortRatios.quadForm_sub' {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm (P - Q) v = quadForm P v - quadForm Q v := by
  unfold quadForm; rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- Expectation of a random quadratic form with integrable entries:
`E Re w*U w = Re w*(E U)w`. -/
theorem CommonPortRatios.integral_quadForm_matrixExpect {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (U : Ω → Matrix ι ι ℂ) (hU : ∀ x y, Integrable (fun ω => U ω x y) μ)
    (w : ι → ℂ) :
    Integrable (fun ω => quadForm (U ω) w) μ ∧
      ∫ ω, quadForm (U ω) w ∂μ = quadForm (matrixExpect μ U) w := by
  have hform : ∀ M : Matrix ι ι ℂ, star w ⬝ᵥ (M *ᵥ w) = ∑ i, ∑ j, (star (w i) * w j) * M i j := by
    intro M
    simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : Integrable (fun ω => star w ⬝ᵥ (U ω *ᵥ w)) μ := by
    simp_rw [hform]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hU i j).const_mul _
  refine ⟨hint.re, ?_⟩
  unfold quadForm
  have := integral_re hint
  simp only [RCLike.re_to_complex] at this
  rw [this]
  congr 1
  simp_rw [hform]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hU i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hU i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

/-- `E|f| ≤ ‖f‖_{L²}` (probability measure), in the form used for the fluctuation clause. -/
theorem CommonPortRatios.integral_norm_le_of_eLpNorm_two_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {c : ℝ}
    (hc : eLpNorm f (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal c) :
    Integrable f μ ∧ ∫ ω, ‖f ω‖ ∂μ ≤ max c 0 := by
  have h2 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
  rw [h2] at hc
  have h12 : eLpNorm f 1 μ ≤ eLpNorm f 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hfin : eLpNorm f 1 μ < ∞ := lt_of_le_of_lt (h12.trans hc) ENNReal.ofReal_lt_top
  have hI : Integrable f μ := by
    rw [← memLp_one_iff_integrable]; exact hfin
  refine ⟨hI, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hf, ← eLpNorm_one_eq_lintegral_enorm hf]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h12.trans hc)
  rw [ENNReal.toReal_ofReal'] at this
  exact this

/-!
## 3. The Laplace estimate
-/

section Abstract

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- **Abstract Laplace estimate.** For a measurable random rectangular `L : Ω → ι × κ` under a
probability law `μ`, with `U = LLᴴ`, `‖E U - γI‖ ≤ c₁` (`E` the entrywise `matrixExpect`) and
`‖w*(U - EU)w‖_{L²(μ)} ≤ c₂‖w‖²` for all `w`, and every `F ⪰ 0`:
`|E_{ω,g} exp(-Re (Lg)*F(Lg)) - E_h exp(-γ Re h*Fh)| ≤ (max c₁ 0 + max c₂ 0) Re Tr F`,
`g ~ CN(0,I_κ)` independent of `ω`, `h ~ CN(0,I_ι)`. -/
theorem abs_laplace_sub_le_of_moments (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : Ω → Matrix ι κ ℂ) (hLm : Measurable L) {γ : ℝ} (hγ : 0 < γ) (c₁ c₂ : ℝ)
    (hmean : ‖matrixExpect μ (fun ω => L ω * (L ω)ᴴ) - ((γ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)‖ ≤ c₁)
    (hfl : ∀ w : ι → ℂ, eLpNorm (fun ω => star w ⬝ᵥ
        ((L ω * (L ω)ᴴ - matrixExpect μ (fun ω => L ω * (L ω)ᴴ)) *ᵥ w))
        (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal (c₂ * l2Norm w * l2Norm w))
    {F : Matrix ι ι ℂ} (hF : F.PosSemidef) :
    |(∫ x, Real.exp (-quadForm F (L x.1 *ᵥ x.2)) ∂μ.prod (circularVectorLaw κ)) -
        ∫ h, Real.exp (-(γ * quadForm F h)) ∂circularVectorLaw ι| ≤
      (max c₁ 0 + max c₂ 0) * F.trace.re := by
  set U : Ω → Matrix ι ι ℂ := fun ω => L ω * (L ω)ᴴ with hUdef
  set EU := matrixExpect μ U
  set c := max c₁ 0 + max c₂ 0
  have hc0 : 0 ≤ c := by positivity
  -- factor `F = BᴴB`
  obtain ⟨B, hFB⟩ : ∃ B : Matrix ι ι ℂ, F = Bᴴ * B := by
    open scoped MatrixOrder in
    obtain ⟨S, hS, -, hSS⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
      hF.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hF.nonneg)
    exact ⟨S, by rw [show Sᴴ = S from hS, hSS]⟩
  have hUpsd : ∀ ω, (U ω).PosSemidef := fun ω => by
    have := posSemidef_conjTranspose_mul_self (L ω)ᴴ
    rwa [conjTranspose_conjTranspose] at this
  have hUm : Measurable U :=
    (Continuous.matrix_mul continuous_id continuous_id.matrix_conjTranspose).measurable.comp hLm
  -- the integrand on `Ω × ℂ^ι`
  have hpair : Measurable (fun p : Ω × (ι → ℂ) => (U p.1, Bᴴ *ᵥ p.2)) :=
    (hUm.comp measurable_fst).prodMk
      ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp measurable_snd)
  have hΦm : Measurable (fun p : Ω × (ι → ℂ) => Real.exp (-quadForm (U p.1) (Bᴴ *ᵥ p.2))) :=
    Real.continuous_exp.measurable.comp ((continuous_quadForm.measurable.comp hpair).neg)
  have hΦb : ∀ p : Ω × (ι → ℂ), |Real.exp (-quadForm (U p.1) (Bᴴ *ᵥ p.2))| ≤ 1 := fun p => by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact CommonPortRatios.quadForm_nonneg_of_posSemidef (hUpsd _) _
  have hΦi : Integrable (fun p : Ω × (ι → ℂ) => Real.exp (-quadForm (U p.1) (Bᴴ *ᵥ p.2)))
      (μ.prod (circularVectorLaw ι)) :=
    Integrable.of_bound hΦm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hΦb p)
  -- Step 1: the probe side
  have hL : (∫ x, Real.exp (-quadForm F (L x.1 *ᵥ x.2)) ∂μ.prod (circularVectorLaw κ)) =
      ∫ h, ∫ ω, Real.exp (-quadForm (U ω) (Bᴴ *ᵥ h)) ∂μ ∂circularVectorLaw ι := by
    have hpm : Measurable (fun x : Ω × (κ → ℂ) => L x.1 *ᵥ x.2) :=
      (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
        ((hLm.comp measurable_fst).prodMk measurable_snd)
    have hm : Measurable (fun x : Ω × (κ → ℂ) => Real.exp (-quadForm F (L x.1 *ᵥ x.2))) :=
      Real.continuous_exp.measurable.comp (Measurable.neg
        ((continuous_quadForm.comp (continuous_const.prodMk continuous_id)).measurable.comp hpm))
    have hb : ∀ x : Ω × (κ → ℂ), ‖Real.exp (-quadForm F (L x.1 *ᵥ x.2))‖ ≤ 1 := fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact CommonPortRatios.quadForm_nonneg_of_posSemidef hF _
    rw [integral_prod _ (Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hb))]
    have hin : ∀ ω, ∫ g, Real.exp (-quadForm F (L ω *ᵥ g)) ∂circularVectorLaw κ =
        ∫ h, Real.exp (-quadForm (U ω) (Bᴴ *ᵥ h)) ∂circularVectorLaw ι := by
      intro ω
      rw [hFB]
      exact integral_exp_neg_quadForm_mulVec_eq B (L ω)
    simp_rw [hin]
    exact integral_integral_swap (f := fun ω h => Real.exp (-quadForm (U ω) (Bᴴ *ᵥ h))) hΦi
  -- Step 2: the reference side
  have hR : ∫ h, Real.exp (-(γ * quadForm F h)) ∂circularVectorLaw ι =
      ∫ h, Real.exp (-(γ * l2Norm (Bᴴ *ᵥ h) ^ 2)) ∂circularVectorLaw ι := by
    have hsq : ((Real.sqrt γ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) *
        (((Real.sqrt γ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ))ᴴ = ((γ : ℝ) : ℂ) • 1 := by
      rw [conjTranspose_smul, conjTranspose_one, smul_mul_smul, Matrix.one_mul, Complex.star_def,
        Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hγ.le]
    have h1 := integral_exp_neg_quadForm_mulVec_eq B (((Real.sqrt γ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ))
    rw [hsq] at h1
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, CommonPortRatios.quadForm_real_smul,
      Real.sq_sqrt hγ.le, ← hFB] at h1
    have h2 : ∀ w : ι → ℂ, quadForm (((γ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) w = γ * l2Norm w ^ 2 := by
      intro w; rw [CommonPortRatios.quadForm_smul_real, CommonPortRatios.quadForm_one]
    simp only [h2] at h1
    exact h1
  -- Step 3: pointwise comparison in `h`
  have hpt : ∀ h : ι → ℂ, |(∫ ω, Real.exp (-quadForm (U ω) (Bᴴ *ᵥ h)) ∂μ) -
      Real.exp (-(γ * l2Norm (Bᴴ *ᵥ h) ^ 2))| ≤ c * l2Norm (Bᴴ *ᵥ h) ^ 2 := by
    intro h
    set w := Bᴴ *ᵥ h
    have hy0 : 0 ≤ γ * l2Norm w ^ 2 := by positivity
    set f : Ω → ℂ := fun ω => star w ⬝ᵥ ((U ω - EU) *ᵥ w)
    have hfm : AEStronglyMeasurable f μ := by
      have hcf : Continuous (fun M : Matrix ι ι ℂ => star w ⬝ᵥ ((M - EU) *ᵥ w)) := by
        simp only [dotProduct, mulVec]
        fun_prop
      exact (hcf.measurable.comp hUm).aestronglyMeasurable
    obtain ⟨hfi, hfle⟩ := CommonPortRatios.integral_norm_le_of_eLpNorm_two_le hfm (hfl w)
    have hxEx : ∀ ω, quadForm (U ω) w - quadForm EU w = (f ω).re := by
      intro ω; simp only [f]; rw [← CommonPortRatios.quadForm_sub']; rfl
    have hmeanw : |quadForm EU w - γ * l2Norm w ^ 2| ≤ max c₁ 0 * l2Norm w ^ 2 := by
      have e1 : quadForm EU w - γ * l2Norm w ^ 2 =
          quadForm (EU - ((γ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) w := by
        rw [CommonPortRatios.quadForm_sub', CommonPortRatios.quadForm_smul_real, CommonPortRatios.quadForm_one]
      rw [e1]
      exact (CommonPortRatios.abs_quadForm_le _ w).trans (mul_le_mul_of_nonneg_right
        (hmean.trans (le_max_left _ _)) (sq_nonneg _))
    have hfl' : ∫ ω, ‖f ω‖ ∂μ ≤ max c₂ 0 * l2Norm w ^ 2 := by
      refine hfle.trans (max_le ?_ (by positivity))
      have := BlockBand.Coarea.ProjectiveHaar.l2Norm_nonneg w
      nlinarith [le_max_left c₂ 0]
    have hbound : ∀ ω, ‖Real.exp (-quadForm (U ω) w) - Real.exp (-(γ * l2Norm w ^ 2))‖ ≤
        ‖f ω‖ + |quadForm EU w - γ * l2Norm w ^ 2| := by
      intro ω
      rw [Real.norm_eq_abs]
      refine (CommonPortRatios.abs_exp_neg_sub_exp_neg_le (CommonPortRatios.quadForm_nonneg_of_posSemidef (hUpsd ω) w) hy0).trans ?_
      calc |quadForm (U ω) w - γ * l2Norm w ^ 2|
          = |(quadForm (U ω) w - quadForm EU w) + (quadForm EU w - γ * l2Norm w ^ 2)| := by
            ring_nf
        _ ≤ |quadForm (U ω) w - quadForm EU w| + |quadForm EU w - γ * l2Norm w ^ 2| :=
            abs_add_le _ _
        _ ≤ _ := by rw [hxEx]; gcongr; exact Complex.abs_re_le_norm _
    have hΦint : Integrable (fun ω => Real.exp (-quadForm (U ω) w)) μ :=
      Integrable.of_bound (Real.continuous_exp.measurable.comp
          ((continuous_quadForm.measurable.comp (hUm.prodMk measurable_const)).neg)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
          exact CommonPortRatios.quadForm_nonneg_of_posSemidef (hUpsd _) _)
    have e2 : (∫ ω, Real.exp (-quadForm (U ω) w) ∂μ) - Real.exp (-(γ * l2Norm w ^ 2)) =
        ∫ ω, (Real.exp (-quadForm (U ω) w) - Real.exp (-(γ * l2Norm w ^ 2))) ∂μ := by
      rw [integral_sub hΦint (integrable_const _), integral_const, probReal_univ, one_smul]
    have hg : Integrable (fun ω => ‖f ω‖ + |quadForm EU w - γ * l2Norm w ^ 2|) μ :=
      hfi.norm.add (integrable_const _)
    rw [e2, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)).trans ?_
    rw [integral_add hfi.norm (integrable_const _), integral_const, probReal_univ, one_smul]
    calc (∫ ω, ‖f ω‖ ∂μ) + |quadForm EU w - γ * l2Norm w ^ 2|
        ≤ max c₂ 0 * l2Norm w ^ 2 + max c₁ 0 * l2Norm w ^ 2 := add_le_add hfl' hmeanw
      _ = c * l2Norm w ^ 2 := by simp only [c]; ring
  -- Step 4: integrate over `h`
  have hw2 : ∀ h : ι → ℂ, l2Norm (Bᴴ *ᵥ h) ^ 2 = quadForm (B * Bᴴ) h := by
    intro h
    rw [← CommonPortRatios.quadForm_one, ← CommonPortRatios.quadForm_conj, conjTranspose_conjTranspose, Matrix.mul_one]
  have hTr : ∫ h, quadForm (B * Bᴴ) h ∂circularVectorLaw ι = F.trace.re := by
    rw [integral_quadForm_circular, hFB, Matrix.trace_mul_comm]
  have hint1 : Integrable (fun h => ∫ ω, Real.exp (-quadForm (U ω) (Bᴴ *ᵥ h)) ∂μ)
      (circularVectorLaw ι) :=
    hΦi.integral_prod_right (f := fun p : Ω × (ι → ℂ) => Real.exp (-quadForm (U p.1) (Bᴴ *ᵥ p.2)))
  have hint2 : Integrable (fun h => Real.exp (-(γ * l2Norm (Bᴴ *ᵥ h) ^ 2)))
      (circularVectorLaw ι) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) 1
      (Filter.Eventually.of_forall fun h => ?_)
    · have := BlockBand.Coarea.ProjectiveHaar.continuous_l2Norm ι
      fun_prop
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      positivity
  rw [hL, hR, ← integral_sub hint1 hint2, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrable_quadForm_circular (B * Bᴴ)).const_mul c)
    (Filter.Eventually.of_forall fun h => ?_)).trans ?_
  · rw [Real.norm_eq_abs, ← hw2]; exact hpt h
  · rw [integral_const_mul, hTr]

end Abstract

/-- **Common-port Laplace estimate**, from `CommonPortMeanContract` only. Fixed
first `b ∈ (0,1/2)`, `κ > 0`; then `δ₀ > 0`, `C ≥ 0`, `W₀`; for every `W ≥ W₀` (`W > 0`),
Hermitian `X`, `e ∈ bulkInterval κ` with `δ = matchedDistance b e X ≤ δ₀` and every `F ⪰ 0`:
`|E_{ω,g} exp(-Re (Lg)*F(Lg)) - E_h exp(-γ Re h*Fh)| ≤ C(δ + W⁻² + W^{-1/2}) Re Tr F`. -/
theorem commonPort_laplace_estimate (hc : CommonPortMeanContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (δ₀ C : ℝ) (W₀ : ℕ), 0 < δ₀ ∧ 0 ≤ C ∧
      ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
      ∀ F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, F.PosSemidef →
        |(∫ x, Real.exp (-quadForm F (commonPortProbe b e X x)) ∂commonPortProbeLaw W b) -
            ∫ h, Real.exp (-(commonPortGamma b * quadForm F h))
              ∂circularVectorLaw (Fin 2 × Fin W)| ≤
          C * (matchedDistance b e X + 1 / (W : ℝ) ^ 2 + (W : ℝ) ^ (-(1 : ℝ) / 2)) *
            F.trace.re := by
  obtain ⟨δ₀, C₁, W₁, hδ₀, hmean⟩ := hc.mean b hb0 hb1 κ hκ
  obtain ⟨C₂, W₂, hfl⟩ := hc.fluctuation b hb0 hb1 κ hκ 2 le_rfl
  refine ⟨δ₀, max C₁ 0 + max C₂ 0, max W₁ W₂, hδ₀, by positivity, ?_⟩
  intro W hW hWW X hX e he hδ F hF
  have := commonPortRatios_isProbabilityMeasure_layerLaw W b
  obtain ⟨-, hEU⟩ := hmean W hW (le_of_max_le_left hWW) X hX e he hδ
  have hδ0 : 0 ≤ matchedDistance b e X := le_max_of_le_left (norm_nonneg _)
  have key := abs_laplace_sub_le_of_moments (layerLaw W b .common) (commonPortL b e X)
    (CommonPortRatios.measurable_commonPortL b e X) (CommonPortRatios.commonPortGamma_pos hb1)
    (C₁ * (matchedDistance b e X + 1 / (W : ℝ) ^ 2)) (C₂ * (W : ℝ) ^ (-(1 : ℝ) / 2))
    hEU (fun w => hfl W hW (le_of_max_le_right hWW) X hX e he w w) hF
  refine key.trans (mul_le_mul_of_nonneg_right ?_ ((Complex.nonneg_iff.mp hF.trace_nonneg).1))
  have hW0 : (0 : ℝ) ≤ (W : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
  have hW1 : (0 : ℝ) ≤ 1 / (W : ℝ) ^ 2 := by positivity
  have hA : max (C₁ * (matchedDistance b e X + 1 / (W : ℝ) ^ 2)) 0 ≤
      max C₁ 0 * (matchedDistance b e X + 1 / (W : ℝ) ^ 2) :=
    max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  have hB : max (C₂ * (W : ℝ) ^ (-(1 : ℝ) / 2)) 0 ≤ max C₂ 0 * (W : ℝ) ^ (-(1 : ℝ) / 2) :=
    max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0) (by positivity)
  have h1 : 0 ≤ max C₁ 0 := le_max_right _ _
  have h2 : 0 ≤ max C₂ 0 := le_max_right _ _
  nlinarith

end BlockBand.Endpoints.Clock
