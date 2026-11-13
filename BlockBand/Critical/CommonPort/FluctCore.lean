module

public import BlockBand.Critical.CommonPort.FluctBounds

/-!
# Common-port mean: the regularized Poincaré argument

Law: `layerLaw W b .common`, realized as the image of `gaussianProduct (tflVar W b .common)`
under `tflEmbed` (`tfl_layerLaw_eq_map`). Domain: `W ≥ 1`, `0 < b < 1/2`, Hermitian `X`,
`|e| ≤ 2` with `0 < η₀ ≤ Im z₀`, arbitrary `u, v`, `p ≥ 1`. Norms: `eLpNorm` at
`ENNReal.ofReal p`; vectors `vnorm` (Euclidean).

* `norm_cpq_le`: `|q(N, N)| ≤ ‖u‖ ‖v‖ ‖K N₁₂‖²`.
* `cp_fluct_core`: with the gradient constant `C_g` of a supplied Gaussian `L^p` gradient
  inequality, a.e. invertibility, and `‖Ψ⁹‖_p ≤ M₉`, `Ψ⁹` integrable:
  `‖F - EF‖_p ≤ C_g √p (C_∇ ‖u‖ ‖v‖ / √W) M₉`, `F = u*(LL*)v`,
  `C_∇ = 8 (η₀⁻¹ c₁)(c₁ (1 + η₀⁻¹))`, `c₁ = 1 + 2(7 + η₀⁻¹)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- `|q(N, N)| ≤ ‖u‖ ‖v‖ ‖K N₁₂‖²`. -/
theorem norm_cpq_le {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (K : Matrix n n ℂ) (u v : n → ℂ) (N : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    ‖cpq K u v N N‖ ≤ vnorm u * vnorm v * ‖K * N.toBlocks₁₂‖ ^ 2 := by
  unfold cpq
  refine (norm_star_dot_le _ _).trans ?_
  have h := vnorm_mulVec_le ((K * N.toBlocks₁₂) * (K * N.toBlocks₁₂)ᴴ) v
  have h2 : ‖(K * N.toBlocks₁₂) * (K * N.toBlocks₁₂)ᴴ‖ ≤ ‖K * N.toBlocks₁₂‖ ^ 2 := by
    refine (l2_opNorm_mul _ _).trans (le_of_eq ?_)
    rw [l2_opNorm_conjTranspose, sq]
  calc vnorm u * vnorm (((K * N.toBlocks₁₂) * (K * N.toBlocks₁₂)ᴴ) *ᵥ v)
      ≤ vnorm u * (‖K * N.toBlocks₁₂‖ ^ 2 * vnorm v) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right h2 (vnorm_nonneg _)))
          (vnorm_nonneg _)
    _ = vnorm u * vnorm v * ‖K * N.toBlocks₁₂‖ ^ 2 := by ring

/-- The unregularized observable `F(ω) = u*(L L*)v = q(𝒢, 𝒢)`. -/
theorem cpq_resolvent_eq {W : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u v : Fin 2 × Fin W → ℂ) (ω : LayerSample W .common) :
    cpq (matchedLeadK b e X) u v (commonPortResolvent b e X ω) (commonPortResolvent b e X ω) =
      star u ⬝ᵥ (commonPortLL b e X ω *ᵥ v) := rfl

/-- Constant of the gradient bound. -/
def cpGradConst (η₀ : ℝ) : ℝ :=
  8 * (η₀⁻¹ * (1 + 2 * (7 + η₀⁻¹))) * ((1 + 2 * (7 + η₀⁻¹)) * (1 + η₀⁻¹))

theorem cpGradConst_nonneg {η₀ : ℝ} (hη : 0 < η₀) : 0 ≤ cpGradConst η₀ := by
  unfold cpGradConst; positivity

/-- **Core fluctuation bound for `u*(LL*)v`.** Law `layerLaw W b .common`, realized via `tfl_layerLaw_eq_map` as the image of
`gaussianProduct (tflVar W b .common)`. Domain: `W ≥ 1`, `0 < b < 1/2`, Hermitian `X`, `|e| ≤ 2`,
`0 < η₀ ≤ Im z₀`, arbitrary `u, v`, `p ≥ 1`. Hypotheses: `hgr`, a Gaussian `L^p` gradient
inequality with constant `C_g` (supplied by `gaussianLpGradient_holds`); `hinv`, a.s.
invertibility of the layer matrix; `hΨ9`, `‖Ψ⁹‖_p ≤ M₉`; `hΨint`, integrability of `Ψ⁹`.
Conclusion: `‖F - EF‖_p ≤ C_g √p (C_∇ ‖u‖‖v‖/√W) M₉`, `F = u*(LL*)v`, `C_∇ = cpGradConst η₀`;
proof by regularization height `t = 1/(m+1) → 0` (dominated convergence and Fatou), at fixed
`W, X, e, u, v`. Norms: `eLpNorm` at `ENNReal.ofReal p`, Euclidean `vnorm`. -/
theorem cp_fluct_core {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {e : ℝ} (he : |e| ≤ 2)
    {η₀ : ℝ} (hη : 0 < η₀) (hzim : η₀ ≤ (commonZ b e).im) (u v : Fin 2 × Fin W → ℂ)
    {p : ℝ} (hp : 1 ≤ p) {Cg : ℝ}
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    (hinv : ∀ᵐ ω ∂layerLaw W b .common, IsUnit (layerMatrix .common e (commonZ b e) X ω).det)
    {M9 : ℝ≥0∞}
    (hΨ9 : eLpNorm (fun ω => cpPsi b e X ω ^ 9) (ENNReal.ofReal p) (layerLaw W b .common) ≤ M9)
    (hΨint : Integrable (fun ω => cpPsi b e X ω ^ 9) (layerLaw W b .common)) :
    eLpNorm (fun ω => star u ⬝ᵥ (commonPortLL b e X ω *ᵥ v) -
        ∫ ω', star u ⬝ᵥ (commonPortLL b e X ω' *ᵥ v) ∂layerLaw W b .common)
        (ENNReal.ofReal p) (layerLaw W b .common) ≤
      ENNReal.ofReal (Cg * Real.sqrt p) *
        (ENNReal.ofReal (cpGradConst η₀ * vnorm u * vnorm v / Real.sqrt W) * M9) := by
  set K := matchedLeadK b e X with hKdef
  set μ := gaussianProduct (tflVar W b .common) with hμ
  set Φ := tflEmbed W b .common with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b .common
  have hlaw : layerLaw W b .common = μ.map Φ := tfl_layerLaw_eq_map W b .common
  have hz0 : 0 ≤ (commonZ b e).im := hη.le.trans hzim
  set B := cpqCLM (m := Fin 1 × Fin W) K u v with hBdef
  have hBc : Continuous (fun N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ => B N N) :=
    B.continuous.clm_apply continuous_id
  have hGm : Measurable (fun ω : LayerSample W .common => commonPortResolvent b e X ω) :=
    measurable_layerResolvent .common e (commonZ b e) X
  let f : LayerSample W .common → ℂ := fun ω => star u ⬝ᵥ (commonPortLL b e X ω *ᵥ v)
  have hfB : f = fun ω => B (commonPortResolvent b e X ω) (commonPortResolvent b e X ω) := rfl
  have hf : Measurable f := by rw [hfB]; exact hBc.measurable.comp hGm
  let F : (TflCoord W .common → ℝ) → ℂ := fun x => f (Φ x)
  have hF : Measurable F := hf.comp hΦ
  let Ψc : (TflCoord W .common → ℝ) → ℝ := fun x => cpPsi b e X (Φ x) ^ 9
  have hΨm : Measurable (fun ω : LayerSample W .common => cpPsi b e X ω ^ 9) :=
    (measurable_cpPsi b e X).pow_const 9
  -- transfer
  have htransfer : eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b .common) (ENNReal.ofReal p)
      (layerLaw W b .common) = eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ := by
    rw [hlaw, integral_map hΦ.aemeasurable hf.aestronglyMeasurable,
      eLpNorm_map_measure (hf.sub_const _).aestronglyMeasurable hΦ.aemeasurable]
    rfl
  change eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b .common) (ENNReal.ofReal p)
      (layerLaw W b .common) ≤ _
  rw [htransfer]
  have hp0 : 0 ≤ p := by linarith
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hinvμ : ∀ᵐ x ∂μ, IsUnit (layerMatrix .common e (commonZ b e) X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hΨμ : eLpNorm Ψc (ENNReal.ofReal p) μ ≤ M9 := by
    rw [hlaw, eLpNorm_map_measure hΨm.aestronglyMeasurable hΦ.aemeasurable] at hΨ9
    exact hΨ9
  have hΨμint : Integrable Ψc μ := by
    rw [hlaw] at hΨint
    exact (integrable_map_measure hΨm.aestronglyMeasurable hΦ.aemeasurable).mp hΨint
  set η' := η₀⁻¹ with hη'
  set c1 : ℝ := 1 + 2 * (7 + η') with hc1
  have hc10 : 0 ≤ c1 := by positivity
  set cg : ℝ := cpGradConst η₀ * vnorm u * vnorm v / Real.sqrt W with hcg
  have hcg0 : 0 ≤ cg := by
    rw [hcg]; have := cpGradConst_nonneg hη; have := vnorm_nonneg u; have := vnorm_nonneg v
    positivity
  set Bd : ℝ≥0∞ := ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal cg * M9) with hBd
  -- pointwise bounds at the coordinates
  have hpt : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
      IsUnit (layerMatrix .common e (commonZ b e) X (Φ x)).det →
      ‖cpG W b e X t x‖ ≤ 2 * cpPsi b e X (Φ x) ∧
      ‖K * (cpG W b e X t x).toBlocks₁₂‖ ≤ η' * c1 * cpPsi b e X (Φ x) ^ 4 ∧
      ‖K * topRows (cpG W b e X t x)‖ ≤ c1 * (1 + η') * cpPsi b e X (Φ x) ^ 4 := by
    intro t ht ht1 x hx
    have hGeq : cpG W b e X t x = regResolvent e (commonZ b e) X t (Φ x) := by
      rw [cpG, tflPsi_inv_eq]; rfl
    rw [hGeq]
    exact reg_bounds hb0.le (by linarith) he hX hη hzim ht ht1 (Φ x)
      (tflEmbed_blockDiag_isHermitian W b .common x) hx
  -- the bound for each regularization `0 < t ≤ 1`
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
      eLpNorm (fun x => cpF W b e X u v t x - ∫ y, cpF W b e X u v t y ∂μ)
        (ENNReal.ofReal p) μ ≤ Bd := by
    intro t ht ht1
    have hC := cpF_contDiff W b e u v hX hz0 ht
    have hcont : Continuous (cpF W b e X u v t) := hC.continuous
    have hmem : MemLp (cpF W b e X u v t) (ENNReal.ofReal p) μ := by
      refine MemLp.of_bound hcont.aestronglyMeasurable
        (vnorm u * vnorm v * (‖K‖ * t⁻¹) ^ 2) (ae_of_all _ fun x => ?_)
      refine (norm_cpq_le K u v _).trans ?_
      have hGt : ‖cpG W b e X t x‖ ≤ t⁻¹ := tflPsi_inv_le W b .common e (commonZ b e) hX hz0 ht x
      have h1 : ‖K * (cpG W b e X t x).toBlocks₁₂‖ ≤ ‖K‖ * t⁻¹ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left
          ((norm_toBlocks12_le _).trans hGt) (norm_nonneg _))
      have := vnorm_nonneg u; have := vnorm_nonneg v
      gcongr
    have h1 := hgr p hp (TflCoord W .common) (tflVar W b .common) (cpF W b e X u v t) hC hmem
    refine h1.trans ?_
    have hwc : Continuous (weightedGradientNorm (tflVar W b .common) (cpF W b e X u v t)) := by
      have hd := hC.continuous_fderiv one_ne_zero
      unfold weightedGradientNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    have hwle : ∀ᵐ x ∂μ, ‖weightedGradientNorm (tflVar W b .common) (cpF W b e X u v t) x‖ ≤
        ‖cg * Ψc x‖ := by
      filter_upwards [hinvμ] with x hx
      have hg := cpF_gradient_le W b e u v hW hb0 hb1 hX hz0 ht x
      obtain ⟨h1, h2, h3⟩ := hpt t ht ht1 x hx
      have hg0 : 0 ≤ weightedGradientNorm (tflVar W b .common) (cpF W b e X u v t) x :=
        Real.sqrt_nonneg _
      have hΨ1 := one_le_cpPsi b e X (Φ x)
      rw [Real.norm_of_nonneg hg0, Real.norm_of_nonneg
        (mul_nonneg hcg0 (pow_nonneg (by linarith : (0 : ℝ) ≤ cpPsi b e X (Φ x)) 9))]
      refine hg.trans ?_
      set P := cpPsi b e X (Φ x)
      have hU := vnorm_nonneg u
      have hV := vnorm_nonneg v
      have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW'
      have hprod : ‖cpG W b e X t x‖ * ‖K * (cpG W b e X t x).toBlocks₁₂‖ *
          ‖K * topRows (cpG W b e X t x)‖ ≤
          (2 * P) * (η' * c1 * P ^ 4) * (c1 * (1 + η') * P ^ 4) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _)
          (by positivity)
      have hfin : 4 * (‖cpG W b e X t x‖ * ‖K * (cpG W b e X t x).toBlocks₁₂‖ *
          ‖K * topRows (cpG W b e X t x)‖ * vnorm u * vnorm v) / Real.sqrt W ≤
          4 * ((2 * P) * (η' * c1 * P ^ 4) * (c1 * (1 + η') * P ^ 4) * vnorm u * vnorm v) /
            Real.sqrt W := by
        gcongr
      refine hfin.trans (le_of_eq ?_)
      show _ = cg * cpPsi b e X (Φ x) ^ 9
      rw [hcg]
      simp only [cpGradConst, ← hη', ← hc1]
      field_simp
      ring
    have h4 := eLpNorm_mono_ae (p := ENNReal.ofReal p) hwc.aestronglyMeasurable hwle
    have h5 : eLpNorm (fun x => cg * Ψc x) (ENNReal.ofReal p) μ =
        ENNReal.ofReal cg * eLpNorm Ψc (ENNReal.ofReal p) μ := by
      rw [show (fun x => cg * Ψc x) = cg • Ψc from rfl, eLpNorm_const_smul,
        Real.enorm_eq_ofReal hcg0]
    rw [hBd]
    gcongr
    exact h4.trans (h5.le.trans (by gcongr))
  -- the limit `t = 1/(m+1) → 0`
  set tm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with htm
  have htpos : ∀ m, 0 < tm m := fun m => by rw [htm]; positivity
  have ht1 : ∀ m, tm m ≤ 1 := fun m => by
    rw [htm, div_le_one (by positivity)]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have htlim : Tendsto tm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Fm : ℕ → (TflCoord W .common → ℝ) → ℂ := fun m => cpF W b e X u v (tm m) with hFm
  have hFmc : ∀ m, Continuous (Fm m) := fun m =>
    (cpF_contDiff W b e u v hX hz0 (htpos m)).continuous
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x) atTop (𝓝 (F x)) := by
    filter_upwards [hinvμ] with x hx
    set N := layerMatrix .common e (commonZ b e) X (Φ x) with hN
    have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hx
    have hcN : Continuous (fun t : ℝ => N + ((t : ℂ) * Complex.I) •
        (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ)) := by fun_prop
    have h1 : Tendsto (fun m => tflPsi W b .common e (commonZ b e) X (tm m) x) atTop (𝓝 N) := by
      have := (hcN.tendsto 0).comp htlim
      simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      rw [tflPsi_eq, tflReg]
    have h2 : Tendsto (fun m => cpG W b e X (tm m) x) atTop (𝓝 (Ring.inverse N)) := by
      have hc := NormedRing.inverse_continuousAt hU.unit
      rw [IsUnit.unit_spec] at hc
      exact hc.tendsto.comp h1
    have h3 := (hBc.tendsto _).comp h2
    have hFx : F x = B (Ring.inverse N) (Ring.inverse N) := by
      rw [← Matrix.nonsing_inv_eq_ringInverse]
      rfl
    rw [hFx]
    exact h3
  have hbound : ∀ m, ∀ᵐ x ∂μ, ‖Fm m x‖ ≤ vnorm u * vnorm v * (η' * c1) ^ 2 * Ψc x := by
    intro m
    filter_upwards [hinvμ] with x hx
    obtain ⟨-, h2, -⟩ := hpt (tm m) (htpos m) (ht1 m) x hx
    refine (norm_cpq_le K u v _).trans ?_
    have hΨ1 := one_le_cpPsi b e X (Φ x)
    set P := cpPsi b e X (Φ x)
    have hU := vnorm_nonneg u
    have hV := vnorm_nonneg v
    have hsq : ‖K * (cpG W b e X (tm m) x).toBlocks₁₂‖ ^ 2 ≤ (η' * c1 * P ^ 4) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hP89 : P ^ 8 ≤ P ^ 9 := pow_le_pow_right₀ hΨ1 (by norm_num)
    calc vnorm u * vnorm v * ‖K * (cpG W b e X (tm m) x).toBlocks₁₂‖ ^ 2
        ≤ vnorm u * vnorm v * (η' * c1 * P ^ 4) ^ 2 := by gcongr
      _ = vnorm u * vnorm v * (η' * c1) ^ 2 * P ^ 8 := by ring
      _ ≤ vnorm u * vnorm v * (η' * c1) ^ 2 * P ^ 9 := by gcongr
  have hint : Tendsto (fun m => ∫ x, Fm m x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => vnorm u * vnorm v * (η' * c1) ^ 2 * Ψc x)
      (fun m => (hFmc m).aestronglyMeasurable) (hΨμint.const_mul _) hbound hconv
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x - ∫ y, Fm m y ∂μ) atTop
      (𝓝 (F x - ∫ y, F y ∂μ)) := hconv.mono fun x hx => hx.sub hint
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun m => ((hFmc m).sub continuous_const).aestronglyMeasurable)
    (fun x => F x - ∫ y, F y ∂μ) (hF.sub_const _).aestronglyMeasurable hconv2
  refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
  exact hstep (tm m) (htpos m) (ht1 m)

end BlockBand.Critical.CommonPort
