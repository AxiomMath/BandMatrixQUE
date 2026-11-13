module

public import BlockBand.Critical.CommonPort.Algebra
public import BlockBand.Critical.CommonPort.GueMoments
public import BlockBand.Layers.LayerMeasurability
public import BlockBand.Layers.MatchedScalar

/-!
# Common-port mean: the `moments` clause

Law: the fresh common-port layer `layerLaw W b .common` (`A_a ~ GUE_W(c/W)`, `c = 1-2b`,
bonds `Gin(b/W)`), conditional on the old deformation: every deterministic Hermitian `X`.
Domain: `0 < b < 1/2`, `κ > 0`, `e ∈ bulkInterval κ`. Norms: operator norms of `L = K𝒢₁₂`
and `H = 𝒢₂₂`; `L^p` norms are `eLpNorm` over `layerLaw` at `ENNReal.ofReal p`.
Quantifiers: `b, κ`, then `p ≥ 1`, then `C, W₀`, then `W ≥ W₀`, `X`, `e`.

* `eLpNorm_mul_le_two`: Hölder `‖fg‖_r ≤ ‖f‖_{2r} ‖g‖_{2r}`.
* `commonPortMean_moments`: the `moments` field of `CommonPortMeanContract`, from
  `GaussianAbsorptionContract` alone (with the bond moments `bond_eLpNorm_le` and GUE
  block moments `gueBlock_eLpNorm_le`). The proof bounds, almost surely,
  `‖L‖ ≤ C₀ (1+‖A₀‖)(1+‖A₁‖)(1+‖Bm‖)³(1+‖𝒢‖)` (`norm_commonPortL_le`) and uses Hölder;
  `W₀ = ⌈8p + 1 + 4p/ε₁⌉`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- **Hölder** `‖f g‖_r ≤ ‖f‖_{2r} ‖g‖_{2r}` (real functions, `r > 0`). -/
theorem eLpNorm_mul_le_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal r) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * r)) μ * eLpNorm g (ENNReal.ofReal (2 * r)) μ := by
  have hH : ENNReal.HolderTriple (ENNReal.ofReal (2 * r)) (ENNReal.ofReal (2 * r))
      (ENNReal.ofReal r) := by
    refine ⟨?_⟩
    have h2 : ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have hr0 : ENNReal.ofReal r ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr
    rw [h2, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := ENNReal.ofReal (2 * r))
    (q := ENNReal.ofReal (2 * r)) (r := ENNReal.ofReal r) (μ := μ) (f := f) (g := g)
    (fun x y : ℝ => x * y) 1 continuous_mul hf hg
    (Filter.Eventually.of_forall fun x => by simp [norm_mul])
  simpa using h

/-- `‖1 + h‖_r ≤ 1 + C` from `‖h‖_r ≤ C`, probability measure, `r ≥ 1`. -/
theorem eLpNorm_one_add_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} {r : ℝ} (hr : 1 ≤ r) {C : ℝ} (hC : 0 ≤ C)
    (hb : eLpNorm h (ENNReal.ofReal r) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => 1 + h ω) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (1 + C) := by
  have h1 : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal 1 := by
    refine (eLpNorm_le_of_ae_bound (C := 1) aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => le_of_eq (by simp))).trans ?_
    simp
  have hadd := eLpNorm_add_le (p := ENNReal.ofReal r) (μ := μ)
    (f := fun _ : Ω => (1 : ℝ)) (g := h)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr)
  calc eLpNorm (fun ω => 1 + h ω) (ENNReal.ofReal r) μ
      ≤ eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal r) μ + eLpNorm h (ENNReal.ofReal r) μ :=
        hadd
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal C := add_le_add h1 hb
    _ = ENNReal.ofReal (1 + C) := (ENNReal.ofReal_add zero_le_one hC).symm

/-- `L = K𝒢₁₂` is measurable in the fresh coordinates. -/
theorem measurable_commonPortL {W : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (fun ω : LayerSample W .common => commonPortL b e X ω) := by
  have hG := BlockBand.Layers.measurable_layerResolvent (W := W) .common e (commonZ b e) X
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [commonPortL, commonPortResolvent, Matrix.mul_apply, Matrix.toBlocks₁₂,
    Matrix.of_apply]
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hG))

/-- `H = 𝒢₂₂` is measurable in the fresh coordinates. -/
theorem measurable_commonPortH {W : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (fun ω : LayerSample W .common => commonPortH b e X ω) := by
  have hG := BlockBand.Layers.measurable_layerResolvent (W := W) .common e (commonZ b e) X
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [commonPortH, commonPortResolvent, Matrix.toBlocks₂₂, Matrix.of_apply]
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hG)

/-- Elementary real inequality behind the `L` moment bound: with `s ≤ η'`, `t ≤ 5`,
`α ≤ A₀ + A₁` (all nonnegative),
`s (1 + (t + α + s B²) G) B ≤ η'(7 + η') ((1+A₀)(1+A₁)((1+B)(1+B)))((1+B)(1+G))`. -/
theorem commonPort_real_bound {s t α A0 A1 B G η' : ℝ} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hα0 : 0 ≤ α) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hB0 : 0 ≤ B) (hG0 : 0 ≤ G) (hs : s ≤ η')
    (ht : t ≤ 5) (hα : α ≤ A0 + A1) :
    s * (1 + (t + α + s * B ^ 2) * G) * B ≤
      η' * (7 + η') * (((1 + A0) * (1 + A1) * ((1 + B) * (1 + B))) * ((1 + B) * (1 + G))) := by
  have hη : 0 ≤ η' := hs0.trans hs
  set u := (1 + A0) * (1 + A1) with hu
  have hu1 : 1 ≤ u := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hαu : α ≤ u := by rw [hu]; nlinarith
  set β := 1 + B with hβ
  have hβ1 : 1 ≤ β := by linarith
  set g := 1 + G with hg
  have hg1 : 1 ≤ g := by linarith
  set Q := u * (β * β) * g with hQ
  have hbb : 1 ≤ β * β := one_le_mul_of_one_le_of_one_le hβ1 hβ1
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hu1 hbb) hg1
  have hgQ : g ≤ Q := le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hu1 hbb)
  have hu0 : 0 ≤ u := by linarith
  have hg0 : 0 ≤ g := by linarith
  have huQ : u * g ≤ Q := by
    calc u * g = u * 1 * g := by ring
      _ ≤ u * (β * β) * g :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbb hu0) hg0
  have hbQ : β * β * g ≤ Q :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) hu1) hg0
  have hBβ : B ^ 2 ≤ β * β := by rw [hβ]; nlinarith
  have hGg : G ≤ g := by linarith
  -- inner factor
  have i1 : t * G ≤ 5 * Q := (mul_le_mul ht hGg hG0 (by norm_num)).trans
    (mul_le_mul_of_nonneg_left hgQ (by norm_num))
  have i2 : α * G ≤ Q := (mul_le_mul hαu hGg hG0 (by linarith)).trans huQ
  have i3 : s * B ^ 2 * G ≤ η' * Q := by
    have : s * B ^ 2 * G ≤ η' * (β * β * g) := by
      calc s * B ^ 2 * G = s * (B ^ 2 * G) := by ring
        _ ≤ η' * ((β * β) * g) :=
          mul_le_mul hs (mul_le_mul hBβ hGg hG0 (by positivity)) (by positivity) hη
    exact this.trans (mul_le_mul_of_nonneg_left hbQ hη)
  have hin : 1 + (t + α + s * B ^ 2) * G ≤ (7 + η') * Q := by nlinarith
  have hin0 : 0 ≤ 1 + (t + α + s * B ^ 2) * G := by positivity
  calc s * (1 + (t + α + s * B ^ 2) * G) * B
      ≤ η' * ((7 + η') * Q) * β :=
        mul_le_mul (mul_le_mul hs hin hin0 hη) (by linarith) hB0 (by positivity)
    _ = η' * (7 + η') * ((u * (β * β)) * (β * g)) := by rw [hQ]; ring

/-- **Common-port mean, `moments` clause.** Law `layerLaw W b .common` (conditional on the old deformation, i.e. every
deterministic Hermitian `X`); `0 < b < 1/2`, `κ > 0` fixed first, then `p ≥ 1`, then `C, W₀`;
uniformly in `W ≥ W₀`, Hermitian `X` (no regularity domain, no norm bound on `X`) and
`e ∈ bulkInterval κ`: `‖ ‖L‖ ‖_{L^p} ≤ C` and `‖ ‖H‖ ‖_{L^p} ≤ C`, operator norms,
`L = K𝒢₁₂ = commonPortL`, `H = 𝒢₂₂ = commonPortH`.
Hypothesis: `GaussianAbsorptionContract` (at `η₀ = (1-2b)√(4-(2-κ)²)/2`, `M = 3`, moment
orders `p ≤ 4p ≤ ε₁ W`); other inputs `bond_eLpNorm_le`, `gueBlock_eLpNorm_le`. -/
theorem commonPortMean_moments (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
        ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        ∀ e ∈ bulkInterval κ,
          eLpNorm (fun ω => ‖commonPortL b e X ω‖) (ENNReal.ofReal p) (layerLaw W b .common) ≤
              ENNReal.ofReal C ∧
            eLpNorm (fun ω => ‖commonPortH b e X ω‖) (ENNReal.ofReal p) (layerLaw W b .common) ≤
              ENNReal.ofReal C := by
  intro b hb0 hb1 κ hκ p hp
  by_cases hκ2 : 2 < κ
  · refine ⟨0, 0, fun W _ _ X _ e he => ?_⟩
    exact absurd (le_trans he.1 he.2) (by linarith)
  push Not at hκ2
  set η₀ : ℝ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη0 : 0 < η₀ := by
    have hs := Real.sqrt_pos.mpr (BlockBand.Layers.four_sub_sq_pos hκ (by linarith))
    have : 0 < 1 - 2 * b := by linarith
    positivity
  obtain ⟨ε₁, CG, hε₁, hCG, hGA'⟩ := hGA b hb0 hb1 η₀ 3 hη0
  obtain ⟨CA, hCA, hA⟩ := gueBlock_eLpNorm_le
  set CB := BlockBand.Layers.bondMomentConst b with hCB
  have hCB0 : 0 < CB := BlockBand.Layers.bondMomentConst_pos b
  set C₀ : ℝ := η₀⁻¹ * (7 + η₀⁻¹) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  set CL : ℝ := C₀ * (CA * CA * (CB * CB) * CB * (1 + CG)) with hCL
  have hp0 : 0 < p := by linarith
  refine ⟨max CL CG, ⌈8 * p + 1 + 4 * p / ε₁⌉₊, ?_⟩
  intro W hW hW₀ X hX e he
  have hWr : 8 * p + 1 + 4 * p / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hW₀)
  have hpe : 0 ≤ 4 * p / ε₁ := by positivity
  have hq4 : 4 * p ≤ ε₁ * W := by
    have : 4 * p / ε₁ ≤ W := by linarith
    rw [div_le_iff₀ hε₁] at this; linarith
  have hq8 : 8 * p ≤ (W : ℝ) - 1 := by linarith
  have := BlockBand.Layers.bond_isProbabilityMeasure_layerLaw W b .common
  set μ := layerLaw W b .common with hμ
  have heabs : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hzim : η₀ ≤ (commonZ b e).im := BlockBand.Layers.commonZ_im_ge_of_mem_bulkInterval
    hb1.le hκ he
  have hznorm : ‖commonZ b e‖ ≤ 3 := BlockBand.Layers.norm_commonZ_le hb0.le (by linarith) heabs
  have hzge : η₀ ≤ ‖commonZ b e‖ := hzim.trans (Complex.im_le_norm _)
  have hz0 : commonZ b e ≠ 0 := by
    intro h; rw [h, norm_zero] at hzge; linarith
  obtain ⟨hinv, hmom⟩ := hGA' W hW .common X hX e (commonZ b e) hzim hznorm
  -- the resolvent moments
  have hGm : Measurable (fun ω : LayerSample W .common => ‖commonPortResolvent b e X ω‖) :=
    BlockBand.Layers.measurable_norm_layerResolvent .common e (commonZ b e) X
  have hG4 : eLpNorm (fun ω => ‖commonPortResolvent b e X ω‖) (ENNReal.ofReal (4 * p)) μ ≤
      ENNReal.ofReal CG := hmom (4 * p) (by linarith) hq4
  have hGp : eLpNorm (fun ω => ‖commonPortResolvent b e X ω‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal CG := hmom p hp (by linarith)
  refine ⟨?_, ?_⟩
  swap
  · -- `H`
    refine (eLpNorm_mono
      (continuous_norm.measurable.comp (measurable_commonPortH b e X)).aestronglyMeasurable
      (fun ω => ?_)).trans (hGp.trans (ENNReal.ofReal_le_ofReal
      (le_max_right _ _)))
    simp only [Function.comp_apply, norm_norm]
    exact norm_commonPortH_le b e X ω
  -- `L`
  set a0 : LayerSample W .common → ℝ := fun ω => 1 + ‖ω.1 0‖ with ha0
  set a1 : LayerSample W .common → ℝ := fun ω => 1 + ‖ω.1 1‖ with ha1
  set β : LayerSample W .common → ℝ := fun ω => 1 + ‖bondMatrix .common ω.2‖ with hβ
  set g : LayerSample W .common → ℝ := fun ω => 1 + ‖commonPortResolvent b e X ω‖ with hg
  have hma : ∀ a : Fin 2, Measurable (fun ω : LayerSample W .common => 1 + ‖ω.1 a‖) := fun a =>
    measurable_const.add
      (continuous_norm.measurable.comp ((measurable_pi_apply a).comp measurable_fst))
  have hmβ : Measurable β := measurable_const.add (BlockBand.Layers.bond_measurable_opNorm _)
  have hmg : Measurable g := measurable_const.add hGm
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂μ, ‖‖commonPortL b e X ω‖‖ ≤
      ‖C₀ * (((a0 ω * a1 ω) * (β ω * β ω)) * (β ω * g ω))‖ := by
    filter_upwards [hinv] with ω hω
    rw [norm_norm]
    have hL := norm_commonPortL_le b e X ω hz0 hω
    have hα : ‖Internal.Contracts.Layers.blockDiag ω.1‖ ≤ ‖ω.1 0‖ + ‖ω.1 1‖ := by
      refine (norm_blockDiag_le ω.1).trans (le_of_eq ?_)
      exact Fin.sum_univ_two _
    have hs : ‖commonZ b e‖⁻¹ ≤ η₀⁻¹ := inv_anti₀ hη0 hzge
    have ht : ‖boundaryZ b e + (e : ℂ)‖ ≤ 5 := by
      refine (norm_add_le _ _).trans ?_
      have := BlockBand.Layers.norm_boundaryZ_le hb0.le (by linarith) heabs
      rw [Complex.norm_real, Real.norm_eq_abs]
      linarith
    have hrhs0 : 0 ≤ C₀ * (((a0 ω * a1 ω) * (β ω * β ω)) * (β ω * g ω)) := by
      simp only [ha0, ha1, hβ, hg]; positivity
    rw [Real.norm_of_nonneg hrhs0]
    exact hL.trans (commonPort_real_bound (by positivity) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hs ht hα)
  have hLm : AEStronglyMeasurable (fun ω => ‖commonPortL b e X ω‖) μ :=
    (continuous_norm.measurable.comp (measurable_commonPortL b e X)).aestronglyMeasurable
  refine (eLpNorm_mono_ae hLm hpt).trans ?_
  -- Hölder tree
  have hm1 : AEStronglyMeasurable (fun ω => a0 ω * a1 ω) μ :=
    ((hma 0).mul (hma 1)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun ω => β ω * β ω) μ := (hmβ.mul hmβ).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun ω => β ω * g ω) μ := (hmβ.mul hmg).aestronglyMeasurable
  have hm12 : AEStronglyMeasurable (fun ω => (a0 ω * a1 ω) * (β ω * β ω)) μ :=
    (((hma 0).mul (hma 1)).mul (hmβ.mul hmβ)).aestronglyMeasurable
  have hsmul : (fun ω => C₀ * (((a0 ω * a1 ω) * (β ω * β ω)) * (β ω * g ω))) =
      C₀ • (fun ω => ((a0 ω * a1 ω) * (β ω * β ω)) * (β ω * g ω)) := by
    ext ω; simp [smul_eq_mul]
  rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal hC₀0]
  have h44 : (2 : ℝ) * (2 * p) = 4 * p := by ring
  have h88 : (2 : ℝ) * (4 * p) = 8 * p := by ring
  -- level 1
  have L1 := eLpNorm_mul_le_two hm12 hm3 hp0 (μ := μ)
  have L2a := eLpNorm_mul_le_two hm1 hm2 (by linarith : (0 : ℝ) < 2 * p) (μ := μ)
  have L2b := eLpNorm_mul_le_two hmβ.aestronglyMeasurable hmg.aestronglyMeasurable
    (by linarith : (0 : ℝ) < 2 * p) (μ := μ)
  have L3a := eLpNorm_mul_le_two (hma 0).aestronglyMeasurable (hma 1).aestronglyMeasurable
    (by linarith : (0 : ℝ) < 4 * p) (μ := μ)
  have L3b := eLpNorm_mul_le_two hmβ.aestronglyMeasurable hmβ.aestronglyMeasurable
    (by linarith : (0 : ℝ) < 4 * p) (μ := μ)
  rw [h44] at L2a L2b
  rw [h88] at L3a L3b
  -- leaf bounds
  have hA8 : ∀ a : Fin 2, eLpNorm (fun ω : LayerSample W .common => 1 + ‖ω.1 a‖)
      (ENNReal.ofReal (8 * p)) μ ≤ ENNReal.ofReal CA := fun a =>
    hA W b hb0.le hb1.le .common a (8 * p) (by linarith) hq8
  have hB8 : eLpNorm β (ENNReal.ofReal (8 * p)) μ ≤ ENNReal.ofReal CB :=
    BlockBand.Layers.bond_eLpNorm_le .common hb0 (by linarith) (by linarith)
  have hB4 : eLpNorm β (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal CB :=
    BlockBand.Layers.bond_eLpNorm_le .common hb0 (by linarith) (by linarith)
  have hg4 : eLpNorm g (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (1 + CG) :=
    eLpNorm_one_add_le (by linarith) hCG.le hG4
  have hCLeq : ENNReal.ofReal C₀ * (ENNReal.ofReal CA * ENNReal.ofReal CA *
      (ENNReal.ofReal CB * ENNReal.ofReal CB) * (ENNReal.ofReal CB * ENNReal.ofReal (1 + CG))) =
      ENNReal.ofReal CL := by
    rw [hCL, ENNReal.ofReal_mul hC₀0, ← ENNReal.ofReal_mul hCA.le,
      ← ENNReal.ofReal_mul hCB0.le, ← ENNReal.ofReal_mul hCB0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 2; ring
  calc ENNReal.ofReal C₀ * eLpNorm (fun ω => ((a0 ω * a1 ω) * (β ω * β ω)) * (β ω * g ω))
        (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal CA * ENNReal.ofReal CA *
          (ENNReal.ofReal CB * ENNReal.ofReal CB) *
          (ENNReal.ofReal CB * ENNReal.ofReal (1 + CG))) := by
        gcongr
        refine L1.trans (mul_le_mul' (L2a.trans (mul_le_mul' (L3a.trans ?_) (L3b.trans ?_)))
          (L2b.trans (mul_le_mul' hB4 hg4)))
        · exact mul_le_mul' (hA8 0) (hA8 1)
        · exact mul_le_mul' hB8 hB8
    _ = ENNReal.ofReal CL := hCLeq
    _ ≤ ENNReal.ofReal (max CL CG) := ENNReal.ofReal_le_ofReal (le_max_left _ _)

end BlockBand.Critical.CommonPort
