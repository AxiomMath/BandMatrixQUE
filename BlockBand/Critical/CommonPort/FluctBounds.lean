module

public import BlockBand.Critical.CommonPort.FluctCalculus
public import BlockBand.Critical.CommonPort.Moments

/-!
# Common-port mean: pointwise and moment bounds for the fluctuation

* `cpPsi ω = (1+‖A₀‖)(1+‖A₁‖)(1+‖Bm‖)(1+‖𝒢‖) ≥ 1` (fresh layer sample `ω`, common port).
* `reg_weighted_real_bound`: elementary real inequality.
* `reg_bounds`: deterministic; for every sample with `IsUnit (layerMatrix .common e z₀ X ω).det`
  and Hermitian diagonal blocks, Hermitian `X`, `|e| ≤ 2`, `0 ≤ b ≤ 1`, regularization height
  `0 < κ ≤ 1`, with `0 < η₀ ≤ Im z₀`: `‖𝒢_κ‖ ≤ 2Ψ`, `‖K𝒢_κ,₁₂‖ ≤ η₀⁻¹ c₁ Ψ⁴`, `‖K · topRows 𝒢_κ‖ ≤ c₁(1+η₀⁻¹)Ψ⁴`,
  `c₁ = 1 + 2(7 + η₀⁻¹)`.
* `eLpNorm_pow_eq`: `‖f^k‖_p = ‖f‖_{kp}^k` for nonnegative `f`.
* `eLpNorm_cpPsi_le`: `‖Ψ‖_{L^r(layerLaw)} ≤ C_A² C_B C_G'` from leaf bounds at exponent `4r`
  (taken as hypotheses: `‖1+‖A_a‖‖_{4r} ≤ C_A`, `‖1+‖Bm‖‖_{4r} ≤ C_B`, `‖1+‖𝒢‖‖_{4r} ≤ C_G'`);
  Hölder via `eLpNorm_mul_le_two`. The power step `‖Ψ⁹‖_p = ‖Ψ‖_{9p}⁹` is applied in the
  fluctuation bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Ψ = (1+‖A₀‖)(1+‖A₁‖)(1+‖Bm‖)(1+‖𝒢‖)`. -/
def cpPsi (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : LayerSample W .common) : ℝ :=
  (1 + ‖ω.1 0‖) * (1 + ‖ω.1 1‖) * (1 + ‖bondMatrix .common ω.2‖) *
    (1 + ‖commonPortResolvent b e X ω‖)

theorem one_le_cpPsi (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : 1 ≤ cpPsi b e X ω := by
  unfold cpPsi
  have h0 := norm_nonneg (ω.1 0)
  have h1 := norm_nonneg (ω.1 1)
  have h2 := norm_nonneg (bondMatrix .common ω.2)
  have h3 := norm_nonneg (commonPortResolvent b e X ω)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) (by linarith)) (by linarith)

theorem measurable_cpPsi (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (cpPsi (W := W) b e X) := by
  have hma : ∀ a : Fin 2, Measurable (fun ω : LayerSample W .common => 1 + ‖ω.1 a‖) := fun a =>
    measurable_const.add
      (continuous_norm.measurable.comp ((measurable_pi_apply a).comp measurable_fst))
  exact (((hma 0).mul (hma 1)).mul (measurable_const.add (bond_measurable_opNorm _))).mul
    (measurable_const.add (measurable_norm_layerResolvent .common e (commonZ b e) X))

/-- Elementary real inequality behind `reg_bounds`. -/
theorem reg_weighted_real_bound {s S α A0 A1 B g g0 η' : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ η')
    (hS0 : 0 ≤ S) (hS : S ≤ 6 + α) (hα : α ≤ A0 + A1) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hB : 0 ≤ B)
    (hg0 : 0 ≤ g) (hg : g ≤ 2 * g0) {Ψ : ℝ}
    (hΨ : Ψ = (1 + A0) * (1 + A1) * (1 + B) * (1 + g0)) :
    1 + (S + s * B ^ 2) * g ≤ (1 + 2 * (7 + η')) * Ψ ^ 3 ∧
      s * (1 + (S + s * B ^ 2) * g) * B ≤ η' * (1 + 2 * (7 + η')) * Ψ ^ 4 := by
  have hη : 0 ≤ η' := hs0.trans hs
  have hu : 1 ≤ (1 + A0) * (1 + A1) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have huB : 1 ≤ (1 + A0) * (1 + A1) * (1 + B) := one_le_mul_of_one_le_of_one_le hu (by linarith)
  have hΨ1 : 1 ≤ Ψ := hΨ ▸ one_le_mul_of_one_le_of_one_le huB (by linarith)
  have hΨ0 : 0 ≤ Ψ := by linarith
  have hαΨ : α ≤ Ψ := by
    have : A0 + A1 ≤ (1 + A0) * (1 + A1) := by nlinarith
    have h2 : (1 + A0) * (1 + A1) ≤ Ψ := by
      have : (1 + A0) * (1 + A1) ≤ (1 + A0) * (1 + A1) * (1 + B) :=
        le_mul_of_one_le_right (by linarith) (by linarith)
      rw [hΨ]
      exact this.trans (le_mul_of_one_le_right (by linarith) (by linarith))
    linarith
  have hBΨ : B ≤ Ψ := by
    have h1 : 1 + B ≤ (1 + A0) * (1 + A1) * (1 + B) := le_mul_of_one_le_left (by linarith) hu
    have h2 : (1 + A0) * (1 + A1) * (1 + B) ≤ Ψ :=
      hΨ ▸ le_mul_of_one_le_right (by linarith) (by linarith)
    linarith
  have hgΨ : g0 ≤ Ψ := by
    have : 1 + g0 ≤ Ψ := hΨ ▸ le_mul_of_one_le_left (by linarith) huB
    linarith
  have hSB : S + s * B ^ 2 ≤ (7 + η') * Ψ ^ 2 := by
    have h1 : s * B ^ 2 ≤ η' * Ψ ^ 2 :=
      mul_le_mul hs (pow_le_pow_left₀ hB hBΨ 2) (by positivity) hη
    have hsq : 1 ≤ Ψ ^ 2 := one_le_pow₀ hΨ1
    have hΨΨ : Ψ ≤ Ψ ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hΨ0 hΨ1
    have e1 : (7 + η') * Ψ ^ 2 = 6 * Ψ ^ 2 + Ψ ^ 2 + η' * Ψ ^ 2 := by ring
    linarith
  have hg2 : g ≤ 2 * Ψ := by linarith
  have hX : (S + s * B ^ 2) * g ≤ 2 * (7 + η') * Ψ ^ 3 := by
    calc (S + s * B ^ 2) * g ≤ ((7 + η') * Ψ ^ 2) * (2 * Ψ) :=
          mul_le_mul hSB hg2 hg0 (by positivity)
      _ = 2 * (7 + η') * Ψ ^ 3 := by ring
  have hΨ3 : 1 ≤ Ψ ^ 3 := one_le_pow₀ hΨ1
  have h11 : 1 + (S + s * B ^ 2) * g ≤ (1 + 2 * (7 + η')) * Ψ ^ 3 := by
    have e1 : (1 + 2 * (7 + η')) * Ψ ^ 3 = Ψ ^ 3 + 2 * (7 + η') * Ψ ^ 3 := by ring
    linarith
  refine ⟨h11, ?_⟩
  have h110 : 0 ≤ 1 + (S + s * B ^ 2) * g := by positivity
  calc s * (1 + (S + s * B ^ 2) * g) * B
      ≤ η' * ((1 + 2 * (7 + η')) * Ψ ^ 3) * Ψ :=
        mul_le_mul (mul_le_mul hs h11 h110 hη) hBΨ hB (by positivity)
    _ = η' * (1 + 2 * (7 + η')) * Ψ ^ 4 := by ring

/-- **Pointwise weighted bounds for the regularized resolvent.**
Deterministic, for every sample `ω` with `IsUnit (layerMatrix .common e z₀ X ω).det` and
Hermitian diagonal blocks; Hermitian `X`; `|e| ≤ 2`, `0 ≤ b ≤ 1`; `0 < κ ≤ 1`;
`0 < η₀ ≤ Im z₀`. With `Ψ = cpPsi`, `c₁ = 1 + 2(7 + η₀⁻¹)`:
`‖𝒢_κ‖ ≤ 2Ψ`, `‖K 𝒢_κ,₁₂‖ ≤ η₀⁻¹ c₁ Ψ⁴`, `‖K · topRows 𝒢_κ‖ ≤ c₁ (1 + η₀⁻¹) Ψ⁴`. -/
theorem reg_bounds {b e : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (he : |e| ≤ 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {η₀ : ℝ} (hη : 0 < η₀) (hzim : η₀ ≤ (commonZ b e).im) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (ω : LayerSample W .common)
    (hA : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian)
    (hN : IsUnit (layerMatrix .common e (commonZ b e) X ω).det) :
    ‖regResolvent e (commonZ b e) X κ ω‖ ≤ 2 * cpPsi b e X ω ∧
      ‖matchedLeadK b e X * (regResolvent e (commonZ b e) X κ ω).toBlocks₁₂‖ ≤
        η₀⁻¹ * (1 + 2 * (7 + η₀⁻¹)) * cpPsi b e X ω ^ 4 ∧
      ‖matchedLeadK b e X * topRows (regResolvent e (commonZ b e) X κ ω)‖ ≤
        (1 + 2 * (7 + η₀⁻¹)) * (1 + η₀⁻¹) * cpPsi b e X ω ^ 4 := by
  have hz0 : 0 ≤ (commonZ b e).im := hη.le.trans hzim
  obtain ⟨hMu, -⟩ := tfl_reg_inv_le .common e hX ω hA hz0 hκ
  have hG2 : ‖regResolvent e (commonZ b e) X κ ω‖ ≤ 2 * ‖commonPortResolvent b e X ω‖ :=
    tfl_reg_inv_le_two .common e hX ω hA hz0 hκ hN
  set z' := commonZ b e + (κ : ℂ) * Complex.I with hz'
  have hz'im : η₀ ≤ z'.im := by
    rw [hz']; simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
    linarith
  have hz'n : η₀ ≤ ‖z'‖ := hz'im.trans (Complex.im_le_norm _)
  have hz'0 : z' ≠ 0 := by intro h; rw [h, norm_zero] at hz'n; linarith
  have hs : ‖z'‖⁻¹ ≤ η₀⁻¹ := inv_anti₀ hη hz'n
  have h11 := norm_K_regG11_le b e X κ ω hz'0 hMu
  have h12 := norm_K_regG12_le b e X κ ω hz'0 hMu
  have hS := norm_regShift_le b e κ ω
  have hzb : ‖boundaryZ b e + (e : ℂ)‖ ≤ 5 := by
    refine (norm_add_le _ _).trans ?_
    have := norm_boundaryZ_le hb0 hb1 he
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hα : ‖Internal.Contracts.Layers.blockDiag ω.1‖ ≤ ‖ω.1 0‖ + ‖ω.1 1‖ :=
    (norm_blockDiag_le ω.1).trans (le_of_eq (Fin.sum_univ_two _))
  have hS' : ‖regShift b e κ ω‖ ≤ 6 + ‖Internal.Contracts.Layers.blockDiag ω.1‖ := by
    rw [abs_of_pos hκ] at hS; linarith
  obtain ⟨r11, r12⟩ := reg_weighted_real_bound (s := ‖z'‖⁻¹) (S := ‖regShift b e κ ω‖)
    (B := ‖bondMatrix .common ω.2‖) (g := ‖regResolvent e (commonZ b e) X κ ω‖)
    (g0 := ‖commonPortResolvent b e X ω‖) (by positivity) hs (norm_nonneg _) hS' hα
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hG2
    (Ψ := cpPsi b e X ω) rfl
  have hΨ1 := one_le_cpPsi b e X ω
  have hg11 := h11.trans r11
  have hg12 := h12.trans r12
  refine ⟨?_, hg12, ?_⟩
  · have : ‖commonPortResolvent b e X ω‖ ≤ cpPsi b e X ω := by
      unfold cpPsi
      have h0 := norm_nonneg (ω.1 0)
      have h1 := norm_nonneg (ω.1 1)
      have h2 := norm_nonneg (bondMatrix .common ω.2)
      have h3 := norm_nonneg (commonPortResolvent b e X ω)
      have hu : 1 ≤ (1 + ‖ω.1 0‖) * (1 + ‖ω.1 1‖) * (1 + ‖bondMatrix .common ω.2‖) :=
        one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) (by linarith)
      have := le_mul_of_one_le_left (by linarith : (0 : ℝ) ≤ 1 + ‖commonPortResolvent b e X ω‖) hu
      linarith
    linarith
  · refine (norm_mul_topRows_le _ _).trans ?_
    have hΨ34 : cpPsi b e X ω ^ 3 ≤ cpPsi b e X ω ^ 4 :=
      pow_le_pow_right₀ hΨ1 (by norm_num)
    have hc1 : 0 ≤ 1 + 2 * (7 + η₀⁻¹) := by positivity
    have := mul_le_mul_of_nonneg_left hΨ34 hc1
    nlinarith [hg11, hg12, this]

/-- `‖f^k‖_p = ‖f‖_{kp}^k` for nonnegative `f`. -/
theorem eLpNorm_pow_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω) (k : ℕ) (hk : 0 < k) {p : ℝ}
    (hp : 0 ≤ p) :
    eLpNorm (fun ω => f ω ^ k) (ENNReal.ofReal p) μ =
      eLpNorm f (ENNReal.ofReal (k * p)) μ ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := eLpNorm_norm_rpow (p := ENNReal.ofReal p) (μ := μ) f hf hk0
  have e1 : (fun ω => ‖f ω‖ ^ (k : ℝ)) = fun ω => f ω ^ k := by
    funext ω; rw [Real.norm_of_nonneg (hf0 ω), Real.rpow_natCast]
  rw [e1, ← ENNReal.ofReal_mul hp, mul_comm p, ENNReal.rpow_natCast] at h
  exact h

/-- **Moments of `Ψ`** (law `layerLaw W b .common`): from leaf bounds at exponent `4r`,
`‖Ψ‖_r ≤ C_A² C_B C_G'`, where `C_A, C_B, C_G'` bound `1+‖A_a‖`, `1+‖Bm‖`, `1+‖𝒢‖` in
`L^{4r}`. -/
theorem eLpNorm_cpPsi_le {b e : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {r : ℝ}
    (hr : 0 < r) {CA CB CG : ℝ}
    (hA : ∀ a : Fin 2, eLpNorm (fun ω : LayerSample W .common => 1 + ‖ω.1 a‖)
      (ENNReal.ofReal (4 * r)) (layerLaw W b .common) ≤ ENNReal.ofReal CA)
    (hB : eLpNorm (fun ω : LayerSample W .common => 1 + ‖bondMatrix .common ω.2‖)
      (ENNReal.ofReal (4 * r)) (layerLaw W b .common) ≤ ENNReal.ofReal CB)
    (hG : eLpNorm (fun ω : LayerSample W .common => 1 + ‖commonPortResolvent b e X ω‖)
      (ENNReal.ofReal (4 * r)) (layerLaw W b .common) ≤ ENNReal.ofReal CG) :
    eLpNorm (cpPsi b e X) (ENNReal.ofReal r) (layerLaw W b .common) ≤
      ENNReal.ofReal CA * ENNReal.ofReal CA * (ENNReal.ofReal CB * ENNReal.ofReal CG) := by
  have hma : ∀ a : Fin 2, Measurable (fun ω : LayerSample W .common => 1 + ‖ω.1 a‖) := fun a =>
    measurable_const.add
      (continuous_norm.measurable.comp ((measurable_pi_apply a).comp measurable_fst))
  have hmβ : Measurable (fun ω : LayerSample W .common => 1 + ‖bondMatrix .common ω.2‖) :=
    measurable_const.add (bond_measurable_opNorm _)
  have hmg : Measurable (fun ω : LayerSample W .common => 1 + ‖commonPortResolvent b e X ω‖) :=
    measurable_const.add (measurable_norm_layerResolvent .common e (commonZ b e) X)
  have L1 := eLpNorm_mul_le_two (μ := layerLaw W b .common)
    ((hma 0).mul (hma 1)).aestronglyMeasurable (hmβ.mul hmg).aestronglyMeasurable hr
  have L2a := eLpNorm_mul_le_two (μ := layerLaw W b .common)
    (hma 0).aestronglyMeasurable (hma 1).aestronglyMeasurable (by linarith : (0 : ℝ) < 2 * r)
  have L2b := eLpNorm_mul_le_two (μ := layerLaw W b .common)
    hmβ.aestronglyMeasurable hmg.aestronglyMeasurable (by linarith : (0 : ℝ) < 2 * r)
  have h44 : (2 : ℝ) * (2 * r) = 4 * r := by ring
  rw [h44] at L2a L2b
  have hfun : cpPsi b e X = fun ω : LayerSample W .common =>
      ((1 + ‖ω.1 0‖) * (1 + ‖ω.1 1‖)) *
        ((1 + ‖bondMatrix .common ω.2‖) * (1 + ‖commonPortResolvent b e X ω‖)) := by
    funext ω; unfold cpPsi; ring
  rw [hfun]
  exact L1.trans (mul_le_mul' (L2a.trans (mul_le_mul' (hA 0) (hA 1)))
    (L2b.trans (mul_le_mul' hB hG)))

end BlockBand.Critical.CommonPort
