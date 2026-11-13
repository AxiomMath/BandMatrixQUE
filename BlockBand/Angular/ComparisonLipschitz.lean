module

public import BlockBand.Angular.Comparison

/-!
# The angular comparison for the Lipschitz class

A test `Φ(v) = φ(𝓛v/‖𝓛v‖)` with `|φ| ≤ M` and `φ` `L_φ`-Lipschitz on the unit sphere of
`Ran 𝓛` is encoded by `ReconLip L Φ L_φ` and `|Φ| ≤ M` off the origin (`ComparisonBasic`).
* `reconLip_factor`: `Φ = g ∘ (𝓛v/‖𝓛v‖)` off the origin with `g` `L_φ`-Lipschitz on the
  Euclidean space `ℂ^κ` and `|g| ≤ M` (McShane extension `LipschitzOnWith.extend_real`, then
  clamping to `[-M, M]`).
* `exists_smooth_lip_approx`: convolution with a normed bump of radius `ε` gives `h` smooth,
  `L_φ`-Lipschitz, `|h| ≤ M`, `|h - g| ≤ L_φ ε`.
* `exists_C1_approx`: hence `C¹` tests `Ψ = h(𝓛v/‖𝓛v‖)` with the same `M, L_φ` and
  `|Ψ - Φ| ≤ δ` off the origin.
* `angular_comparison`: the angular comparison for the Lipschitz class, with the constant
  `compConst σ Y Zb C₀ χ` of `angular_comparison_C1`; the error of the approximation is
  `δ ∫ e^{q}𝔷 χ|j - j_*| dν_N → 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix Metric
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open scoped ComplexConjugate NNReal Convolution

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem norm_toLp_sub (x y : κ → ℂ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ κ) - WithLp.toLp 2 y‖ = l2Norm (x - y) := by
  rw [← WithLp.toLp_sub, ← l2Norm_eq_norm]

/-- **Factorization** (McShane): a bounded reconstruction-Lipschitz test is
`g(𝓛v/‖𝓛v‖)` off the origin with `g` `L_φ`-Lipschitz on `ℂ^κ` (Euclidean) and `|g| ≤ M`. -/
theorem reconLip_factor {L : Matrix κ ι ℂ} {Φ : (ι → ℂ) → ℝ} {M Lφ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ v, v ≠ 0 → |Φ v| ≤ M) (hLφ : 0 ≤ Lφ) (hlip : ReconLip L Φ Lφ) :
    ∃ g : EuclideanSpace ℂ κ → ℝ, LipschitzWith Lφ.toNNReal g ∧ (∀ x, |g x| ≤ M) ∧
      ∀ v, v ≠ 0 → Φ v = g (WithLp.toLp 2 (recon L v)) := by
  classical
  let f : EuclideanSpace ℂ κ → ℝ := fun u =>
    if h : ∃ v, v ≠ 0 ∧ WithLp.toLp 2 (recon L v) = u then Φ h.choose else 0
  have hf : ∀ v, v ≠ 0 → f (WithLp.toLp 2 (recon L v)) = Φ v := by
    intro v hv
    have h : ∃ w, w ≠ 0 ∧ WithLp.toLp 2 (recon L w) = WithLp.toLp 2 (recon L v) := ⟨v, hv, rfl⟩
    simp only [f]
    rw [dite_eq_left_of_eq_true (eq_true h)]
    have hw := h.choose_spec
    have e : recon L h.choose = recon L v := by
      have := congrArg WithLp.ofLp hw.2; simpa using this
    have := hlip h.choose v hw.1 hv
    rw [e, sub_self, show l2Norm (0 : κ → ℂ) = 0 by simp [l2Norm_eq, normSqSum], mul_zero]
      at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  have hfl : LipschitzOnWith Lφ.toNNReal f {u | ∃ v, v ≠ 0 ∧ WithLp.toLp 2 (recon L v) = u} := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    rw [hf v hv, hf w hw, Real.dist_eq, dist_eq_norm, norm_toLp_sub, Real.coe_toNNReal _ hLφ]
    exact hlip v w hv hw
  obtain ⟨g₀, hg₀, heq⟩ := hfl.extend_real
  refine ⟨fun x => max (-M) (min M (g₀ x)), (hg₀.const_min M).const_max (-M), fun x => ?_,
    fun v hv => ?_⟩
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · have h1 : g₀ (WithLp.toLp 2 (recon L v)) = Φ v := (heq ⟨v, hv, rfl⟩).symm.trans (hf v hv)
    have := abs_le.1 (hM v hv)
    simp only [h1, min_eq_right this.2, max_eq_right this.1]

/-- **Mollification**: a bounded Lipschitz function on `ℂ^κ` is uniformly approximated by smooth
functions with the same bound and Lipschitz constant. -/
theorem exists_smooth_lip_approx {g : EuclideanSpace ℂ κ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {M : ℝ} (hgM : ∀ x, |g x| ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : EuclideanSpace ℂ κ → ℝ, ContDiff ℝ 1 h ∧ LipschitzWith K h ∧ (∀ x, |h x| ≤ M) ∧
      ∀ x, |h x - g x| ≤ K * ε := by
  let μ : Measure (EuclideanSpace ℂ κ) := Measure.addHaar
  let ρ : ContDiffBump (0 : EuclideanSpace ℂ κ) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let k := ρ.normed μ
  have hgc := hg.continuous
  have key : ∀ F : EuclideanSpace ℂ κ → ℝ, Continuous F → ∀ B, (∀ t, |F t| ≤ B) →
      |∫ t, k t * F t ∂μ| ≤ B := by
    intro F hF B hB
    have hi : Integrable (fun t => k t * F t) μ :=
      (ρ.continuous_normed.mul hF).integrable_of_hasCompactSupport
        ρ.hasCompactSupport_normed.mul_right
    calc |∫ t, k t * F t ∂μ| ≤ ∫ t, |k t * F t| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ t, k t * B ∂μ := integral_mono hi.abs (ρ.integrable_normed.mul_const B) fun t => by
          rw [abs_mul, abs_of_nonneg (ρ.nonneg_normed t)]
          exact mul_le_mul_of_nonneg_left (hB t) (ρ.nonneg_normed t)
      _ = B := by rw [integral_mul_const, ρ.integral_normed, one_mul]
  have hconv : ∀ x, (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x = ∫ t, k t * g (x - t) ∂μ := fun x => by
    rw [convolution_def]; rfl
  have hint : ∀ x, Integrable (fun t => k t * g (x - t)) μ := fun x =>
    (ρ.continuous_normed.mul (hgc.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport ρ.hasCompactSupport_normed.mul_right
  refine ⟨k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g, ?_, ?_, ?_, ?_⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) ρ.contDiff_normed
      hgc.locallyIntegrable
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, hconv, hconv, ← integral_sub (hint x) (hint y)]
    have e : (fun t => k t * g (x - t) - k t * g (y - t)) =
        fun t => k t * (g (x - t) - g (y - t)) := funext fun t => by ring
    rw [e]
    refine key _ ((hgc.comp (continuous_const.sub continuous_id)).sub
      (hgc.comp (continuous_const.sub continuous_id))) _ fun t => ?_
    have := hg.dist_le_mul (x - t) (y - t)
    rwa [Real.dist_eq, dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm] at this
  · intro x; rw [hconv]
    exact key _ (hgc.comp (continuous_const.sub continuous_id)) M fun t => hgM _
  · intro x
    have := ρ.dist_normed_convolution_le (μ := μ) (x₀ := x) (ε := K * ε)
      hgc.aestronglyMeasurable fun y hy =>
        (hg.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball.1 hy)) K.2)
    rwa [Real.dist_eq] at this

/-- `v ↦ 𝓛v/‖𝓛v‖ ∈ ℂ^κ` (Euclidean) is `C¹` off the origin for injective `𝓛`. -/
theorem toLp_recon_c1 {L : Matrix κ ι ℂ} (hL : ∀ x, L *ᵥ x = 0 → x = 0) :
    ContDiffOn ℝ 1 (fun v => (WithLp.toLp 2 (recon L v) : EuclideanSpace ℂ κ)) {z | z ≠ 0} := by
  have hlin : ContDiff ℝ 1 (fun v : ι → ℂ => L *ᵥ v) :=
    ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)).restrictScalars ℝ).contDiff
  have hn : ContDiffOn ℝ 1 (fun v => l2Norm (L *ᵥ v)) {z | z ≠ 0} := by
    have h0 : ContDiffOn ℝ 1 (fun v => normSqSum (L *ᵥ v)) {z : ι → ℂ | z ≠ 0} :=
      ((contDiff_normSqSum.of_le le_top).comp hlin).contDiffOn
    exact h0.sqrt fun v hv => (normSqSum_pos fun h => hv (hL v h)).ne'
  have hc : ContDiffOn ℝ 1 (fun v => ((l2Norm (L *ᵥ v) : ℂ))⁻¹) {z | z ≠ 0} :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hn).inv fun v hv => by
      simp [(ConeDivergence.l2Norm_pos fun h => hv (hL v h)).ne']
  have hr : ContDiffOn ℝ 1 (recon L) {z | z ≠ 0} := hc.smul hlin.contDiffOn
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.contDiff.comp_contDiffOn hr

/-- **Smooth approximation**: a bounded reconstruction-Lipschitz test is uniformly approximated
off the origin by `C¹` tests with the same bound and Lipschitz constant. -/
theorem exists_C1_approx {L : Matrix κ ι ℂ} (hL : ∀ x, L *ᵥ x = 0 → x = 0)
    {Φ : (ι → ℂ) → ℝ} {M Lφ : ℝ} (hM0 : 0 ≤ M) (hM : ∀ v, v ≠ 0 → |Φ v| ≤ M) (hLφ : 0 ≤ Lφ)
    (hlip : ReconLip L Φ Lφ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ψ : (ι → ℂ) → ℝ, ContDiffOn ℝ 1 Ψ {z | z ≠ 0} ∧ (∀ v, v ≠ 0 → |Ψ v| ≤ M) ∧
      ReconLip L Ψ Lφ ∧ ∀ v, v ≠ 0 → |Ψ v - Φ v| ≤ δ := by
  obtain ⟨g, hg, hgM, hΦg⟩ := reconLip_factor hM0 hM hLφ hlip
  have hε : 0 < δ / (Lφ + 1) := div_pos hδ (by linarith)
  obtain ⟨h, hc, hh, hhM, hhg⟩ := exists_smooth_lip_approx hg hgM hε
  refine ⟨fun v => h (WithLp.toLp 2 (recon L v)), hc.comp_contDiffOn (toLp_recon_c1 hL),
    fun v _ => hhM _, fun v v' _ _ => ?_, fun v hv => ?_⟩
  · have := hh.dist_le_mul (WithLp.toLp 2 (recon L v)) (WithLp.toLp 2 (recon L v'))
    rwa [Real.dist_eq, dist_eq_norm, norm_toLp_sub, Real.coe_toNNReal _ hLφ] at this
  · rw [hΦg v hv]
    refine (hhg _).trans ?_
    rw [Real.coe_toNNReal _ hLφ, ← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith

/-- **The angular comparison**. Let `𝓛` be injective, `J` a Hermitian
contraction, `χ` a cutoff, `𝔷 ≥ 0` scale-invariant and `C¹` off `0`, and assume
the angular first-moment bound in the tested form of `angular_ratio`. If `Φ(v) = φ(𝓛v/‖𝓛v‖)` with
`|φ| ≤ M` and `φ` `L_φ`-Lipschitz on the unit sphere of `Ran 𝓛` (encoded as `|Φ| ≤ M` off the
origin and `ReconLip L Φ L_φ`), then
`|ν[χ(b₂)(j - j_*)Φ]| ≤ C(M + L_φ)/N · {Z + r + ν(χ‖H‖)}`,
`j = Re v*Jv`, `j_* = N⁻¹ Re Tr ΓJ`, with `C = compConst σ Y Zb C₀ χ` depending only on
`σ ≥ s, s⁻¹`, `Y ≥ (Im ζ)⁻¹`, `Zb ≥ |ζ|`, `C₀` and the cutoff data; it is independent of `N`,
of every singular value of `𝓛`, of `J`, `𝔷`, `r`, `M` and `L_φ`. -/
theorem angular_comparison [Nonempty ι] (D : AngularData ι) {L : Matrix κ ι ℂ}
    (hL : ∀ x, L *ᵥ x = 0 → x = 0) {J : Matrix ι ι ℂ} (hJ : IsContraction J)
    {σ Y Zb : ℝ} (hs1 : D.s ≤ σ) (hs2 : D.s⁻¹ ≤ σ) (hY : D.ζ.im⁻¹ ≤ Y) (hZb : ‖D.ζ‖ ≤ Zb)
    (X : Cutoff) {Zf : (ι → ℂ) → ℝ} (hZm : Measurable Zf) (hZi : IsScaleInvariant Zf)
    (hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0}) (hZ0 : ∀ v, 0 ≤ Zf v)
    {C₀ r : ℝ} (hC₀ : 0 ≤ C₀) (hr : 0 ≤ r)
    (hFM : ∀ w : ι → ℂ, ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι ≤
      C₀ * ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r) / Fintype.card ι *
        (star w ⬝ᵥ (D.Γ *ᵥ w)).re)
    {Φ : (ι → ℂ) → ℝ} {M Lφ : ℝ} (hM : ∀ v, v ≠ 0 → |Φ v| ≤ M) (hLφ : 0 ≤ Lφ)
    (hlip : ReconLip L Φ Lφ) :
    |∫ v, Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (quadQuot J v - D.jStar J) * Φ v)
        ∂projectiveHaar ι| ≤
      compConst σ Y Zb C₀ X * (M + Lφ) / Fintype.card ι *
        ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r +
          ∫ v, Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v ∂projectiveHaar ι) := by
  set f : (ι → ℂ) → ℝ := fun v =>
    Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) * (quadQuot J v - D.jStar J)) with hfdef
  have hform : ∀ Ψ : (ι → ℂ) → ℝ, (∫ v, Real.exp (D.expo v) * Zf v *
      (X.χ (D.b₂ v) * (quadQuot J v - D.jStar J) * Ψ v) ∂projectiveHaar ι) =
      ∫ v, f v * Ψ v ∂projectiveHaar ι := fun Ψ =>
    integral_congr_ae (ae_of_all _ fun v => by simp only [hfdef]; ring)
  have hM0 : 0 ≤ M := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have hne : (Pi.single i (1 : ℂ) : ι → ℂ) ≠ 0 := Function.ne_iff.2 ⟨i, by simp⟩
    exact (abs_nonneg _).trans (hM _ hne)
  have hEc : ContinuousOn (fun v => Real.exp (D.expo v)) {z | z ≠ 0} :=
    Real.continuous_exp.comp_continuousOn D.expo_c1.continuousOn
  have hfc : ContinuousOn f {z | z ≠ 0} :=
    (hEc.mul hZc.continuousOn).mul ((X.smooth.continuous.comp_continuousOn
      (b₂_c1 D).continuousOn).mul ((contDiffOn_quadQuot J).continuousOn.sub continuousOn_const))
  obtain ⟨g, hg, -, hΦg⟩ := reconLip_factor hM0 hM hLφ hlip
  have hΦc : ContinuousOn Φ {z | z ≠ 0} :=
    (hg.continuous.comp_continuousOn (toLp_recon_c1 hL).continuousOn).congr fun v hv => hΦg v hv
  have iΦ : Integrable (fun v => f v * Φ v) (projectiveHaar ι) :=
    integrable_of_continuousOn (hfc.mul hΦc)
  have iA : Integrable (fun v => |f v|) (projectiveHaar ι) := integrable_of_continuousOn hfc.abs
  set A := ∫ v, |f v| ∂projectiveHaar ι with hA
  have hA0 : 0 ≤ A := integral_nonneg fun v => abs_nonneg _
  rw [hform Φ]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (A + 1) := div_pos hε (by linarith)
  obtain ⟨Ψ, hΨc, hΨM, hΨl, hΨa⟩ := exists_C1_approx hL hM0 hM hLφ hlip hδ
  have h1 := angular_comparison_C1 D hL hJ hs1 hs2 hY hZb X hZm hZi hZc hZ0 hC₀ hr hFM hΨc
    hΨM hLφ hΨl
  rw [hform Ψ] at h1
  have iΨ : Integrable (fun v => f v * Ψ v) (projectiveHaar ι) :=
    integrable_of_continuousOn (hfc.mul hΨc.continuousOn)
  have h2 : |(∫ v, f v * Φ v ∂projectiveHaar ι) - ∫ v, f v * Ψ v ∂projectiveHaar ι| ≤ ε := by
    rw [← integral_sub iΦ iΨ]
    refine (abs_integral_le_of_pw (iA.mul_const (ε / (A + 1))) fun v hv => ?_).trans ?_
    · rw [← mul_sub, abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (hΨa v (ne_zero_of_unit hv)) (abs_nonneg _)
    · rw [integral_mul_const, ← hA, ← mul_div_assoc, div_le_iff₀ (by linarith)]
      nlinarith
  have h3 := abs_sub_abs_le_abs_sub (∫ v, f v * Φ v ∂projectiveHaar ι)
    (∫ v, f v * Ψ v ∂projectiveHaar ι)
  linarith

end BlockBand.Angular.Ratio
