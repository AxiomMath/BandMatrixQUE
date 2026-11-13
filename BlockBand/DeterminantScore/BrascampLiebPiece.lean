module

public import BlockBand.DeterminantScore.BrascampLiebLocal

/-!
# Brascamp–Lieb on a convex piece with compact closure in the domain

`variance_le_piece` (uses the Prékopa input `hP`): let `D ⊆ ℝ^m` be open, `𝒰, f` be
`C²` on `D` with `f` measurable, `w > 0` on `D` with `Σ_j w_j a_j² ≤ ∇²𝒰(x)[a,a]` on `D`, and
let `P` be open convex with `P ⊆ K ⊆ D`, `K` compact. If `gibbsOn P 𝒰` is a probability measure,
then `Var f ≤ E q` under `gibbsOn P 𝒰` for a measurable `q ≤ Σ_j (∂_j f)²/w_j` on `D` (the
measurable intermediate is kept because `w` itself need not be measurable). Proof: `q = sup_b (2∇f·b - ∇²𝒰[b,b])`
is continuous on `K`; a `C²` Stone–Weierstrass approximation `Φ ∈ [q + δ, q + 3δ]` makes
`𝒰 - t f + t²Φ/2` jointly convex on `(-t₀, t₀) × P` for small `t₀`; then
`variance_le_of_convexOn_tilt`; finally `δ → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {m : ℕ}

/-- The diagonal energy density. -/
def energyDensity (f : (Fin m → ℝ) → ℝ) (w : (Fin m → ℝ) → Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ j, (fderiv ℝ f x (Pi.single j 1)) ^ 2 / w x j

set_option maxHeartbeats 1000000 in
/-- **Brascamp–Lieb on a convex piece** (via Prékopa's theorem). -/
theorem variance_le_piece (hP : BlockBand.External.Prekopa.SourceContract)
    {D K P : Set (Fin m → ℝ)} (hDo : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (hPo : IsOpen P) (hPc : Convex ℝ P) (hPK : P ⊆ K)
    {𝒰 f : (Fin m → ℝ) → ℝ} (h𝒰 : ContDiffOn ℝ 2 𝒰 D) (hf : ContDiffOn ℝ 2 f D)
    (hfm : Measurable f) {w : (Fin m → ℝ) → Fin m → ℝ} (hw : ∀ x ∈ D, ∀ j, 0 < w x j)
    (hH : ∀ x ∈ D, ∀ a, ∑ j, w x j * a j ^ 2 ≤ fderiv ℝ (fderiv ℝ 𝒰) x a a)
    (hprob : IsProbabilityMeasure (gibbsOn P 𝒰)) :
    ∃ q : (Fin m → ℝ) → ℝ, Measurable q ∧ (∀ x ∈ D, q x ≤ energyDensity f w x) ∧
      ENNReal.ofReal (variance f (gibbsOn P 𝒰)) ≤ ∫⁻ x, ENNReal.ofReal (q x) ∂gibbsOn P 𝒰 := by
  classical
  set μ := gibbsOn P 𝒰 with hμ
  have hPD : P ⊆ D := hPK.trans hKD
  have hae : ∀ᵐ x ∂μ, x ∈ P := ae_mem_gibbsOn hPo.measurableSet 𝒰
  -- a measurable version of `𝒰`
  set 𝒰' : (Fin m → ℝ) → ℝ := P.piecewise 𝒰 0 with h𝒰'def
  have h𝒰'm : Measurable 𝒰' := ContinuousOn.measurable_piecewise
    (h𝒰.continuousOn.mono hPD) continuousOn_const hPo.measurableSet
  have hμ' : gibbsOn P 𝒰' = μ := by
    rw [hμ, gibbsOn, gibbsOn]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hPo.measurableSet] with x hx
    rw [h𝒰'def, Set.piecewise_eq_of_mem _ _ _ hx]
  -- uniform constants on `K`
  obtain ⟨c, hc, hcoer⟩ := exists_coercive hDo hK hKD h𝒰 hw hH
  have hf1 : ContinuousOn (fderiv ℝ f) D := hf.continuousOn_fderiv_of_isOpen hDo (by norm_num)
  obtain ⟨G₀, hG₀⟩ := hK.exists_bound_of_continuousOn (hf1.mono hKD)
  set G := max G₀ 0 with hGdef
  have hG : 0 ≤ G := le_max_right _ _
  have hGK : ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ G := fun x hx => (hG₀ x hx).trans (le_max_left _ _)
  set R := 2 * G / c with hRdef
  have hR : 0 ≤ R := by positivity
  set q : (Fin m → ℝ) → ℝ := fun x => dualQ R (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ 𝒰) x)
    with hqdef
  have hqc : ContinuousOn q K :=
    (continuous_dualQ R).comp_continuousOn
      ((hf1.mono hKD).prodMk ((continuousOn_fderiv_fderiv hDo h𝒰).mono hKD))
  have hqm : Measurable q :=
    (continuous_dualQ R).measurable.comp
      ((measurable_fderiv ℝ f).prodMk (measurable_fderiv ℝ (fderiv ℝ 𝒰)))
  have hq0 : ∀ x, 0 ≤ q x := fun x => dualQ_nonneg hR _ _
  have hqE : ∀ x ∈ D, q x ≤ energyDensity f w x := fun x hx =>
    dualQ_le_energy hR _ _ (hw x hx) (hH x hx)
  have hqG : ∀ x ∈ K, q x ≤ G ^ 2 / c := fun x hx =>
    dualQ_le_sq_div hR hc _ _ (hcoer x hx) (hGK x hx)
  have hqi : Integrable q μ := Integrable.of_bound hqm.aestronglyMeasurable (G ^ 2 / c)
    (hae.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 x)]; exact hqG x (hPK hx))
  -- `f` is bounded on `K`
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKD)
  -- the main estimate for each `δ > 0`
  have hmain : ∀ δ : ℝ, 0 < δ → variance f μ ≤ ∫ x, q x ∂μ + 3 * δ := by
    intro δ hδ
    obtain ⟨F, hF, hFK⟩ := exists_contDiff_near hK hqc hδ
    set Φ : (Fin m → ℝ) → ℝ := fun x => F x + 2 * δ with hΦdef
    have hΦ : ContDiff ℝ 2 Φ := hF.add contDiff_const
    have hΦlo : ∀ x ∈ K, q x + δ ≤ Φ x := fun x hx => by
      have := (abs_lt.1 (hFK x hx)).1; simp only [hΦdef]; linarith
    have hΦhi : ∀ x ∈ K, Φ x ≤ q x + 3 * δ := fun x hx => by
      have := (abs_lt.1 (hFK x hx)).2; simp only [hΦdef]; linarith
    -- derivative bounds on `K`
    obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn
      (E := (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ)
      ((continuousOn_fderiv_fderiv hDo hf).mono hKD)
    obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn
      (hΦ.continuous_fderiv (by norm_num)).continuousOn
    obtain ⟨M₃, hM₃⟩ := hK.exists_bound_of_continuousOn
      (E := (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ)
      ((continuousOn_fderiv_fderiv isOpen_univ hΦ.contDiffOn).mono (Set.subset_univ K))
    set M := max M₁ 0 + max M₂ 0 + max M₃ 0 + 1 with hMdef
    have hMpos : 0 < M := by positivity
    have hM1 : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M := fun x hx => by
      have := hM₁ x hx; have := le_max_left M₁ 0
      have := le_max_right M₂ 0; have := le_max_right M₃ 0; linarith
    have hM2 : ∀ x ∈ K, ‖fderiv ℝ Φ x‖ ≤ M := fun x hx => by
      have := hM₂ x hx; have := le_max_left M₂ 0
      have := le_max_right M₁ 0; have := le_max_right M₃ 0; linarith
    have hM3 : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ M := fun x hx => by
      have := hM₃ x hx; have := le_max_left M₃ 0
      have := le_max_right M₁ 0; have := le_max_right M₂ 0; linarith
    set lam := min (1 / 2) (δ * c / (4 * (G ^ 2 + 1))) with hlamdef
    have hlam : 0 < lam := lt_min (by norm_num) (by positivity)
    have hlam2 : lam ≤ 1 / 2 := min_le_left _ _
    have hlamG : lam * (G ^ 2 / c) ≤ δ / 4 := by
      have h1 : lam ≤ δ * c / (4 * (G ^ 2 + 1)) := min_le_right _ _
      calc lam * (G ^ 2 / c) ≤ δ * c / (4 * (G ^ 2 + 1)) * (G ^ 2 / c) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = δ / 4 * (G ^ 2 / (G ^ 2 + 1)) := by field_simp
        _ ≤ δ / 4 * 1 := by
            gcongr
            rw [div_le_one (by positivity)]; linarith
        _ = δ / 4 := mul_one _
    set κ := min (δ / 8) (lam * c) with hκdef
    have hκ : 0 < κ := lt_min (by positivity) (by positivity)
    set t₀ := min 1 (κ / (4 * M)) with ht₀def
    have ht₀ : 0 < t₀ := lt_min one_pos (by positivity)
    have hpos : ∀ x ∈ P, ∀ T : ℝ, |T| < t₀ → ∀ (σ : ℝ) (u : Fin m → ℝ),
        0 ≤ fderiv ℝ (fderiv ℝ 𝒰) x u u - 2 * σ * fderiv ℝ f x u + σ ^ 2 * Φ x +
          T * (-fderiv ℝ (fderiv ℝ f) x u u + 2 * σ * fderiv ℝ Φ x u) +
          T ^ 2 / 2 * fderiv ℝ (fderiv ℝ Φ) x u u := by
      intro x hxP T hT σ u
      have hxK := hPK hxP
      have hT1 : |T| ≤ 1 := hT.le.trans (min_le_left _ _)
      have hTκ : |T| * (4 * M) ≤ κ := by
        have := hT.le.trans (min_le_right _ _)
        rwa [le_div_iff₀ (by positivity)] at this
      have e1 : |fderiv ℝ (fderiv ℝ f) x u u| ≤ M * ‖u‖ ^ 2 := by
        have h1 := (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ u u
        rw [Real.norm_eq_abs] at h1
        have h2 := mul_le_mul_of_nonneg_right (hM1 x hxK) (mul_nonneg (norm_nonneg u)
          (norm_nonneg u))
        linarith
      have e2 : |fderiv ℝ Φ x u| ≤ M * ‖u‖ := by
        have h1 := (fderiv ℝ Φ x).le_opNorm u
        rw [Real.norm_eq_abs] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right (hM2 x hxK) (norm_nonneg u))
      have e3 : |fderiv ℝ (fderiv ℝ Φ) x u u| ≤ M * ‖u‖ ^ 2 := by
        have h1 := (fderiv ℝ (fderiv ℝ Φ) x).le_opNorm₂ u u
        rw [Real.norm_eq_abs] at h1
        have h2 := mul_le_mul_of_nonneg_right (hM3 x hxK) (mul_nonneg (norm_nonneg u)
          (norm_nonneg u))
        linarith
      exact tilt_hessian_nonneg hlam hlam2 hδ (hcoer x hxK u)
        (fun s => dualQ_square hc hG (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ 𝒰) x) (hcoer x hxK)
          (hGK x hxK) u s) (hΦlo x hxK) (hqG x hxK) hlamG hMpos e1 e2 e3 hT1 hTκ
    have hW := convexOn_tilt hDo hPo hPc hPD h𝒰 hf hΦ.contDiffOn hpos
    have hW' : ConvexOn ℝ (Set.Ioo (-t₀) t₀ ×ˢ P)
        (fun p : ℝ × (Fin m → ℝ) => 𝒰' p.2 - p.1 * f p.2 + p.1 ^ 2 / 2 * Φ p.2) :=
      hW.congr fun p hp => by
        simp only [tilt, h𝒰'def, Set.piecewise_eq_of_mem _ _ _ hp.2]
    obtain ⟨CΦ, hCΦ⟩ := hK.exists_bound_of_continuousOn hΦ.continuous.continuousOn
    have hv := variance_le_of_convexOn_tilt hP hPo.measurableSet h𝒰'm hfm
      hΦ.continuous.measurable (C := max Cf CΦ)
      (fun x hx => by
        have := hCf x (hPK hx); rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_left _ _))
      (fun x hx => by
        have := hCΦ x (hPK hx); rw [Real.norm_eq_abs] at this
        exact this.trans (le_max_right _ _))
      (hμ' ▸ hprob) ht₀ hW'
    rw [hμ'] at hv
    have hΦi : Integrable Φ μ := Integrable.of_bound hΦ.continuous.measurable.aestronglyMeasurable
      CΦ (hae.mono fun x hx => hCΦ x (hPK hx))
    calc variance f μ ≤ ∫ x, Φ x ∂μ := hv
      _ ≤ ∫ x, (q x + 3 * δ) ∂μ :=
          integral_mono_ae hΦi (hqi.add (integrable_const _))
            (hae.mono fun x hx => hΦhi x (hPK hx))
      _ = ∫ x, q x ∂μ + 3 * δ := by
          rw [integral_add hqi (integrable_const _), integral_const, probReal_univ, one_smul]
  have hvq : variance f μ ≤ ∫ x, q x ∂μ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hmain (ε / 3) (by positivity)
    linarith
  refine ⟨q, hqm, hqE, ?_⟩
  calc ENNReal.ofReal (variance f μ) ≤ ENNReal.ofReal (∫ x, q x ∂μ) :=
        ENNReal.ofReal_le_ofReal hvq
    _ = ∫⁻ x, ENNReal.ofReal (q x) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hqi (Filter.Eventually.of_forall hq0)

end BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb
