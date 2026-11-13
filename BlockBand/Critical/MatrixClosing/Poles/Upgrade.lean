module

public import BlockBand.Critical.MatrixClosing.Poles.Laplace
public import BlockBand.Critical.MatrixClosing.Poles.Smooth
public import BlockBand.Critical.MatrixClosing.Poles.Compare

/-!
# The decorated clause for continuous tests and a perturbed unfolding scale

* `DecoratedContinuousClause`: the decorated clause of the relative mixed vectors theorem with the test
  class enlarged to all nonnegative `f ∈ C_c(ℝ × ℂ^r)` and the unfolding density `ρ_F` replaced by
  any `ρ` with `|ρ - ρ_F| ≤ ε` (same law: `G ~ GUE_N(c/N)`, uniform phases, marks
  `√N e^{iθ_ℓ}V^*u_ℓ`; same quantifiers and uniformity as `RelativeMixedVectorsDecorated`: `f`, `δ`
  fixed, then `ε, N₀` uniform over `N ≥ N₀`, `F ∈ FreshClass`, frames with `|(V^*ΓV - I)_{ij}| ≤ ε`).
* **`decoratedContinuous_of_decorated : RelativeMixedVectorsDecorated → DecoratedContinuousClause`.**
  Proof: rescaling `Nρ(λ - E) = (ρ/ρ_F)·Nρ_F(λ - E)` (`markedIntegrand_rescale`, `ρ_F ≥ v₀/π`);
  smooth approximation `ψ` of `f`; the clause for `ψ` and for the count test `t β_R` (count tail);
  sup-norm comparison on both sides.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.RelativeVectors
open BlockBand.Internal.Contracts.CriticalEntire
open scoped NNReal

variable {N r : ℕ}

/-!
## Rescaling the unfolding scale
-/

/-- The rescaled test `(x, z) ↦ f(s x, z)`. -/
def rescaleTest (f : ℝ × (Fin r → ℂ) → ℝ) (s : ℝ) : ℝ × (Fin r → ℂ) → ℝ :=
  fun p => f (s * p.1, p.2)

theorem markedIntegrand_rescale (f : ℝ × (Fin r → ℂ) → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (ρ' E : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    markedIntegrand ρ' E V f K = markedIntegrand ρ E V (rescaleTest f (ρ' / ρ)) K := by
  unfold markedIntegrand rescaleTest
  congr 1
  funext θ
  congr 2
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 2
  field_simp

theorem continuous_rescaleTest {f : ℝ × (Fin r → ℂ) → ℝ} (hf : Continuous f) (s : ℝ) :
    Continuous (rescaleTest f s) :=
  hf.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)

theorem rescaleTest_eq_zero {f : ℝ × (Fin r → ℂ) → ℝ} {R : ℝ} (hR0 : 0 ≤ R)
    (hfR : ∀ x z, R < |x| → f (x, z) = 0) {s : ℝ} (hs : |s - 1| ≤ 1 / 2) (x : ℝ)
    (z : Fin r → ℂ) (hx : 2 * R < |x|) : rescaleTest f s (x, z) = 0 := by
  refine hfR _ _ ?_
  have hs1 : 1 / 2 ≤ s := by linarith [(abs_le.1 hs).1]
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s)]
  have hx0 : 0 ≤ |x| := abs_nonneg x
  nlinarith

/-- **Uniform closeness of rescaled tests.** -/
theorem exists_rescale_close (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) {R : ℝ}
    (hR0 : 0 ≤ R) (hfR : ∀ x z, R < |x| → f (x, z) = 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ s : ℝ, |s - 1| ≤ ε → ∀ p, |rescaleTest f s p - f p| ≤ η := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1
    (f.hasCompactSupport.uniformContinuous_of_continuous f.continuous) η hη
  have hA : 0 < 2 * (2 * R + 1) := by positivity
  refine ⟨min (1 / 2) (δ / (2 * (2 * R + 1))), lt_min (by norm_num) (div_pos hδ hA),
    min_le_left _ _, fun s hs p => ?_⟩
  obtain ⟨x, z⟩ := p
  have hs2 : |s - 1| ≤ 1 / 2 := hs.trans (min_le_left _ _)
  by_cases hx : 2 * R < |x|
  · rw [rescaleTest_eq_zero hR0 hfR hs2 x z hx, hfR x z (by linarith), sub_zero, abs_zero]
    exact hη.le
  · push Not at hx
    have hd : dist (s * x, z) (x, z) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      have h1 : |s * x - x| = |s - 1| * |x| := by rw [← abs_mul]; ring_nf
      have h2 : |s - 1| * |x| ≤ δ / (2 * (2 * R + 1)) * (2 * R) :=
        mul_le_mul (hs.trans (min_le_right _ _)) hx (abs_nonneg _) (div_pos hδ hA).le
      have h3 : δ / (2 * (2 * R + 1)) * (2 * R) < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hA]
        nlinarith
      rw [max_eq_left (abs_nonneg _)]
      linarith
    have := hδf hd
    rw [Real.dist_eq] at this
    exact this.le

/-!
## The unfolding density under regularity
-/

theorem unfoldingDensity_ge {F : Matrix (Fin N) (Fin N) ℂ} {A c E r₀ s₀ v₀ : ℝ}
    (hFC : FreshConstants c r₀ s₀ v₀) (hF : FreshClass F A c E r₀ s₀ v₀) :
    v₀ / Real.pi ≤ unfoldingDensity F c E := by
  obtain ⟨hc, -, hr₀, hs₀, -, -⟩ := hFC
  have h := (hF.2.2 c ⟨by linarith, le_rfl⟩ E (by simp [hr₀.le]) 0 ⟨le_rfl, zero_le_one⟩).1
  unfold unfoldingDensity
  exact div_le_div_of_nonneg_right h Real.pi_pos.le

/-!
## The enlarged decorated clause
-/

/-- **The decorated clause for continuous tests and a perturbed unfolding scale.** Law:
`G ~ GUE_N(c/N)` and uniform phases; points `x_ℓ = Nρ(λ_ℓ(F + G) - E)`, marks
`√N e^{iθ_ℓ}V^*u_ℓ`. Tests: every nonnegative `f ∈ C_c(ℝ × ℂ^r)`. The unfolding density `ρ` is
any real within `ε` of `ρ_F = π⁻¹ Im m_{F,c}(E)`. Quantifiers as in
`RelativeMixedVectorsDecorated`. -/
def DecoratedContinuousClause : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
  ∀ (r : ℕ) (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ), (∀ p, 0 ≤ f p) →
  ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
  ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
  ∀ V : Matrix (Fin N) (Fin r) ℂ,
    (∀ i j : Fin r, ‖(Vᴴ * freshGamma F c E * V - (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤ ε) →
  ∀ ρ : ℝ, |ρ - unfoldingDensity F c E| ≤ ε →
    |∫ G, markedIntegrand ρ E V f (F + G) ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) -
      decoratedSineLaplace r f| ≤ δ

/-- **The decorated clause gives its enlarged form.** -/
theorem decoratedContinuous_of_decorated (hD : RelativeMixedVectorsDecorated) :
    DecoratedContinuousClause := by
  intro A c r₀ s₀ v₀ hFC r f hf δ hδ
  obtain ⟨R, hR0, hfR, hsmooth⟩ := exists_smooth_approx f hf
  set R₁ := 2 * R + 1 with hR₁
  -- the count test
  obtain ⟨t, ht, htL⟩ := exists_markedSineLaplace_countTest (r := r) R₁
    (show (0 : ℝ) < δ / 40 by positivity)
  set k : ℕ := ⌈2 / t⌉₊
  have hk : Real.exp (-(t * (k + 1))) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_two_le_half
    have h1 : 2 / t ≤ (k : ℝ) := Nat.le_ceil _
    have h2 : 2 ≤ t * k := by
      have := mul_le_mul_of_nonneg_left h1 ht.le
      rwa [mul_div_cancel₀ _ ht.ne'] at this
    nlinarith
  -- the sup tolerance
  set η := δ / (5 * (2 * k + 2 * R + 3)) with hηdef
  have hden : 0 < 5 * (2 * (k : ℝ) + 2 * R + 3) := by positivity
  have hη : 0 < η := div_pos hδ hden
  have hηb : η * (2 * k + 2 * R + 2) ≤ δ / 5 := by
    rw [hηdef, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 5)]
    nlinarith
  obtain ⟨ψ, hψd, hψ0, hψf, hψR⟩ := hsmooth η hη
  obtain ⟨Kψ, hKψ⟩ := isDecoratedTest_of_smooth (r := r) hψd ψ.hasCompactSupport hψ0 hψR
  obtain ⟨εs, hεs, hεs2, hres⟩ := exists_rescale_close f hR0 hfR hη
  -- the clause for `ψ` and for the count test
  obtain ⟨ε₁, hε₁, N₁, h₁⟩ := hD A c r₀ s₀ v₀ hFC r R Kψ ψ hKψ (δ / 5) (by positivity)
  obtain ⟨ε₂, hε₂, N₂, h₂⟩ := hD A c r₀ s₀ v₀ hFC r (R₁ + 1) t (countTest R₁ t)
    (isDecoratedTest_countTest R₁ ht.le) (δ / 40) (by positivity)
  have hv₀ : 0 < v₀ := hFC.2.2.2.2.2
  set ε := min ε₁ (min ε₂ (εs * v₀ / Real.pi))
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₂ (by positivity))
  refine ⟨ε, hε, max N₁ N₂, fun N hN F E hF V hV ρ hρ => ?_⟩
  have : IsProbabilityMeasure (gueMeasure (Fin N) (Real.toNNReal (c / N))) := inferInstance
  set ν := gueMeasure (Fin N) (Real.toNNReal (c / N)) with hνdef
  set ρF := unfoldingDensity F c E with hρFdef
  have hρF : v₀ / Real.pi ≤ ρF := unfoldingDensity_ge hFC hF
  have hρFpos : 0 < ρF := lt_of_lt_of_le (by positivity) hρF
  set s := ρ / ρF
  have hs : |s - 1| ≤ εs := by
    have e : s - 1 = (ρ - ρF) / ρF := by simp only [s]; field_simp
    rw [e, abs_div, abs_of_pos hρFpos, div_le_iff₀ hρFpos]
    have h1 : |ρ - ρF| ≤ εs * v₀ / Real.pi := hρ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : εs * v₀ / Real.pi = εs * (v₀ / Real.pi) := by ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hρF hεs.le)
  have hs2 : |s - 1| ≤ 1 / 2 := hs.trans hεs2
  have hV₁ : ∀ i j : Fin r, ‖(Vᴴ * freshGamma F c E * V - (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤ ε₁ := fun i j =>
    (hV i j).trans (min_le_left _ _)
  have hV₂ : ∀ i j : Fin r, ‖(Vᴴ * freshGamma F c E * V - (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤ ε₂ := fun i j =>
    (hV i j).trans ((min_le_right _ _).trans (min_le_left _ _))
  have c1 := h₁ N (le_of_max_le_left hN) F E hF V hV₁
  have c2 := h₂ N (le_of_max_le_right hN) F E hF V hV₂
  rw [markedLaplace_eq, ← hρFdef, ← hνdef] at c1 c2
  -- rescaling
  have e1 : ∫ G, markedIntegrand ρ E V f (F + G) ∂ν =
      ∫ G, markedIntegrand ρF E V (rescaleTest f s) (F + G) ∂ν := by
    congr 1
    funext G
    exact markedIntegrand_rescale f hρFpos.ne' ρ E V (F + G)
  -- count tail
  have hcount := measureReal_windowCard_le ν F ρF E R₁ V ht.le hk
  have hcount' : ν.real {G | k < (windowSet ρF E R₁ (F + G)).card} ≤ δ / 10 := by
    rw [abs_le] at c2
    linarith [c2.1]
  -- finite comparison
  have hfs0 : ∀ q, 0 ≤ rescaleTest f s q := fun q => hf _
  have hfsψ : ∀ q, |rescaleTest f s q - ψ q| ≤ 2 * η := by
    intro q
    have h1 := hres s hs q
    have h2 := hψf q
    calc |rescaleTest f s q - ψ q| = |(rescaleTest f s q - f q) - (ψ q - f q)| := by ring_nf
      _ ≤ |rescaleTest f s q - f q| + |ψ q - f q| := abs_sub _ _
      _ ≤ 2 * η := by linarith
  have hfsR : ∀ x z, R₁ < |x| → rescaleTest f s (x, z) = 0 := fun x z hx =>
    rescaleTest_eq_zero hR0 hfR hs2 x z (by linarith)
  have hψR₁ : ∀ x z, R₁ < |x| → ψ (x, z) = 0 := fun x z hx => hψR x z (by linarith)
  have hcmp := abs_integral_markedIntegrand_sub_le (f := rescaleTest (⇑f) s) (g := ⇑ψ) ν F ρF E V
    (continuous_rescaleTest f.continuous s) ψ.continuous hfs0 hψ0 (by positivity : (0 : ℝ) ≤ 2 * η)
    hfsψ hfsR hψR₁ k
  -- sine comparison
  have hsine := abs_decoratedSineLaplace_sub_le ψ f hψ0 hf hη hR0 hψf hψR hfR
  have hm : markedSineLaplace r ψ = decoratedSineLaplace r ψ := rfl
  rw [hm] at c1
  rw [e1]
  have htot : |∫ G, markedIntegrand ρF E V (rescaleTest f s) (F + G) ∂ν -
      decoratedSineLaplace r f| ≤ (2 * η * k + δ / 10) + δ / 5 + η * (2 * R + 2) := by
    have := abs_sub_le (∫ G, markedIntegrand ρF E V (rescaleTest f s) (F + G) ∂ν)
      (∫ G, markedIntegrand ρF E V ψ (F + G) ∂ν) (decoratedSineLaplace r ψ)
    have h2 := abs_sub_le (∫ G, markedIntegrand ρF E V (rescaleTest f s) (F + G) ∂ν)
      (decoratedSineLaplace r ψ) (decoratedSineLaplace r f)
    linarith
  have : 2 * η * k + η * (2 * R + 2) ≤ δ / 5 := by nlinarith
  linarith

end BlockBand.Critical.MatrixClosing.Poles
