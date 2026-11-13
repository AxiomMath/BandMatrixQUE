module

public import BlockBand.DeterminantScore.SpectralConvexityVariance
public import BlockBand.DeterminantScore.NegativeSpreadPrekopa

/-!
# Brascamp–Lieb via Prékopa: the second-order estimate

The Brascamp–Lieb inequality from Prékopa's theorem (`BlockBand.External.Prekopa.SourceContract`,
the explicit hypothesis `hP`).

## Statements

* `variance_le_of_mgf_prod_le_one`: on a probability space, if `X, Y` are a.e. bounded and
  `E[e^{tX - t²Y/2}] · E[e^{-tX - t²Y/2}] ≤ 1` for all `0 < t < t₀`, then `Var X ≤ E Y`
  (third-order Taylor bound for `exp`, explicit constants).
* `variance_le_of_convexOn_tilt` (uses `hP`): let `D ⊆ ℝ^m` be measurable (convexity is part
  of the joint-convexity hypothesis),
  `gibbsOn D 𝒰` a probability measure, `f, φ` measurable and bounded by `C` on `D`. If
  `W(t, x) = 𝒰(x) - t f(x) + t² φ(x)/2` is jointly convex on `(-t₀, t₀) × D`, then
  `Var f ≤ ∫ φ` under `gibbsOn D 𝒰`. (Prékopa: `t ↦ ∫_D e^{-W(t,x)} dx` is log-concave, so
  `Z(t) Z(-t) ≤ Z(0)² = 1`.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Third-order lower bound for `exp` on `[-1, 1]`. -/
theorem one_add_add_sq_sub_le_exp {s : ℝ} (hs : |s| ≤ 1) :
    1 + s + s ^ 2 / 2 - |s| ^ 3 ≤ Real.exp s := by
  have h := Real.exp_bound hs (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have h3 : 0 ≤ |s| ^ 3 := by positivity
  have := (abs_le.1 h).1
  nlinarith

/-- Pointwise expansion of `exp(σ t x - t² y / 2)`. -/
theorem exp_expand_le {C t σ x y : ℝ} (hC : 0 ≤ C) (ht : 0 < t) (ht1 : t ≤ 1)
    (htC : 2 * t * C ≤ 1) (hσ : σ ^ 2 = 1) (hx : |x| ≤ C) (hy : |y| ≤ C) :
    1 + σ * t * x + t ^ 2 / 2 * (x ^ 2 - y) - (C ^ 2 / 2 + 8 * C ^ 3) * t ^ 3 ≤
      Real.exp (σ * t * x - t ^ 2 / 2 * y) := by
  set s := σ * t * x - t ^ 2 / 2 * y with hsdef
  have hσa : |σ| = 1 := by
    have : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσ
    nlinarith [abs_nonneg σ]
  have hs2 : |s| ≤ 2 * t * C := by
    calc |s| ≤ |σ * t * x| + |t ^ 2 / 2 * y| := abs_sub _ _
      _ = t * |x| + t ^ 2 / 2 * |y| := by
          rw [abs_mul, abs_mul, hσa, abs_of_pos ht,
            abs_mul (t ^ 2 / 2), abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)]
          ring
      _ ≤ t * C + t ^ 2 / 2 * C := by gcongr
      _ ≤ 2 * t * C := by
          have h1 : t ^ 2 ≤ t := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right h1 hC]
  have hs1 : |s| ≤ 1 := hs2.trans htC
  have hcube : |s| ^ 3 ≤ 8 * C ^ 3 * t ^ 3 := by
    calc |s| ^ 3 ≤ (2 * t * C) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hs2 3
      _ = 8 * C ^ 3 * t ^ 3 := by ring
  have hxy : |x * y| ≤ C ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hx hy (abs_nonneg _) hC
  have hxy' : σ * (x * y) ≤ C ^ 2 := by
    have : |σ * (x * y)| ≤ C ^ 2 := by rw [abs_mul, hσa, one_mul]; exact hxy
    exact (abs_le.1 this).2
  have hsq : s ^ 2 = t ^ 2 * x ^ 2 - t ^ 3 * (σ * (x * y)) + t ^ 4 / 4 * y ^ 2 := by
    rw [hsdef]
    linear_combination t ^ 2 * x ^ 2 * hσ
  have hsq' : t ^ 2 * x ^ 2 - t ^ 3 * C ^ 2 ≤ s ^ 2 := by
    rw [hsq]
    have h4 : 0 ≤ t ^ 4 / 4 * y ^ 2 := by positivity
    have h3 : 0 < t ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hxy' h3.le]
  have key := one_add_add_sq_sub_le_exp hs1
  have ht3 : 0 < t ^ 3 := by positivity
  nlinarith

/-- If `a ≤ b t` for all small `t > 0`, then `a ≤ 0`. -/
theorem nonpos_of_le_mul {a b t₁ : ℝ} (ht₁ : 0 < t₁) (h : ∀ t, 0 < t → t ≤ t₁ → a ≤ b * t) :
    a ≤ 0 := by
  by_contra ha'
  have ha := not_le.1 ha'
  set t := min t₁ (a / (2 * (|b| + 1))) with htdef
  have hb1 : 0 < |b| + 1 := by positivity
  have htpos : 0 < t := lt_min ht₁ (by positivity)
  have h1 := h t htpos (min_le_left _ _)
  have h2 : t ≤ a / (2 * (|b| + 1)) := min_le_right _ _
  have h3 : b * t ≤ |b| * t := mul_le_mul_of_nonneg_right (le_abs_self b) htpos.le
  have h4 : (|b| + 1) * t ≤ a / 2 := by
    calc (|b| + 1) * t ≤ (|b| + 1) * (a / (2 * (|b| + 1))) :=
          mul_le_mul_of_nonneg_left h2 hb1.le
      _ = a / 2 := by field_simp
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
/-- **Second-order estimate.** If, for all small `t > 0`, `E[e^{tX - t²Y/2}] E[e^{-tX - t²Y/2}] ≤ 1`
with `X, Y` bounded, then `Var X ≤ E Y`. -/
theorem variance_le_of_mgf_prod_le_one {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) {C : ℝ}
    (hXC : ∀ᵐ ω ∂μ, |X ω| ≤ C) (hYC : ∀ᵐ ω ∂μ, |Y ω| ≤ C) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t, 0 < t → t < t₀ →
      (∫ ω, Real.exp (1 * t * X ω - t ^ 2 / 2 * Y ω) ∂μ) *
        (∫ ω, Real.exp ((-1) * t * X ω - t ^ 2 / 2 * Y ω) ∂μ) ≤ 1) :
    variance X μ ≤ ∫ ω, Y ω ∂μ := by
  have hC : 0 ≤ C := by
    obtain ⟨ω, hω⟩ := hXC.exists
    exact (abs_nonneg _).trans hω
  set K := C ^ 2 / 2 + 8 * C ^ 3 with hK
  have hK0 : 0 ≤ K := by positivity
  have hXi : Integrable X μ := Integrable.of_bound hX C (by simpa [Real.norm_eq_abs] using hXC)
  have hYi : Integrable Y μ := Integrable.of_bound hY C (by simpa [Real.norm_eq_abs] using hYC)
  have hX2 : MemLp X 2 μ := MemLp.of_bound hX C (by simpa [Real.norm_eq_abs] using hXC)
  have hX2i : Integrable (fun ω => X ω ^ 2) μ := by
    refine Integrable.of_bound (hX.pow 2) (C ^ 2) ?_
    filter_upwards [hXC] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  set A := ∫ ω, X ω ∂μ
  set B := ∫ ω, X ω ^ 2 ∂μ
  set P := ∫ ω, Y ω ∂μ
  have hA : |A| ≤ C := by
    calc |A| ≤ ∫ ω, |X ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ω, C ∂μ := integral_mono_ae hXi.abs (integrable_const C) hXC
      _ = C := by simp
  have hB0 : 0 ≤ B := integral_nonneg fun ω => sq_nonneg _
  have hB : B ≤ C ^ 2 := by
    calc B ≤ ∫ _ω, C ^ 2 ∂μ := by
          refine integral_mono_ae hX2i (integrable_const _) ?_
          filter_upwards [hXC] with ω hω
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      _ = C ^ 2 := by simp
  have hP : |P| ≤ C := by
    calc |P| ≤ ∫ ω, |Y ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ω, C ∂μ := integral_mono_ae hYi.abs (integrable_const C) hYC
      _ = C := by simp
  -- lower bound for each exponential moment
  have hlow : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ t, 0 < t → t ≤ 1 → 2 * t * C ≤ 1 →
      1 + σ * t * A + t ^ 2 / 2 * (B - P) - K * t ^ 3 ≤
        ∫ ω, Real.exp (σ * t * X ω - t ^ 2 / 2 * Y ω) ∂μ := by
    intro σ hσ t ht ht1 htC
    have hEi : Integrable (fun ω => Real.exp (σ * t * X ω - t ^ 2 / 2 * Y ω)) μ := by
      refine Integrable.of_bound ?_ (Real.exp (|σ * t| * C + t ^ 2 / 2 * C)) ?_
      · exact Real.continuous_exp.comp_aestronglyMeasurable
          (((hX.const_mul (σ * t))).sub (hY.const_mul (t ^ 2 / 2)))
      · filter_upwards [hXC, hYC] with ω hx hy
        rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
        have h1 : σ * t * X ω ≤ |σ * t| * C := by
          calc σ * t * X ω ≤ |σ * t * X ω| := le_abs_self _
            _ = |σ * t| * |X ω| := abs_mul _ _
            _ ≤ |σ * t| * C := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
        have h2 : -(t ^ 2 / 2 * Y ω) ≤ t ^ 2 / 2 * C := by
          have : -Y ω ≤ C := (neg_le_abs _).trans hy
          nlinarith [sq_nonneg t]
        linarith
    have hLi : Integrable (fun ω => (1 - K * t ^ 3) + (σ * t) * X ω +
        (t ^ 2 / 2) * X ω ^ 2 - (t ^ 2 / 2) * Y ω) μ :=
      (((integrable_const _).add (hXi.const_mul _)).add (hX2i.const_mul _)).sub
        (hYi.const_mul _)
    have hmono := integral_mono_ae hLi hEi (by
      filter_upwards [hXC, hYC] with ω hx hy
      have := exp_expand_le hC ht ht1 htC hσ hx hy
      rw [← hK] at this
      linarith)
    have hint : ∫ ω, ((1 - K * t ^ 3) + (σ * t) * X ω + (t ^ 2 / 2) * X ω ^ 2 -
        (t ^ 2 / 2) * Y ω) ∂μ = (1 - K * t ^ 3) + σ * t * A + t ^ 2 / 2 * B - t ^ 2 / 2 * P := by
      rw [integral_sub, integral_add, integral_add, integral_const, integral_const_mul,
        integral_const_mul, integral_const_mul]
      · simp [measureReal_def, A, B, P]
      · exact integrable_const _
      · exact hXi.const_mul _
      · exact (integrable_const _).add (hXi.const_mul _)
      · exact hX2i.const_mul _
      · exact ((integrable_const _).add (hXi.const_mul _)).add (hX2i.const_mul _)
      · exact hYi.const_mul _
    rw [hint] at hmono
    linarith
  have hmain : ∀ t, 0 < t → t ≤ min (t₀ / 2) (1 / (4 * (1 + C + C ^ 2 + K))) →
      B - A ^ 2 - P ≤ (2 * K) * t := by
    intro t ht htle
    have ht0 : t < t₀ := by
      have := (htle.trans (min_le_left _ _)); linarith
    have hden : 0 < 4 * (1 + C + C ^ 2 + K) := by positivity
    have htsmall : t * (4 * (1 + C + C ^ 2 + K)) ≤ 1 := by
      have := htle.trans (min_le_right _ _)
      rwa [le_div_iff₀ hden] at this
    have h1 := mul_nonneg ht.le hC
    have h2 := mul_nonneg ht.le hK0
    have h3 := mul_nonneg ht.le (sq_nonneg C)
    have hsum : t + t * C + t * C ^ 2 + t * K ≤ 1 / 4 := by linarith
    have htC' : t * C ≤ 1 / 4 := by linarith
    have htK : t * K ≤ 1 / 4 := by linarith
    have ht1 : t ≤ 1 := by linarith
    have htC : 2 * t * C ≤ 1 := by linarith
    have hp := hlow 1 (by norm_num) t ht ht1 htC
    have hm := hlow (-1) (by norm_num) t ht ht1 htC
    have hprod := h t ht ht0
    set Ep := ∫ ω, Real.exp (1 * t * X ω - t ^ 2 / 2 * Y ω) ∂μ
    set Em := ∫ ω, Real.exp ((-1) * t * X ω - t ^ 2 / 2 * Y ω) ∂μ
    set R := t ^ 2 / 2 * (B - P) - K * t ^ 3 with hRdef
    have hp' : 1 + t * A + R ≤ Ep := by rw [hRdef]; linarith
    have hm' : 1 - t * A + R ≤ Em := by rw [hRdef]; linarith
    have ht2 : t ^ 2 ≤ t := by nlinarith
    have ht3 : t ^ 3 ≤ t := by nlinarith
    have hR : -(1 / 2) ≤ R := by
      have hBP : -(C ^ 2 + C) ≤ B - P := by
        have := (abs_le.1 hP).2; linarith
      have h3 : t ^ 2 * (-(C ^ 2 + C)) ≤ t ^ 2 * (B - P) :=
        mul_le_mul_of_nonneg_left hBP (by positivity)
      have h4 : t ^ 2 * (C ^ 2 + C) ≤ t * (C ^ 2 + C) :=
        mul_le_mul_of_nonneg_right ht2 (by positivity)
      have h5 : K * t ^ 3 ≤ K * t := mul_le_mul_of_nonneg_left ht3 hK0
      rw [hRdef]
      nlinarith
    have htA : |t * A| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_pos ht]
      have := mul_le_mul_of_nonneg_left hA ht.le
      linarith
    have hLp : 0 ≤ 1 + t * A + R := by
      have := (abs_le.1 htA).1; linarith
    have hLm : 0 ≤ 1 - t * A + R := by
      have := (abs_le.1 htA).2; linarith
    have hprod' : (1 + t * A + R) * (1 - t * A + R) ≤ 1 :=
      le_trans (mul_le_mul hp' hm' hLm (hLp.trans hp')) hprod
    have hexp : (1 + t * A + R) * (1 - t * A + R) = 1 + 2 * R + R ^ 2 - t ^ 2 * A ^ 2 := by
      ring
    rw [hexp] at hprod'
    have h2R : 2 * R - t ^ 2 * A ^ 2 ≤ 0 := by nlinarith [sq_nonneg R]
    have key : t ^ 2 * (B - A ^ 2 - P) ≤ t ^ 2 * (2 * K * t) := by
      have e : 2 * R - t ^ 2 * A ^ 2 = t ^ 2 * (B - A ^ 2 - P) - t ^ 2 * (2 * K * t) := by
        rw [hRdef]; ring
      linarith
    exact le_of_mul_le_mul_left key (by positivity)
  have ht1pos : 0 < min (t₀ / 2) (1 / (4 * (1 + C + C ^ 2 + K))) :=
    lt_min (by linarith) (by positivity)
  have hfin := nonpos_of_le_mul ht1pos hmain
  rw [variance_eq_sub hX2]
  have : μ[X ^ 2] = B := rfl
  rw [this]
  linarith

/-- `gibbsOn D 𝒰` is carried by `D`. -/
theorem ae_mem_gibbsOn {m : ℕ} {D : Set (Fin m → ℝ)} (hDm : MeasurableSet D)
    (𝒰 : (Fin m → ℝ) → ℝ) : ∀ᵐ x ∂gibbsOn D 𝒰, x ∈ D :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hDm)

/-- Integral against `gibbsOn D 𝒰` as a set integral with density. -/
theorem lintegral_gibbsOn {m : ℕ} {D : Set (Fin m → ℝ)} (hDm : MeasurableSet D)
    {𝒰 : (Fin m → ℝ) → ℝ} (h𝒰 : Measurable 𝒰) {g : (Fin m → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂gibbsOn D 𝒰 =
      ∫⁻ x, D.indicator (fun x => ENNReal.ofReal (Real.exp (-𝒰 x)) * g x) x := by
  have hd : Measurable fun x => ENNReal.ofReal (Real.exp (-𝒰 x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h𝒰.neg)
  rw [gibbsOn, lintegral_withDensity_eq_lintegral_mul _ hd hg, lintegral_indicator hDm]
  rfl

/-- **Brascamp–Lieb from a jointly convex tilt.** If `W(t,x) = 𝒰(x) - t f(x) + t² φ(x)/2`
is jointly convex on `(-t₀, t₀) × D`, then `Var f ≤ ∫ φ` under `gibbsOn D 𝒰`. -/
theorem variance_le_of_convexOn_tilt (hP : BlockBand.External.Prekopa.SourceContract)
    {m : ℕ} {D : Set (Fin m → ℝ)} (hDm : MeasurableSet D)
    {𝒰 f φ : (Fin m → ℝ) → ℝ} (h𝒰 : Measurable 𝒰) (hf : Measurable f) (hφ : Measurable φ)
    {C : ℝ} (hfC : ∀ x ∈ D, |f x| ≤ C) (hφC : ∀ x ∈ D, |φ x| ≤ C)
    (hprob : IsProbabilityMeasure (gibbsOn D 𝒰)) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hW : ConvexOn ℝ (Set.Ioo (-t₀) t₀ ×ˢ D)
      (fun p : ℝ × (Fin m → ℝ) => 𝒰 p.2 - p.1 * f p.2 + p.1 ^ 2 / 2 * φ p.2)) :
    variance f (gibbsOn D 𝒰) ≤ ∫ x, φ x ∂gibbsOn D 𝒰 := by
  classical
  set μ := gibbsOn D 𝒰 with hμ
  have hae := ae_mem_gibbsOn hDm 𝒰
  have hfC' : ∀ᵐ x ∂μ, |f x| ≤ C := hae.mono hfC
  have hφC' : ∀ᵐ x ∂μ, |φ x| ≤ C := hae.mono hφC
  set W : ℝ × (Fin m → ℝ) → ℝ := fun p => 𝒰 p.2 - p.1 * f p.2 + p.1 ^ 2 / 2 * φ p.2
    with hWdef
  set F : (Fin 1 → ℝ) × (Fin m → ℝ) → ℝ≥0 := fun z =>
    if z.1 0 ∈ Set.Ioo (-t₀) t₀ ∧ z.2 ∈ D then Real.toNNReal (Real.exp (-W (z.1 0, z.2)))
    else 0 with hFdef
  have hFcoe : ∀ z, (F z : ℝ≥0∞) = if z.1 0 ∈ Set.Ioo (-t₀) t₀ ∧ z.2 ∈ D then
      ENNReal.ofReal (Real.exp (-W (z.1 0, z.2))) else 0 := by
    intro z
    simp only [hFdef]
    split_ifs <;> rfl
  have hF : BlockBand.External.Prekopa.JointLogConcave 1 m F := by
    intro z w a ha ha1
    have hb : 0 < 1 - a := by linarith
    simp only [hFcoe]
    by_cases hz : z.1 0 ∈ Set.Ioo (-t₀) t₀ ∧ z.2 ∈ D
    · by_cases hw : w.1 0 ∈ Set.Ioo (-t₀) t₀ ∧ w.2 ∈ D
      · have hc1 : (a • z + (1 - a) • w).1 0 = a * z.1 0 + (1 - a) * w.1 0 := rfl
        have hc2 : (a • z + (1 - a) • w).2 = a • z.2 + (1 - a) • w.2 := rfl
        have hpz : (z.1 0, z.2) ∈ Set.Ioo (-t₀) t₀ ×ˢ D := ⟨hz.1, hz.2⟩
        have hpw : (w.1 0, w.2) ∈ Set.Ioo (-t₀) t₀ ×ˢ D := ⟨hw.1, hw.2⟩
        have hmem := hW.1 hpz hpw ha.le hb.le (by ring)
        have hpair : a • (z.1 0, z.2) + (1 - a) • (w.1 0, w.2) =
            ((a • z + (1 - a) • w).1 0, (a • z + (1 - a) • w).2) := by
          rw [hc1, hc2]
          rfl
        rw [hpair] at hmem
        have hconv := hW.2 hpz hpw ha.le hb.le (by ring)
        rw [hpair] at hconv
        rw [ite_eq_left hz, ite_eq_left hw, ite_eq_left ⟨hmem.1, hmem.2⟩,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ha.le,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hb.le,
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
        simp only [smul_eq_mul] at hconv
        linarith
      · rw [ite_eq_right hw, ENNReal.zero_rpow_of_pos hb, mul_zero]
        exact bot_le
    · rw [ite_eq_right hz, ENNReal.zero_rpow_of_pos ha, zero_mul]
      exact bot_le
  have hLC := hP.theorem6 1 m F Set.univ hF convex_univ
  -- integrability of the tilted densities
  have hEi : ∀ τ : ℝ, Integrable (fun x => Real.exp (τ * f x - τ ^ 2 / 2 * φ x)) μ := by
    intro τ
    refine Integrable.of_bound ?_ (Real.exp (|τ| * C + τ ^ 2 / 2 * C)) ?_
    · exact (Real.measurable_exp.comp ((hf.const_mul τ).sub
        (hφ.const_mul (τ ^ 2 / 2)))).aestronglyMeasurable
    · filter_upwards [hfC', hφC'] with x hx hy
      rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
      have h1 : τ * f x ≤ |τ| * C := by
        calc τ * f x ≤ |τ * f x| := le_abs_self _
          _ = |τ| * |f x| := abs_mul _ _
          _ ≤ |τ| * C := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      have h2 : -(τ ^ 2 / 2 * φ x) ≤ τ ^ 2 / 2 * C := by
        have : -φ x ≤ C := (neg_le_abs _).trans hy
        nlinarith [sq_nonneg τ]
      linarith
  -- the marginal is the tilted exponential moment
  have hmarg : ∀ s : Fin 1 → ℝ, s 0 ∈ Set.Ioo (-t₀) t₀ →
      BlockBand.External.Prekopa.marginal F Set.univ s =
        ENNReal.ofReal (∫ x, Real.exp (s 0 * f x - s 0 ^ 2 / 2 * φ x) ∂μ) := by
    intro s hs
    have hpt : ∀ y, (F (s, y) : ℝ≥0∞) = D.indicator (fun y => ENNReal.ofReal
        (Real.exp (-𝒰 y)) * ENNReal.ofReal (Real.exp (s 0 * f y - s 0 ^ 2 / 2 * φ y))) y := by
      intro y
      rw [hFcoe]
      by_cases hy : y ∈ D
      · rw [ite_eq_left ⟨hs, hy⟩, Set.indicator_of_mem hy, ← ENNReal.ofReal_mul
          (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        simp only [hWdef]
        ring
      · rw [ite_eq_right (fun h => hy h.2), Set.indicator_of_notMem hy]
    have hgm : Measurable fun y => ENNReal.ofReal (Real.exp (s 0 * f y - s 0 ^ 2 / 2 * φ y)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hf.const_mul _).sub
        (hφ.const_mul _)))
    have hmeas : Measurable fun y : Fin m → ℝ => (F (s, y) : ℝ≥0∞) := by
      simp only [hpt]
      exact (((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h𝒰.neg)).mul
        hgm)).indicator hDm
    have hm1 : BlockBand.External.Prekopa.marginal F Set.univ s =
        ∫⁻ y : NullMeasurableSpace (Fin m → ℝ) (volume : Measure (Fin m → ℝ)),
          (F (s, y) : ℝ≥0∞) ∂(volume : Measure (Fin m → ℝ)).completion := by
      unfold BlockBand.External.Prekopa.marginal
      exact lintegral_congr fun y => ite_eq_left (Set.mem_univ _)
    rw [hm1, NegativeSpread.lintegral_completion_eq volume hmeas, lintegral_congr hpt,
      ← lintegral_gibbsOn hDm h𝒰 hgm, ofReal_integral_eq_lintegral_ofReal (hEi _)
        (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  have hprod : ∀ t, 0 < t → t < t₀ →
      (∫ x, Real.exp (1 * t * f x - t ^ 2 / 2 * φ x) ∂μ) *
        (∫ x, Real.exp ((-1) * t * f x - t ^ 2 / 2 * φ x) ∂μ) ≤ 1 := by
    intro t ht ht'
    have hmem : ∀ τ : ℝ, |τ| ≤ t → (fun _ : Fin 1 => τ) 0 ∈ Set.Ioo (-t₀) t₀ := by
      intro τ hτ
      exact ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    have h := hLC (fun _ => t) (fun _ => -t) (1 / 2) (by norm_num) (by norm_num)
    have hmid : (1 / 2 : ℝ) • (fun _ : Fin 1 => t) + (1 - 1 / 2 : ℝ) • (fun _ : Fin 1 => -t) =
        fun _ => 0 := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hmid, hmarg _ (hmem t (abs_of_pos ht).le), hmarg _ (hmem (-t) (by rw [abs_neg,
      abs_of_pos ht])), hmarg _ (hmem 0 (by rw [abs_zero]; exact ht.le))] at h
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, sub_zero, Real.exp_zero, integral_const, probReal_univ,
      smul_eq_mul, mul_one, ENNReal.ofReal_one] at h
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← ENNReal.mul_rpow_of_nonneg _ _
      (by norm_num), ← ENNReal.ofReal_mul (integral_nonneg fun _ => (Real.exp_pos _).le),
      show (1 : ℝ≥0∞) = 1 ^ (1 / 2 : ℝ) by rw [ENNReal.one_rpow],
      ENNReal.rpow_le_rpow_iff (by norm_num), ENNReal.ofReal_le_one] at h
    convert h using 3
    · funext x; ring_nf
    · funext x; ring_nf
  exact variance_le_of_mgf_prod_le_one hf.aestronglyMeasurable hφ.aestronglyMeasurable
    hfC' hφC' ht₀ hprod

end BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb
