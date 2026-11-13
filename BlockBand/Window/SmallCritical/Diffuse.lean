module

public import BlockBand.Window.SmallCritical.FourierPair

/-!
# The small-ratio critical theorem: diffuse clause

Almost surely every profile mark of a critical marked limit lies in `H^{-s}(𝕋)` for every
`s > 0` and has no atoms.

Proof. From the mode clause at `T = τ`: `v_m(P, w) ≤ C K |m|^{-(1-η)}`.
* `H^{-s}`: with `η < 2s`, `E_P Σ_α w(u_α) Σ_{m≠0} (1+4π²m²)^{-s}|ν̂_{α,m}|² < ∞` (Tonelli), so
  a.s. every mark in the window `{w > 0}` has finite `H^{-s}` norm; intersect over the
  countable family of windows `windowWeight R` and of exponents `s = 1/(k+1)`.
* atoms: the finite Wiener/Fejér inequality `fourier_pair_sum_ge` with frequency spacing `L`
  gives `ν({r})² - 1/L ≤ L⁻² Σ_{j≠k<L} |ν̂_{L(j-k)}|²`, whose window expectation is
  `≤ C K L^{-(1-η)} → 0`; Fatou (twice) shows the `liminf` vanishes a.s. at every atom of `ξ` in
  the window, hence `ν({r}) = 0` (Cesàro decay of `v_m` with Fatou).

Hypotheses: those of the mode clause (`WindowTransferContract`, `ModeBoundContract`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal NNReal

attribute [local instance] massProfile_opensMeasurableSpace

/-!
### Countably many spectral windows
-/

/-- Smooth bump centred at `0`, `= 1` on `[-(R+1), R+1]`, positive on `(-(R+2), R+2)`. -/
def windowBump (R : ℕ) : ContDiffBump (0 : ℝ) := ⟨R + 1, R + 2, by positivity, by linarith⟩

/-- The spectral weight `w_R = windowBump R / ∫ windowBump R`. -/
def windowWeight (R : ℕ) : SpectralWeight where
  toContinuousMap := ⟨(windowBump R).normed volume, (windowBump R).continuous_normed⟩
  smooth := (windowBump R).contDiff_normed
  compactSupport := (windowBump R).hasCompactSupport_normed
  nonnegative := fun x => (windowBump R).nonneg_normed x
  integral_eq_one := (windowBump R).integral_normed

theorem windowWeight_pos (R : ℕ) {u : ℝ} (hu : |u| < R + 2) : 0 < windowWeight R u := by
  change 0 < (windowBump R).normed volume u
  rw [ContDiffBump.normed_def]
  apply div_pos _ (windowBump R).integral_pos
  apply (windowBump R).pos_of_mem_ball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact hu

/-!
### Mark-side linearity of `Λ`
-/

theorem weightFunctional_markSum (P : ProbabilityMeasure MarkedPointMeasure) {ι : Type*}
    (s : Finset ι) (g : ι → MassProfile → ℝ) (hg : ∀ i, Continuous (g i))
    (hg0 : ∀ i ν, 0 ≤ g i ν) {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w)
    (hw0 : ∀ u, 0 ≤ w u) :
    weightFunctional P (fun ν => ∑ i ∈ s, g i ν) w = ∑ i ∈ s, weightFunctional P (g i) w := by
  unfold weightFunctional
  have hin : ∀ ξ : MarkedPointMeasure,
      ∫⁻ x, ENNReal.ofReal (w x.1 * ∑ i ∈ s, g i x.2) ∂ξ.marked.measure =
        ∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (w x.1 * g i x.2) ∂ξ.marked.measure := by
    intro ξ
    rw [← lintegral_finsetSum]
    · refine lintegral_congr fun x => ?_
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw0 _) (hg0 i _))]
    · intro i _
      exact ENNReal.measurable_ofReal.comp (continuous_prodTest hwc (hg i)).measurable
  simp_rw [hin]
  rw [lintegral_finsetSum]
  intro i _
  exact measurable_markedLIntegral (continuous_prodTest hwc (hg i))
    (hasCompactSupport_prodTest hws _) (prodTest_nonneg hw0 (hg0 i))

theorem weightFunctional_markConst (P : ProbabilityMeasure MarkedPointMeasure)
    (g : MassProfile → ℝ) (w : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    weightFunctional P (fun ν => c * g ν) w = ENNReal.ofReal c * weightFunctional P g w := by
  rw [← weightFunctional_const_mul P g w hc]
  unfold weightFunctional
  refine lintegral_congr fun ξ => lintegral_congr fun x => ?_
  ring_nf

theorem modeMark_zero (ν : MassProfile) : modeMark 0 ν = 1 := by
  unfold modeMark
  simp

/-!
### Power decay of the mode variances at fixed `τ`
-/

theorem mode_pow_bound (hWT : WindowTransferContract)
    (hMode : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      ModeBoundContract b θ T hb hb')
    {b : ℝ} {hb : 0 < b} {hb' : b < 1 / 2} {E : ℝ} (hE : E ^ 2 < 4) {τ : ℝ} (hτ : 0 < τ)
    {P : ProbabilityMeasure MarkedPointMeasure} (hP : IsCriticalMarkedLimit τ b E hb hb' P)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : SpectralWeight) (m : ℤ), m ≠ 0 →
      modeVariance P w m ≤
        ENNReal.ofReal (C * (τ + τ ^ (3 / 2 : ℝ)) ^ (1 - η) * |(m : ℝ)| ^ (-(1 - η))) := by
  obtain ⟨C, hC0, hC⟩ := smallCritical_mode hWT hMode b hb hb' E hE τ η hη hη1
  refine ⟨C, hC0, fun w m hm => (hC τ hτ le_rfl P hP w m hm).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hma : 0 < |(m : ℝ)| := abs_pos.mpr hmR
  have hm1 : 1 ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  have he : 0 ≤ 1 - η := by linarith
  have hτ32 : 0 ≤ τ ^ (3 / 2 : ℝ) := by positivity
  have hX : τ / |(m : ℝ)| + τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2 ≤ (τ + τ ^ (3 / 2 : ℝ)) / |(m : ℝ)| := by
    rw [add_div]
    have : τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2 ≤ τ ^ (3 / 2 : ℝ) / |(m : ℝ)| := by
      apply div_le_div_of_nonneg_left hτ32 hma
      rw [← sq_abs]; nlinarith
    linarith
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC0
  calc min 1 ((τ / |(m : ℝ)| + τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2) ^ (1 - η)) ≤
        (τ / |(m : ℝ)| + τ ^ (3 / 2 : ℝ) / (m : ℝ) ^ 2) ^ (1 - η) := min_le_right _ _
    _ ≤ ((τ + τ ^ (3 / 2 : ℝ)) / |(m : ℝ)|) ^ (1 - η) :=
        Real.rpow_le_rpow (by positivity) hX he
    _ = (τ + τ ^ (3 / 2 : ℝ)) ^ (1 - η) * |(m : ℝ)| ^ (-(1 - η)) := by
        rw [Real.div_rpow (by positivity) hma.le, Real.rpow_neg hma.le, div_eq_mul_inv]

/-!
### `H^{-s}` regularity in one window
-/

/-- `(1 + 4π²m²)^{-σ} ≤ |m|^{-2σ}` for `m ≠ 0`, `σ ≥ 0`. -/
theorem sobolevWeight_le {m : ℤ} (hm : m ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    (1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2) ^ (-σ) ≤ |(m : ℝ)| ^ (-(2 * σ)) := by
  have hma : 0 < |(m : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hm)
  have hle : |(m : ℝ)| ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2 := by
    rw [sq_abs]
    have : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg (m : ℝ)]
  rw [show -(2 * σ) = (2 : ℝ) * (-σ) by ring, Real.rpow_mul hma.le, Real.rpow_two,
    Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  apply inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
  exact Real.rpow_le_rpow (by positivity) hle hσ

theorem sobolev_window_ae (hWT : WindowTransferContract)
    (hMode : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      ModeBoundContract b θ T hb hb')
    {b : ℝ} {hb : 0 < b} {hb' : b < 1 / 2} {E : ℝ} (hE : E ^ 2 < 4) {τ : ℝ} (hτ : 0 < τ)
    {P : ProbabilityMeasure MarkedPointMeasure} (hP : IsCriticalMarkedLimit τ b E hb hb' P)
    (R : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∀ᵐ ξ ∂(P : Measure MarkedPointMeasure), ∀ x : MarkedSpectralSpace,
      ξ.marked.measure {x} ≠ 0 → |x.1| < R + 2 →
        Summable (fun m : ℤ => (1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2) ^ (-σ) *
          ‖∫ r, fourier m r ∂(x.2 : Measure Torus)‖ ^ 2) := by
  set η : ℝ := σ / 2 with hηdef
  have hη : 0 < η := by positivity
  have hη1 : η < 1 := by linarith
  obtain ⟨C, hC0, hC⟩ := mode_pow_bound hWT hMode hE hτ hP hη hη1
  set K : ℝ := C * (τ + τ ^ (3 / 2 : ℝ)) ^ (1 - η) with hK
  have hK0 : 0 ≤ K := by positivity
  set w : SpectralWeight := windowWeight R with hw
  set d : ℤ → ℝ := fun m => if m = 0 then 0 else (1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2) ^ (-σ)
    with hd
  have hd0 : ∀ m, 0 ≤ d m := fun m => by
    by_cases hm : m = 0
    · simp [hd, hm]
    · simp only [hd, hm, ↓reduceIte]; positivity
  set g : ℤ → MassProfile → ℝ := fun m ν => d m * modeMark (-m) ν with hg
  have hgc : ∀ m, Continuous (g m) := fun m => continuous_const.mul (continuous_modeMark _)
  have hg0 : ∀ m ν, 0 ≤ g m ν := fun m ν => mul_nonneg (hd0 m) (modeMark_nonneg _ _)
  set f : ℤ → MarkedSpectralSpace → ℝ≥0∞ := fun m x => ENNReal.ofReal (w x.1 * g m x.2) with hf
  have hfm : ∀ m, Measurable (f m) := fun m =>
    ENNReal.measurable_ofReal.comp (continuous_prodTest w.toContinuousMap.continuous (hgc m)).measurable
  set G : MarkedPointMeasure → ℝ≥0∞ := fun ξ => ∑' m, ∫⁻ x, f m x ∂ξ.marked.measure with hG
  have hGm : Measurable G := Measurable.tsum fun m => measurable_markedLIntegral
    (continuous_prodTest w.toContinuousMap.continuous (hgc m))
    (hasCompactSupport_prodTest w.compactSupport _) (prodTest_nonneg w.nonnegative (hg0 m))
  -- the expectation is finite
  set bexp : ℝ := 2 * σ + (1 - η) with hbexp
  have hb1 : 1 < bexp := by rw [hbexp, hηdef]; linarith
  set B : ℤ → ℝ := fun m => if m = 0 then 0 else K * |(m : ℝ)| ^ (-bexp) with hB
  have hB0 : ∀ m, 0 ≤ B m := fun m => by
    by_cases hm : m = 0
    · simp [hB, hm]
    · simp only [hB, hm, ↓reduceIte]; positivity
  have hBs : Summable B := by
    refine Summable.of_nonneg_of_le hB0 (fun m => ?_) ((Real.summable_abs_int_rpow hb1).mul_left K)
    by_cases hm : m = 0
    · simp only [hB, hm, ↓reduceIte]; positivity
    · simp only [hB, hm, ↓reduceIte]; exact le_rfl
  have hterm : ∀ m, weightFunctional P (g m) w ≤ ENNReal.ofReal (B m) := by
    intro m
    rw [weightFunctional_markConst P _ _ (hd0 m)]
    by_cases hm : m = 0
    · simp [hd, hB, hm]
    · have hv := hC w (-m) (neg_ne_zero.mpr hm)
      rw [← modeVariance_eq_weightFunctional] at *
      simp only [hd, hB, hm, ↓reduceIte]
      refine (mul_le_mul' le_rfl hv).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hma : 0 < |(m : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hm)
      have hsw := sobolevWeight_le hm hσ.le
      have hneg : |((-m : ℤ) : ℝ)| = |(m : ℝ)| := by push_cast; exact abs_neg _
      rw [hneg]
      calc (1 + 4 * Real.pi ^ 2 * (m : ℝ) ^ 2) ^ (-σ) * (K * |(m : ℝ)| ^ (-(1 - η))) ≤
            |(m : ℝ)| ^ (-(2 * σ)) * (K * |(m : ℝ)| ^ (-(1 - η))) :=
            mul_le_mul_of_nonneg_right hsw (by positivity)
        _ = K * |(m : ℝ)| ^ (-bexp) := by
            rw [hbexp, show -(2 * σ + (1 - η)) = -(2 * σ) + -(1 - η) by ring,
              Real.rpow_add hma]
            ring
  have hfin : ∫⁻ ξ, G ξ ∂(P : Measure MarkedPointMeasure) ≠ ⊤ := by
    rw [lintegral_tsum fun m => (measurable_markedLIntegral
      (continuous_prodTest w.toContinuousMap.continuous (hgc m))
      (hasCompactSupport_prodTest w.compactSupport _)
      (prodTest_nonneg w.nonnegative (hg0 m))).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [← ENNReal.ofReal_tsum_of_nonneg hB0 hBs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top hGm hfin] with ξ hξ x hx hxR
  -- the atom
  have hinner : ∫⁻ y, ∑' m, f m y ∂ξ.marked.measure = G ξ :=
    lintegral_tsum fun m => (hfm m).aemeasurable
  have hmt : Measurable (fun y => ∑' m, f m y) := Measurable.tsum hfm
  have hsingle := lintegral_singleton' (μ := ξ.marked.measure) hmt x
  have hle : (∑' m, f m x) * ξ.marked.measure {x} ≤ G ξ := by
    rw [← hsingle, ← hinner]
    exact setLIntegral_le_lintegral _ _
  have hfx : ∑' m, f m x ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_mul hx] at hle
    exact absurd (lt_of_le_of_lt hle hξ) (lt_irrefl _)
  have hwpos : 0 < w x.1 := windowWeight_pos R hxR
  have hsplit : ∀ m, f m x = ENNReal.ofReal (w x.1) * ENNReal.ofReal (g m x.2) := fun m =>
    ENNReal.ofReal_mul hwpos.le
  simp_rw [hsplit] at hfx
  rw [ENNReal.tsum_mul_left] at hfx
  have hfx' : ∑' m, ENNReal.ofReal (g m x.2) ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by simpa using hwpos)] at hfx; exact hfx rfl
  have hsum : Summable (fun m => g m x.2) := by
    have h1 : Summable (fun m => (g m x.2).toNNReal) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp hfx'
    exact (NNReal.summable_coe.mpr h1).congr fun m => Real.coe_toNNReal _ (hg0 m x.2)
  -- restore the `m = 0` term
  have hupd := hsum.update 0 ((1 + 4 * Real.pi ^ 2 * ((0 : ℤ) : ℝ) ^ 2) ^ (-σ) *
    ‖∫ r, fourier (0 : ℤ) r ∂(x.2 : Measure Torus)‖ ^ 2)
  refine hupd.congr fun m => ?_
  by_cases hm : m = 0
  · subst hm; simp
  · rw [Function.update_of_ne hm]
    simp only [hg, hd, hm, ↓reduceIte, modeMark, neg_neg]

end BlockBand.Window.SmallCritical
