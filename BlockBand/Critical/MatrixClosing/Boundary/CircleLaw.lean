module

public import BlockBand.Critical.MatrixClosing.Boundary.Circle
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Matrix closing, boundary clause: Poisson kernels of the phase force the Cauchy law

* `measureReal_abs_gt_le`: real Poisson kernels give `μ{|t| > r} ≤ 4/r` (tightness).
* `norm_integral_cay_pow_le`: the Poisson kernels give the Fourier moments `‖∫ c(t)ⁿ dμ‖ ≤ 2ⁿε`
  (Fubini over the phase of `w = e^{iφ}/2` and `integral_pk_mul_exp`).
* `cayChar`, `cayAlg`: the star algebra of Laurent polynomials in `c`, which separates points.
* **`tendsto_cauchy_of_poisson`**: if `|∫ P(w c(t)) dμ_N - 1| ≤ ε_N → 0` uniformly in `‖w‖ < 1`,
  then `μ_N → Cauchy(0,1)` weakly (Mathlib `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints`
  and `integral_cay_pow_cauchy`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Boundary

open Complex MeasureTheory Filter
open scoped Real Topology ComplexConjugate NNReal ENNReal BoundedContinuousFunction

theorem continuous_pk_cay {w : ℂ} (hw : ‖w‖ < 1) : Continuous fun t : ℝ => pk w (cay t) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (continuousAt_pk (one_sub_ne_zero_of_norm_lt
    (norm_mul_lt_one hw (norm_cay t).le))).comp continuous_cay.continuousAt

theorem integrable_pk_cay {w : ℂ} (hw : ‖w‖ < 1) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t : ℝ => pk w (cay t)) μ :=
  Integrable.of_bound (continuous_pk_cay hw).aestronglyMeasurable _
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_pk_le hw (norm_cay t).le)

/-- **Tightness from the real Poisson kernels.** If `∫ P(ρ c(t)) dμ ≤ 2` for every `0 ≤ ρ < 1`,
then `μ{|t| > r} ≤ 4/r` for `r ≥ 1`. -/
theorem measureReal_abs_gt_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : ∀ w : ℂ, ‖w‖ < 1 → ∫ t, pk w (cay t) ∂μ ≤ 2) {r : ℝ} (hr : 1 ≤ r) :
    μ.real {t | r < ‖t‖} ≤ 4 / r := by
  set ρ : ℝ := (r - 1) / (r + 1)
  have hr1 : (0 : ℝ) < r + 1 := by linarith
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hr1.le
  have hρ1 : ρ < 1 := by rw [div_lt_one hr1]; linarith
  have hw : ‖(ρ : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hρ0]; exact hρ1
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun t => pk_nonneg hw (norm_cay t).le) (integrable_pk_cay hw μ) (r / 2)
  have hsub : {t : ℝ | r < ‖t‖} ⊆ {t | r / 2 ≤ pk (ρ : ℂ) (cay t)} := by
    intro t ht
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at ht
    exact pk_cay_real_ge hr ht.le
  have hmono : μ.real {t : ℝ | r < ‖t‖} ≤ μ.real {t | r / 2 ≤ pk (ρ : ℂ) (cay t)} :=
    measureReal_mono hsub
  have h2 := h _ hw
  have hr0 : 0 < r := by linarith
  rw [le_div_iff₀ hr0]
  nlinarith

/-- **The Cayley phase moments from the Poisson kernels.** If `|∫ P(wc(t)) dμ - 1| ≤ ε` for every
`‖w‖ < 1`, then `‖∫ c(t)ⁿ dμ‖ ≤ 2ⁿ ε` for `n ≥ 1`. -/
theorem norm_integral_cay_pow_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {ε : ℝ}
    (h : ∀ w : ℂ, ‖w‖ < 1 → |∫ t, pk w (cay t) ∂μ - 1| ≤ ε) {n : ℕ} (hn : 1 ≤ n) :
    ‖∫ t, cay t ^ n ∂μ‖ ≤ 2 ^ n * ε := by
  set ρ : ℝ := 1 / 2
  have hρ0 : (0 : ℝ) ≤ ρ := by norm_num [ρ]
  have hρ1 : ρ < 1 := by norm_num [ρ]
  have hwφ : ∀ φ : ℝ, ‖(ρ : ℂ) * cexp (φ * I)‖ < 1 := by
    intro φ; rw [norm_mul_exp_I, Complex.norm_real, Real.norm_of_nonneg hρ0]; exact hρ1
  set g : ℝ → ℝ → ℂ := fun t φ =>
    (pk ((ρ : ℂ) * cexp (φ * I)) (cay t) : ℂ) * cexp (-(n : ℂ) * I * φ)
  have hgc : Continuous (Function.uncurry g) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t, φ⟩
    have h1 : ContinuousAt (fun p : ℝ × ℝ => pk ((ρ : ℂ) * cexp (p.2 * I)) (cay p.1)) (t, φ) := by
      unfold pk
      refine ContinuousAt.sub (ContinuousAt.mul continuousAt_const ?_) continuousAt_const
      refine Complex.continuous_re.continuousAt.comp ?_
      refine ContinuousAt.inv₀ (continuous_const.sub ((continuous_const.mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))).mul (continuous_cay.comp continuous_fst))).continuousAt ?_
      exact one_sub_ne_zero_of_norm_lt (norm_mul_lt_one (hwφ φ) (norm_cay t).le)
    have h2 := (Complex.continuous_ofReal.continuousAt.comp h1).mul
      (by fun_prop : ContinuousAt (fun p : ℝ × ℝ => cexp (-(n : ℂ) * I * p.2)) (t, φ))
    exact h2
  have hgb : ∀ t φ, ‖g t φ‖ ≤ 2 * (1 - ρ)⁻¹ + 1 := by
    intro t φ
    simp only [g, norm_mul]
    rw [show -(n : ℂ) * I * φ = ((-(n : ℝ) * φ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := abs_pk_le (hwφ φ) (norm_cay t).le
    rwa [norm_mul_exp_I, Complex.norm_real, Real.norm_of_nonneg hρ0] at this
  set ν : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * π))
  have hint : Integrable (Function.uncurry g) (μ.prod ν) :=
    Integrable.of_bound hgc.aestronglyMeasurable _ (Eventually.of_forall fun p => hgb p.1 p.2)
  have hswap := integral_integral_swap hint
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  -- inner integral over the phase
  have hin : ∀ t, ∫ φ, g t φ ∂ν = ((2 * π : ℝ) : ℂ) * ((ρ : ℂ) * cay t) ^ n := by
    intro t
    rw [← intervalIntegral.integral_of_le h2π]
    exact integral_pk_mul_exp hρ0 hρ1 (norm_cay t).le hn
  simp_rw [hin] at hswap
  rw [integral_const_mul] at hswap
  simp_rw [mul_pow, integral_const_mul] at hswap
  -- inner integral over `μ`
  have hin2 : ∀ φ, ∫ t, g t φ ∂μ =
      (((∫ t, pk ((ρ : ℂ) * cexp (φ * I)) (cay t) ∂μ) - 1 : ℝ) : ℂ) * cexp (-(n : ℂ) * I * φ) +
        cexp (-(n : ℂ) * I * φ) := by
    intro φ
    simp only [g]
    rw [integral_mul_const, integral_complex_ofReal]
    push_cast; ring
  simp_rw [hin2] at hswap
  have hcI : Integrable (fun φ : ℝ => cexp (-(n : ℂ) * I * φ)) ν :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun φ => by
      rw [show -(n : ℂ) * I * φ = ((-(n : ℝ) * φ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])
  have hzero : ∫ φ, cexp (-(n : ℂ) * I * φ) ∂ν = 0 := by
    rw [← intervalIntegral.integral_of_le h2π]
    have := integral_exp_int_mul_I (-(n : ℤ))
    have hn0 : (-(n : ℤ)) ≠ 0 := by omega
    simp only [hn0, ite_false] at this
    convert this using 3
    push_cast; ring
  have hD : Integrable (fun φ : ℝ => (((∫ t, pk ((ρ : ℂ) * cexp (φ * I)) (cay t) ∂μ) - 1 : ℝ) : ℂ) *
      cexp (-(n : ℂ) * I * φ)) ν := by
    have hs : (fun φ : ℝ => (((∫ t, pk ((ρ : ℂ) * cexp (φ * I)) (cay t) ∂μ) - 1 : ℝ) : ℂ) *
        cexp (-(n : ℂ) * I * φ)) = fun φ => (∫ t, g t φ ∂μ) - cexp (-(n : ℂ) * I * φ) := by
      funext φ; rw [hin2]; ring
    rw [hs]
    refine Integrable.sub ?_ hcI
    exact MeasureTheory.Integrable.integral_prod_right hint
  rw [integral_add hD hcI, hzero, add_zero] at hswap
  have hbound : ‖∫ φ, (((∫ t, pk ((ρ : ℂ) * cexp (φ * I)) (cay t) ∂μ) - 1 : ℝ) : ℂ) *
      cexp (-(n : ℂ) * I * φ) ∂ν‖ ≤ ε * (2 * π) := by
    rw [← intervalIntegral.integral_of_le h2π]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (C := ε) (f := fun φ : ℝ => (((∫ t, pk ((ρ : ℂ) * cexp (φ * I)) (cay t) ∂μ) - 1 : ℝ) : ℂ) *
        cexp (-(n : ℂ) * I * φ)) (fun φ _ => by
          rw [norm_mul, show -(n : ℂ) * I * φ = ((-(n : ℝ) * φ : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact h _ (hwφ φ))
    rwa [sub_zero, abs_of_nonneg h2π] at this
  rw [← hswap] at hbound
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg h2π, Real.norm_of_nonneg hρ0] at hbound
  have hρn : (0 : ℝ) < ρ ^ n := pow_pos (by norm_num [ρ]) n
  have h2πpos : 0 < 2 * π := by positivity
  have hρ2 : ρ ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num [ρ]
  have key : ρ ^ n * ‖∫ t, cay t ^ n ∂μ‖ ≤ ε := by
    have := hbound
    rw [mul_comm ε] at this
    exact le_of_mul_le_mul_left (by linarith) h2πpos
  calc ‖∫ t, cay t ^ n ∂μ‖ = 2 ^ n * (ρ ^ n * ‖∫ t, cay t ^ n ∂μ‖) := by
        rw [← mul_assoc, mul_comm (2 ^ n : ℝ), hρ2, one_mul]
    _ ≤ 2 ^ n * ε := by gcongr

/-!
## The star algebra of Cayley characters
-/

/-- The Cayley characters `t ↦ c(t)ⁿ`, `n ∈ ℤ`, as bounded continuous functions. -/
def cayChar (n : ℤ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun t => cay t ^ n, continuous_cay.zpow₀ n fun t => Or.inl (cay_ne_zero t)⟩ 2 fun s t => by
      simp only [ContinuousMap.coe_mk]
      calc dist (cay s ^ n) (cay t ^ n) ≤ ‖cay s ^ n‖ + ‖cay t ^ n‖ := dist_le_norm_add_norm _ _
        _ = 2 := by rw [norm_zpow, norm_zpow, norm_cay, norm_cay, one_zpow]; norm_num

theorem cayChar_apply (n : ℤ) (t : ℝ) : cayChar n t = cay t ^ n := rfl

theorem cayChar_mul (m n : ℤ) : cayChar m * cayChar n = cayChar (m + n) := by
  ext t
  simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply, cayChar_apply,
    zpow_add₀ (cay_ne_zero t)]

theorem cayChar_zero : cayChar 0 = 1 := by
  ext t; rw [cayChar_apply, zpow_zero]; rfl

theorem star_cayChar (n : ℤ) : star (cayChar n) = cayChar (-n) := by
  ext t
  simp only [BoundedContinuousFunction.star_apply, cayChar_apply]
  rw [Complex.star_def, map_zpow₀, conj_cay, inv_zpow']

/-- The span of the Cayley characters. -/
abbrev cayspan : Submodule ℂ (ℝ →ᵇ ℂ) := Submodule.span ℂ (Set.range cayChar)

theorem cayChar_mem (n : ℤ) : cayChar n ∈ cayspan := Submodule.subset_span ⟨n, rfl⟩

theorem cayspan_mul_mem {x y : ℝ →ᵇ ℂ} (hx : x ∈ cayspan) (hy : y ∈ cayspan) :
    x * y ∈ cayspan := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨m, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨n, rfl⟩ := hb
      rw [cayChar_mul]; exact cayChar_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

theorem cayspan_star_mem {x : ℝ →ᵇ ℂ} (hx : x ∈ cayspan) : star x ∈ cayspan := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨m, rfl⟩ := ha
    rw [star_cayChar]; exact cayChar_mem _
  | zero => rw [star_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [star_add]; exact add_mem ha hb
  | smul c a _ ha => rw [star_smul]; exact Submodule.smul_mem _ _ ha

/-- The star subalgebra of trigonometric polynomials in the Cayley phase. -/
def cayAlg : StarSubalgebra ℂ (ℝ →ᵇ ℂ) :=
  { cayspan.toSubalgebra (by rw [← cayChar_zero]; exact cayChar_mem 0)
      (fun _ _ hx hy => cayspan_mul_mem hx hy) with
    star_mem' := fun hx => cayspan_star_mem hx }

theorem mem_cayAlg {x : ℝ →ᵇ ℂ} : x ∈ cayAlg ↔ x ∈ cayspan := Iff.rfl

theorem cayAlg_separatesPoints :
    (cayAlg.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro s t hst
  refine ⟨_, ⟨(BoundedContinuousFunction.toContinuousMapStarₐ ℂ) (cayChar 1),
    ⟨cayChar 1, cayChar_mem 1, rfl⟩, rfl⟩, ?_⟩
  simp only [BoundedContinuousFunction.toContinuousMapStarₐ_apply_apply, cayChar_apply, zpow_one]
  exact fun h => hst (cay_injective h)

/-- Convergence of the integrals on the span follows from convergence on the characters. -/
theorem tendsto_integral_of_mem_cayspan {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hgen : ∀ n : ℤ, Tendsto (fun N => ∫ t, cayChar n t ∂(μ N : Measure ℝ)) atTop
      (𝓝 (∫ t, cayChar n t ∂(ν : Measure ℝ))))
    {g : ℝ →ᵇ ℂ} (hg : g ∈ cayspan) :
    Tendsto (fun N => ∫ t, g t ∂(μ N : Measure ℝ)) atTop (𝓝 (∫ t, g t ∂(ν : Measure ℝ))) := by
  induction hg using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, rfl⟩ := ha
    exact hgen n
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    have e : ∀ m : Measure ℝ, [IsFiniteMeasure m] →
        ∫ t, (a t + b t) ∂m = ∫ t, a t ∂m + ∫ t, b t ∂m := fun m _ =>
      integral_add (a.integrable m) (b.integrable m)
    simp only [e]
    exact ha.add hb
  | smul c a _ ha =>
    simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, integral_const_mul]
    exact ha.const_mul c

/-- **Poisson kernels of the Cayley phase determine the standard Cauchy limit.** Let `μ_N` be
probability measures on `ℝ` with `|∫ P(w c(t)) dμ_N - 1| ≤ ε_N` for all `‖w‖ < 1`, eventually,
where `ε_N → 0`. Then `μ_N → Cauchy(0,1)` weakly. (Letting `ρ ↑ 1` would show that the law of `ζ` has density between `1 - o(1)` and
`1 + o(1)` relative to uniform circle measure; here the proof goes through tightness and the
Fourier moments of `ζ = c(t)`.) -/
theorem tendsto_cauchy_of_poisson {μ : ℕ → ProbabilityMeasure ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ N in atTop, ∀ w : ℂ, ‖w‖ < 1 → |∫ t, pk w (cay t) ∂(μ N : Measure ℝ) - 1| ≤ ε N) :
    Tendsto μ atTop (𝓝 ⟨ProbabilityTheory.cauchyMeasure 0 1, inferInstance⟩) := by
  have hε1 : ∀ᶠ N in atTop, ε N ≤ 1 := hε.eventually (ge_mem_nhds (by norm_num))
  -- tightness
  have htight : IsTightMeasureSet {(μ n : Measure ℝ) | n} := by
    have := isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
      (μ := fun n => (μ n : Measure ℝ)) (E := ℝ) ?_
    · exact this
    have hb : ∀ r : ℝ, 1 ≤ r → limsup (fun n => (μ n : Measure ℝ) {x | r < ‖x‖}) atTop ≤
        ENNReal.ofReal (4 / r) := by
      intro r hr
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [h, hε1] with N hN hN1
      have h2 : ∀ w : ℂ, ‖w‖ < 1 → ∫ t, pk w (cay t) ∂(μ N : Measure ℝ) ≤ 2 := by
        intro w hw
        have := hN w hw
        rw [abs_le] at this
        linarith
      have := measureReal_abs_gt_le h2 hr
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal this
    have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (4 / r)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop tendsto_id)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le)
      ((eventually_ge_atTop 1).mono fun r hr => hb r hr)
  refine ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℂ htight cayAlg_separatesPoints ?_
  intro g hg
  refine tendsto_integral_of_mem_cayspan (fun n => ?_) (mem_cayAlg.1 hg)
  simp only [cayChar_apply, ProbabilityMeasure.coe_mk]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · -- negative characters: conjugates
    obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, 1 ≤ k ∧ n = -(k : ℤ) := ⟨(-n).toNat, by omega, by omega⟩
    have hc : ∀ t, cay t ^ (-(k : ℤ)) = conj (cay t ^ k) := by
      intro t
      rw [zpow_neg, zpow_natCast, map_pow, conj_cay, inv_pow]
    simp only [hc, integral_conj]
    rw [integral_cay_pow_cauchy hk, map_zero]
    have hm : Tendsto (fun N => ∫ t, cay t ^ k ∂(μ N : Measure ℝ)) atTop (𝓝 0) := by
      have hb : Tendsto (fun N => (2 : ℝ) ^ k * ε N) atTop (𝓝 0) := by
        simpa using hε.const_mul ((2 : ℝ) ^ k)
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [h] with N hN
      exact norm_integral_cay_pow_le hN hk
    have := (Complex.continuous_conj.tendsto 0).comp hm
    rw [map_zero] at this
    exact this
  · simp
  · obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, 1 ≤ k ∧ n = (k : ℤ) := ⟨n.toNat, by omega, by omega⟩
    simp only [zpow_natCast]
    rw [integral_cay_pow_cauchy hk]
    have hb : Tendsto (fun N => (2 : ℝ) ^ k * ε N) atTop (𝓝 0) := by
      simpa using hε.const_mul ((2 : ℝ) ^ k)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [h] with N hN
    exact norm_integral_cay_pow_le hN hk

end BlockBand.Critical.MatrixClosing.Boundary
