module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbDefs
public import BlockBand.Model.Construction.OrderedSpectrum
public import BlockBand.Density.Stieltjes
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The zero-entrance lemma: the limiting measures (Stieltjes-transform tools)

We collect the Stieltjes-transform tools used to construct the limiting measures of the
zero-entrance lemma.

* `norm_stieltjesG_le`: `|G_μ(ζ)| ≤ 1/Im ζ` for a probability measure.
* `stieltjesG_differentiableOn`: `G_μ` is holomorphic on the upper half-plane (finite `μ`;
  differentiation under the integral).
* `exists_prob_of_stieltjes_tendsto`: if probability measures `ν_n` have Stieltjes transforms
  converging pointwise on the upper half-plane to `g`, and `(iy) g(iy) → 1` as `y → ∞`, then
  `g = G_μ` on the upper half-plane for a probability measure `μ`. Tightness comes from
  `ν{|x| > y} ≤ 2 Re(1 - (iy) G_ν(iy)) = 2 ∫ x²/(x² + y²) dν` (the large-`y` behaviour of the limit
  transform gives the tightness directly, without a count bound for the deformed Gaussian
  matrices); Mathlib's Prokhorov theorem gives a cluster point, whose Stieltjes
  transform is identified by weak continuity of `ν ↦ ∫ (ζ - x)⁻¹ dν`.
* `exists_expectedSpectral`: for an almost surely Hermitian measurable random `W × W` matrix `X`
  (`W ≥ 1`), the expected empirical spectral law `ν = W⁻¹ Σ_i Law(λ_i(X))` is a probability
  measure with `G_ν(ζ) = E W⁻¹ Tr (ζ - X)⁻¹` (increasing eigenvalues of the Hermitian part, which
  are continuous, hence measurable).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BoundedContinuousFunction

namespace ZeroEntranceMeasure

/-!
## The Stieltjes kernel
-/

theorem kernel_ne_zero {ζ : ℂ} (hζ : 0 < ζ.im) (x : ℝ) : ζ - (x : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem norm_kernel_le {ζ : ℂ} (hζ : 0 < ζ.im) (x : ℝ) : ‖(ζ - (x : ℂ))⁻¹‖ ≤ 1 / ζ.im := by
  rw [norm_inv, one_div]
  refine inv_anti₀ hζ ?_
  have h := Complex.abs_im_le_norm (ζ - (x : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
  exact (le_abs_self _).trans h

theorem continuous_kernel {ζ : ℂ} (hζ : 0 < ζ.im) :
    Continuous (fun x : ℝ => (ζ - (x : ℂ))⁻¹) :=
  (continuous_const.sub Complex.continuous_ofReal).inv₀ (kernel_ne_zero hζ)

/-- `x ↦ (ζ - x)⁻¹` as a bounded continuous function (`Im ζ > 0`). -/
def kernelBCF (ζ : ℂ) (hζ : 0 < ζ.im) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ℝ => (ζ - (x : ℂ))⁻¹)
    (continuous_kernel hζ) (1 / ζ.im) (norm_kernel_le hζ)

theorem kernelBCF_apply (ζ : ℂ) (hζ : 0 < ζ.im) (x : ℝ) :
    kernelBCF ζ hζ x = (ζ - (x : ℂ))⁻¹ := rfl

theorem integrable_kernel (μ : Measure ℝ) [IsFiniteMeasure μ] {ζ : ℂ} (hζ : 0 < ζ.im) :
    Integrable (fun x : ℝ => (ζ - (x : ℂ))⁻¹) μ :=
  (kernelBCF ζ hζ).integrable μ

end ZeroEntranceMeasure

open ZeroEntranceMeasure

/-- `|G_μ(ζ)| ≤ 1/Im ζ` for a probability measure `μ` and `Im ζ > 0`. -/
theorem norm_stieltjesG_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {ζ : ℂ} (hζ : 0 < ζ.im) :
    ‖stieltjesG μ ζ‖ ≤ 1 / ζ.im := by
  unfold stieltjesG
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1 / ζ.im)
    (Eventually.of_forall (norm_kernel_le hζ))
  simpa using this

/-- `G_μ` is holomorphic on the upper half-plane (finite `μ`). -/
theorem stieltjesG_differentiableOn (μ : Measure ℝ) [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (stieltjesG μ) {ζ : ℂ | 0 < ζ.im} := by
  intro ζ₀ hζ₀
  have hη : 0 < ζ₀.im := hζ₀
  refine DifferentiableAt.differentiableWithinAt ?_
  set ε := ζ₀.im / 2 with hε
  have hεpos : 0 < ε := by positivity
  have him : ∀ ζ ∈ ball ζ₀ ε, ε < ζ.im := by
    intro ζ hζ
    rw [mem_ball, dist_eq_norm] at hζ
    have h1 := Complex.abs_im_le_norm (ζ - ζ₀)
    rw [Complex.sub_im] at h1
    have := neg_abs_le (ζ.im - ζ₀.im)
    linarith
  have hball : ball ζ₀ ε ∈ 𝓝 ζ₀ := ball_mem_nhds _ hεpos
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun ζ (x : ℝ) => (ζ - (x : ℂ))⁻¹)
    (F' := fun ζ (x : ℝ) => -1 / (ζ - (x : ℂ)) ^ 2) (bound := fun _ => (1 / ε) ^ 2)
    hball ?_ (integrable_kernel μ hη) ?_ ?_ (integrable_const _) ?_
  · exact key.2.differentiableAt
  · filter_upwards [hball] with ζ hζ
    exact (continuous_kernel (hεpos.trans (him ζ hζ))).aestronglyMeasurable
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.div ((continuous_const.sub Complex.continuous_ofReal).pow 2)
      (fun x => pow_ne_zero 2 (kernel_ne_zero hη x))
  · refine Eventually.of_forall fun x ζ hζ => ?_
    have hz := hεpos.trans (him ζ hζ)
    rw [norm_div, norm_neg, norm_one, norm_pow, one_div, ← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have h1 := norm_kernel_le hz x
    rw [norm_inv] at h1
    refine h1.trans ?_
    rw [one_div, one_div]
    exact inv_anti₀ hεpos (him ζ hζ).le
  · refine Eventually.of_forall fun x ζ hζ => ?_
    have hz := hεpos.trans (him ζ hζ)
    have h := ((hasDerivAt_id ζ).sub_const (x : ℂ)).inv (kernel_ne_zero hz x)
    simp only [id] at h
    exact h

/-!
## Tightness from the Stieltjes transform
-/

namespace ZeroEntranceMeasure

theorem im_kernel_imag (r x : ℝ) (hr : 0 < r) :
    (((r : ℂ) * Complex.I - (x : ℂ))⁻¹).im = -r / (x ^ 2 + r ^ 2) := by
  rw [Complex.inv_im]
  simp [Complex.normSq_apply]
  have : 0 < x ^ 2 + r ^ 2 := by positivity
  field_simp

/-- `ν{|x| > r} ≤ 2 |1 - (ir) G_ν(ir)|` for a probability measure `ν` and `r > 0`. -/
theorem measure_norm_gt_le (ν : Measure ℝ) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r) :
    ν {x : ℝ | r < ‖x‖} ≤
      ENNReal.ofReal (2 * ‖1 - ((r : ℂ) * Complex.I) * stieltjesG ν ((r : ℂ) * Complex.I)‖) := by
  set ζ : ℂ := (r : ℂ) * Complex.I with hζdef
  have hζ : 0 < ζ.im := by simp [ζ, hr]
  set k : ℝ → ℝ := fun x => x ^ 2 / (x ^ 2 + r ^ 2) with hk
  have hkint : ∫ x, k x ∂ν = 1 + r * (stieltjesG ν ζ).im := by
    have hpt : ∀ x : ℝ, k x = 1 + r * ((ζ - (x : ℂ))⁻¹).im := by
      intro x
      rw [hζdef, im_kernel_imag r x hr]
      have : 0 < x ^ 2 + r ^ 2 := by positivity
      simp only [k]
      field_simp
      ring
    have hint := integrable_kernel ν hζ
    have hIm : Integrable (fun x : ℝ => ((ζ - (x : ℂ))⁻¹).im) ν := hint.im
    rw [show k = fun x : ℝ => 1 + r * ((ζ - (x : ℂ))⁻¹).im from funext hpt,
      integral_add (integrable_const _) (hIm.const_mul r), integral_const, integral_const_mul]
    unfold stieltjesG
    have := integral_im (𝕜 := ℂ) hint
    simp only [RCLike.im_to_complex] at this
    rw [this]
    simp
  have hkre : 1 + r * (stieltjesG ν ζ).im ≤ ‖1 - ζ * stieltjesG ν ζ‖ := by
    have h := Complex.re_le_norm (1 - ζ * stieltjesG ν ζ)
    have : (1 - ζ * stieltjesG ν ζ).re = 1 + r * (stieltjesG ν ζ).im := by
      simp [ζ]
    linarith
  have hS : MeasurableSet {x : ℝ | r < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  have hind : ∀ x, ({x : ℝ | r < ‖x‖}.indicator (fun _ => (1 : ℝ)) x) ≤ 2 * k x := by
    intro x
    by_cases hx : r < ‖x‖
    · rw [Set.indicator_of_mem (by exact hx)]
      have hx2 : r ^ 2 < x ^ 2 := by
        rw [Real.norm_eq_abs] at hx
        nlinarith [abs_nonneg x, sq_abs x]
      simp only [k]
      have : 0 < x ^ 2 + r ^ 2 := by positivity
      rw [← sub_nonneg]
      have : 2 * (x ^ 2 / (x ^ 2 + r ^ 2)) - 1 = (x ^ 2 - r ^ 2) / (x ^ 2 + r ^ 2) := by
        field_simp; ring
      rw [this]
      exact div_nonneg (by linarith) (by positivity)
    · rw [Set.indicator_of_notMem (by exact hx)]
      simp only [k]
      positivity
  have hkI : Integrable k ν := by
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun x => ?_)
    · exact (Continuous.aestronglyMeasurable (by
        refine (continuous_pow 2).div ((continuous_pow 2).add continuous_const) ?_
        intro x; positivity))
    · simp only [k, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg r]
  have hreal : ν.real {x : ℝ | r < ‖x‖} ≤ 2 * ‖1 - ζ * stieltjesG ν ζ‖ := by
    rw [← integral_indicator_one hS]
    calc ∫ x, {x : ℝ | r < ‖x‖}.indicator 1 x ∂ν ≤ ∫ x, 2 * k x ∂ν :=
          integral_mono ((integrable_const 1).indicator hS) (hkI.const_mul 2) hind
      _ = 2 * (1 + r * (stieltjesG ν ζ).im) := by rw [integral_const_mul, hkint]
      _ ≤ 2 * ‖1 - ζ * stieltjesG ν ζ‖ := by linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

end ZeroEntranceMeasure

open ZeroEntranceMeasure in
/-- **Limit measure from Stieltjes convergence.** If probability measures `ν n` on `ℝ` have
Stieltjes transforms converging pointwise on the upper half-plane to `g`, and
`(iy) g(iy) → 1` as `y → ∞`, then `g = G_μ` on the upper half-plane for a probability
measure `μ` (tightness from `measure_norm_gt_le`, Prokhorov, weak continuity of `G`). -/
theorem exists_prob_of_stieltjes_tendsto {ν : ℕ → Measure ℝ}
    (hν : ∀ n, IsProbabilityMeasure (ν n)) {g : ℂ → ℂ}
    (hconv : ∀ ζ : ℂ, 0 < ζ.im → Tendsto (fun n => stieltjesG (ν n) ζ) atTop (𝓝 (g ζ)))
    (hinf : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * g ((y : ℂ) * Complex.I)) atTop
      (𝓝 1)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ ζ : ℂ, 0 < ζ.im → stieltjesG μ ζ = g ζ := by
  have : ∀ n, IsFiniteMeasure (ν n) := fun n => by have := hν n; infer_instance
  -- tightness of the sequence
  have hlim : ∀ r : ℝ, 0 < r → limsup (fun n => ν n {x : ℝ | r < ‖x‖}) atTop ≤
      ENNReal.ofReal (2 * ‖1 - ((r : ℂ) * Complex.I) * g ((r : ℂ) * Complex.I)‖) := by
    intro r hr
    have hζ : 0 < ((r : ℂ) * Complex.I).im := by simp [hr]
    have ht : Tendsto (fun n => ENNReal.ofReal (2 * ‖1 - ((r : ℂ) * Complex.I) *
        stieltjesG (ν n) ((r : ℂ) * Complex.I)‖)) atTop
        (𝓝 (ENNReal.ofReal (2 * ‖1 - ((r : ℂ) * Complex.I) * g ((r : ℂ) * Complex.I)‖))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((((hconv _ hζ).const_mul ((r : ℂ) * Complex.I)).const_sub 1).norm.const_mul 2)
    rw [← ht.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall fun n => by
      have := hν n; exact measure_norm_gt_le (ν n) hr)
  have htight : IsTightMeasureSet (Set.range ν) := by
    refine isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt ?_
    have h0 : Tendsto (fun r : ℝ =>
        ENNReal.ofReal (2 * ‖1 - ((r : ℂ) * Complex.I) * g ((r : ℂ) * Complex.I)‖)) atTop
        (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto _).comp
        (((hinf.const_sub 1).norm).const_mul 2)
      simp only [sub_self, norm_zero, mul_zero, ENNReal.ofReal_zero] at this
      exact this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact hlim r hr
  -- Prokhorov
  let νP : ℕ → ProbabilityMeasure ℝ := fun n => ⟨ν n, hν n⟩
  have hS : IsTightMeasureSet
      {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range νP} := by
    convert htight using 1
    ext m
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨νP n, ⟨n, rfl⟩, rfl⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  obtain ⟨μ, -, hclus⟩ := hK (f := map νP atTop)
    (le_principal_iff.2 (mem_map.2 (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩)))
  refine ⟨(μ : Measure ℝ), inferInstance, fun ζ hζ => ?_⟩
  -- weak continuity of the Stieltjes transform
  have hcont : ContinuousAt (fun m : ProbabilityMeasure ℝ => stieltjesG (m : Measure ℝ) ζ) μ := by
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ
      (μs := fun m : ProbabilityMeasure ℝ => m) (F := 𝓝 μ) (μ := μ)).1 tendsto_id
      (kernelBCF ζ hζ)
    simp only [kernelBCF_apply] at this
    exact this
  have hmap : Tendsto (fun m : ProbabilityMeasure ℝ => stieltjesG (m : Measure ℝ) ζ)
      (map νP atTop) (𝓝 (g ζ)) := by
    rw [tendsto_map'_iff]
    exact hconv ζ hζ
  have hcl := hclus.map hcont hmap
  exact eq_of_nhds_neBot hcl

namespace ZeroEntranceMeasure

open Matrix

/-- The Hermitian part `½(M + Mᴴ)` as an element of the Hermitian subtype. -/
def hermPart {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    BlockBand.Model.Construction.HermitianMatrix (Fin W) :=
  ⟨(1 / 2 : ℂ) • (M + Mᴴ), by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm]
    congr 1
    simp⟩

theorem measurable_hermPart {W : ℕ} :
    Measurable (fun M : Matrix (Fin W) (Fin W) ℂ => hermPart M) := by
  refine Measurable.subtype_mk ?_
  refine Continuous.measurable ?_
  have hc : Continuous (fun M : Matrix (Fin W) (Fin W) ℂ => Mᴴ) :=
    continuous_id.matrix_conjTranspose
  exact (continuous_id.add hc).const_smul (1 / 2 : ℂ)

theorem hermPart_of_isHermitian {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) :
    hermPart M = ⟨M, hM⟩ := by
  apply Subtype.ext
  change (1 / 2 : ℂ) • (M + Mᴴ) = M
  rw [hM.eq, ← two_smul ℂ M, smul_smul]
  norm_num

/-- `Σ_j (ζ - λ_j)⁻¹` over the increasing eigenvalues is `W · W⁻¹ Tr (ζ - M)⁻¹`. -/
theorem normalizedResolventTrace_eq_increasing {W : ℕ} {M : Matrix (Fin W) (Fin W) ℂ}
    (hM : M.IsHermitian) {ζ : ℂ} (hζ : 0 < ζ.im) :
    normalizedResolventTrace M ζ = ∑ j : Fin (Fintype.card (Fin W)),
      Complex.ofReal ((W : ℝ)⁻¹) *
        (ζ - (BlockBand.Foundations.Spectral.increasingEigenvalue hM j : ℂ))⁻¹ := by
  rw [normalizedResolventTrace_eq hM hζ.ne', cavityStieltjes]
  exact BlockBand.Density.sum_eigenvalues_eq_sum_increasing hM
    (fun t => Complex.ofReal ((W : ℝ)⁻¹) * (ζ - (t : ℂ))⁻¹)

end ZeroEntranceMeasure

open ZeroEntranceMeasure in
/-- **Expected empirical spectral law.** For an almost surely Hermitian measurable random
`W × W` matrix (`W ≥ 1`), `ν = W⁻¹ Σ_i Law(λ_i)` (increasing eigenvalues of the Hermitian part)
is a probability measure with `G_ν(ζ) = E W⁻¹ Tr (ζ - X)⁻¹` on the upper half-plane. -/
theorem exists_expectedSpectral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {W : ℕ} (hW : 0 < W) {X : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hX : Measurable X) (hH : ∀ᵐ ω ∂P, (X ω).IsHermitian) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ ζ : ℂ, 0 < ζ.im →
      stieltjesG ν ζ = ∫ ω, normalizedResolventTrace (X ω) ζ ∂P := by
  set lam : Fin (Fintype.card (Fin W)) → Ω → ℝ := fun i ω =>
    BlockBand.Model.Construction.orderedEigenvalue (hermPart (X ω)) i with hlam
  have hlm : ∀ i, Measurable (lam i) := fun i =>
    (BlockBand.Model.Construction.measurable_orderedEigenvalue i).comp
      (measurable_hermPart.comp hX)
  set ν : Measure ℝ := ∑ i, ((W : ℝ≥0∞)⁻¹) • P.map (lam i) with hν
  have hWne : (W : ℝ≥0∞) ≠ 0 := by exact_mod_cast hW.ne'
  have hprob : IsProbabilityMeasure ν := by
    constructor
    rw [hν, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, Measure.map_apply (hlm _) MeasurableSet.univ,
      Set.preimage_univ, measure_univ, smul_eq_mul, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel hWne (ENNReal.natCast_ne_top W)
  refine ⟨ν, hprob, fun ζ hζ => ?_⟩
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m],
      Integrable (fun x : ℝ => (ζ - (x : ℂ))⁻¹) m := fun m _ => integrable_kernel m hζ
  unfold stieltjesG
  rw [hν, integral_finsetSum_measure (fun i _ =>
    (hint (P.map (lam i))).smul_measure (ENNReal.inv_ne_top.2 hWne))]
  simp only [integral_smul_measure]
  have hmap : ∀ i, ∫ x, (ζ - (x : ℂ))⁻¹ ∂(P.map (lam i)) = ∫ ω, (ζ - (lam i ω : ℂ))⁻¹ ∂P :=
    fun i => integral_map (hlm i).aemeasurable (continuous_kernel hζ).aestronglyMeasurable
  simp only [hmap]
  have hae : (fun ω => normalizedResolventTrace (X ω) ζ) =ᵐ[P]
      fun ω => ∑ i, Complex.ofReal ((W : ℝ)⁻¹) * (ζ - (lam i ω : ℂ))⁻¹ := by
    filter_upwards [hH] with ω hω
    rw [normalizedResolventTrace_eq_increasing hω hζ]
    simp only [hlam, hermPart_of_isHermitian hω]
    rfl
  have hsum := integral_finsetSum (μ := P) Finset.univ
    (f := fun i ω => Complex.ofReal ((W : ℝ)⁻¹) * (ζ - (lam i ω : ℂ))⁻¹)
    (fun i _ => ((integrable_kernel (P.map (lam i)) hζ).comp_measurable (hlm i)).const_mul _)
  rw [integral_congr_ae hae, hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]

end BlockBand.Endpoints.Clock
