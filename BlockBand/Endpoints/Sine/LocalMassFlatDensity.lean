module

public import BlockBand.Endpoints.Sine.LocalMassFlatDefs
public import BlockBand.Counting.PSSSPhysicalCounting

/-!
# The spectral window mass along critical sequences

Step 4 of the proof of the local-mass flatness theorem, together with the critical density
theorem for the limit of `E Σ_α w(u_α)`.

* `lmf_windowSum_eq_density` (exact, every admissible `p`, model, bulk `E`): if `ρ_{n,W}` is a
  continuous nonnegative density of the normalized mean empirical measure
  (`meanEmpiricalMeasure`), then
  `E Σ_α w(u_α) = ρ(E)⁻¹ ∫ ρ_{n,W}(E + u/(Nρ(E))) w(u) du`, `u_α = Nρ(E)(λ_α - E)`,
  `ρ = semicircleDensity`; `w` continuous with compact support.
* `lmf_spectralWindow_tendsto`: under `CriticalDensityEstimate` (the critical density theorem,
  both clauses), for `0 < b < 1/2`, `-2 < E < 2`, a window `w` (`IsWindow`: continuous,
  compactly supported, `w ≥ 0`, `∫ w = 1`), `τ > 0`, every critical sequence `n/W → τ` and every
  sequence of models, `E Σ_α w(u_α) → 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-- The semicircle density is positive in the open bulk. -/
theorem lmf_semicircleDensity_pos {E : ℝ} (hE : -2 < E) (hE' : E < 2) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  apply div_pos _ (by positivity)
  apply Real.sqrt_pos.mpr
  nlinarith

/-- The semicircle density is continuous. -/
theorem lmf_continuous_semicircleDensity : Continuous Parameters.semicircleDensity := by
  unfold Parameters.semicircleDensity
  fun_prop

/-- **Exact window mass through a density** of the mean empirical measure. -/
theorem lmf_windowSum_eq_density (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    (hρE : 0 < Parameters.semicircleDensity E) (w : ℝ → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (ρn : ℝ → ℝ) (hρc : Continuous ρn) (hρ0 : ∀ e, 0 ≤ ρn e)
    (hmean : meanEmpiricalMeasure p model =
      volume.withDensity (fun e => ENNReal.ofReal (ρn e))) :
    (∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α))
        ∂(model.law : Measure p.SiteMatrix)) =
      (Parameters.semicircleDensity E)⁻¹ *
        ∫ u, ρn (E + u / ((p.N : ℝ) * Parameters.semicircleDensity E)) * w u := by
  set ρE := Parameters.semicircleDensity E with hρE_def
  set a : ℝ := (p.N : ℝ) * ρE with ha_def
  have hN : (0 : ℝ) < p.N := by
    have h4 : 0 < p.n := by have := p.n_ge_four; omega
    have : 0 < p.N := by unfold Parameters.N; exact Nat.mul_pos h4 p.W_pos
    exact_mod_cast this
  have ha : 0 < a := mul_pos hN hρE
  let loc : p.SiteMatrix → Fin (Fintype.card p.Site) → ℝ := fun H i =>
    BlockBand.Foundations.Spectral.increasingEigenvalue (p.physicalHermitianVersion H).2 i
  have hloc : ∀ i, Measurable (fun H => loc H i) := fun i =>
    (measurable_increasingEigenvalue i).comp p.measurable_physicalHermitianVersion
  let g : ℝ → ℝ := fun e => w (microCoord p E e)
  have hg : Continuous g := by
    unfold g microCoord; fun_prop
  obtain ⟨M, hM⟩ := hw.bounded_above_of_compact_support hwc
  have hgM : ∀ e, ‖g e‖ ≤ M := fun e => hM _
  -- Step 1: reindex to the counting convention.
  have h1 : (∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α))
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ H, ∑ i : Fin (Fintype.card p.Site), g (loc H i) ∂(model.law : Measure p.SiteMatrix) := by
    refine integral_congr_ae ?_
    filter_upwards [model.isPhysical.1] with H hH
    have hv : p.physicalHermitianVersion H = ⟨H, hH⟩ :=
      Subtype.ext (p.gaussianReconstruction_gaussianExtraction H hH)
    have hl : ∀ i, loc H i = BlockBand.Foundations.Spectral.increasingEigenvalue hH i := by
      intro i
      simp only [loc, hv]
    simp only [hl]
    refine Fintype.sum_equiv (finCongr (physicalSite_card p).symm) _ _ fun α => ?_
    simp only [g, physicalOrderedEigenvalue, rawIncreasingEigenvalue_eq _ H hH]
    rfl
  -- Step 2: the finite spectral intensity.
  have hint : Integrable g (BlockBand.Counting.finiteSpectralIntensity
      (model.law : Measure p.SiteMatrix) loc) :=
    (integrable_const M).mono' hg.aestronglyMeasurable (Eventually.of_forall hgM)
  have h2 := BlockBand.Counting.integral_finiteSpectralIntensity
    (model.law : Measure p.SiteMatrix) loc hloc g hint
  -- Step 3: the intensity is `N` times the mean empirical measure.
  have h3 : BlockBand.Counting.finiteSpectralIntensity (model.law : Measure p.SiteMatrix) loc =
      (p.N : ℝ≥0∞) • meanEmpiricalMeasure p model := by
    unfold meanEmpiricalMeasure
    rw [smul_smul, ENNReal.mul_inv_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top _),
      one_smul]
  -- Step 4: the density.
  have h4 : (∫ e, g e ∂(meanEmpiricalMeasure p model)) = ∫ e, ρn e * g e := by
    rw [hmean]
    have hf : Measurable (fun e => (ρn e).toNNReal) := hρc.measurable.real_toNNReal
    have := integral_withDensity_eq_integral_smul (μ := volume) hf g
    refine this.trans (integral_congr_ae (Eventually.of_forall fun e => ?_))
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hρ0 e)]
  -- Step 5: the change of variables `e = E + u/a`.
  have h5 : (∫ u, ρn (E + u / a) * w u) = a * ∫ e, ρn e * g e := by
    have hc := Measure.integral_comp_mul_left (fun y => ρn (E + y) * g (E + y)) a⁻¹
    rw [inv_inv, abs_of_pos ha, smul_eq_mul,
      integral_add_left_eq_self (fun e => ρn e * g e) E] at hc
    rw [← hc]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [g, microCoord]
    rw [← ha_def, add_sub_cancel_left, div_eq_inv_mul]
    congr 2
    field_simp
  rw [h1, ← h2, h3, integral_smul_measure, h4, ENNReal.toReal_natCast, smul_eq_mul, h5]
  field_simp
  rw [ha_def]; ring

/-- **The window mass tends to `∫ w = 1`** along every critical sequence (the critical density
theorem, `CriticalDensityEstimate`). -/
theorem lmf_spectralWindow_tendsto (hDens : CriticalDensityEstimate) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (E : ℝ) (hE : -2 < E) (hE' : E < 2) (w : ℝ → ℝ) (hw : IsWindow w)
    (τ : ℝ) (hτ : 0 < τ) (s : CriticalSequence τ)
    (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel) :
    Tendsto (fun j => ∫ H, ∑ α : Fin (s.parameters b hb hb' j).N,
        w (microCoord (s.parameters b hb hb' j) E
          (physicalOrderedEigenvalue (s.parameters b hb hb' j) H α))
        ∂((R j).law : Measure _)) atTop (𝓝 1) := by
  obtain ⟨hwc0, hwc, hw0, hwone⟩ := hw
  set ρE := Parameters.semicircleDensity E with hρE_def
  have hρE : 0 < ρE := lmf_semicircleDensity_pos hE hE'
  set κ : ℝ := (2 - |E|) / 2 with hκ_def
  have hEabs : |E| < 2 := abs_lt.mpr ⟨hE, hE'⟩
  have hκ : 0 < κ := by rw [hκ_def]; linarith
  obtain ⟨C, hC0, hC⟩ := hDens.2 b κ (2 * τ) hb hb' hκ (by linarith)
  choose ρn hρs hρ0 hρeq using fun j => hDens.1 (s.parameters b hb hb' j) (R j)
  have hρc : ∀ j, Continuous (ρn j) := fun j => (hρs j).continuous
  -- the support of `w`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ u, w u ≠ 0 → |u| ≤ L := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hwc.isCompact.isBounded
    refine ⟨r, fun u hu => ?_⟩
    have := hr (subset_tsupport w hu)
    simpa [Metric.mem_closedBall, Real.dist_eq] using this
  -- widths and `a_j = N_j ρ(E)`
  have hWr : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  set a : ℕ → ℝ := fun j => ((s.parameters b hb hb' j).N : ℝ) * ρE with ha_def
  have hapos : ∀ j, 0 < a j := by
    intro j
    have h4 : 0 < s.n j := by have := s.n_ge_four j; omega
    have : 0 < (s.parameters b hb hb' j).N := by
      unfold Parameters.N; exact Nat.mul_pos h4 (s.W_pos j)
    exact mul_pos (by exact_mod_cast this) hρE
  have hNW : ∀ j, (s.W j : ℝ) ≤ ((s.parameters b hb hb' j).N : ℝ) := by
    intro j
    have : s.W j ≤ s.n j * s.W j := Nat.le_mul_of_pos_left _ (by have := s.n_ge_four j; omega)
    exact_mod_cast this
  have hatop : Tendsto a atTop atTop := by
    refine Tendsto.atTop_mul_const hρE (tendsto_atTop_mono hNW hWr)
  have hLa : Tendsto (fun j => L / a j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hatop
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε * ρE / 2 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨r₀, hr₀, hcont⟩ := Metric.continuousAt_iff.1
    lmf_continuous_semicircleDensity.continuousAt (ε := η / 2) (by positivity)
  set r : ℝ := min r₀ κ with hr_def
  have hr : 0 < r := lt_min hr₀ hκ
  -- eventual conditions
  have hc1 : ∀ᶠ j in atTop, L / a j < r := (tendsto_order.1 hLa).2 r hr
  have hc2 : ∀ᶠ j in atTop, C * (s.W j : ℝ) ^ (-(1 : ℝ) / 32) < η / 2 := by
    have h0 : Tendsto (fun j => C * (s.W j : ℝ) ^ (-(1 : ℝ) / 32)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 / 32) (by norm_num)).comp hWr
      simpa [neg_div] using this.const_mul C
    exact (tendsto_order.1 h0).2 _ (by positivity)
  have hratio := s.ratio_tendsto
  have hlo : ∀ᶠ j in atTop, τ / 2 < (s.n j : ℝ) / s.W j := (tendsto_order.1 hratio).1 _ (by linarith)
  have hhi : ∀ᶠ j in atTop, (s.n j : ℝ) / s.W j < 2 * τ := (tendsto_order.1 hratio).2 _ (by linarith)
  have hw16 : ∀ᶠ j in atTop, (s.W j : ℝ) ^ (-(1 / 16 : ℝ)) ≤ τ / 16 :=
    (tendsto_order.1 ((tendsto_rpow_neg_atTop (y := 1 / 16) (by norm_num)).comp hWr)).2 _
      (by positivity) |>.mono fun _ h => h.le
  have hwinv : ∀ᶠ j in atTop, (s.W j : ℝ)⁻¹ ≤ τ / 16 :=
    (tendsto_order.1 (tendsto_inv_atTop_zero.comp hWr)).2 _ (by positivity) |>.mono
      fun _ h => h.le
  filter_upwards [hc1, hc2, hlo, hhi, hw16, hwinv] with j h1 h2 h3 h4 h5 h6
  have hWj : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hnW : (s.n j : ℝ) = (s.n j : ℝ) / s.W j * s.W j := by field_simp
  -- admissibility of `(n, W)` for clause 2
  have hadm1 : 4 * ⌈(s.W j : ℝ) ^ ((15 : ℝ) / 16)⌉₊ ≤ s.n j := by
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (s.W j : ℝ) ^ ((15 : ℝ) / 16) by positivity)
    have hsplit : (s.W j : ℝ) ^ ((15 : ℝ) / 16) = s.W j * (s.W j : ℝ) ^ (-(1 / 16 : ℝ)) := by
      rw [← Real.rpow_one_add' hWj.le (by norm_num)]; norm_num
    have hA : 4 * (s.W j : ℝ) ^ ((15 : ℝ) / 16) ≤ τ / 4 * s.W j := by
      rw [hsplit]; nlinarith
    have hB : (4 : ℝ) ≤ τ / 4 * s.W j := by
      have := mul_le_mul_of_nonneg_right h6 hWj.le
      rw [inv_mul_cancel₀ hWj.ne'] at this
      nlinarith
    have hn : τ / 2 * s.W j < s.n j := by
      rw [hnW]; exact mul_lt_mul_of_pos_right h3 hWj
    have : (4 * ⌈(s.W j : ℝ) ^ ((15 : ℝ) / 16)⌉₊ : ℝ) < s.n j := by
      nlinarith
    exact_mod_cast this.le
  have hadm2 : (s.n j : ℝ) ≤ 2 * τ * s.W j := by
    rw [hnW]; exact (mul_lt_mul_of_pos_right h4 hWj).le
  have hdens := hC (s.n j) (s.W j) (s.n_ge_four j) (s.W_pos j) hadm1 hadm2 (R j) (ρn j) (hρc j)
    (hρeq j)
  -- the pointwise bound on the support of `w`
  have hpt : ∀ u, w u ≠ 0 → |ρn j (E + u / a j) - ρE| < η := by
    intro u hu
    have hu' := hL u hu
    have hdist : |u / a j| < r := by
      rw [abs_div, abs_of_pos (hapos j)]
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right hu' (hapos j).le) h1
    have he : |E + u / a j| ≤ 2 - κ := by
      have := abs_add_le E (u / a j)
      have hrk : r ≤ κ := min_le_right _ _
      rw [hκ_def] at hrk ⊢; linarith
    have hd1 := hdens (E + u / a j) he
    have hd2 : |Parameters.semicircleDensity (E + u / a j) - ρE| < η / 2 := by
      have := hcont (x := E + u / a j) (by
        rw [Real.dist_eq, add_sub_cancel_left]
        exact lt_of_lt_of_le hdist (min_le_left _ _))
      rwa [Real.dist_eq] at this
    calc |ρn j (E + u / a j) - ρE|
        ≤ |ρn j (E + u / a j) - Parameters.semicircleDensity (E + u / a j)| +
          |Parameters.semicircleDensity (E + u / a j) - ρE| := abs_sub_le _ _ _
      _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (hd1.trans h2.le) hd2
      _ = η := by ring
  -- conclude
  rw [lmf_windowSum_eq_density (s.parameters b hb hb' j) (R j) E hρE w hwc0 hwc (ρn j) (hρc j)
    (hρ0 j) (hρeq j)]
  change dist (ρE⁻¹ * ∫ u, ρn j (E + u / a j) * w u) 1 < ε
  have hwint : Integrable w volume := hwc0.integrable_of_hasCompactSupport hwc
  have hFint : Integrable (fun u => ρn j (E + u / a j) * w u) volume :=
    ((hρc j).comp (continuous_const.add (continuous_id.div_const _))).mul hwc0
      |>.integrable_of_hasCompactSupport hwc.mul_left
  have hone : (1 : ℝ) = ρE⁻¹ * ∫ u, ρE * w u := by
    rw [integral_const_mul, hwone, mul_one, inv_mul_cancel₀ hρE.ne']
  rw [Real.dist_eq, hone, ← mul_sub, ← integral_sub hFint (hwint.const_mul _), abs_mul,
    abs_of_pos (inv_pos.mpr hρE)]
  have hbound : ‖∫ u, (ρn j (E + u / a j) * w u - ρE * w u)‖ ≤ ∫ u, η * w u := by
    refine norm_integral_le_of_norm_le (hwint.const_mul _) (Eventually.of_forall fun u => ?_)
    by_cases hu : w u = 0
    · simp [hu]
    · rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 u)]
      exact mul_le_mul_of_nonneg_right (hpt u hu).le (hw0 u)
  rw [integral_const_mul, hwone, mul_one] at hbound
  rw [← Real.norm_eq_abs]
  calc ρE⁻¹ * ‖∫ u, (ρn j (E + u / a j) * w u - ρE * w u)‖ ≤ ρE⁻¹ * η :=
        mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hρE).le
    _ = ε / 2 := by rw [hη_def]; field_simp
    _ < ε := by linarith

end BlockBand.Endpoints
