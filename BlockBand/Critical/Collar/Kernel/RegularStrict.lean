module

public import BlockBand.Critical.Collar.Kernel.ExceptionalPhases

/-!
# The regular collar-kernel bound at zero height (strict clause), from phase bounds

*Law.* `collarLaw W b`, `0 < b < 1/2`, `W ≥ 1`; deterministic `X` with `Y = -Im X ≻ 0`, zero
height, shift `s`; Cauchy phases `t ~ stdCauchy`, `X_t = X_h + tY`.

`lintegral_collarKernel_quad_le_phases`: if on the regular phases `d_e(X_t) ≤ d₁` the regularized
fresh-row form obeys `E π⁻¹ Im⟨y,(ℋ_{X_t} - iε)⁻¹y⟩ ≤ A + εK` (every `ε > 0`), and the exceptional
phases have Cauchy mass `≤ m`, then
`E Re q*𝒫(Ur)q ≤ η⁻¹ (π A + m C_{b,w} √W ‖q‖²)`.
The regular phases are supplied by `Density.lintegral_collarRow_le_of_regular` (from
`CollarDensityRegularClause`), the exceptional mass by `stdCauchy_matchedDistance_gt_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open BlockBand.Critical.Collar.Density
open scoped ComplexOrder ENNReal

variable {W : ℕ}

theorem rowCoeff_eq (b e s : ℝ) : rowCoeff b e s = star (boundaryZ b e) + ((e + s : ℝ) : ℂ) := by
  rw [rowCoeff, star_add, Complex.star_def, Complex.conj_ofReal]

theorem mk_zero_eq_mul_I (ε : ℝ) : (⟨0, ε⟩ : ℂ) = (ε : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- **Strict regular kernel bound from phase bounds** (zero height). -/
theorem lintegral_collarKernel_quad_le_phases {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hW : 0 < W) (e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosDef)
    (q : Fin 2 × Fin W → ℂ) {d₁ A K m : ℝ} (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hgood : ∀ t : ℝ, matchedDistance b e (rePart X + (t : ℂ) • (-Critical.imPart X)) ≤ d₁ →
      ∀ ε : ℝ, 0 < ε →
        ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec (rowCoeff b e s) q ω) ⬝ᵥ
          ((collarMatrix (e + s) (rePart X + (t : ℂ) • (-Critical.imPart X)) ω -
            (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
              collarRowVec (rowCoeff b e s) q ω)).im) ∂Critical.collarLaw W b ≤
          ENNReal.ofReal A + ENNReal.ofReal (ε * K))
    (hbad : stdCauchy {t : ℝ | d₁ < matchedDistance b e
      (rePart X + (t : ℂ) • (-Critical.imPart X))} ≤ ENNReal.ofReal m) :
    ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s 0 ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b ≤
      ENNReal.ofReal ((boundaryZ b e).im⁻¹ * (Real.pi * A +
        m * (collarRowConst b (rowCoeff b e s) * Real.sqrt W * ∑ x, ‖q x‖ ^ 2))) := by
  set η := (boundaryZ b e).im
  set e' := e + s
  set w := rowCoeff b e s
  set rv := collarRowVec w q
  set B := collarRowConst b w * Real.sqrt W * ∑ x, ‖q x‖ ^ 2
  have hB : 0 ≤ B := by
    have := collarRowConst_nonneg hb0.le w
    have : 0 ≤ ∑ x, ‖q x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  set Y := -Critical.imPart X
  set Xh := rePart X
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεn : ∀ n, 0 < εn n := fun n => by positivity
  have hεt : Tendsto εn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set N : Critical.CollarSample W → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (-(star (rv ω) ⬝ᵥ ((collarMatrix e' X ω)⁻¹ *ᵥ rv ω)).im)
  set Nn : ℕ → Critical.CollarSample W → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (-(star (rv ω) ⬝ᵥ ((collarMatrix e' X ω +
      ((εn n : ℂ) * Complex.I) • 1)⁻¹ *ᵥ rv ω)).im)
  set G : ℕ → ℝ × Critical.CollarSample W → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal ((star (rv p.2) ⬝ᵥ ((collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 -
      ((εn n : ℂ) * Complex.I) • 1)⁻¹ *ᵥ rv p.2)).im)
  have hrv : Measurable rv := Density.measurable_collarRowVec w q
  have hMc := Density.measurable_collarMatrix e' X (W := W)
  have hNn : ∀ n, Measurable (Nn n) := fun n =>
    measurable_ofReal_neg_im_form (Measurable.of_eval_matrix _ fun i j =>
      ((Matrix.measurable_apply).comp hMc).add measurable_const) hrv
  have hG : ∀ n, Measurable (G n) := by
    intro n
    have hM : Measurable fun p : ℝ × Critical.CollarSample W =>
        collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((εn n : ℂ) * Complex.I) • 1 := by
      have heq : (fun p : ℝ × Critical.CollarSample W =>
          collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((εn n : ℂ) * Complex.I) • 1) =
          fun p => collarMatrix e' Xh p.2 - (p.1 : ℂ) • topLift Y -
            ((εn n : ℂ) * Complex.I) • 1 := by
        funext p; rw [collarMatrix_add_right, topLift_smul]
      rw [heq]
      refine Measurable.of_eval_matrix _ fun i j => ?_
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine (((Matrix.measurable_apply).comp ((Density.measurable_collarMatrix e' Xh).comp
        measurable_snd)).sub ?_).sub measurable_const
      exact (Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const
    exact Density.measurable_ofReal_im_form hM (hrv.comp measurable_snd)
  have hHerm := Density.ae_collarMatrix_isHermitian b e' (rePart_isHermitian X) (W := W)
  have hDinv := ae_isUnit_det_middleBlock hb e s (W := W)
  have h1 : ∀ᵐ ω ∂Critical.collarLaw W b, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel
      (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X) *ᵥ q)).re =
      ENNReal.ofReal η⁻¹ * N ω := by
    filter_upwards [hHerm, hDinv] with ω hω hD
    rw [collar_poissonKernel_quad b e s hη hω.2.1 hω.2.2 hD hY q,
      collarRow_conjTranspose_mulVec b e s hω.2.1 q, Complex.ofReal_re,
      ENNReal.ofReal_mul (inv_nonneg.2 hη.le)]
  have h2 : ∀ᵐ ω ∂Critical.collarLaw W b, N ω = liminf (fun n => Nn n ω) atTop := by
    filter_upwards [hHerm, hDinv] with ω hω hD
    have hH := isUnit_det_collarMatrix b e s hω.2.1 hω.2.2 hD hY
    have ht := tendsto_inv_add_smul_I _ hH hεt
    have hc : Continuous fun M : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
        ENNReal.ofReal (-(star (rv ω) ⬝ᵥ (M *ᵥ rv ω)).im) :=
      ENNReal.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_const.dotProduct
        (continuous_id.matrix_mulVec continuous_const))).neg
    exact ((hc.tendsto _).comp ht).liminf_eq.symm
  -- each `ε`: split the phases
  set bad := {t : ℝ | d₁ < matchedDistance b e (Xh + (t : ℂ) • Y)}
  set Bn : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal Real.pi * (ENNReal.ofReal A +
    ENNReal.ofReal (εn n * K)) + ENNReal.ofReal m * ENNReal.ofReal B
  have h4 : ∀ n, ∫⁻ ω, Nn n ω ∂Critical.collarLaw W b ≤ Bn n := by
    intro n
    have hpt : ∀ᵐ ω ∂Critical.collarLaw W b, Nn n ω = ∫⁻ t, G n (t, ω) ∂stdCauchy := by
      filter_upwards [hHerm] with ω hω
      obtain ⟨hint, heq⟩ := neg_im_collarResolvent_eq_integral e' hω.2.1 hω.2.2
        hY.posSemidef (hεn n) (rv ω)
      simp only [Nn, G]
      rw [← heq, ofReal_integral_eq_lintegral_ofReal hint]
      refine Filter.Eventually.of_forall fun t => ?_
      have hHt := collarMatrix_isHermitian e' hω.2.1 hω.2.2 (dilatedOld_isHermitian X t)
      exact Density.im_dotProduct_inv_mulVec_nonneg' hHt (by simp [hεn n]) _
    have hsw : AEMeasurable (Function.uncurry fun (ω : Critical.CollarSample W) (t : ℝ) =>
        G n (t, ω)) ((Critical.collarLaw W b).prod stdCauchy) :=
      ((hG n).comp measurable_swap).aemeasurable
    rw [lintegral_congr_ae hpt, lintegral_lintegral_swap hsw]
    set T := toMeasurable stdCauchy bad
    have hT : MeasurableSet T := measurableSet_toMeasurable _ _
    have hphase : ∀ t, ∫⁻ ω, G n (t, ω) ∂Critical.collarLaw W b ≤
        ENNReal.ofReal Real.pi * (ENNReal.ofReal A + ENNReal.ofReal (εn n * K)) +
          T.indicator (fun _ => ENNReal.ofReal B) t := by
      intro t
      by_cases ht : t ∈ bad
      · refine le_add_left ?_
        rw [Set.indicator_of_mem (subset_toMeasurable _ _ ht)]
        exact Density.lintegral_im_resolvent_collarRow_le_sqrt hb0 hb hW e'
          (dilatedOld_isHermitian X t) (by simp [hεn n]) w q
      · refine le_add_right ?_
        have hgt := hgood t (not_lt.1 ht) (εn n) (hεn n)
        calc ∫⁻ ω, G n (t, ω) ∂Critical.collarLaw W b
            = ENNReal.ofReal Real.pi * ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (rv ω) ⬝ᵥ
                ((collarMatrix e' (Xh + (t : ℂ) • Y) ω - (⟨0, εn n⟩ : ℂ) • 1)⁻¹ *ᵥ rv ω)).im)
                ∂Critical.collarLaw W b := by
              rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              refine lintegral_congr fun ω => ?_
              simp only [G]
              rw [mk_zero_eq_mul_I, ← ENNReal.ofReal_mul Real.pi_pos.le, ← mul_assoc,
                mul_inv_cancel₀ Real.pi_pos.ne', one_mul]
          _ ≤ _ := by gcongr
    calc ∫⁻ t, ∫⁻ ω, G n (t, ω) ∂Critical.collarLaw W b ∂stdCauchy
        ≤ ∫⁻ t, (ENNReal.ofReal Real.pi * (ENNReal.ofReal A + ENNReal.ofReal (εn n * K)) +
            T.indicator (fun _ => ENNReal.ofReal B) t) ∂stdCauchy := lintegral_mono hphase
      _ = ENNReal.ofReal Real.pi * (ENNReal.ofReal A + ENNReal.ofReal (εn n * K)) +
            ENNReal.ofReal B * stdCauchy T := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_indicator_const hT]
      _ ≤ Bn n := by
          simp only [Bn]
          rw [measure_toMeasurable, mul_comm (ENNReal.ofReal B)]
          gcongr
  have hBlim : Tendsto Bn atTop (𝓝 (ENNReal.ofReal Real.pi * (ENNReal.ofReal A + 0) +
      ENNReal.ofReal m * ENNReal.ofReal B)) := by
    refine Tendsto.add_const _ (ENNReal.Tendsto.const_mul (Tendsto.const_add _ ?_) (Or.inr
      ENNReal.ofReal_ne_top))
    have : Tendsto (fun n => εn n * K) atTop (𝓝 (0 * K)) := hεt.mul_const K
    rw [zero_mul] at this
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp this
    rw [ENNReal.ofReal_zero] at h
    exact h
  calc ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s 0 ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b
      = ENNReal.ofReal η⁻¹ * ∫⁻ ω, N ω ∂Critical.collarLaw W b := by
        rw [lintegral_congr_ae h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal η⁻¹ * ∫⁻ ω, liminf (fun n => Nn n ω) atTop ∂Critical.collarLaw W b := by
        rw [lintegral_congr_ae h2]
    _ ≤ ENNReal.ofReal η⁻¹ * liminf (fun n => ∫⁻ ω, Nn n ω ∂Critical.collarLaw W b) atTop := by
        gcongr
        exact lintegral_liminf_le hNn
    _ ≤ ENNReal.ofReal η⁻¹ * liminf Bn atTop := by
        gcongr
        exact liminf_le_liminf (Eventually.of_forall h4)
    _ = ENNReal.ofReal η⁻¹ * (ENNReal.ofReal Real.pi * (ENNReal.ofReal A + 0) +
          ENNReal.ofReal m * ENNReal.ofReal B) := by rw [hBlim.liminf_eq]
    _ = _ := by
        rw [add_zero, ← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_mul hm,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (inv_nonneg.2 hη.le)]

end BlockBand.Critical.Collar.Kernel
