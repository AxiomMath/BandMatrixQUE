module

public import BlockBand.Critical.Collar.Kernel.RegularStrict

/-!
# The regular collar-kernel bound at positive height, from phase bounds

*Law.* `collarLaw W b`, `0 < b < 1/2`, `W ≥ 1`; `X` with `Y = -Im X ⪰ 0`; height `ν > 0`, shift `s`.

`lintegral_collarKernel_quad_le_height_phases`: the proof of `lintegral_collarKernel_quad_le_height`
(through `weightedBoundaryIdentity_general`, dilation at `ε = ν`) with the Cauchy phases split into
regular phases `d_e(X_t) ≤ d₁` (bound `A` for `E π⁻¹ Im⟨y,(ℋ_{X_t} - iν)⁻¹y⟩`) and exceptional phases
of Cauchy mass `≤ m` (fresh-row bound `C_{b,w}√W`):
`E Re q*𝒫(Ur)q ≤ η⁻¹(2(πA + m C_{b,w}√W‖q‖²) + 2ν‖q‖²)`.
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

theorem lintegral_collarKernel_quad_le_height_phases {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hW : 0 < W) (e s : ℝ) {ν : ℝ} (hν : 0 < ν) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    (q : Fin 2 × Fin W → ℂ) {d₁ A m : ℝ} (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hgood : ∀ t : ℝ, matchedDistance b e (rePart X + (t : ℂ) • (-Critical.imPart X)) ≤ d₁ →
      ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec
          (star (boundaryZ b e + Critical.collarShift e s ν)) q ω) ⬝ᵥ
        ((collarMatrix (e + s) (rePart X + (t : ℂ) • (-Critical.imPart X)) ω -
          (⟨0, ν⟩ : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ))⁻¹ *ᵥ
            collarRowVec (star (boundaryZ b e + Critical.collarShift e s ν)) q ω)).im)
          ∂Critical.collarLaw W b ≤ ENNReal.ofReal A)
    (hbad : stdCauchy {t : ℝ | d₁ < matchedDistance b e
      (rePart X + (t : ℂ) • (-Critical.imPart X))} ≤ ENNReal.ofReal m) :
    ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s ν ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b ≤
      ENNReal.ofReal ((boundaryZ b e).im⁻¹ * (2 * (Real.pi * A + m * (collarRowConst b
        (star (boundaryZ b e + Critical.collarShift e s ν)) * Real.sqrt W * ∑ x, ‖q x‖ ^ 2)) +
          2 * ν * ∑ x, ‖q x‖ ^ 2)) := by
  set η := (boundaryZ b e).im
  set e' := e + s
  set w := star (boundaryZ b e + Critical.collarShift e s ν)
  set rv := collarRowVec w q
  set Sq := ∑ x, ‖q x‖ ^ 2
  have hSq : 0 ≤ Sq := Finset.sum_nonneg fun _ _ => by positivity
  set B := collarRowConst b w * Real.sqrt W * Sq
  set Y := -Critical.imPart X
  set Xh := rePart X
  set N : Critical.CollarSample W → ℝ := fun ω =>
    -(star (rv ω) ⬝ᵥ ((heightMatrix e s ν X ω)⁻¹ *ᵥ rv ω)).im
  set G : ℝ × Critical.CollarSample W → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((star (rv p.2) ⬝ᵥ ((collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 -
      ((ν : ℂ) * Complex.I) • 1)⁻¹ *ᵥ rv p.2)).im)
  have hrv : Measurable rv := Density.measurable_collarRowVec w q
  have hG : Measurable G := by
    have hM : Measurable fun p : ℝ × Critical.CollarSample W =>
        collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((ν : ℂ) * Complex.I) • 1 := by
      have heq : (fun p : ℝ × Critical.CollarSample W =>
          collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((ν : ℂ) * Complex.I) • 1) =
          fun p => collarMatrix e' Xh p.2 - (p.1 : ℂ) • topLift Y - ((ν : ℂ) * Complex.I) • 1 := by
        funext p; rw [collarMatrix_add_right, topLift_smul]
      rw [heq]
      refine Measurable.of_eval_matrix _ fun i j => ?_
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine (((Matrix.measurable_apply).comp ((Density.measurable_collarMatrix e' Xh).comp
        measurable_snd)).sub ?_).sub measurable_const
      exact (Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const
    exact Density.measurable_ofReal_im_form hM (hrv.comp measurable_snd)
  have hHerm := Density.ae_collarMatrix_isHermitian b e' (rePart_isHermitian X) (W := W)
  -- pointwise bound
  have h1 : ∀ᵐ ω ∂Critical.collarLaw W b, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X) *ᵥ q)).re ≤
      ENNReal.ofReal η⁻¹ * (2 * ENNReal.ofReal (N ω) + ENNReal.ofReal (2 * ν * Sq)) := by
    filter_upwards [hHerm] with ω hω
    have hb := collar_poissonKernel_quad_le_height b e s hν hη hω.2.1 hω.2.2 hY q
    have hN : 0 ≤ N ω := by
      obtain ⟨hint, heq⟩ := neg_im_collarResolvent_eq_integral e' hω.2.1 hω.2.2 hY hν (rv ω)
      simp only [N, heightMatrix]
      rw [← heq]
      refine integral_nonneg fun t => ?_
      exact Density.im_dotProduct_inv_mulVec_nonneg'
        (collarMatrix_isHermitian e' hω.2.1 hω.2.2 (dilatedOld_isHermitian X t)) (by simp [hν]) _
    refine (ENNReal.ofReal_le_ofReal hb).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hη.le), ENNReal.ofReal_add (by positivity)
      (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  -- the `N` integral, split into regular and exceptional phases
  set bad := {t : ℝ | d₁ < matchedDistance b e (Xh + (t : ℂ) • Y)}
  have h4 : ∫⁻ ω, ENNReal.ofReal (N ω) ∂Critical.collarLaw W b ≤
      ENNReal.ofReal Real.pi * ENNReal.ofReal A + ENNReal.ofReal m * ENNReal.ofReal B := by
    have hpt : ∀ᵐ ω ∂Critical.collarLaw W b, ENNReal.ofReal (N ω) =
        ∫⁻ t, G (t, ω) ∂stdCauchy := by
      filter_upwards [hHerm] with ω hω
      obtain ⟨hint, heq⟩ := neg_im_collarResolvent_eq_integral e' hω.2.1 hω.2.2 hY hν (rv ω)
      simp only [N, G, heightMatrix]
      rw [← heq, ofReal_integral_eq_lintegral_ofReal hint]
      refine Filter.Eventually.of_forall fun t => ?_
      exact Density.im_dotProduct_inv_mulVec_nonneg'
        (collarMatrix_isHermitian e' hω.2.1 hω.2.2 (dilatedOld_isHermitian X t)) (by simp [hν]) _
    have hsw : AEMeasurable (Function.uncurry fun (ω : Critical.CollarSample W) (t : ℝ) =>
        G (t, ω)) ((Critical.collarLaw W b).prod stdCauchy) := (hG.comp measurable_swap).aemeasurable
    rw [lintegral_congr_ae hpt, lintegral_lintegral_swap hsw]
    set T := toMeasurable stdCauchy bad
    have hT : MeasurableSet T := measurableSet_toMeasurable _ _
    have hphase : ∀ t, ∫⁻ ω, G (t, ω) ∂Critical.collarLaw W b ≤
        ENNReal.ofReal Real.pi * ENNReal.ofReal A + T.indicator (fun _ => ENNReal.ofReal B) t := by
      intro t
      by_cases ht : t ∈ bad
      · refine le_add_left ?_
        rw [Set.indicator_of_mem (subset_toMeasurable _ _ ht)]
        exact Density.lintegral_im_resolvent_collarRow_le_sqrt hb0 hb hW e'
          (dilatedOld_isHermitian X t) (by simp [hν]) w q
      · refine le_add_right ?_
        have hgt := hgood t (not_lt.1 ht)
        calc ∫⁻ ω, G (t, ω) ∂Critical.collarLaw W b
            = ENNReal.ofReal Real.pi * ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (rv ω) ⬝ᵥ
                ((collarMatrix e' (Xh + (t : ℂ) • Y) ω - (⟨0, ν⟩ : ℂ) • 1)⁻¹ *ᵥ rv ω)).im)
                ∂Critical.collarLaw W b := by
              rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              refine lintegral_congr fun ω => ?_
              simp only [G]
              rw [mk_zero_eq_mul_I, ← ENNReal.ofReal_mul Real.pi_pos.le, ← mul_assoc,
                mul_inv_cancel₀ Real.pi_pos.ne', one_mul]
          _ ≤ _ := by gcongr
    calc ∫⁻ t, ∫⁻ ω, G (t, ω) ∂Critical.collarLaw W b ∂stdCauchy
        ≤ ∫⁻ t, (ENNReal.ofReal Real.pi * ENNReal.ofReal A +
            T.indicator (fun _ => ENNReal.ofReal B) t) ∂stdCauchy := lintegral_mono hphase
      _ = ENNReal.ofReal Real.pi * ENNReal.ofReal A + ENNReal.ofReal B * stdCauchy T := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_indicator_const hT]
      _ ≤ _ := by
          rw [measure_toMeasurable, mul_comm (ENNReal.ofReal B)]
          gcongr
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Density.collarRowConst_nonneg hb0.le _)
    (Real.sqrt_nonneg _)) hSq
  calc ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s ν ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal η⁻¹ * (2 * ENNReal.ofReal (N ω) + ENNReal.ofReal (2 * ν * Sq))
          ∂Critical.collarLaw W b := lintegral_mono_ae h1
    _ = ENNReal.ofReal η⁻¹ * (2 * ∫⁻ ω, ENNReal.ofReal (N ω) ∂Critical.collarLaw W b +
          ENNReal.ofReal (2 * ν * Sq)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (by simp), lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal η⁻¹ * (2 * (ENNReal.ofReal Real.pi * ENNReal.ofReal A +
          ENNReal.ofReal m * ENNReal.ofReal B) + ENNReal.ofReal (2 * ν * Sq)) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul Real.pi_pos.le, ← ENNReal.ofReal_mul hm,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (inv_nonneg.2 hη.le)]

end BlockBand.Critical.Collar.Kernel
