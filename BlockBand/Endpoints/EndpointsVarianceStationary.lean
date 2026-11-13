module

public import BlockBand.Endpoints.EndpointsVarianceBasic

/-!
# `EpStationaryWeightFree`: the limiting weighted intensity does not depend on `w`

**Theorem `epStationaryWeightFree_holds : EpStationaryWeightFree`** (no hypotheses).
For a law `𝖯` with `IsSpectrallyStationary`, a nonnegative bounded continuous mark
functional `Φ` and two spectral weights `w, w'`, `E_𝖯 Σ w(u)Φ(ν) = E_𝖯 Σ w'(u)Φ(ν)` in `[0, ∞]`.

Proof.
1. *Shift invariance in expectation* (`epv_stationary_shift`): for continuous compactly
   supported `g ≥ 0`, the variables `X = ∫ g(u + a)Φ(ν) dξ` and `Y = ∫ g(u)Φ(ν) dξ` have the same
   Laplace transform (stationarity at the nonnegative test `c·(g ⊗ Φ)`), hence the same
   expectation in `[0, ∞]` (`epv_lintegral_eq_of_laplace`).
2. *Convolution instead of Haar uniqueness*: with `J(w, w') = E Σ ∫ w'(a) w(u - a) Φ(ν) da`,
   `I(w) = ∫ w'(a) I(w(· - a)) da = J(w, w')` (step 1 and Tonelli, `epv_lintegral_swap`), and the
   substitution `a ↦ u - a` gives `J(w, w') = J(w', w)`. Hence `I(w) = J(w,w') = J(w',w) = I(w')`.

The unit-intensity hypothesis of `EpStationaryWeightFree` is not used (everything is in
`[0, ∞]`); the common value is `c = E Σ_{u ∈ [0,1)} Φ(ν)`, generally not `1`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction Pointwise

attribute [local instance] BlockBand.Model.Construction.massProfile_borelSpace

/-- The weighted statistic `I_Φ(g) = E_𝖯 Σ g(u)Φ(ν)` of a function `g` on `ℝ`. -/
def epv_weighted (P : ProbabilityMeasure MarkedPointMeasure) (g : ℝ → ℝ)
    (Φ : MassProfile →ᵇ ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (g x.1 * Φ x.2) ∂ξ.marked.measure ∂(P : Measure MarkedPointMeasure)

theorem epv_weighted_spectralWeight (P : ProbabilityMeasure MarkedPointMeasure)
    (w : SpectralWeight) (Φ : MassProfile →ᵇ ℝ) :
    epv_weighted P w Φ = ep_limitOneMark P w Φ := rfl

/-- **Shift invariance in expectation**: `I_Φ(g(· + a)) = I_Φ(g)` for continuous compactly supported
`g ≥ 0`. -/
theorem epv_stationary_shift {P : ProbabilityMeasure MarkedPointMeasure}
    (hP : IsSpectrallyStationary P) {Φ : MassProfile →ᵇ ℝ} (hΦ : ∀ ν, 0 ≤ Φ ν) {g : ℝ → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) (a : ℝ) :
    epv_weighted P (fun u => g (u + a)) Φ = epv_weighted P g Φ := by
  set f : MarkedSpectralSpace → ℝ := fun z => g z.1 * Φ z.2 with hf
  have hfc : Continuous f := (hg.comp continuous_fst).mul (Φ.continuous.comp continuous_snd)
  obtain ⟨K, hK, hKs⟩ : ∃ K : Set ℝ, IsCompact K ∧ ∀ u, u ∉ K → g u = 0 :=
    ⟨tsupport g, hgs, fun u hu => image_eq_zero_of_notMem_tsupport hu⟩
  have hfs : HasCompactSupport f :=
    epv_hasCompactSupport_of_fst hK fun z hz => by simp [hf, hKs _ hz]
  have hf0 : ∀ z, 0 ≤ f z := fun z => mul_nonneg (hg0 _) (hΦ _)
  set fa : MarkedSpectralSpace → ℝ := fun z => f (z.1 + a, z.2) with hfa
  have hfac : Continuous fa := hfc.comp ((continuous_fst.add continuous_const).prodMk
    continuous_snd)
  have hKa : IsCompact ((fun u => u + a) ⁻¹' K) := by
    have : (fun u => u + a) ⁻¹' K = (Homeomorph.addRight a).symm '' K := by
      ext u; simp [Homeomorph.addRight]
    rw [this]; exact hK.image (Homeomorph.continuous _)
  have hfas : HasCompactSupport fa :=
    epv_hasCompactSupport_of_fst hKa fun z hz => by simp [hfa, hf, hKs _ hz]
  have hfa0 : ∀ z, 0 ≤ fa z := fun z => hf0 _
  unfold epv_weighted
  rw [show (fun ξ : MarkedPointMeasure => ∫⁻ x, ENNReal.ofReal (g (x.1 + a) * Φ x.2)
      ∂ξ.marked.measure) = fun ξ => ENNReal.ofReal (epv_markedIntegral fa ξ) from
    funext fun ξ => epv_lintegral_marked_eq hfac hfas hfa0 ξ,
    show (fun ξ : MarkedPointMeasure => ∫⁻ x, ENNReal.ofReal (g x.1 * Φ x.2)
      ∂ξ.marked.measure) = fun ξ => ENNReal.ofReal (epv_markedIntegral f ξ) from
    funext fun ξ => epv_lintegral_marked_eq hfc hfs hf0 ξ]
  refine epv_lintegral_eq_of_laplace (P : Measure MarkedPointMeasure)
    (epv_measurable_markedIntegral hfac hfas) (epv_measurable_markedIntegral hfc hfs)
    (epv_markedIntegral_nonneg hfa0) (epv_markedIntegral_nonneg hf0) fun c hc => ?_
  let F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ :=
    ⟨⟨fun z => c * f z, continuous_const.mul hfc⟩, hfs.mul_left⟩
  have hst := hP a F fun z => mul_nonneg hc.le (hf0 z)
  have e1 : ∀ ξ : MarkedPointMeasure, ∫ z, F (z.1 + a, z.2) ∂ξ.marked.measure =
      c * epv_markedIntegral fa ξ := fun ξ => integral_const_mul _ _
  have e2 : ∀ ξ : MarkedPointMeasure, ∫ z, F z ∂ξ.marked.measure =
      c * epv_markedIntegral f ξ := fun ξ => integral_const_mul _ _
  simp_rw [e1, e2] at hst
  exact hst

/-- The bound and support of a spectral weight. -/
theorem epv_spectralWeight_bound (w : SpectralWeight) : ∃ C, ∀ u, w u ≤ C := by
  obtain ⟨C, hC⟩ := w.toContinuousMap.continuous.bounded_above_of_compact_support w.compactSupport
  exact ⟨C, fun u => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC u)⟩

theorem epv_lintegral_spectralWeight (w : SpectralWeight) :
    ∫⁻ a, ENNReal.ofReal (w a) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (w.toContinuousMap.continuous.integrable_of_hasCompactSupport w.compactSupport)
    (Eventually.of_forall w.nonnegative)]
  change ENNReal.ofReal (∫ x, w.toContinuousMap x) = 1
  rw [w.integral_eq_one, ENNReal.ofReal_one]

/-- The convolution statistic `J(w, w') = E Σ ∫ w'(a) w(u - a) Φ(ν) da`. -/
def epv_convolved (P : ProbabilityMeasure MarkedPointMeasure) (w w' : SpectralWeight)
    (Φ : MassProfile →ᵇ ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ, ∫⁻ x, ∫⁻ a, ENNReal.ofReal (w' a * w (x.1 - a) * Φ x.2) ∂volume ∂ξ.marked.measure
    ∂(P : Measure MarkedPointMeasure)

/-- `I(w) = J(w, w')`, by shift invariance and Tonelli. -/
theorem epv_weighted_eq_convolved {P : ProbabilityMeasure MarkedPointMeasure}
    (hP : IsSpectrallyStationary P) {Φ : MassProfile →ᵇ ℝ} (hΦ : ∀ ν, 0 ≤ Φ ν)
    (w w' : SpectralWeight) : ep_limitOneMark P w Φ = epv_convolved P w w' Φ := by
  have hw := w.toContinuousMap.continuous
  have hw' := w'.toContinuousMap.continuous
  have hshift : ∀ a : ℝ, epv_weighted P (fun u => w (u - a)) Φ = ep_limitOneMark P w Φ := by
    intro a
    have := epv_stationary_shift hP hΦ hw w.compactSupport w.nonnegative (-a)
    rw [show (fun u => w (u - a)) = fun u => w (u + -a) from
      funext fun u => by rw [sub_eq_add_neg]]
    exact this
  obtain ⟨Cw, hCw⟩ := epv_spectralWeight_bound w
  obtain ⟨Cw', hCw'⟩ := epv_spectralWeight_bound w'
  have hK : IsCompact (tsupport (w' : ℝ → ℝ) + tsupport (w : ℝ → ℝ)) :=
    IsCompact.add w'.compactSupport w.compactSupport
  calc ep_limitOneMark P w Φ
      = ∫⁻ a, ENNReal.ofReal (w' a) * ep_limitOneMark P w Φ := by
        rw [lintegral_mul_const _ (show Measurable fun a => ENNReal.ofReal (w' a) from
            ENNReal.measurable_ofReal.comp hw'.measurable),
          epv_lintegral_spectralWeight, one_mul]
    _ = ∫⁻ a, ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (w' a * w (x.1 - a) * Φ x.2) ∂ξ.marked.measure
          ∂(P : Measure MarkedPointMeasure) := by
        refine lintegral_congr fun a => ?_
        rw [← hshift a, epv_weighted, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ξ => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul (w'.nonnegative a), mul_assoc]
    _ = epv_convolved P w w' Φ :=
        epv_lintegral_swap volume P (fun a x => w' a * w (x.1 - a) * Φ x.2) hK
          (Cw' * Cw * ‖Φ‖)
          (fun a => (continuous_const.mul (hw.comp (continuous_fst.sub continuous_const))).mul
            (Φ.continuous.comp continuous_snd))
          (fun x => ((hw'.mul (hw.comp (continuous_const.sub continuous_id))).mul
            continuous_const))
          (fun a x => mul_nonneg (mul_nonneg (w'.nonnegative a) (w.nonnegative _)) (hΦ _))
          (fun a x hx => by
            by_contra hne
            have h1 : w' a ≠ 0 := fun h => hne (by simp [h])
            have h2 : w (x.1 - a) ≠ 0 := fun h => hne (by simp [h])
            exact hx (by
              have := add_mem_add (subset_tsupport _ h1) (subset_tsupport _ h2)
              simpa using this))
          (fun a x => by
            have h1 := hCw' a
            have h2 := hCw (x.1 - a)
            have h3 : Φ x.2 ≤ ‖Φ‖ := (le_abs_self _).trans
              (by simpa [Real.norm_eq_abs] using Φ.norm_coe_le_norm x.2)
            have h0w' := w'.nonnegative a
            have h0w := w.nonnegative (x.1 - a)
            have h0Φ := hΦ x.2
            have hCw0 : 0 ≤ Cw := h0w.trans h2
            have hCw0' : 0 ≤ Cw' := h0w'.trans h1
            calc w' a * w (x.1 - a) * Φ x.2 ≤ Cw' * Cw * Φ x.2 := by gcongr
              _ ≤ Cw' * Cw * ‖Φ‖ := by gcongr)

/-- `J(w, w') = J(w', w)` (substitution `a ↦ u - a` in the inner integral). -/
theorem epv_convolved_comm (P : ProbabilityMeasure MarkedPointMeasure) (w w' : SpectralWeight)
    (Φ : MassProfile →ᵇ ℝ) : epv_convolved P w w' Φ = epv_convolved P w' w Φ := by
  unfold epv_convolved
  refine lintegral_congr fun ξ => lintegral_congr fun x => ?_
  have := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
    (fun b => ENNReal.ofReal (w b * w' (x.1 - b) * Φ x.2)) x.1
  rw [← this]
  refine lintegral_congr fun a => ?_
  simp only [sub_sub_cancel]
  ring_nf

/-- **`EpStationaryWeightFree`**: for a spectrally stationary law, the limiting statistic
`E_𝖯 Σ w(u)Φ(ν)` of a nonnegative bounded continuous mark functional is the same for every
spectral weight `w`. -/
theorem epStationaryWeightFree_holds : EpStationaryWeightFree := by
  intro P hP _ Φ hΦ w w'
  rw [epv_weighted_eq_convolved hP hΦ w w', epv_weighted_eq_convolved hP hΦ w' w,
    epv_convolved_comm]

end BlockBand.Endpoints
