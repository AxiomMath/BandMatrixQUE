module

public import BlockBand.Endpoints.EndpointsVarianceStationary
public import BlockBand.Endpoints.EndpointsAssembly

/-!
# `EpRotationFourierDiagonal`: rotation invariance diagonalizes the Fourier covariance

**Theorem `epRotationFourierDiagonal_holds : EpRotationFourierDiagonal`** (proved, no
hypotheses). For a law `𝖯` with `IsMarkRotationInvariant`, every spectral weight `w`
and every profile test `φ`,
`V_𝖯(w,φ) = Σ_{m ≠ 0} |φ̂_m|² E_𝖯 Σ w(u)|ν(e_m)|²` in `[0, ∞]`.

Proof (a rotation average replaces the expansion of the square and the off-diagonal
cancellation of the paper's proof; no Fourier decay or summability is needed because everything
is in `[0, ∞]`).
1. *Rotation invariance in expectation* (`epv_rotation_expectation`): for a nonnegative bounded
   continuous `Ψ`, `E Σ w(u)Ψ(R_aν) = E Σ w(u)Ψ(ν)` for every `a ∈ 𝕋` (equal Laplace transforms,
   `epv_lintegral_eq_of_laplace`).
2. *Average over `a`* with the Haar probability of `𝕋`, and exchange `∫ da`, `E` and `Σ_{x∈ξ}`
   (Tonelli, `epv_lintegral_swap`): `V_𝖯(w,φ) = E Σ w(u) ∫ |(R_aν)(φ) - φ̄|² da`.
3. *Parseval in `a`* (`epv_lintegral_rot_profile`): `a ↦ (R_aν)(φ) - φ̄ = ∫ φ(a + r) ν(dr) - φ̄`
   has Fourier coefficients `φ̂_m ν(e_m)` for `m ≠ 0` and `0` for `m = 0`, so
   `∫ |(R_aν)(φ) - φ̄|² da = Σ_{m≠0} |φ̂_m|² |ν(e_m)|²`.
4. Exchange `E Σ` with `Σ_m` (`lintegral_tsum`).

The unit-intensity hypothesis of `EpRotationFourierDiagonal` is not used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.WindowAngular (markVariance modeVariance)
open AddCircle (haarAddCircle)
open scoped ENNReal BoundedContinuousFunction

attribute [local instance] BlockBand.Model.Construction.massProfile_borelSpace

/-!
## 1. Rotations of a mass profile
-/

/-- The rotated mass profile `R_aν = ν ∘ (a + ·)⁻¹`, as in `IsMarkRotationInvariant`. -/
abbrev epv_rot (a : Torus) (ν : MassProfile) : MassProfile := ν.map (Homeomorph.addLeft a)

theorem epv_continuous_rot (a : Torus) : Continuous (epv_rot a) :=
  ProbabilityMeasure.continuous_map (Homeomorph.addLeft a).continuous

theorem epv_integral_rot (a : Torus) (ν : MassProfile) {f : Torus → ℝ} (hf : Continuous f) :
    ∫ r, f r ∂(epv_rot a ν : Measure Torus) = ∫ r, f (a + r) ∂(ν : Measure Torus) := by
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    (Homeomorph.addLeft a).continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  rfl

theorem epv_continuous_translate_integral {f : Torus → ℝ} (hf : Continuous f) (ν : MassProfile) :
    Continuous fun a : Torus => ∫ r, f (a + r) ∂(ν : Measure Torus) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace f)
  exact continuous_of_dominated (bound := fun _ => C)
    (fun a => (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (fun a => Eventually.of_forall fun r => hC _) (integrable_const C)
    (Eventually.of_forall fun r => hf.comp (continuous_id.add continuous_const))

/-!
## 2. Rotation invariance in expectation
-/

/-- **Step 1.** Rotation invariance of the marked Laplace functional gives rotation invariance of
the mean weighted mark statistics, in `[0, ∞]`. -/
theorem epv_rotation_expectation {P : ProbabilityMeasure MarkedPointMeasure}
    (hP : IsMarkRotationInvariant P) {g : ℝ → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) {Ψ : MassProfile →ᵇ ℝ} (hΨ : ∀ ν, 0 ≤ Ψ ν) (a : Torus) :
    ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (g x.1 * Ψ (epv_rot a x.2)) ∂ξ.marked.measure
        ∂(P : Measure MarkedPointMeasure) =
      ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (g x.1 * Ψ x.2) ∂ξ.marked.measure
        ∂(P : Measure MarkedPointMeasure) := by
  set f : MarkedSpectralSpace → ℝ := fun z => g z.1 * Ψ z.2 with hf
  have hfc : Continuous f := (hg.comp continuous_fst).mul (Ψ.continuous.comp continuous_snd)
  obtain ⟨K, hK, hKs⟩ : ∃ K : Set ℝ, IsCompact K ∧ ∀ u, u ∉ K → g u = 0 :=
    ⟨tsupport g, hgs, fun u hu => image_eq_zero_of_notMem_tsupport hu⟩
  have hfs : HasCompactSupport f :=
    epv_hasCompactSupport_of_fst hK fun z hz => by simp [hf, hKs _ hz]
  have hf0 : ∀ z, 0 ≤ f z := fun z => mul_nonneg (hg0 _) (hΨ _)
  set fa : MarkedSpectralSpace → ℝ := fun z => f (z.1, epv_rot a z.2) with hfa
  have hfac : Continuous fa :=
    hfc.comp (continuous_fst.prodMk ((epv_continuous_rot a).comp continuous_snd))
  have hfas : HasCompactSupport fa :=
    epv_hasCompactSupport_of_fst hK fun z hz => by simp [hfa, hf, hKs _ hz]
  have hfa0 : ∀ z, 0 ≤ fa z := fun z => hf0 _
  rw [show (fun ξ : MarkedPointMeasure => ∫⁻ x, ENNReal.ofReal (g x.1 * Ψ (epv_rot a x.2))
      ∂ξ.marked.measure) = fun ξ => ENNReal.ofReal (epv_markedIntegral fa ξ) from
    funext fun ξ => epv_lintegral_marked_eq hfac hfas hfa0 ξ,
    show (fun ξ : MarkedPointMeasure => ∫⁻ x, ENNReal.ofReal (g x.1 * Ψ x.2)
      ∂ξ.marked.measure) = fun ξ => ENNReal.ofReal (epv_markedIntegral f ξ) from
    funext fun ξ => epv_lintegral_marked_eq hfc hfs hf0 ξ]
  refine epv_lintegral_eq_of_laplace (P : Measure MarkedPointMeasure)
    (epv_measurable_markedIntegral hfac hfas) (epv_measurable_markedIntegral hfc hfs)
    (epv_markedIntegral_nonneg hfa0) (epv_markedIntegral_nonneg hf0) fun c hc => ?_
  let F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ :=
    ⟨⟨fun z => c * f z, continuous_const.mul hfc⟩, hfs.mul_left⟩
  have hst := hP a F fun z => mul_nonneg hc.le (hf0 z)
  have e1 : ∀ ξ : MarkedPointMeasure,
      ∫ z, F (z.1, z.2.map (Homeomorph.addLeft a)) ∂ξ.marked.measure =
        c * epv_markedIntegral fa ξ := fun ξ => integral_const_mul _ _
  have e2 : ∀ ξ : MarkedPointMeasure, ∫ z, F z ∂ξ.marked.measure =
      c * epv_markedIntegral f ξ := fun ξ => integral_const_mul _ _
  simp_rw [e1, e2] at hst
  exact hst

/-!
## 3. Parseval for the rotation average
-/

/-- The character identity `e_{-m}(b - r) = e_{-m}(b) e_m(r)`. -/
theorem epv_fourier_sub (m : ℤ) (b r : Torus) :
    fourier (-m) (b - r) = fourier (-m) b * fourier m r := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_sub, sub_eq_add_neg, ← neg_smul,
    neg_neg, AddCircle.toCircle_add, Circle.coe_mul]

/-- The inner Fourier integral of a translate: `∫ e_{-m}(a) φ(a + r) da = e_m(r) φ̂_m`. -/
theorem epv_fourier_translate (φ : Torus → ℝ) (m : ℤ) (r : Torus) :
    ∫ a, fourier (-m) a * ((φ (a + r) : ℝ) : ℂ) ∂haarAddCircle =
      fourier m r * fourierCoeff (fun t : Torus => ((φ t : ℝ) : ℂ)) m := by
  have := integral_add_right_eq_self (μ := (haarAddCircle : Measure Torus))
    (fun b => fourier (-m) (b - r) * ((φ b : ℝ) : ℂ)) r
  simp only [add_sub_cancel_right] at this
  rw [this, fourierCoeff, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [epv_fourier_sub, smul_eq_mul]
  ring

/-- The Fourier coefficients of `a ↦ ∫ φ(a + r) ν(dr)`: `φ̂_m ν(e_m)`. -/
theorem epv_fourierCoeff_translate {φ : Torus → ℝ} (hφ : Continuous φ) (ν : MassProfile)
    (m : ℤ) :
    fourierCoeff (fun a : Torus => ∫ r, ((φ (a + r) : ℝ) : ℂ) ∂(ν : Measure Torus)) m =
      fourierCoeff (fun t : Torus => ((φ t : ℝ) : ℂ)) m *
        ∫ r, fourier m r ∂(ν : Measure Torus) := by
  have hcont : Continuous (Function.uncurry fun (a r : Torus) =>
      fourier (-m) a * ((φ (a + r) : ℝ) : ℂ)) :=
    ((fourier (-m)).continuous.comp continuous_fst).mul
      (Complex.continuous_ofReal.comp (hφ.comp (continuous_fst.add continuous_snd)))
  rw [fourierCoeff]
  simp_rw [smul_eq_mul, ← integral_const_mul]
  rw [integral_integral_swap (hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  simp_rw [epv_fourier_translate φ m]
  rw [integral_mul_const, integral_const_mul]
  ring

theorem epv_fourierCoeff_zero (φ : Torus → ℝ) :
    fourierCoeff (fun t : Torus => ((φ t : ℝ) : ℂ)) 0 = ((∫ r, φ r : ℝ) : ℂ) := by
  rw [fourierCoeff]
  simp only [neg_zero, fourier_zero, one_smul]
  rw [integral_complex_ofReal]
  congr 1
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- **Step 3 (Parseval).** For every mass profile `ν`,
`∫ |(R_aν)(φ) - φ̄|² da = Σ_{m≠0} |φ̂_m|² |ν(e_m)|²` in `[0, ∞]`. -/
theorem epv_lintegral_rot_profile (φ : ProfileTest) (ν : MassProfile) :
    ∫⁻ a, ENNReal.ofReal (ep_profileFunctional φ (epv_rot a ν)) ∂haarAddCircle =
      ∑' m : ℤ, if m = 0 then 0 else
        ENNReal.ofReal (‖fourierCoeff (fun r : Torus => ((φ r : ℝ) : ℂ)) m‖ ^ 2) *
          ENNReal.ofReal (‖∫ r, fourier m r ∂(ν : Measure Torus)‖ ^ 2) := by
  have hφ : Continuous (φ : Torus → ℝ) := φ.toContinuousMap.continuous
  set φbar : ℝ := ∫ r, φ r with hφbar
  set s : Torus → ℂ := fun a => ∫ r, ((φ (a + r) : ℝ) : ℂ) ∂(ν : Measure Torus) with hs
  have hsr : ∀ a, s a = ((∫ r, φ (a + r) ∂(ν : Measure Torus) : ℝ) : ℂ) := fun a =>
    integral_complex_ofReal
  have hsc : Continuous s := by
    have : s = fun a => ((∫ r, φ (a + r) ∂(ν : Measure Torus) : ℝ) : ℂ) := funext hsr
    rw [this]
    exact Complex.continuous_ofReal.comp (epv_continuous_translate_integral hφ ν)
  let c : ℂ := (φbar : ℂ)
  let g : C(Torus, ℂ) := ⟨fun a => s a + (-c) • fourier (T := 1) 0 a,
    hsc.add ((fourier (T := 1) 0).continuous.const_smul (-c))⟩
  have hg : ∀ a, ep_profileFunctional φ (epv_rot a ν) = ‖g a‖ ^ 2 := by
    intro a
    rw [ep_profileFunctional_apply, epv_integral_rot a ν hφ]
    have : g a = ((∫ r, φ (a + r) ∂(ν : Measure Torus) - φbar : ℝ) : ℂ) := by
      change s a + (-c) • fourier (T := 1) 0 a = _
      rw [hsr, fourier_zero, smul_eq_mul, mul_one, Complex.ofReal_sub]
      ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  -- the Fourier coefficients of `g`
  have hsi : Integrable s haarAddCircle :=
    hsc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (fun a => (-c) • fourier (T := 1) 0 a) haarAddCircle :=
    ((fourier (T := 1) 0).continuous.const_smul (-c)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hν1 : ∫ r, fourier (T := 1) 0 r ∂(ν : Measure Torus) = 1 := by
    simp
  have hcoef : ∀ m : ℤ, fourierCoeff g m = if m = 0 then 0 else
      fourierCoeff (fun r : Torus => ((φ r : ℝ) : ℂ)) m * ∫ r, fourier m r ∂(ν : Measure Torus) := by
    intro m
    have hadd := congrFun (fourierCoeff.add hsi hgi) m
    have hsm := fourierCoeff.const_smul (fun r => fourier (T := 1) 0 r) (-c) m
    have hF := congrFun (fourierCoeff_fourier (T := 1) 0) m
    have hg' : fourierCoeff g m = fourierCoeff s m +
        (-c) • fourierCoeff (⇑(fourier (T := 1) 0)) m :=
      hadd.trans (by rw [Pi.add_apply]; exact congrArg _ hsm)
    rw [hg', hF, hs, epv_fourierCoeff_translate hφ ν m]
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [↓reduceIte, Pi.single_eq_same, smul_eq_mul, mul_one, hν1,
        epv_fourierCoeff_zero φ, c]
      ring
    · simp [hm]
  -- Parseval
  have hpars := hasSum_sq_fourierCoeff (T := 1) (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g)
  simp only [fourierCoeff_toLp] at hpars
  have hae : (fun t => ‖(ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g) t‖ ^ 2)
      =ᵐ[haarAddCircle] fun t => ‖g t‖ ^ 2 := by
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2) haarAddCircle g] with t ht
    rw [ht]
  rw [integral_congr_ae hae] at hpars
  have hgc : Continuous fun t => ‖g t‖ ^ 2 := g.continuous.norm.pow 2
  have hint : Integrable (fun t => ‖g t‖ ^ 2) haarAddCircle :=
    hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [hg]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => by positivity),
    ← hpars.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hpars.summable]
  refine tsum_congr fun m => ?_
  rw [hcoef m]
  split_ifs
  · simp
  · rw [norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity)]

/-!
## 4. The diagonalization
-/

theorem epv_measurable_weighted (w : SpectralWeight) {Ψ : MassProfile →ᵇ ℝ}
    (hΨ : ∀ ν, 0 ≤ Ψ ν) :
    Measurable fun ξ : MarkedPointMeasure =>
      ∫⁻ x, ENNReal.ofReal (w x.1 * Ψ x.2) ∂ξ.marked.measure := by
  obtain ⟨hc, hcs⟩ := epv_weight_product_props w Ψ
  have h0 : ∀ x : MarkedSpectralSpace, 0 ≤ w x.1 * Ψ x.2 := fun x =>
    mul_nonneg (w.nonnegative _) (hΨ _)
  rw [funext fun ξ => epv_lintegral_marked_eq hc hcs h0 ξ]
  exact ENNReal.measurable_ofReal.comp (epv_measurable_markedIntegral hc hcs)

/-- **`EpRotationFourierDiagonal`**: for a law invariant under simultaneous rotation of the
marks, every spectral weight `w` and every profile test `φ`,
`V_𝖯(w,φ) = Σ_{m≠0} |φ̂_m|² v_{-m}(𝖯)` in `[0, ∞]`, with `v_{-m}` the `modeVariance`
(integrand `|ν(e_m)|²`). -/
theorem epRotationFourierDiagonal_holds : EpRotationFourierDiagonal := by
  intro P hP _ w φ
  have hw := w.toContinuousMap.continuous
  have hφ : Continuous (φ : Torus → ℝ) := φ.toContinuousMap.continuous
  set F := ep_profileFunctional φ with hFdef
  have hF0 : ∀ ν, 0 ≤ F ν := ep_profileFunctional_nonneg φ
  obtain ⟨Cw, hCw⟩ := epv_spectralWeight_bound w
  set c : ℤ → ℝ≥0∞ := fun m =>
    ENNReal.ofReal (‖fourierCoeff (fun r : Torus => ((φ r : ℝ) : ℂ)) m‖ ^ 2) with hc
  have hrotc : ∀ ν : MassProfile, Continuous fun a : Torus => F (epv_rot a ν) := by
    intro ν
    have : (fun a : Torus => F (epv_rot a ν)) =
        fun a => |(∫ r, φ (a + r) ∂(ν : Measure Torus)) - ∫ r, φ r| ^ 2 := by
      funext a
      rw [hFdef, ep_profileFunctional_apply, epv_integral_rot a ν hφ]
    rw [this]
    exact ((epv_continuous_translate_integral hφ ν).sub continuous_const).abs.pow 2
  calc markVariance P w φ
      = ∫⁻ _a, markVariance P w φ ∂haarAddCircle := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ a, ∫⁻ ξ, ∫⁻ x, ENNReal.ofReal (w x.1 * F (epv_rot a x.2)) ∂ξ.marked.measure
          ∂(P : Measure MarkedPointMeasure) ∂haarAddCircle :=
        lintegral_congr fun a =>
          (epv_rotation_expectation hP hw w.compactSupport w.nonnegative hF0 a).symm
    _ = ∫⁻ ξ, ∫⁻ x, ∫⁻ a, ENNReal.ofReal (w x.1 * F (epv_rot a x.2)) ∂haarAddCircle
          ∂ξ.marked.measure ∂(P : Measure MarkedPointMeasure) :=
        epv_lintegral_swap haarAddCircle P (fun a x => w x.1 * F (epv_rot a x.2))
          w.compactSupport (Cw * ‖F‖)
          (fun a => (hw.comp continuous_fst).mul
            (F.continuous.comp ((epv_continuous_rot a).comp continuous_snd)))
          (fun x => continuous_const.mul (hrotc x.2))
          (fun a x => mul_nonneg (w.nonnegative _) (hF0 _))
          (fun a x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
          (fun a x => by
            have h1 := hCw x.1
            have h3 : F (epv_rot a x.2) ≤ ‖F‖ := (le_abs_self _).trans
              (by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (epv_rot a x.2))
            have h0w := w.nonnegative x.1
            have h0F := hF0 (epv_rot a x.2)
            have hCw0 : 0 ≤ Cw := h0w.trans h1
            calc w x.1 * F (epv_rot a x.2) ≤ Cw * F (epv_rot a x.2) := by gcongr
              _ ≤ Cw * ‖F‖ := by gcongr)
    _ = ∫⁻ ξ, ∫⁻ x, ∑' m : ℤ, (if m = 0 then 0 else
          c m * ENNReal.ofReal (w x.1 * rvFourierTest m x.2)) ∂ξ.marked.measure
          ∂(P : Measure MarkedPointMeasure) := by
        refine lintegral_congr fun ξ => lintegral_congr fun x => ?_
        simp_rw [ENNReal.ofReal_mul (w.nonnegative x.1)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, epv_lintegral_rot_profile φ x.2,
          ← ENNReal.tsum_mul_left]
        refine tsum_congr fun m => ?_
        split_ifs
        · simp
        · change _ = c m * (ENNReal.ofReal (w x.1) *
            ENNReal.ofReal (‖∫ r, fourier m r ∂(x.2 : Measure Torus)‖ ^ 2))
          ring
    _ = ∑' m : ℤ, if m = 0 then 0 else c m * modeVariance P w (-m) := by
        have hmx : ∀ (m : ℤ) (ξ : MarkedPointMeasure), Measurable fun x : MarkedSpectralSpace =>
            (if m = 0 then 0 else c m * ENNReal.ofReal (w x.1 * rvFourierTest m x.2)) := by
          intro m ξ
          split_ifs
          · exact measurable_const
          · exact measurable_const.mul (ENNReal.measurable_ofReal.comp
              (epv_weight_product_props w (rvFourierTest m)).1.measurable)
        simp_rw [fun ξ : MarkedPointMeasure => lintegral_tsum
          (μ := ξ.marked.measure) fun m => (hmx m ξ).aemeasurable]
        rw [lintegral_tsum fun m => ?_]
        · refine tsum_congr fun m => ?_
          split_ifs with hm
          · simp
          · have hcm : c m ≠ ∞ := ENNReal.ofReal_ne_top
            rw [ep_modeVariance_eq, neg_neg, ep_limitOneMark, ← lintegral_const_mul' _ _ hcm]
            refine lintegral_congr fun ξ => ?_
            rw [lintegral_const_mul' _ _ hcm]
        · refine Measurable.aemeasurable ?_
          by_cases hm : m = 0
          · simp only [hm, ↓reduceIte, lintegral_zero]; exact measurable_const
          · have hcm : c m ≠ ∞ := ENNReal.ofReal_ne_top
            simp only [hm, ↓reduceIte]
            simp_rw [lintegral_const_mul' _ _ hcm]
            exact measurable_const.mul (epv_measurable_weighted w (ep_rvFourierTest_nonneg m))

end BlockBand.Endpoints
