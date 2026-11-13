module

public import BlockBand.SourceProcess.PhysApprox.B3Jet1Main
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# One closing-shift estimate for both closed jets (Cauchy estimate)

The closing shift of the normalized near trace is a function of the boundary parameter `w`:
`Δ_y(w) = f(X_cl(y), w) - f(X_{n_s}(y), w)`, `f(X, w) = W⁻¹Tr(w - X)⁻¹` (`stieltjes`). For
passive inputs it is holomorphic on `Im w > 0`. `ClosedJetShiftStartLp` is its value at
`w = z_∂`; `ClosedJet1ShiftLp` is its `w`-derivative at `z_∂`. One estimate gives both:

* **`ClosedJetShiftNbhdLp`**, stated as a hypothesis: for every `p ≥ 1` there are `r > 0` and `C`
  with `‖Δ(w)‖_{L^p(closedLaw)} ≤ C/W` **uniformly for `|w - z_∂| ≤ r`**, eventually in `W`, at
  the closing time `n_s` (whole space). At `w = z_∂` this is `ClosedJetShiftStartLp b3ClosedX`
  (`closedJetShiftStartLp_of_nbhd`).
* **`closedJet1ShiftLp_of_nbhd`**: this estimate and the passivity of `b3ClosedX` at `n_s` give
  `ClosedJet1ShiftLp`, with constant `C/ρ`, `ρ = min(r, Im z_∂/2)`. The proof: Cauchy's formula
  for the derivative on the circle `|w - z_∂| = ρ` (`Complex.cderiv_eq_deriv`) gives
  `|Δ'(z_∂)| ≤ ρ⁻¹ ∫|Δ(z_∂ + ρe^{iθ})| dθ/2π` pointwise (`norm_cderiv_le_phase`); then Jensen and
  Tonelli move the `L^p` norm inside the `θ`-average (`eLpNorm_integral_le_of_forall`).

So only the value of the shift is assumed, on a fixed disc; the derivative costs nothing.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet1

open MeasureTheory Filter Topology Matrix Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PathJet
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open scoped ENNReal ComplexOrder

/-!
## The `L^p` norm of an average (Jensen + Tonelli)
-/

/-- **`L^p` norm of an average**: if `‖G(·, θ)‖_{L^p(μ)} ≤ c` for every `θ`, then
`‖∫ G(·, θ) dν(θ)‖_{L^p(μ)} ≤ c` for a probability `ν`. -/
theorem eLpNorm_integral_le_of_forall {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure Ω) [SFinite μ] (ν : Measure Θ) [IsProbabilityMeasure ν] {G : Ω → Θ → ℝ}
    (hG : Measurable (Function.uncurry G)) {p c : ℝ} (hp : 1 ≤ p)
    (h : ∀ θ, eLpNorm (fun ω => G ω θ) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal c) :
    eLpNorm (fun ω => ∫ θ, G ω θ ∂ν) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal c := by
  have hp0 : 0 < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hqt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsec : ∀ ω, Measurable fun θ => G ω θ := fun ω => hG.comp measurable_prodMk_left
  have hsec' : ∀ θ, Measurable fun ω => G ω θ := fun θ =>
    hG.comp (measurable_id.prodMk measurable_const)
  have hI : Measurable fun ω => ∫ θ, G ω θ ∂ν :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hI.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le, one_div, ENNReal.rpow_inv_le_iff hp0]
  have hθ : ∀ θ, ∫⁻ ω, ‖G ω θ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal c ^ p := fun θ => by
    have h1 := h θ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt (hsec' θ).aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le, one_div, ENNReal.rpow_inv_le_iff hp0] at h1
    exact h1
  have hJ : ∀ ω, ‖∫ θ, G ω θ ∂ν‖ₑ ^ p ≤ ∫⁻ θ, ‖G ω θ‖ₑ ^ p ∂ν := fun ω => by
    have h1 : ‖∫ θ, G ω θ ∂ν‖ₑ ≤ ∫⁻ θ, ‖G ω θ‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    have h2 : eLpNorm (fun θ => G ω θ) 1 ν ≤ eLpNorm (fun θ => G ω θ) (ENNReal.ofReal p) ν :=
      eLpNorm_le_eLpNorm_of_exponent_le (by simpa using ENNReal.ofReal_le_ofReal hp)
    rw [eLpNorm_one_eq_lintegral_enorm (hsec ω).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt
      (hsec ω).aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le, one_div,
      ENNReal.le_rpow_inv_iff hp0] at h2
    exact (ENNReal.rpow_le_rpow h1 hp0.le).trans h2
  calc ∫⁻ ω, ‖∫ θ, G ω θ ∂ν‖ₑ ^ p ∂μ ≤ ∫⁻ ω, ∫⁻ θ, ‖G ω θ‖ₑ ^ p ∂ν ∂μ := lintegral_mono hJ
    _ = ∫⁻ θ, ∫⁻ ω, ‖G ω θ‖ₑ ^ p ∂μ ∂ν :=
        lintegral_lintegral_swap (hG.enorm.pow_const p).aemeasurable
    _ ≤ ∫⁻ _θ, ENNReal.ofReal c ^ p ∂ν := lintegral_mono hθ
    _ = ENNReal.ofReal c ^ p := by rw [lintegral_const, measure_univ, mul_one]

/-!
## Cauchy's formula for the derivative, as a phase average
-/

/-- **Cauchy's estimate as a phase average**:
`‖cderiv ρ f z‖ ≤ ρ⁻¹ ∫ ‖f(z + ρe^{iθ})‖ dphaseLaw(θ)` (`phaseLaw` uniform on `[0, 2π)`). -/
theorem norm_cderiv_le_phase {f : ℂ → ℂ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    ‖Complex.cderiv ρ f z‖ ≤ ρ⁻¹ * ∫ θ, ‖f (circleMap z ρ θ)‖ ∂phaseLaw := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpt : ∀ θ : ℝ, ‖deriv (circleMap z ρ) θ •
      (((circleMap z ρ θ - z) ^ 2)⁻¹ • f (circleMap z ρ θ))‖ =
        ρ⁻¹ * ‖f (circleMap z ρ θ)‖ := fun θ => by
    rw [norm_smul, norm_smul, deriv_circleMap, circleMap_sub_center, norm_mul, norm_inv,
      norm_pow, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_pos hρ]
    field_simp
  have hint : ∫ θ, ‖f (circleMap z ρ θ)‖ ∂phaseLaw =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap z ρ θ)‖ := by
    rw [phaseLaw, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      intervalIntegral.integral_of_le h2π, integral_Ico_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo, smul_eq_mul]
  have hle := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun θ => deriv (circleMap z ρ) θ •
      (((circleMap z ρ θ - z) ^ 2)⁻¹ • f (circleMap z ρ θ))) h2π
  simp only [hpt] at hle
  rw [intervalIntegral.integral_const_mul] at hle
  have hn : ‖((2 * Real.pi * Complex.I : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  unfold Complex.cderiv circleIntegral
  rw [norm_smul, hn, hint]
  have h0 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap z ρ) θ •
        (((circleMap z ρ θ - z) ^ 2)⁻¹ • f (circleMap z ρ θ))‖
      ≤ (2 * Real.pi)⁻¹ * (ρ⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap z ρ θ)‖) :=
        mul_le_mul_of_nonneg_left hle h0
    _ = ρ⁻¹ * ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap z ρ θ)‖) := by
        ring

/-!
## The first-jet shift is controlled by the value shift on a circle
-/

theorem measurable_stieltjes_joint {W : ℕ} :
    Measurable fun q : Matrix (Fin W) (Fin W) ℂ × ℂ => stieltjes q.1 q.2 := by
  have hR : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × ℂ =>
      (q.2 • (1 : Matrix (Fin W) (Fin W) ℂ) - q.1)⁻¹ := by
    refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (measurable_snd.mul measurable_const).sub measurable_fst.eval_matrix
  simp only [stieltjes, Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hR.eval_matrix)

theorem jet1D_eq_deriv (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    jet1D b E X = deriv (stieltjes X) (boundaryZ b E) := rfl

/-- **Pointwise Cauchy bound for the first-jet shift**: for passive `X, X'` and
`0 < ρ < Im z_∂`, `‖jet1D X - jet1D X'‖ ≤ ρ⁻¹ ∫ ‖f(X, w_θ) - f(X', w_θ)‖ dphaseLaw`,
`w_θ = z_∂ + ρe^{iθ}`. -/
theorem norm_jet1D_sub_le {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ}
    {X X' : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    (hX' : (passiveY X').PosSemidef) {ρ : ℝ} (hρ : 0 < ρ) (hρz : ρ < (boundaryZ b E).im) :
    ‖jet1D b E X - jet1D b E X'‖ ≤ ρ⁻¹ * ∫ θ, ‖stieltjes X (circleMap (boundaryZ b E) ρ θ) -
      stieltjes X' (circleMap (boundaryZ b E) ρ θ)‖ ∂phaseLaw := by
  have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd : ∀ Y : Matrix (Fin W) (Fin W) ℂ, (passiveY Y).PosSemidef →
      DifferentiableOn ℂ (stieltjes Y) {w : ℂ | 0 < w.im} :=
    fun Y hY w hw => (hasDerivAt_stieltjes hY hw).differentiableAt.differentiableWithinAt
  have hz : 0 < (boundaryZ b E).im := BlockBand.Transmission.Bridge.boundaryZ_im_pos hb hE1 hE2
  have hball : closedBall (boundaryZ b E) ρ ⊆ {w : ℂ | 0 < w.im} := fun w hw => by
    have h1 := Complex.abs_im_le_norm (w - boundaryZ b E)
    rw [Complex.sub_im] at h1
    have h2 : ‖w - boundaryZ b E‖ ≤ ρ := by rw [← dist_eq_norm]; exact hw
    have h3 := (abs_le.1 (h1.trans h2)).1
    show 0 < w.im
    linarith
  have hD : DifferentiableOn ℂ (fun w => stieltjes X w - stieltjes X' w) {w : ℂ | 0 < w.im} :=
    (hd X hX).sub (hd X' hX')
  have heq : jet1D b E X - jet1D b E X' =
      deriv (fun w => stieltjes X w - stieltjes X' w) (boundaryZ b E) := by
    rw [show (fun w => stieltjes X w - stieltjes X' w) = stieltjes X - stieltjes X' from rfl,
      deriv_sub ((hd X hX).differentiableAt (hU.mem_nhds hz))
      ((hd X' hX').differentiableAt (hU.mem_nhds hz))]
    rfl
  rw [heq, ← Complex.cderiv_eq_deriv hU hD hρ hball]
  exact norm_cderiv_le_phase hρ

/-!
## The common estimate and the `δ₁` consequence
-/

/-- **`ClosedJetShiftNbhdLp`: the closing shift of the normalized near trace is `O(1/W)` in every
`L^p`, uniformly on a disc around `z_∂`** (at the closing time `n_s`; whole space):
`‖f(X_cl,n_s, w) - f(X_{n_s}, w)‖_p ≤ C_p/W` for `|w - z_∂| ≤ r`, `f(X, w) = W⁻¹Tr(w - X)⁻¹`. -/
def ClosedJetShiftNbhdLp : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → ∃ r C : ℝ, 0 < r ∧ ∀ᶠ W in atTop,
      ∀ w ∈ closedBall (boundaryZ b E) r,
        eLpNorm (fun y => ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) w -
            stieltjes (pathX b E W (closeLen s W) y.1.1) w‖) (ENNReal.ofReal p)
          (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedJet1ShiftLp` from the common estimate** and the passivity of `b3ClosedX`
(`ClosedInputPassive b3ClosedX`): Cauchy on `|w - z_∂| = ρ`, `ρ = min(r, Im z_∂/2)`, then Jensen
and Tonelli. -/
theorem closedJet1ShiftLp_of_nbhd
    (hP : ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef)
    (hN : ClosedJetShiftNbhdLp) : ClosedJet1ShiftLp := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨⟨-, hb, hE1, hE2, -, -, -, -⟩, -, -, -, -, -⟩ := id hFD
  have hb1 : b < 1 := by linarith
  obtain ⟨r, C, hr, hev⟩ := hN b E np τ m T s h K Vs hFD p hp
  have hzim : 0 < (boundaryZ b E).im := BlockBand.Transmission.Bridge.boundaryZ_im_pos hb1 hE1 hE2
  obtain ⟨ρ, hρ0, hρr, hρz⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ρ < (boundaryZ b E).im :=
    ⟨min r ((boundaryZ b E).im / 2), lt_min hr (by positivity), min_le_left _ _,
      (min_le_right _ _).trans_lt (by linarith)⟩
  have hρi : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
  refine ⟨ρ⁻¹ * max C 0, by positivity, ?_⟩
  filter_upwards [hev, hP b E np τ m T s h K Vs hFD, hFD.2.2.2.2.2] with W hW hWP hVW hlt
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hAm : NullMeasurableSet (b3Alive b E s h τ m R W (closeLen s W) (Vs W))
      (closedLaw b W np) :=
    nullMeasurableSet_b3Alive hb1 hE1 hE2 s h τ m R W (closeLen s W) hV
  have hpc : ∀ᵐ y ∂closedLaw b W np,
      (passiveY (b3ClosedX b E s h τ m W (closeLen s W) y)).PosSemidef :=
    hWP _ (Finset.mem_Ico.2 ⟨le_rfl, hlt⟩)
  have hpo : ∀ᵐ y ∂closedLaw b W np, (passiveY (pathX b E W (closeLen s W) y.1.1)).PosSemidef := by
    have h0 : ∀ᵐ ω ∂growthPathLaw W b, (passiveY (pathX b E W (closeLen s W) ω)).PosSemidef := by
      filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb1 hE1 hE2]
        with ω hP'
      exact pathNearSchur_passive hP' _
    rw [← closedLaw_map_path b W np] at h0
    exact ae_of_ae_map (measurable_fst.comp measurable_fst).aemeasurable h0
  have hGm : Measurable (Function.uncurry fun (y : ProbedPath W np × ℝ) (θ : ℝ) =>
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖) := by
    have hc : Measurable fun q : (ProbedPath W np × ℝ) × ℝ => circleMap (boundaryZ b E) ρ q.2 :=
      (continuous_circleMap _ ρ).measurable.comp measurable_snd
    have h1 := measurable_stieltjes_joint.comp
      (((measurable_b3ClosedX b E s h τ m (closeLen s W)).comp measurable_fst).prodMk hc)
    have h2 := measurable_stieltjes_joint.comp
      ((((measurable_pathX b E (closeLen s W)).comp (measurable_fst.comp measurable_fst)).comp
        measurable_fst).prodMk hc)
    exact (h1.sub h2).norm
  have hθ : ∀ θ : ℝ, eLpNorm (fun y : ProbedPath W np × ℝ =>
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖)
      (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (max C 0 / W) := fun θ =>
    (hW _ (by
      rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hρ0]
      exact hρr)).trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)))
  have hB := eLpNorm_integral_le_of_forall (closedLaw b W np) phaseLaw hGm hp hθ
  have hf₀ : Measurable fun y : ProbedPath W np × ℝ =>
      ‖-crossTr (b3ClosedX b E s h τ m W (closeLen s W) y) (boundaryZ b E) (boundaryZ b E) -
        -crossTr (pathX b E W (closeLen s W) y.1.1) (boundaryZ b E) (boundaryZ b E)‖ :=
    (((measurable_crossTr_mat _).comp (measurable_b3ClosedX b E s h τ m (closeLen s W))).neg.sub
      ((measurable_crossTr_mat _).comp ((measurable_pathX b E (closeLen s W)).comp
        (measurable_fst.comp measurable_fst))).neg).norm
  have hae : ∀ᵐ y ∂closedLaw b W np,
      jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y =
        ‖-crossTr (b3ClosedX b E s h τ m W (closeLen s W) y) (boundaryZ b E) (boundaryZ b E) -
          -crossTr (pathX b E W (closeLen s W) y.1.1) (boundaryZ b E) (boundaryZ b E)‖ := by
    filter_upwards [hpc, hpo] with y h1 h2
    rw [jet1Shift, jet1D_eq_deriv, jet1D_eq_deriv, deriv_stieltjes h1 hzim,
      deriv_stieltjes h2 hzim]
  have hm : AEStronglyMeasurable ((b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
      fun y => jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y)
      (closedLaw b W np) := by
    refine (hf₀.aestronglyMeasurable.indicator₀ hAm).congr ?_
    filter_upwards [hae] with y hy
    by_cases hyA : y ∈ b3Alive b E s h τ m R W (closeLen s W) (Vs W)
    · rw [Set.indicator_of_mem hyA, Set.indicator_of_mem hyA, hy]
    · rw [Set.indicator_of_notMem hyA, Set.indicator_of_notMem hyA]
  have hpt : ∀ᵐ y ∂closedLaw b W np,
      ‖(b3Alive b E s h τ m R W (closeLen s W) (Vs W)).indicator
        (fun y => jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y) y‖ ≤
      ‖ρ⁻¹ * ∫ θ, ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y)
          (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw‖ := by
    filter_upwards [hpc, hpo] with y h1 h2
    have hk := norm_jet1D_sub_le hb1 hE1 hE2 h1 h2 hρ0 hρz
    have hI0 : 0 ≤ ρ⁻¹ * ∫ θ, ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y)
          (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw :=
      mul_nonneg hρi (integral_nonneg fun θ => norm_nonneg _)
    rw [Real.norm_of_nonneg hI0]
    by_cases hyA : y ∈ b3Alive b E s h τ m R W (closeLen s W) (Vs W)
    · have hj0 : 0 ≤ jet1Shift b E (b3ClosedX b E s h τ m W (closeLen s W) y) (closeLen s W) y :=
        norm_nonneg _
      rw [Set.indicator_of_mem hyA, Real.norm_of_nonneg hj0]
      exact hk
    · rw [Set.indicator_of_notMem hyA, norm_zero]
      exact hI0
  refine (eLpNorm_mono_ae hm hpt).trans ?_
  have hsm := eLpNorm_const_smul ρ⁻¹ (fun y : ProbedPath W np × ℝ => ∫ θ,
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw) (ENNReal.ofReal p) (closedLaw b W np)
  rw [Real.enorm_of_nonneg hρi] at hsm
  refine (le_of_eq hsm).trans ?_
  calc ENNReal.ofReal ρ⁻¹ * eLpNorm (fun y : ProbedPath W np × ℝ => ∫ θ,
      ‖stieltjes (b3ClosedX b E s h τ m W (closeLen s W) y) (circleMap (boundaryZ b E) ρ θ) -
        stieltjes (pathX b E W (closeLen s W) y.1.1) (circleMap (boundaryZ b E) ρ θ)‖
          ∂phaseLaw) (ENNReal.ofReal p) (closedLaw b W np)
      ≤ ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal (max C 0 / W) := by gcongr
    _ = ENNReal.ofReal (ρ⁻¹ * max C 0 / W) := by
        rw [← ENNReal.ofReal_mul hρi, mul_div_assoc]

end BlockBand.SourceProcess.PhysApprox.B3.Jet1
