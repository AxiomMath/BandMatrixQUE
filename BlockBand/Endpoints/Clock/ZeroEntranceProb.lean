module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbLimit

/-!
# The zero-entrance lemma: the zero-boundary entrance

`zeroEntrance_of` proves `ZeroEntranceStatement` (the full statement with its uniformity in the
compact parameter sets) from
* `CavityMeanStatement` (the cavity-mean lemma), and
* `GaussianAbsorptionContract` (the Gaussian absorption lemma).
`zeroEntrance_of_contracts` proves it from `GaussianAbsorptionContract` and `TraceMatrixContract`
(through `cavityMean_of`), and `zeroEntrance_of_inputs` from `ConditionalBlockGUECount` and
`GaussianLpGradient` (through `cavityMean_of_inputs` and `gaussianAbsorption_holds`).

Structure of the proof (the steps of the paper's proof):
* Step 2, the finite chain with general port `z'` and its existence; the identification
  `E h_J(z') = m_{J+1}(z') + O(1/W)` by nesting the cavity maps (`meanBound_all`).
* Steps 3–7, the seed estimate (`zeroEntrance_finite_seed_exists`).
* Step 1, the limiting measures and convergence in probability.
* Steps 8–9, concentration uniform in the initial matrix (`fluctBound_all`; induction with the
  conditional map instead of scattering matrices), the derivative, and the perturbation in `D`
  (`pertBound_all`), with Gaussian norm moments.
* Step 10, uniformity in `b` on compact sets (rescaling the fresh Gaussians to one base parameter).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Metric
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Real Matrix.Norms.L2Operator

namespace ZeroEntranceProb

open CavityMeanProb

/-- Standard hypotheses of the Cauchy transfer for `H = zeTrace e D J`. -/
theorem deriv_setup {W : ℕ} (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) {z : ℂ} {η₀ M : ℝ} (hη : 0 < η₀) (hz : η₀ ≤ z.im)
    (hzM : ‖z‖ ≤ M) :
    Measurable (fun q : ℂ × (Fin J → OneEndedLayer W) => zeTrace e D J q.1 q.2) ∧
      (∀ᵐ ω ∂oneEndedLaw W b J,
        DifferentiableOn ℂ (fun ζ => zeTrace e D J ζ ω) {ζ : ℂ | 0 < ζ.im}) ∧
      closedBall z (η₀ / 2) ⊆ {ζ : ℂ | η₀ / 2 ≤ ζ.im} ∧
      (∀ᵐ ω ∂oneEndedLaw W b J, ∀ ζ ∈ sphere z (η₀ / 2), ‖zeTrace e D J ζ ω‖ ≤ 1 / (η₀ / 2)) ∧
      ContinuousOn (fun ζ => ∫ ω, zeTrace e D J ζ ω ∂oneEndedLaw W b J) (sphere z (η₀ / 2)) := by
  obtain ⟨hball, hsph⟩ := cauchy_disc hz hzM
  have hη2 : 0 < η₀ / 2 := by positivity
  refine ⟨measurable_zeTrace_joint e D J, ?_, hball, ?_, ?_⟩
  · filter_upwards [ae_X_isHermitian b e hD J] with ω hω
    exact normalizedResolventTrace_differentiableOn hω
  · filter_upwards [ae_X_isHermitian b e hD J] with ω hω
    intro ζ hζ
    have h1 := (hsph ζ hζ).1
    exact (norm_zeTrace_le hW e hω (hη2.trans_le h1)).trans (one_div_le_one_div_of_le hη2 h1)
  · exact (meanTrace_differentiableOn hW b e hD J).continuousOn.mono fun ζ hζ =>
      hη2.trans_le (hsph ζ hζ).1

end ZeroEntranceProb

open ZeroEntranceProb CavityMeanProb

/-- **The zero-entrance lemma** (`ZeroEntranceStatement`), from `CavityMeanStatement` and
`GaussianAbsorptionContract`. -/
theorem zeroEntrance_of (hQ : CavityMeanStatement) (habs : GaussianAbsorptionContract) :
    ZeroEntranceStatement := by
  have hU := cavityLayerUniform_of hQ
  have hA := absorptionUniform_of habs
  classical
  set μ : ℝ → ℝ → ℕ → Measure ℝ := fun b e J =>
    if h : 0 < b ∧ b < 1 / 2 ∧ -2 < e ∧ e < 2 then
      Classical.choose (exists_limitMeasure hU h.1 h.2.1 h.2.2.1 h.2.2.2 J)
    else Measure.dirac 0 with hμdef
  have hμ : ∀ b e : ℝ, 0 < b → b < 1 / 2 → -2 < e → e < 2 → ∀ J : ℕ,
      IsProbabilityMeasure (μ b e J) ∧
        ∀ ζ : ℂ, 0 < ζ.im → stieltjesG (μ b e J) ζ = chainPort b e J ζ := by
    intro b e hb0 hb1 he0 he1 J
    have h : 0 < b ∧ b < 1 / 2 ∧ -2 < e ∧ e < 2 := ⟨hb0, hb1, he0, he1⟩
    have hμe : μ b e J = Classical.choose (exists_limitMeasure hU hb0 hb1 he0 he1 J) := by
      rw [hμdef]; dsimp only; split_ifs
      rfl
    rw [hμe]
    exact Classical.choose_spec (exists_limitMeasure hU hb0 hb1 he0 he1 J)
  have hparam : ∀ κ b e : ℝ, 0 < κ → zeParam κ b e →
      0 < b ∧ b < 1 / 2 ∧ -2 < e ∧ e < 2 := by
    intro κ b e hκ hbe
    obtain ⟨hb0, hb1, -, -, -, -, -⟩ := zeParam_facts hκ hbe
    have : e ^ 2 < 4 := by have := hbe.2.2; linarith
    exact ⟨hb0, hb1, by nlinarith, by nlinarith⟩
  refine ⟨μ, ?_, ?_, ?_⟩
  · -- (i) probability measure and convergence in probability
    intro b e hb0 hb1 he0 he1 J
    refine ⟨(hμ b e hb0 hb1 he0 he1 J).1, ?_⟩
    intro ζ hζ δ hδ
    obtain ⟨hκ, hbe⟩ := kappaOf_facts hb0 hb1 he0 he1
    obtain ⟨K, W₀, hK, hP⟩ := prob_zeTrace_le hU hκ J (η := ζ.im) (M := ‖ζ‖) hζ
    rw [(hμ b e hb0 hb1 he0 he1 J).2 ζ hζ]
    have hup : Tendsto (fun W : ℕ => ENNReal.ofReal (K / (δ * W))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have h := tendsto_const_div_atTop_nhds_zero_nat (K / δ)
      refine h.congr fun W => ?_
      rw [div_div]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop (max W₀ 1)] with W hW
    exact hP W ((le_max_left _ _).trans hW) ((le_max_right _ _).trans hW) b e hbe ζ le_rfl le_rfl
      δ hδ
  · -- (ii) the seed estimate
    intro κ hκ
    obtain ⟨C, cstar, hC, hc, hseed⟩ := zeroEntrance_finite_seed_exists hκ
    refine ⟨C, cstar, hC, hc, ?_⟩
    intro b e J hbe
    obtain ⟨hb0, hb1, he0, he1⟩ := hparam κ b e hκ hbe
    have he4 : e ^ 2 ≤ 4 := by nlinarith
    have hz : 0 < (boundaryZ b e).im := by
      rw [ZeroEntrance.boundaryZ_im he4]
      have : 0 < Real.sqrt (4 - e ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
      have : 0 < 1 - b := by linarith
      positivity
    rw [(hμ b e hb0 hb1 he0 he1 J).2 _ hz]
    obtain ⟨m, hm, hme⟩ := chainPort_spec (e := e) hb0 (by linarith) J hz
    rw [← hme]
    exact hseed b e J m hbe.1 hbe.2.1 hbe.2.2 (isPortChain_boundaryZ_iff.mp hm)
  · -- (iii) the estimates at fixed `J`, uniform in the compact parameter set
    intro κ hκ J
    set ηz := Real.sqrt κ / 4 with hηz
    have hηz0 : 0 < ηz := by positivity
    set Mz : ℝ := 2 with hMz
    set r := ηz / 2 with hr
    have hr0 : 0 < r := by positivity
    have hregion : ∀ b e : ℝ, zeParam κ b e → ηz ≤ (boundaryZ b e).im ∧ ‖boundaryZ b e‖ ≤ Mz := by
      intro b e hbe
      obtain ⟨hb0, hb1, -, -, -, -, he4⟩ := zeParam_facts hκ hbe
      refine ⟨?_, ?_⟩
      · rw [ZeroEntrance.boundaryZ_im he4]
        have h1 : Real.sqrt κ ≤ Real.sqrt (4 - e ^ 2) := Real.sqrt_le_sqrt hbe.2.2
        have h2 : 1 / 2 ≤ 1 - b := by linarith
        have h3 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
        rw [hηz]
        nlinarith
      · have := ZeroEntrance.boundaryZ_norm_le hb0.le he4 (b := b)
        rw [hMz]; linarith
    obtain ⟨a₁, C₁, ha₁, hC₁, hF1⟩ := fluctBound_all hU hκ J ηz Mz hηz0
    obtain ⟨a₂, C₂, ha₂, hC₂, hF2⟩ := fluctBound_all hU hκ J (ηz / 2) (Mz + ηz / 2) (by positivity)
    obtain ⟨C₃, hC₃, hM1⟩ := meanBound_all hU hκ J ηz Mz hηz0
    obtain ⟨C₄, hC₄, hM2⟩ := meanBound_all hU hκ J (ηz / 2) (Mz + ηz / 2) (by positivity)
    obtain ⟨C₅, W₅, hC₅, hP1⟩ := pertBound_all hA hκ J (M := Mz) hηz0
    obtain ⟨C₆, W₆, hC₆, hP2⟩ := pertBound_all hA hκ J (M := Mz + ηz / 2) (η := ηz / 2)
      (by positivity)
    refine ⟨min a₁ a₂, C₁ + C₂ / r + C₃ + C₄ / r + C₅ + C₆ / r + 1, max (max W₅ W₆) 1,
      lt_min ha₁ ha₂, by positivity, ?_⟩
    intro W hW b e hbe
    have hW0 : 0 < W := (le_max_right _ _).trans hW
    have hW5 : W₅ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
    have hW6 : W₆ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
    obtain ⟨hb0, hb1, he0, he1⟩ := hparam κ b e hκ hbe
    obtain ⟨hzi, hzn⟩ := hregion b e hbe
    set z := boundaryZ b e with hzdef
    have hz0 : 0 < z.im := hηz0.trans_le hzi
    have hD0 : (0 : Matrix (Fin W) (Fin W) ℂ).IsHermitian := Matrix.isHermitian_zero
    have hG := (hμ b e hb0 hb1 he0 he1 J).2
    have := (hμ b e hb0 hb1 he0 he1 J).1
    have hc : 0 < 1 - 2 * b := by linarith
    -- chain values on the sphere
    have hmean_sph : ∀ ζ ∈ sphere z r, ‖(∫ ω, zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ ω
        ∂oneEndedLaw W b J) - stieltjesG (μ b e J) ζ‖ ≤ C₄ / W := by
      intro ζ hζ
      obtain ⟨-, hsph⟩ := cauchy_disc hzi hzn
      obtain ⟨h1, h2⟩ := hsph ζ hζ
      have hζ0 : 0 < ζ.im := (by positivity : (0 : ℝ) < ηz / 2).trans_le h1
      obtain ⟨m, hm, hme⟩ := chainPort_spec (e := e) hb0 hc J hζ0
      rw [hG ζ hζ0, ← hme]
      exact hM2 W hW0 b e hbe ζ h1 h2 m hm
    have hsph_reg : ∀ ζ ∈ sphere z r, ηz / 2 ≤ ζ.im ∧ ‖ζ‖ ≤ Mz + ηz / 2 :=
      (cauchy_disc hzi hzn).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- mean
      obtain ⟨m, hm, hme⟩ := chainPort_spec (e := e) hb0 hc J hz0
      rw [hG z hz0, ← hme]
      refine (hM1 W hW0 b e hbe z hzi hzn m hm).trans ?_
      gcongr
      have : 0 ≤ C₂ / r := by positivity
      have : 0 ≤ C₄ / r := by positivity
      have : 0 ≤ C₆ / r := by positivity
      linarith
    · -- mean of the derivative
      obtain ⟨hHm, hHd, hball, hHb, hHmc⟩ := deriv_setup hW0 b e hD0 J hηz0 hzi hzn
      have h := deriv_mean_le hHm hHd hr0 (by positivity) hball hHb hHmc
        (stieltjesG_differentiableOn (μ b e J)) hmean_sph
      refine h.trans ?_
      rw [div_div, mul_comm, ← div_div]
      gcongr
      have : 0 ≤ C₂ / r := by positivity
      have : 0 ≤ C₆ / r := by positivity
      linarith
    · -- concentration, uniform in `D`
      intro D hD p hp2 hpa
      have hpa₁ : p ≤ a₁ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le)
      have hpa₂ : p ≤ a₂ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
      have hsq : 0 ≤ Real.sqrt p / W := by positivity
      have hCle : ∀ c : ℝ, c ≤ C₁ + C₂ / r + C₃ + C₄ / r + C₅ + C₆ / r + 1 →
          ENNReal.ofReal (c * Real.sqrt p / W) ≤
            ENNReal.ofReal ((C₁ + C₂ / r + C₃ + C₄ / r + C₅ + C₆ / r + 1) * Real.sqrt p / W) := by
        intro c hc'
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hc' hsq
      refine ⟨(hF1 W hW0 b e hbe D hD z hzi hzn p hp2 hpa₁).trans (hCle C₁ ?_), ?_⟩
      · have : 0 ≤ C₂ / r := by positivity
        have : 0 ≤ C₄ / r := by positivity
        have : 0 ≤ C₆ / r := by positivity
        linarith
      obtain ⟨hHm, hHd, hball, hHb, hHmc⟩ := deriv_setup hW0 b e hD J hηz0 hzi hzn
      have h := deriv_fluct_le hHm hHd hr0 (by positivity) hball hHb hHmc (by linarith : (1 : ℝ) ≤ p)
        (B := C₂ * Real.sqrt p / W)
        (fun ζ hζ => hF2 W hW0 b e hbe D hD ζ (hsph_reg ζ hζ).1 (hsph_reg ζ hζ).2 p hp2 hpa₂)
      refine h.trans ?_
      have : C₂ * Real.sqrt p / W / r = C₂ / r * Real.sqrt p / W := by ring
      rw [this]
      refine hCle _ ?_
      have : 0 ≤ C₄ / r := by positivity
      have : 0 ≤ C₆ / r := by positivity
      linarith
    · -- perturbation by the initial matrix
      intro ε D hD hDε
      have hε : 0 ≤ ε := (norm_nonneg _).trans hDε
      refine ⟨?_, ?_⟩
      · refine (hP1 W hW5 hW0 b e hbe D hD z hzi hzn).trans ?_
        have : 0 ≤ C₂ / r := by positivity
        have : 0 ≤ C₄ / r := by positivity
        have : 0 ≤ C₆ / r := by positivity
        calc C₅ * ‖D‖ ≤ C₅ * ε := mul_le_mul_of_nonneg_left hDε hC₅
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hε
      · obtain ⟨hHm, hHd, hball, hHb, hHmc⟩ := deriv_setup hW0 b e hD J hηz0 hzi hzn
        obtain ⟨hHm0, hHd0, -, hHb0, hHmc0⟩ := deriv_setup hW0 b e hD0 J hηz0 hzi hzn
        have hg := meanTrace_differentiableOn hW0 b e hD0 J
        have h1 := deriv_mean_le hHm hHd hr0 (by positivity) hball hHb hHmc hg
          (B := C₆ * ‖D‖) (fun ζ hζ => hP2 W hW6 hW0 b e hbe D hD ζ (hsph_reg ζ hζ).1
            (hsph_reg ζ hζ).2)
        have h2 := deriv_mean_le hHm0 hHd0 hr0 (by positivity) hball hHb0 hHmc0 hg (B := 0)
          (fun ζ _ => by
            rw [show (∫ ω, zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ ω ∂oneEndedLaw W b J) =
              meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ from rfl, sub_self, norm_zero])
        rw [zero_div] at h2
        have := norm_sub_le_norm_sub_add_norm_sub
          (∫ ω, deriv (fun ζ => zeTrace e D J ζ ω) z ∂oneEndedLaw W b J)
          (deriv (meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) J) z)
          (∫ ω, deriv (fun ζ => zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ ω) z
            ∂oneEndedLaw W b J)
        rw [norm_sub_rev (deriv _ z)] at this
        refine this.trans ?_
        have h3 : C₆ * ‖D‖ / r ≤ C₆ / r * ε := by
          rw [mul_comm C₆, mul_div_assoc, mul_comm]
          exact mul_le_mul_of_nonneg_left hDε (by positivity)
        have : 0 ≤ C₂ / r := by positivity
        have : 0 ≤ C₄ / r := by positivity
        calc _ ≤ C₆ * ‖D‖ / r + 0 := add_le_add h1 h2
          _ ≤ C₆ / r * ε := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hε

/-- **The zero-entrance lemma** from `GaussianAbsorptionContract` and `TraceMatrixContract`
(through `cavityMean_of`).
-/
theorem zeroEntrance_of_contracts (habs : GaussianAbsorptionContract)
    (htm : TraceMatrixContract) : ZeroEntranceStatement :=
  zeroEntrance_of (cavityMean_of habs htm) habs

/-- **The zero-entrance lemma** from `ConditionalBlockGUECount` and `GaussianLpGradient` (through
`gaussianAbsorption_holds` and `traceMatrix_holds`).
-/
theorem zeroEntrance_of_inputs (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) : ZeroEntranceStatement :=
  zeroEntrance_of (cavityMean_of_inputs hcount hgrad)
    (BlockBand.Layers.gaussianAbsorption_holds hcount)

end BlockBand.Endpoints.Clock
