module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepGram
public import BlockBand.SourceProcess.ProjSeparator.Layer
public import BlockBand.SourceProcess.FullSourceCovariance.Reduction
public import BlockBand.SourceProcess.FullSourceCovariance.FirstTermHolds
public import BlockBand.SourceProcess.FullSourceCovariance.Decomposition
public import BlockBand.SourceProcess.FullSourceCovariance.Strict
public import BlockBand.SourceProcess.FullSourceCovariance.Assembly
public import BlockBand.SourceProcess.FullSource.DeltaMoments
public import BlockBand.SourceProcess.RawTag.DeltaBounds

/-!
# Fresh second moments of `u*Δv` at a passive input

For a deterministic passive `X` and vectors with `‖·‖ ≤ C_f`, with `a = x*Δ(X)y`, `b = x'*Δ(X)y'`:

* `integral_mul_eq_cov_add`, `integral_mul_conj_eq_cov_add` (generic): in `L²`,
  `E[ab] = E[(a - Ea)(b - Eb)] + Ea Eb`, and the same with `conj b`;
* `fresh_delta_memLp`: the fresh second moments of `‖Δ‖` and `x*Δy ∈ L²`;
* `fresh_delta_same_le`, `fresh_delta_opp_le`: `E[ab] = (σ₋/W)(crossed tensor) + error` and
  `E[a conj b] = (σ₊/W)(x*x')(y'*y) + error`, with error `≤ C C_f⁴(covErr + (δ₀ + W⁻¹)²)`.

Here `covErr = W⁻² + W⁻¹(δ₀ + δ₁ + g/W)`, uniformly in `W ≥ W₀`, `E` in the bulk and `X`.

Support for the `𝒦` brackets (`CovLayerHypK`, `ConjLayerHyp`), with the closed exact update
`d𝒦 = u*Δ(X_cl)v` of `closedK_step`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceCovariance
open BlockBand.Transmission.PassiveLayer (MomBd)
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## Generic centring
-/

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_mul_eq_cov_add {a b : Ω → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ ω, a ω * b ω ∂μ =
      ∫ ω, (a ω - ∫ ω, a ω ∂μ) * (b ω - ∫ ω, b ω ∂μ) ∂μ + (∫ ω, a ω ∂μ) * ∫ ω, b ω ∂μ := by
  set A := ∫ ω, a ω ∂μ
  set B := ∫ ω, b ω ∂μ
  have hab : Integrable (fun ω => a ω * b ω) μ := ha.integrable_mul hb
  have hai := ha.integrable one_le_two
  have hbi := hb.integrable one_le_two
  have e : (fun ω => (a ω - A) * (b ω - B)) =
      fun ω => a ω * b ω - A * b ω - B * a ω + A * B := by funext ω; ring
  have h1 : Integrable (fun ω => a ω * b ω - A * b ω - B * a ω) μ :=
    (hab.sub (hbi.const_mul A)).sub (hai.const_mul B)
  have h2 : Integrable (fun ω => a ω * b ω - A * b ω) μ := hab.sub (hbi.const_mul A)
  rw [e, integral_add h1 (integrable_const _), integral_sub h2 (hai.const_mul B),
    integral_sub hab (hbi.const_mul A), integral_const_mul, integral_const_mul, integral_const,
    probReal_univ, one_smul]
  ring

theorem integral_mul_conj_eq_cov_add {a b : Ω → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ ω, a ω * star (b ω) ∂μ =
      ∫ ω, (a ω - ∫ ω, a ω ∂μ) * star (b ω - ∫ ω, b ω ∂μ) ∂μ +
        (∫ ω, a ω ∂μ) * star (∫ ω, b ω ∂μ) := by
  have hb' : MemLp (fun ω => star (b ω)) 2 μ := hb.star
  have h := integral_mul_eq_cov_add ha hb'
  have hc : ∫ ω, star (b ω) ∂μ = star (∫ ω, b ω ∂μ) := integral_conj
  rw [hc] at h
  simpa only [star_sub] using h

end Generic

/-!
## `u*Δv` at a passive input
-/

theorem bilinear_sub' {n : Type*} [Fintype n] (u : n → ℂ) (M N : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (M - N) v = bilinear u M v - bilinear u N v := by
  simp only [bilinear, sub_mulVec, dotProduct_sub]

/-- The fresh second moments of `‖Δ‖` and the `L²` membership of `x*Δy`. -/
theorem fresh_delta_memLp (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C₂ : ℝ) (W₀ : ℕ), 0 ≤ C₂ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        MemLp (fun F => ‖freshDelta b E X F‖) 2 (freshLaw W b) ∧
        eLpNorm (fun F => ‖freshDelta b E X F‖) 2 (freshLaw W b) ≤ ENNReal.ofReal C₂ ∧
        ∀ x y : Fin W → ℂ, MemLp (fun F => bilinear x (freshDelta b E X F) y) 2 (freshLaw W b) := by
  obtain ⟨C, W₀, hC0, hM⟩ :=
    BlockBand.SourceProcess.FullSource.delta_moments hGA b hb0 hb κ hκ 2 one_le_two
  refine ⟨C, W₀, hC0, fun W hW E hE X hX => ?_⟩
  obtain ⟨hm, hle⟩ := hM W hW E hE X hX
  rw [show ENNReal.ofReal 2 = 2 by simp] at hle
  have hN : MemLp (fun F => ‖freshDelta b E X F‖) 2 (freshLaw W b) :=
    hle.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hN, hle, fun x y => ?_⟩
  have hΔm : Measurable fun F => freshDelta b E X F :=
    BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E measurable_const measurable_id
  have hbm : Measurable fun F => bilinear x (freshDelta b E X F) y :=
    BlockBand.SourceProcess.RawTag.measurable_bilinear_jt measurable_const hΔm measurable_const
  refine (hN.const_mul (vecNorm x * vecNorm y)).of_le hbm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun F => ?_)
  have h := Transmission.PassiveCovariance.norm_bilinear_le x (freshDelta b E X F) y
  have h0 := Transmission.PassiveCovariance.vecNorm_nonneg x
  have h1 := Transmission.PassiveCovariance.vecNorm_nonneg y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg (freshDelta b E X F)]

/-- FSC's equal-sign `Δ`-covariance, from the input hypotheses. -/
theorem deltaCovarianceSame_holds' (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    DeltaCovarianceSame :=
  deltaCovarianceSame_of_onDomain hGA hLp (deltaCovarianceSameOnDomain_of_strict hGA
    (deltaCovarianceSameOnDomainStrict_of
      (BlockBand.Transmission.PassiveLayer.passiveBounds_holds hGA hLp) hGA
      (firstTermBound_holds hGA hLp) (crossedSameBound_holds hGA hLp)))

theorem norm_mean_mul_le {Cm Cf δ ma mb : ℝ} (hCm : 0 ≤ Cm) (hδ : 0 ≤ δ)
    (ha : ma ≤ Cm * Cf ^ 2 * δ) (hb : mb ≤ Cm * Cf ^ 2 * δ) (hb0 : 0 ≤ mb) :
    ma * mb ≤ Cm ^ 2 * Cf ^ 4 * δ ^ 2 := by
  have := mul_le_mul ha hb hb0 (by positivity)
  nlinarith

theorem fourNorm_le {n : Type*} [Fintype n] {x y x' y' : n → ℂ} {Cf : ℝ} (hx : vecNorm x ≤ Cf)
    (hy : vecNorm y ≤ Cf) (hx' : vecNorm x' ≤ Cf) (hy' : vecNorm y' ≤ Cf) :
    fourNorm x y x' y' ≤ Cf ^ 4 := by
  have hCf : 0 ≤ Cf := (Transmission.PassiveCovariance.vecNorm_nonneg x).trans hx
  unfold fourNorm
  have := Transmission.PassiveCovariance.vecNorm_nonneg x
  have := Transmission.PassiveCovariance.vecNorm_nonneg y
  have := Transmission.PassiveCovariance.vecNorm_nonneg x'
  have := Transmission.PassiveCovariance.vecNorm_nonneg y'
  calc vecNorm x * vecNorm y * vecNorm x' * vecNorm y' ≤ Cf * Cf * Cf * Cf := by gcongr
    _ = Cf ^ 4 := by ring

theorem covErr_nonneg {b E κ : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    (s : ℂ) {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    0 ≤ covErr b E s X := by
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := conductance_nonneg b E hη.le hX
  have h0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have h1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  unfold covErr
  exact add_nonneg (by positivity)
    (mul_nonneg (by positivity) (add_nonneg (add_nonneg h0 h1) (div_nonneg hg (Nat.cast_nonneg _))))

/-- **The equal-sign fresh second moment** of `u*Δv` at a passive input. -/
theorem fresh_delta_same_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (x y x' y' : Fin W → ℂ) (Cf : ℝ), vecNorm x ≤ Cf → vecNorm y ≤ Cf →
        vecNorm x' ≤ Cf → vecNorm y' ≤ Cf →
        ‖∫ F, bilinear x (freshDelta b E X F) y * bilinear x' (freshDelta b E X F) y'
            ∂freshLaw W b - sigmaMinus b E s / W * crossedTensor x y x' y' 1 1‖ ≤
          C * Cf ^ 4 * (covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨CS, WS, hS⟩ := deltaCovarianceSame_holds' hGA hLp b hb0 hb κ hκ
  obtain ⟨Cm, Cfl, Wm, hCm, -, hD⟩ :=
    BlockBand.SourceProcess.RawTag.delta_fresh_bounds hGA hLp b hb0 hb κ hκ 1 le_rfl
  obtain ⟨C₂, W₂, -, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  refine ⟨max CS 0 + Cm ^ 2, max (max WS Wm) W₂, by positivity, ?_⟩
  intro W hW E hE s hs X hX x y x' y' Cf hx hy hx' hy'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWS, hWm⟩, hW2⟩ := hW
  obtain ⟨hint, hmean, -⟩ := hD W hWm E hE X hX
  obtain ⟨-, -, hL2⟩ := hM W hW2 E hE X hX
  set M := matrixExpect (freshLaw W b) (freshDelta b E X)
  have hia := integral_bilinear_freshDelta b E X x y hint
  have hib := integral_bilinear_freshDelta b E X x' y' hint
  rw [integral_mul_eq_cov_add (hL2 x y) (hL2 x' y'), hia, hib]
  have hcov : ∫ F, (bilinear x (freshDelta b E X F) y - bilinear x M y) *
      (bilinear x' (freshDelta b E X F) y' - bilinear x' M y') ∂freshLaw W b =
      bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y' := by
    unfold bilinearCovariance
    simp only [bilinear_sub', M]
  rw [hcov]
  have h1 := hS W hWS E hE s hs X hX x y x' y'
  have hma : ‖bilinear x M y‖ ≤ Cm * Cf ^ 2 * (jetDistance0 b E X + (W : ℝ)⁻¹) := by
    refine (norm_bilinear_le_of_vecNorm hx hy).trans ?_
    calc Cf ^ 2 * ‖M‖ ≤ Cf ^ 2 * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hmean (sq_nonneg _)
      _ = _ := by ring
  have hmb : ‖bilinear x' M y'‖ ≤ Cm * Cf ^ 2 * (jetDistance0 b E X + (W : ℝ)⁻¹) := by
    refine (norm_bilinear_le_of_vecNorm hx' hy').trans ?_
    calc Cf ^ 2 * ‖M‖ ≤ Cf ^ 2 * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hmean (sq_nonneg _)
      _ = _ := by ring
  have hδ : 0 ≤ jetDistance0 b E X + (W : ℝ)⁻¹ := add_nonneg (norm_nonneg _) (by positivity)
  have hprod := norm_mean_mul_le hCm hδ hma hmb (norm_nonneg _)
  have hce := covErr_nonneg hb hκ hE s hX
  have hf4' : CS * covErr b E s X * fourNorm x y x' y' ≤ max CS 0 * covErr b E s X * Cf ^ 4 := by
    have h0 : 0 ≤ fourNorm x y x' y' := by
      unfold fourNorm
      have := Transmission.PassiveCovariance.vecNorm_nonneg x
      have := Transmission.PassiveCovariance.vecNorm_nonneg y
      have := Transmission.PassiveCovariance.vecNorm_nonneg x'
      have := Transmission.PassiveCovariance.vecNorm_nonneg y'
      positivity
    calc CS * covErr b E s X * fourNorm x y x' y' ≤
          max CS 0 * covErr b E s X * fourNorm x y x' y' := by
          gcongr; exact le_max_left _ _
      _ ≤ _ := by
          have hf4 : fourNorm x y x' y' ≤ Cf ^ 4 := fourNorm_le hx hy hx' hy'
          gcongr
  calc ‖bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y' +
        bilinear x M y * bilinear x' M y' - sigmaMinus b E s / W * crossedTensor x y x' y' 1 1‖
      ≤ ‖bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
          sigmaMinus b E s / W * crossedTensor x y x' y' 1 1‖ +
        ‖bilinear x M y‖ * ‖bilinear x' M y'‖ := by
        rw [← norm_mul]
        refine le_of_eq_of_le ?_ (norm_add_le _ _)
        ring_nf
    _ ≤ max CS 0 * covErr b E s X * Cf ^ 4 +
          Cm ^ 2 * Cf ^ 4 * (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 :=
        add_le_add (h1.trans hf4') hprod
    _ ≤ _ := by
        have hC4 : 0 ≤ Cf ^ 4 := by positivity
        have hδ2 : 0 ≤ (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 := sq_nonneg _
        have hm0 : 0 ≤ max CS 0 := le_max_right _ _
        nlinarith [mul_nonneg (mul_nonneg hm0 hC4) hδ2, mul_nonneg (mul_nonneg (sq_nonneg Cm) hC4)
          hce]

/-- **The opposite-sign fresh second moment** of `u*Δv` at a passive input. -/
theorem fresh_delta_opp_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (x y x' y' : Fin W → ℂ) (Cf : ℝ), vecNorm x ≤ Cf → vecNorm y ≤ Cf →
        vecNorm x' ≤ Cf → vecNorm y' ≤ Cf →
        ‖∫ F, bilinear x (freshDelta b E X F) y * star (bilinear x' (freshDelta b E X F) y')
            ∂freshLaw W b - ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear x 1 x' * bilinear y' 1 y)‖ ≤
          C * Cf ^ 4 * (covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨CS, WS, hS⟩ :=
    BlockBand.SourceProcess.ProjSeparator.deltaCovarianceOpposite_holds hGA hLp hP b hb0 hb κ hκ
  obtain ⟨Cm, Cfl, Wm, hCm, -, hD⟩ :=
    BlockBand.SourceProcess.RawTag.delta_fresh_bounds hGA hLp b hb0 hb κ hκ 1 le_rfl
  obtain ⟨C₂, W₂, -, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  refine ⟨max CS 0 + Cm ^ 2, max (max WS Wm) W₂, by positivity, ?_⟩
  intro W hW E hE s hs X hX x y x' y' Cf hx hy hx' hy'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWS, hWm⟩, hW2⟩ := hW
  obtain ⟨hint, hmean, -⟩ := hD W hWm E hE X hX
  obtain ⟨-, -, hL2⟩ := hM W hW2 E hE X hX
  set M := matrixExpect (freshLaw W b) (freshDelta b E X)
  have hia := integral_bilinear_freshDelta b E X x y hint
  have hib := integral_bilinear_freshDelta b E X x' y' hint
  rw [integral_mul_conj_eq_cov_add (hL2 x y) (hL2 x' y'), hia, hib]
  have hcov : ∫ F, (bilinear x (freshDelta b E X F) y - bilinear x M y) *
      star (bilinear x' (freshDelta b E X F) y' - bilinear x' M y') ∂freshLaw W b =
      bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' := by
    unfold bilinearCrossCovariance
    simp only [bilinear_sub', M]
  rw [hcov]
  have h1 := hS W hWS E hE s hs X hX x y x' y'
  have hma : ‖bilinear x M y‖ ≤ Cm * Cf ^ 2 * (jetDistance0 b E X + (W : ℝ)⁻¹) := by
    refine (norm_bilinear_le_of_vecNorm hx hy).trans ?_
    calc Cf ^ 2 * ‖M‖ ≤ Cf ^ 2 * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hmean (sq_nonneg _)
      _ = _ := by ring
  have hmb : ‖bilinear x' M y'‖ ≤ Cm * Cf ^ 2 * (jetDistance0 b E X + (W : ℝ)⁻¹) := by
    refine (norm_bilinear_le_of_vecNorm hx' hy').trans ?_
    calc Cf ^ 2 * ‖M‖ ≤ Cf ^ 2 * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hmean (sq_nonneg _)
      _ = _ := by ring
  have hδ : 0 ≤ jetDistance0 b E X + (W : ℝ)⁻¹ := add_nonneg (norm_nonneg _) (by positivity)
  have hprod := norm_mean_mul_le hCm hδ hma hmb (norm_nonneg _)
  have hce := covErr_nonneg hb hκ hE s hX
  have hf4' : CS * covErr b E s X * fourNorm x y x' y' ≤ max CS 0 * covErr b E s X * Cf ^ 4 := by
    have h0 : 0 ≤ fourNorm x y x' y' := by
      unfold fourNorm
      have := Transmission.PassiveCovariance.vecNorm_nonneg x
      have := Transmission.PassiveCovariance.vecNorm_nonneg y
      have := Transmission.PassiveCovariance.vecNorm_nonneg x'
      have := Transmission.PassiveCovariance.vecNorm_nonneg y'
      positivity
    calc CS * covErr b E s X * fourNorm x y x' y' ≤
          max CS 0 * covErr b E s X * fourNorm x y x' y' := by
          gcongr; exact le_max_left _ _
      _ ≤ _ := by
          have hf4 : fourNorm x y x' y' ≤ Cf ^ 4 := fourNorm_le hx hy hx' hy'
          gcongr
  calc ‖bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' +
        bilinear x M y * star (bilinear x' M y') -
        ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear x 1 x' * bilinear y' 1 y)‖
      ≤ ‖bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
          ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear x 1 x' * bilinear y' 1 y)‖ +
        ‖bilinear x M y‖ * ‖bilinear x' M y'‖ := by
        rw [← norm_star (bilinear x' M y'), ← norm_mul]
        refine le_of_eq_of_le ?_ (norm_add_le _ _)
        ring_nf
    _ ≤ max CS 0 * covErr b E s X * Cf ^ 4 +
          Cm ^ 2 * Cf ^ 4 * (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 :=
        add_le_add (h1.trans hf4') hprod
    _ ≤ _ := by
        have hC4 : 0 ≤ Cf ^ 4 := by positivity
        have hδ2 : 0 ≤ (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 := sq_nonneg _
        have hm0 : 0 ≤ max CS 0 := le_max_right _ _
        nlinarith [mul_nonneg (mul_nonneg hm0 hC4) hδ2, mul_nonneg (mul_nonneg (sq_nonneg Cm) hC4)
          hce]

end BlockBand.SourceProcess.PhysApprox.B3
