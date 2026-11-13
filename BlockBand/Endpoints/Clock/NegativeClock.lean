module

public import BlockBand.Endpoints.Clock.NegativeClockClosure
public import BlockBand.Endpoints.Clock.NegativeClockBrownian
public import BlockBand.Endpoints.Clock.NegativeClockMoments
public import BlockBand.Endpoints.Clock.NegativeClockTight

/-!
# The negative-clock theorem from the full-source moments and the Robin entrance limit

We prove `NegativeClockContract` from `FullSourceMomentsEnergyUniformContract` and
`RobinEntranceLimit`, the conclusion of the Robin entrance lemma in the form used by the proof of
the negative-clock theorem.

## Proof

1. `tight`: `negativeClock_tight` (from `FullSourceMomentsEnergyUniformContract.clock` at `p = 1`;
   Gaussian conditioning `E_h h*Yh = Re Tr Y`; Markov).
2. Convexity/Jensen and the path expectation at finite width: `negativeClock_finite_laplace`,
   with the almost-sure unitarity of `𝕊` and invertibility of the transmission `t` from
   `negativeClock_ae_scattering` (so the phase-resolution identity holds on the finite path,
   `n ≥ 1`).
3. The limit along the critical subsequence, using `RobinEntranceLimit`:
   `E e^{-sT} ≤ E e^{-saX_τ}` for every `s > 0`, `a = |I|/(2π)`.
4. `μ{0} = 0` and `E T^{-p} ≤ a^{-p} E X_τ^{-p}` (`negativeClock_negMoment_of_laplace`).
5. `E X_τ^{-p} ≤ C_{p,T₀} τ^{-p}` (`negativeClock_openClock_negMoment`, by Jensen instead of a
   bound on the Brownian supremum).

The constants are uniform as in the contract (`β, κ, T₀, p` first; `C = (ℓ/(2π))^{-p} C_B` with
`ℓ` the uniform lower bound of the phase-interval length from `RobinEntranceLimit` and `C_B` the
Brownian constant).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Real
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal Matrix BoundedContinuousFunction

/-- The law of `X_τ = d∫₀^τ exp{√D₀ B_s - D₀ s/2} ds`, `d = (1-b)⁻¹`, `D₀ = 2/(b(4-E²))`, on the
constructed Wiener measure. -/
def openClockLaw (b E τ : ℝ) : Measure ℝ :=
  BlockBand.SourceProcess.canonicalWienerLaw.map (openClockFunctional b E τ)

/-- For compact parameter sets (`b ∈ [β, 1/2-β]`, `E ∈ bulkInterval κ`) there is a uniform
`ℓ > 0` and, for each `b, E`, a phase interval `I = [θ₁, θ₂] ⊆ [0, 2π]` of length `≥ ℓ`
("independent of `W`", "its measure has a uniform positive lower bound on the compact `b, E`
sets") such that, along every clock sequence `n_j/W_j → τ > 0`, energies `E_j → E` (eventually
in `bulkInterval κ`, the moving energies of the `ClockSequence`), the law of the
Gaussian-probe interior clock after closing the far port by `e^{iθ}`, divided by `W²`
(`closedClockLaw`), converges to the law of `X_τ` (`openClockLaw b E τ`, base energy `E`)
**uniformly in `θ ∈ I`**: for every bounded continuous test `f` and `ε > 0`, eventually
`sup_{θ ∈ I} |E f(closed clock) - E f(X_τ)| ≤ ε`.
-/
def RobinEntranceLimit : Prop :=
  ∀ β κ : ℝ, 0 < β → β < 1 / 4 → 0 < κ → ∃ ℓ : ℝ, 0 < ℓ ∧
    ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ,
      ∃ θ₁ θ₂ : ℝ, 0 ≤ θ₁ ∧ θ₁ + ℓ ≤ θ₂ ∧ θ₂ ≤ 2 * π ∧
        ∀ τ : ℝ, 0 < τ → ∀ s : ClockSequence τ E, (∀ᶠ j in atTop, s.energy j ∈ bulkInterval κ) →
          ∀ f : ℝ →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ θ ∈ Set.Icc θ₁ θ₂,
            |∫ x, f x ∂closedClockLaw (s.W j) b (s.energy j) (s.n j) θ -
              ∫ x, f x ∂openClockLaw b E τ| ≤ ε

namespace NegativeClockAssembly

/-- The bounded continuous test `x ↦ exp(-c max(x, 0))`, `c ≥ 0`. -/
def expTest (c : ℝ) (hc : 0 ≤ c) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.exp (-(c * max x 0)),
      Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const)).neg⟩
    1 fun x y => by
      have h1 : ∀ z : ℝ, 0 ≤ Real.exp (-(c * max z 0)) ∧ Real.exp (-(c * max z 0)) ≤ 1 :=
        fun z => ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
          (by nlinarith [le_max_right z 0])⟩
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor <;> linarith [h1 x, h1 y]

theorem expTest_apply (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    expTest c hc x = Real.exp (-(c * max x 0)) := rfl

/-- All clock laws are carried by `[0, ∞)`. -/
theorem clockLaw_scaledClock_Iio (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    clockLaw (s.W j) b (scaledClock b s j) (Set.Iio 0) = 0 := by
  unfold clockLaw
  rw [Measure.map_apply (measurable_scaledClock b s j) measurableSet_Iio]
  have : scaledClock b s j ⁻¹' Set.Iio 0 = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [scaledClock_apply]
    exact div_nonneg (fullClock_quadForm_nonneg _ _ _ _ _ _) (sq_nonneg _)
  rw [this, measure_empty]

end NegativeClockAssembly

open NegativeClockAssembly NegativeClockClosure in

/-- **The negative-clock theorem** (`NegativeClockContract`), from
`FullSourceMomentsEnergyUniformContract` (only `clock` at `p = 1`, for `tight`) and the hypothesis
`RobinEntranceLimit` (used for `negative` only). No other hypothesis. Uniformity exactly as in
`NegativeClockContract`.
-/
theorem negativeClock_of (hFSM : FullSourceMomentsEnergyUniformContract)
    (hRobin : RobinEntranceLimit) : NegativeClockContract := by
  refine ⟨fun b hb0 hb1 E hE0 hE1 τ hτ s => negativeClock_tight hFSM hb0 hb1 hE0 hE1 hτ s, ?_⟩
  intro β κ T₀ p hβ hβ4 hκ hT₀ hp
  obtain ⟨ℓ, hℓ, hI⟩ := hRobin β κ hβ hβ4 hκ
  obtain ⟨CB, hCB0, hCB⟩ := negativeClock_openClock_negMoment β κ T₀ p hβ hβ4 hκ hT₀ hp
  refine ⟨(ℓ / (2 * π)) ^ (-p) * CB, fun b hb E hE τ hτ hτT s hev μ hμ => ?_⟩
  have hb' : β ≤ b ∧ b ≤ 1 / 2 - β := hb
  have hb0 : 0 < b := lt_of_lt_of_le hβ hb'.1
  have hb1 : b < 1 / 2 := lt_of_le_of_lt hb'.2 (by linarith)
  obtain ⟨θ₁, θ₂, h0, hℓ12, h2, hconv⟩ := hI b hb E hE
  have h12 : θ₁ < θ₂ := by linarith
  have hπ : 0 < 2 * π := by positivity
  have hℓa : ℓ / (2 * π) ≤ (θ₂ - θ₁) / (2 * π) := div_le_div_of_nonneg_right (by linarith) hπ.le
  have hℓ0 : 0 < ℓ / (2 * π) := div_pos hℓ hπ
  have ha0 : 0 < (θ₂ - θ₁) / (2 * π) := lt_of_lt_of_le hℓ0 hℓa
  obtain ⟨hprob, φ, hφ, hlim⟩ := hμ
  have hIio : μ (Set.Iio 0) = 0 :=
    negativeClock_limit_Iio_zero (ν := fun k => clockLaw (s.W (φ k)) b (scaledClock b s (φ k)))
      (fun k => clockLaw_scaledClock_Iio b s (φ k)) hlim
  set X := openClockFunctional b E τ with hXdef
  have hXm : Measurable X := measurable_openClockFunctional b E τ
  have hXpos : ∀ ω, 0 < X ω := openClockFunctional_pos (by linarith) E hτ
  -- Laplace domination in the limit
  have hL : ∀ s' : ℝ, 0 < s' → ∫ x, Real.exp (-(s' * max x 0)) ∂μ ≤
      ∫ ω, Real.exp (-(s' * ((θ₂ - θ₁) / (2 * π)) * X ω))
        ∂BlockBand.SourceProcess.canonicalWienerLaw := by
    intro s' hs'
    have hsa : 0 ≤ s' * ((θ₂ - θ₁) / (2 * π)) := mul_nonneg hs'.le ha0.le
    set m := ∫ x, expTest _ hsa x ∂openClockLaw b E τ with hm
    have hmX : m = ∫ ω, Real.exp (-(s' * ((θ₂ - θ₁) / (2 * π)) * X ω))
        ∂BlockBand.SourceProcess.canonicalWienerLaw := by
      rw [hm, openClockLaw, integral_map hXm.aemeasurable
        (expTest _ hsa).continuous.aestronglyMeasurable]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [expTest_apply, max_eq_left (hXpos ω).le]
    have hm0 : 0 ≤ m := integral_nonneg fun x => by rw [expTest_apply]; exact (Real.exp_pos _).le
    rw [← hmX]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev1 := hconv τ hτ s hev (expTest _ hsa) ε hε
    have hev2 := eventually_half_le_ratio s hτ
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hbd : ∀ᶠ k in atTop, ∫ x, expTest s' hs'.le x
        ∂clockLaw (s.W (φ k)) b (scaledClock b s (φ k)) ≤ m + ε := by
      filter_upwards [hφt.eventually (hev1.and (hev2.and hev))] with k hk
      obtain ⟨hk1, hk2, hk3⟩ := hk
      have hn := pos_of_half_le_ratio s hτ hk2
      have hE' : -2 + κ ≤ s.energy (φ k) ∧ s.energy (φ k) ≤ 2 - κ := hk3
      have hfin := negativeClock_finite_laplace hb0 hb1 (E := s.energy (φ k))
        (by linarith [hE'.1]) (by linarith [hE'.2]) (W := s.W (φ k)) hn h0 h12 h2 hs'.le
      have hRHS : ∫⁻ θ in Set.Ioc θ₁ θ₂, ENNReal.ofReal (∫ x, Real.exp
          (-(s' * ((θ₂ - θ₁) / (2 * π)) * max x 0))
          ∂closedClockLaw (s.W (φ k)) b (s.energy (φ k)) (s.n (φ k)) θ) ≤
          ∫⁻ θ in Set.Ioc θ₁ θ₂, ENNReal.ofReal (m + ε) := by
        refine setLIntegral_mono measurable_const fun θ hθ => ENNReal.ofReal_le_ofReal ?_
        have := hk1 θ ⟨hθ.1.le, hθ.2⟩
        rw [abs_le] at this
        have e : ∫ x, Real.exp (-(s' * ((θ₂ - θ₁) / (2 * π)) * max x 0))
            ∂closedClockLaw (s.W (φ k)) b (s.energy (φ k)) (s.n (φ k)) θ =
            ∫ x, expTest _ hsa x
              ∂closedClockLaw (s.W (φ k)) b (s.energy (φ k)) (s.n (φ k)) θ := by
          simp only [expTest_apply, mul_assoc]
        rw [e]; linarith [this.2]
      rw [setLIntegral_const, Real.volume_Ioc] at hRHS
      have hchain := hfin.trans (mul_le_mul' le_rfl hRHS)
      have e : ENNReal.ofReal (θ₂ - θ₁)⁻¹ * (ENNReal.ofReal (m + ε) *
          ENNReal.ofReal (θ₂ - θ₁)) = ENNReal.ofReal (m + ε) := by
        rw [mul_comm (ENNReal.ofReal (m + ε)), ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith)),
          inv_mul_cancel₀ (by linarith : θ₂ - θ₁ ≠ 0), ENNReal.ofReal_one, one_mul]
      rw [e] at hchain
      rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hchain
      simpa only [expTest_apply, scaledClock_eq_probeClock] using hchain
    have hlimf := hlim (expTest s' hs'.le)
    have := le_of_tendsto hlimf hbd
    simpa only [expTest_apply] using this
  obtain ⟨hIic, hmom⟩ := negativeClock_negMoment_of_laplace (μ := μ) hIio hXm hXpos ha0 hL hp
  refine ⟨hIic, hmom.trans ?_⟩
  have hX := hCB b hb E hE τ hτ hτT
  have hτp : 0 ≤ τ ^ (-p) := Real.rpow_nonneg hτ.le _
  have hapow : ((θ₂ - θ₁) / (2 * π)) ^ (-p) ≤ (ℓ / (2 * π)) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hℓ0 hℓa (by linarith)
  calc ENNReal.ofReal (((θ₂ - θ₁) / (2 * π)) ^ (-p)) *
        ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂BlockBand.SourceProcess.canonicalWienerLaw
      ≤ ENNReal.ofReal (((θ₂ - θ₁) / (2 * π)) ^ (-p)) * ENNReal.ofReal (CB * τ ^ (-p)) :=
        mul_le_mul' le_rfl hX
    _ = ENNReal.ofReal (((θ₂ - θ₁) / (2 * π)) ^ (-p) * (CB * τ ^ (-p))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le _)).symm
    _ ≤ ENNReal.ofReal ((ℓ / (2 * π)) ^ (-p) * CB * τ ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hapow (mul_nonneg hCB0 hτp)

end BlockBand.Endpoints.Clock
