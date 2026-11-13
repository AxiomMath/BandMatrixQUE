module

public import BlockBand.Transmission.PathJet.JetMeanLimit

/-!
# Generic path recursion: `L^p` linear recursion and the generic fresh step error

* `eLpNorm_linrec`: on any measure space, if `0 ≤ y_{j+1} ≤ ρy_j + e_j` a.e. for
  `1 ≤ j < n`, `‖y_1‖_p ≤ A` and `‖e_j‖_p ≤ B`, then `‖y_r‖_p ≤ ρ^{r-1}A + B/(1-ρ)` for
  `1 ≤ r ≤ n` (Minkowski only; no independence). No stopping is needed when the domain
  condition of the step is paid by a deterministic bound, as in `ae_jet_step`.
* `stepFluctOf Φ κ j`: for any jointly measurable fresh functional `Φ(X, fresh)`, the centred
  fresh error `‖Φ(X_j^in, fresh) - E_fresh Φ(X_j^in, ·)‖` of the growth step `j → j+1`
  (input `stepInput κ j`); `eLpNorm_stepFluctOf_le`: a uniform fresh fluctuation bound
  for passive inputs gives the same bound under `growthPathLaw` (Fubini over
  `pastLaw ⊗ freshLaw`). This is `eLpNorm_stepFluct_le` with `freshPortTrace` replaced
  by an arbitrary `Φ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

/-- **`L^p` bound for a linear recursion inequality.** -/
theorem eLpNorm_linrec {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {y e : ℕ → Ω → ℝ}
    {ρ A B : ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {n : ℕ} (hy0 : ∀ j ω, 0 ≤ y j ω) (hym : ∀ j, AEStronglyMeasurable (y j) μ)
    (hstep : ∀ j, 1 ≤ j → j < n → ∀ᵐ ω ∂μ, y (j + 1) ω ≤ ρ * y j ω + e j ω)
    (h1 : eLpNorm (y 1) p μ ≤ ENNReal.ofReal A)
    (he : ∀ j, 1 ≤ j → j < n → eLpNorm (e j) p μ ≤ ENNReal.ofReal B) :
    ∀ r, 1 ≤ r → r ≤ n → eLpNorm (y r) p μ ≤ ENNReal.ofReal (ρ ^ (r - 1) * A + B / (1 - ρ)) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  intro r hr hrn
  induction r, hr using Nat.le_induction with
  | base =>
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [Nat.sub_self, pow_zero, one_mul]
    have : 0 ≤ B / (1 - ρ) := by positivity
    linarith
  | succ r hr ih =>
    have ih' := ih (by omega)
    have hmono : eLpNorm (y (r + 1)) p μ ≤ eLpNorm (fun ω => ρ * y r ω + e r ω) p μ := by
      refine eLpNorm_mono_ae_real (hym (r + 1)) ?_
      filter_upwards [hstep r hr (by omega)] with ω hω
      rw [Real.norm_of_nonneg (hy0 _ _)]
      exact hω
    have hadd := eLpNorm_add_le (f := fun ω => ρ * y r ω) (g := e r) (p := p) (μ := μ) hp
    have hsm : eLpNorm (fun ω => ρ * y r ω) p μ = ENNReal.ofReal ρ * eLpNorm (y r) p μ := by
      have := eLpNorm_const_smul ρ (y r) p μ
      rw [show (ρ • y r) = fun ω => ρ * y r ω from rfl, Real.enorm_eq_ofReal hρ0] at this
      exact this
    refine hmono.trans (hadd.trans ?_)
    rw [hsm]
    calc ENNReal.ofReal ρ * eLpNorm (y r) p μ + eLpNorm (e r) p μ
        ≤ ENNReal.ofReal ρ * ENNReal.ofReal (ρ ^ (r - 1) * A + B / (1 - ρ)) + ENNReal.ofReal B :=
          add_le_add (mul_le_mul' le_rfl ih') (he r hr (by omega))
      _ = ENNReal.ofReal (ρ * (ρ ^ (r - 1) * A + B / (1 - ρ)) + B) := by
          rw [← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add (by positivity) hB]
      _ ≤ ENNReal.ofReal (ρ ^ (r + 1 - 1) * A + B / (1 - ρ)) := by
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          have hr' : r + 1 - 1 = (r - 1) + 1 := by omega
          rw [hr', pow_succ]
          field_simp
          ring

variable {W : ℕ}

/-- The centred fresh value of a functional `Φ` on `pastSample × freshSample`. -/
def stepPhiOf (Φ : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ) (b E : ℝ)
    (κ : ℝ → ℝ) (j : ℕ) (q : PastSample W j × LayerSample W .oneBlockOnePort) : ℝ :=
  ‖Φ (stepInput b E κ W j q.1) q.2 - ∫ f, Φ (stepInput b E κ W j q.1) f ∂freshLaw W b‖

/-- The fresh error `ξ_{j+1}` of the step `j → j+1` for the functional `Φ`. -/
def stepFluctOf (Φ : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ) (b E : ℝ)
    (κ : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) : ℝ :=
  stepPhiOf Φ b E κ j (pastCoords W j ω, freshSample W j ω)

section
variable {Φ : Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → ℂ}
  (hΦ : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort => Φ q.1 q.2)
include hΦ

theorem measurable_stepPhiOf (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) :
    Measurable (stepPhiOf Φ b E κ j) := by
  have hF : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      Φ (stepInput b E κ W j q.1) q.2 :=
    hΦ.comp (((measurable_stepInput b E κ j).comp measurable_fst).prodMk measurable_snd)
  have hI : Measurable fun p : PastSample W j =>
      ∫ f, Φ (stepInput b E κ W j p) f ∂freshLaw W b :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  exact (hF.sub (hI.comp measurable_fst)).norm

theorem measurable_stepFluctOf (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) :
    Measurable (stepFluctOf Φ b E κ j) :=
  (measurable_stepPhiOf hΦ b E κ j).comp
    ((measurable_pastCoords W j).prodMk (measurable_freshSample W j))

/-- **Moments of the generic fresh error** (Fubini over `pastLaw ⊗ freshLaw`). -/
theorem eLpNorm_stepFluctOf_le {b E p C : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hp : 0 < p) {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (j : ℕ)
    (hfl : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => ‖Φ X ω - ∫ ω', Φ X ω' ∂freshLaw W b‖) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal C) :
    eLpNorm (stepFluctOf Φ b E κ j) (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal C := by
  have hg := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have : stepFluctOf Φ b E κ j = stepPhiOf Φ b E κ j ∘ fun ω => (pastCoords W j ω, freshSample W j ω) := by
    funext ω; simp only [stepFluctOf, Function.comp]
  rw [this, ← eLpNorm_map_measure (measurable_stepPhiOf hΦ b E κ j).aestronglyMeasurable
    hg.aemeasurable, growthPathLaw_map_past_fresh]
  refine eLpNorm_prod_le_of_section (pastLaw W j b) (freshLaw W b) (measurable_stepPhiOf hΦ b E κ j)
    hp ?_
  filter_upwards [ae_pastLaw_hermitian W j b] with q hq
  exact hfl (stepInput b E κ W j q) (passiveY_stepInput hb hE1 hE2 hκ hq)

end

end BlockBand.Transmission.PathJet
