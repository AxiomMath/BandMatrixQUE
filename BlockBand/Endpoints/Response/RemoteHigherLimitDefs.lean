module

public import BlockBand.Endpoints.Response.NearSchattenDefs
public import BlockBand.Endpoints.Response.RemoteHigherDefs

/-!
# The regularized higher limit generator

For `ε > 0` write `H_ε = Tr f_ε(A)` (`f_ε(x) = (x+ε)^p - ε^p`; at a critical limit
`nsRegTrace p ε μ = ∫ f_ε(x)/x dμ`), `Diss_ε = Σ_i λ_i²(λ_i+ε)^{p-2}` (`nsDissTrace`) and
`δ = ε^p`. The regularized higher functional is `Φ_ε = (H_ε + ε^p)^r` (`rhlPowTrace`) and its
dissipation is `(H_ε + ε^p)^{r-1} Diss_ε` (`rhlDissPowTrace`). The shift by `ε^p` makes the chain
rule close without error: the regularized bracket is `Γ(H_ε,H_ε) = D Σ_i (λ_i f_ε'(λ_i))² S_ii`
and `(λ f_ε'(λ))² = p² λ²(λ+ε)^{p-2} (λ+ε)^p` with `(λ+ε)^p = f_ε(λ) + ε^p ≤ H_ε + ε^p`, so
`Γ ≤ Dp² Diss_ε (H_ε + ε^p)`; with `𝒢H_ε ≤ -(Dp(1-p)/2) Diss_ε` the chain rule
`𝒢Φ_ε = r(H_ε+ε^p)^{r-1}𝒢H_ε + ½ r(r-1)(H_ε+ε^p)^{r-2}Γ` gives
`𝒢Φ_ε ≤ -(D r p(1-rp)/2) (H_ε+ε^p)^{r-1} Diss_ε` exactly, the rate of the higher clock decay.
(Without the shift the bracket bound has an error `ε^p Diss_ε`.) Since `H_ε + ε^p ≥ ε^p > 0`,
`x ↦ x^r` is smooth on the range for every real `r ≥ 1`, so no integrality of `r` is needed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- The regularized higher functional `Φ_ε = (Tr f_ε(A) + ε^p)^r` of a clock trace measure. -/
def rhlPowTrace (p r ε : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  (nsRegTrace p ε μ + ENNReal.ofReal (ε ^ p)) ^ r

/-- Its dissipation `(Tr f_ε(A) + ε^p)^{r-1} Σ_i λ_i²(λ_i+ε)^{p-2}`. -/
def rhlDissPowTrace (p r ε : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  (nsRegTrace p ε μ + ENNReal.ofReal (ε ^ p)) ^ (r - 1) * nsDissTrace p ε μ

/-- The decay rate `κ_r = D₀ r p (1 - rp)/2` of the higher clock decay. -/
def rhlDecayRate (b E p r : ℝ) : ℝ := transportD0 b E * r * p * (1 - r * p) / 2

/-- The integrated regularized higher generator inequality at critical limits, the `r`-analogue
of `NsRegularizedLimitGenerator`. The bracket and the chain rule give
`𝒢H_p^r ≤ -D₀rp(1-rp)H_p^r/2`; the smooth power regularization, then trace stopping, pass this
chain rule and Gronwall to the limit.

Same law, parameters, source class and critical-limit encoding as `RhHigherLimitDecay` (fixed
`0 < b < 1/2`, bulk `E`, `0 < p < 1`, `r ≥ 1`, `pr < 1`, a unit source, a joint critical word
limit `(P, Z)` on `[t₁ + R, ∞)` with a.s. clock measures `μ_t`). For every `ε > 0` and all times
`t₁ + R < u₁ ≤ u₂`:
`E Φ_ε(u₂) + κ_r ∫_{u₁}^{u₂} E (H_ε+ε^p)^{r-1}Diss_ε(u) du ≤ E Φ_ε(u₁)`,
`Φ_ε = (H_ε + ε^p)^r`, `κ_r = D₀rp(1-rp)/2` (lower integrals in `ℝ≥0∞`, no measurability
assumed). At `r = 1` it is `NsRegularizedLimitGenerator` with the constant `ε^p` added to both
sides. -/
def RhlRegularizedLimitGenerator : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ),
      IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z →
    ∀ μ : ℝ → Ω → Measure ℝ, (∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ ω ∂P, IsClockMeasure Z t ω (μ t ω)) →
    ∀ ε : ℝ, 0 < ε → ∀ u₁ u₂ : ℝ, t₁ + R < u₁ → u₁ ≤ u₂ →
      ∫⁻ ω, rhlPowTrace p r ε (μ u₂ ω) ∂P +
          ENNReal.ofReal (rhlDecayRate b E p r) *
            ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, rhlDissPowTrace p r ε (μ u ω) ∂P ≤
        ∫⁻ ω, rhlPowTrace p r ε (μ u₁ ω) ∂P

end BlockBand.Endpoints
