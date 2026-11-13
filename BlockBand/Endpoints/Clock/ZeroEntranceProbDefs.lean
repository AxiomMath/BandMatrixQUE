module

public import BlockBand.Endpoints.Clock.OpenInputsPath
public import BlockBand.Endpoints.Clock.CavityMeanProb
public import BlockBand.Endpoints.Clock.ZeroEntranceChain

/-!
# The zero-entrance lemma: the statement

This file states the zero-entrance lemma, `ZeroEntranceStatement`; it is proved by
`zeroEntrance_of`.

## Objects

* `zeTrace e D J ζ ω = W⁻¹ Tr (ζ - X_J)⁻¹` is the normalized trace (`normalizedResolventTrace`,
  sign convention of the cavity-mean lemma), and its first `z`-derivative is
  `deriv (fun ζ => zeTrace e D J ζ ω) z`.
* `stieltjesG μ ζ = ∫ (ζ - x)⁻¹ dμ(x)` is the Stieltjes transform `G_μ` in the same convention
  (for `μ` the empirical law of a Hermitian `X`, `G_μ(ζ) = W⁻¹ Tr (ζ - X)⁻¹`).
* The compact parameter sets are `zeParam κ b e : κ ≤ b ∧ κ ≤ 1 - 2b ∧ κ ≤ 4 - e²` (`κ > 0`);
  every compact subset of `(0,1/2) × (-2,2)` lies in one of them (as for `zeroEntrance_finite_seed`).

## Representation of "the empirical law converges in probability"

The empirical law of the Hermitian (almost surely) `X_J` is `W⁻¹ Σ_i δ_{λ_i(X_J)}`; its
Stieltjes transform is `zeTrace e 0 J ζ`. We state convergence in probability to the deterministic
probability measure `μ_J` in its Stieltjes form: for every `ζ` in the upper half-plane and every
`δ > 0`, `P(|zeTrace e 0 J ζ - G_{μ_J}(ζ)| ≥ δ) → 0` as `W → ∞`. For a deterministic probability
limit this is equivalent to weak convergence in probability of the empirical laws (the Stieltjes
transforms at a countable dense set of `ζ` determine the vague topology on sub-probability
measures, and a probability limit upgrades vague to weak convergence; e.g. Anderson–Guionnet–
Zeitouni, Thm. 2.4.4). This is the form in which the limit is proved (conditional concentration, together with a
countable set of Stieltjes tests). The statement is in addition quantitative (clause (iii) below gives the rate `C_J/W` for the mean and
`C_J √p / W` for the fluctuation at the matched test).

## The statement (`ZeroEntranceStatement`)

There is a deterministic family of measures `μ b e J` such that:
* (i) for `0 < b < 1/2`, `-2 < e < 2` and every `J`: `μ b e J` is a probability measure and the
  empirical law of `X_J` (`X_0 = 0`) converges in probability to it (Stieltjes form above);
* (ii) the finite seed bound: for every `κ > 0` there are `C, c_* > 0` such that
  `|G_{μ_J}(z) - a| ≤ C e^{-c_* J}` for every `J` and every `(b, e)` in the compact set;
* (iii) for every `κ > 0` and every fixed `J` there are `a_J, C_J > 0` and `W₀` such that for
  `W ≥ W₀`, uniformly for `(b, e)` in the compact set:
  - means (uniform convergence on the compact parameter set, with rate):
    `|E h_J(z) - G_{μ_J}(z)| ≤ C_J/W` and `|E h_J'(z) - G_{μ_J}'(z)| ≤ C_J/W` (`X_0 = 0`);
  - concentration, uniform in every deterministic Hermitian initial matrix `D`:
    `‖h_J(z) - E h_J(z)‖_p ≤ C_J √p / W` and the same for `h_J'(z)`, `2 ≤ p ≤ a_J W`;
  - perturbation: for every deterministic Hermitian `D` with `‖D‖ ≤ ε` (operator norm),
    `|E h_J^D(z) - E h_J^0(z)| ≤ C_J ε` and the same for the derivative.
  Here `h_J = zeTrace e D J`, `E` is the expectation under `oneEndedLaw W b J`, the centered
  `L^p` norm is `eLpNorm` of order `p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- `h_J(ζ) = W⁻¹ Tr (ζ - X_J)⁻¹` along the one-ended path `X_0 = D`. -/
def zeTrace (e : ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (ζ : ℂ)
    (ω : Fin J → OneEndedLayer W) : ℂ :=
  normalizedResolventTrace (oneEndedX e D J ω) ζ

/-- The Stieltjes transform `G_μ(ζ) = ∫ (ζ - x)⁻¹ dμ(x)` (sign convention of
the cavity-mean lemma, `f(ζ) = W⁻¹ Tr (ζ - X)⁻¹`). -/
def stieltjesG (μ : Measure ℝ) (ζ : ℂ) : ℂ := ∫ x, (ζ - (x : ℂ))⁻¹ ∂μ

/-- The compact parameter sets `κ ≤ b`, `κ ≤ 1 - 2b`, `κ ≤ 4 - e²`. -/
def zeParam (κ b e : ℝ) : Prop := κ ≤ b ∧ κ ≤ 1 - 2 * b ∧ κ ≤ 4 - e ^ 2

/-- The law of the first `J` layers is a probability measure. -/
instance oneEndedLaw_isProbabilityMeasure (W : ℕ) (b : ℝ) (J : ℕ) :
    IsProbabilityMeasure (oneEndedLaw W b J) := by
  unfold oneEndedLaw; infer_instance

/-- The `k = 0` clauses (ii)–(iii) of the cavity-mean lemma with constants uniform for `b` in the
compact set `κ ≤ b`, `κ ≤ 1 - 2b` (proved from `CavityMeanStatement` by rescaling the fresh
Gaussians, `cavityLayerUniform_of`). -/
def CavityLayerUniform : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ η₀ M : ℝ, 0 < η₀ → ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧
    ∀ b : ℝ, κ ≤ b → κ ≤ 1 - 2 * b → ∀ W : ℕ, 0 < W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ (e : ℝ) (z' : ℂ), η₀ ≤ z'.im →
        ‖z'‖ ≤ M →
        ‖(∫ ω, cavityHplus e X z' ω ∂layerLaw W b .oneBlockOnePort) - cavityU X b e z'‖ ≤
            C / (W : ℝ) ^ 2 ∧
        ∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
          eLpNorm (fun ω => cavityHplus e X z' ω -
              ∫ ω', cavityHplus e X z' ω' ∂layerLaw W b .oneBlockOnePort)
            (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
            ENNReal.ofReal (C * Real.sqrt p / W)

/-- The Gaussian absorption lemma for the one-block one-port layer with constants uniform for `b`
in the compact set `κ ≤ b`, `κ ≤ 1 - 2b` (proved from `GaussianAbsorptionContract` by rescaling,
`absorptionUniform_of`). -/
def AbsorptionUniform : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ η₀ M : ℝ, 0 < η₀ → ∃ ε₁ C : ℝ, 0 < ε₁ ∧ 0 < C ∧
    ∀ b : ℝ, κ ≤ b → κ ≤ 1 - 2 * b → ∀ W : ℕ, 0 < W →
      ∀ X : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ,
        X.IsHermitian → ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
          (∀ᵐ ω ∂layerLaw W b .oneBlockOnePort,
            IsUnit (layerMatrix .oneBlockOnePort E z X ω).det) ∧
          ∀ p : ℝ, 1 ≤ p → p ≤ ε₁ * W →
            eLpNorm (fun ω => ‖layerResolvent .oneBlockOnePort E z X ω‖) (ENNReal.ofReal p)
              (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C

/-- **the zero-entrance lemma**, full statement; see the module docstring.
Operator norm `‖D‖` (`Matrix.Norms.L2Operator`). -/
def ZeroEntranceStatement : Prop :=
  ∃ μ : ℝ → ℝ → ℕ → Measure ℝ,
    (∀ b e : ℝ, 0 < b → b < 1 / 2 → -2 < e → e < 2 → ∀ J : ℕ,
      IsProbabilityMeasure (μ b e J) ∧
      ∀ ζ : ℂ, 0 < ζ.im → ∀ δ : ℝ, 0 < δ →
        Tendsto (fun W : ℕ => oneEndedLaw W b J
            {ω | δ ≤ ‖zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ ω - stieltjesG (μ b e J) ζ‖})
          atTop (𝓝 0)) ∧
    (∀ κ : ℝ, 0 < κ → ∃ C cstar : ℝ, 0 < C ∧ 0 < cstar ∧ ∀ (b e : ℝ) (J : ℕ), zeParam κ b e →
      ‖stieltjesG (μ b e J) (boundaryZ b e) - matchedA e‖ ≤ C * Real.exp (-cstar * J)) ∧
    (∀ κ : ℝ, 0 < κ → ∀ J : ℕ, ∃ (a C : ℝ) (W₀ : ℕ), 0 < a ∧ 0 < C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ b e : ℝ, zeParam κ b e →
        ‖(∫ ω, zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J (boundaryZ b e) ω
            ∂oneEndedLaw W b J) - stieltjesG (μ b e J) (boundaryZ b e)‖ ≤ C / W ∧
        ‖(∫ ω, deriv (fun ζ => zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ ω) (boundaryZ b e)
            ∂oneEndedLaw W b J) - deriv (stieltjesG (μ b e J)) (boundaryZ b e)‖ ≤ C / W ∧
        (∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ∀ p : ℝ, 2 ≤ p → p ≤ a * W →
          eLpNorm (fun ω => zeTrace e D J (boundaryZ b e) ω -
              ∫ ω', zeTrace e D J (boundaryZ b e) ω' ∂oneEndedLaw W b J)
            (ENNReal.ofReal p) (oneEndedLaw W b J) ≤ ENNReal.ofReal (C * Real.sqrt p / W) ∧
          eLpNorm (fun ω => deriv (fun ζ => zeTrace e D J ζ ω) (boundaryZ b e) -
              ∫ ω', deriv (fun ζ => zeTrace e D J ζ ω') (boundaryZ b e) ∂oneEndedLaw W b J)
            (ENNReal.ofReal p) (oneEndedLaw W b J) ≤ ENNReal.ofReal (C * Real.sqrt p / W)) ∧
        (∀ (ε : ℝ) (D : Matrix (Fin W) (Fin W) ℂ), D.IsHermitian → ‖D‖ ≤ ε →
          ‖(∫ ω, zeTrace e D J (boundaryZ b e) ω ∂oneEndedLaw W b J) -
              ∫ ω, zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J (boundaryZ b e) ω
                ∂oneEndedLaw W b J‖ ≤ C * ε ∧
          ‖(∫ ω, deriv (fun ζ => zeTrace e D J ζ ω) (boundaryZ b e) ∂oneEndedLaw W b J) -
              ∫ ω, deriv (fun ζ => zeTrace e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ ω)
                (boundaryZ b e) ∂oneEndedLaw W b J‖ ≤ C * ε))

end BlockBand.Endpoints.Clock
