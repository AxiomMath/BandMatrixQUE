module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramPassDefs

/-!
# The large-level local Gram estimate

`GramPassLocal` quantifies over every level `R`. When `W τ_i ∈ ℕ` for a birth `τ_i − s ∈ (a, t)`,
the grid point `cellT … (W τ_i) = τ_i − s` carries `pG = b3ClosedGramAt … (W τ_i)` (tag `i`
absent) but `gramJ (τ_i − s)` (birth `i` present), and the adjacent cells carry different alive
indicators; the difference is `E[1{σ_W^R = W τ_i} φ (F(Z^w) − F(Z'))]`, which is not controlled
for small `R`. For `R > R_χ + Σ_i d_* m_i` both `F` values vanish on `{Re Tr M ≥ R}`. Hence the
estimate below asks the conclusion only for `R ≥ R₀`, `R₀` independent of `W` (the constant `C_H`
is independent of `R`).

Measure: `closedLaw b W np` (unconditioned; the cap event is inside `b3Alive`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

/-- **`GramPassLocalLarge`** (with the endpoint correction): the statement of `GramPassLocal`
for every level `R ≥ R₀`, where `R₀` may depend on all the data except `W` (e.g.
`R₀ = R_χ + Σ_i d_* m_i`). -/
def GramPassLocalLarge : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
    ∀ χ : ℝ → ℝ, ContDiff ℝ 3 χ → HasCompactSupport χ →
    ∀ (F : ZSt K np → ℂ) (Λ : GSt K np × ZSt K np → ℂ), IsGenPair χ b E F Λ →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∀ a t : ℝ≥0, a ≤ t → a ∉ birthTimes s τ → t ∉ birthTimes s τ →
    ∀ (r : ℕ) (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0), (∀ l, u l ≤ a) →
      (∀ l, u l ∉ birthTimes s τ) → ∀ φ : BoundedContinuousFunction (Fin r → ℂ) ℝ,
      Tendsto (fun W => pStopSum χ b E s h τ m W (Vs W) F Λ R i u φ a t) atTop (𝓝 0)

/-- `GramPassLocal` implies `GramPassLocalLarge`. -/
theorem gramPassLocalLarge_of (h : GramPassLocal) : GramPassLocalLarge :=
  fun h1 h2 h3 h4 h5 b E np τ m T s h' K Vs hD χ hc hs F Λ hp =>
    ⟨0, fun R _ => h h1 h2 h3 h4 h5 b E np τ m T s h' K Vs hD χ hc hs F Λ hp R⟩

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
