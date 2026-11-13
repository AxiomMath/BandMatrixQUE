module

public import BlockBand.SourceProcess.Stochastic.Dyson.B2

/-!
# Dyson Brownian motion from the non-collision and angular clauses

`DysonNonCollision N` and `DysonAngular N` are clauses (b1) and (b3) of `DysonBrownianMotion N`,
as standalone propositions. `dysonBrownianMotion_of_ito_b1_b3` proves `DysonBrownianMotion N` from
the Itô formula `SemimartingaleItoFormula`, the stopping statement `StoppedSemimartingale` and
these two clauses: (b2) is `dysonBM_b2_of_b1` and (b4) is `dysonBM_b4_of_b1`. Clauses (b1) and
(b3) are hypotheses here; they are proved as `dysonNonCollision_holds` and `dysonAngular_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

/-- Clause (b1) of `DysonBrownianMotion N` (non-collision). -/
def DysonNonCollision (N : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)

/-- Clause (b3) of `DysonBrownianMotion N` (conditional angular martingale problem). -/
def DysonAngular (N : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
    (∀ (s : ℝ≥0), 0 < s → ∀ (q : Fin N → ℂ) (n : ℕ), 0 < n → ∀ (f : (Fin N → ℝ) → ℝ),
      ContDiff ℝ 2 f →
      ∀ (u : ℝ≥0) (Λ : Ω → ℝ),
        Measurable[⨆ v : ℝ≥0, MeasurableSpace.comap
          (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) inferInstance] Λ →
        (∃ C, ∀ ω, |Λ ω| ≤ C) →
        let e : Ω → ℝ := fun ω => Λ ω * (stoppedProcess (fun v ω =>
            f (fun i => dysonOverlap N q (F ω + G (s + v) ω) i) -
            f (fun i => dysonOverlap N q (F ω + G s ω) i) -
            ∫ r in Set.Ioc (0 : ℝ) v, angularGenerator N
              (dysonEigenvalue N (F ω + G (s + r.toNNReal) ω)) f
              (fun i => dysonOverlap N q (F ω + G (s + r.toNNReal) ω) i))
          (gapStop N (fun t ω => F ω + G t ω) s n) u ω)
        Integrable e Q ∧ ∫ ω, e ω ∂Q = 0)

/-- **`DysonBrownianMotion N` from `SemimartingaleItoFormula`, `StoppedSemimartingale`, (b1) and
(b3).** Clauses (b2) and (b4) are proved. -/
theorem dysonBrownianMotion_of_ito_b1_b3 (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) (N : ℕ) (h1 : DysonNonCollision N)
    (h3 : DysonAngular N) : DysonBrownianMotion N := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh
  have hb1 := h1 Ω Q 𝓖 G F hG hF hFh
  exact ⟨hb1, fun s hs q => dysonBM_b2_of_b1 hIto hStop hG hF hFh hb1 s hs q,
    h3 Ω Q 𝓖 G F hG hF hFh, dysonBM_b4_of_b1 hG hF hb1⟩

end BlockBand.SourceProcess.Stochastic.Dyson
