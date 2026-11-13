module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegAlg
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.IsometryZ
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerY
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Degenerate setups: a stopped solution and a family of regularized Brownian drivers

`DegSetup c W P` (square case, `σ : ℝ^d → ℝ^{d×d}` possibly degenerate, coefficients
`c : LipCoef d`): on `(Ω, 𝓕, P)` a joint vector integrator `Z = (M, B')`
(`Fin d ⊕ Fin (d + d)`, density `aZ`), a raw stopping time `τ` equal a.s. to the exit time
from `W`, a process `Y` with `Y_{t∧τ} = ξ + ∫_0^t 1_{[[0,τ]]} c.b(Y) + ∫_0^t 1_{[[0,τ]]} e_i dZ`,
and for every `n` a Brownian motion `Bd n = ∫ H n dZ` whose integrand is the regularized
driver `hval (c.σ Y) ε_n` on `[[0,τ]]` and `offval` after; pointwise, `aZ = zDens(1_{[[0,τ]]} c.σ(Y))`.

* `zBdd`: the `Z`-integrand `∑_k H n k · K_k` of a `Bd n`-integral, bounded predictable.
* **`eulZ_rep_all`**, **`eulZ_rep_stop`**: the Euler scheme driven by `Bd n` (unstopped, and
  stopped at `τ`), a.s. for all `t ≤ N`, as an Itô process against `Z` (associativity
  `vecCont_assoc`).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

variable {d : ℕ}

open Classical in
/-- A degenerate setup (see the module docstring). -/
structure DegSetup (c : LipCoef d) (W : Set (Fin d → ℝ)) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  𝓕 : Filtration ℝ≥0 mΩ
  ξ : Ω → Fin d → ℝ
  τ : Ω → WithTop ℝ≥0
  Y : ℝ≥0 → Ω → Fin d → ℝ
  Z : Fin d ⊕ Fin (d + d) → ℝ≥0 → Ω → ℝ
  aZ : Fin d ⊕ Fin (d + d) → Fin d ⊕ Fin (d + d) → ℝ≥0 → Ω → ℝ
  Bd : ℕ → ℝ≥0 → Ω → Fin d → ℝ
  H : ℕ → Fin d → Fin d ⊕ Fin (d + d) → ℝ × Ω → ℝ
  hZ : IsL2IntegratorVec P 𝓕 Z aZ
  hZs : ∀ i j t ω, aZ i j t ω = aZ j i t ω
  hH : ∀ n k c, IsBddPred 𝓕 (H n k c)
  hBd : ∀ n, IsFiltrationBrownian P 𝓕 (Bd n)
  hBdH : ∀ n (T : ℝ≥0) k, ∀ t ≤ T, haveI := hZ.isFiniteMeasure_bar T
    (fun ω => Bd n t ω k) =ᵐ[P] hZ.vecCont T (fun c => bpL2 _ (hH n k c)) t
  hξ : Measurable[𝓕 0] ξ
  hτ : IsStoppingTime 𝓕 τ
  hτe : ∀ᵐ ω ∂P, τ ω = exitTimeFrom W Y ω
  hYm : ∀ t, Measurable (Y t)
  hYc : ∀ᵐ ω ∂P, Continuous fun t => Y t ω
  hrep : ∀ n : ℕ, haveI := hZ.isFiniteMeasure_bar (n : ℝ≥0)
    ∀ᵐ ω ∂P, ∀ t ≤ (n : ℝ≥0), ∀ i, Y (stopTime (τ ω) t) ω i = ξ ω i +
      ((∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator
          (fun p => c.b (Y p.1.toNNReal p.2) i) (r, ω)) +
        hZ.vecCont (n : ℝ≥0) (fun j => bpL2 _ (isBddPred_unitStop hτ (Sum.inl i) j)) t ω)
  haZ : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ c₁ c₂, aZ c₁ c₂ r.toNNReal ω =
    zDens (if (r, ω) ∈ stopSet τ then c.σ (Y r.toNNReal ω) else 0) c₁ c₂
  hHv : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ n k c', H n k c' (r, ω) =
    if (r, ω) ∈ stopSet τ then hval (c.σ (Y r.toNNReal ω)) (regSeq n) k c' else offval k c'

namespace DegSetup

variable {c : LipCoef d} {W : Set (Fin d → ℝ)} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] (S : DegSetup c W P)

/-- The `Z`-integrand `∑_k H n k · K_k` of the `Bd n`-integral of `K`. -/
theorem zBdd (n : ℕ) {K : Fin d → ℝ × Ω → ℝ} (hK : ∀ k, IsBddPred S.𝓕 (K k))
    (c' : Fin d ⊕ Fin (d + d)) : IsBddPred S.𝓕 fun p => ∑ k, S.H n k c' p * K k p :=
  IsBddPred.sum Finset.univ fun k => (S.hH n k c').mul (hK k)

theorem measW (n : ℕ) : ∀ t, Measurable[S.𝓕 t] (S.Bd n t) :=
  fun t => ((S.hBd n).adapted t).measurable

/-- **The Euler scheme driven by `Bd n` against `Z`.** -/
theorem eulZ_rep_all (m n N : ℕ) :
    haveI := S.hZ.isFiniteMeasure_bar (N : ℝ≥0)
    ∀ᵐ ω ∂P, ∀ t ≤ (N : ℝ≥0), ∀ i, eulX c m S.ξ (S.Bd n) t ω i = S.ξ ω i +
      ((∫ r in Ioc (0 : ℝ) t, eulDrift c m S.ξ (S.Bd n) (N * 2 ^ m) i (r, ω)) +
        S.hZ.vecCont (N : ℝ≥0) (fun c' => bpL2 _ (S.zBdd n (fun k =>
          isBddPred_eulDiff c m (S.measW n) S.hξ (N * 2 ^ m) i k) c')) t ω) := by
  have := S.hZ.isFiniteMeasure_bar (N : ℝ≥0)
  have := (S.hBd n).isL2IntegratorVec.isFiniteMeasure_bar (N : ℝ≥0)
  filter_upwards [eulX_rep_all c m (S.hBd n) S.hξ N, ae_all_iff.2 fun i =>
    vecCont_assoc S.hZ (S.hBd n).isL2IntegratorVec (N : ℝ≥0) (S.hH n) (S.hBdH n N)
      (fun k => isBddPred_eulDiff c m (S.measW n) S.hξ (N * 2 ^ m) i k)] with ω h1 h2 t ht i
  rw [h1 t ht i, h2 i t]

/-- **The stopped Euler scheme driven by `Bd n` against `Z`.** -/
theorem eulZ_rep_stop (m n N : ℕ) :
    haveI := S.hZ.isFiniteMeasure_bar (N : ℝ≥0)
    ∀ᵐ ω ∂P, ∀ t ≤ (N : ℝ≥0), ∀ i, eulX c m S.ξ (S.Bd n) (stopTime (S.τ ω) t) ω i = S.ξ ω i +
      ((∫ r in Ioc (0 : ℝ) t, (stopSet S.τ).indicator
          (eulDrift c m S.ξ (S.Bd n) (N * 2 ^ m) i) (r, ω)) +
        S.hZ.vecCont (N : ℝ≥0) (fun c' => bpL2 _ (S.zBdd n (fun k =>
          (isBddPred_eulDiff c m (S.measW n) S.hξ (N * 2 ^ m) i k).indicator
            (measurableSet_stopSet S.𝓕 S.hτ)) c')) t ω) := by
  have := S.hZ.isFiniteMeasure_bar (N : ℝ≥0)
  have := (S.hBd n).isL2IntegratorVec.isFiniteMeasure_bar (N : ℝ≥0)
  filter_upwards [eulX_rep_stop c m (S.hBd n) S.hξ N S.hτ, ae_all_iff.2 fun i =>
    vecCont_assoc S.hZ (S.hBd n).isL2IntegratorVec (N : ℝ≥0) (S.hH n) (S.hBdH n N)
      (fun k => (isBddPred_eulDiff c m (S.measW n) S.hξ (N * 2 ^ m) i k).indicator
        (measurableSet_stopSet S.𝓕 S.hτ))] with ω h1 h2 t ht i
  rw [h1 t ht i, h2 i t]

end DegSetup

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
