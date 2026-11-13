module

public import BlockBand.Internal.Contracts.TransmissionSequences

/-!
# The complex source law theorem: decomposition into named statements

* `ComplexFiniteUniqueness` — **finite uniqueness** (adding the linear martingale equation of `𝒦`
  to the smooth Gram charts): two complex finite models with the same `(b, E, s, τ, m, h, K)` and
  entrance law give the same expectation of every bounded continuous function of the final source
  data.
* `ComplexSourceConstruction` — **identification of the critical limit and the positive
  construction** (the update, brackets and births at finite retained current rank; moments; the
  extended coupling; the real part of the closing error): the finite-width source-data law converges to
  some `ν`, and for some transmission limit at `κ ≡ 0` the expectations under *some* complex
  finite model at each `(h, K)` converge to `∫Φdν`, first `K → ∞`, then `h ↓ 0`.
* `KolmogorovConjugate` — the conjugate Kolmogorov inequality, an ingredient for the real part of
  the closing error in `ComplexSourceConstruction`; not used by the assembly.
* `RawTagMoments`, `ExtendedSourceMoments` — moment bounds for the bilinear tag forms of the
  interior resolvent and for the extended source matrix; `LengthContinuity` — the source data at
  lengths `r_j ~ T W_j` and at `⌊W_j T⌋` are close in probability.

`moments` and `extendedSourceMoments` are *derived* from `RawTagMoments` (`moments_of_raw`,
`extendedSourceMoments_of_raw`); `limit` is `ComplexFiniteUniqueness` + `ComplexSourceConstruction`
(`limit_of`); the sequence contract is `LengthContinuity` + Slutsky
(`complexSourceLimitSequence_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

/-- The domain of the `ComplexSourceLawContract.limit`:
`0 < b < 1/2`, bulk `E`, distinct
positive birth times below the final time `T`, nonnegative masses.
-/
def ComplexSourceLawDomain (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (T : ℝ) : Prop :=
  0 < b ∧ b < 1 / 2 ∧ -2 < E ∧ E < 2 ∧ Function.Injective τ ∧ (∀ j, 0 < τ j) ∧
    (∀ j, 0 ≤ m j) ∧ ∀ j, τ j < T

/-- The expectation of `Φ` of the final source data `(𝒦, M_pr, B_pr, (M𝖣M)_pr)` of a complex
finite model (the integrand of `ComplexModelValue`). -/
def modelExpectation {np : ℕ} (K : ℕ) (s T : ℝ) {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) : ℝ :=
  ∫ ω, Φ (modelSourceData (srcSignature K (Fin np)) (Kc (T - s).toNNReal ω)
    (G (T - s).toNNReal ω)) ∂Q

/-- **Finite uniqueness** (with deterministic births): on the domain, for a source-free start `0 < s < min τ_j`, cutoff `h > 0` and cap `K`, any two
complex finite models (`IsFiniteComplexSourceModel`: entrance of law `entrance`, Gram law of the
finite source SDE with births `d_* m_j`, complex source SDE with births `a m_j`) give
the same expectation of every bounded continuous test of the final source data. -/
def ComplexFiniteUniqueness : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ h : ℝ, 0 < h → ∀ (K : ℕ)
    (entrance : Measure (Measure unitInterval)) (Φ : BoundedContinuousFunction (SourceData np) ℝ),
  ∀ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓖₁ : Filtration ℝ≥0 m₁) (Q₁ : Measure Ω₁)
    (tseq₁ : Ω₁ → ℕ → ℝ) (G₁ : ℝ≥0 → Ω₁ → GramState (SrcCol K (Fin np)))
    (K₁ : ℝ≥0 → Ω₁ → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖₁ Q₁ tseq₁ G₁ K₁ →
  ∀ (Ω₂ : Type) (m₂ : MeasurableSpace Ω₂) (𝓖₂ : Filtration ℝ≥0 m₂) (Q₂ : Measure Ω₂)
    (tseq₂ : Ω₂ → ℕ → ℝ) (G₂ : ℝ≥0 → Ω₂ → GramState (SrcCol K (Fin np)))
    (K₂ : ℝ≥0 → Ω₂ → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖₂ Q₂ tseq₂ G₂ K₂ →
      modelExpectation K s T Q₁ G₁ K₁ Φ = modelExpectation K s T Q₂ G₂ K₂ Φ

/-- `Ψ` is realized by complex finite models: at every `(K, h)`, `h > 0`, some model exists and
its expectation of `Φ` is `Ψ K h`. -/
def RealizedValues (b E s T : ℝ) {np : ℕ} (τ m : Fin np → ℝ)
    (entrance : Measure (Measure unitInterval)) (Φ : BoundedContinuousFunction (SourceData np) ℝ)
    (Ψ : ℕ → ℝ → ℝ) : Prop :=
  ∀ K h, 0 < h → ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc ∧
      modelExpectation K s T Q G Kc Φ = Ψ K h

/-- **Identification and positive construction**, completed as in the source process theorem:
on the domain, the finite-width joint law of
`(𝒦, M_pr, B_pr, J_pr)` converges to some `ν`, and for some critical transmission limit `(P, μ)`
at `κ ≡ 0`, for every source-free start `s` and test `Φ`, the expectations `Ψ K h` under some
complex finite models (entrance `μ(s)`) converge to `∫Φdν`, first `K → ∞`, then `h ↓ 0`. -/
def ComplexSourceConstruction : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
    ∃ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ ∧
        ∀ s : ℝ, 0 < s → (∀ j, s < τ j) →
        ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
          ∃ Ψ : ℕ → ℝ → ℝ, RealizedValues b E s T τ m (entranceLaw P μ s) Φ Ψ ∧
            ∃ Λ : ℝ → ℝ, (∀ h, 0 < h → Tendsto (fun K => Ψ K h) atTop (𝓝 (Λ h))) ∧
              Tendsto Λ (𝓝[>] 0) (𝓝 (∫ y, Φ y ∂ν))

/-- **Raw tag moments**: bulk-uniform `p`-th moments of the normalized-tag bilinear forms
`ξ_j*Gξ'_k` of the interior resolvent, `E|ξ_j*Gξ'_k|^p ≤ C (m_j m_k)^{p/2}`, for independent tags
and for the same tag. -/
def RawTagMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ T p : ℝ, 1 ≤ p →
    ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ n : ℕ, (n : ℝ) ≤ T * W →
      ∀ (j k : Fin n) (mj mk : ℝ), 0 ≤ mj → 0 ≤ mk →
        (∫⁻ x, ENNReal.ofReal (‖star (tagVector W n j mj x.2.1) ⬝ᵥ
            ((fullInverse b E W n x.1).toBlocks₁₁ *ᵥ tagVector W n k mk x.2.2)‖ ^ p)
          ∂(growthPathLaw W b).prod
            ((circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W))) ≤
          ENNReal.ofReal (C * (mj * mk) ^ (p / 2))) ∧
        ∫⁻ x, ENNReal.ofReal (‖star (tagVector W n j mj x.2) ⬝ᵥ
            ((fullInverse b E W n x.1).toBlocks₁₁ *ᵥ tagVector W n j mj x.2)‖ ^ p)
          ∂(growthPathLaw W b).prod (circularVectorLaw (Fin W)) ≤
          ENNReal.ofReal (C * (mj * mj) ^ (p / 2))

/-- **Extended source moments**: `sup_W E[|Tr A_Q|^p + ‖A_Q‖_HS^p] < ∞`,
`A_Q = W⁻²Q^{1/2}GQ^{1/2}`, uniformly over profiles `0 ≤ q_k ≤ q̄`, `n ≤ TW`, bulk `E`. In the
paper it is derived from the raw tag moments by Gaussian sampling and Jensen.
-/
def ExtendedSourceMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ T p qmax : ℝ, 1 ≤ p → ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ n : ℕ, (n : ℝ) ≤ T * W → ∀ q : Fin n → ℝ, (∀ k, 0 ≤ q k ∧ q k ≤ qmax) →
        ∫⁻ ω, ENNReal.ofReal (‖(extendedSourceMatrix b E W n q ω).trace‖ ^ p +
            (Real.sqrt (∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2)) ^ p)
          ∂growthPathLaw W b ≤ ENNReal.ofReal C

/-- **Length continuity** of the source data: on the domain, along widths `W_j → ∞` and lengths
`r_j` with `r_j / W_j → T`, every entry of the source data at length `r_j` differs from the one at
`⌊W_j T⌋` (same path and tag Gaussians) by at least `ε` with probability tending to `0`. -/
def LengthContinuity : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ Wseq rseq : ℕ → ℕ, Tendsto Wseq atTop atTop →
    Tendsto (fun j => (rseq j : ℝ) / (Wseq j : ℝ)) atTop (𝓝 T) →
  ∀ (r : Fin 4) (i k : Fin np) (ε : ℝ), 0 < ε →
    Tendsto (fun j => probedPathLaw (Wseq j) np b {x | ε ≤
      ‖complexSourceData b E (Wseq j) (rseq j) τ m x r i k -
        complexSourceData b E (Wseq j) ⌊(Wseq j : ℝ) * T⌋₊ τ m x r i k‖}) atTop (𝓝 0)

/-- **The conjugate Kolmogorov inequality**: for `f` analytic on a neighbourhood of the
closed unit disk with `f(0) = 0` and `0 < p < 1`,
`∫|f(e^{iθ})|^p dθ/2π ≤ C_p (∫|Im f(e^{iθ})| dθ/2π)^p`. An ingredient for
`ComplexSourceConstruction`; not used by the assembly. -/
def KolmogorovConjugate : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, ∀ (f : ℂ → ℂ) (R : ℝ), 1 < R →
    DifferentiableOn ℂ f (Metric.ball 0 R) → f 0 = 0 →
      ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ‖f (Complex.exp (θ * Complex.I))‖ ^ p ≤
        C * (2 * Real.pi) ^ (1 - p) *
          (∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), |(f (Complex.exp (θ * Complex.I))).im|) ^ p

end BlockBand.SourceProcess.ComplexSourceLaw
