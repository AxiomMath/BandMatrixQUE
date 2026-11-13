module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The coupled pair of cutoff models

Two models are coupled using the same noise `Z` in a common padded space and the same signature
`𝖣`; a shared birth is chosen perpendicular to both old frames in unused near dimensions, and
equivariance and padding give the prescribed marginal law.

`IsCutoffCoupling` is the coupling used to compare two current cutoffs `h₁ ≤ h₂` at the
same count cap `K` and sample size `M`. On one driver space (initial data `S`, common noise `Z`),
two solutions `X₁, X₂` of the finite source equation with the same births satisfy all hypotheses
of `RankFreeCoupling`. Their initial frames are an isometric embedding of the canonical frames
`initialFrame K π t h_i` of the same entrance sequence `t`, and their Gram processes
`gramPair P X_i` are finite source models (`IsFiniteSourceModel`) at the cutoffs `h_i`.

`CoupledCutoffFrames` asserts that such a coupling exists for every entrance law of a random
transmission sequence (the quantification of `ModelExists`); it is proved as
`CoupledFrames.coupledCutoffFrames_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal ComplexConjugate

/-- The embedded canonical frame `Emb · initialFrame K π (t x) h` of a sequence-valued map `t`. -/
def cutFrame {Ω ι : Type*} [Fintype ι] {K : ℕ} (π : Type*) (Emb : Matrix ι (Fin K × Fin 2) ℂ)
    (tseq : Ω → ℕ → ℝ) (h : ℝ) (x : Ω) : Matrix ι (SrcCol K π) ℂ :=
  Emb * initialFrame K π (tseq x) h

/-- **The coupling of two cutoff models**. Data: a driver space over `S` with
law `driverLaw μ`, a near projection `P` of rank `Naux` on the padded space `ι`, an isometry
`Emb` of the canonical mode space into `ι`, a filtration `𝓖`, the entrance sequence `tseq`, the
sampled locations `σb`, `nb` shared births (times `τ`, columns `col`, vectors `w`, squared norms
`β`) and the two frames `X₁, X₂`. Conditions: every hypothesis of `RankFreeCoupling`
for the initial frames `cutFrame … h₁`, `cutFrame … h₂`; the total birth mass is that of the model
(`Σ_{a,k} d_* m_a / M`); and both Gram processes are finite source models with the given entrance,
at cutoffs `h₁` and `h₂`, on the same space, with the same `tseq` and `σb`. -/
structure IsCutoffCoupling (b E s T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (h₁ h₂ : ℝ) (K M : ℕ)
    (entrance : Measure (Measure unitInterval)) {ι S : Type} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ] (Naux : ℕ) (P : Matrix ι ι ℂ)
    (Emb : Matrix ι (Fin K × Fin 2) ℂ)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι))))
    (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ)
    (σb : DriverSample S (SourceNoise ι) → Fin p × Fin M → ℝ) {nb : ℕ}
    (τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0) (col : Fin nb → SrcCol K (Fin p × Fin M))
    (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ) (β : Fin nb → ℝ)
    (X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin p × Fin M)) ℂ) :
    Prop where
  nearProj : IsNearProjection P Naux
  isometry : Embᴴ * Emb = 1
  frame₁_meas : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0]
    (cutFrame (Fin p × Fin M) Emb tseq h₁)
  frame₂_meas : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0]
    (cutFrame (Fin p × Fin M) Emb tseq h₂)
  frame₁_two : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
    TwoProjection P (srcSignature K (Fin p × Fin M)) (cutFrame (Fin p × Fin M) Emb tseq h₁ x)
  frame₂_two : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
    TwoProjection P (srcSignature K (Fin p × Fin M)) (cutFrame (Fin p × Fin M) Emb tseq h₂ x)
  stopping : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
    (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))
  birth_meas : ∀ k, StronglyMeasurable[(stopping k).measurableSpace] (w k)
  col_inj : Function.Injective col
  col_sig : ∀ k j, srcSignature K (Fin p × Fin M) (col k) j = 0 ∧
    srcSignature K (Fin p × Fin M) j (col k) = 0
  col_zero : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ i,
    cutFrame (Fin p × Fin M) Emb tseq h₁ x i (col k) = 0 ∧
      cutFrame (Fin p × Fin M) Emb tseq h₂ x i (col k) = 0
  birth_near : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
    P *ᵥ w k x = w k x ∧ ∑ i, ‖w k x i‖ ^ 2 = β k
  birth_total : ∑ k, β k = ∑ i : Fin p × Fin M, dStar b * sourceMass s T (q i.1) / M
  sol₁ : IsBornSDESolution μ (transportD0 b E) Naux P (srcSignature K (Fin p × Fin M))
    (cutFrame (Fin p × Fin M) Emb tseq h₁) (frameBirthJump τ col w) X₁
  sol₂ : IsBornSDESolution μ (transportD0 b E) Naux P (srcSignature K (Fin p × Fin M))
    (cutFrame (Fin p × Fin M) Emb tseq h₂) (frameBirthJump τ col w) X₂
  perp : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ j, j ≠ col k →
    (∑ i, conj (X₁ (τ k x) x i j) * w k x i = 0) ∧ ∑ i, conj (X₂ (τ k x) x i j) * w k x i = 0
  model₁ : IsFiniteSourceModel b E s T q h₁ K M entrance 𝓖 (driverLaw (κ := SourceNoise ι) μ)
    tseq σb (fun t x => gramPair P (X₁ t x))
  model₂ : IsFiniteSourceModel b E s T q h₂ K M entrance 𝓖 (driverLaw (κ := SourceNoise ι) μ)
    tseq σb (fun t x => gramPair P (X₂ t x))

/-- **The coupled cutoff models exist** (the same
construction as `ModelExists`, run twice on one driver space; proved as
`CoupledFrames.coupledCutoffFrames_holds`). For every entrance that is
the trace-measure law of a random transmission sequence, cutoffs `0 < h₁ ≤ h₂`, every cap `K` and
`M > 0`, a coupling `IsCutoffCoupling` exists. -/
def CoupledCutoffFrames : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ ρ : Measure (ℕ → ℝ), IsProbabilityMeasure ρ → (∀ᵐ t ∂ρ, IsTransmissionSequence t) →
    ∀ (h₁ h₂ : ℝ) (K M : ℕ), 0 < h₁ → h₁ ≤ h₂ → 0 < M →
      ∃ (ι S : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : MeasurableSpace S)
        (μ : Measure S) (_ : IsProbabilityMeasure μ) (Naux : ℕ) (P : Matrix ι ι ℂ)
        (Emb : Matrix ι (Fin K × Fin 2) ℂ)
        (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι))))
        (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ)
        (σb : DriverSample S (SourceNoise ι) → Fin p × Fin M → ℝ) (nb : ℕ)
        (τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0)
        (col : Fin nb → SrcCol K (Fin p × Fin M)) (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ)
        (β : Fin nb → ℝ)
        (X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin p × Fin M)) ℂ),
        IsCutoffCoupling b E s T q h₁ h₂ K M (ρ.map seqTraceMeasure) μ Naux P Emb 𝓖 tseq σb τ col
          w β X₁ X₂

end BlockBand.SourceProcess.CutoffLimit
