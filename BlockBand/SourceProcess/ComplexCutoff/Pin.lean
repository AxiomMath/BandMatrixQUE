module

public import BlockBand.SourceProcess.ComplexConstruct.Interface
public import BlockBand.SourceProcess.ComplexUnique.Noise
public import BlockBand.SourceProcess.CutoffLimit.Pin

/-!
# The coupled complex cutoff models and the extended rank-free coupling

* `IsComplexCutoffCoupling`: the frame coupling `IsCutoffCoupling` of two cutoffs `h₁ ≤ h₂` on one
  driver space (same `Z`, shared births), with the probe-birth data of the complex model, extended
  by the `𝒦` equation `d𝒦 = -2iη V_pr*dA V_pr` driven by the same noise: `Y_i` is the Itô
  integral of the frame coefficient `kNoise(X_i)`, and `𝒦_i = J_𝒦 + (Y_i - Y_i(0))_pr`. Both
  `(gramPair P X_i, 𝒦_i)` are complex finite models (`IsFiniteComplexSourceModel`) at the
  cutoffs `h_i`.
* `CoupledComplexCutoff`: such a coupling exists for every entrance law of a random
  transmission sequence (the quantification of `ComplexModelExists`); it is proved as
  `coupledComplexCutoff_holds`.
* `ExtendedRankFreeCoupling`: the rank-free coupling estimate extended to the `𝒦` equation; it
  follows from `StoppedBracketCoupling` (`extendedRankFreeCoupling_of`), which is proved as
  `stoppedBracketCoupling_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.ComplexUnique
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.CutoffLimit
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal ComplexConjugate

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The `𝒦` process of the coupling: `𝒦(t) = J_𝒦(t) + (Y_t - Y_0)_pr`, `J_𝒦` the deterministic
birth entries `a m_j` at `τ_j - s`. -/
def kProc (E s : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) {Ω : Type*}
    (Y : ℝ≥0 → Ω → Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) (t : ℝ≥0) (x : Ω) :
    Matrix (Fin np) (Fin np) ℂ :=
  kBirthJump E (fun j => τ j - s) m (t : ℝ) + probeBlock (Y t x - Y 0 x)

/-- **The coupling of two complex cutoff models**. The frame part is `IsCutoffCoupling` (every
hypothesis of `RankFreeCoupling`, an isometric embedding of the canonical initial frames, shared
births of total mass `Σ_j d_* m_j`); `Y_i` solves `dY = kNoise(X_i) dW` (zero drift) with the same noise; both
`(gramPair P X_i, kProc … Y_i)` are complex finite models at cutoff `h_i` with the same `tseq`.
-/
structure IsComplexCutoffCoupling (b E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (h₁ h₂ : ℝ) (K : ℕ)
    (entrance : Measure (Measure unitInterval)) {ι S : Type} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ] (Naux : ℕ) (P : Matrix ι ι ℂ)
    (Emb : Matrix ι (Fin K × Fin 2) ℂ)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι))))
    (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ) {nb : ℕ}
    (tb : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0) (col : Fin nb → SrcCol K (Fin np))
    (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ) (β : Fin nb → ℝ)
    (X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin np)) ℂ)
    (Y₁ Y₂ : ℝ≥0 → DriverSample S (SourceNoise ι) →
      Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) : Prop where
  nearProj : IsNearProjection P Naux
  isometry : Embᴴ * Emb = 1
  frame₁_meas : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0]
    (cutFrame (Fin np) Emb tseq h₁)
  frame₂_meas : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0]
    (cutFrame (Fin np) Emb tseq h₂)
  frame₁_two : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
    TwoProjection P (srcSignature K (Fin np)) (cutFrame (Fin np) Emb tseq h₁ x)
  frame₂_two : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
    TwoProjection P (srcSignature K (Fin np)) (cutFrame (Fin np) Emb tseq h₂ x)
  stopping : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
    (fun x => ((tb k x : ℝ≥0) : WithTop ℝ≥0))
  birth_meas : ∀ k, StronglyMeasurable[(stopping k).measurableSpace] (w k)
  col_inj : Function.Injective col
  col_sig : ∀ k j, srcSignature K (Fin np) (col k) j = 0 ∧ srcSignature K (Fin np) j (col k) = 0
  col_zero : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ i,
    cutFrame (Fin np) Emb tseq h₁ x i (col k) = 0 ∧ cutFrame (Fin np) Emb tseq h₂ x i (col k) = 0
  birth_near : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
    P *ᵥ w k x = w k x ∧ ∑ i, ‖w k x i‖ ^ 2 = β k
  birth_total : ∑ k, β k = ∑ j, dStar b * m j
  sol₁ : IsBornSDESolution μ (transportD0 b E) Naux P (srcSignature K (Fin np))
    (cutFrame (Fin np) Emb tseq h₁) (frameBirthJump tb col w) X₁
  sol₂ : IsBornSDESolution μ (transportD0 b E) Naux P (srcSignature K (Fin np))
    (cutFrame (Fin np) Emb tseq h₂) (frameBirthJump tb col w) X₂
  perp : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ j, j ≠ col k →
    (∑ i, conj (X₁ (tb k x) x i j) * w k x i = 0) ∧ ∑ i, conj (X₂ (tb k x) x i j) * w k x i = 0
  kSol₁ : IsNativeItoProcess μ Y₁ (fun _ _ => 0)
    (fun a t x => kNoise (transportD0 b E) (etaZ b E) P (srcSignature K (Fin np)) a (X₁ t x))
  kSol₂ : IsNativeItoProcess μ Y₂ (fun _ _ => 0)
    (fun a t x => kNoise (transportD0 b E) (etaZ b E) P (srcSignature K (Fin np)) a (X₂ t x))
  model₁ : IsFiniteComplexSourceModel b E s τ m h₁ K entrance 𝓖
    (driverLaw (κ := SourceNoise ι) μ) tseq (fun t x => gramPair P (X₁ t x)) (kProc E s τ m Y₁)
  model₂ : IsFiniteComplexSourceModel b E s τ m h₂ K entrance 𝓖
    (driverLaw (κ := SourceNoise ι) μ) tseq (fun t x => gramPair P (X₂ t x)) (kProc E s τ m Y₂)

/-- **The coupled complex cutoff models exist**: the coupled cutoff frames with the
deterministic probe births of the complex model, plus the `𝒦` integral of the same noise. On the
domain, for a source-free start `0 < s < min τ_j`, every law `ρ` of a random transmission sequence,
cutoffs `0 < h₁ ≤ h₂` and cap `K`, a coupling `IsComplexCutoffCoupling` with entrance
`ρ.map seqTraceMeasure` exists. -/
def CoupledComplexCutoff : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) →
  ∀ ρ : Measure (ℕ → ℝ), IsProbabilityMeasure ρ → (∀ᵐ t ∂ρ, IsTransmissionSequence t) →
  ∀ (h₁ h₂ : ℝ) (K : ℕ), 0 < h₁ → h₁ ≤ h₂ →
    ∃ (ι S : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : MeasurableSpace S)
      (μ : Measure S) (_ : IsProbabilityMeasure μ) (Naux : ℕ) (P : Matrix ι ι ℂ)
      (Emb : Matrix ι (Fin K × Fin 2) ℂ)
      (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι))))
      (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ) (nb : ℕ)
      (tb : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0) (col : Fin nb → SrcCol K (Fin np))
      (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ) (β : Fin nb → ℝ)
      (X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin np)) ℂ)
      (Y₁ Y₂ : ℝ≥0 → DriverSample S (SourceNoise ι) →
        Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ),
      IsComplexCutoffCoupling b E s τ m h₁ h₂ K (ρ.map seqTraceMeasure) μ Naux P Emb 𝓖 tseq tb
        col w β X₁ X₂ Y₁ Y₂

/-- For `D₀, η` there is
`C: ℝ → ℝ` (the constant `C_L` at trace level `L`) such that, under every hypothesis of the
`RankFreeCoupling` and for Itô processes `Y_i` (`IsNativeItoProcess`) with zero drift and diffusion
`kNoise(X_i)` (`d𝒦 = -2iη V*dA V`), for all `L, u, δ > 0` and `t`, with `ΔY_i = Y_i(t) - Y_i(0)`:
`P{‖ΔY₁ - ΔY₂‖²_HS > δ} ≤ 2(E R₀ + 2B)/L + e^{D₀L²t/2} E X₀/u + C_L u t/δ` and
`P{‖ΔY₁‖²_HS > δ} ≤ (E R₀ + 2B)/L + C_L t/δ`.
`C_L` does not depend on the spaces `ι, c`.
-/
def ExtendedRankFreeCoupling : Prop :=
  ∀ D0 η : ℝ, ∃ C : ℝ → ℝ,
  ∀ (ι c S : Type) [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (Naux : ℕ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ), 0 < D0 → IsNearProjection P Naux → IsSignature D →
  ∀ ξ₁ ξ₂ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₁ →
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₂ →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₁ x)) →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₂ x)) →
  ∀ (nb : ℕ) (tb : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ) (β : Fin nb → ℝ)
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((tb k x : ℝ≥0) : WithTop ℝ≥0))),
    (∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k)) →
    Function.Injective col → (∀ k j, D (col k) j = 0 ∧ D j (col k) = 0) →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ i, ξ₁ x i (col k) = 0 ∧ ξ₂ x i (col k) = 0) →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      P *ᵥ w k x = w k x ∧ ∑ i, ‖w k x i‖ ^ 2 = β k) →
  ∀ X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    IsBornSDESolution μ D0 Naux P D ξ₁ (frameBirthJump tb col w) X₁ →
    IsBornSDESolution μ D0 Naux P D ξ₂ (frameBirthJump tb col w) X₂ →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ j, j ≠ col k →
      (∑ i, conj (X₁ (tb k x) x i j) * w k x i = 0) ∧
        ∑ i, conj (X₂ (tb k x) x i j) * w k x i = 0) →
  ∀ Y₁ Y₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c c ℂ,
    IsNativeItoProcess μ Y₁ (fun _ _ => 0) (fun a t x => kNoise D0 η P D a (X₁ t x)) →
    IsNativeItoProcess μ Y₂ (fun _ _ => 0) (fun a t x => kNoise D0 η P D a (X₂ t x)) →
  ∀ (L u δ : ℝ) (t : ℝ≥0), 0 < L → 0 < u → 0 < δ →
    driverLaw (κ := SourceNoise ι) μ
        {x | δ < hsSq ((Y₁ t x - Y₁ 0 x) - (Y₂ t x - Y₂ 0 x))} ≤
      2 * ((∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) +
            ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L +
        ENNReal.ofReal (Real.exp (D0 * L ^ 2 * t / 2)) *
          (∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x - ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) /
          ENNReal.ofReal u +
        ENNReal.ofReal (C L * u * t / δ) ∧
    driverLaw (κ := SourceNoise ι) μ {x | δ < hsSq (Y₁ t x - Y₁ 0 x)} ≤
      ((∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) +
            ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L +
        ENNReal.ofReal (C L * t / δ)

end BlockBand.SourceProcess.ComplexCutoff
