module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealBridge
public import BlockBand.SourceProcess.Stochastic.GramChar.Conditional
public import BlockBand.SourceProcess.Stochastic.Bridges.NativeIto
public import BlockBand.SourceProcess.Stochastic.ItoNative.CoordRepBuild
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The ambient Gram process in real coordinates

The real coordinates `toGramReal` of the Gram process of an ambient source solution form a
continuous semimartingale (`ambient_isContinuousSemimartingale`), whose drift and covariance are
`gramRealDrift` and `gramRealCov` of the Gram state (`ambient_drift_eq`, `ambient_cov_eq`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramChar BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- `toGramReal` as a real-linear map. -/
def toGramRealLin : (Matrix c c ℂ × Matrix c c ℂ) →ₗ[ℝ] (Fin (gramDim c) → ℝ) where
  toFun := toGramReal
  map_add' x y := by
    funext i
    simp only [toGramReal, Pi.add_apply, reIm, gramEntry]
    split_ifs <;> simp
  map_smul' r x := by
    funext i
    simp only [toGramReal, Pi.smul_apply, reIm, gramEntry, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.real_smul]

/-- `toGramReal` as a continuous linear map. -/
def toGramRealCLM :=
  toCLM (F₁ := Matrix c c ℂ × Matrix c c ℂ) (F₂ := Fin (gramDim c) → ℝ) (toGramRealLin (c := c))

omit [DecidableEq c] in
theorem toGramRealCLM_apply (H : Matrix c c ℂ × Matrix c c ℂ) :
    toGramRealCLM H = toGramReal H := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [DecidableEq c] in
theorem ambient_isContinuousSemimartingale {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X) :
    IsContinuousSemimartingale (driverLaw (κ := SourceNoise ι) μ)
      (driverAugmented (κ := SourceNoise ι) μ) (fun t x => toGramReal (gramPair P (X t x)))
      (fun t x => toGramReal (gramDrift D0 Naux P D (X t x)))
      (fun t x => Matrix.of fun i j => ∑ a, toGramReal (gramNoise D0 P D a (X t x)) i *
        toGramReal (gramNoise D0 P D a (X t x)) j) :=
  ((gramPair_nativeIto μ hX).map_clm (toGramRealCLM (c := c))).isContinuousSemimartingale

theorem ambient_drift_eq {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) :
    toGramReal (gramDrift D0 Naux P D V) = gramRealDrift D0 D (toGramReal (gramPair P V)) := by
  rw [gramDrift_eq hD0 hP hV, gramRealDrift, fromGramReal_toGramReal]
  rfl

theorem ambient_cov_eq {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    (hV : TwoProjection P D V) :
    (Matrix.of fun i j => ∑ a, toGramReal (gramNoise D0 P D a V) i *
      toGramReal (gramNoise D0 P D a V) j) = gramRealCov D0 D (toGramReal (gramPair P V)) := by
  ext i j
  simp only [Matrix.of_apply, toGramReal_apply, reIm_mul_reIm, Finset.sum_add_distrib,
    ← map_sum]
  simp only [fun a => star_gramEntry_of_herm (gramNoise_herm D0 hP.1 D a V).1
    (gramNoise_herm D0 hP.1 D a V).2 (qi j).1, gramNoise_cov_entry hD0 hP hD hV]
  simp only [gramRealCov, fromGramReal_toGramReal, realCovEntry_eq]
  rfl

end BlockBand.SourceProcess.Stochastic.GramUniqueness
