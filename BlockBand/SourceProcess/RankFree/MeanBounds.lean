module

public import BlockBand.SourceProcess.RankFree.TraceDominates
public import BlockBand.SourceProcess.RankFree.DistanceDrift
public import BlockBand.SourceProcess.Stochastic.ItoNative.Pair

/-!
# The two stopped mean bounds of the rank-free coupling

* `lintegral_stopped_trace_le`: for every stopping time `σ`, with `R = traceProc X₁ + traceProc X₂`,
  `E R_{t∧σ} ≤ E(‖ξ₁‖² + ‖ξ₂‖²) + 2 ∑_k β_k` (zero drift, nonnegativity).
* `lintegral_stopped_distance_le`: for every stopping time `ρ` before which
  `‖X₁‖² + ‖X₂‖² ≤ K`, `E e^{-c(t∧ρ)} ‖X₁ - X₂‖²_{t∧ρ} ≤ E ‖ξ₁ - ξ₂‖²` with `c = D₀K²/2`
  (`distance_generator_le`: the upper drift `D₀R²X/2 ≤ cX`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {nb : ℕ}

omit [DecidableEq ι] [DecidableEq c] in
theorem hsSq_eq (V : Matrix ι c ℂ) : hsSq V = ‖V‖ ^ 2 := (frob_sq V).symm

/-- The difference of two born solutions with the same births is an Itô process. -/
theorem isNative_distance {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {ξ₁ ξ₂ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {Jb X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (h₁ : IsBornSDESolution μ D0 Naux P D ξ₁ Jb X₁)
    (h₂ : IsBornSDESolution μ D0 Naux P D ξ₂ Jb X₂) :
    IsNativeItoProcess μ (fun t x => X₁ t x - X₂ t x)
      (fun t x => sourceDrift D0 Naux P (X₁ t x) - sourceDrift D0 Naux P (X₂ t x))
      (fun a t x => sourceDiffusion D0 P D a (X₁ t x) - sourceDiffusion D0 P D a (X₂ t x)) := by
  have h := (h₁.1.prod h₂.1).map_clm (ContinuousLinearMap.fst ℝ (Matrix ι c ℂ) (Matrix ι c ℂ) -
    ContinuousLinearMap.snd ℝ (Matrix ι c ℂ) (Matrix ι c ℂ))
  convert h using 1
  · funext t x
    show X₁ t x - X₂ t x = (X₁ t x - Jb t x) - (X₂ t x - Jb t x)
    abel
  · funext t x; rfl
  · funext a t x; rfl

/-- **The stopped trace bound.** -/
theorem lintegral_stopped_trace_le {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {ξ₁ ξ₂ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ₁ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₁)
    (hξ₂ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₂)
    (hξ₁0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₁ x))
    (hξ₂0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₂ x))
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k))
    (hcol : Function.Injective col) (hDcol : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0)
    (hξ₁c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ₁ x i (col k) = 0)
    (hξ₂c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ₂ x i (col k) = 0)
    (hwβ : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∑ i, ‖w k x i‖ ^ 2 = β k)
    {X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX₁ : IsBornSDESolution μ D0 Naux P D ξ₁ (frameBirthJump τ col w) X₁)
    (hX₂ : IsBornSDESolution μ D0 Naux P D ξ₂ (frameBirthJump τ col w) X₂)
    {σ : DriverSample S (SourceNoise ι) → WithTop ℝ≥0}
    (hσ : IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ) σ) (t : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (stoppedProcess (fun t x => traceProc X₁ τ col w β t x +
        traceProc X₂ τ col w β t x) σ t x) ∂driverLaw (κ := SourceNoise ι) μ ≤
      (∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) +
        ENNReal.ofReal (2 * ∑ k, β k) := by
  have hR := ((locMart_traceProc hD0 hP hD hξ₁ hξ₁0 hτ hw hDcol hξ₁c hwβ hX₁).add
    (locMart_traceProc hD0 hP hD hξ₂ hξ₂0 hτ hw hDcol hξ₂c hwβ hX₂)).stop hσ
  have hd₁ := norm_sq_le_traceProc hD0 hP hD hξ₁ hξ₁0 hτ hw hcol hDcol hξ₁c hwβ hX₁
  have hd₂ := norm_sq_le_traceProc hD0 hP hD hξ₂ hξ₂0 hτ hw hcol hDcol hξ₂c hwβ hX₂
  have hnn : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, 0 ≤ stoppedProcess (fun t x =>
      traceProc X₁ τ col w β t x + traceProc X₂ τ col w β t x) σ t x := by
    filter_upwards [hd₁, hd₂] with x h1 h2 t
    rw [stoppedProcess_eq_stopTime]
    nlinarith [h1 (stopTime (σ x) t), h2 (stopTime (σ x) t), sq_nonneg ‖X₁ (stopTime (σ x) t) x‖,
      sq_nonneg ‖X₂ (stopTime (σ x) t) x‖]
  have hb := hR.lintegral_le hnn (ae_of_all _ fun x t => by simp only [switchAfter, add_zero, ite_self, integral_zero, le_refl])
    (hR.prog.stronglyAdapted 0) t
  refine hb.trans ?_
  have h0 : ∀ x, stoppedProcess (fun t x => traceProc X₁ τ col w β t x +
      traceProc X₂ τ col w β t x) σ 0 x = traceProc X₁ τ col w β 0 x +
        traceProc X₂ τ col w β 0 x := fun x => by
    rw [stoppedProcess_eq_stopTime, le_antisymm (stopTime_le _ 0) zero_le]
  simp only [h0]
  calc ∫⁻ x, ENNReal.ofReal (traceProc X₁ τ col w β 0 x + traceProc X₂ τ col w β 0 x)
        ∂driverLaw (κ := SourceNoise ι) μ
      ≤ ∫⁻ x, (ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) + ENNReal.ofReal (2 * ∑ k, β k))
        ∂driverLaw (κ := SourceNoise ι) μ := lintegral_mono_ae ?_
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  filter_upwards [traceProc_zero_le hwβ hX₁, traceProc_zero_le hwβ hX₂] with x h1 h2
  have hβ : 0 ≤ ∑ k, β k := Finset.sum_nonneg fun k _ => beta_nonneg (hwβ k)
  rw [← ENNReal.ofReal_add (by rw [hsSq_eq, hsSq_eq]; positivity) (by positivity), hsSq_eq,
    hsSq_eq]
  exact ENNReal.ofReal_le_ofReal (by linarith)

omit [DecidableEq c] in
/-- The drift of the discounted distance is nonpositive while `‖X₁‖² + ‖X₂‖² ≤ K`. -/
theorem distance_drift_nonpos {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {V₁ V₂ : Matrix ι c ℂ} (h₁ : TwoProjection P D V₁) (h₂ : TwoProjection P D V₂) {K : ℝ}
    (hK : ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2 ≤ K) (s : ℝ) :
    Real.exp (-(D0 * K ^ 2 / 2) * s) * (-(D0 * K ^ 2 / 2) * ‖V₁ - V₂‖ ^ 2 +
      sdeGenerator (fun _ => sourceDrift D0 Naux P V₁ - sourceDrift D0 Naux P V₂)
        (fun a _ => sourceDiffusion D0 P D a V₁ - sourceDiffusion D0 P D a V₂)
        (fun W : Matrix ι c ℂ => ‖W‖ ^ 2) (V₁ - V₂)) ≤ 0 := by
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  have hg := distance_generator_le hD0.le hP hD h₁ h₂
  have hR0 : 0 ≤ ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2 := by positivity
  have hsq : (‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hR0 hK 2
  have : D0 / 2 * (‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) ^ 2 * ‖V₁ - V₂‖ ^ 2 ≤
      D0 * K ^ 2 / 2 * ‖V₁ - V₂‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖V₁ - V₂‖)
    nlinarith
  linarith

/-- **The stopped distance bound.** -/
theorem lintegral_stopped_distance_le {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {ξ₁ ξ₂ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ₁ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₁)
    (hξ₂ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₂)
    (hξ₁0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₁ x))
    (hξ₂0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₂ x))
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ}
    (hDcol : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0)
    (hξ₁c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ₁ x i (col k) = 0)
    (hξ₂c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ₂ x i (col k) = 0)
    {X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX₁ : IsBornSDESolution μ D0 Naux P D ξ₁ (frameBirthJump τ col w) X₁)
    (hX₂ : IsBornSDESolution μ D0 Naux P D ξ₂ (frameBirthJump τ col w) X₂) {K : ℝ}
    {ρ : DriverSample S (SourceNoise ι) → WithTop ℝ≥0}
    (hρ : IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ) ρ)
    (hρK : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖X₁ s x‖ ^ 2 + ‖X₂ s x‖ ^ 2 ≤ K) (t : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (stoppedProcess (fun (t : ℝ≥0) x => Real.exp (-(D0 * K ^ 2 / 2) * t) *
        ‖X₁ t x - X₂ t x‖ ^ 2) ρ t x) ∂driverLaw (κ := SourceNoise ι) μ ≤
      ∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x - ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ := by
  have hTP₁ := twoProjection_born hD0 hP hD hξ₁ hξ₁0 hDcol hξ₁c hX₁
  have hTP₂ := twoProjection_born hD0 hP hD hξ₂ hξ₂0 hDcol hξ₂c hX₂
  have hZ := ((isNative_distance hX₁ hX₂).locMart_disc (contDiff_normSq (k := 2))
    (D0 * K ^ 2 / 2)).stop hρ
  have hnn : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, 0 ≤ stoppedProcess (fun (t : ℝ≥0) x =>
      Real.exp (-(D0 * K ^ 2 / 2) * t) * ‖X₁ t x - X₂ t x‖ ^ 2) ρ t x :=
    ae_of_all _ fun x t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hβ : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t : ℝ≥0,
      ∫ s in Ioc (0 : ℝ) t, switchAfter ρ (fun (s : ℝ≥0) x => Real.exp (-(D0 * K ^ 2 / 2) * s) *
        (-(D0 * K ^ 2 / 2) * ‖X₁ s x - X₂ s x‖ ^ 2 +
          sdeGenerator (fun _ => sourceDrift D0 Naux P (X₁ s x) - sourceDrift D0 Naux P (X₂ s x))
            (fun a _ => sourceDiffusion D0 P D a (X₁ s x) - sourceDiffusion D0 P D a (X₂ s x))
            (fun W : Matrix ι c ℂ => ‖W‖ ^ 2) (X₁ s x - X₂ s x))) s.toNNReal x ≤ 0 := by
    filter_upwards [hTP₁, hTP₂, hρK] with x h1 h2 h3 t
    refine setIntegral_nonpos measurableSet_Ioc fun s hs => ?_
    simp only [switchAfter]
    split_ifs with hle
    · exact distance_drift_nonpos hD0 hP hD (h1 _) (h2 _) (h3 _ (Real.toNNReal_pos.2 hs.1) hle) _
    · exact le_rfl
  refine (hZ.lintegral_le hnn hβ (hZ.prog.stronglyAdapted 0) t).trans
    (lintegral_mono_ae ?_)
  filter_upwards [hX₁.2, hX₂.2] with x h1 h2
  rw [stoppedProcess_eq_stopTime, le_antisymm (stopTime_le _ 0) zero_le, hsSq_eq]
  simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul]
  rw [show X₁ 0 x - X₂ 0 x = ξ₁ x - ξ₂ x by rw [h1, h2]]

end BlockBand.SourceProcess.RankFree
