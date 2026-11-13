module

public import BlockBand.SourceProcess.ComplexCoupled.ClauseK
public import BlockBand.SourceProcess.ModelExist.TransMain
public import BlockBand.SourceProcess.ComplexConstruct.KBracket
public import BlockBand.SourceProcess.BornUnique.Reduce

/-!
# The born `𝒦` process is a complex source extension

`complexExt_born`: for a constrained ambient solution `Y`, its ambient `𝒦` integral `𝒴`, born
coordinates `θ, λ` with `L 𝖣 Lᴴ = 𝖣'` and a born frame `X = Y L`, the born `𝒦` process built from
`𝒴` is a complex source extension of the born Gram process.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal ComplexConjugate
open BlockBand.SourceProcess BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.ModelExist BlockBand.SourceProcess.ComplexUnique
open BlockBand.SourceProcess.ComplexConstruct BlockBand.SourceProcess.BornUnique
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ι c' π : Type*} [Fintype ι] [DecidableEq ι] [Fintype c'] [DecidableEq c'] [Fintype π]
  [DecidableEq π] {K : ℕ}

omit [MeasurableSpace S] [Fintype ι] [DecidableEq ι] [Fintype π] [DecidableEq π] in
theorem kComp_eq (JK : ℝ≥0 → Matrix π π ℂ)
    (Yk : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix (SrcCol K π) (SrcCol K π) ℂ) (i j : π)
    (t : ℝ≥0) (x : DriverSample S (SourceNoise ι)) :
    kCompensated (fun t x => JK t + probeBlock (Yk t x - Yk 0 x)) (fun t _ => JK t) i j t x =
      Yk t x (Sum.inr i) (Sum.inr j) - Yk 0 x (Sum.inr i) (Sum.inr j) := by
  simp [kCompensated, probeBlock]

omit [DecidableEq c'] in
/-- **The born `𝒦` process is a complex source extension.** -/
theorem complexExt_born {b E : ℝ} (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) {Naux : ℕ}
    {P : Matrix ι ι ℂ} (hP : IsNearProjection P Naux) {D' : Matrix c' c' ℂ} (hD' : IsSignature D')
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c' ℂ}
    (hξm : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D' (ξ x))
    {Y : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c' ℂ}
    (hY : IsSDESolution μ (sourceDrift (transportD0 b E) Naux P)
      (sourceDiffusion (transportD0 b E) P D') ξ Y)
    {𝒴 : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c' c' ℂ}
    (h𝒴 : IsNativeItoProcess μ 𝒴 (fun _ _ => 0)
      (fun a t x => kNoise (transportD0 b E) (etaZ b E) P D' a (Y t x)))
    {θ : SrcCol K π → DriverSample S (SourceNoise ι) → ℝ≥0}
    {lam : SrcCol K π → DriverSample S (SourceNoise ι) → c' → ℂ}
    (hθ : ∀ y, Measurable[driverAugmented (κ := SourceNoise ι) μ 0] (θ y))
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    (hsig : ∀ t ω, bornL θ lam t ω * srcSignature K π * (bornL θ lam t ω)ᴴ = D')
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K π) ℂ}
    (hXp : IsStronglyProgressive (driverAugmented (κ := SourceNoise ι) μ) X)
    (hX : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, X t x = Y t x * bornL θ lam t x)
    {Fb : Type*} [Fintype Fb] {j : Fb → GramState (SrcCol K π)}
    {β : Fb → DriverSample S (SourceNoise ι) → ℝ} (hj : ∀ f, 0 ≤ ((j f).1.trace).re)
    (hβ : ∀ f, Measurable[driverAugmented (κ := SourceNoise ι) μ 0] (β f))
    (hG : IsBornGramSolution (driverLaw (κ := SourceNoise ι) μ)
      (driverAugmented (κ := SourceNoise ι) μ) (transportD0 b E) (srcSignature K π) (bJ j β)
      (fun t x => gramPair P (X t x)))
    (hrep : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ e t,
      bornCompensated (transportD0 b E) (srcSignature K π) (fun t x => gramPair P (X t x))
        (bJ j β) e t x =
      bornRep θ lam (gramCompensated (transportD0 b E) D' (fun t x => gramPair P (Y t x))) e t x)
    (JK : ℝ≥0 → Matrix π π ℂ) :
    IsComplexSourceExtension (driverLaw (κ := SourceNoise ι) μ)
      (driverAugmented (κ := SourceNoise ι) μ) b E (srcSignature K π) (bJ j β)
      (fun t x => gramPair P (X t x)) (fun t _ => JK t)
      (fun t x => JK t + probeBlock (kBorn θ lam 𝒴 t x - kBorn θ lam 𝒴 0 x)) := by
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hK := isNativeItoProcess_kBorn h𝒴 hθ hlam hsig hXp hX
  have hgN := fun e => isNativeItoProcess_bornGram hD0.le hP hD' hξm hξc hY hθ hlam hsig hXp hX e
  have hcon := SourceSDE.isSDESolution_twoProjection μ hD0.le hP hD'.1 hξm hξc hY
  have hTP : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t,
      TwoProjection P (srcSignature K π) (X t x) := by
    filter_upwards [hcon, hX] with x h1 h2 t
    rw [h2 t]; unfold TwoProjection; rw [gramProjection_mul P (Y t x) _ (hsig t x)]; exact h1 t
  have hPH := hP.1
  have hPP := hP.2.1
  have hDh := (isSignature_srcSignature K π).1
  have hstop : ∀ L : ℝ, ∃ ρ, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ) ρ ∧
      (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
        ρ x = gramTraceStop (fun t x => gramPair P (X t x)) L x) ∧
      ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < ρ x →
        ((X s x)ᴴ * X s x).trace.re ≤ L := by
    intro L
    obtain ⟨ρ, hρ, hρσ⟩ := exists_stop_ae_eq_traceStop hG.adapted hj hβ hG.continuous L
    refine ⟨ρ, hρ, hρσ, ?_⟩
    filter_upwards [hρσ] with x hx s hs
    rw [hx] at hs
    exact (re_trace_lt_of_lt_pathStop (G := fun t => gramPair P (X t x)) hs).le
  refine ⟨fun t => ?_, fun t => stronglyMeasurable_const, ?_, fun L i k => ?_,
    fun L i k i' k' => ?_, fun L i k i' k' => ?_, fun L i k y z => ?_, fun L i k y z => ?_⟩
  · have hpb : Continuous fun A : Matrix (SrcCol K π) (SrcCol K π) ℂ => probeBlock A :=
      continuous_matrix fun i k => (eCLM (Sum.inr i) (Sum.inr k)).continuous
    exact stronglyMeasurable_const.add (hpb.comp_stronglyMeasurable ((hK.adapted t).sub
      ((hK.adapted 0).mono ((driverAugmented (κ := SourceNoise ι) μ).mono zero_le))))
  · filter_upwards [hK.continuous] with x hx
    have e : (fun t => JK t + probeBlock (kBorn θ lam 𝒴 t x - kBorn θ lam 𝒴 0 x) - JK t) =
        fun t => probeBlock (kBorn θ lam 𝒴 t x - kBorn θ lam 𝒴 0 x) := by
      funext t; abel
    rw [e]
    exact continuous_matrix fun i k =>
      ((eCLM (Sum.inr i) (Sum.inr k)).continuous.comp (hx.sub continuous_const))
  · obtain ⟨ρ, hρ, hρσ, hL⟩ := hstop L
    exact kclause_lin hK hρ hρσ hL (Sum.inr i) (Sum.inr k)
      (ae_of_all _ fun x t => kComp_eq JK _ i k t x)
  · obtain ⟨ρ, hρ, hρσ, hL⟩ := hstop L
    refine kclause_mul hK hρ hρσ hL (Sum.inr i) (Sum.inr k) (Sum.inr i') (Sum.inr k') ?_
    filter_upwards [hTP] with x hx t
    rw [kComp_eq, kComp_eq]
    have h0 : (fun s : ℝ => ∑ a, kNoise (transportD0 b E) (etaZ b E) P (srcSignature K π) a
        (X s.toNNReal x) (Sum.inr i) (Sum.inr k) * kNoise (transportD0 b E) (etaZ b E) P
          (srcSignature K π) a (X s.toNNReal x) (Sum.inr i') (Sum.inr k')) = fun _ => 0 :=
      funext fun s => (kNoise_brackets hD0.le (etaZ b E) hPH hPP hDh (hx _) _ _ _ _).1
    rw [h0, integral_zero, sub_zero]
  · obtain ⟨ρ, hρ, hρσ, hL⟩ := hstop L
    refine kclause_star hK hρ hρσ hL (Sum.inr i) (Sum.inr k) (Sum.inr i') (Sum.inr k') ?_
    filter_upwards [hTP] with x hx t
    rw [kComp_eq, kComp_eq, map_sub]
    have h0 := funext fun s : ℝ =>
      (kNoise_brackets hD0.le (etaZ b E) hPH hPP hDh (hx s.toNNReal) (Sum.inr i) (Sum.inr k)
        (Sum.inr i') (Sum.inr k')).2.1
    simp only [Complex.star_def] at h0 ⊢
    rw [h0]
  · obtain ⟨ρ, hρ, hρσ, hL⟩ := hstop L
    refine gclause_mul hK hρ hρσ hL (0, y, z) (hgN (0, y, z)) (Sum.inr i) (Sum.inr k) ?_
    filter_upwards [hTP, hrep] with x hx hr t
    rw [kComp_eq, hr, bornRep_zero, sub_zero]
    have h0 := funext fun s : ℝ =>
      (kNoise_brackets hD0.le (etaZ b E) hPH hPP hDh (hx s.toNNReal) (Sum.inr i) (Sum.inr k)
        y z).2.2.1
    rw [h0]
  · obtain ⟨ρ, hρ, hρσ, hL⟩ := hstop L
    refine gclause_mul hK hρ hρσ hL (1, y, z) (hgN (1, y, z)) (Sum.inr i) (Sum.inr k) ?_
    filter_upwards [hTP, hrep] with x hx hr t
    rw [kComp_eq, hr, bornRep_zero, sub_zero]
    have h0 := funext fun s : ℝ =>
      (kNoise_brackets hD0.le (etaZ b E) hPH hPP hDh (hx s.toNNReal) (Sum.inr i) (Sum.inr k)
        y z).2.2.2
    rw [h0]

end BlockBand.SourceProcess.ComplexCoupled
