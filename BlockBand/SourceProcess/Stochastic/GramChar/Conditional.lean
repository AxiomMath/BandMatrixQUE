module
public import BlockBand.SourceProcess.Stochastic.GramChar.Bilinear
public import BlockBand.SourceProcess.Stochastic.GramChar.DriftCongr
public import BlockBand.SourceProcess.Stochastic.ItoNative.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram characteristics of a constrained source solution

`gramCharacteristics_of_constraint` takes the constraint as an explicit hypothesis; it is
discharged by the constraint-preservation clause of `FiniteSourceWellPosed`.
Uses `0 ≤ D₀`, `IsNearProjection`, and (for the `MB` bracket) `𝖣ᴴ = 𝖣`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramChar
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.FiniteDriverIntegration

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

/-- A global solution is an Itô process with the (unswitched) source coefficients. -/
theorem IsSDESolution.nativeIto {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X) :
    IsNativeItoProcess μ X (fun t x => sourceDrift D0 Naux P (X t x))
      (fun a t x => sourceDiffusion D0 P D a (X t x)) := by
  have h := hX.1
  have e1 : switchOff (S := S) (κ := SourceNoise ι) (fun _ => ⊤)
      (fun t x => sourceDrift D0 Naux P (X t x)) = fun t x => sourceDrift D0 Naux P (X t x) := by
    funext t x
    exact ite_eq_left le_top
  have e2 : (fun a => switchOff (S := S) (κ := SourceNoise ι) (fun _ => ⊤)
      (fun t x => sourceDiffusion D0 P D a (X t x))) =
      fun a t x => sourceDiffusion D0 P D a (X t x) := by
    funext a t x
    exact ite_eq_left le_top
  rw [e1, e2] at h
  exact h

/-- **Product rule for the Gram pair (every frame).** -/
theorem gramPair_nativeIto {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X) :
    IsNativeItoProcess μ (fun t x => gramPair P (X t x))
      (fun t x => gramDrift D0 Naux P D (X t x))
      (fun a t x => gramNoise D0 P D a (X t x)) := by
  have hX1 := IsSDESolution.nativeIto μ hX
  have h := ItoNative.itoProductRuleFor_holds (κ := SourceNoise ι) μ (E := Matrix ι c ℂ)
    (F := Matrix ι c ℂ) (G := Matrix c c ℂ × Matrix c c ℂ) _ _ _ _ _ _ hX1 hX1 (gramPairBil P)
  have hd : (fun (t : ℝ≥0) (x : DriverSample S (SourceNoise ι)) =>
      gramDrift D0 Naux P D (X t x)) = fun t x =>
      gramPairBil P (sourceDrift D0 Naux P (X t x)) (X t x) +
        gramPairBil P (X t x) (sourceDrift D0 Naux P (X t x)) +
        ∑ a, gramPairBil P (sourceDiffusion D0 P D a (X t x))
          (sourceDiffusion D0 P D a (X t x)) := by
    funext t x
    exact (gramPairBil_drift D0 Naux P D (X t x)).symm
  rw [hd]
  exact h

/-- **Gram characteristics, conditional on the constraint.** Under `0 ≤ D₀`,
`IsNearProjection P Naux`, `𝖣ᴴ = 𝖣`, for every global solution `X` of the finite source equation
satisfying the two-projection
constraint at all times a.s., the Gram pair is an Itô process with drift
`(0, -(D₀/2) g B)` and diffusion `gramNoise`, whose complex bilinear brackets are the
`crossedBracket` formulas of the Gram covariance at all times a.s. -/
theorem gramCharacteristics_of_constraint {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ}
    {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X)
    (hconstr : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, TwoProjection P D (X t x)) :
    IsNativeItoProcess μ (fun t x => gramPair P (X t x))
        (fun t x => (0, (-(((D0 / 2 : ℝ) : ℂ) * gramScalar D (sourceGram (X t x)))) •
          nearGram P (X t x))) (fun a t x => gramNoise D0 P D a (X t x)) ∧
      ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, ∀ i j k l : c,
        let M := sourceGram (X t x)
        let B := nearGram P (X t x)
        (∑ a, (gramNoise D0 P D a (X t x)).1 i j * (gramNoise D0 P D a (X t x)).1 k l =
            crossedBracket D0 B (gramC0 M B D) (gramC0 M B D) i j k l) ∧
        (∑ a, (gramNoise D0 P D a (X t x)).1 i j * (gramNoise D0 P D a (X t x)).2 k l =
            crossedBracket D0 B (gramC1 M B D)ᴴ (gramC1 M B D) i j k l) ∧
        (∑ a, (gramNoise D0 P D a (X t x)).2 i j * (gramNoise D0 P D a (X t x)).2 k l =
            crossedBracket D0 B (gramC2 B D) (gramC2 B D) i j k l) := by
  have hG := gramPair_nativeIto μ hX
  have hprog : IsStronglyProgressive (driverAugmented (κ := SourceNoise ι) μ)
      (fun t x => gramTargetDrift D0 P D (X t x)) := fun t =>
    (continuous_gramTargetDrift D0 P D).comp_stronglyMeasurable
      ((IsSDESolution.nativeIto μ hX).progressive t)
  refine ⟨hG.congr_drift hprog ?_, ?_⟩
  · filter_upwards [hconstr] with x hx t
    exact gramDrift_eq hD0 hP (hx t)
  · filter_upwards [hconstr] with x hx t i j k l
    exact ⟨gram_bracket_MM hD0 hP (hx t) i j k l, gram_bracket_MB hD0 hP hD (hx t) i j k l,
      gram_bracket_BB hD0 hP (hx t) i j k l⟩

end BlockBand.SourceProcess.Stochastic.GramChar
