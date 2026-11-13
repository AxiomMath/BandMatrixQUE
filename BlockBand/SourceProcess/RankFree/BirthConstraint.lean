module

public import BlockBand.SourceProcess.RankFree.BirthProcess
public import BlockBand.SourceProcess.Stochastic.ItoNative.CoordRepBuild

/-!
# Born frames keep the two-projection constraint

`twoProjection_born`: for a born solution `X` of the finite-source SDE whose births sit in
zero-signature columns that vanish in `ξ`, almost surely `TwoProjection P 𝖣 (X_t)` for all `t`.
Proof: `X𝚷 = (X - J_b)𝚷` (`𝚷` = `nonBirthProj`) solves the finite-source SDE from `ξ𝚷 = ξ` (the
coefficients act column by column and `P'(X𝚷) = P'(X)`), so the constraint for SDE solutions
(`isSDESolution_twoProjection`) applies, and the constraint only depends on `P'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {nb : ℕ}

omit [DecidableEq ι] in
theorem twoProjection_mul_nonBirthProj {col : Fin nb → c} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    (hDcol : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0) (V : Matrix ι c ℂ) :
    TwoProjection P D (V * nonBirthProj col) ↔ TwoProjection P D V := by
  unfold TwoProjection
  rw [gramProjection_mul_nonBirthProj hDcol]

/-- **The constraint along born solutions.** -/
theorem twoProjection_born {D0 : ℝ} (hD0 : 0 < D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hξ : StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ)
    (hξ0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x))
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ}
    (hDcol : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0)
    (hξcol : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i, ξ x i (col k) = 0)
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsBornSDESolution μ D0 Naux P D ξ (frameBirthJump τ col w) X) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, TwoProjection P D (X t x) := by
  set Pi0 := nonBirthProj col
  have h1 := hX.1.map_clm ((mulBil (l := ι) (m := c) (n := c)).flip Pi0)
  have hJ : ∀ t x, frameBirthJump τ col w t x * Pi0 = 0 := fun t x =>
    frameBirthJump_mul_nonBirthProj τ w t x
  simp only [ContinuousLinearMap.flip_apply, mulBil_apply, Matrix.sub_mul, hJ, sub_zero,
    sourceDrift_mul, sourceDiffusion_mul] at h1
  have hdiff : ∀ (a : SourceNoise ι) (V : Matrix ι c ℂ),
      SourceAlgebra.sourceWeight D0 a.2 • (gramProjection P V D * SourceAlgebra.sourceUnit a *
        (P * V * Pi0)) = sourceDiffusion D0 P D a (V * Pi0) := fun a V => by
    rw [sourceDiffusion_eq', gramProjection_mul_nonBirthProj hDcol]
    simp only [Matrix.mul_assoc]
  simp only [hdiff] at h1
  have hY : IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ
      (fun t x => X t x * Pi0) := by
    have hsw : ∀ f : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
        switchOff (fun _ => (⊤ : WithTop ℝ≥0)) f = f := fun f => by
      funext t x; exact ite_eq_left_of_eq_true _ _ (eq_true le_top)
    refine ⟨?_, ?_⟩
    · simp only [hsw]
      exact h1
    · filter_upwards [hX.2, hξcol] with x h0 hc
      rw [h0]
      exact mul_nonBirthProj_of_col fun k i => hc k i
  filter_upwards [isSDESolution_twoProjection μ hD0.le hP hD.1 hξ hξ0 hY] with x hx t
  exact (twoProjection_mul_nonBirthProj hDcol _).1 (hx t)

end BlockBand.SourceProcess.RankFree
