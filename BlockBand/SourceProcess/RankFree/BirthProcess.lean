module

public import BlockBand.SourceProcess.RankFree.BirthAlgebra
public import BlockBand.SourceProcess.RankFree.NativeBridge
public import BlockBand.SourceProcess.RankFree.LocMartShift
public import BlockBand.SourceProcess.Stochastic.SourceSDE.Main

/-!
# Born frames as Itô processes

* `posW`: the birth vector switched off at time-zero births (a birth at `τ_k = 0` is cancelled by
  `X₀ = ξ`, whose birth columns vanish); `sharpFrame X = X - J⁺` with the positive-time births
  `J⁺`. `sharpFrame` is `X - J_b` plus the `𝓕₀`-measurable constant `J_b(0)`, hence a native
  Itô process with the coefficients of `X` (`isNative_sharpFrame`), started at `ξ`.
* `twoProjection_born` (proved in a sibling module from these): `X_t` satisfies the two-projection constraint at all times a.s.
  (`X𝚷` solves the finite-source SDE, since `P'` does not see zero-signature columns; then
  `isSDESolution_twoProjection`).
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

/-- `birthMat j` as a continuous real-linear map. -/
def birthCLM (j : c) : (ι → ℂ) →L[ℝ] Matrix ι c ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := birthMat j
      map_add' := fun u v => by
        ext i l
        simp only [birthMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun r v => by
        ext i l
        simp only [birthMat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

omit [DecidableEq ι] [Fintype c] in
theorem birthCLM_apply (j : c) (v : ι → ℂ) : birthCLM j v = birthMat j v := rfl

variable {Ω : Type*} {nb : ℕ}

/-- Birth vectors switched off at time-zero births. -/
def posW (τ : Fin nb → Ω → ℝ≥0) (w : Fin nb → Ω → ι → ℂ) (k : Fin nb) (x : Ω) : ι → ℂ :=
  if 0 < τ k x then w k x else 0

/-- The frame without its positive-time births. -/
def sharpFrame (X : ℝ≥0 → Ω → Matrix ι c ℂ) (τ : Fin nb → Ω → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → Ω → ι → ℂ) : ℝ≥0 → Ω → Matrix ι c ℂ :=
  fun t x => X t x - frameBirthJump τ col (posW τ w) t x

omit [Fintype ι] [DecidableEq ι] [Fintype c] in
theorem frameBirthJump_sub_pos (τ : Fin nb → Ω → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → Ω → ι → ℂ) (t : ℝ≥0) (x : Ω) :
    frameBirthJump τ col w t x - frameBirthJump τ col (posW τ w) t x =
      frameBirthJump τ col w 0 x := by
  rw [frameBirthJump_eq, frameBirthJump_eq, frameBirthJump_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [posW]
  rcases eq_zero_or_pos (τ k x) with h | h
  · simp [h, birthMat_zero]
  · simp [h, not_le.2 h]

omit [Fintype ι] [DecidableEq ι] [Fintype c] in
theorem sharpFrame_eq (X : ℝ≥0 → Ω → Matrix ι c ℂ) (τ : Fin nb → Ω → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → Ω → ι → ℂ) :
    sharpFrame X τ col w =
      fun t x => (X t x - frameBirthJump τ col w t x) + frameBirthJump τ col w 0 x := by
  funext t x
  rw [sharpFrame, ← frameBirthJump_sub_pos τ col w t x]
  abel

omit [Fintype ι] [DecidableEq ι] [Fintype c] in
theorem X_eq_sharpFrame_add (X : ℝ≥0 → Ω → Matrix ι c ℂ) (τ : Fin nb → Ω → ℝ≥0)
    (col : Fin nb → c) (w : Fin nb → Ω → ι → ℂ) (t : ℝ≥0) (x : Ω) :
    X t x = sharpFrame X τ col w t x +
      ∑ k, if τ k x ≤ t then birthMat (col k) (posW τ w k x) else 0 := by
  rw [sharpFrame, ← frameBirthJump_eq]
  abel

omit [Fintype ι] [DecidableEq ι] [Fintype c] in
theorem frameBirthJump_pos_zero (τ : Fin nb → Ω → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → Ω → ι → ℂ) (x : Ω) : frameBirthJump τ col (posW τ w) 0 x = 0 := by
  rw [frameBirthJump_eq]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [posW]
  rcases eq_zero_or_pos (τ k x) with h | h
  · simp [h, birthMat_zero]
  · simp [not_le.2 h]

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

omit [DecidableEq ι] [Fintype c] [IsProbabilityMeasure μ] in
/-- Time-zero births are `𝓕₀`-measurable. -/
theorem stronglyMeasurable_frameBirthJump_zero (τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0)
    (col : Fin nb → c) (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ)
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k)) :
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0]
      (frameBirthJump τ col w 0) := by
  have e : frameBirthJump τ col w 0 = fun x => ∑ k, (fun x =>
      if ((τ k x : ℝ≥0) : WithTop ℝ≥0) ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) then
        birthCLM (col k) (w k x) else 0) x := by
    funext x
    simp only [frameBirthJump_eq, WithTop.coe_le_coe, birthCLM_apply]
  rw [e]
  exact Finset.stronglyMeasurable_fun_sum _ fun k _ =>
    stronglyMeasurable_ite_le (hτ k) ((birthCLM (col k)).continuous.comp_stronglyMeasurable (hw k)) 0

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
/-- The positive-time birth vectors are `𝓕_τ`-measurable. -/
theorem stronglyMeasurable_posW (τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0)
    (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ)
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k)) (k : Fin nb) :
    StronglyMeasurable[(hτ k).measurableSpace] (posW τ w k) := by
  have hset : MeasurableSet[(hτ k).measurableSpace] {x | 0 < τ k x} := by
    have := (hτ k).measurableSet_gt' 0
    simpa only [WithTop.coe_lt_coe] using this
  exact StronglyMeasurable.ite hset (hw k) stronglyMeasurable_const

/-- **The frame without positive-time births is an Itô process.** -/
theorem isNative_sharpFrame {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ}
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)))
    (hw : ∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k))
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    (hX : IsBornSDESolution μ D0 Naux P D ξ (frameBirthJump τ col w) X) :
    IsNativeItoProcess μ (sharpFrame X τ col w) (fun t x => sourceDrift D0 Naux P (X t x))
      (fun a t x => sourceDiffusion D0 P D a (X t x)) := by
  rw [sharpFrame_eq]
  exact hX.1.add_const (stronglyMeasurable_frameBirthJump_zero τ col w hτ hw)

omit [IsProbabilityMeasure μ] in
theorem sharpFrame_zero {D0 : ℝ} {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ}
    {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → c}
    {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ}
    {X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ} [IsProbabilityMeasure μ]
    (hX : IsBornSDESolution μ D0 Naux P D ξ (frameBirthJump τ col w) X) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, sharpFrame X τ col w 0 x = ξ x := by
  filter_upwards [hX.2] with x hx
  rw [sharpFrame, frameBirthJump_pos_zero, sub_zero, hx]

end BlockBand.SourceProcess.RankFree
