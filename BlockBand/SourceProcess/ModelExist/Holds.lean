module

public import BlockBand.SourceProcess.ModelExist.Main

/-!
# Probes born at time zero

`ae_birth_zero`: under the birth-time law of the finite source model, a probe born at model time
`0` has birth value `v = 0` almost surely.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal

/-- A probe born at model time `0` has `v = 0`, almost surely. -/
theorem ae_birth_zero {p M : ℕ} {s T b : ℝ} {q : Fin p → ℝ → ℝ} (hq : ∀ i, IsSourceTest s T (q i))
    {κ : Type*} [Fintype κ] (ρ : Measure (ℕ → ℝ)) [IsProbabilityMeasure ρ]
    [∀ i : Fin p × Fin M, IsProbabilityMeasure (birthTimeLaw s T (q i.1))] :
    ∀ᵐ x ∂driverLaw (κ := κ) (ρ.prod (Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1))),
      ∀ i : Fin p × Fin M, ((x : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ).1.2 i -
        s).toNNReal = 0 → dStar b * sourceMass s T (q i.1) / M = 0 := by
  refine ae_all_iff.2 fun i => ?_
  by_cases hm : 0 < sourceMass s T (q i.1)
  · have hmap : (driverLaw (κ := κ) (ρ.prod (Measure.pi fun i : Fin p × Fin M =>
        birthTimeLaw s T (q i.1)))).map
        (fun x : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ => x.1.2 i) =
        birthTimeLaw s T (q i.1) := by
      have e : (fun x : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ => x.1.2 i) =
          Function.eval i ∘ fun x : DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ => x.1.2 :=
        rfl
      rw [e, ← Measure.map_map (measurable_pi_apply i) measurable_τ', map_τ]
      exact (measurePreserving_eval _ i).map_eq
    have h1 : ∀ᵐ y ∂birthTimeLaw s T (q i.1), s < y := by
      rw [ae_iff]
      convert birthTimeLaw_Iic hm using 2
      ext y; simp
    rw [← hmap] at h1
    filter_upwards [ae_of_ae_map ((measurable_pi_apply i).comp measurable_τ').aemeasurable h1]
      with x hx h0
    have hx' : s < x.1.2 i := hx
    exact absurd (Real.toNNReal_eq_zero.1 h0) (by linarith)
  · have : sourceMass s T (q i.1) = 0 := le_antisymm (not_lt.1 hm) (sourceMass_nonneg (hq i.1))
    exact ae_of_all _ fun x _ => by rw [this]; simp

end BlockBand.SourceProcess.ModelExist
