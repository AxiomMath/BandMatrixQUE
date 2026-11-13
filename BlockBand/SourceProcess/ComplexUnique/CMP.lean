module

public import BlockBand.SourceProcess.ComplexUnique.RealCoord

/-!
# Complex clauses give the real martingale problem

`isMPSolutionOn_of_complex`: if for every relatively compact subdomain `W ⊆ U` the complex
compensated coordinates `cC`, products `cB` and sesquilinear products `cB'` of a real path `Y`,
stopped at the exit from `W`, have martingale modifications, and the time coordinate runs at unit
speed before the exit, then `Y` solves the `(realDrift β, realCov Γ Γ')` martingale problem in
`U` (`IsMPSolutionOn`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

variable {κ : Type*} [Fintype κ] {Ω : Type*} [MeasurableSpace Ω]

theorem realDrift_none (β : (κ → ℂ) → κ → ℂ) (y : Fin (rDim κ) → ℝ) :
    realDrift β y (rEquiv κ none) = 1 := by
  simp [realDrift]

theorem realCov_none_left (Γ Γ' : (κ → ℂ) → κ → κ → ℂ) (y : Fin (rDim κ) → ℝ)
    (j : Fin (rDim κ)) : realCov Γ Γ' y (rEquiv κ none) j = 0 := by
  simp [realCov]

theorem realCov_none_right (Γ Γ' : (κ → ℂ) → κ → κ → ℂ) (y : Fin (rDim κ) → ℝ)
    (i : Fin (rDim κ)) : realCov Γ Γ' y i (rEquiv κ none) = 0 := by
  simp only [realCov]
  rcases ((rEquiv κ).symm i) with _ | q <;> simp

omit [MeasurableSpace Ω] in
theorem mpCompensated_none (β : (κ → ℂ) → κ → ℂ) (Y : ℝ≥0 → Ω → Fin (rDim κ) → ℝ) (t : ℝ≥0)
    (ω : Ω) : mpCompensated (realDrift β) Y (rEquiv κ none) t ω =
      tOf (Y t ω) - tOf (Y 0 ω) - t := by
  simp only [mpCompensated, realDrift_none, tOf]
  rw [setIntegral_const, Real.volume_real_Ioc, sub_zero, smul_eq_mul, mul_one]
  congr 1
  exact max_eq_left t.2

/-- **The real martingale problem from complex clauses.** -/
theorem isMPSolutionOn_of_complex {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {β : (κ → ℂ) → κ → ℂ}
    {Γ Γ' : (κ → ℂ) → κ → κ → ℂ} (hβ : Continuous β) (hΓ : Continuous Γ) (hΓ' : Continuous Γ')
    {U : Set (Fin (rDim κ) → ℝ)} {Y : ℝ≥0 → Ω → Fin (rDim κ) → ℝ}
    (hYa : ∀ t, StronglyMeasurable[𝓗 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    (htime : ∀ W, IsInteriorDomain W U → ∀ᵐ ω ∂Q, ∀ u : ℝ≥0,
      tOf (Y (stopTime (exitTimeFrom W Y ω) u) ω) - tOf (Y 0 ω) = stopTime (exitTimeFrom W Y ω) u)
    (hC : ∀ W, IsInteriorDomain W U → ∀ p, ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓗 Q ∧
      ∀ u, N u =ᵐ[Q] stoppedProcess (cC β Y p) (exitTimeFrom W Y) u)
    (hB : ∀ W, IsInteriorDomain W U → ∀ p q, ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓗 Q ∧
      ∀ u, N u =ᵐ[Q] stoppedProcess (cB β Γ Y p q) (exitTimeFrom W Y) u)
    (hB' : ∀ W, IsInteriorDomain W U → ∀ p q, ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓗 Q ∧
      ∀ u, N u =ᵐ[Q] stoppedProcess (cB' β Γ' Y p q) (exitTimeFrom W Y) u) :
    IsMPSolutionOn Q 𝓗 (realDrift β) (realCov Γ Γ') U Y := by
  have hzero : ∀ W, IsInteriorDomain W U → ∀ᵐ ω ∂Q, ∀ u : ℝ≥0,
      mpCompensated (realDrift β) Y (rEquiv κ none) (stopTime (exitTimeFrom W Y ω) u) ω = 0 :=
    fun W hW => by
      filter_upwards [htime W hW] with ω h u
      rw [mpCompensated_none, h u, sub_self]
  refine ⟨hYa, hYc, fun W hW i => ?_, fun W hW i j => ?_⟩
  · obtain ⟨x, rfl⟩ := (rEquiv κ).surjective i
    rcases x with _ | q
    · refine ⟨0, martingale_zero _ _ _, fun u => ?_⟩
      filter_upwards [hzero W hW] with ω h
      rw [stoppedProcess_eq_stopTime, h u]; rfl
    · obtain ⟨N, hN, hNX⟩ := hC W hW q.1
      refine ⟨fun u ω => reImCLM q.2 (N u ω), martingale_clm hN _, fun u => ?_⟩
      filter_upwards [hNX u, hYc] with ω h hc
      rw [h, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, mpCompensated_some hβ hc,
        reImCLM_apply]
  · obtain ⟨x, rfl⟩ := (rEquiv κ).surjective i
    obtain ⟨x', rfl⟩ := (rEquiv κ).surjective j
    rcases x with _ | q
    · refine ⟨0, martingale_zero _ _ _, fun u => ?_⟩
      filter_upwards [hzero W hW] with ω h
      simp only [stoppedProcess_eq_stopTime, h u, realCov_none_left, integral_zero, zero_mul,
        sub_zero]
      rfl
    rcases x' with _ | q'
    · refine ⟨0, martingale_zero _ _ _, fun u => ?_⟩
      filter_upwards [hzero W hW] with ω h
      simp only [stoppedProcess_eq_stopTime, h u, realCov_none_right, integral_zero, mul_zero,
        sub_zero]
      rfl
    obtain ⟨N, hN, hNX⟩ := hB W hW q.1 q'.1
    obtain ⟨N', hN', hNX'⟩ := hB' W hW q.1 q'.1
    refine ⟨fun u ω => realCovL q.2 q'.2 (N u ω) + realCovL' q.2 q'.2 (N' u ω),
      (martingale_clm hN _).add (martingale_clm hN' _), fun u => ?_⟩
    filter_upwards [hNX u, hNX' u, hYc] with ω h h' hc
    rw [h, h', stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime,
      mpBracket_some hβ hΓ hΓ' hc]

end BlockBand.SourceProcess.ComplexUnique
