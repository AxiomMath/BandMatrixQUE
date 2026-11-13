module
public import BlockBand.Diffusion.PathSpace.AdapterDrift
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Restarting the test-function martingale problem at a fixed time

For a fixed time `q`: `shiftFiltration 𝓖 q = (𝓖_{q+r})_r` and `shiftProc Z q = (Z_{q+r})_r`.

**Headline (`IsTestMPSolution.exists_martingale_stopped_shift`).** For a solution of the raw
test-function martingale problem, a test `f` and an open `W`, the compensated test process of
the restarted path, stopped at its exit from `W`,
`f(Z_{q+r∧τ}) - f(Z_q) - ∫_0^{r∧τ} 𝓛f(Z_{q+v}) dv`, has a `shiftFiltration 𝓖 q`-martingale
modification. (The restarted path need not solve the raw problem exactly on the null set of
discontinuous paths; the modification form is what optional stopping needs.)
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.Internal.Contracts.Transmission (shiftFiltration)
open scoped NNReal

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

@[simp] theorem shiftFiltration_apply (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (q r : ℝ≥0) : shiftFiltration 𝓖 q r = 𝓖 (q + r) := rfl

omit [MeasurableSpace Ω] in
/-- The path restarted at `q`. -/
def shiftProc {E : Type*} (Z : ℝ≥0 → Ω → E) (q : ℝ≥0) (r : ℝ≥0) (ω : Ω) : E := Z (q + r) ω

omit [MeasurableSpace Ω] in
@[simp] theorem shiftProc_apply {E : Type*} (Z : ℝ≥0 → Ω → E) (q r : ℝ≥0) (ω : Ω) :
    shiftProc Z q r ω = Z (q + r) ω := rfl

omit [MeasurableSpace Ω] in
theorem continuous_shiftProc {E : Type*} [TopologicalSpace E] {Z : ℝ≥0 → Ω → E} {ω : Ω}
    (hZ : Continuous fun t => Z t ω) (q : ℝ≥0) : Continuous fun r => shiftProc Z q r ω :=
  hZ.comp (continuous_const.add continuous_id)

omit [MeasurableSpace Ω] in
/-- Pathwise identity behind the restart. -/
theorem integral_shift {g : ℝ → ℝ} (hg : Continuous g) (q r : ℝ≥0) :
    (∫ u in Ioc (0 : ℝ) (q + r : ℝ≥0), g u) - ∫ u in Ioc (0 : ℝ) q, g u =
      ∫ u in Ioc (0 : ℝ) r, g ((q + u.toNNReal : ℝ≥0) : ℝ) := by
  rw [← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity),
    ← intervalIntegral.integral_of_le (by positivity)]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) 0 (q : ℝ))
    (hg.intervalIntegrable (μ := volume) (q : ℝ) ((q + r : ℝ≥0) : ℝ))
  have e : ∫ u in (0 : ℝ)..r, g ((q + u.toNNReal : ℝ≥0) : ℝ) = ∫ u in (0 : ℝ)..r, g (u + q) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg r)] at hu
    simp [Real.coe_toNNReal _ hu.1, add_comm]
  have e2 := intervalIntegral.integral_comp_add_right g (q : ℝ) (a := 0) (b := r)
  rw [e, e2, zero_add, ← hadd, NNReal.coe_add, add_comm (r : ℝ)]
  ring

variable {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ}

omit [IsProbabilityMeasure Q] in
theorem martingale_shift {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 Q) (q : ℝ≥0) :
    Martingale (fun r => M (q + r)) (shiftFiltration 𝓖 q) Q :=
  ⟨fun r => hM.1 (q + r), fun i j hij => hM.2 (q + i) (q + j) (add_le_add (le_refl q) hij)⟩

/-- **Restarted optional stopping.** -/
theorem IsTestMPSolution.exists_martingale_stopped_shift (h : IsTestMPSolution Q 𝓖 b a U Z)
    (hU : IsOpen U) (hb : ContinuousOn b U) (ha : ContinuousOn a U) {f : (Fin d → ℝ) → ℝ}
    (hf : IsMPTest U f) {W : Set (Fin d → ℝ)} (hW : IsOpen W) (q : ℝ≥0) :
    ∃ N : ℝ≥0 → Ω → ℝ, Martingale N (shiftFiltration 𝓖 q) Q ∧ ∀ r,
      N r =ᵐ[Q] stoppedProcess (testCompensated f (mpGenerator b a f) (shiftProc Z q))
        (exitTimeFrom W (shiftProc Z q)) r := by
  set g := mpGenerator b a f with hgdef
  have hgc : Continuous g := continuous_mpGenerator hU hb ha hf
  have hM := h.martingale_testCompensated hf
  have hq : StronglyMeasurable[shiftFiltration 𝓖 q ⊥] (testCompensated f g Z q) := by
    have : shiftFiltration 𝓖 q ⊥ = 𝓖 q := by simp
    rw [this]; exact hM.1 q
  have hN₀ : Martingale (fun r ω => testCompensated f g Z (q + r) ω - testCompensated f g Z q ω)
      (shiftFiltration 𝓖 q) Q :=
    (martingale_shift hM q).sub (martingale_const_fun _ Q hq (hM.integrable q))
  have hae : ∀ r, (fun ω => testCompensated f g Z (q + r) ω - testCompensated f g Z q ω) =ᵐ[Q]
      testCompensated f g (shiftProc Z q) r := fun r => by
    filter_upwards [h.continuous] with ω hω
    have key : (∫ u in Ioc (0 : ℝ) ((q + r : ℝ≥0) : ℝ), g (Z u.toNNReal ω)) -
        ∫ u in Ioc (0 : ℝ) (q : ℝ), g (Z u.toNNReal ω) =
          ∫ u in Ioc (0 : ℝ) (r : ℝ), g (Z (q + u.toNNReal) ω) := by
      have hI := integral_shift (g := fun u => g (Z u.toNNReal ω))
        (hgc.comp (hω.comp continuous_real_toNNReal)) q r
      simp only [Real.toNNReal_coe] at hI
      exact hI
    simp only [testCompensated, shiftProc_apply, add_zero]
    linarith [key]
  have hc : ∀ᵐ ω ∂Q, Continuous fun r => testCompensated f g (shiftProc Z q) r ω := by
    filter_upwards [h.continuous] with ω hω
    exact continuous_testCompensated hf.1.continuous hgc (continuous_shiftProc hω q)
  have hρ : IsStoppingTime (shiftFiltration 𝓖 q) (rawHit Wᶜ (shiftProc Z q)) :=
    isStoppingTime_rawHit fun r => h.adapted (q + r)
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hN₀ hae hc hρ
  refine ⟨M', hM', fun r => (hM'X r).trans ?_⟩
  filter_upwards [h.continuous] with ω hω
  simp only [stoppedProcess_eq_stopTime,
    rawHit_compl_eq_exitTimeFrom hW (continuous_shiftProc hω q)]

end BlockBand.Diffusion
