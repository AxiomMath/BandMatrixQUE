module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeContinuousMartingale

/-!
# Continuous grid sums are martingales

Every continuous grid sum is an adapted continuous martingale, square integrable at every time,
whose value at the horizon is the finite stochastic sum.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

omit [IsProbabilityMeasure μ] in
private theorem finite_native_martingale {ι : Type*} (s : Finset ι)
    (f : ι → ℝ≥0 → DriverSample S κ → ℝ)
    (hf : ∀ i ∈ s, Martingale (f i) (commonWienerFiltration S κ) (driverLaw (κ := κ) μ)) :
    Martingale (∑ i ∈ s, f i) (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (martingale_zero ℝ (commonWienerFiltration S κ) (driverLaw (κ := κ) μ))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

namespace GridPresentation

/-- Every continuous grid sum is an adapted martingale. -/
theorem continuousIntegral_martingale (d : GridPresentation (κ := κ) μ T) :
    Martingale d.continuousIntegral (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) := by
  have he : (∑ k : Fin d.steps, ∑ a : κ, d.continuousTerm k a) = d.continuousIntegral := by
    funext u x
    simp only [Finset.sum_apply, continuousIntegral]
  rw [← he]
  exact finite_native_martingale Finset.univ _ (fun k _ =>
    finite_native_martingale Finset.univ _ (fun a _ => d.continuousTerm_martingale k a))

/-- Every continuous grid sum is square integrable at every time. -/
theorem continuousIntegral_memLp (d : GridPresentation (κ := κ) μ T) (u : ℝ≥0) :
    MemLp (d.continuousIntegral u) 2 (driverLaw (κ := κ) μ) := by
  exact memLp_finsetSum _ (fun k _ => memLp_finsetSum _
    (fun a _ => d.continuousTerm_memLp k a u))

omit [IsProbabilityMeasure μ] in
/-- At the horizon, the continuous grid sum is the finite stochastic sum. -/
theorem continuousIntegral_terminal (d : GridPresentation (κ := κ) μ T) :
    d.continuousIntegral T = d.integral := by
  funext x
  unfold continuousIntegral integral
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  have hr : d.grid.time k.succ ≤ T := by
    calc d.grid.time k.succ ≤ d.grid.time (Fin.last d.steps) :=
           d.grid.strictMono_time.monotone (Fin.le_last _)
         _ = T := d.terminal_time
  have hl : d.grid.time k.castSucc ≤ T :=
    (d.grid.strictMono_time k.castSucc_lt_succ).le.trans hr
  rw [d.term_apply]
  simp only [continuousTerm, min_eq_right hr, min_eq_right hl]

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
