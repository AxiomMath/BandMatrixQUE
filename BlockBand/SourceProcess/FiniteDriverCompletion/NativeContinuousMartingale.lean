module
public import BlockBand.SourceProcess.FiniteDriverCompletion.ContinuousNativeGrid
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeEarlierPast
public import Mathlib.Probability.Martingale.Basic

/-!
# Stopped increments are continuous martingales

Each stopped increment `H(W_a(t ∧ u) - W_a(s ∧ u))` with `H` square integrable and measurable at
time `s` is a continuous, adapted, square-integrable martingale under the driver law.
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
namespace GridPresentation

omit [IsProbabilityMeasure μ] in
/-- At or after its left endpoint, the stopped process is a driver step. -/
theorem continuousTerm_eq_driverStep (d : GridPresentation (κ := κ) μ T)
    (k : Fin d.steps) (a : κ) (u : ℝ≥0) (hu : d.grid.time k.castSucc ≤ u) :
    d.continuousTerm k a u = driverStep (d.grid.time k.castSucc)
      (min u (d.grid.time k.succ) - d.grid.time k.castSucc) a (d.coeff k a) := by
  have hl : d.grid.time k.castSucc ≤ min u (d.grid.time k.succ) :=
    le_min hu (d.grid.strictMono_time k.castSucc_lt_succ).le
  funext x
  simp only [continuousTerm, driverStep, driverIncrement, min_eq_right hu,
    add_tsub_cancel_of_le hl]

omit [IsProbabilityMeasure μ] in
/-- Before its left endpoint, the stopped process is identically zero. -/
theorem continuousTerm_eq_zero (d : GridPresentation (κ := κ) μ T)
    (k : Fin d.steps) (a : κ) (u : ℝ≥0) (hu : u ≤ d.grid.time k.castSucc) :
    d.continuousTerm k a u = 0 := by
  have hr : u ≤ d.grid.time k.succ := hu.trans
    (d.grid.strictMono_time k.castSucc_lt_succ).le
  funext x
  simp [continuousTerm, min_eq_left hu, min_eq_left hr]

/-- Stopped terms are square integrable at every time. -/
theorem continuousTerm_memLp (d : GridPresentation (κ := κ) μ T)
    (k : Fin d.steps) (a : κ) (u : ℝ≥0) :
    MemLp (d.continuousTerm k a u) 2 (driverLaw (κ := κ) μ) := by
  by_cases hu : u ≤ d.grid.time k.castSucc
  · rw [d.continuousTerm_eq_zero k a u hu]
    exact MemLp.zero
  · rw [d.continuousTerm_eq_driverStep k a u (lt_of_not_ge hu).le]
    exact driverStep_memLp μ _ _ a (d.adapted k a) (d.coeffL2 k a)

/-- The conditional martingale identity for a stopped term. -/
theorem continuousTerm_condExp (d : GridPresentation (κ := κ) μ T)
    (k : Fin d.steps) (a : κ) (r v : ℝ≥0) (hrv : r ≤ v) :
    (driverLaw (κ := κ) μ)[d.continuousTerm k a v | commonWienerFiltration S κ r]
      =ᵐ[driverLaw (κ := κ) μ] d.continuousTerm k a r := by
  by_cases hvl : v ≤ d.grid.time k.castSucc
  · rw [d.continuousTerm_eq_zero k a v hvl,
      d.continuousTerm_eq_zero k a r (hrv.trans hvl), condExp_zero]
  by_cases hrl : r ≤ d.grid.time k.castSucc
  · rw [d.continuousTerm_eq_zero k a r hrl,
      d.continuousTerm_eq_driverStep k a v (lt_of_not_ge hvl).le]
    exact driverStep_condExp_earlier μ r _ _ hrl a (d.adapted k a) (d.coeffL2 k a)
  have hlr : d.grid.time k.castSucc ≤ r := (lt_of_not_ge hrl).le
  have hcoef : Measurable[commonWienerFiltration S κ r] (d.coeff k a) :=
    (d.adapted k a).mono ((commonWienerFiltration S κ).mono hlr) le_rfl
  have hir := (d.continuousTerm_memLp k a r).integrable (by norm_num)
  have hself := condExp_of_stronglyMeasurable ((commonWienerFiltration S κ).le r)
    (d.continuousTerm_adapted k a r).stronglyMeasurable hir
  by_cases hright : d.grid.time k.succ ≤ r
  · have he : d.continuousTerm k a v = d.continuousTerm k a r := by
      funext x
      simp only [continuousTerm, min_eq_right hright,
        min_eq_right (hright.trans hrv), min_eq_right hlr, min_eq_right (hlr.trans hrv)]
    rw [he, hself]
  have hrh : r ≤ d.grid.time k.succ := (lt_of_not_ge hright).le
  have hrend : r ≤ min v (d.grid.time k.succ) := le_min hrv hrh
  let Y := driverStep r (min v (d.grid.time k.succ) - r) a (d.coeff k a)
  have hYL2 := driverStep_memLp μ r (min v (d.grid.time k.succ) - r)
    a hcoef (d.coeffL2 k a)
  have he : d.continuousTerm k a v = d.continuousTerm k a r + Y := by
    funext x
    simp only [continuousTerm, Y, driverStep, driverIncrement,
      min_eq_right (hlr.trans hrv), min_eq_right hlr, min_eq_left hrh,
      add_tsub_cancel_of_le hrend, Pi.add_apply]
    ring
  rw [he]
  have hz := driverStep_condExp μ r (min v (d.grid.time k.succ) - r)
    a hcoef (d.coeffL2 k a)
  filter_upwards [condExp_add hir (hYL2.integrable (by norm_num))
    (commonWienerFiltration S κ r), hz] with x hx hy
  rw [hx, hself]
  change d.continuousTerm k a r x +
    (driverLaw (κ := κ) μ)[Y | commonWienerFiltration S κ r] x = _
  change (driverLaw (κ := κ) μ)[Y | commonWienerFiltration S κ r] x = 0 at hy
  rw [hy, add_zero]

/-- A stopped term is a continuous adapted martingale under the driver law. -/
theorem continuousTerm_martingale (d : GridPresentation (κ := κ) μ T)
    (k : Fin d.steps) (a : κ) :
    Martingale (d.continuousTerm k a) (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) :=
  ⟨fun r => (d.continuousTerm_adapted k a r).stronglyMeasurable,
    fun r v hrv => d.continuousTerm_condExp k a r v hrv⟩

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
