module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativePredictableCompletion

/-!
# Grid presentations of predictable rectangles

Every bounded-horizon rectangle `(s,t] × H` in one noise direction, with `H` square integrable and
measurable at time `s`, has a finite grid presentation whose coefficients vanish in the other
directions.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open FiniteIto ContinuousItoCommonRefinement PredictableRectangle

/-- The time grid with the two endpoints `s < t`. -/
def twoPointGrid (s t : ℝ≥0) (hst : s < t) : TimeGrid 1 where
  time i := if i = 0 then s else t
  strictMono_time := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- A masked consecutive block of fine predictable rectangles is the large rectangle. -/
theorem masked_rectangle_sum {Ω : Type*} {n : ℕ} (π : TimeGrid n)
    (i j : Fin (n + 1)) (hij : i ≤ j) (H : Ω → ℝ) (x : ℝ × Ω) :
    (∑ k : Fin n, coefficientRectangle (π.time k.castSucc) (π.time k.succ)
      (if i ≤ k.castSucc ∧ k.succ ≤ j then H else 0) x) =
      coefficientRectangle (π.time i) (π.time j) H x := by
  classical
  let p : Fin n → Prop := fun k => i ≤ k.castSucc ∧ k.succ ≤ j
  let R : Fin n → ℝ := fun k => coefficientRectangle (π.time k.castSucc) (π.time k.succ) H x
  have hsum : (∑ k : Fin n, coefficientRectangle (π.time k.castSucc) (π.time k.succ)
      (if p k then H else 0) x) = ∑ k : {k : Fin n // p k}, R k := by
    calc
      _ = ∑ k : Fin n, if p k then R k else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : p k <;> simp [hk, R, coefficientRectangle]
      _ = ∑ k ∈ Finset.univ.filter p, R k := (Finset.sum_filter p R).symm
      _ = _ := Finset.sum_subtype _ (by simp) R
  rw [hsum]
  let F : Fin (n + 1) → ℝ := fun k => if x.1 ≤ (π.time k : ℝ) then 1 else 0
  calc
    _ = ∑ k : {k : Fin n // p k}, H x.2 * (F k.val.succ - F k.val.castSucc) := by
      apply Finset.sum_congr rfl
      intro k _
      exact coefficientRectangle_eq_mul_endpointDifference _ _
        (π.strictMono_time k.val.castSucc_lt_succ).le H x
    _ = H x.2 * ∑ k : {k : Fin n // p k}, (F k.val.succ - F k.val.castSucc) := by
      rw [Finset.mul_sum]
    _ = H x.2 * (F j - F i) := by rw [sum_differences_between F i j hij]
    _ = _ := (coefficientRectangle_eq_mul_endpointDifference _ _
      (π.strictMono_time.monotone hij) H x).symm

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)
variable [DecidableEq κ]

omit [IsProbabilityMeasure μ] in
/-- Every bounded-horizon rectangle with a square-integrable past-measurable coefficient has a grid
presentation, with zero coefficients in the other noise directions. -/
theorem exists_rectangle_presentation (s t : ℝ≥0) (hst : s < t) (htT : t ≤ T) (a : κ)
    (H : DriverSample S κ → ℝ)
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    ∃ d : GridPresentation (κ := κ) μ T, ∀ b x,
      d.predictableFunction b x = if b = a then coefficientRectangle s t H x else 0 := by
  classical
  have hT : 0 < T := (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hst).trans_le htT
  let base := twoPointGrid 0 T hT
  let middle := twoPointGrid s t hst
  let π := commonTimeGrid base middle
  let i := rightEndpointIndex base middle (0 : Fin 2)
  let j := rightEndpointIndex base middle (Fin.last 1)
  have hi : π.time i = s := by
    simp [π, i, commonTimeGrid_rightEndpointIndex, middle, twoPointGrid]
  have hj : π.time j = t := by
    simp [π, j, commonTimeGrid_rightEndpointIndex, middle, twoPointGrid]
  have hij : i ≤ j := (rightEndpointIndex_strictMono base middle).monotone (Fin.zero_le _)
  have hzero : π.time 0 = 0 := by
    apply le_antisymm
    · calc π.time 0 ≤ π.time (leftEndpointIndex base middle 0) :=
             π.strictMono_time.monotone (Fin.zero_le _)
           _ = 0 := by simp [π, commonTimeGrid_leftEndpointIndex, base, twoPointGrid]
    · exact zero_le
  have hupper (k : Fin (commonStepCount base middle + 1)) : π.time k ≤ T := by
    have hm := (commonEndpointOrderIso base middle k).property
    change π.time k ∈ commonEndpointSet base middle at hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_image.mp hm with ⟨l, _, hl⟩
      rw [← hl]
      fin_cases l <;> simp [base, twoPointGrid]
    · rcases Finset.mem_image.mp hm with ⟨l, _, hl⟩
      rw [← hl]
      fin_cases l
      · simpa [middle, twoPointGrid] using hst.le.trans htT
      · simpa [middle, twoPointGrid] using htT
  have hlast : π.time (Fin.last (commonStepCount base middle)) = T := by
    apply le_antisymm (hupper _)
    calc T = π.time (leftEndpointIndex base middle (Fin.last 1)) := by
           simp [π, commonTimeGrid_leftEndpointIndex, base, twoPointGrid]
         _ ≤ π.time (Fin.last (commonStepCount base middle)) :=
           π.strictMono_time.monotone (Fin.le_last _)
  let d : GridPresentation (κ := κ) μ T :=
    { steps := commonStepCount base middle
      grid := π
      initial_time := hzero
      terminal_time := hlast
      coeff := fun k b x => if i ≤ k.castSucc ∧ k.succ ≤ j then
        if b = a then H x else 0 else 0
      adapted := by
        intro k b
        by_cases hk : i ≤ k.castSucc ∧ k.succ ≤ j
        · by_cases hb : b = a
          · simp only [ite_eq_left hk, ite_eq_left hb]
            apply hH.mono _ le_rfl
            apply (commonWienerFiltration S κ).mono
            rw [← hi]
            exact π.strictMono_time.monotone hk.1
          · simp only [ite_eq_left hk, ite_eq_right hb]
            exact measurable_const
        · simp only [ite_eq_right hk]
          exact measurable_const
      coeffL2 := by
        intro k b
        by_cases hk : i ≤ k.castSucc ∧ k.succ ≤ j
        · by_cases hb : b = a
          · simpa only [ite_eq_left hk, ite_eq_left hb] using hHL2
          · simp only [ite_eq_left hk, ite_eq_right hb]
            exact MemLp.zero
        · simp only [ite_eq_right hk]
          exact MemLp.zero }
  refine ⟨d, ?_⟩
  intro b x
  by_cases hb : b = a
  · simp only [ite_eq_left hb]
    have hc : (fun k : Fin (commonStepCount base middle) => d.coeff k b) =
        fun k => if i ≤ k.castSucc ∧ k.succ ≤ j then H else 0 := by
      funext k y
      dsimp only [d]
      by_cases hk : i ≤ k.castSucc ∧ k.succ ≤ j <;> simp [hk, hb]
    change (∑ k, coefficientRectangle (π.time k.castSucc) (π.time k.succ) (d.coeff k b) x) = _
    have hpoint (k : Fin (commonStepCount base middle)) :
        d.coeff k b = if i ≤ k.castSucc ∧ k.succ ≤ j then H else 0 := congrFun hc k
    simp_rw [hpoint]
    rw [masked_rectangle_sum π i j hij H x, hi, hj]
  · simp only [ite_eq_right hb]
    have hpoint (k : Fin (commonStepCount base middle)) : d.coeff k b = 0 := by
      funext y
      dsimp only [d]
      by_cases hk : i ≤ k.castSucc ∧ k.succ ≤ j <;> simp [hk, hb]
    change (∑ k, coefficientRectangle (π.time k.castSucc) (π.time k.succ) (d.coeff k b) x) = 0
    simp [hpoint, coefficientRectangle]

end BlockBand.SourceProcess.FiniteDriverCompletion
