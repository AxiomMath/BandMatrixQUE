module
public import BlockBand.SourceProcess.Stochastic.Integral.Indicator
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Terminal integral of one predictable rectangle

For `s, t ≤ T`, a noise direction `a` and an `F_s`-measurable coefficient `H ∈ L²(driverLaw μ)`,
the adopted terminal isometry `fullNativeIntegral μ T` sends the predictable rectangle
`1_{(s,t]}(r) H(x)` in direction `a` to `H · (W^a_{max s t} − W^a_s)`, almost surely for
`driverLaw μ`. For `s < t` this is the finite stochastic sum of an explicit grid
presentation (the construction of `exists_rectangle_presentation`, with its stochastic sum
computed); for `t ≤ s` both sides vanish.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open FiniteIto ContinuousItoCommonRefinement PredictableRectangle

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ] (T : ℝ≥0)
variable [DecidableEq κ]

omit [IsProbabilityMeasure μ] in
/-- A rectangle grid presentation whose finite stochastic sum is computed explicitly. -/
theorem exists_rectangle_presentation_integral (s t : ℝ≥0) (hst : s < t) (htT : t ≤ T)
    (a : κ) (H : DriverSample S κ → ℝ)
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    ∃ d : GridPresentation (κ := κ) μ T,
      (∀ b x, d.predictableFunction b x = if b = a then coefficientRectangle s t H x else 0) ∧
      ∀ x, d.integral x = H x * (commonRealBrownian t x a - commonRealBrownian s x a) := by
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
  refine ⟨d, ?_, ?_⟩
  · intro b x
    by_cases hb : b = a
    · simp only [ite_eq_left hb]
      have hpoint (k : Fin (commonStepCount base middle)) :
          d.coeff k b = if i ≤ k.castSucc ∧ k.succ ≤ j then H else 0 := by
        funext y
        dsimp only [d]
        by_cases hk : i ≤ k.castSucc ∧ k.succ ≤ j <;> simp [hk, hb]
      change (∑ k, coefficientRectangle (π.time k.castSucc) (π.time k.succ) (d.coeff k b) x) = _
      simp_rw [hpoint]
      rw [masked_rectangle_sum π i j hij H x, hi, hj]
    · simp only [ite_eq_right hb]
      have hpoint (k : Fin (commonStepCount base middle)) : d.coeff k b = 0 := by
        funext y
        dsimp only [d]
        by_cases hk : i ≤ k.castSucc ∧ k.succ ≤ j <;> simp [hk, hb]
      change (∑ k, coefficientRectangle (π.time k.castSucc) (π.time k.succ) (d.coeff k b) x) = 0
      simp [hpoint, coefficientRectangle]
  · intro x
    let B : Fin (commonStepCount base middle + 1) → ℝ := fun l =>
      commonRealBrownian (π.time l) x a
    let p : Fin (commonStepCount base middle) → Prop := fun k => i ≤ k.castSucc ∧ k.succ ≤ j
    have hterm (k : Fin (commonStepCount base middle)) :
        (∑ b : κ, d.term k b x) = if p k then H x * (B k.succ - B k.castSucc) else 0 := by
      simp only [GridPresentation.term_apply]
      by_cases hk : p k
      · simp only [d, p] at hk ⊢
        simp [hk, B, π]
      · simp only [d, p] at hk ⊢
        simp [hk]
    let R : Fin (commonStepCount base middle) → ℝ := fun k => H x * (B k.succ - B k.castSucc)
    calc d.integral x = ∑ k, ∑ b : κ, d.term k b x := by
          simp only [GridPresentation.integral, Fintype.sum_prod_type]
      _ = ∑ k, if p k then R k else 0 :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = ∑ k ∈ Finset.univ.filter p, R k := (Finset.sum_filter p R).symm
      _ = ∑ k : {k // p k}, R k := Finset.sum_subtype _ (by simp) R
      _ = H x * (B j - B i) := by
          simp only [R]
          rw [← Finset.mul_sum, sum_differences_between B i j hij]
      _ = _ := by simp only [B, hi, hj]

/-- The terminal integral of a nondegenerate bounded-horizon rectangle in direction `a`. -/
theorem fullNativeIntegral_rectangle_lt (s t : ℝ≥0) (hst : s < t) (htT : t ≤ T)
    (a : κ) (H : DriverSample S κ → ℝ)
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    (fullNativeIntegral (κ := κ) μ T (PiLp.single 2 a
      (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2)) : DriverSample S κ → ℝ)
      =ᵐ[driverLaw (κ := κ) μ]
      fun x => H x * (commonRealBrownian t x a - commonRealBrownian s x a) := by
  obtain ⟨d, hd, hint⟩ := exists_rectangle_presentation_integral μ T s t hst htT a H hH hHL2
  have he : d.predictableFamily = PiLp.single 2 a
      (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2) := by
    apply PiLp.ext
    intro b
    change d.scalarPredictable b = _
    by_cases hb : b = a
    · subst b
      rw [PiLp.single_eq_same]
      apply (predictableL2_eq_iff_ae_eq _ _).2
      filter_upwards [d.scalarPredictable_coeFn a,
        coefficientRectangle_class_coeFn μ T H hH hHL2] with x hx hy
      rw [hx, hy, hd, ite_eq_left rfl]
    · rw [PiLp.single_eq_of_ne 2 hb]
      apply (predictableL2_eq_iff_ae_eq _ _).2
      filter_upwards [d.scalarPredictable_coeFn b,
        (Lp.coeFn_zero ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))] with x hx hy
      rw [hx, hd, ite_eq_right hb]
      exact hy.symm
  rw [← he, fullNativeIntegral_presentation]
  filter_upwards [d.integralLp_coeFn] with x hx
  rw [hx, hint]

/-- The terminal integral of an arbitrary rectangle `(s,t]`, `t ≤ T` (possibly empty). -/
theorem fullNativeIntegral_rectangle (s t : ℝ≥0) (htT : t ≤ T)
    (a : κ) (H : DriverSample S κ → ℝ)
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    (fullNativeIntegral (κ := κ) μ T (PiLp.single 2 a
      (coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2)) : DriverSample S κ → ℝ)
      =ᵐ[driverLaw (κ := κ) μ]
      fun x => H x * (commonRealBrownian (max s t) x a - commonRealBrownian s x a) := by
  by_cases hst : s < t
  · simpa only [max_eq_right hst.le] using fullNativeIntegral_rectangle_lt μ T s t hst htT a H hH hHL2
  · have hts : t ≤ s := le_of_not_gt hst
    have hz : coefficientRectanglePredictableL2 enlargedPredictableFiltration T
        (driverLaw (κ := κ) μ) (s := s) (t := t) H hH hHL2 = 0 := by
      apply (predictableL2_eq_iff_ae_eq _ _).2
      filter_upwards [coefficientRectangle_class_coeFn μ T H hH hHL2,
        Lp.coeFn_zero ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))] with x hx hy
      rw [hx]
      change coefficientRectangle s t H x =
        ((0 : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ) x
      rw [hy]
      have hn : x ∉ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set (DriverSample S κ)) := by
        intro hx'
        have h1 := hx'.1.1
        have h2 := hx'.1.2
        have : (t : ℝ) ≤ (s : ℝ) := by exact_mod_cast hts
        linarith
      simp only [coefficientRectangle, Set.indicator_of_notMem hn, Pi.zero_apply]
    rw [hz, (PiLp.single_eq_zero_iff 2 a).2 rfl, map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 (driverLaw (κ := κ) μ)] with x hx
    rw [hx, max_eq_left hts, sub_self, mul_zero]
    rfl

end BlockBand.SourceProcess.Stochastic.Integral
