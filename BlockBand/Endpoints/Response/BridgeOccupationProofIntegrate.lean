module

public import BlockBand.Endpoints.Response.BridgeOccupationProofReduce

/-!
# From pointwise bridge-mean bounds to the occupation bounds

`bop_occupation_of_pointwise`: if a function `M ≥ 0` on `(0, T)` satisfies
`c (cosh((1-s/T)r₀) - 1)/2 ≤ M(s) ≤ C e^{(1-s/T)r₀} + 1`, `r₀ ≥ 3`, `0 < T ≤ τ`, then
* `∫_0^T M < ∞`;
* `∫_0^T M ≥ c' e^{r₀} T / r₀` with `c' = c e^{-1}/8` (integrate over `(0, T/r₀)`, where
  `(1-s/T)r₀ ≥ r₀ - 1` and `(cosh(r₀-1) - 1)/2 ≥ e^{r₀-1}/8` once `e^{r₀-1} ≥ 4`);
* for every `δ ∈ (0, τ)`: `∫_δ^T M ≤ C' (e^{-δr₀/τ} + r₀e^{-r₀}) ∫_0^T M` with
  `C' = (C+1)/c'` (`∫_δ^T e^{(1-s/T)r₀} ds ≤ (T/r₀)e^{r₀}e^{-δr₀/T}`, the `Y`-term `≤ T`,
  `e^{-δr₀/T} ≤ e^{-δr₀/τ}`, divide by the lower bound). The constants do not
  depend on `δ`, `T`, `r₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal

/-- `∫_δ^T e^{(1-s/T)r₀} ds ≤ (T/r₀) e^{(1-δ/T)r₀}`. -/
theorem bop_integral_exp_le {r₀ T δ : ℝ} (hr : 0 < r₀) (hT : 0 < T) :
    ∫ s in δ..T, Real.exp ((1 - s / T) * r₀) ≤ T / r₀ * Real.exp ((1 - δ / T) * r₀) := by
  have hderiv : ∀ x ∈ uIcc δ T, HasDerivAt (fun s => -(T / r₀) * Real.exp ((1 - s / T) * r₀))
      (Real.exp ((1 - x / T) * r₀)) x := by
    intro x _
    have h1 : HasDerivAt (fun s => (1 - s / T) * r₀) (-(1 / T) * r₀) x := by
      have := (((hasDerivAt_id x).div_const T).const_sub 1).mul_const r₀
      simpa using this
    have h2 := h1.exp.const_mul (-(T / r₀))
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)]
  have : 0 ≤ T / r₀ * Real.exp ((1 - T / T) * r₀) := by positivity
  linarith

/-- The same bound for the lower Lebesgue integral of `C e^{(1-s/T)r₀}` over `(δ, T)`. -/
theorem bop_lintegral_exp_le {C r₀ T δ : ℝ} (hC : 0 ≤ C) (hr : 0 < r₀) (hT : 0 < T)
    (hδT : δ ≤ T) :
    ∫⁻ s in Ioo δ T, ENNReal.ofReal (C * Real.exp ((1 - s / T) * r₀)) ≤
      ENNReal.ofReal (C * (T / r₀ * Real.exp ((1 - δ / T) * r₀))) := by
  have hcont : Continuous fun s => C * Real.exp ((1 - s / T) * r₀) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hcont.integrableOn_Icc (a := δ) (b := T)).mono_set Ioo_subset_Icc_self)
    (ae_of_all _ fun s => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδT,
    intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (bop_integral_exp_le hr hT) hC

/-- `c e^{r₀} e^{-1}/8 ≤ c (cosh((1-s/T)r₀) - 1)/2` for `s ≤ T/r₀`, `r₀ ≥ 3`. -/
theorem bop_cosh_lower {c r₀ T s : ℝ} (hc : 0 < c) (hr₀ : 3 ≤ r₀) (hT : 0 < T) (hs0 : 0 < s)
    (hs : s < T / r₀) :
    c * Real.exp (-1) / 8 * Real.exp r₀ ≤ c * ((Real.cosh ((1 - s / T) * r₀) - 1) / 2) := by
  have hr0 : 0 < r₀ := by linarith
  have hsT : s / T * r₀ ≤ 1 := by
    rw [lt_div_iff₀ hr0] at hs
    rw [div_mul_eq_mul_div, div_le_one hT]
    linarith
  have hsT0 : 0 ≤ s / T * r₀ := by positivity
  have h1 : r₀ - 1 ≤ (1 - s / T) * r₀ := by nlinarith
  have h2 : Real.cosh (r₀ - 1) ≤ Real.cosh ((1 - s / T) * r₀) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
    exact h1
  have h3 : Real.exp (r₀ - 1) / 2 ≤ Real.cosh (r₀ - 1) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(r₀ - 1))]
  have h4 : 4 ≤ Real.exp (r₀ - 1) := by
    have h5 := Real.add_one_le_exp ((r₀ - 1) / 2)
    have h6 : Real.exp (r₀ - 1) = Real.exp ((r₀ - 1) / 2) * Real.exp ((r₀ - 1) / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [h6]
    nlinarith
  have h7 : Real.exp (r₀ - 1) = Real.exp r₀ * Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have key : Real.exp r₀ * Real.exp (-1) / 8 ≤ (Real.cosh ((1 - s / T) * r₀) - 1) / 2 := by
    rw [← h7]; linarith
  calc c * Real.exp (-1) / 8 * Real.exp r₀ = c * (Real.exp r₀ * Real.exp (-1) / 8) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hc.le

/-- **The occupation bounds from pointwise bounds**. -/
theorem bop_occupation_of_pointwise {c C r₀ τ T : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hr₀ : 3 ≤ r₀)
    (hT : T ∈ Ioc 0 τ) {M : ℝ → ℝ≥0∞}
    (hlow : ∀ s ∈ Ioo 0 T, ENNReal.ofReal (c * ((Real.cosh ((1 - s / T) * r₀) - 1) / 2)) ≤ M s)
    (hup : ∀ s ∈ Ioo 0 T, M s ≤ ENNReal.ofReal (C * Real.exp ((1 - s / T) * r₀)) + 1) :
    (∫⁻ s in Ioo 0 T, M s) ≠ ⊤ ∧
    ENNReal.ofReal (c * Real.exp (-1) / 8 * Real.exp r₀ * T / r₀) ≤ ∫⁻ s in Ioo 0 T, M s ∧
    ∀ δ ∈ Ioo 0 τ, ∫⁻ s in Ioo δ T, M s ≤
      ENNReal.ofReal ((C + 1) / (c * Real.exp (-1) / 8) *
        (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀))) * ∫⁻ s in Ioo 0 T, M s := by
  obtain ⟨hT0, hTτ⟩ := hT
  have hr0 : 0 < r₀ := by linarith
  set c' := c * Real.exp (-1) / 8 with hc'
  have hc'0 : 0 < c' := by positivity
  -- finiteness
  have hfin : (∫⁻ s in Ioo 0 T, M s) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioo 0 T, (ENNReal.ofReal (C * Real.exp r₀) + 1)) ?_
      (setLIntegral_mono' measurableSet_Ioo fun s hs => (hup s hs).trans ?_)
    · rw [setLIntegral_const, Real.volume_Ioo]
      exact ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)
        ENNReal.ofReal_ne_top
    · gcongr
      have : 0 ≤ s / T * r₀ := by have := hs.1; positivity
      nlinarith
  -- the lower bound
  have hlowI : ENNReal.ofReal (c' * Real.exp r₀ * T / r₀) ≤ ∫⁻ s in Ioo 0 T, M s := by
    have hsub : Ioo 0 (T / r₀) ⊆ Ioo 0 T :=
      Ioo_subset_Ioo_right (div_le_self hT0.le (by linarith))
    have hK : ∀ s ∈ Ioo 0 (T / r₀), ENNReal.ofReal (c' * Real.exp r₀) ≤ M s := fun s hs =>
      (ENNReal.ofReal_le_ofReal (bop_cosh_lower hc hr₀ hT0 hs.1 hs.2)).trans (hlow s (hsub hs))
    calc ENNReal.ofReal (c' * Real.exp r₀ * T / r₀)
        = ∫⁻ _ in Ioo 0 (T / r₀), ENNReal.ofReal (c' * Real.exp r₀) := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ ≤ ∫⁻ s in Ioo 0 (T / r₀), M s := setLIntegral_mono' measurableSet_Ioo hK
      _ ≤ ∫⁻ s in Ioo 0 T, M s := lintegral_mono_set hsub
  refine ⟨hfin, hlowI, fun δ hδ => ?_⟩
  by_cases hδT : T ≤ δ
  · rw [Ioo_eq_empty (not_lt.2 hδT), Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  rw [not_le] at hδT
  set A := Real.exp (r₀ - δ / τ * r₀) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have hexp : Real.exp ((1 - δ / T) * r₀) ≤ A := by
    refine Real.exp_le_exp.2 ?_
    have : δ / τ ≤ δ / T := div_le_div_of_nonneg_left hδ.1.le hT0 hTτ
    nlinarith
  have hkey : C * (T / r₀ * Real.exp ((1 - δ / T) * r₀)) + T ≤
      (C + 1) / c' * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀)) *
        (c' * Real.exp r₀ * T / r₀) := by
    have e1 : Real.exp (-(δ * r₀ / τ)) * Real.exp r₀ = A := by
      rw [← Real.exp_add, hA]; ring_nf
    have e2 : Real.exp (-r₀) * Real.exp r₀ = 1 := by
      rw [← Real.exp_add]; simp
    have hR : (C + 1) / c' * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀)) *
        (c' * Real.exp r₀ * T / r₀) = (C + 1) * (A * T / r₀ + T) := by
      calc (C + 1) / c' * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀)) *
            (c' * Real.exp r₀ * T / r₀)
          = (C + 1) * (Real.exp (-(δ * r₀ / τ)) * Real.exp r₀ +
              r₀ * (Real.exp (-r₀) * Real.exp r₀)) * T / r₀ := by
            field_simp
        _ = (C + 1) * (A * T / r₀ + T) := by
            rw [e1, e2]; field_simp
    rw [hR]
    have h1 : C * (T / r₀ * Real.exp ((1 - δ / T) * r₀)) ≤ C * (A * T / r₀) := by
      rw [show A * T / r₀ = T / r₀ * A by ring]
      gcongr
    have h2 : 0 ≤ A * T / r₀ := by positivity
    nlinarith
  calc ∫⁻ s in Ioo δ T, M s
      ≤ ∫⁻ s in Ioo δ T, (ENNReal.ofReal (C * Real.exp ((1 - s / T) * r₀)) + 1) :=
        setLIntegral_mono' measurableSet_Ioo fun s hs => hup s ⟨hδ.1.trans hs.1, hs.2⟩
    _ = (∫⁻ s in Ioo δ T, ENNReal.ofReal (C * Real.exp ((1 - s / T) * r₀))) +
          ENNReal.ofReal (T - δ) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioo, one_mul]
    _ ≤ ENNReal.ofReal (C * (T / r₀ * Real.exp ((1 - δ / T) * r₀))) + ENNReal.ofReal T :=
        add_le_add (bop_lintegral_exp_le hC hr0 hT0 hδT.le)
          (ENNReal.ofReal_le_ofReal (by linarith [hδ.1]))
    _ = ENNReal.ofReal (C * (T / r₀ * Real.exp ((1 - δ / T) * r₀)) + T) :=
        (ENNReal.ofReal_add (by positivity) hT0.le).symm
    _ ≤ ENNReal.ofReal ((C + 1) / c' * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀)) *
          (c' * Real.exp r₀ * T / r₀)) := ENNReal.ofReal_le_ofReal hkey
    _ = ENNReal.ofReal ((C + 1) / c' * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀))) *
          ENNReal.ofReal (c' * Real.exp r₀ * T / r₀) := ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr

end BlockBand.Endpoints
