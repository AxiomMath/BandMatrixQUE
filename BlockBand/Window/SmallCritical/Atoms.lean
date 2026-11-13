module

public import BlockBand.Window.SmallCritical.Diffuse

/-!
# Absence of atoms in the critical profile marks

The diffuseness part of the small-ratio critical theorem: almost surely the profile marks of a
critical marked limit have no atoms.

For the window `w_R` and spacing `L ≥ 1`, `pairMark L ν = L⁻² Σ_{j≠k<L} |ν̂_{L(j-k)}|²`
satisfies `ν({r})² - 1/L ≤ pairMark L ν` (`fourier_pair_sum_ge`) and
`E_P Σ_α w_R(u_α) pairMark L ν_α ≤ C K L^{-1/2}` (mode clause, `|L(j-k)| ≥ L`). Fatou twice and
the atom lower bound `F(x) ξ({x}) ≤ ∫ F dξ` give `ν({r}) = 0` for every atom `(u, ν)` of `ξ` with
`|u| < R + 2`, `P`-a.s.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal NNReal

attribute [local instance] massProfile_opensMeasurableSpace

/-- Off-diagonal pair term `|ν̂_{L(j-k)}|²` (zero on the diagonal). -/
def pairTerm (L : ℕ) (z : ℕ × ℕ) (ν : MassProfile) : ℝ :=
  if z.1 = z.2 then 0 else modeMark ((L : ℤ) * ((z.1 : ℤ) - z.2)) ν

/-- `pairMark L ν = L⁻² Σ_{j≠k<L} |ν̂_{L(j-k)}|²`. -/
def pairMark (L : ℕ) (ν : MassProfile) : ℝ :=
  ∑ z ∈ Finset.range L ×ˢ Finset.range L, (1 / (L : ℝ) ^ 2) * pairTerm L z ν

theorem continuous_pairTerm (L : ℕ) (z : ℕ × ℕ) : Continuous (pairTerm L z) := by
  unfold pairTerm
  split_ifs
  · exact continuous_const
  · exact continuous_modeMark _

theorem pairTerm_nonneg (L : ℕ) (z : ℕ × ℕ) (ν : MassProfile) : 0 ≤ pairTerm L z ν := by
  unfold pairTerm; split_ifs
  · exact le_rfl
  · exact modeMark_nonneg _ _

theorem continuous_pairMark (L : ℕ) : Continuous (pairMark L) :=
  continuous_finsetSum _ fun z _ => continuous_const.mul (continuous_pairTerm L z)

theorem pairMark_nonneg (L : ℕ) (ν : MassProfile) : 0 ≤ pairMark L ν :=
  Finset.sum_nonneg fun z _ => mul_nonneg (by positivity) (pairTerm_nonneg L z ν)

/-- `ν({r})² - 1/L ≤ pairMark L ν` for `L ≥ 1`. -/
theorem pairMark_ge (L : ℕ) (hL : 0 < L) (ν : MassProfile) (r : Torus) :
    (ν : Measure Torus).real {r} ^ 2 - 1 / (L : ℝ) ≤ pairMark L ν := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hbase := fourier_pair_sum_ge (ν : Measure Torus) r L L
  have hsplit : ∀ j k : ℕ, ‖∫ s, fourier (-((L : ℤ) * ((j : ℤ) - k))) s ∂(ν : Measure Torus)‖ ^ 2 =
      pairTerm L (j, k) ν + if j = k then 1 else 0 := by
    intro j k
    unfold pairTerm
    by_cases h : j = k
    · subst h; simp
    · simp only [h, ↓reduceIte, add_zero, modeMark]
  have hd : ∀ j ∈ Finset.range L, (∑ k ∈ Finset.range L,
      ‖∫ s, fourier (-((L : ℤ) * ((j : ℤ) - k))) s ∂(ν : Measure Torus)‖ ^ 2) =
      (∑ k ∈ Finset.range L, pairTerm L (j, k) ν) + 1 := by
    intro j hj
    rw [Finset.sum_congr rfl (fun k _ => hsplit j k), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [Finset.mem_range.mp hj]
  rw [Finset.sum_congr rfl hd, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hbase
  have hpm : pairMark L ν = (1 / (L : ℝ) ^ 2) *
      ∑ j ∈ Finset.range L, ∑ k ∈ Finset.range L, pairTerm L (j, k) ν := by
    unfold pairMark
    rw [← Finset.mul_sum, Finset.sum_product]
  rw [hpm]
  have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hL2]
  have : ((ν : Measure Torus).real {r} ^ 2 - 1 / (L : ℝ)) * (L : ℝ) ^ 2 =
      (ν : Measure Torus).real {r} ^ 2 * (L : ℝ) ^ 2 - L := by
    field_simp
  rw [this]
  linarith

theorem atoms_window_ae (hWT : WindowTransferContract)
    (hMode : ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ → θ < 1 / 2 →
      ModeBoundContract b θ T hb hb')
    {b : ℝ} {hb : 0 < b} {hb' : b < 1 / 2} {E : ℝ} (hE : E ^ 2 < 4) {τ : ℝ} (hτ : 0 < τ)
    {P : ProbabilityMeasure MarkedPointMeasure} (hP : IsCriticalMarkedLimit τ b E hb hb' P)
    (R : ℕ) :
    ∀ᵐ ξ ∂(P : Measure MarkedPointMeasure), ∀ x : MarkedSpectralSpace,
      ξ.marked.measure {x} ≠ 0 → |x.1| < R + 2 → ∀ r : Torus, (x.2 : Measure Torus) {r} = 0 := by
  obtain ⟨C, hC0, hC⟩ := mode_pow_bound hWT hMode hE hτ hP (η := 1 / 2) (by norm_num)
    (by norm_num)
  set K : ℝ := C * (τ + τ ^ (3 / 2 : ℝ)) ^ (1 - 1 / 2 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set w : SpectralWeight := windowWeight R with hw
  have hwc : Continuous (w : ℝ → ℝ) := w.toContinuousMap.continuous
  -- the expectation bound
  have hexp : ∀ n : ℕ, weightFunctional P (pairMark (n + 1)) w ≤
      ENNReal.ofReal (K * ((n + 1 : ℕ) : ℝ) ^ (-(1 - 1 / 2 : ℝ))) := by
    intro n
    set L : ℕ := n + 1 with hLdef
    have hLR : (0 : ℝ) < L := by positivity
    unfold pairMark
    rw [weightFunctional_markSum P (Finset.range L ×ˢ Finset.range L)
      (fun z ν => 1 / (L : ℝ) ^ 2 * pairTerm L z ν)
      (fun z => continuous_const.mul (continuous_pairTerm L z))
      (fun z ν => mul_nonneg (by positivity) (pairTerm_nonneg L z ν)) hwc w.compactSupport
      w.nonnegative]
    have hz : ∀ z ∈ Finset.range L ×ˢ Finset.range L,
        weightFunctional P (fun ν => 1 / (L : ℝ) ^ 2 * pairTerm L z ν) w ≤
          ENNReal.ofReal (1 / (L : ℝ) ^ 2 * (K * (L : ℝ) ^ (-(1 - 1 / 2 : ℝ)))) := by
      intro z _
      rw [weightFunctional_markConst P _ _ (by positivity), ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' le_rfl ?_
      by_cases hjk : z.1 = z.2
      · have : pairTerm L z = fun _ => 0 := by funext ν; simp [pairTerm, hjk]
        rw [this]
        unfold weightFunctional
        simp
      · have hm : ((L : ℤ) * ((z.1 : ℤ) - z.2)) ≠ 0 := by
          apply mul_ne_zero (by exact_mod_cast (show L ≠ 0 by omega))
          intro h; apply hjk; omega
        have hpt : pairTerm L z = modeMark ((L : ℤ) * ((z.1 : ℤ) - z.2)) := by
          funext ν; simp [pairTerm, hjk]
        rw [hpt, ← modeVariance_eq_weightFunctional]
        refine (hC w _ hm).trans (ENNReal.ofReal_le_ofReal ?_)
        apply mul_le_mul_of_nonneg_left _ hK0
        have hge : (L : ℝ) ≤ |(((L : ℤ) * ((z.1 : ℤ) - z.2) : ℤ) : ℝ)| := by
          push_cast
          rw [abs_mul, abs_of_pos hLR]
          have : (1 : ℝ) ≤ |((z.1 : ℝ) - z.2)| := by
            have h1 : ((z.1 : ℤ) - z.2) ≠ 0 := by intro h; apply hjk; omega
            have := Int.one_le_abs h1
            have h2 : (1 : ℝ) ≤ ((|((z.1 : ℤ) - z.2)| : ℤ) : ℝ) := by exact_mod_cast this
            push_cast at h2
            exact h2
          nlinarith
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
        exact inv_anti₀ (Real.rpow_pos_of_pos hLR _) (Real.rpow_le_rpow hLR.le hge (by norm_num))
    refine (Finset.sum_le_sum hz).trans ?_
    rw [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    push_cast
    field_simp
  -- Fatou
  set F : ℕ → MarkedSpectralSpace → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (w x.1 * pairMark (n + 1) x.2) with hF
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp (continuous_prodTest hwc (continuous_pairMark _)).measurable
  set G : ℕ → MarkedPointMeasure → ℝ≥0∞ := fun n ξ => ∫⁻ x, F n x ∂ξ.marked.measure with hG
  have hGm : ∀ n, Measurable (G n) := fun n =>
    measurable_markedLIntegral (continuous_prodTest hwc (continuous_pairMark _))
      (hasCompactSupport_prodTest w.compactSupport _)
      (prodTest_nonneg w.nonnegative (pairMark_nonneg _))
  have hHm : Measurable (fun ξ => liminf (fun n => G n ξ) atTop) := Measurable.liminf hGm
  have hdecay : Tendsto (fun n : ℕ => ENNReal.ofReal (K * ((n + 1 : ℕ) : ℝ) ^ (-(1 - 1 / 2 : ℝ))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 - 1 / 2)).comp h1
    have h3 := (ENNReal.continuous_ofReal.tendsto _).comp (h2.const_mul K)
    simpa [Function.comp_def] using h3
  have hzero : ∫⁻ ξ, liminf (fun n => G n ξ) atTop ∂(P : Measure MarkedPointMeasure) = 0 := by
    apply le_antisymm _ zero_le
    refine (lintegral_liminf_le hGm).trans ?_
    rw [← hdecay.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hexp) (by isBoundedDefault) (by isBoundedDefault)
  have hae := (lintegral_eq_zero_iff hHm).mp hzero
  filter_upwards [hae] with ξ hξ x hx hxR r
  have hξ' : liminf (fun n => G n ξ) atTop = 0 := hξ
  have hinner : ∫⁻ y, liminf (fun n => F n y) atTop ∂ξ.marked.measure = 0 :=
    le_antisymm ((lintegral_liminf_le hFm).trans_eq hξ') zero_le
  have hsingle := lintegral_singleton' (μ := ξ.marked.measure) (Measurable.liminf hFm) x
  have hFx : liminf (fun n => F n x) atTop = 0 := by
    have hle : liminf (fun n => F n x) atTop * ξ.marked.measure {x} ≤ 0 := by
      rw [← hsingle, ← hinner]
      exact setLIntegral_le_lintegral _ _
    rcases mul_eq_zero.mp (le_antisymm hle zero_le) with h | h
    · exact h
    · exact absurd h hx
  -- lower bound
  set a : ℝ := (x.2 : Measure Torus).real {r} with ha
  have hwpos : 0 < w x.1 := windowWeight_pos R hxR
  have hlow : Tendsto (fun n : ℕ => ENNReal.ofReal (w x.1 * (a ^ 2 - 1 / ((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (ENNReal.ofReal (w x.1 * a ^ 2))) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using this
    have h2 := (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds (x := a ^ 2)).sub h1 |>.const_mul (w x.1))
    simpa [Function.comp_def] using h2
  have hge : ENNReal.ofReal (w x.1 * a ^ 2) ≤ liminf (fun n => F n x) atTop := by
    rw [← hlow.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_) (by isBoundedDefault)
      (by isBoundedDefault)
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (pairMark_ge (n + 1) (Nat.succ_pos n) x.2 r) hwpos.le)
  rw [hFx, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hge
  have ha2 : a ^ 2 ≤ 0 := by
    by_contra h
    linarith [mul_pos hwpos (not_le.mp h)]
  have ha0 : a = 0 := by nlinarith [sq_nonneg a]
  rw [ha, measureReal_eq_zero_iff (measure_ne_top _ _)] at ha0
  exact ha0

end BlockBand.Window.SmallCritical
