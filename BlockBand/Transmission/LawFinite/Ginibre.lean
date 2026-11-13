module

public import BlockBand.Transmission.LawFinite.GinibreFubini
public import BlockBand.Transmission.LawFinite.Along

/-!
# The small-singular-value fraction of a Ginibre matrix

`E #{i : s_i(B)² < a} · log(1/a) ≤ (b + log(1/b) + 4) W` for `B ~ Gin(b/W)`, `0 < a < 1`:
integrate `ofReal_count_mul_log_le` with `m_j = (b/W)(W - j)`, using `E Tr BᴴB = bW`
(`lintegral_chiSum_le`), `E nlog(‖gs_j‖²/m_j) ≤ 3` (`lintegral_nlog_gs_le`) and
`Σ_j log(1/m_j) = W log(W/b) - log W! ≤ W log(1/b) + W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Nat

/-- `Σ_{j<W} log(1/((b/W)(W-j))) ≤ W log(1/b) + W`. -/
theorem sum_log_inv_le {b : ℝ} (hb0 : 0 < b) (W : ℕ) (hW : 0 < W) :
    ∑ j : Fin W, Real.log ((b / W * ((W - j.val : ℕ) : ℝ))⁻¹) ≤
      W * Real.log b⁻¹ + W := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hk : ∀ j : Fin W, (0 : ℝ) < ((W - j.val : ℕ) : ℝ) := fun j => by
    have := j.isLt; exact_mod_cast (show 0 < W - j.val by omega)
  have hterm : ∀ j : Fin W, Real.log ((b / W * ((W - j.val : ℕ) : ℝ))⁻¹) =
      Real.log b⁻¹ + Real.log W - Real.log ((W - j.val : ℕ) : ℝ) := fun j => by
    rw [Real.log_inv, Real.log_mul (by positivity) (hk j).ne', Real.log_div hb0.ne' hW0.ne',
      Real.log_inv]
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfact : ∑ j : Fin W, Real.log ((W - j.val : ℕ) : ℝ) = Real.log (W ! : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => Real.log ((W - i : ℕ) : ℝ)),
      ← Finset.sum_range_reflect, ← Real.log_prod (fun i hi => by
        have := Finset.mem_range.1 hi; exact Nat.cast_ne_zero.2 (by omega))]
    congr 1
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [show W - (W - 1 - i) = i + 1 by omega]
    push_cast; ring
  rw [hfact]
  have hst := Real.pow_div_factorial_le_exp (x := (W : ℝ)) hW0.le W
  have hfpos : (0 : ℝ) < (W ! : ℝ) := by exact_mod_cast Nat.factorial_pos W
  have hlog : (W : ℝ) * Real.log W - Real.log (W ! : ℝ) ≤ W := by
    have := Real.log_le_log (by positivity) hst
    rw [Real.log_div (by positivity) hfpos.ne', Real.log_pow, Real.log_exp] at this
    linarith
  nlinarith [hlog]

/-- **`GinibreSmallSingularFraction`**, from Mathlib only. -/
theorem ginibreSmallSingularFraction_holds : GinibreSmallSingularFraction := by
  intro b hb0 hb
  have hlb : 0 < Real.log b⁻¹ := Real.log_pos ((one_lt_inv₀ hb0).2 (by linarith))
  refine ⟨b + Real.log b⁻¹ + 4, fun W hW a ha0 ha1 => ?_⟩
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  set t : ℝ≥0 := Real.toNNReal (b / W)
  have htR : (t : ℝ) = b / W := Real.coe_toNNReal _ (by positivity)
  have ht : t ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    simp only [htR, NNReal.coe_zero] at this
    exact (div_pos hb0 hW0).ne' this
  set L := Real.log a⁻¹
  have hL : 0 < L := Real.log_pos ((one_lt_inv₀ ha0).2 ha1)
  set μ := Measure.pi fun _ : Fin W => colLaw W t
  set m : Fin W → ℝ := fun j => (t : ℝ) * ((W - j.val : ℕ) : ℝ)
  have hm : ∀ j, 0 < m j := fun j => by
    have := j.isLt
    have : (0 : ℝ) < ((W - j.val : ℕ) : ℝ) := by exact_mod_cast (show 0 < W - j.val by omega)
    simp only [m, htR]; positivity
  have hcount : Measurable fun c : Fin W → Fin W → ℂ => (smallSingularCount a (colsMat c) : ℝ≥0∞) :=
    measurable_from_nat.comp ((measurable_smallSingularCount a).comp measurable_colsMat)
  rw [ginibre_eq_cols, lintegral_map
    (f := fun B : Matrix (Fin W) (Fin W) ℂ => (smallSingularCount a B : ℝ≥0∞))
    (measurable_from_nat.comp (measurable_smallSingularCount a)) measurable_colsMat]
  -- the integrated pointwise bound
  have hpt : ∀ c : Fin W → Fin W → ℂ, ENNReal.ofReal L * (smallSingularCount a (colsMat c) : ℝ≥0∞) ≤
      ENNReal.ofReal (∑ j, chiSum W (c j)) +
        ∑ j, (nlog (‖gsC c j‖ ^ 2 / m j) + ENNReal.ofReal (Real.log (m j)⁻¹)) := by
    intro c
    refine le_trans (le_of_eq ?_) (ofReal_count_mul_log_le c ha0 ha1 m hm)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]
  have hchi : ∫⁻ c, ENNReal.ofReal (∑ j, chiSum W (c j)) ∂μ = ENNReal.ofReal (W * b) := by
    rw [show (fun c : Fin W → Fin W → ℂ => ENNReal.ofReal (∑ j, chiSum W (c j))) =
        fun c => ∑ j, ENNReal.ofReal (chiSum W (c j)) from funext fun c =>
          ENNReal.ofReal_sum_of_nonneg fun j _ => chiSum_nonneg W _]
    rw [lintegral_finsetSum (f := fun j (c : Fin W → Fin W → ℂ) => ENNReal.ofReal (chiSum W (c j)))
      _ fun j _ => ENNReal.measurable_ofReal.comp ((continuous_chiSum W).measurable.comp
        (measurable_pi_apply j))]
    have hj : ∀ j : Fin W, ∫⁻ c, ENNReal.ofReal (chiSum W (c j)) ∂μ = ENNReal.ofReal (W * t) := by
      intro j
      have hmp := measurePreserving_eval_infinitePi (fun _ : Fin W => colLaw W t) j
      rw [Measure.infinitePi_eq_pi] at hmp
      exact (hmp.lintegral_comp (f := fun g => ENNReal.ofReal (chiSum W g))
        (ENNReal.measurable_ofReal.comp (continuous_chiSum W).measurable)).trans
        (lintegral_chiSum_le t)
    simp_rw [hj]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), htR]
    congr 1
    field_simp
  have hnl : ∀ j : Fin W, ∫⁻ c, nlog (‖gsC c j‖ ^ 2 / m j) ∂μ ≤ 3 :=
    fun j => lintegral_nlog_gs_le ht j
  have hlogs : ∑ j, ENNReal.ofReal (Real.log (m j)⁻¹) ≤
      ENNReal.ofReal (W * Real.log b⁻¹ + W) := by
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ Real.log (m j)⁻¹ := fun j _ => by
      apply Real.log_nonneg
      rw [one_le_inv₀ (hm j)]
      simp only [m, htR]
      have : ((W - j.val : ℕ) : ℝ) ≤ W := by exact_mod_cast Nat.sub_le _ _
      calc b / W * ((W - j.val : ℕ) : ℝ) ≤ b / W * W :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = b := by field_simp
        _ ≤ 1 := by linarith
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    apply ENNReal.ofReal_le_ofReal
    simpa [m, htR] using sum_log_inv_le hb0 W hW
  have hmeasF : ∀ j : Fin W, Measurable fun c : Fin W → Fin W → ℂ =>
      nlog (‖gsC c j‖ ^ 2 / m j) + ENNReal.ofReal (Real.log (m j)⁻¹) := fun j =>
    (measurable_nlog.comp (((measurable_gsC j).norm.pow_const 2).div_const _)).add measurable_const
  have hint : ENNReal.ofReal L * ∫⁻ c, (smallSingularCount a (colsMat c) : ℝ≥0∞) ∂μ ≤
      ENNReal.ofReal ((b + Real.log b⁻¹ + 4) * W) := by
    rw [← lintegral_const_mul _ hcount]
    refine (lintegral_mono hpt).trans ?_
    have hm1 : Measurable fun c : Fin W → Fin W → ℂ => ENNReal.ofReal (∑ j, chiSum W (c j)) :=
      ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ =>
        (continuous_chiSum W).measurable.comp (measurable_pi_apply j))
    rw [lintegral_add_left hm1, hchi, lintegral_finsetSum _ fun j _ => hmeasF j]
    have hsplit : ∀ j : Fin W, ∫⁻ c, (nlog (‖gsC c j‖ ^ 2 / m j) +
        ENNReal.ofReal (Real.log (m j)⁻¹)) ∂μ ≤ 3 + ENNReal.ofReal (Real.log (m j)⁻¹) := by
      intro j
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      exact add_le_add (hnl j) le_rfl
    refine (add_le_add le_rfl (Finset.sum_le_sum fun j _ => hsplit j)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine (add_le_add le_rfl (add_le_add le_rfl hlogs)).trans (le_of_eq ?_)
    rw [show (W : ℝ≥0∞) * 3 = ENNReal.ofReal (W * 3) by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]; norm_num]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [ENNReal.ofReal_div_of_pos hL]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hL)) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm]
  simpa [mul_div_assoc] using hint

end BlockBand.Transmission.LawFinite
