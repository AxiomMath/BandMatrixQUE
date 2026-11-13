module

public import BlockBand.Transmission.LawFinite.GinibreCount
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Moments.Variance

/-!
# Ginibre matrices as independent columns; per-column expectations

* `ginibre_eq_cols`: `Gin(t) = (⊗_j colLaw W t).map colsMat` (independent columns);
* `measurable_gsC`: Gram–Schmidt vectors are Borel in the columns;
* **`lintegral_nlog_gs_le`**: `E nlog(‖gs_j‖²/(t(W-j))) ≤ 3` (condition on the other columns
  with `lmarginal`; frame + Bessel + unitary invariance + chi-square tail);
* `lintegral_chiSum_le`: `E Σ_x |g_x|² ≤ W t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal InnerProductSpace

variable {W : ℕ}

theorem measurable_colsMat :
    Measurable (colsMat : (Fin W → Fin W → ℂ) → Matrix (Fin W) (Fin W) ℂ) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun j => ?_
  exact (measurable_pi_apply x).comp (measurable_pi_apply j)

theorem measurable_toC_cols :
    Measurable fun R : Fin W → (Fin W × Fin 2 → ℝ) => fun j => toC (R j) := by
  refine Measurable.of_eval fun j => ?_
  exact measurable_toC.comp (measurable_pi_apply j)

/-- Independent columns. -/
theorem ginibre_eq_cols (t : ℝ≥0) :
    ginibreMeasure (Fin W) (Fin W) t =
      (Measure.pi fun _ : Fin W => colLaw W t).map colsMat := by
  set N := gaussianReal 0 (t / 2)
  set σ : Fin W × (Fin W × Fin 2) ≃ Fin W × (Fin W × Fin 2) :=
    { toFun := fun q => (q.2.1, (q.1, q.2.2)), invFun := fun q => (q.2.1, (q.1, q.2.2)),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hσ := measurePreserving_piCongrLeft (fun _ : Fin W × (Fin W × Fin 2) => N) σ
  have hcur : (Measure.pi fun _ : Fin W × (Fin W × Fin 2) => N).map
      (MeasurableEquiv.curry (Fin W) (Fin W × Fin 2) ℝ) =
        Measure.pi fun _ : Fin W => Measure.pi fun _ : Fin W × Fin 2 => N := by
    have h := Measure.infinitePi_map_curry (fun (_ : Fin W) (_ : Fin W × Fin 2) => N)
    simp only [Measure.infinitePi_eq_pi] at h
    convert h using 3
  have hcol : (Measure.pi fun _ : Fin W => colLaw W t) =
      (Measure.pi fun _ : Fin W => Measure.pi fun _ : Fin W × Fin 2 => N).map
        (fun R j => toC (R j)) := by
    rw [Measure.pi_map_pi (fun _ => measurable_toC.aemeasurable)]
    rfl
  have hc := (MeasurableEquiv.curry (Fin W) (Fin W × Fin 2) ℝ).measurable
  rw [hcol, ← hcur, ← hσ.map_eq, Measure.map_map measurable_toC_cols hc,
    Measure.map_map measurable_colsMat (measurable_toC_cols.comp hc),
    Measure.map_map (measurable_colsMat.comp (measurable_toC_cols.comp hc))
      (MeasurableEquiv.piCongrLeft _ σ).measurable]
  rw [ginibreMeasure]
  congr 1

theorem measurable_colsE (j : Fin W) : Measurable fun c : Fin W → Fin W → ℂ => colsE c j :=
  ((PiLp.continuous_toLp 2 _).comp (continuous_apply j)).measurable

/-- Gram–Schmidt vectors are measurable in the columns. -/
theorem measurable_gsC (j : Fin W) : Measurable fun c : Fin W → Fin W → ℂ => gsC c j := by
  induction j using WellFoundedLT.induction with
  | ind n ih =>
    have h : (fun c : Fin W → Fin W → ℂ => gsC c n) = fun c => colsE c n -
        ∑ i ∈ Finset.Iio n, (⟪gsC c i, colsE c n⟫_ℂ / ((‖gsC c i‖ : ℂ) ^ 2)) • gsC c i := by
      funext c
      have := gramSchmidt_def'' ℂ (colsE c) n
      show gramSchmidt ℂ (colsE c) n = colsE c n - ∑ i ∈ Finset.Iio n,
        (⟪gramSchmidt ℂ (colsE c) i, colsE c n⟫_ℂ / ((‖gramSchmidt ℂ (colsE c) i‖ : ℂ) ^ 2)) •
          gramSchmidt ℂ (colsE c) i
      rw [eq_sub_iff_add_eq]
      exact this.symm
    rw [h]
    refine (measurable_colsE n).sub (Finset.measurable_sum _ fun i hi => ?_)
    have hi' := ih i (Finset.mem_Iio.1 hi)
    have hcoef : Measurable fun c : Fin W → Fin W → ℂ =>
        ⟪gsC c i, colsE c n⟫_ℂ / ((‖gsC c i‖ : ℂ) ^ 2) :=
      ((continuous_inner.measurable).comp (hi'.prodMk (measurable_colsE n))).div
        ((Complex.measurable_ofReal.comp hi'.norm).pow_const 2)
    exact hcoef.smul hi'

theorem measurable_nlog : Measurable nlog :=
  Measurable.ite measurableSet_Ioi (ENNReal.measurable_ofReal.comp Real.measurable_log.neg)
    measurable_const

/-- **Per-column expectation**: `E nlog(‖gs_j‖²/(t(W-j))) ≤ 3`. -/
theorem lintegral_nlog_gs_le {t : ℝ≥0} (ht : t ≠ 0) (j : Fin W) :
    ∫⁻ c, nlog (‖gsC c j‖ ^ 2 / (t * ((W - j.val : ℕ) : ℝ)))
      ∂(Measure.pi fun _ : Fin W => colLaw W t) ≤ 3 := by
  classical
  set k := W - j.val
  have hk1 : 1 ≤ k := by have := j.isLt; omega
  have hkW : k ≤ W := Nat.sub_le _ _
  set F : (Fin W → Fin W → ℂ) → ℝ≥0∞ := fun c => nlog (‖gsC c j‖ ^ 2 / (t * (k : ℝ)))
  have hF : Measurable F :=
    measurable_nlog.comp (((measurable_gsC j).norm.pow_const 2).div_const _)
  have hinner : ∀ x : Fin W → Fin W → ℂ,
      ∫⁻ y, F (Function.update x j y) ∂colLaw W t ≤ 3 := by
    intro x
    obtain ⟨u, hu⟩ := exists_frame x j
    have hu' : ∀ y, ∀ l : Fin W, l.val < k → ∀ m < j,
        ⟪u l, colsE (Function.update x j y) m⟫_ℂ = 0 := by
      intro y l hl m hm
      have : colsE (Function.update x j y) m = colsE x m := by
        simp [colsE, Function.update_of_ne (ne_of_lt hm)]
      rw [this]; exact hu l hl m hm
    have hle : ∀ y, F (Function.update x j y) ≤
        nlog (chiSum k (reprMap u y) / (t * (k : ℝ))) := by
      intro y
      have h := chiSum_le_gs (Function.update x j y) j u k (hu' y)
      rw [Function.update_self] at h
      exact nlog_antitone (div_le_div_of_nonneg_right h (by positivity))
    have hm : Measurable fun z : Fin W → ℂ => nlog (chiSum k z / (t * (k : ℝ))) :=
      measurable_nlog.comp ((continuous_chiSum k).measurable.div_const _)
    calc ∫⁻ y, F (Function.update x j y) ∂colLaw W t
        ≤ ∫⁻ y, nlog (chiSum k (reprMap u y) / (t * (k : ℝ))) ∂colLaw W t := lintegral_mono hle
      _ = ∫⁻ z, nlog (chiSum k z / (t * (k : ℝ))) ∂(colLaw W t).map (reprMap u) :=
          (lintegral_map hm (measurable_reprMap u)).symm
      _ = ∫⁻ z, nlog (chiSum k z / (t * (k : ℝ))) ∂colLaw W t := by rw [colLaw_map_repr]
      _ ≤ 3 := lintegral_nlog_chiSum_le ht hk1 hkW
  set x₀ : Fin W → Fin W → ℂ := fun _ _ => 0
  rw [lintegral_eq_lmarginal_univ x₀, lmarginal_erase' _ hF (Finset.mem_univ j)]
  calc (∫⋯∫⁻_Finset.univ.erase j, (fun x => ∫⁻ y, F (Function.update x j y) ∂colLaw W t)
        ∂fun _ => colLaw W t) x₀
      ≤ (∫⋯∫⁻_Finset.univ.erase j, (fun _ => (3 : ℝ≥0∞)) ∂fun _ => colLaw W t) x₀ :=
        lmarginal_mono (fun x => hinner x) x₀
    _ = 3 := by
      simp only [lmarginal, lintegral_const, measure_univ, mul_one]

/-- `E (r²) = v` for `r ~ N(0,v)`, as a lower integral. -/
theorem lintegral_sq_gaussianReal (v : ℝ≥0) :
    ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂gaussianReal 0 v = ENNReal.ofReal v := by
  have hint : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => sq_nonneg y)]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ => x) aemeasurable_id'] at h
  simp only [integral_id_gaussianReal, sub_zero] at h
  rw [h]

/-- `E Σ_x |g_x|² = W t`. -/
theorem lintegral_chiSum_le (t : ℝ≥0) :
    ∫⁻ g, ENNReal.ofReal (chiSum W g) ∂colLaw W t = ENNReal.ofReal (W * t) := by
  have hm : Measurable fun g : Fin W → ℂ => ENNReal.ofReal (chiSum W g) :=
    ENNReal.measurable_ofReal.comp (continuous_chiSum W).measurable
  rw [colLaw, lintegral_map hm measurable_toC]
  have hsum : ∀ r : Fin W × Fin 2 → ℝ, chiSum W (toC r) = ∑ p, r p ^ 2 := fun r => by
    rw [chiSum_toC]; exact Finset.sum_congr rfl fun p _ => by simp [p.1.isLt]
  simp_rw [hsum]
  rw [show (fun r : Fin W × Fin 2 → ℝ => ENNReal.ofReal (∑ p, r p ^ 2)) =
      fun r => ∑ p, ENNReal.ofReal (r p ^ 2) from funext fun r =>
        ENNReal.ofReal_sum_of_nonneg fun p _ => sq_nonneg _]
  rw [lintegral_finsetSum (f := fun p (r : Fin W × Fin 2 → ℝ) => ENNReal.ofReal (r p ^ 2)) _
    fun p _ => ENNReal.measurable_ofReal.comp ((measurable_pi_apply p).pow_const 2)]
  have hp : ∀ p : Fin W × Fin 2, ∫⁻ r, ENNReal.ofReal (r p ^ 2)
      ∂(Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 (t / 2)) = ENNReal.ofReal (t / 2) := by
    intro p
    have hmp := measurePreserving_eval_infinitePi (fun _ : Fin W × Fin 2 => gaussianReal 0 (t / 2)) p
    rw [Measure.infinitePi_eq_pi] at hmp
    refine (hmp.lintegral_comp (f := fun y : ℝ => ENNReal.ofReal (y ^ 2))
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2))).trans ?_
    rw [lintegral_sq_gaussianReal]
    simp
  simp_rw [hp]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

end BlockBand.Transmission.LawFinite
