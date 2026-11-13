module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Diagonal border law: polar coordinates on `ℂ^n`

The image of Lebesgue measure on `ℂ` under `z ↦ |z|²` is `π` times Lebesgue measure on `(0, ∞)`
(`map_normSq_volume`, from `vol{|z|² ≤ t} = π t`); taking products,
`∫_{ℂ^n} F(|v_1|², …, |v_n|²) dv = π^n ∫_{(0,∞)^n} F(r) dr` for measurable `F ≥ 0`
(`lintegral_normSq_pi`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory Set
open scoped ENNReal

/-- `vol{z ∈ ℂ : |z|² ≤ t} = π t` (`0` for `t < 0`). -/
theorem volume_normSq_le (t : ℝ) :
    volume {z : ℂ | ‖z‖ ^ 2 ≤ t} = ENNReal.ofReal t * ENNReal.ofReal Real.pi := by
  rcases lt_or_ge t 0 with ht | ht
  · have : {z : ℂ | ‖z‖ ^ 2 ≤ t} = ∅ := by
      ext z; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht (sq_nonneg _)
    rw [this, measure_empty, ENNReal.ofReal_of_nonpos ht.le, zero_mul]
  · have : {z : ℂ | ‖z‖ ^ 2 ≤ t} = Metric.closedBall 0 (Real.sqrt t) := by
      ext z
      simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
      rw [Real.le_sqrt (norm_nonneg _) ht]
    rw [this, Complex.volume_closedBall, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt ht, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- `(π : ℝ≥0) = ofReal π` in `ℝ≥0∞`. -/
theorem coe_nnreal_pi_eq_ofReal : ((NNReal.pi : NNReal) : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- The image of Lebesgue measure on `ℂ` under `z ↦ |z|²` is `π · Leb|_(0,∞)`. -/
theorem map_normSq_volume :
    (volume : Measure ℂ).map (fun z => ‖z‖ ^ 2) =
      NNReal.pi • (volume : Measure ℝ).restrict (Ioi 0) := by
  have hm : Measurable fun z : ℂ => ‖z‖ ^ 2 := by fun_prop
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b hab => ?_)
  · rw [Measure.map_apply hm measurableSet_Ioc]
    refine ne_top_of_le_ne_top (b := volume {z : ℂ | ‖z‖ ^ 2 ≤ b}) ?_ (measure_mono ?_)
    · rw [volume_normSq_le]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · intro z hz; exact hz.2
  · rw [Measure.map_apply hm measurableSet_Ioc, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul, coe_nnreal_pi_eq_ofReal,
      Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi, Real.volume_Ioc]
    have hset : (fun z : ℂ => ‖z‖ ^ 2) ⁻¹' Ioc a b =
        {z : ℂ | ‖z‖ ^ 2 ≤ b} \ {z : ℂ | ‖z‖ ^ 2 ≤ a} := by
      ext z; simp [and_comm]
    have hsub : {z : ℂ | ‖z‖ ^ 2 ≤ a} ⊆ {z : ℂ | ‖z‖ ^ 2 ≤ b} := fun z hz =>
      le_trans hz hab.le
    rw [hset, measure_sdiff hsub ?_ ?_, volume_normSq_le,
      volume_normSq_le, ← ENNReal.sub_mul (fun _ _ => ENNReal.ofReal_ne_top)]
    · rw [mul_comm]
      congr 1
      rw [ENNReal.ofReal_sub _ (le_max_right a 0)]
      congr 1
      rcases le_total a 0 with ha | ha
      · rw [max_eq_right ha, ENNReal.ofReal_of_nonpos ha, ENNReal.ofReal_zero]
      · rw [max_eq_left ha]
    · exact (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet
    · rw [volume_normSq_le]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The image of Lebesgue measure on `ℂ^n` under `v ↦ (|v_i|²)_i` is `π^n · Leb|_(0,∞)^n`. -/
theorem map_normSq_pi {n : ℕ} :
    (volume : Measure (Fin n → ℂ)).map (fun v i => ‖v i‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ n) •
        (volume : Measure (Fin n → ℝ)).restrict (univ.pi fun _ => Ioi 0) := by
  have : SigmaFinite ((volume : Measure ℂ).map (fun z => ‖z‖ ^ 2)) := by
    rw [map_normSq_volume]; infer_instance
  have hm : Measurable fun z : ℂ => ‖z‖ ^ 2 := by fun_prop
  rw [volume_pi, Measure.pi_map_pi (fun _ => hm.aemeasurable),
    volume_pi, Measure.restrict_pi_pi]
  simp_rw [map_normSq_volume]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, coe_nnreal_pi_eq_ofReal,
    ENNReal.ofReal_pow Real.pi_pos.le]

/-- **Polar coordinates on `ℂ^n`**: `∫_{ℂ^n} F(|v_i|²) dv = π^n ∫_{(0,∞)^n} F(r) dr`. -/
theorem lintegral_normSq_pi {n : ℕ} (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ v : Fin n → ℂ, F (fun i => ‖v i‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ n) * ∫⁻ r in univ.pi (fun _ => Ioi 0), F r := by
  rw [← lintegral_map hF (by fun_prop), map_normSq_pi, lintegral_smul_measure, smul_eq_mul]

end BlockBand.DeterminantScore.WeylIntegration
