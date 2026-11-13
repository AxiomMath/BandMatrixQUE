module

public import BlockBand.SourceProcess.ComplexSourceLaw.KcMoments
public import BlockBand.Transmission.PassiveCovariance.Scalars

/-!
# Finite-width moments of the source data from the raw tag bound

Each entry of the source data `y = (𝒦, M_pr, B_pr, J_pr)` is controlled by four entries of `𝒦`
(`norm_sourceData_rpow_le`), so the raw tag bounds give `E Σ|y_{rij}|^p ≤ momentBound`
(`lintegral_sourceDataMoment_le`), with `B_ab = C(m_a m_b)^{p/2}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws

variable {W : ℕ}

theorem four_rpow_le {a b c d p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hp : 1 ≤ p) : (a + b + c + d) ^ p ≤ 4 ^ (p - 1) * (a ^ p + b ^ p + c ^ p + d ^ p) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ) (f := ![a, b, c, d])
    hp (by intro i _; fin_cases i <;> simpa)
  simp only [Fin.sum_univ_four, Finset.card_univ, Fintype.card_fin, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at h
  norm_num at h
  exact h

/-- The constant `(1 + η⁻¹)^p 4^{p-1}`. -/
def entryConst (η p : ℝ) : ℝ := (1 + η⁻¹) ^ p * 4 ^ (p - 1)

theorem entryConst_nonneg {η : ℝ} (hη : 0 < η) (p : ℝ) : 0 ≤ entryConst η p := by
  unfold entryConst; positivity

/-- Entrywise: `|y_{rij}|^p ≤ c(|𝒦ᵢⱼ|^p + |𝒦ⱼᵢ|^p + |𝒦ᵢᵢ|^p + |𝒦ⱼⱼ|^p)`. -/
theorem norm_sourceData_rpow_le (b E : ℝ) (hη : 0 < etaZ b E) {np : ℕ} (n : ℕ)
    (τ m : Fin np → ℝ) (x : ProbedPath W np) (hA : ∀ k, (x.1.1 k).IsHermitian) {p : ℝ}
    (hp : 1 ≤ p) (r : Fin 4) (i j : Fin np) :
    ‖complexSourceData b E W n τ m x r i j‖ ^ p ≤ entryConst (etaZ b E) p *
      (‖complexSourceK b E W n τ m x i j‖ ^ p + ‖complexSourceK b E W n τ m x j i‖ ^ p +
        ‖complexSourceK b E W n τ m x i i‖ ^ p + ‖complexSourceK b E W n τ m x j j‖ ^ p) := by
  have h := norm_sourceData_le b E hη n τ m x hA r i j
  have hp0 : 0 ≤ p := by linarith
  have he : 0 ≤ 1 + (etaZ b E)⁻¹ := by positivity
  calc ‖complexSourceData b E W n τ m x r i j‖ ^ p
      ≤ ((1 + (etaZ b E)⁻¹) * (‖complexSourceK b E W n τ m x i j‖ +
          ‖complexSourceK b E W n τ m x j i‖ + ‖complexSourceK b E W n τ m x i i‖ +
          ‖complexSourceK b E W n τ m x j j‖)) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h hp0
    _ = (1 + (etaZ b E)⁻¹) ^ p * (‖complexSourceK b E W n τ m x i j‖ +
          ‖complexSourceK b E W n τ m x j i‖ + ‖complexSourceK b E W n τ m x i i‖ +
          ‖complexSourceK b E W n τ m x j j‖) ^ p := Real.mul_rpow he (by positivity)
    _ ≤ _ := by
        rw [entryConst, mul_assoc]
        exact mul_le_mul_of_nonneg_left (four_rpow_le (norm_nonneg _) (norm_nonneg _)
          (norm_nonneg _) (norm_nonneg _) hp) (by positivity)

theorem ae_isHermitian_probed (W np : ℕ) (b : ℝ) :
    ∀ᵐ x ∂probedPathLaw W np b, ∀ k, (x.1.1 k).IsHermitian :=
  (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).ae
    (Transmission.Bridge.ae_growth_isHermitian W b)

/-- The bound `Σ_{r,i,j} c (Bᵢⱼ + Bⱼᵢ + Bᵢᵢ + Bⱼⱼ)`, `B_ab = C(m_a m_b)^{p/2}`. -/
def momentBound (η p C : ℝ) {np : ℕ} (m : Fin np → ℝ) : ENNReal :=
  ∑ _r : Fin 4, ∑ i, ∑ j, ENNReal.ofReal (entryConst η p) *
    (ENNReal.ofReal (C * (m i * m j) ^ (p / 2)) + ENNReal.ofReal (C * (m j * m i) ^ (p / 2)) +
      ENNReal.ofReal (C * (m i * m i) ^ (p / 2)) + ENNReal.ofReal (C * (m j * m j) ^ (p / 2)))

theorem momentBound_ne_top (η p C : ℝ) {np : ℕ} (m : Fin np → ℝ) :
    momentBound η p C m ≠ ⊤ := by
  unfold momentBound
  refine ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ =>
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  simp only [ne_eq, ENNReal.add_eq_top, ENNReal.ofReal_ne_top, or_self, not_false_eq_true]

/-- **Finite-width source moments**: `E Σ|y_{rij}|^p ≤ momentBound`. -/
theorem lintegral_sourceDataMoment_le (b E : ℝ) (hη : 0 < etaZ b E) {np : ℕ} (n : ℕ)
    (τ m : Fin np → ℝ) (hm : ∀ j, 0 ≤ m j) {p C : ℝ} (hp : 1 ≤ p)
    (hraw : RawTagBoundAt b E W n p C) :
    ∫⁻ x, ENNReal.ofReal (sourceDataMoment p (complexSourceData b E W n τ m x))
      ∂probedPathLaw W np b ≤ momentBound (etaZ b E) p C m := by
  set c := entryConst (etaZ b E) p
  have hc := entryConst_nonneg hη p
  have hp0 : 0 < p := by linarith
  have hf : ∀ a d : Fin np, Measurable fun x =>
      ENNReal.ofReal (‖complexSourceK b E W n τ m x a d‖ ^ p) := fun a d =>
    ENNReal.measurable_ofReal.comp
      ((measurable_complexSourceK b E W n τ m).eval_matrix.norm.pow_const p)
  have hpt : ∀ᵐ x ∂probedPathLaw W np b,
      ENNReal.ofReal (sourceDataMoment p (complexSourceData b E W n τ m x)) ≤
        ∑ _r : Fin 4, ∑ i, ∑ j, ENNReal.ofReal c *
          (ENNReal.ofReal (‖complexSourceK b E W n τ m x i j‖ ^ p) +
            ENNReal.ofReal (‖complexSourceK b E W n τ m x j i‖ ^ p) +
            ENNReal.ofReal (‖complexSourceK b E W n τ m x i i‖ ^ p) +
            ENNReal.ofReal (‖complexSourceK b E W n τ m x j j‖ ^ p)) := by
    filter_upwards [ae_isHermitian_probed W np b] with x hx
    unfold sourceDataMoment
    refine (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).le.trans
      (Finset.sum_le_sum fun r _ => ?_)
    refine (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).le.trans
      (Finset.sum_le_sum fun i _ => ?_)
    refine (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).le.trans
      (Finset.sum_le_sum fun j _ => ?_)
    refine (ENNReal.ofReal_le_ofReal (norm_sourceData_rpow_le b E hη n τ m x hx hp r i j)).trans
      (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
  have hg : ∀ i j : Fin np, Measurable fun x => ENNReal.ofReal c *
      (ENNReal.ofReal (‖complexSourceK b E W n τ m x i j‖ ^ p) +
        ENNReal.ofReal (‖complexSourceK b E W n τ m x j i‖ ^ p) +
        ENNReal.ofReal (‖complexSourceK b E W n τ m x i i‖ ^ p) +
        ENNReal.ofReal (‖complexSourceK b E W n τ m x j j‖ ^ p)) := fun i j =>
    ((((hf i j).add (hf j i)).add (hf i i)).add (hf j j)).const_mul _
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_finsetSum _ fun r _ => Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => hg i j]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [lintegral_finsetSum _ fun i _ => Finset.measurable_sum _ fun j _ => hg i j]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [lintegral_finsetSum _ fun j _ => hg i j]
  refine Finset.sum_le_sum fun j _ => ?_
  have hs : Measurable fun x =>
      ENNReal.ofReal (‖complexSourceK b E W n τ m x i j‖ ^ p) +
        ENNReal.ofReal (‖complexSourceK b E W n τ m x j i‖ ^ p) +
        ENNReal.ofReal (‖complexSourceK b E W n τ m x i i‖ ^ p) +
        ENNReal.ofReal (‖complexSourceK b E W n τ m x j j‖ ^ p) :=
    (((hf i j).add (hf j i)).add (hf i i)).add (hf j j)
  rw [lintegral_const_mul _ hs,
    lintegral_add_right _ (hf j j), lintegral_add_right _ (hf i i),
    lintegral_add_right _ (hf j i)]
  gcongr
  · exact lintegral_kc_le b E n τ m hm hp0 hraw i j
  · exact lintegral_kc_le b E n τ m hm hp0 hraw j i
  · exact lintegral_kc_le b E n τ m hm hp0 hraw i i
  · exact lintegral_kc_le b E n τ m hm hp0 hraw j j

end BlockBand.SourceProcess.ComplexSourceLaw
