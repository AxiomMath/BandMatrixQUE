module

public import BlockBand.SourceProcess.CutoffLimit.FrameAlg
public import BlockBand.SourceProcess.SourcePins.AtomFinite

/-!
# Initial frame traces in terms of the entrance measure

The initial distance `E X₀ = 2E Σ_omitted √t_i` tends to `0`, and the initial frame traces have
uniformly bounded first moment. For a sequence `t` in `[0,1]`:

* `hsSq_initialFrame_le`: `‖initialFrame K π t h‖²_HS ≤ 4 ∫ ψ_{1/2} d(Σ t_iδ_{t_i}) = 4 Σ √t_i`;
* `hsSq_initialFrame_sub_le` (`0 ≤ h₁ ≤ h₂`): the frames differ only in the modes
  `h₁² < t_k ≤ h₂²`, so `‖initialFrame t h₁ − initialFrame t h₂‖²_HS ≤ 4 ∫ ψ_{1/2} 1_{y ≤ h₂²}`.
Both bounds are uniform in the cap `K` (the constant `2` is possible; `4` is enough here).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.SourcePins
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

/-- `ψ_{1/2} 1_{y ≤ h²}`: the small-mode part of `ψ_{1/2}`. -/
def tailPsi (h : ℝ) : unitInterval → ℝ≥0∞ := Set.indicator {y : unitInterval | (y : ℝ) ≤ h ^ 2} (psiP (1 / 2))

theorem measurable_tailPsi (h : ℝ) : Measurable (tailPsi h) :=
  (measurable_psiP _).indicator (measurableSet_le measurable_subtype_coe measurable_const)

theorem lintegral_seqTraceMeasure (t : ℕ → ℝ) (F : unitInterval → ℝ≥0∞) :
    ∫⁻ y, F y ∂seqTraceMeasure t = ∑' i, ENNReal.ofReal (t i) * F (toUnit (t i)) := by
  rw [seqTraceMeasure, lintegral_sum_measure]
  refine tsum_congr fun i => ?_
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

theorem ofReal_mul_psiP {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    ENNReal.ofReal y * psiP (1 / 2) (toUnit y) = ENNReal.ofReal (Real.sqrt y) := by
  have := mul_psiP_toUnit (p := 1 / 2) (by norm_num) h0 h1
  rw [Real.sqrt_eq_rpow]
  exact this

theorem norm_modeVector_sq_le {t : ℝ} (h1 : t ≤ 1) (σ y : Fin 2) :
    ‖modeVector t σ y‖ ^ 2 ≤ 1 := by
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 h1
  have key : ∀ u : ℝ, u ≤ 2 → |√u| / |√2| ≤ 1 := by
    intro u hu2
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
      div_le_one (by positivity)]
    exact Real.sqrt_le_sqrt hu2
  have hn : ‖modeVector t σ y‖ ≤ 1 := by
    fin_cases σ <;> fin_cases y <;> simp [modeVector] <;> exact key _ (by linarith)
  exact pow_le_one₀ (norm_nonneg _) hn

theorem norm_mode_entry_sq_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (σ y : Fin 2) :
    ‖((t ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector t σ y‖ ^ 2 ≤ Real.sqrt t := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Real.rpow_natCast, ← Real.rpow_mul h0, Real.sqrt_eq_rpow]
  norm_num
  have := norm_modeVector_sq_le h1 σ y
  have hp : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg h0 _
  nlinarith

theorem hsSq_mode_le {K : ℕ} {π : Type*} [Fintype π] (F : Matrix (Fin K × Fin 2) (SrcCol K π) ℂ)
    (a : Fin K → ℝ) (C : Fin K → Prop) [DecidablePred C]
    (hF : ∀ x k σ, ‖F x (Sum.inl (k, σ))‖ ^ 2 ≤ if x.1 = k ∧ C k then a k else 0)
    (hπ : ∀ x j, F x (Sum.inr j) = 0) :
    hsSq F ≤ ∑ k, 4 * (if C k then a k else 0) := by
  calc hsSq F ≤ ∑ x : Fin K × Fin 2, ∑ y : Fin K × Fin 2, (if x.1 = y.1 ∧ C y.1 then a y.1 else 0) := by
        unfold hsSq
        refine Finset.sum_le_sum fun x _ => ?_
        rw [Fintype.sum_sum_type]
        simp only [hπ, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          Finset.sum_const_zero, add_zero]
        exact Finset.sum_le_sum fun y _ => hF x y.1 y.2
    _ = ∑ k, 4 * (if C k then a k else 0) := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ite_and, Finset.sum_add_distrib,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

theorem ofReal_sum_le_tsum {K : ℕ} (a : Fin K → ℝ) (ha : ∀ k, 0 ≤ a k) (b : ℕ → ℝ≥0∞)
    (hab : ∀ k : Fin K, ENNReal.ofReal (a k) ≤ b k) :
    ENNReal.ofReal (∑ k, 4 * a k) ≤ 4 * ∑' i, b i := by
  rw [← Finset.mul_sum, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg fun k _ => ha k]
  simp only [ENNReal.ofReal_ofNat]
  gcongr
  calc ∑ k : Fin K, ENNReal.ofReal (a k) ≤ ∑ k : Fin K, b k := Finset.sum_le_sum fun k _ => hab k
    _ = ∑ i ∈ Finset.range K, b i := Fin.sum_univ_eq_sum_range b K
    _ ≤ ∑' i, b i := ENNReal.sum_le_tsum _

theorem hsSq_initialFrame_le {K : ℕ} {π : Type*} [Fintype π] {t : ℕ → ℝ}
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (h : ℝ) :
    ENNReal.ofReal (hsSq (initialFrame K π t h)) ≤
      4 * ∫⁻ y, psiP (1 / 2) y ∂seqTraceMeasure t := by
  have hb := hsSq_mode_le (initialFrame K π t h) (fun k => Real.sqrt (t k.val))
    (fun k => h ^ 2 < t k.val) (fun x k σ => by
      simp only [initialFrame]
      split_ifs
      · exact norm_mode_entry_sq_le (ht _).1 (ht _).2 σ x.2
      · simp) (fun x j => rfl)
  rw [lintegral_seqTraceMeasure]
  refine (ENNReal.ofReal_le_ofReal hb).trans (ofReal_sum_le_tsum _
    (fun k => by split_ifs <;> simp [Real.sqrt_nonneg]) _ fun k => ?_)
  rw [ofReal_mul_psiP (ht _).1 (ht _).2]
  split_ifs
  · exact le_rfl
  · simp

theorem ofReal_mul_tailPsi {y h : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    ENNReal.ofReal y * tailPsi h (toUnit y) =
      if y ≤ h ^ 2 then ENNReal.ofReal (Real.sqrt y) else 0 := by
  rw [tailPsi, Set.indicator_apply]
  simp only [Set.mem_ofPred_eq, coe_toUnit_of_mem h0 h1]
  split_ifs
  · exact ofReal_mul_psiP h0 h1
  · simp

theorem hsSq_initialFrame_sub_le {K : ℕ} {π : Type*} [Fintype π] {t : ℕ → ℝ}
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) {h₁ h₂ : ℝ} (h0 : 0 ≤ h₁) (h12 : h₁ ≤ h₂) :
    ENNReal.ofReal (hsSq (initialFrame K π t h₁ - initialFrame K π t h₂)) ≤
      4 * ∫⁻ y, tailPsi h₂ y ∂seqTraceMeasure t := by
  have hsq : h₁ ^ 2 ≤ h₂ ^ 2 := pow_le_pow_left₀ h0 h12 2
  have hb := hsSq_mode_le (initialFrame K π t h₁ - initialFrame K π t h₂)
    (fun k => Real.sqrt (t k.val)) (fun k => t k.val ≤ h₂ ^ 2) (fun x k σ => by
      simp only [Matrix.sub_apply, initialFrame]
      by_cases hx : x.1 = k
      · by_cases hk2 : h₂ ^ 2 < t k.val
        · have hk1 : h₁ ^ 2 < t k.val := lt_of_le_of_lt hsq hk2
          simp only [hx, hk1, hk2, true_and, ite_true, sub_self, norm_zero]
          split_ifs <;> simp [Real.sqrt_nonneg]
        · simp only [hx, hk2, true_and, ite_false, sub_zero, not_lt.1 hk2, ite_true]
          split_ifs
          · exact norm_mode_entry_sq_le (ht _).1 (ht _).2 σ x.2
          · simp [Real.sqrt_nonneg]
      · simp [hx]) (fun x j => by simp [initialFrame])
  rw [lintegral_seqTraceMeasure]
  refine (ENNReal.ofReal_le_ofReal hb).trans (ofReal_sum_le_tsum _
    (fun k => by split_ifs <;> simp [Real.sqrt_nonneg]) _ fun k => ?_)
  rw [ofReal_mul_tailPsi (ht _).1 (ht _).2]
  split_ifs
  · exact le_rfl
  · simp

end BlockBand.SourceProcess.CutoffLimit

