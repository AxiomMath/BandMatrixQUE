module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Augment
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Localize
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Measurability, path continuity and bounds of the Itô coefficients)

For `φ : ℝ × ℝ^d → ℝ` (contract objects `partialTime`, `partialSpace`, `partialSpace2`,
`itoDrift`, `itoBracket` of `BlockBand.Internal.Contracts.Transmission`):

* the partial derivatives are Borel measurable with **no** regularity of `φ`
  (`measurable_fderiv`); hence `itoDrift`, `itoBracket` evaluated along measurable
  arguments are measurable (`measurable_itoDrift_comp`, `measurable_itoBracket_comp`);
* for `φ ∈ C²(univ ×ˢ U)` and a continuous path in `U`, the partial derivatives along the path
  are continuous (`continuous_partial*_path`), and the paths of `itoDrift`, `itoBracket` are
  integrable on every `(0, t]` when `β`, `α` are (`integrableOn_itoDrift_path`,
  `integrableOn_itoBracket_path`);
* on a compact `Kc ⊆ univ ×ˢ U` the partial derivatives are bounded by one constant `M`, and
  `|itoDrift| ≤ M (1 + Σ|b_i| + Σ|a_ij|)` (`abs_itoDrift_le`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ}

theorem measurable_partialTime (φ : ℝ × (Fin d → ℝ) → ℝ) : Measurable (partialTime φ) :=
  measurable_fderiv_apply_const ℝ φ (1, 0)

theorem measurable_partialSpace (φ : ℝ × (Fin d → ℝ) → ℝ) (i : Fin d) :
    Measurable fun p => partialSpace φ p i :=
  measurable_fderiv_apply_const ℝ φ (0, Pi.single i 1)

theorem measurable_partialSpace2 (φ : ℝ × (Fin d → ℝ) → ℝ) (i j : Fin d) :
    Measurable fun p => partialSpace2 φ p i j :=
  (ContinuousLinearMap.measurable_apply _).comp
    (measurable_fderiv_apply_const ℝ (fderiv ℝ φ) (0, Pi.single i 1))

theorem measurable_itoDrift_comp {X : Type*} [MeasurableSpace X] (φ : ℝ × (Fin d → ℝ) → ℝ)
    {T : X → ℝ≥0} {y b : X → Fin d → ℝ} {a : X → Fin d → Fin d → ℝ} (hT : Measurable T)
    (hy : Measurable y) (hb : Measurable b) (ha : Measurable a) :
    Measurable fun x => itoDrift φ (y x) (T x) (b x) (a x) := by
  have hp : Measurable fun x => (((T x : ℝ≥0) : ℝ), y x) :=
    (measurable_coe_nnreal_real.comp hT).prodMk hy
  unfold itoDrift
  refine ((measurable_partialTime φ).comp hp).add (Finset.measurable_sum _ fun i _ => ?_)
    |>.add (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => ?_))
  · exact ((measurable_pi_apply i).comp hb).mul ((measurable_partialSpace φ i).comp hp)
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp ha)).mul
      ((measurable_partialSpace2 φ i j).comp hp)

theorem measurable_itoBracket_comp {X : Type*} [MeasurableSpace X] (φ : ℝ × (Fin d → ℝ) → ℝ)
    {T : X → ℝ≥0} {y : X → Fin d → ℝ} {a : X → Fin d → Fin d → ℝ} (hT : Measurable T)
    (hy : Measurable y) (ha : Measurable a) :
    Measurable fun x => itoBracket φ (y x) (T x) (a x) := by
  have hp : Measurable fun x => (((T x : ℝ≥0) : ℝ), y x) :=
    (measurable_coe_nnreal_real.comp hT).prodMk hy
  unfold itoBracket
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp ha)).mul
    ((measurable_partialSpace φ i).comp hp)).mul ((measurable_partialSpace φ j).comp hp)

variable {U : Set (Fin d → ℝ)} {φ : ℝ × (Fin d → ℝ) → ℝ}

theorem continuousOn_fderiv_U (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U)) :
    ContinuousOn (fderiv ℝ φ) (univ ×ˢ U) :=
  hφ.continuousOn_fderiv_of_isOpen (isOpen_univ.prod hU) (by norm_num)

theorem continuousOn_fderiv2_U (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U)) :
    ContinuousOn (fderiv ℝ (fderiv ℝ φ)) (univ ×ˢ U) :=
  (hφ.fderiv_of_isOpen (isOpen_univ.prod hU) (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
    (isOpen_univ.prod hU) le_rfl

variable {Ω : Type*} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}

theorem continuous_pair_path (hY : Continuous fun t => Y t ω) :
    Continuous fun s : ℝ => (((s.toNNReal : ℝ≥0) : ℝ), Y s.toNNReal ω) :=
  (NNReal.continuous_coe.comp continuous_real_toNNReal).prodMk
    (hY.comp continuous_real_toNNReal)

theorem continuous_partialTime_path (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    (hY : Continuous fun t => Y t ω) (hYU : ∀ t, Y t ω ∈ U) :
    Continuous fun s : ℝ => partialTime φ (((s.toNNReal : ℝ≥0) : ℝ), Y s.toNNReal ω) :=
  ((continuousOn_fderiv_U hU hφ).comp_continuous (continuous_pair_path hY)
    fun _ => ⟨mem_univ _, hYU _⟩).clm_apply continuous_const

theorem continuous_partialSpace_path (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    (hY : Continuous fun t => Y t ω) (hYU : ∀ t, Y t ω ∈ U) (i : Fin d) :
    Continuous fun s : ℝ => partialSpace φ (((s.toNNReal : ℝ≥0) : ℝ), Y s.toNNReal ω) i :=
  ((continuousOn_fderiv_U hU hφ).comp_continuous (continuous_pair_path hY)
    fun _ => ⟨mem_univ _, hYU _⟩).clm_apply continuous_const

theorem continuous_partialSpace2_path (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    (hY : Continuous fun t => Y t ω) (hYU : ∀ t, Y t ω ∈ U) (i j : Fin d) :
    Continuous fun s : ℝ => partialSpace2 φ (((s.toNNReal : ℝ≥0) : ℝ), Y s.toNNReal ω) i j :=
  (((continuousOn_fderiv2_U hU hφ).comp_continuous (continuous_pair_path hY)
    fun _ => ⟨mem_univ _, hYU _⟩).clm_apply continuous_const).clm_apply continuous_const

theorem integrableOn_mul_continuous {f g : ℝ → ℝ} {t : ℝ≥0} (hf : IntegrableOn f (Ioc 0 t))
    (hg : Continuous g) : IntegrableOn (fun s => f s * g s) (Ioc 0 t) := by
  have hf' : IntegrableOn f (Icc 0 t) := (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).2 hf
  exact (hf'.mul_continuousOn hg.continuousOn isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- Paths of `itoDrift` are integrable on every `(0, t]`. -/
theorem integrableOn_itoDrift_path (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
    (hY : Continuous fun t => Y t ω) (hYU : ∀ t, Y t ω ∈ U) (t : ℝ≥0)
    (hβ : ∀ i, IntegrableOn (fun s : ℝ => β s.toNNReal ω i) (Ioc 0 t))
    (hα : ∀ i j, IntegrableOn (fun s : ℝ => α s.toNNReal ω i j) (Ioc 0 t)) :
    IntegrableOn (fun s : ℝ => itoDrift φ (Y s.toNNReal ω) s.toNNReal (β s.toNNReal ω)
      (α s.toNNReal ω)) (Ioc 0 t) := by
  unfold itoDrift
  refine ((continuous_partialTime_path hU hφ hY hYU).continuousOn.integrableOn_compact
    isCompact_Icc |>.mono_set Ioc_subset_Icc_self).add
    (integrable_finsetSum _ fun i _ => ?_) |>.add ((integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => ?_).const_mul _)
  · exact integrableOn_mul_continuous (hβ i) (continuous_partialSpace_path hU hφ hY hYU i)
  · exact integrableOn_mul_continuous (hα i j) (continuous_partialSpace2_path hU hφ hY hYU i j)

/-- Paths of `itoBracket` are integrable on every `(0, t]`. -/
theorem integrableOn_itoBracket_path (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
    (hY : Continuous fun t => Y t ω) (hYU : ∀ t, Y t ω ∈ U) (t : ℝ≥0)
    (hα : ∀ i j, IntegrableOn (fun s : ℝ => α s.toNNReal ω i j) (Ioc 0 t)) :
    IntegrableOn (fun s : ℝ => itoBracket φ (Y s.toNNReal ω) s.toNNReal (α s.toNNReal ω))
      (Ioc 0 t) := by
  unfold itoBracket
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  exact integrableOn_mul_continuous (integrableOn_mul_continuous (hα i j)
    (continuous_partialSpace_path hU hφ hY hYU i)) (continuous_partialSpace_path hU hφ hY hYU j)

/-- One bound for the partial derivatives on a compact subset of `univ ×ˢ U`. -/
theorem exists_partial_bound (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ (univ ×ˢ U))
    {Kc : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact Kc) (hKU : Kc ⊆ univ ×ˢ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Kc, |partialTime φ p| ≤ M ∧ (∀ i, |partialSpace φ p i| ≤ M) ∧
      ∀ i j, |partialSpace2 φ p i j| ≤ M := by
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ φ)
    ((continuousOn_fderiv_U hU hφ).mono hKU)
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ φ))
    ((continuousOn_fderiv2_U hU hφ).mono hKU)
  have hv0 : ‖((1 : ℝ), (0 : Fin d → ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hvi : ∀ i : Fin d, ‖((0 : ℝ), (Pi.single i 1 : Fin d → ℝ))‖ ≤ 1 := fun i => by
    rw [Prod.norm_def, norm_zero]
    exact max_le zero_le_one (norm_ev_le i)
  refine ⟨max M₁ M₂ ⊔ 0, le_sup_right, fun p hp => ⟨?_, fun i => ?_, fun i j => ?_⟩⟩
  · rw [← Real.norm_eq_abs, partialTime]
    refine ((fderiv ℝ φ p).le_opNorm _).trans ?_
    calc ‖fderiv ℝ φ p‖ * ‖((1 : ℝ), (0 : Fin d → ℝ))‖ ≤ M₁ * 1 :=
          mul_le_mul (hM₁ p hp) hv0 (norm_nonneg _) ((norm_nonneg _).trans (hM₁ p hp))
      _ ≤ _ := by rw [mul_one]; exact (le_max_left _ _).trans le_sup_left
  · rw [← Real.norm_eq_abs, partialSpace]
    refine ((fderiv ℝ φ p).le_opNorm _).trans ?_
    calc ‖fderiv ℝ φ p‖ * ‖((0 : ℝ), (Pi.single i 1 : Fin d → ℝ))‖ ≤ M₁ * 1 :=
          mul_le_mul (hM₁ p hp) (hvi i) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ p hp))
      _ ≤ _ := by rw [mul_one]; exact (le_max_left _ _).trans le_sup_left
  · rw [← Real.norm_eq_abs, partialSpace2]
    refine ((fderiv ℝ (fderiv ℝ φ) p _).le_opNorm _).trans ?_
    have h1 := (fderiv ℝ (fderiv ℝ φ) p).le_opNorm ((0 : ℝ), (Pi.single i 1 : Fin d → ℝ))
    have h2 : ‖fderiv ℝ (fderiv ℝ φ) p‖ * ‖((0 : ℝ), (Pi.single i 1 : Fin d → ℝ))‖ ≤ M₂ :=
      (mul_le_mul (hM₂ p hp) (hvi i) (norm_nonneg _) ((norm_nonneg _).trans (hM₂ p hp))).trans
        (by rw [mul_one])
    calc ‖fderiv ℝ (fderiv ℝ φ) p (0, Pi.single i 1)‖ *
          ‖((0 : ℝ), (Pi.single j 1 : Fin d → ℝ))‖ ≤ M₂ * 1 :=
          mul_le_mul (h1.trans h2) (hvi j) (norm_nonneg _) ((norm_nonneg _).trans (h1.trans h2))
      _ ≤ _ := by rw [mul_one]; exact (le_max_right _ _).trans le_sup_left

/-- `|itoDrift| ≤ M (1 + Σ|b_i| + Σ|a_ij|)` on the compact. -/
theorem abs_itoDrift_le {M : ℝ} (hM0 : 0 ≤ M) {y : Fin d → ℝ} {t : ℝ≥0} {b : Fin d → ℝ}
    {a : Fin d → Fin d → ℝ}
    (hM : |partialTime φ ((t : ℝ), y)| ≤ M ∧ (∀ i, |partialSpace φ ((t : ℝ), y) i| ≤ M) ∧
      ∀ i j, |partialSpace2 φ ((t : ℝ), y) i j| ≤ M) :
    |itoDrift φ y t b a| ≤ M * (1 + (∑ i, |b i| + ∑ i, ∑ j, |a i j|)) := by
  obtain ⟨h0, h1, h2⟩ := hM
  unfold itoDrift
  have s1 : |∑ i, b i * partialSpace φ ((t : ℝ), y) i| ≤ M * ∑ i, |b i| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (h1 i) (abs_nonneg _)
  have s2 : |∑ i, ∑ j, a i j * partialSpace2 φ ((t : ℝ), y) i j| ≤ M * ∑ i, ∑ j, |a i j| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (h2 i j) (abs_nonneg _)
  have hb : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha : 0 ≤ ∑ i, ∑ j, |a i j| := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have e := abs_add_le (partialTime φ ((t : ℝ), y) + ∑ i, b i * partialSpace φ ((t : ℝ), y) i)
    ((1 / 2 : ℝ) * ∑ i, ∑ j, a i j * partialSpace2 φ ((t : ℝ), y) i j)
  have e2 := abs_add_le (partialTime φ ((t : ℝ), y)) (∑ i, b i * partialSpace φ ((t : ℝ), y) i)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at e
  nlinarith

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
