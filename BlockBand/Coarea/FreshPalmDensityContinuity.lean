module

public import BlockBand.Coarea.FreshPalmDensityBound
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalActualPairGoodEventReadback

/-!
# Continuity in the energy of the fresh eigenpair fiber density

*Measures.* `ν_N = projectiveHaar (Fin N)`, `GUE_{N-1}(t) = gueMeasure (Fin (N-1)) t`.
*Domain.* `N ≥ 1`, Hermitian `F`, any `t : ℝ≥0`, any zero-based rank `ℓ`, measurable frame
`U` (`IsFreshFrame`), measurable `φ ≥ 0` of `v` bounded by a finite constant. Exact; the
statement is continuity of `E ↦ freshEigenpairFiber F t ℓ U E (fun v _ => φ v)` on `ℝ`.

The `E`-integrand `c_{N,t} 𝓡(E,v,F) |det M_E|² 1{N_-(M_E) = ℓ}` is continuous in `E` for
Hermitian `G'`: where `det M_E ≠ 0` the inertia `N_-(M_E)` is locally constant (no
eigenvalue of `U*FU + G'` crosses `E`), and where `det M_E = 0` the weight `|det M_E|²`
vanishes. Domination on `|E - E₀| < 1`: `𝓡 ≤ 1`, `|det M_E|² ≤ ((N-1)! xᴺ⁻¹)²` with
`x = Σ|F| + Σ|G'| + |E₀| + 1`, whose `GUE_{N-1}` moments are finite.

* `eventually_negativeCount_eq`: local constancy of `N_-(B - E)` off the spectrum.
* `fiberKernel`, `measurable_fiberKernel`, `tendsto_fiberKernel`, `fiberKernel_le`.
* **`continuous_freshEigenpairFiber`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FreshPalm

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw BlockBand.Coarea.FixedOmega
  BlockBand.Coarea.ClockRank
open CoareaNative.BlockBand (negativeEigenvalueCount)
open scoped ENNReal NNReal ComplexConjugate

section Inertia

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem negativeCount_sub_eq_eigenCount {B : Matrix n n ℂ} (hB : B.IsHermitian) (E : ℝ) :
    negativeCount (B - (E : ℂ) • 1) =
      CoareaNative.BlockBand.eigenCount (⟨B, hB⟩ : CoareaNative.BlockBand.HermitianMatrix n)
        (Set.Iio E) := by
  rw [negativeCount_eq (shift_isHermitian hB E)]
  exact CoareaNative.BlockBand.negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
    ⟨B, hB⟩ E

/-- `N_-(B - E)` is locally constant in `E` off the spectrum of `B`. -/
theorem eventually_negativeCount_eq {B : Matrix n n ℂ} (hB : B.IsHermitian) {E₀ : ℝ}
    (hdet : (B - (E₀ : ℂ) • 1).det ≠ 0) :
    ∀ᶠ E : ℝ in 𝓝 E₀, negativeCount (B - (E : ℂ) • 1) = negativeCount (B - (E₀ : ℂ) • 1) := by
  classical
  set A : CoareaNative.BlockBand.HermitianMatrix n := ⟨B, hB⟩
  have hne : ∀ s, CoareaNative.BlockBand.orderedEigenvalue A s ≠ E₀ := by
    intro s hs
    exact hdet ((CoareaNative.BlockBand.GaussianRing.det_sub_real_smul_one_eq_zero_iff A E₀).2 ⟨s, hs⟩)
  have hev : ∀ᶠ E : ℝ in 𝓝 E₀, ∀ s, (CoareaNative.BlockBand.orderedEigenvalue A s < E ↔
      CoareaNative.BlockBand.orderedEigenvalue A s < E₀) := by
    rw [Filter.eventually_all]
    intro s
    rcases lt_or_gt_of_ne (hne s) with h | h
    · filter_upwards [Ioi_mem_nhds h] with E hE
      exact ⟨fun _ => h, fun _ => hE⟩
    · filter_upwards [Iio_mem_nhds h] with E hE
      exact ⟨fun h' => (lt_irrefl _ (h'.trans hE)).elim, fun h' => (lt_asymm h' h).elim⟩
  filter_upwards [hev] with E hE
  rw [negativeCount_sub_eq_eigenCount hB, negativeCount_sub_eq_eigenCount hB,
    CoareaNative.BlockBand.eigenCount_def, CoareaNative.BlockBand.eigenCount_def]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iio]
  exact hE s

end Inertia

variable {N : ℕ}

/-- The `G'`-integrand of `freshEigenpairFiber` without its observable. -/
def fiberKernel (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ℓ : Fin N) (E : ℝ) (v : Fin N → ℂ)
    (G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (coareaConstant N t * regressionFactor t E v F *
      Complex.normSq (freshFrameM U F E v G').det) *
    (if negativeCount (freshFrameM U F E v G') = ℓ.val then 1 else 0)

theorem freshEigenpairFiber_eq (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ℓ : Fin N)
    (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ) (E : ℝ) (φ : (Fin N → ℂ) → ℝ≥0∞) :
    freshEigenpairFiber F t ℓ U E (fun v _ => φ v) =
      ∫⁻ v, ∫⁻ G', fiberKernel U F t ℓ E v G' * φ v
        ∂gueMeasure (Fin (N - 1)) t ∂projectiveHaar (Fin N) := rfl

theorem continuous_l2Norm {ι : Type*} [Fintype ι] : Continuous (l2Norm (ι := ι)) := by
  unfold l2Norm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
    ((continuous_apply k).norm).pow 2)

theorem continuous_regressionFactor_v {ι : Type*} [Fintype ι] (t E : ℝ) (F : Matrix ι ι ℂ) :
    Continuous fun v : ι → ℂ => regressionFactor t E v F := by
  unfold regressionFactor
  have h1 : Continuous fun v : ι → ℂ => star v ⬝ᵥ (F *ᵥ v) :=
    (continuous_id.star).dotProduct (continuous_const.matrix_mulVec continuous_id)
  have h2 : Continuous fun v : ι → ℂ => F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v :=
    (continuous_const.matrix_mulVec continuous_id).sub (h1.smul continuous_id)
  exact Real.continuous_exp.comp ((((continuous_const.sub (Complex.continuous_re.comp h1)).pow
    2).add (continuous_const.mul ((continuous_l2Norm.comp h2).pow 2))).neg.div_const _)

theorem continuous_regressionFactor_E {ι : Type*} [Fintype ι] (t : ℝ) (v : ι → ℂ)
    (F : Matrix ι ι ℂ) : Continuous fun E : ℝ => regressionFactor t E v F := by
  unfold regressionFactor
  fun_prop

theorem measurable_freshFrameM {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ}
    (hU : Measurable U) (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) :
    Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      freshFrameM U F E p.1 p.2 := by
  have hU1 : Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ => U p.1 :=
    hU.comp measurable_fst
  have hUh : Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      (U p.1)ᴴ := CoareaNative.BlockBand.Measurable.matrix_conjTranspose hU1
  have hA : Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      (U p.1)ᴴ * F * U p.1 :=
    CoareaNative.BlockBand.measurable_matrix_mul_rect
      (CoareaNative.BlockBand.measurable_matrix_mul_rect hUh measurable_const) hU1
  unfold freshFrameM
  exact measurable_matrix_sub (measurable_matrix_add hA measurable_snd) measurable_const

theorem measurable_fiberKernel {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ}
    (hU : Measurable U) (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ℓ : Fin N) (E : ℝ) :
    Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      fiberKernel U F t ℓ E p.1 p.2 := by
  have hM := measurable_freshFrameM hU F E
  have hdet : Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      Complex.normSq (freshFrameM U F E p.1 p.2).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hR : Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      regressionFactor t E p.1 F :=
    (continuous_regressionFactor_v (t : ℝ) E F).measurable.comp measurable_fst
  have hind := measurable_indicator_negativeCount hM 0 ℓ.val
  simp only [add_zero] at hind
  unfold fiberKernel
  exact (ENNReal.measurable_ofReal.comp ((measurable_const.mul hR).mul hdet)).mul hind

/-- Continuity in `E` of the kernel at a Hermitian `G'`. -/
theorem tendsto_fiberKernel (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (t : ℝ≥0) (ℓ : Fin N) (v : Fin N → ℂ)
    {G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ} (hG' : G'.IsHermitian) (E₀ : ℝ) :
    Tendsto (fun E => fiberKernel U F t ℓ E v G') (𝓝 E₀)
      (𝓝 (fiberKernel U F t ℓ E₀ v G')) := by
  set B := (U v)ᴴ * F * U v + G'
  have hB : B.IsHermitian := (isHermitian_conjTranspose_mul_mul (U v) hF).add hG'
  have hMeq : ∀ E, freshFrameM U F E v G' = B - (E : ℂ) • 1 := fun E => rfl
  set a : ℝ → ℝ := fun E => coareaConstant N t * regressionFactor t E v F *
    Complex.normSq (B - (E : ℂ) • 1).det
  have ha : Continuous a := by
    have hdet : Continuous fun E : ℝ => (B - (E : ℂ) • 1).det :=
      (continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)).matrix_det
    exact (continuous_const.mul (continuous_regressionFactor_E _ v F)).mul
      (Complex.continuous_normSq.comp hdet)
  have hk : ∀ E, fiberKernel U F t ℓ E v G' = ENNReal.ofReal (a E) *
      (if negativeCount (B - (E : ℂ) • 1) = ℓ.val then 1 else 0) := fun E => rfl
  simp_rw [hk]
  have hoa : Tendsto (fun E => ENNReal.ofReal (a E)) (𝓝 E₀) (𝓝 (ENNReal.ofReal (a E₀))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp (ha.tendsto E₀)
  by_cases hdet : (B - (E₀ : ℂ) • 1).det = 0
  · have ha0 : a E₀ = 0 := by simp only [a]; rw [hdet]; simp
    rw [ha0, ENNReal.ofReal_zero, zero_mul]
    rw [ha0, ENNReal.ofReal_zero] at hoa
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hoa
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun E => ?_)
    split_ifs <;> simp
  · have hev := eventually_negativeCount_eq hB hdet
    refine Tendsto.congr' ?_ (ENNReal.Tendsto.mul_const hoa (Or.inr (by split_ifs <;> simp)))
    filter_upwards [hev] with E hE
    rw [hE]

/-- The domination constant on `|E - E₀| < 1`. -/
def kernelBound (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (E₀ : ℝ)
    (G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (coareaConstant N t * ((N - 1).factorial : ℝ) ^ 2) *
    ENNReal.ofReal ((entrySum F + |E₀| + 1 + entrySum G') ^ (2 * (N - 1)))

theorem fiberKernel_le (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ℓ : Fin N) {E E₀ : ℝ} (hE : |E - E₀| < 1)
    (v : Fin N → ℂ) (hUU : (U v)ᴴ * U v = 1) (G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) :
    fiberKernel U F t ℓ E v G' ≤ kernelBound F t E₀ G' := by
  set x := entrySum F + |E₀| + 1 + entrySum G'
  have hx0 : 0 ≤ x := by
    have := entrySum_nonneg F; have := entrySum_nonneg G'; positivity
  have hEx : |E| ≤ |E₀| + 1 := by
    have := abs_sub_abs_le_abs_sub E E₀; linarith
  have hentry : ∀ i j, ‖freshFrameM U F E v G' i j‖ ≤ x := fun i j =>
    (norm_frameM_apply_le U F E v G' hUU i j).trans (by simp only [x]; linarith)
  have hdet := normSq_det_le _ hentry
  rw [Fintype.card_fin] at hdet
  have hc := coareaConstant_nonneg N (t.coe_nonneg)
  have hR0 := regressionFactor_nonneg (t : ℝ) E v F
  have hR1 := regressionFactor_le_one t.coe_nonneg E v F
  unfold fiberKernel kernelBound
  rw [← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (coareaConstant N t * regressionFactor t E v F *
        Complex.normSq (freshFrameM U F E v G').det) *
        (if negativeCount (freshFrameM U F E v G') = ℓ.val then 1 else 0)
      ≤ ENNReal.ofReal (coareaConstant N t * regressionFactor t E v F *
        Complex.normSq (freshFrameM U F E v G').det) * 1 := by
        gcongr; split_ifs <;> simp
    _ ≤ _ := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        have hn := Complex.normSq_nonneg (freshFrameM U F E v G').det
        calc coareaConstant N t * regressionFactor t E v F *
              Complex.normSq (freshFrameM U F E v G').det
            ≤ coareaConstant N t * 1 * (((N - 1).factorial : ℝ) * x ^ (N - 1)) ^ 2 := by
              gcongr
          _ = _ := by ring

theorem lintegral_kernelBound_lt_top (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (E₀ : ℝ) :
    ∫⁻ G', kernelBound F t E₀ G' ∂gueMeasure (Fin (N - 1)) t < ∞ := by
  unfold kernelBound
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have ha : 0 ≤ entrySum F + |E₀| + 1 := by have := entrySum_nonneg F; positivity
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lintegral_ofReal_entrySum_pow_lt_top t ha _)

theorem measurable_kernelBound (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (E₀ : ℝ) :
    Measurable fun G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ => kernelBound F t E₀ G' := by
  unfold kernelBound
  exact measurable_const.mul (ENNReal.measurable_ofReal.comp
    ((continuous_const.add continuous_entrySum).pow _).measurable)

theorem lintegral_kernelBound_mul_ne_top (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (E₀ : ℝ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) :
    ∫⁻ G', kernelBound F t E₀ G' * C ∂gueMeasure (Fin (N - 1)) t ≠ ∞ := by
  rw [lintegral_mul_const _ (measurable_kernelBound F t E₀)]
  exact ENNReal.mul_ne_top (lintegral_kernelBound_lt_top F t E₀).ne hC

theorem eventually_abs_sub_lt_one (E₀ : ℝ) : ∀ᶠ E in 𝓝 E₀, |E - E₀| < 1 := by
  filter_upwards [Metric.ball_mem_nhds E₀ one_pos] with E hE
  rwa [Metric.mem_ball, Real.dist_eq] at hE

/-- Inner (`G'`) continuity at a fixed frame vector. -/
theorem tendsto_inner_fiber {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ}
    (hU : Measurable U) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (t : ℝ≥0)
    (ℓ : Fin N) (v : Fin N → ℂ) (hUU : (U v)ᴴ * U v = 1) (c : ℝ≥0∞) (hc : c ≠ ∞) (E₀ : ℝ) :
    Tendsto (fun E => ∫⁻ G', fiberKernel U F t ℓ E v G' * c ∂gueMeasure (Fin (N - 1)) t)
      (𝓝 E₀) (𝓝 (∫⁻ G', fiberKernel U F t ℓ E₀ v G' * c ∂gueMeasure (Fin (N - 1)) t)) := by
  have hmeas : ∀ E, Measurable fun G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      fiberKernel U F t ℓ E v G' * c := fun E =>
    ((measurable_fiberKernel hU F t ℓ E).comp (measurable_prodMk_left (x := v))).mul_const c
  refine tendsto_lintegral_filter_of_dominated_convergence
    (F := fun E G' => fiberKernel U F t ℓ E v G' * c)
    (f := fun G' => fiberKernel U F t ℓ E₀ v G' * c)
    (fun G' => kernelBound F t E₀ G' * c) (Eventually.of_forall hmeas) ?_
    (lintegral_kernelBound_mul_ne_top F t E₀ hc) ?_
  · filter_upwards [eventually_abs_sub_lt_one E₀] with E hE
    exact Eventually.of_forall fun G' =>
      mul_le_mul_left (fiberKernel_le U F t ℓ hE v hUU G') c
  · filter_upwards [ae_isHermitian_gueMeasure (ι := Fin (N - 1)) t] with G' hG'
    exact ENNReal.Tendsto.mul_const (tendsto_fiberKernel U hF t ℓ v hG' E₀) (Or.inr hc)

/-- **Continuity in `E` of the fresh fiber density** for a bounded observable of `v`. -/
theorem continuous_freshEigenpairFiber (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (t : ℝ≥0) (ℓ : Fin N)
    {U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ} (hU : IsFreshFrame U)
    {φ : (Fin N → ℂ) → ℝ≥0∞} (hφ : Measurable φ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hφC : ∀ v, φ v ≤ C) :
    Continuous fun E : ℝ => freshEigenpairFiber F t ℓ U E (fun v _ => φ v) := by
  have hne : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simp_rw [freshEigenpairFiber_eq]
  rw [continuous_iff_continuousAt]
  intro E₀
  have hjoint : ∀ E, Measurable fun p : (Fin N → ℂ) × Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ =>
      fiberKernel U F t ℓ E p.1 p.2 * φ p.1 := fun E =>
    (measurable_fiberKernel hU.1 F t ℓ E).mul (hφ.comp measurable_fst)
  refine tendsto_lintegral_filter_of_dominated_convergence
    (F := fun E v => ∫⁻ G', fiberKernel U F t ℓ E v G' * φ v ∂gueMeasure (Fin (N - 1)) t)
    (f := fun v => ∫⁻ G', fiberKernel U F t ℓ E₀ v G' * φ v ∂gueMeasure (Fin (N - 1)) t)
    (fun _ => ∫⁻ G', kernelBound F t E₀ G' * C ∂gueMeasure (Fin (N - 1)) t)
    (Eventually.of_forall fun E => (hjoint E).lintegral_prod_right') ?_ ?_ ?_
  · filter_upwards [eventually_abs_sub_lt_one E₀] with E hE
    filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (Fin N)] with v hv
    exact lintegral_mono fun G' =>
      mul_le_mul' (fiberKernel_le U F t ℓ hE v (hU.2 v hv).1 G') (hφC v)
  · rw [lintegral_const, measure_univ, mul_one]
    exact lintegral_kernelBound_mul_ne_top F t E₀ hC
  · filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (Fin N)] with v hv
    exact tendsto_inner_fiber hU.1 hF t ℓ v (hU.2 v hv).1 (φ v)
      (ne_top_of_le_ne_top hC (hφC v)) E₀

end BlockBand.Coarea.FreshPalm
