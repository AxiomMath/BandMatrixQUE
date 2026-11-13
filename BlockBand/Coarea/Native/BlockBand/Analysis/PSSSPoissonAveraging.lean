module

public import BlockBand.Coarea.Native.BlockBand.Analysis.ExpectedSpectralMeasure
public import BlockBand.Coarea.Native.BlockBand.Analysis.PoissonLayerCake
public import BlockBand.Coarea.Native.BlockBand.Counting.ProjectedWegner
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Sharp PSSS Poisson averaging

This module turns the order-one PSSS closed-interval count bound into the
sharp one-block Poisson-kernel estimate.  The proof uses the radial layer-cake
identity and Tonelli; the numerical radial moment is exactly `π`.  The result
is uniform in the energy, regulator, block dimensions, and deterministic
Hermitian deformation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

universe u

/-- The positive scalar Poisson kernel centered at `e`. -/
def centeredPoissonKernel (e η x : ℝ) : ℝ :=
  η / ((x - e) ^ 2 + η ^ 2)

/-- The finite eigenvalue sum whose expectation is controlled by PSSS. -/
def BlockGUE.poissonEigenvalueSum
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e η : ℝ) (ω : M.Ω) : ℝ :=
  ∑ i : Fin (Fintype.card (BlockGUE.Index d)),
    centeredPoissonKernel e η
      (orderedEigenvalue (BlockGUE.deformed M A₀ ω) i)

theorem centeredPoissonKernel_nonneg
    {e η x : ℝ} (hη : 0 < η) :
    0 ≤ centeredPoissonKernel e η x := by
  unfold centeredPoissonKernel
  positivity

private theorem measurable_centeredPoissonKernel (e η : ℝ) :
    Measurable (centeredPoissonKernel e η) := by
  unfold centeredPoissonKernel
  fun_prop

private theorem lintegral_poissonRadialWeight_Ioi_abs
    {η x : ℝ} (hη : 0 < η) :
    (∫⁻ r : ℝ in Ioi |x|, ENNReal.ofReal (poissonRadialWeight η r)) =
      ENNReal.ofReal (η / (x ^ 2 + η ^ 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_poissonRadialWeight_Ioi hη (abs_nonneg x))]
  · rw [integral_poissonRadialWeight_Ioi_abs hη]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := (abs_nonneg x).trans_lt hr
    unfold poissonRadialWeight
    positivity

private theorem lintegral_radial_indicator
    {η x : ℝ} (hη : 0 < η) :
    (∫⁻ r : ℝ in Ioi 0,
      (Ioi |x|).indicator
        (fun r => ENNReal.ofReal (poissonRadialWeight η r)) r) =
      ENNReal.ofReal (η / (x ^ 2 + η ^ 2)) := by
  rw [setLIntegral_indicator measurableSet_Ioi]
  have hinter : Ioi |x| ∩ Ioi 0 = Ioi |x| := by
    ext r
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, (abs_nonneg x).trans_lt h⟩
  rw [hinter]
  exact lintegral_poissonRadialWeight_Ioi_abs hη

/-- Sharp layer-cake estimate for a measure satisfying the PSSS linear bound
on all centered closed intervals. -/
theorem lintegral_centeredPoissonKernel_le_of_Icc
    (ν : Measure ℝ) [SFinite ν] (e η K : ℝ) (hη : 0 < η) (hK : 0 ≤ K)
    (hIcc : ∀ r : ℝ, 0 ≤ r →
      ν (Icc (e - r) (e + r)) ≤ ENNReal.ofReal (2 * K * r)) :
    (∫⁻ x : ℝ, ENNReal.ofReal (centeredPoissonKernel e η x) ∂ν) ≤
      ENNReal.ofReal (Real.pi * K) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun x r =>
    (Ioi |x - e|).indicator
      (fun r => ENNReal.ofReal (poissonRadialWeight η r)) r
  have hF : Measurable (Function.uncurry F) := by
    have hw : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (poissonRadialWeight η p.2)) := by
      unfold poissonRadialWeight
      fun_prop
    apply hw.indicator
    change MeasurableSet {p : ℝ × ℝ | |p.1 - e| < p.2}
    exact measurableSet_lt
      ((measurable_fst.sub measurable_const).norm) measurable_snd
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal (centeredPoissonKernel e η x) ∂ν) =
        ∫⁻ x : ℝ, (∫⁻ r : ℝ in Ioi 0, F x r) ∂ν := by
          apply lintegral_congr
          intro x
          unfold centeredPoissonKernel F
          simpa [abs_sub_comm] using
            (lintegral_radial_indicator (η := η) (x := x - e) hη).symm
    _ = ∫⁻ r : ℝ in Ioi 0, ∫⁻ x : ℝ, F x r ∂ν := by
          exact lintegral_lintegral_swap
            (μ := ν) (ν := volume.restrict (Ioi 0)) hF.aemeasurable
    _ ≤ ∫⁻ r : ℝ in Ioi 0,
        ENNReal.ofReal (poissonRadialWeight η r) *
          ENNReal.ofReal (2 * K * r) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          have hr0 : 0 ≤ r := hr.le
          calc
            (∫⁻ x : ℝ, F x r ∂ν) =
                ENNReal.ofReal (poissonRadialWeight η r) *
                  ν (Ioo (e - r) (e + r)) := by
                    have hfun : (fun x => F x r) =
                        (Ioo (e - r) (e + r)).indicator
                          (fun _ => ENNReal.ofReal
                            (poissonRadialWeight η r)) := by
                      funext x
                      have hmem :
                          r ∈ Ioi |x - e| ↔ x ∈ Ioo (e - r) (e + r) := by
                        simp only [mem_Ioi, mem_Ioo, abs_lt]
                        constructor <;> intro h
                        · constructor <;> linarith [h.1, h.2]
                        · constructor <;> linarith [h.1, h.2]
                      simp only [F, Set.indicator, hmem]
                    rw [hfun, lintegral_indicator measurableSet_Ioo,
                      setLIntegral_const]
            _ ≤ ENNReal.ofReal (poissonRadialWeight η r) *
                  ν (Icc (e - r) (e + r)) := by
                    gcongr
                    exact Ioo_subset_Icc_self
            _ ≤ ENNReal.ofReal (poissonRadialWeight η r) *
                  ENNReal.ofReal (2 * K * r) := by
                    gcongr
                    exact hIcc r hr0
    _ = ENNReal.ofReal (Real.pi * K) := by
          rw [show (∫⁻ r : ℝ in Ioi 0,
              ENNReal.ofReal (poissonRadialWeight η r) *
                ENNReal.ofReal (2 * K * r)) =
              ∫⁻ r : ℝ in Ioi 0,
                ENNReal.ofReal
                  (K * ((2 * r) * poissonRadialWeight η r)) by
            apply setLIntegral_congr_fun measurableSet_Ioi
            intro r hr
            have hr0 : 0 ≤ r := hr.le
            have hw : 0 ≤ poissonRadialWeight η r := by
              unfold poissonRadialWeight
              positivity
            dsimp only
            rw [← ENNReal.ofReal_mul hw]
            congr 1
            ring]
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · rw [integral_const_mul,
              integral_mul_poissonRadialWeight_Ioi hη]
            congr 1
            ring
          · exact
              (integrableOn_mul_poissonRadialWeight_Ioi hη).const_mul K
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
            have hr0 : 0 ≤ r := hr.le
            unfold poissonRadialWeight
            positivity

/-- The order-one PSSS interval theorem gives both integrability and
the sharp expected Poisson-eigenvalue-sum bound `π C dim`. -/
theorem psss_poissonEigenvalueSum_integrable_and_integral_le
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (BlockGUE.poissonEigenvalueSum M A₀ e η) M.P ∧
      ∫ ω, BlockGUE.poissonEigenvalueSum M A₀ e η ω ∂M.P ≤
        Real.pi * input.C * (Fintype.card (BlockGUE.Index d) : ℝ) := by
  let N : ℝ := input.C * (Fintype.card (BlockGUE.Index d) : ℝ)
  have hN : 0 ≤ N := mul_nonneg input.C_nonneg (Nat.cast_nonneg _)
  let ν := BlockGUE.expectedSpectralMeasure M A₀
  have hνIcc (r : ℝ) (hr : 0 ≤ r) :
      ν (Icc (e - r) (e + r)) ≤ ENNReal.ofReal (2 * N * r) := by
    have h := psss_expectedSpectralMeasure_Icc_le input hd M A₀
      (e - r) (e + r) (by linarith)
    simpa only [ν, N] using (show
      ENNReal.ofReal
          (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
            (e + r - (e - r))) =
        ENNReal.ofReal
          (2 * (input.C * (Fintype.card (BlockGUE.Index d) : ℝ)) * r) by
      congr 1
      ring) ▸ h
  let _ : IsFiniteMeasure ν := by
    unfold ν BlockGUE.expectedSpectralMeasure
    infer_instance
  have hkernel :
      (∫⁻ x : ℝ, ENNReal.ofReal (centeredPoissonKernel e η x) ∂ν) ≤
        ENNReal.ofReal (Real.pi * N) :=
    lintegral_centeredPoissonKernel_le_of_Icc ν e η N hη hN hνIcc
  have hmeasDef : Measurable (fun ω => BlockGUE.deformed M A₀ ω) := by
    apply Measurable.subtype_mk
    rw [Matrix.measurable_iff]
    intro x y
    exact measurable_const.add (M.measurable_entry x y)
  have hmeas :
      Measurable (BlockGUE.poissonEigenvalueSum M A₀ e η) := by
    unfold BlockGUE.poissonEigenvalueSum
    apply Finset.measurable_sum
    intro i _hi
    exact (measurable_centeredPoissonKernel e η).comp
      ((measurable_orderedEigenvalue i).comp hmeasDef)
  have hnonneg :
      0 ≤ᵐ[M.P] BlockGUE.poissonEigenvalueSum M A₀ e η :=
    Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun i _hi =>
      centeredPoissonKernel_nonneg hη
  have hlin :
      (∫⁻ ω, ENNReal.ofReal
        (BlockGUE.poissonEigenvalueSum M A₀ e η ω) ∂M.P) ≤
          ENNReal.ofReal (Real.pi * N) := by
    rw [show (∫⁻ ω, ENNReal.ofReal
        (BlockGUE.poissonEigenvalueSum M A₀ e η ω) ∂M.P) =
        ∫⁻ ω, ∑ i : Fin (Fintype.card (BlockGUE.Index d)),
          ENNReal.ofReal (centeredPoissonKernel e η
            (orderedEigenvalue (BlockGUE.deformed M A₀ ω) i)) ∂M.P by
      apply lintegral_congr
      intro ω
      rw [BlockGUE.poissonEigenvalueSum, ENNReal.ofReal_sum_of_nonneg]
      intro i _hi
      exact centeredPoissonKernel_nonneg hη]
    rw [← BlockGUE.lintegral_expectedSpectralMeasure M A₀
      (fun x => ENNReal.ofReal (centeredPoissonKernel e η x))
      (measurable_centeredPoissonKernel e η).ennreal_ofReal]
    exact hkernel
  have hint : Integrable (BlockGUE.poissonEigenvalueSum M A₀ e η) M.P := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hmeas.aestronglyMeasurable hnonneg).mp
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg
    hmeas.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal
  · exact mul_nonneg (mul_nonneg Real.pi_nonneg input.C_nonneg)
      (Nat.cast_nonneg _)
  · simpa only [N, mul_assoc] using hlin

/-- Integrability of the PSSS Poisson eigenvalue sum. -/
theorem psss_poissonEigenvalueSum_integrable
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (BlockGUE.poissonEigenvalueSum M A₀ e η) M.P :=
  (psss_poissonEigenvalueSum_integrable_and_integral_le
    input hd M A₀ e hη).1

/-- Sharp expected Poisson-eigenvalue-sum bound `π C dim`. -/
theorem psss_poissonEigenvalueSum_integral_le
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ ω, BlockGUE.poissonEigenvalueSum M A₀ e η ω ∂M.P ≤
      Real.pi * input.C * (Fintype.card (BlockGUE.Index d) : ℝ) :=
  (psss_poissonEigenvalueSum_integrable_and_integral_le
    input hd M A₀ e hη).2

/-- The sharp PSSS Poisson estimate constructs the explicit one-block
averaging object used by the finite-block projected-Wegner summation lemma.
The singleton index records that this theorem is the conditioned one-block
step; no conditional-independence assertion is hidden here. -/
theorem psss_singleBlockAveraging
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e : ℝ) {η : ℝ} (hη : 0 < η) :
    SingleBlockAveraging M.P
      (fun (_j : Fin 1) => BlockGUE.poissonEigenvalueSum M A₀ e η)
      input.C (Fintype.card (BlockGUE.Index d) : ℝ) where
  integrable := fun _j =>
    psss_poissonEigenvalueSum_integrable input hd M A₀ e hη
  nonneg := fun _j =>
    Filter.Eventually.of_forall fun _ω => Finset.sum_nonneg fun _i _hi =>
      centeredPoissonKernel_nonneg hη
  oneBlock := fun _j =>
    psss_poissonEigenvalueSum_integral_le input hd M A₀ e hη

end CoareaNative.BlockBand
