module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Interface
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import BlockBand.Native.PSSS.BlockBand.Analysis.PoissonLayerCake
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

namespace PSSSNative.BlockBand

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

universe u

/-- The positive scalar Poisson kernel centered at `e`. -/
def centeredPoissonKernel (e η x : ℝ) : ℝ :=
  η / ((x - e) ^ 2 + η ^ 2)

theorem centeredPoissonKernel_nonneg
    {e η x : ℝ} (hη : 0 < η) :
    0 ≤ centeredPoissonKernel e η x := by
  unfold centeredPoissonKernel
  positivity

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

end PSSSNative.BlockBand
