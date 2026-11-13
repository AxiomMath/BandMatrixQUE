module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedNormalizedKernel
public import BlockBand.Native.PSSS.BlockBand.Analysis.PoissonLayerCake

/-!
# Exact linear radial integration for the corrected kernel

Once the selected-block estimate contributes only the source-faithful linear
mesh factor `2 K xi`, the Poisson-radial integral is exactly `π K`.  No higher
radial moment occurs because the fixed `Icc a b` predecessor is independent of
`xi`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

/-- Exact `ℝ≥0∞` form of the remaining linear radial integral. -/
theorem lintegral_two_mul_radius_mul_poissonRadialWeight
    {eta K : ℝ} (heta : 0 < eta) (hK : 0 ≤ K) :
    (∫⁻ xi : ℝ in Set.Ioi 0,
      ENNReal.ofReal (2 * K * xi) *
        ENNReal.ofReal (poissonRadialWeight eta xi)) =
      ENNReal.ofReal (Real.pi * K) := by
  rw [show (∫⁻ xi : ℝ in Set.Ioi 0,
      ENNReal.ofReal (2 * K * xi) *
        ENNReal.ofReal (poissonRadialWeight eta xi)) =
      ∫⁻ xi : ℝ in Set.Ioi 0,
        ENNReal.ofReal (K * ((2 * xi) * poissonRadialWeight eta xi)) by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro xi hxi
    have hxi0 : 0 ≤ xi := hxi.le
    have hw : 0 ≤ poissonRadialWeight eta xi := by
      unfold poissonRadialWeight
      positivity
    change ENNReal.ofReal (2 * K * xi) *
      ENNReal.ofReal (poissonRadialWeight eta xi) =
      ENNReal.ofReal (K * ((2 * xi) * poissonRadialWeight eta xi))
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * K * xi)]
    congr 1
    ring]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, integral_mul_poissonRadialWeight_Ioi heta]
    congr 1
    ring
  · exact (integrableOn_mul_poissonRadialWeight_Ioi heta).const_mul K
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with xi hxi
    have hxi0 : 0 ≤ xi := hxi.le
    have hw : 0 ≤ poissonRadialWeight eta xi := by
      unfold poissonRadialWeight
      positivity
    positivity

end PSSSNative.BlockBand.PSSS
