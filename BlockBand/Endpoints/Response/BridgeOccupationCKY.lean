module

public import BlockBand.Endpoints.Response.BridgeOccupationProofCK
public import BlockBand.Endpoints.Response.LifetimeBridgeSpherePos

/-!
# The spherical corner Chapman–Kolmogorov identity

This file proves `LbkCornerCKY`, the Chapman–Kolmogorov identity for the spherical factor of the
base kernel at the corner, and combines it with the hyperbolic factor to obtain the bridge-occupation
statement.

Both factors of the integrand are nonnegative (`lbkSphereKernelPos_holds`), so the lower integral is
`ofReal` of the Bochner integral of the product, which vanishes off `[0,1]` and is continuous on
`[0,1]`; on `[0,1]` it equals `∫₀¹ k_s(y,w) k_{T-s}(w,0) dw = k_T(y,0)` by the Chapman–Kolmogorov
identity `lbkp_chapman` (Legendre orthogonality and a termwise interchange).

## Main results

* `lbkCornerCKY_holds`: the spherical corner identity for every `D₀ > 0`.
* `bridgeOccupationMeas_of_kernelBoundsX`: `BridgeOccupationMeasStatement` from
  `LbkBaseTransitionLaw`, the hyperbolic factor `LbkCornerCKX` (the semigroup property of McKean's
  kernel on `H²`, radialised, at the pole) and the two hyperbolic bridge-mean bounds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set
open scoped ENNReal

/-- The spherical bridge integrand as an indicator of a continuous function on `[0,1]`. -/
theorem bocky_integrand_eq {D0 s u y : ℝ} (hs : 0 < s) (hu : 0 < u) (hy : y ∈ Icc (0 : ℝ) 1) :
    (fun w => lbkKernelY D0 s y w * lbkKernelY D0 u w 0) =
      (Icc (0 : ℝ) 1).indicator (fun w => lbkSphereSeries D0 s y w * lbkSphereSeries D0 u w 0) := by
  funext w
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  by_cases hw : w ∈ Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hw, lbk_kernelY_eq hs hy hw, lbk_kernelY_eq hu hw h0]
  · rw [Set.indicator_of_notMem hw]
    simp [lbkKernelY, hw]

theorem bocky_continuousOn {D0 s u y : ℝ} (hD0 : 0 < D0) (hs : 0 < s) (hu : 0 < u)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun w => lbkSphereSeries D0 s y w * lbkSphereSeries D0 u w 0) (Icc 0 1) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h2 : ContinuousOn (fun w => lbkSphereSeries D0 u w 0) (Icc 0 1) :=
    (lbk_sphereSeries_continuousOn hD0 hu h0).congr fun w _ => lbkp_series_symm D0 u w 0
  exact (lbk_sphereSeries_continuousOn hD0 hs hy).mul h2

/-- The spherical corner Chapman–Kolmogorov identity holds for every `D₀ > 0`. -/
theorem lbkCornerCKY_holds (D0 : ℝ) (hD0 : 0 < D0) : LbkCornerCKY D0 := by
  intro T s hs hsT y hy
  have hu : 0 < T - s := sub_pos.2 hsT
  have hpos := lbkSphereKernelPos_holds D0 hD0
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hnn : ∀ w, 0 ≤ lbkKernelY D0 s y w * lbkKernelY D0 (T - s) w 0 := fun w =>
    mul_nonneg (lbk_kernelY_nonneg hpos _ _ _) (lbk_kernelY_nonneg hpos _ _ _)
  have hint : Integrable (fun w => lbkKernelY D0 s y w * lbkKernelY D0 (T - s) w 0) := by
    rw [bocky_integrand_eq hs hu hy]
    exact (bocky_continuousOn hD0 hs hu hy).integrableOn_Icc.integrable_indicator
      measurableSet_Icc
  have hlhs : bopYMass D0 y T s =
      ∫⁻ w, ENNReal.ofReal (lbkKernelY D0 s y w * lbkKernelY D0 (T - s) w 0) := by
    unfold bopYMass
    refine lintegral_congr fun w => ?_
    rw [ENNReal.ofReal_mul (lbk_kernelY_nonneg hpos _ _ _)]
  rw [hlhs, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)]
  congr 1
  rw [bocky_integrand_eq hs hu hy, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← lbkp_chapman hD0 hs hu hy h0, add_sub_cancel, lbk_kernelY_eq (hs.trans hsT) hy h0]

/-- The corner Chapman–Kolmogorov identity from its hyperbolic factor alone. -/
theorem lbkCornerCK_of_CKX {D0 : ℝ} (hD0 : 0 < D0) (hX : LbkCornerCKX D0) :
    LbkCornerChapmanKolmogorov D0 :=
  lbkCornerCK_of_factors hD0 hX (lbkCornerCKY_holds D0 hD0)

/-- The bridge-occupation lemma (measurable form) from the transition law, the hyperbolic factor
`LbkCornerCKX` and the two hyperbolic bridge-mean bounds; sphere positivity and the spherical corner
identity are proved. -/
theorem bridgeOccupationMeas_of_kernelBoundsX
    (hbase : ∀ D0 : ℝ, 0 < D0 → LbkBaseTransitionLaw D0 ∧ LbkCornerCKX D0)
    (hL : LbkHypBridgeMeanLower) (hU : LbkHypBridgeMeanUpper) : BridgeOccupationMeasStatement :=
  bridgeOccupationMeas_of_factorBounds (fun D0 hD0 =>
    ⟨lbkSphereKernelPos_holds D0 hD0, (hbase D0 hD0).1, (hbase D0 hD0).2,
      lbkCornerCKY_holds D0 hD0⟩) hL hU

end BlockBand.Endpoints
