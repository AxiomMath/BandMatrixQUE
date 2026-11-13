module

public import BlockBand.Endpoints.Response.BridgeOccupationProof
public import BlockBand.Endpoints.Response.NonzeroResponse

/-!
# Nonzero response from the measurable bridge-occupation statement

`nonzeroResponse` takes `LifetimeBridgeStatement` and `BridgeOccupationStatement`, which are jointly
inconsistent (`not_bridgeOccupationStatement_of_lifetimeBridge`). Its proof only applies the
occupation bounds to the witness `p` of `LifetimeBridgeStatement`, which is jointly measurable
(`hpm`). `nonzeroResponse_of_occMeas` is the same proof with `BridgeOccupationStatement` replaced by
`BridgeOccupationMeasStatement` (one extra argument `hpm` at the single use).
`nonzeroResponse_of_kernelBounds` composes it with `bridgeOccupationMeas_of_kernelBounds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- From the `DualBoundaryStartContract`,
`LifetimeBridgeStatement` and the repaired `BridgeOccupationMeasStatement` (the committed proof
of `nonzeroResponse`, with the measurability `hpm` of the lifetime-bridge witness passed to the
occupation bounds).
-/
theorem nonzeroResponse_of_occMeas (hBdry : DualBoundaryStartContract)
    (hLB : LifetimeBridgeStatement) (hOcc : BridgeOccupationMeasStatement) :
    NonzeroResponseStatement := by
  intro D0 hD0 τ hτ m hm
  obtain ⟨p, hpd, hpm, -, hstart⟩ := hLB D0 hD0
  obtain ⟨c, hc, C, hC, r₁, hO'⟩ := hOcc (D0 * τ) (mul_pos hD0 hτ)
  have hO := hO' D0 τ hD0 hτ rfl
  have hm' : 0 < |(m : ℝ)| := abs_pos.2 (by exact_mod_cast hm)
  have hm1 : 1 ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm
  set δ := τ / (6 * |(m : ℝ)|) with hδdef
  have hδ : 0 < δ := by positivity
  have hδτ : δ < τ := by
    rw [hδdef, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨r₀, hr₁, hr₀1, hsmall⟩ := nzr_choose_radius (C := C) hδ hτ r₁
  set x := (Real.cosh r₀ - 1) / 2 with hxdef
  have hx : 0 < x := by
    have := Real.one_lt_cosh.2 (show r₀ ≠ 0 by linarith)
    rw [hxdef]; linarith
  have hds : IsDualStart ![x] ![0] :=
    isDualStart_one hx.le le_rfl zero_le_one (fun h => hx.ne' h.1)
  obtain ⟨hpos, -, hdis⟩ := hstart x 0 hds
  set q := rvCosineTest τ m
  have hq := rvCosineTest_continuous τ m
  have hq1 := rvCosineTest_abs_le τ m
  have hqδ : ∀ s ∈ Ioc 0 δ, 1 / 2 ≤ q s := fun s hs => nzr_cos_ge_half hτ hm hs.1.le hs.2
  set ε := C * (Real.exp (-(δ * r₀ / τ)) + r₀ * Real.exp (-r₀))
  have hε0 : 0 ≤ ε := mul_nonneg hC (by positivity)
  have hz : bridgeStart r₀ = (x, 0) := rfl
  -- a realization, and the representation
  obtain ⟨Ω, mΩ, 𝓖, P, N, X, Y, hR⟩ := hBdry.exists_ D0 hD0 x 0 hds
  have hrep := nzr_response_eq hτ hq hq1 hpm hBdry hD0 hds hR (hdis Ω mΩ 𝓖 P N X Y hR).2
  have hKp : nzr_kernelPart D0 τ p (x, 0) (nzr_pos q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrep.1
  have hKm : nzr_kernelPart D0 τ p (x, 0) (nzr_neg q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrep.2.1
  -- strict comparison of the kernel parts
  have hlt : nzr_kernelPart D0 τ p (x, 0) (nzr_neg q) <
      nzr_kernelPart D0 τ p (x, 0) (nzr_pos q) := by
    have hpt : ∀ t ∈ Ioc 0 τ, nzr_inner τ p (x, 0) (nzr_neg q) t <
        nzr_inner τ p (x, 0) (nzr_pos q) t := by
      intro t ht
      obtain ⟨hfin, hlow, hlate⟩ := hO p hpd hpm r₀ hr₁ t ht
      rw [hz] at hfin hlow hlate
      have hpos' : 0 < bridgeOccupation p (x, 0) t 0 t := by
        refine lt_of_lt_of_le ?_ hlow
        exact ENNReal.ofReal_pos.2 (by have := ht.1; positivity)
      exact nzr_inner_lt hδ hq1 hqδ ht hε0 hsmall hfin hpos' (hlate δ ⟨hδ, hδτ⟩)
    have hρ : ∀ t ∈ Ioc 0 τ, nzr_cut τ t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, 0) t) ≠ 0 ∧
        nzr_cut τ t * ENNReal.ofReal (cornerLifetimeDensity D0 p (x, 0) t) ≠ ⊤ := by
      intro t ht
      have hcut : nzr_cut τ t = 1 := by
        unfold nzr_cut; rw [indicator_of_mem (show t ∈ Iic τ from ht.2)]
      rw [hcut, one_mul]
      refine ⟨(ENNReal.ofReal_pos.2 ?_).ne', ENNReal.ofReal_ne_top⟩
      unfold cornerLifetimeDensity
      have := hpos t ht.1
      simp only [add_zero]
      positivity
    unfold nzr_kernelPart
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (s := Ioc 0 τ) ?_ hKm ?_ ?_ ?_
    · exact (((nzr_cut_measurable τ).mul (nzr_rho_measurable hpm D0 (x, 0))).mul
        (nzr_inner_measurable hpm τ (x, 0) (nzr_pos_continuous hq).measurable)).aemeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
      by_cases htτ : t ≤ τ
      · have h := hρ t ⟨ht0, htτ⟩
        exact ((ENNReal.mul_lt_mul_iff_right h.1 h.2).2 (hpt t ⟨ht0, htτ⟩)).le
      · have hcut : nzr_cut τ t = 0 := by
          unfold nzr_cut; rw [indicator_of_notMem (show t ∉ Iic τ from htτ)]
        simp [hcut]
    · rw [Measure.restrict_apply measurableSet_Ioc,
        inter_eq_left.2 Ioc_subset_Ioi_self, Real.volume_Ioc]
      exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
    · exact ae_of_all _ fun t ht => by
        have h := hρ t ht
        exact (ENNReal.mul_lt_mul_iff_right h.1 h.2).2 (hpt t ht)
  refine ⟨x, hx, _, (ENNReal.toReal_lt_toReal hKm hKp).2 hlt |> sub_pos.2, ?_⟩
  refine Or.inr ⟨fun h => hx.ne' h.1, ⟨Ω, mΩ, 𝓖, P, N, X, Y, hR⟩, ?_⟩
  intro Ω' m' 𝓖' P' N' X' Y' hR'
  exact (nzr_response_eq hτ hq hq1 hpm hBdry hD0 hds hR' (hdis Ω' m' 𝓖' P' N' X' Y' hR').2).2.2

/-- The nonzero-response proposition from `DualBoundaryStartContract`, `LifetimeBridgeStatement`
and the analytic inputs of the bridge-occupation lemma. -/
theorem nonzeroResponse_of_kernelBounds (hBdry : DualBoundaryStartContract)
    (hLB : LifetimeBridgeStatement)
    (hbase : ∀ D0 : ℝ, 0 < D0 →
      LbkSphereKernelPos D0 ∧ LbkBaseTransitionLaw D0 ∧ LbkCornerChapmanKolmogorov D0)
    (hL : LbkHypBridgeMeanLower) (hU : LbkHypBridgeMeanUpper) : NonzeroResponseStatement :=
  nonzeroResponse_of_occMeas hBdry hLB (bridgeOccupationMeas_of_kernelBounds hbase hL hU)

end BlockBand.Endpoints
