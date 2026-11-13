module

public import BlockBand.Endpoints.Response.BridgeOccupationMeanPolar

/-!
# The hyperbolic bridge-mean bounds from the radial Gaussian comparison

This file derives the lower and upper hyperbolic bridge-mean bounds from the two-sided comparison
`LbkHypRadialGaussCompare` of the hyperbolic radial kernel with a conjugated planar kernel.

## Main results

* `lbkHypBridgeMeanLower_of_gaussCompare : LbkHypRadialGaussCompare → LbkHypBridgeMeanLower`,
  with `c(κ) = (c₀/C₀)²`;
* `lbkHypBridgeMeanUpper_of_gaussCompare : LbkHypRadialGaussCompare → LbkHypBridgeMeanUpper`,
  with `C(κ) = (C₀/c₀)² e^{2κ}`;
  here `c₀, C₀` are the comparison constants of `LbkHypRadialGaussCompare` on `(0, κ/2]`.
* `bridgeOccupationMeas_of_baseCKX`: `BridgeOccupationMeasStatement` from the transition law,
  `LbkCornerCKX` for every `D₀ > 0` and `LbkHypRadialGaussCompare`, via
  `bridgeOccupationMeas_of_kernelBoundsX`.

## Proof

With `a = D₀s/2`, `b = D₀(T-s)/2` (both in `(0, κ/2]`) and `x' = (cosh r' - 1)/2`, `bopXMass` and
`bopXMoment` are radial integrals of `lbkHypRadial a x₀ x(r') · lbkHypRadial b x(r') 0`
(`bom_mass_eq`, `bom_moment_eq`). The comparison replaces both factors by the planar kernels
`bomEuclRadial` up to `c₀², C₀²` (`bom_prod_compare`); for those, the radial integral is
`K₁ ∫_{ℝ²} G · W` with the planar bridge weight `W` (`bom_radialInt_eucl`). The planar Gaussian
bounds `bom_planarW_lower`/`upper` at `m = b r₀/(a+b) = (1-s/T)r₀`, `σ² = ab/(a+b) ≤ κ/2`
conclude.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Real
open scoped ENNReal

theorem bom_planarX_polar {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    ENNReal.ofReal (bomPlanarX (r * Real.cos φ, r * Real.sin φ)) = ENNReal.ofReal (bomX r) := by
  unfold bomPlanarX bomX
  have h := Real.sin_sq_add_cos_sq φ
  rw [show (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 by linear_combination r ^ 2 * h,
    Real.sqrt_sq hr.le]

theorem bom_eucl_mass {a b r₀ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    bomRadialInt 1 (fun r' => bomEuclRadial a r₀ r' * bomEuclRadial b r' 0) =
      ENNReal.ofReal (bomK1 a b r₀) * ∫⁻ q, ENNReal.ofReal (bomW a b r₀ q) := by
  rw [bom_radialInt_eucl ha hb (fun _ => 1) measurable_const 1 (fun _ _ _ => rfl)]
  simp only [one_mul]

theorem bom_eucl_moment {a b r₀ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    bomRadialInt (fun r => ENNReal.ofReal (bomX r))
        (fun r' => bomEuclRadial a r₀ r' * bomEuclRadial b r' 0) =
      ENNReal.ofReal (bomK1 a b r₀) *
        ∫⁻ q, ENNReal.ofReal (bomPlanarX q) * ENNReal.ofReal (bomW a b r₀ q) :=
  bom_radialInt_eucl ha hb _ bom_planarX_continuous.measurable.ennreal_ofReal _
    (fun _ hr φ => bom_planarX_polar hr φ)

/-- The comparison for the bridge product `pX_s(x₀, x') pX_{T-s}(x', 0)`. -/
theorem bom_prod_compare {c C T₀ a b r₀ : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hcmp : ∀ T ∈ Ioc 0 T₀, ∀ r r' : ℝ, 0 ≤ r → 0 ≤ r' →
      c * bomEuclRadial T r r' ≤ lbkHypRadial T (bomX r) (bomX r') ∧
        lbkHypRadial T (bomX r) (bomX r') ≤ C * bomEuclRadial T r r')
    (ha : a ∈ Ioc 0 T₀) (hb : b ∈ Ioc 0 T₀) (hr₀ : 0 ≤ r₀) (r' : ℝ) (hr' : 0 ≤ r') :
    c ^ 2 * (bomEuclRadial a r₀ r' * bomEuclRadial b r' 0) ≤
        lbkHypRadial a (bomX r₀) (bomX r') * lbkHypRadial b (bomX r') 0 ∧
      lbkHypRadial a (bomX r₀) (bomX r') * lbkHypRadial b (bomX r') 0 ≤
        C ^ 2 * (bomEuclRadial a r₀ r' * bomEuclRadial b r' 0) := by
  obtain ⟨h1, h2⟩ := hcmp a ha r₀ r' hr₀ hr'
  obtain ⟨h3, h4⟩ := hcmp b hb r' 0 hr' le_rfl
  rw [bom_X_zero] at h3 h4
  have hEa := bom_euclRadial_nonneg ha.1 r₀ r'
  have hEb := bom_euclRadial_nonneg hb.1 r' 0
  have hHb := lbk_hypRadial_nonneg hb.1 (bomX r') 0
  constructor
  · calc c ^ 2 * (bomEuclRadial a r₀ r' * bomEuclRadial b r' 0)
        = (c * bomEuclRadial a r₀ r') * (c * bomEuclRadial b r' 0) := by ring
      _ ≤ _ := mul_le_mul h1 h3 (by positivity) ((mul_nonneg hc.le hEa).trans h1)
  · calc lbkHypRadial a (bomX r₀) (bomX r') * lbkHypRadial b (bomX r') 0
        ≤ (C * bomEuclRadial a r₀ r') * (C * bomEuclRadial b r' 0) :=
          mul_le_mul h2 h4 hHb (by positivity)
      _ = _ := by ring

/-- The hyperbolic times `a = D₀s/2`, `b = D₀(T-s)/2` lie in `(0, κ/2]`. -/
theorem bom_times_mem {κ D0 τ T s : ℝ} (hD0 : 0 < D0) (hκ : D0 * τ = κ) (hT : T ∈ Ioc 0 τ)
    (hs : s ∈ Ioo 0 T) :
    D0 * s / 2 ∈ Ioc 0 (κ / 2) ∧ D0 * (T - s) / 2 ∈ Ioc 0 (κ / 2) := by
  obtain ⟨hs0, hsT⟩ := hs
  have hu : 0 < T - s := sub_pos.2 hsT
  rw [← hκ]
  refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
  · have : D0 * s ≤ D0 * τ := mul_le_mul_of_nonneg_left (by linarith [hT.2]) hD0.le
    linarith
  · have : D0 * (T - s) ≤ D0 * τ := mul_le_mul_of_nonneg_left (by linarith [hT.2]) hD0.le
    linarith

theorem bom_m_eq {D0 T s r₀ : ℝ} (hD0 : 0 < D0) (hT : 0 < T) :
    D0 * (T - s) / 2 * r₀ / (D0 * s / 2 + D0 * (T - s) / 2) = (1 - s / T) * r₀ := by
  rw [show D0 * s / 2 + D0 * (T - s) / 2 = D0 * T / 2 by ring]
  field_simp

/-- `LbkHypBridgeMeanLower` from the radial Gaussian comparison. -/
theorem lbkHypBridgeMeanLower_of_gaussCompare (hP : LbkHypRadialGaussCompare) :
    LbkHypBridgeMeanLower := by
  intro κ hκ
  obtain ⟨c, hc, C, hC, hcmp⟩ := hP (κ / 2) (by positivity)
  refine ⟨(c / C) ^ 2, by positivity, ?_⟩
  intro D0 τ hD0 hτ hκ' r₀ hr₀ T hT s hs
  obtain ⟨haI, hbI⟩ := bom_times_mem hD0 hκ' hT hs
  have hm := bom_m_eq (s := s) (r₀ := r₀) hD0 hT.1
  rw [show (Real.cosh r₀ - 1) / 2 = bomX r₀ from rfl, bom_mass_eq hD0 hs.1 hs.2,
    bom_moment_eq hD0 hs.1 hs.2]
  set a := D0 * s / 2
  set b := D0 * (T - s) / 2
  have ha : 0 < a := haI.1
  have hb : 0 < b := hbI.1
  have hcmp' := bom_prod_compare hc hC hcmp haI hbI hr₀
  set k₁ := fun r => lbkHypRadial a (bomX r₀) (bomX r) * lbkHypRadial b (bomX r) 0
  set k₂ := fun r' => bomEuclRadial a r₀ r' * bomEuclRadial b r' 0
  set g := fun r => ENNReal.ofReal (bomX r)
  set BE := ∫⁻ q, ENNReal.ofReal (bomW a b r₀ q)
  set AE := ∫⁻ q, ENNReal.ofReal (bomPlanarX q) * ENNReal.ofReal (bomW a b r₀ q)
  set Xm := (Real.cosh ((1 - s / T) * r₀) - 1) / 2
  have hXm : 0 ≤ Xm := bom_X_nonneg _
  have hK := bom_K1_nonneg ha hb r₀
  have hmass : bomRadialInt 1 k₁ ≤
      ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * BE) := by
    calc bomRadialInt 1 k₁ ≤ bomRadialInt 1 (fun r => C ^ 2 * k₂ r) :=
          bom_radialInt_mono fun r hr => (hcmp' r hr).2
      _ = ENNReal.ofReal (C ^ 2) * bomRadialInt 1 k₂ :=
          bom_radialInt_const_mul _ _ (by positivity)
      _ = _ := by rw [bom_eucl_mass ha hb]
  have hmom : ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * AE) ≤
      bomRadialInt g k₁ := by
    calc ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * AE)
        = ENNReal.ofReal (c ^ 2) * bomRadialInt g k₂ := by rw [bom_eucl_moment ha hb]
      _ = bomRadialInt g (fun r => c ^ 2 * k₂ r) :=
          (bom_radialInt_const_mul _ _ (by positivity)).symm
      _ ≤ bomRadialInt g k₁ := bom_radialInt_mono fun r hr => (hcmp' r hr).1
  have hpl : ENNReal.ofReal Xm * BE ≤ AE := by
    have := bom_planarW_lower ha hb hr₀
    rwa [hm] at this
  calc ENNReal.ofReal ((c / C) ^ 2 * Xm) * bomRadialInt 1 k₁
      ≤ ENNReal.ofReal ((c / C) ^ 2 * Xm) *
          (ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * BE)) := by gcongr
    _ = ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * (ENNReal.ofReal Xm * BE)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show (c / C) ^ 2 * Xm * C ^ 2 = c ^ 2 * Xm by field_simp,
          ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * AE) := by gcongr
    _ ≤ bomRadialInt g k₁ := hmom

/-- `LbkHypBridgeMeanUpper` from the radial Gaussian comparison. -/
theorem lbkHypBridgeMeanUpper_of_gaussCompare (hP : LbkHypRadialGaussCompare) :
    LbkHypBridgeMeanUpper := by
  intro κ hκ
  obtain ⟨c, hc, C, hC, hcmp⟩ := hP (κ / 2) (by positivity)
  refine ⟨(C / c) ^ 2 * Real.exp (2 * κ), by positivity, ?_⟩
  intro D0 τ hD0 hτ hκ' r₀ hr₀ T hT s hs
  obtain ⟨haI, hbI⟩ := bom_times_mem hD0 hκ' hT hs
  have hm := bom_m_eq (s := s) (r₀ := r₀) hD0 hT.1
  rw [show (Real.cosh r₀ - 1) / 2 = bomX r₀ from rfl, bom_mass_eq hD0 hs.1 hs.2,
    bom_moment_eq hD0 hs.1 hs.2]
  set a := D0 * s / 2
  set b := D0 * (T - s) / 2
  have ha : 0 < a := haI.1
  have hb : 0 < b := hbI.1
  have hcmp' := bom_prod_compare hc hC hcmp haI hbI hr₀
  set k₁ := fun r => lbkHypRadial a (bomX r₀) (bomX r) * lbkHypRadial b (bomX r) 0
  set k₂ := fun r' => bomEuclRadial a r₀ r' * bomEuclRadial b r' 0
  set g := fun r => ENNReal.ofReal (bomX r)
  set BE := ∫⁻ q, ENNReal.ofReal (bomW a b r₀ q)
  set AE := ∫⁻ q, ENNReal.ofReal (bomPlanarX q) * ENNReal.ofReal (bomW a b r₀ q)
  set em := Real.exp ((1 - s / T) * r₀)
  have hK := bom_K1_nonneg ha hb r₀
  have hmass : ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * BE) ≤
      bomRadialInt 1 k₁ := by
    calc ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * BE)
        = ENNReal.ofReal (c ^ 2) * bomRadialInt 1 k₂ := by rw [bom_eucl_mass ha hb]
      _ = bomRadialInt 1 (fun r => c ^ 2 * k₂ r) :=
          (bom_radialInt_const_mul _ _ (by positivity)).symm
      _ ≤ bomRadialInt 1 k₁ := bom_radialInt_mono fun r hr => (hcmp' r hr).1
  have hmom : bomRadialInt g k₁ ≤
      ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * AE) := by
    calc bomRadialInt g k₁ ≤ bomRadialInt g (fun r => C ^ 2 * k₂ r) :=
          bom_radialInt_mono fun r hr => (hcmp' r hr).2
      _ = ENNReal.ofReal (C ^ 2) * bomRadialInt g k₂ :=
          bom_radialInt_const_mul _ _ (by positivity)
      _ = _ := by rw [bom_eucl_moment ha hb]
  have hσ : 4 * (a * b / (a + b)) ≤ 2 * κ := by
    have hab : 0 < a + b := by positivity
    have : a * b / (a + b) ≤ a := by
      rw [div_le_iff₀ hab]
      nlinarith
    linarith [haI.2]
  have hpu : AE ≤ ENNReal.ofReal (Real.exp (2 * κ) * em) * BE := by
    refine (bom_planarW_upper ha hb hr₀).trans ?_
    gcongr
    rw [← Real.exp_add, hm]
    exact Real.exp_le_exp.2 (by linarith)
  calc bomRadialInt g k₁
      ≤ ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) *
          (ENNReal.ofReal (Real.exp (2 * κ) * em) * BE)) := by
        refine hmom.trans ?_
        gcongr
    _ = ENNReal.ofReal ((C / c) ^ 2 * Real.exp (2 * κ) * em) *
          (ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (bomK1 a b r₀) * BE)) := by
        have hcoef : ENNReal.ofReal ((C / c) ^ 2 * Real.exp (2 * κ) * em) *
            ENNReal.ofReal (c ^ 2) =
            ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (Real.exp (2 * κ) * em) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        rw [← mul_assoc (ENNReal.ofReal ((C / c) ^ 2 * Real.exp (2 * κ) * em)), hcoef]
        ring
    _ ≤ ENNReal.ofReal ((C / c) ^ 2 * Real.exp (2 * κ) * em) * bomRadialInt 1 k₁ := by gcongr

/-- The bridge-occupation lemma (measurable form) from the transition law, `LbkCornerCKX` and the
radial Gaussian comparison (which gives the two bridge-mean bounds). -/
theorem bridgeOccupationMeas_of_baseCKX
    (hbase : ∀ D0 : ℝ, 0 < D0 → LbkBaseTransitionLaw D0 ∧ LbkCornerCKX D0)
    (hP : LbkHypRadialGaussCompare) : BridgeOccupationMeasStatement :=
  bridgeOccupationMeas_of_kernelBoundsX hbase (lbkHypBridgeMeanLower_of_gaussCompare hP)
    (lbkHypBridgeMeanUpper_of_gaussCompare hP)

end BlockBand.Endpoints
