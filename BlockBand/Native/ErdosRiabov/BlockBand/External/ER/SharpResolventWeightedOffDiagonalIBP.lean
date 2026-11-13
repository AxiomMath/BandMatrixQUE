module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SharpResolventWeightedProductFubini

/-!
# Supported off-diagonal IBP for the resolvent-weighted Dyson test

This module lifts the two one-dimensional Gaussian integrations by parts to
the strict coordinate/background product, recombines both circular
orientations, treats zero variance by the Dirac law, and transfers the
identities back to the Gaussian-ring law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSharpCoordinateIBP

open Matrix MeasureTheory ProbabilityTheory
open ERGaussianCoordinate ERStrictCoordinateDisintegration
open ERResolventMomentIBP ERProfile
open ERComplementBackgroundReconstruction ERConcrete
open scoped BigOperators NNReal Matrix.Norms.L2Operator

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Integrability under a nondegenerate Gaussian measure supplies the exact
density-level integrability required by the repository's Gaussian IBP lemma. -/
theorem integrable_gaussianPDF_mul_of_integrable_gaussianReal
    (v : NNReal) (hv : v ≠ 0) {F : ℝ → ℂ}
    (hF : Integrable F (gaussianReal 0 v)) :
    Integrable (fun r : ℝ =>
      ((gaussianPDFReal 0 v r : ℝ) : ℂ) * F r) := by
  rw [gaussianReal_of_var_ne_zero 0 hv] at hF
  have h := (integrable_withDensity_iff_integrable_smul
    (by fun_prop)).1 hF
  convert h using 1
  funext r
  change ((gaussianPDFReal 0 v r : ℝ) : ℂ) * F r =
    (((((gaussianPDFReal 0 v r).toNNReal : NNReal) : ℝ) : ℂ) * F r)
  rw [Real.coe_toNNReal _ (gaussianPDFReal_nonneg _ _ _)]

/-- The coordinate-weighted density obligation follows in the same way from
Gaussian-measure integrability of the weighted test. -/
theorem integrable_id_gaussianPDF_mul_of_integrable_gaussianReal
    (v : NNReal) (hv : v ≠ 0) {F : ℝ → ℂ}
    (hF : Integrable (fun r : ℝ => (r : ℂ) * F r) (gaussianReal 0 v)) :
    Integrable (fun r : ℝ =>
      ((r * gaussianPDFReal 0 v r : ℝ) : ℂ) * F r) := by
  have h := integrable_gaussianPDF_mul_of_integrable_gaussianReal v hv hF
  convert h using 1
  funext r
  push_cast
  ring

/-- Fubini lifts the supported real-coordinate IBP for the
resolvent-weighted lower-moment test through the imaginary coordinate and
the background marginal. -/
theorem Law.integral_realWeightedCoordinateResolventLowerTest_eq_derivative_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2)
    (x y i j : Site p.n p.W) (z : ℂ) (hz : 0 < z.im) (m : ℕ)
    (hvar : 0 < siteCovariance p q₀.1.1 q₀.1.2) :
    (∫ v, (v.1.1 : ℂ) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2 ∂strictCoordinateProductMeasure M q₀) =
      (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
        ∫ v, coordinateResolventLowerDerivReal p v.2
          q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀) := by
  let t : NNReal :=
    ⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩
  let v : NNReal := t / 2
  have hv : v ≠ 0 := by
    apply ne_of_gt
    exact div_pos (show 0 < t by exact hvar) (by norm_num)
  let μB := strictBackgroundMeasure M q₀
  let _ : IsFiniteMeasure μB := Measure.isFiniteMeasure_map M.P _
  let _ : IsFiniteMeasure (circularGaussianMeasure t) :=
    circularGaussianMeasure_isFinite t
  let FL : ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ :=
    fun w => (w.1.1 : ℂ) *
      coordinateResolventLowerTest p w.2 q₀.1.1 q₀.1.2
        x y i j z m w.1.1 w.1.2
  let FT : ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ :=
    fun w => coordinateResolventLowerTest p w.2 q₀.1.1 q₀.1.2
      x y i j z m w.1.1 w.1.2
  let FR : ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ :=
    fun w => coordinateResolventLowerDerivReal p w.2 q₀.1.1 q₀.1.2
      x y i j z m w.1.1 w.1.2
  have hL : Integrable FL ((circularGaussianMeasure t).prod μB) := by
    simpa [FL, t, μB, strictCoordinateProductMeasure] using
      Law.integrable_realWeightedCoordinateResolventLowerTest_product
        M q₀ hne x y i j z hz m
  have hT : Integrable FT ((circularGaussianMeasure t).prod μB) := by
    simpa [FT, t, μB, strictCoordinateProductMeasure] using
      Law.integrable_coordinateResolventLowerTest_product
        M q₀ hne x y i j z hz m
  have hR : Integrable FR ((circularGaussianMeasure t).prod μB) := by
    simpa [FR, t, μB, strictCoordinateProductMeasure] using
      Law.integrable_coordinateResolventLowerDerivReal_product
        M q₀ hne x y i j z hz m
  change (∫ w, FL w ∂(circularGaussianMeasure t).prod μB) =
    (((v : NNReal) : ℝ) : ℂ) *
      ∫ w, FR w ∂(circularGaussianMeasure t).prod μB
  rw [integral_prod_symm FL hL, integral_prod_symm FR hR,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Law.offdiagBackground_ae_isHermitian M q₀ hne,
    hL.prod_left_ae, hT.prod_left_ae, hR.prod_left_ae] with B hB hLB hTB hRB
  rw [show circularGaussianMeasure t =
      (gaussianReal 0 v).prod (gaussianReal 0 v) by rfl,
    integral_prod_symm _ hLB, integral_prod_symm _ hRB,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hLB.prod_left_ae, hTB.prod_left_ae,
    hRB.prod_left_ae] with s hLs hTs hRs
  exact gaussianIBP_jointTest_real v hv
    (fun r s (_ : Unit) => coordinateResolventLowerTest p B q₀.1.1 q₀.1.2
      x y i j z m r s)
    (fun r s (_ : Unit) => coordinateResolventLowerDerivReal p B q₀.1.1 q₀.1.2
      x y i j z m r s)
    (fun r s _ => hasDerivAt_coordinateResolventLowerTest_real
      p B hB q₀.1.1 q₀.1.2 x y i j z hz.ne' m r s)
    s ()
    (integrable_id_gaussianPDF_mul_of_integrable_gaussianReal v hv hLs)
    (integrable_gaussianPDF_mul_of_integrable_gaussianReal v hv hRs)
    (integrable_gaussianPDF_mul_of_integrable_gaussianReal v hv hTs)

/-- Fubini lifts the supported imaginary-coordinate IBP for the same test. -/
theorem Law.integral_imaginaryWeightedCoordinateResolventLowerTest_eq_derivative_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2)
    (x y i j : Site p.n p.W) (z : ℂ) (hz : 0 < z.im) (m : ℕ)
    (hvar : 0 < siteCovariance p q₀.1.1 q₀.1.2) :
    (∫ v, (v.1.2 : ℂ) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2 ∂strictCoordinateProductMeasure M q₀) =
      (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
        ∫ v, coordinateResolventLowerDerivImaginary p v.2
          q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀) := by
  let t : NNReal :=
    ⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩
  let v : NNReal := t / 2
  have hv : v ≠ 0 := by
    apply ne_of_gt
    exact div_pos (show 0 < t by exact hvar) (by norm_num)
  let μB := strictBackgroundMeasure M q₀
  let _ : IsFiniteMeasure μB := Measure.isFiniteMeasure_map M.P _
  let _ : IsFiniteMeasure (circularGaussianMeasure t) :=
    circularGaussianMeasure_isFinite t
  let FL : ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ :=
    fun w => (w.1.2 : ℂ) *
      coordinateResolventLowerTest p w.2 q₀.1.1 q₀.1.2
        x y i j z m w.1.1 w.1.2
  let FT : ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ :=
    fun w => coordinateResolventLowerTest p w.2 q₀.1.1 q₀.1.2
      x y i j z m w.1.1 w.1.2
  let FR : ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ :=
    fun w => coordinateResolventLowerDerivImaginary p w.2
      q₀.1.1 q₀.1.2 x y i j z m w.1.1 w.1.2
  have hL : Integrable FL ((circularGaussianMeasure t).prod μB) := by
    simpa [FL, t, μB, strictCoordinateProductMeasure] using
      Law.integrable_imaginaryWeightedCoordinateResolventLowerTest_product
        M q₀ hne x y i j z hz m
  have hT : Integrable FT ((circularGaussianMeasure t).prod μB) := by
    simpa [FT, t, μB, strictCoordinateProductMeasure] using
      Law.integrable_coordinateResolventLowerTest_product
        M q₀ hne x y i j z hz m
  have hR : Integrable FR ((circularGaussianMeasure t).prod μB) := by
    simpa [FR, t, μB, strictCoordinateProductMeasure] using
      Law.integrable_coordinateResolventLowerDerivImaginary_product
        M q₀ hne x y i j z hz m
  change (∫ w, FL w ∂(circularGaussianMeasure t).prod μB) =
    (((v : NNReal) : ℝ) : ℂ) *
      ∫ w, FR w ∂(circularGaussianMeasure t).prod μB
  rw [integral_prod_symm FL hL, integral_prod_symm FR hR,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Law.offdiagBackground_ae_isHermitian M q₀ hne,
    hL.prod_left_ae, hT.prod_left_ae, hR.prod_left_ae] with B hB hLB hTB hRB
  rw [show circularGaussianMeasure t =
      (gaussianReal 0 v).prod (gaussianReal 0 v) by rfl,
    integral_prod _ hLB, integral_prod _ hRB,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hLB.prod_right_ae, hTB.prod_right_ae,
    hRB.prod_right_ae] with r hLr hTr hRr
  exact gaussianIBP_jointTest_imaginary v hv
    (fun r s (_ : Unit) => coordinateResolventLowerTest p B q₀.1.1 q₀.1.2
      x y i j z m r s)
    (fun r s (_ : Unit) => coordinateResolventLowerDerivImaginary
      p B q₀.1.1 q₀.1.2 x y i j z m r s)
    (fun r s _ => hasDerivAt_coordinateResolventLowerTest_imaginary
      p B hB q₀.1.1 q₀.1.2 x y i j z hz.ne' m r s)
    r ()
    (integrable_id_gaussianPDF_mul_of_integrable_gaussianReal v hv hLr)
    (integrable_gaussianPDF_mul_of_integrable_gaussianReal v hv hRr)
    (integrable_gaussianPDF_mul_of_integrable_gaussianReal v hv hTr)

/-- At zero variance both circular orientations vanish because the selected
pair is the Dirac mass at `(0,0)`. -/
theorem Law.integral_linearWeightedCoordinateResolventLowerTest_eq_zero_of_covariance_zero
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hvar : siteCovariance p q₀.1.1 q₀.1.2 = 0)
    (x y i j : Site p.n p.W) (z ε : ℂ) (m : ℕ) :
    (∫ v, ((v.1.1 : ℂ) + ε * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2
      ∂strictCoordinateProductMeasure M q₀) = 0 := by
  let t : NNReal := ⟨siteCovariance p q₀.1.1 q₀.1.2,
    (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩
  have ht : t = 0 := by
    ext
    exact hvar
  let _ : IsFiniteMeasure (strictBackgroundMeasure M q₀) :=
    Measure.isFiniteMeasure_map M.P _
  let F : ((ℝ × ℝ) × Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ :=
    fun v => ((v.1.1 : ℂ) + ε * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2
  have hF : Measurable F := by
    exact (((measurable_fst.comp measurable_fst).complex_ofReal.add
      (measurable_const.mul
        ((measurable_snd.comp measurable_fst).complex_ofReal))).mul
      (measurable_coordinateResolventLowerTest_product
        p q₀.1.1 q₀.1.2 x y i j z m))
  change (∫ v, F v ∂
      (circularGaussianMeasure t).prod (strictBackgroundMeasure M q₀)) = 0
  rw [ht, circularGaussianMeasure_zero, Measure.dirac_prod]
  change (∫ v, F v ∂Measure.map (fun B => ((0, 0), B))
    (strictBackgroundMeasure M q₀)) = 0
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable]
  simp [F]

/-- The real and imaginary supported identities recombine in the
`r + i s` orientation. -/
theorem Law.integral_circularWeightedCoordinateResolventLowerTest_eq_derivative_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2)
    (x y i j : Site p.n p.W) (z : ℂ) (hz : 0 < z.im) (m : ℕ)
    (hvar : 0 < siteCovariance p q₀.1.1 q₀.1.2) :
    (∫ v, ((v.1.1 : ℂ) + Complex.I * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2
      ∂strictCoordinateProductMeasure M q₀) =
      (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
        ∫ v, (coordinateResolventLowerDerivReal p v.2
            q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2 +
          Complex.I * coordinateResolventLowerDerivImaginary p v.2
            q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
          ∂strictCoordinateProductMeasure M q₀) := by
  have hWr :=
    Law.integrable_realWeightedCoordinateResolventLowerTest_product
      M q₀ hne x y i j z hz m
  have hWi :=
    Law.integrable_imaginaryWeightedCoordinateResolventLowerTest_product
      M q₀ hne x y i j z hz m
  have hDr := Law.integrable_coordinateResolventLowerDerivReal_product
    M q₀ hne x y i j z hz m
  have hDi := Law.integrable_coordinateResolventLowerDerivImaginary_product
    M q₀ hne x y i j z hz m
  calc
    _ = (∫ v, (v.1.1 : ℂ) *
          coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀) +
        Complex.I * (∫ v, (v.1.2 : ℂ) *
          coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀) := by
      rw [← integral_const_mul,
        ← integral_add hWr (hWi.const_mul Complex.I)]
      apply integral_congr_ae
      filter_upwards [] with v
      ring
    _ = (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
          ∫ v, coordinateResolventLowerDerivReal p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
            ∂strictCoordinateProductMeasure M q₀) +
        Complex.I *
          (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
          ∫ v, coordinateResolventLowerDerivImaginary p v.2
            q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2
            ∂strictCoordinateProductMeasure M q₀) := by
      rw [Law.integral_realWeightedCoordinateResolventLowerTest_eq_derivative_product
          M q₀ hne x y i j z hz m hvar,
        Law.integral_imaginaryWeightedCoordinateResolventLowerTest_eq_derivative_product
          M q₀ hne x y i j z hz m hvar]
    _ = _ := by
      rw [integral_add hDr (hDi.const_mul Complex.I), integral_const_mul]
      ring

/-- The conjugate `r - i s` orientation has the corresponding difference
of the two coordinate derivatives. -/
theorem Law.integral_conjugateCircularWeightedCoordinateResolventLowerTest_eq_derivative_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2)
    (x y i j : Site p.n p.W) (z : ℂ) (hz : 0 < z.im) (m : ℕ)
    (hvar : 0 < siteCovariance p q₀.1.1 q₀.1.2) :
    (∫ v, ((v.1.1 : ℂ) - Complex.I * (v.1.2 : ℂ)) *
      coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
        x y i j z m v.1.1 v.1.2
      ∂strictCoordinateProductMeasure M q₀) =
      (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
        ∫ v, (coordinateResolventLowerDerivReal p v.2
            q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2 -
          Complex.I * coordinateResolventLowerDerivImaginary p v.2
            q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
          ∂strictCoordinateProductMeasure M q₀) := by
  have hWr :=
    Law.integrable_realWeightedCoordinateResolventLowerTest_product
      M q₀ hne x y i j z hz m
  have hWi :=
    Law.integrable_imaginaryWeightedCoordinateResolventLowerTest_product
      M q₀ hne x y i j z hz m
  have hDr := Law.integrable_coordinateResolventLowerDerivReal_product
    M q₀ hne x y i j z hz m
  have hDi := Law.integrable_coordinateResolventLowerDerivImaginary_product
    M q₀ hne x y i j z hz m
  calc
    _ = (∫ v, (v.1.1 : ℂ) *
          coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀) -
        Complex.I * (∫ v, (v.1.2 : ℂ) *
          coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀) := by
      rw [← integral_const_mul]
      rw [show (∫ v, (v.1.1 : ℂ) *
          coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀) -
          ∫ v, Complex.I * ((v.1.2 : ℂ) *
            coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
              x y i j z m v.1.1 v.1.2)
            ∂strictCoordinateProductMeasure M q₀ =
          ∫ v, (v.1.1 : ℂ) *
              coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
                x y i j z m v.1.1 v.1.2 -
            Complex.I * ((v.1.2 : ℂ) *
              coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
                x y i j z m v.1.1 v.1.2)
            ∂strictCoordinateProductMeasure M q₀ by
          rw [integral_sub hWr (hWi.const_mul Complex.I)]]
      apply integral_congr_ae
      filter_upwards [] with v
      ring
    _ = (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
          ∫ v, coordinateResolventLowerDerivReal p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
            ∂strictCoordinateProductMeasure M q₀) -
        Complex.I *
          (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
          ∫ v, coordinateResolventLowerDerivImaginary p v.2
            q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2
            ∂strictCoordinateProductMeasure M q₀) := by
      rw [Law.integral_realWeightedCoordinateResolventLowerTest_eq_derivative_product
          M q₀ hne x y i j z hz m hvar,
        Law.integral_imaginaryWeightedCoordinateResolventLowerTest_eq_derivative_product
          M q₀ hne x y i j z hz m hvar]
    _ = _ := by
      rw [integral_sub hDr (hDi.const_mul Complex.I), integral_const_mul]
      ring

/-- Circular derivative test evaluated after removing and reinserting the
observed strict coordinate of the sample matrix. -/
def actualCoordinateResolventLowerDerivativeCircular
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (ω : M.Ω) : ℂ :=
  coordinateResolventLowerDerivReal p
      (offdiagBackground (M.H ω) q₀.1.1 q₀.1.2)
      q₀.1.1 q₀.1.2 x y i j z m
      (M.H ω q₀.1.1 q₀.1.2).re (M.H ω q₀.1.1 q₀.1.2).im +
    Complex.I * coordinateResolventLowerDerivImaginary p
      (offdiagBackground (M.H ω) q₀.1.1 q₀.1.2)
      q₀.1.1 q₀.1.2 x y i j z m
      (M.H ω q₀.1.1 q₀.1.2).re (M.H ω q₀.1.1 q₀.1.2).im

/-- Conjugate-circular derivative test on the sample matrix. -/
def actualCoordinateResolventLowerDerivativeConjugateCircular
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (x y i j : Site p.n p.W) (z : ℂ) (m : ℕ) (ω : M.Ω) : ℂ :=
  coordinateResolventLowerDerivReal p
      (offdiagBackground (M.H ω) q₀.1.1 q₀.1.2)
      q₀.1.1 q₀.1.2 x y i j z m
      (M.H ω q₀.1.1 q₀.1.2).re (M.H ω q₀.1.1 q₀.1.2).im -
    Complex.I * coordinateResolventLowerDerivImaginary p
      (offdiagBackground (M.H ω) q₀.1.1 q₀.1.2)
      q₀.1.1 q₀.1.2 x y i j z m
      (M.H ω q₀.1.1 q₀.1.2).re (M.H ω q₀.1.1 q₀.1.2).im

/-- Exact disintegration transfers the circular derivative test back to the
Gaussian-ring law. -/
theorem Law.integral_actualCoordinateResolventLowerDerivativeCircular_eq_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (m : ℕ) :
    (∫ ω, actualCoordinateResolventLowerDerivativeCircular
      M q₀ x y i j z m ω ∂M.P) =
      ∫ v, (coordinateResolventLowerDerivReal p v.2
          q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2 +
        Complex.I * coordinateResolventLowerDerivImaginary p v.2
          q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
        ∂strictCoordinateProductMeasure M q₀ := by
  unfold strictCoordinateProductMeasure circularGaussianMeasure
    strictBackgroundMeasure
  have hv : (⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩ / 2 : NNReal) =
      ⟨siteCovariance p q₀.1.1 q₀.1.2 / 2,
        div_nonneg (siteCovariance_flat p q₀.1.1 q₀.1.2).1
          (by norm_num)⟩ := by
    ext
    rfl
  rw [hv, ← Law.integral_offdiagGaussian_background M q₀ hne]
  · rfl
  · exact ((measurable_coordinateResolventLowerDerivReal_product
      p q₀.1.1 q₀.1.2 x y i j z m).add
        (measurable_const.mul
          (measurable_coordinateResolventLowerDerivImaginary_product
            p q₀.1.1 q₀.1.2 x y i j z m))).aestronglyMeasurable

/-- Exact disintegration transfer for the conjugate-circular derivative. -/
theorem Law.integral_actualCoordinateResolventLowerDerivativeConjugateCircular_eq_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (m : ℕ) :
    (∫ ω, actualCoordinateResolventLowerDerivativeConjugateCircular
      M q₀ x y i j z m ω ∂M.P) =
      ∫ v, (coordinateResolventLowerDerivReal p v.2
          q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2 -
        Complex.I * coordinateResolventLowerDerivImaginary p v.2
          q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
        ∂strictCoordinateProductMeasure M q₀ := by
  unfold strictCoordinateProductMeasure circularGaussianMeasure
    strictBackgroundMeasure
  have hv : (⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩ / 2 : NNReal) =
      ⟨siteCovariance p q₀.1.1 q₀.1.2 / 2,
        div_nonneg (siteCovariance_flat p q₀.1.1 q₀.1.2).1
          (by norm_num)⟩ := by
    ext
    rfl
  rw [hv, ← Law.integral_offdiagGaussian_background M q₀ hne]
  · rfl
  · exact ((measurable_coordinateResolventLowerDerivReal_product
      p q₀.1.1 q₀.1.2 x y i j z m).sub
        (measurable_const.mul
          (measurable_coordinateResolventLowerDerivImaginary_product
            p q₀.1.1 q₀.1.2 x y i j z m))).aestronglyMeasurable

/-- The `H_ab`-weighted Green/lower-moment test is the circular product
integral after exact coordinate/background disintegration. -/
theorem Law.integral_entryWeightedResolventLowerTest_eq_circular_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) :
    (∫ ω, M.H ω q₀.1.1 q₀.1.2 * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω) ∂M.P) =
      ∫ v, ((v.1.1 : ℂ) + Complex.I * (v.1.2 : ℂ)) *
        coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
          x y i j z m v.1.1 v.1.2
        ∂strictCoordinateProductMeasure M q₀ := by
  unfold strictCoordinateProductMeasure circularGaussianMeasure
    strictBackgroundMeasure
  have hv : (⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩ / 2 : NNReal) =
      ⟨siteCovariance p q₀.1.1 q₀.1.2 / 2,
        div_nonneg (siteCovariance_flat p q₀.1.1 q₀.1.2).1
          (by norm_num)⟩ := by
    ext
    rfl
  rw [hv, ← Law.integral_offdiagGaussian_background M q₀ hne]
  · apply integral_congr_ae
    filter_upwards [] with ω
    rw [coordinateResolventLowerTest_actual M q₀.1.1 q₀.1.2
      x y i j q₀.2 z hz m ω]
    have hreim :
        M.H ω q₀.1.1 q₀.1.2 =
          ((M.H ω q₀.1.1 q₀.1.2).re : ℂ) +
            Complex.I * (M.H ω q₀.1.1 q₀.1.2).im := by
      apply Complex.ext <;> simp
    nth_rewrite 1 [hreim]
    ring
  · exact ((((measurable_fst.comp measurable_fst).complex_ofReal.add
      (measurable_const.mul
        ((measurable_snd.comp measurable_fst).complex_ofReal))).mul
      (measurable_coordinateResolventLowerTest_product
        p q₀.1.1 q₀.1.2 x y i j z m))).aestronglyMeasurable

/-- The reversed Hermitian entry `H_ba` transfers to the conjugate-circular
coordinate orientation. -/
theorem Law.integral_starEntryWeightedResolventLowerTest_eq_conjugateCircular_product
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : z.im ≠ 0) (m : ℕ) :
    (∫ ω, M.H ω q₀.1.2 q₀.1.1 * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω) ∂M.P) =
      ∫ v, ((v.1.1 : ℂ) - Complex.I * (v.1.2 : ℂ)) *
        coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
          x y i j z m v.1.1 v.1.2
        ∂strictCoordinateProductMeasure M q₀ := by
  unfold strictCoordinateProductMeasure circularGaussianMeasure
    strictBackgroundMeasure
  have hv : (⟨siteCovariance p q₀.1.1 q₀.1.2,
      (siteCovariance_flat p q₀.1.1 q₀.1.2).1⟩ / 2 : NNReal) =
      ⟨siteCovariance p q₀.1.1 q₀.1.2 / 2,
        div_nonneg (siteCovariance_flat p q₀.1.1 q₀.1.2).1
          (by norm_num)⟩ := by
    ext
    rfl
  rw [hv, ← Law.integral_offdiagGaussian_background M q₀ hne]
  · apply integral_congr_ae
    filter_upwards [] with ω
    rw [coordinateResolventLowerTest_actual M q₀.1.1 q₀.1.2
      x y i j q₀.2 z hz m ω]
    have hstar := (M.H_hermitian ω).apply q₀.1.2 q₀.1.1
    rw [← hstar]
    have hconj :
        star (M.H ω q₀.1.1 q₀.1.2) =
          ((M.H ω q₀.1.1 q₀.1.2).re : ℂ) -
            Complex.I * (M.H ω q₀.1.1 q₀.1.2).im := by
      apply Complex.ext <;> simp
    nth_rewrite 1 [hconj]
    ring
  · exact ((((measurable_fst.comp measurable_fst).complex_ofReal.sub
      (measurable_const.mul
        ((measurable_snd.comp measurable_fst).complex_ofReal))).mul
      (measurable_coordinateResolventLowerTest_product
        p q₀.1.1 q₀.1.2 x y i j z m))).aestronglyMeasurable

/-- Circular IBP under the matrix law for one ordered off-diagonal term.  The
zero-covariance case is discharged by the Dirac law rather than division by
the variance. -/
theorem Law.integral_entryWeightedResolventLowerTest_eq_actualCircularDerivative
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    (∫ ω, M.H ω q₀.1.1 q₀.1.2 * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω) ∂M.P) =
      (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
        ∫ ω, actualCoordinateResolventLowerDerivativeCircular
          M q₀ x y i j z m ω ∂M.P) := by
  rcases siteCovariance_zero_or_positive p q₀.1.1 q₀.1.2 with h0 | hp
  · rw [h0]
    norm_num
    rw [Law.integral_entryWeightedResolventLowerTest_eq_circular_product
      M q₀ hne x y i j z hz.ne' m]
    exact
      Law.integral_linearWeightedCoordinateResolventLowerTest_eq_zero_of_covariance_zero
        M q₀ h0 x y i j z Complex.I m
  · calc
      _ = ∫ v, ((v.1.1 : ℂ) + Complex.I * (v.1.2 : ℂ)) *
          coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀ :=
        Law.integral_entryWeightedResolventLowerTest_eq_circular_product
          M q₀ hne x y i j z hz.ne' m
      _ = (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
          ∫ v, (coordinateResolventLowerDerivReal p v.2
              q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2 +
            Complex.I * coordinateResolventLowerDerivImaginary p v.2
              q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
            ∂strictCoordinateProductMeasure M q₀) :=
        Law.integral_circularWeightedCoordinateResolventLowerTest_eq_derivative_product
          M q₀ hne x y i j z hz m hp
      _ = _ := by
        rw [←
          Law.integral_actualCoordinateResolventLowerDerivativeCircular_eq_product
            M q₀ hne x y i j z m]

/-- Conjugate-circular IBP under the matrix law for the reversed Hermitian entry,
again including the zero-variance branch. -/
theorem Law.integral_starEntryWeightedResolventLowerTest_eq_actualConjugateCircularDerivative
    {p : Params} (M : Law p) (q₀ : UpperPair p)
    (hne : q₀.1.1 ≠ q₀.1.2) (x y i j : Site p.n p.W)
    (z : ℂ) (hz : 0 < z.im) (m : ℕ) :
    (∫ ω, M.H ω q₀.1.2 q₀.1.1 * green M z ω i j *
      lowerConjugateMomentTest m
        (ERFluctuationMoments.signedResolventError M z x y ω) ∂M.P) =
      (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
        ∫ ω, actualCoordinateResolventLowerDerivativeConjugateCircular
          M q₀ x y i j z m ω ∂M.P) := by
  rcases siteCovariance_zero_or_positive p q₀.1.1 q₀.1.2 with h0 | hp
  · rw [h0]
    norm_num
    rw [
      Law.integral_starEntryWeightedResolventLowerTest_eq_conjugateCircular_product
        M q₀ hne x y i j z hz.ne' m]
    simpa [sub_eq_add_neg] using
      (Law.integral_linearWeightedCoordinateResolventLowerTest_eq_zero_of_covariance_zero
        M q₀ h0 x y i j z (-Complex.I) m)
  · calc
      _ = ∫ v, ((v.1.1 : ℂ) - Complex.I * (v.1.2 : ℂ)) *
          coordinateResolventLowerTest p v.2 q₀.1.1 q₀.1.2
            x y i j z m v.1.1 v.1.2
          ∂strictCoordinateProductMeasure M q₀ :=
        Law.integral_starEntryWeightedResolventLowerTest_eq_conjugateCircular_product
          M q₀ hne x y i j z hz.ne' m
      _ = (((siteCovariance p q₀.1.1 q₀.1.2 / 2 : ℝ) : ℂ) *
          ∫ v, (coordinateResolventLowerDerivReal p v.2
              q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2 -
            Complex.I * coordinateResolventLowerDerivImaginary p v.2
              q₀.1.1 q₀.1.2 x y i j z m v.1.1 v.1.2)
            ∂strictCoordinateProductMeasure M q₀) :=
        Law.integral_conjugateCircularWeightedCoordinateResolventLowerTest_eq_derivative_product
          M q₀ hne x y i j z hz m hp
      _ = _ := by
        rw [←
          Law.integral_actualCoordinateResolventLowerDerivativeConjugateCircular_eq_product
            M q₀ hne x y i j z m]

end ERSharpCoordinateIBP
end GaussianRing
end ERNative.BlockBand
