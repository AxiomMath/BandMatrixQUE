module

public import BlockBand.Coarea.FixedOmegaChartZero

/-!
# Fixed-`ω` coarea: the pivot-`0` chart integral equals the fixed-`ω` fiber

## Main result

* `lintegral_decoderChartIntegrand_eq_finFiber`:
  `∫ 1_{source₀} ρ₀ Z_d⁻¹ e^{-‖G‖²/(2t)} g(G) dx = finFiber`, where
  `finFiber = ∫dE ∫dν_d(v) ∫dGUE_{d-1}(t)(G') c_{d,t} 𝓡(E,v,F) Re(vᴴDv) |det M|²
  1{N_-(M) + N_-(H_R - E) = α} g(E vvᴴ + U_v(U_vᴴFU_v + G')U_vᴴ - F)`,
  `M = U_vᴴ F U_v + G' - E` (`F = F(E)`, `D = D(E)`), i.e. the Fin-indexed form of
  `coareaFiber`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory
open CoareaNative.BlockBand BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open scoped ENNReal NNReal ComplexConjugate

variable {dR d : ℕ}

/-- The Fin-indexed fixed-`ω` fiber (`coareaFiber` with index `Fin d`). -/
def finFiber (α : ℕ) (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    (V : Matrix (Fin d) (Fin d) ℂ) (t : ℝ≥0) (U : (Fin d → ℂ) → Matrix (Fin d) (Fin (d - 1)) ℂ)
    (g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ E : ℝ, ∫⁻ v, ∫⁻ G',
    fiberIntegrand (U v) (BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V E)
      E v (negativeCount ((hermitianOfFinCoordinates dR R).1 - (E : ℂ) • 1)) α
      (coareaConstant d t * regressionFactor t E v
          (BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V E) *
        (star v ⬝ᵥ (BlockBand.Coarea.physicalCoareaD (hermitianOfFinCoordinates dR R).1 C E *ᵥ
          v)).re) g G'
    ∂gueMeasure (Fin (d - 1)) t ∂projectiveHaar (Fin d)

/-!
## Measurability of the chart integrand
-/

theorem measurable_decoderChartIntegrand (hd : 1 ≤ d) (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (t : ℝ≥0)
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (decoderChartIntegrand hd α R C V t g) := by
  have hdec : Measurable (physicalSelectedSimpleDecode R (⟨0, hd⟩ : Fin d)
      (physicalChartCoupling C ⟨0, hd⟩) (physicalChartPotential V ⟨0, hd⟩)) :=
    measurable_physicalSchurFinCoordinateDecode _ (measurable_physicalCoareaF _ _ _)
  have hρ := measurable_physicalSchurDecoderDensity (d := d) ⟨0, hd⟩
    (hermitianOfFinCoordinates dR R).1 (physicalChartCoupling C ⟨0, hd⟩)
  have hdens := (measurable_hermitianGUEDensity_comp_block d t).comp hdec
  have hmat : Measurable fun x : HermitianCoordinateSpace d =>
      (hermitianOfFinCoordinates d x).1 :=
    measurable_subtype_coe.comp (measurable_hermitianOfFinCoordinates d)
  unfold decoderChartIntegrand
  refine Measurable.indicator ?_ (measurableSet_physicalSelectedSimpleSource α R ⟨0, hd⟩)
  exact (ENNReal.measurable_ofReal.comp hρ).mul (hdens.mul (hg.comp (hmat.comp hdec)))

/-!
## Step 1: Lebesgue chart coordinates and Tonelli
-/

theorem lintegral_decoderChartIntegrand_eq_iterated (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, decoderChartIntegrand hd α R C V t g x =
      ∫⁻ E : ℝ, ∫⁻ z : Fin (d - 1) → ℂ, ∫⁻ b : HermitianCoordinateSpace (d - 1),
        fiberChartIntegrand hd α R C V t g (E, z, b) := by
  set L := chartEquiv d ⟨0, hd⟩
  have hmp := measurePreserving_chartEquiv d hd ⟨0, hd⟩
  have hemb : MeasurableEmbedding L :=
    L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have h1 : ∫⁻ x, decoderChartIntegrand hd α R C V t g x =
      ∫⁻ p, fiberChartIntegrand hd α R C V t g p := by
    rw [← hmp.lintegral_comp_emb hemb]
    refine lintegral_congr fun x => ?_
    rw [← decoderChartIntegrand_chartEquiv_symm hd α R C hV ht g, LinearEquiv.symm_apply_apply]
  have hmeas : Measurable (fiberChartIntegrand hd α R C V t g) := by
    have h := (measurable_decoderChartIntegrand hd α R C V t hg).comp
      (L.symm.toContinuousLinearEquiv.continuous.measurable)
    have heq : decoderChartIntegrand hd α R C V t g ∘ L.symm =
        fiberChartIntegrand hd α R C V t g := by
      funext p
      exact decoderChartIntegrand_chartEquiv_symm hd α R C hV ht g p
    rw [← heq]
    exact h
  rw [h1, Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun E => ?_
  rw [Measure.volume_eq_prod]
  exact lintegral_prod (fun q => fiberChartIntegrand hd α R C V t g (E, q))
    (hmeas.comp measurable_prodMk_left).aemeasurable

/-!
## Step 2: the complementary-block integral
-/

theorem measurable_fiberIntegrand_right {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℂ) (F : Matrix ι ι ℂ) (E : ℝ) (v : ι → ℂ) (nR α : ℕ)
    (K : ℝ) {g : Matrix ι ι ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fiberIntegrand U F E v nR α K g) := by
  have hM : Measurable fun G' : Matrix κ κ ℂ => Uᴴ * F * U + G' - (E : ℂ) • 1 :=
    measurable_matrix_sub (measurable_matrix_add measurable_const measurable_id) measurable_const
  have hdet : Measurable fun G' : Matrix κ κ ℂ =>
      Complex.normSq (Uᴴ * F * U + G' - (E : ℂ) • 1).det :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hM)
  have hrec : Measurable fun G' : Matrix κ κ ℂ =>
      (E : ℂ) • vecMulVec v (star v) + U * (Uᴴ * F * U + G') * Uᴴ - F :=
    measurable_matrix_sub (measurable_matrix_add measurable_const
      (measurable_matrix_mul_rect (measurable_matrix_mul_rect measurable_const
        (measurable_matrix_add measurable_const measurable_id)) measurable_const))
      measurable_const
  unfold fiberIntegrand
  exact ((ENNReal.measurable_ofReal.comp (measurable_const.mul hdet)).mul
    (measurable_indicator_negativeCount hM nR α)).mul (hg.comp hrec)

open Classical in
theorem lintegral_fiberChartIntegrand_b (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g) (E : ℝ)
    (z : Fin (d - 1) → ℂ) :
    ∫⁻ b : HermitianCoordinateSpace (d - 1), fiberChartIntegrand hd α R C V t g (E, z, b) =
      (if (R, E) ∈ coareaExteriorPoleFree dR then 1 else 0) *
        ENNReal.ofReal (((1 + ProjectiveHaar.chartSq z) ^ d)⁻¹) *
        ENNReal.ofReal (gueNormalizer (d - 1) t / gueNormalizer d t) *
        ∫⁻ G', fiberIntegrand (chartFrame ⟨0, hd⟩ z)
          (BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V E) E
          (chartVector ⟨0, hd⟩ z)
          (negativeCount ((hermitianOfFinCoordinates dR R).1 - (E : ℂ) • 1)) α
          (regressionFactor t E (chartVector ⟨0, hd⟩ z)
              (BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V E) *
            (star (chartVector ⟨0, hd⟩ z) ⬝ᵥ
              (BlockBand.Coarea.physicalCoareaD (hermitianOfFinCoordinates dR R).1 C E *ᵥ
                chartVector ⟨0, hd⟩ z)).re) g G' ∂gueMeasure (Fin (d - 1)) t := by
  set H_R := (hermitianOfFinCoordinates dR R).1
  have hHR : H_R.IsHermitian := (hermitianOfFinCoordinates dR R).2
  set F := BlockBand.Coarea.physicalCoareaF H_R C V E
  have hF : F.IsHermitian := physicalCoareaF_isHermitian' hHR C hV E
  set U := chartFrame (⟨0, hd⟩ : Fin d) z
  set v := chartVector (⟨0, hd⟩ : Fin d) z
  set K := regressionFactor t E v F *
    (star v ⬝ᵥ (BlockBand.Coarea.physicalCoareaD H_R C E *ᵥ v)).re
  have hA : (Uᴴ * F * U).IsHermitian := isHermitian_conjTranspose_mul_mul U hF
  have hΘ : Measurable (fiberIntegrand U F E v (negativeCount (H_R - (E : ℂ) • 1)) α K g) :=
    measurable_fiberIntegrand_right U F E v _ α K hg
  have hne1 : (if (R, E) ∈ coareaExteriorPoleFree dR then (1 : ℝ≥0∞) else 0) ≠ ⊤ := by
    split_ifs <;> simp
  unfold fiberChartIntegrand
  simp only
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top hne1 ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top)]
  congr 1
  exact lintegral_translated_gueDensity (d - 1) ht hA hΘ

/-!
## Step 3: the angular integrand and its properties
-/

theorem measurable_regressionFactor {ι : Type*} [Fintype ι] (t E : ℝ) (F : Matrix ι ι ℂ) :
    Measurable (fun v : ι → ℂ => regressionFactor t E v F) := by
  unfold regressionFactor l2Norm
  have hc : Continuous (fun v : ι → ℂ => star v ⬝ᵥ (F *ᵥ v)) := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  have hc2 : Continuous (fun v : ι → ℂ => F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) := by
    refine Continuous.sub ?_ (hc.smul continuous_id)
    exact (Matrix.mulVecLin F).continuous_of_finiteDimensional
  have hc3 : Continuous (fun v : ι → ℂ => Real.sqrt (∑ k,
      ‖(F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) k‖ ^ 2)) := by
    refine Real.continuous_sqrt.comp ?_
    refine continuous_finsetSum _ fun k _ => ?_
    exact ((continuous_apply k).comp hc2).norm.pow 2
  refine Continuous.measurable ?_
  refine Real.continuous_exp.comp ?_
  refine Continuous.div_const ?_ _
  refine Continuous.neg ?_
  exact ((continuous_const.sub (Complex.continuous_re.comp hc)).pow 2).add
    (continuous_const.mul (hc3.pow 2))

theorem measurable_clockSpeed' {ι : Type*} [Fintype ι] (D : Matrix ι ι ℂ) :
    Measurable (fun v : ι → ℂ => (star v ⬝ᵥ (D *ᵥ v)).re) := by
  have hc : Continuous (fun v : ι → ℂ => star v ⬝ᵥ (D *ᵥ v)) := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  exact (Complex.continuous_re.comp hc).measurable

/-- The angular integrand `h_E(v) = 1{‖v‖=1} ∫ fiberIntegrand (U v) … dGUE_{d-1}`. -/
def angularIntegrand (t : ℝ≥0) (U : (Fin d → ℂ) → Matrix (Fin d) (Fin (d - 1)) ℂ)
    (F D : Matrix (Fin d) (Fin d) ℂ) (E : ℝ) (nR α : ℕ) (g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (v : Fin d → ℂ) : ℝ≥0∞ := by
  classical
  exact (if l2Norm v = 1 then 1 else 0) *
    ∫⁻ G', fiberIntegrand (U v) F E v nR α
      (regressionFactor t E v F * (star v ⬝ᵥ (D *ᵥ v)).re) g G' ∂gueMeasure (Fin (d - 1)) t

theorem measurable_angularIntegrand (t : ℝ≥0) {U : (Fin d → ℂ) → Matrix (Fin d) (Fin (d - 1)) ℂ}
    (hU : Measurable U) (F D : Matrix (Fin d) (Fin d) ℂ) (E : ℝ) (nR α : ℕ)
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (angularIntegrand t U F D E nR α g) := by
  classical
  have hK : Measurable fun v : Fin d → ℂ =>
      regressionFactor t E v F * (star v ⬝ᵥ (D *ᵥ v)).re :=
    (measurable_regressionFactor t E F).mul (measurable_clockSpeed' D)
  have h := (measurable_fiberIntegrand (κ := Fin (d - 1)) hU F E nR α hK hg).lintegral_prod_right'
    (ν := gueMeasure (Fin (d - 1)) t)
  have hset : MeasurableSet {v : Fin d → ℂ | l2Norm v = 1} :=
    measurableSet_eq_fun (ProjectiveHaar.continuous_l2Norm (Fin d)).measurable measurable_const
  unfold angularIntegrand
  exact (Measurable.ite hset measurable_const measurable_const).mul h

theorem angularIntegrand_smul (t : ℝ≥0) {U : (Fin d → ℂ) → Matrix (Fin d) (Fin (d - 1)) ℂ}
    (hUf : ∀ v, l2Norm v = 1 → IsFrameOf v (U v)) (F D : Matrix (Fin d) (Fin d) ℂ) (E : ℝ)
    (nR α : ℕ) (g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (c : ℂ) (hc : ‖c‖ = 1)
    (v : Fin d → ℂ) :
    angularIntegrand t U F D E nR α g (c • v) = angularIntegrand t U F D E nR α g v := by
  classical
  unfold angularIntegrand
  rw [l2Norm_smul_of_norm_one hc]
  by_cases hv : l2Norm v = 1
  · simp only [hv, ↓reduceIte, one_mul]
    rw [regressionFactor_smul t E hc v F, quadSpeed_smul hc v D]
    have hcard : Fintype.card (Fin d) = Fintype.card (Fin (d - 1)) + 1 := by
      simp only [Fintype.card_fin]
      have : d ≠ 0 := by
        intro h; subst h
        simp [l2Norm] at hv
      omega
    exact lintegral_fiberIntegrand_phase t hcard (star_dotProduct_self_of_l2Norm hv) hc
      (hUf (c • v) (by rw [l2Norm_smul_of_norm_one hc]; exact hv)) (hUf v hv) F E nR α _ g
  · simp [hv]

/-!
## Step 4: the `z`-integral
-/

open Classical in
theorem lintegral_fiberChartIntegrand_zb (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {U : (Fin d → ℂ) → Matrix (Fin d) (Fin (d - 1)) ℂ} (hU : Measurable U)
    (hUf : ∀ v, l2Norm v = 1 → IsFrameOf v (U v))
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g) (E : ℝ) :
    ∫⁻ z : Fin (d - 1) → ℂ, ∫⁻ b : HermitianCoordinateSpace (d - 1),
        fiberChartIntegrand hd α R C V t g (E, z, b) =
      (if (R, E) ∈ coareaExteriorPoleFree dR then 1 else 0) *
        ENNReal.ofReal (gueNormalizer (d - 1) t / gueNormalizer d t) *
        (ENNReal.ofReal (Real.pi ^ (d - 1) / (d - 1).factorial) *
          ∫⁻ v, angularIntegrand t U
            (BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V E)
            (BlockBand.Coarea.physicalCoareaD (hermitianOfFinCoordinates dR R).1 C E) E
            (negativeCount ((hermitianOfFinCoordinates dR R).1 - (E : ℂ) • 1)) α g v
            ∂projectiveHaar (Fin d)) := by
  set H_R := (hermitianOfFinCoordinates dR R).1
  set F := BlockBand.Coarea.physicalCoareaF H_R C V E
  set D := BlockBand.Coarea.physicalCoareaD H_R C E
  set nR := negativeCount (H_R - (E : ℂ) • 1)
  set h := angularIntegrand t U F D E nR α g
  have hcard : Fintype.card (Fin d) = Fintype.card (Fin (d - 1)) + 1 := by
    simp only [Fintype.card_fin]; omega
  have hpt : ∀ z : Fin (d - 1) → ℂ,
      ∫⁻ b : HermitianCoordinateSpace (d - 1), fiberChartIntegrand hd α R C V t g (E, z, b) =
        ((if (R, E) ∈ coareaExteriorPoleFree dR then 1 else 0) *
          ENNReal.ofReal (gueNormalizer (d - 1) t / gueNormalizer d t)) *
          (ENNReal.ofReal (((1 + ProjectiveHaar.chartSq z) ^ d)⁻¹) *
            h (((Real.sqrt (1 + ProjectiveHaar.chartSq z))⁻¹ : ℂ) • ProjectiveHaar.affineLift z)) := by
    intro z
    rw [lintegral_fiberChartIntegrand_b hd α R C hV ht hg E z]
    have hv1 := l2Norm_chartVector (⟨0, hd⟩ : Fin d) z
    have hframe := lintegral_fiberIntegrand_frame_eq t hcard
      (star_chartVector_dotProduct (⟨0, hd⟩ : Fin d) z)
      (hUf _ hv1) (isFrameOf_chartFrame (⟨0, hd⟩ : Fin d) z) F E nR α
      (regressionFactor t E (chartVector ⟨0, hd⟩ z) F *
        (star (chartVector ⟨0, hd⟩ z) ⬝ᵥ (D *ᵥ chartVector ⟨0, hd⟩ z)).re) g
    rw [hframe, ← chartVector_zero hd z]
    simp only [h, angularIntegrand, hv1, ↓reduceIte, one_mul]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by split_ifs <;> simp) ENNReal.ofReal_ne_top)]
  have hchart := ProjectiveHaar.lintegral_projectiveHaar_affineChart_of_one_le d hd
    (measurable_angularIntegrand t hU F D E nR α hg)
    (fun c hc v => angularIntegrand_smul t hUf F D E nR α g c hc v)
  rw [hchart, ← mul_assoc (ENNReal.ofReal _), ← ENNReal.ofReal_mul (by positivity)]
  have hpi : 0 < Real.pi ^ (d - 1) := by have := Real.pi_pos; positivity
  have hf : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [show Real.pi ^ (d - 1) / ((d - 1).factorial : ℝ) * (((d - 1).factorial : ℝ) /
      Real.pi ^ (d - 1)) = 1 by field_simp, ENNReal.ofReal_one, one_mul]

/-!
## Step 5: assembly
-/

theorem fiberIntegrand_const_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {c : ℝ} (hc : 0 ≤ c) (U : Matrix ι κ ℂ) (F : Matrix ι ι ℂ) (E : ℝ)
    (v : ι → ℂ) (nR α : ℕ) (K : ℝ) (g : Matrix ι ι ℂ → ℝ≥0∞) (G' : Matrix κ κ ℂ) :
    ENNReal.ofReal c * fiberIntegrand U F E v nR α K g G' =
      fiberIntegrand U F E v nR α (c * K) g G' := by
  unfold fiberIntegrand
  rw [mul_assoc c K, ENNReal.ofReal_mul hc]
  ring

theorem ae_poleFree (R : HermitianCoordinateSpace dR) :
    ∀ᵐ E : ℝ, (R, E) ∈ coareaExteriorPoleFree dR := by
  have hfin : {E : ℝ | (R, E) ∉ coareaExteriorPoleFree dR} ⊆
      Set.range (fun r : Fin (Fintype.card (Fin dR)) =>
        orderedEigenvalue (hermitianOfFinCoordinates dR R) r) := by
    intro E hE
    simp only [coareaExteriorPoleFree, Set.mem_ofPred_eq, not_forall, not_not] at hE
    obtain ⟨r, hr⟩ := hE
    exact ⟨r, hr⟩
  rw [ae_iff]
  exact measure_mono_null hfin ((Set.finite_range _).measure_zero volume)

/-- **The pivot-`0` chart integral is the fixed-`ω` fiber** (Fin-indexed). -/
theorem lintegral_decoderChartIntegrand_eq_finFiber (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {U : (Fin d → ℂ) → Matrix (Fin d) (Fin (d - 1)) ℂ} (hU : Measurable U)
    (hUf : ∀ v, l2Norm v = 1 → IsFrameOf v (U v))
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, decoderChartIntegrand hd α R C V t g x = finFiber α R C V t U g := by
  classical
  rw [lintegral_decoderChartIntegrand_eq_iterated hd α R C hV ht hg]
  unfold finFiber
  have hc : 0 ≤ coareaConstant d t := by unfold coareaConstant; positivity
  have hconst : ENNReal.ofReal (gueNormalizer (d - 1) t / gueNormalizer d t) *
      ENNReal.ofReal (Real.pi ^ (d - 1) / (d - 1).factorial) =
      ENNReal.ofReal (coareaConstant d t) := by
    rw [← ENNReal.ofReal_mul (by unfold gueNormalizer; positivity), mul_comm,
      projectiveJacobian_mul_gueNormalizerRatio (by omega) (NNReal.coe_pos.2 ht)]
    rfl
  have hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine lintegral_congr_ae ?_
  filter_upwards [ae_poleFree R] with E hE
  rw [lintegral_fiberChartIntegrand_zb hd α R C hV ht hU hUf hg E]
  simp only [hE, ↓reduceIte, one_mul]
  rw [← mul_assoc, hconst, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [ProjectiveHaar.ae_l2Norm_projectiveHaar (Fin d)] with v hv
  simp only [angularIntegrand, hv, ↓reduceIte, one_mul]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun G' => ?_
  rw [fiberIntegrand_const_mul hc, mul_assoc]

end BlockBand.Coarea.FixedOmega
