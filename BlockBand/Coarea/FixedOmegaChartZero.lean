module

public import BlockBand.Coarea.FixedOmegaGaussian

/-!
# Fixed-`ω` coarea: the pivot-`0` chart integrand in fiber form

The chart integrand on the pivot-`0` projective chart, composed with the inverse chart, equals
the fiber integrand (Gaussian norm splitting with the rank sector).

## Main results

* `physicalCoareaF_isHermitian'`, `clockSpeed_nonneg'`: `F(E)` is Hermitian (every `E`; the
  resolvent is totalized) and `Re(vᴴ D(E) v) ≥ 0`.
* `decoderChartIntegrand_chartEquiv_symm`: the pointwise chart identity.
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

/-- `F(E) = V - Cᴴ(H_R - E)⁻¹C` is Hermitian for every real `E` (generic indices). -/
theorem physicalCoareaF_isHermitian' {α β : Type*} [Fintype α] [DecidableEq α]
    {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ) {V : Matrix β β ℂ}
    (hV : V.IsHermitian) (E : ℝ) :
    (BlockBand.Coarea.physicalCoareaF H_R C V E).IsHermitian := by
  unfold BlockBand.Coarea.physicalCoareaF BlockBand.Coarea.physicalCoareaResolvent
  have h1 : (H_R - (E : ℂ) • 1).IsHermitian :=
    hH.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  exact hV.sub (isHermitian_conjTranspose_mul_mul C h1.inv)

/-- The crossing speed `Re(vᴴ D(E) v)` is nonnegative. -/
theorem clockSpeed_nonneg' {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (H_R : Matrix α α ℂ) (C : Matrix α β ℂ) (E : ℝ) (v : β → ℂ) :
    0 ≤ (star v ⬝ᵥ (BlockBand.Coarea.physicalCoareaD H_R C E *ᵥ v)).re := by
  unfold BlockBand.Coarea.physicalCoareaD BlockBand.Coarea.schurClock
  set T := BlockBand.Coarea.physicalCoareaT H_R C E
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Complex.add_re, ← l2Norm_sq_eq_re,
    ← l2Norm_sq_eq_re]
  positivity

/-!
## Measurability of the Jacobian density
-/

theorem measurable_canonicalProjectiveUnitVector_apply {d : ℕ} (a : Unit ⊕ Fin (d - 1)) :
    Measurable (fun z : Fin (d - 1) → ℂ => canonicalProjectiveUnitVector z a) := by
  have h : Continuous (fun z : Fin (d - 1) → ℂ => physicalCoareaFrame z a (Sum.inl ())) :=
    (continuous_apply_apply a (Sum.inl ())).comp continuous_physicalCoareaFrame
  simp_rw [physicalCoareaFrame_apply_inl] at h
  exact h.measurable

theorem measurable_physicalSchurDecoderDensity {d dR : ℕ} (i : Fin d)
    (H_R : Matrix (Fin dR) (Fin dR) ℂ) (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      physicalSchurDecoderDensity i (CoareaNative.BlockBand.physicalCoareaT H_R C) x) := by
  have hy := measurable_eigenpairIncidenceCoordinates_complete i
  have hE : Measurable (fun x : HermitianCoordinateSpace d =>
      (eigenpairIncidenceCoordinates i x).1) := measurable_fst.comp hy
  have hz : Measurable (fun x : HermitianCoordinateSpace d =>
      (eigenpairIncidenceCoordinates i x).2.1) := measurable_fst.comp (measurable_snd.comp hy)
  have hgap := measurable_eigenpairIncidenceGapMatrix (d := d) i
  have hdet : Measurable (fun x : HermitianCoordinateSpace d =>
      Complex.normSq (eigenpairGapMatrix (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2.1).det) :=
    Complex.continuous_normSq.measurable.comp ((continuous_id.matrix_det).measurable.comp hgap)
  have hpa : Measurable (fun x : HermitianCoordinateSpace d =>
      canonicalProjectiveAffineDensity (d := d) (eigenpairIncidenceCoordinates i x).2.1) := by
    have hc : Measurable (fun z : Fin (d - 1) → ℂ => canonicalProjectiveAffineDensity (d := d) z) := by
      unfold canonicalProjectiveAffineDensity projectiveAffineDensity projectiveAffineRadiusSq
      refine Measurable.pow_const (Measurable.inv (measurable_const.add ?_)) _
      refine Finset.measurable_sum _ fun j _ => ?_
      exact Complex.continuous_normSq.measurable.comp
        ((measurable_pi_apply j).comp
          (canonicalProjectiveChartCoordinatesLinearMap (n := Fin (d - 1))).continuous_of_finiteDimensional.measurable)
    exact hc.comp hz
  have hT : Measurable (fun x : HermitianCoordinateSpace d =>
      CoareaNative.BlockBand.schurClock
        (CoareaNative.BlockBand.physicalCoareaT H_R C (eigenpairIncidenceCoordinates i x).1)) := by
    have h0 := (measurable_physicalCoareaT H_R C).comp hE
    unfold CoareaNative.BlockBand.schurClock
    exact measurable_matrix_add measurable_const
      (measurable_matrix_mul_rect (Measurable.matrix_conjTranspose h0) h0)
  have hu : ∀ a, Measurable (fun x : HermitianCoordinateSpace d =>
      canonicalProjectiveUnitVector (eigenpairIncidenceCoordinates i x).2.1 a) :=
    fun a => (measurable_canonicalProjectiveUnitVector_apply a).comp hz
  have hq : Measurable (fun x : HermitianCoordinateSpace d =>
      physicalEigenpairCrossingQuadratic
        (CoareaNative.BlockBand.physicalCoareaT H_R C (eigenpairIncidenceCoordinates i x).1)
        (eigenpairIncidenceCoordinates i x).2.1) := by
    unfold physicalEigenpairCrossingQuadratic
    refine Complex.measurable_re.comp ?_
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine Finset.measurable_sum _ fun a _ => ?_
    refine (Complex.continuous_conj.measurable.comp (hu a)).mul ?_
    refine Finset.measurable_sum _ fun b _ => ?_
    exact (Matrix.measurable_iff.mp hT a b).mul (hu b)
  unfold physicalSchurDecoderDensity
  exact (hpa.mul hdet).mul hq

/-!
## The pointwise chart integrand
-/

section ChartZero

variable {dR d : ℕ}

/-- The pivot-`0` chart integrand (source indicator, Jacobian, GUE density, `g`). -/
def decoderChartIntegrand (hd : 1 ≤ d) (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (t : ℝ≥0)
    (g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) : HermitianCoordinateSpace d → ℝ≥0∞ :=
  (physicalSelectedSimpleSource α R (⟨0, hd⟩ : Fin d)).indicator fun x =>
    ENNReal.ofReal (physicalSchurDecoderDensity (⟨0, hd⟩ : Fin d)
        (CoareaNative.BlockBand.physicalCoareaT (hermitianOfFinCoordinates dR R).1
          (physicalChartCoupling C ⟨0, hd⟩)) x) *
      (hermitianGUEDensity d t (hermitianOfFinCoordinates d
          (physicalSelectedSimpleDecode R ⟨0, hd⟩ (physicalChartCoupling C ⟨0, hd⟩)
            (physicalChartPotential V ⟨0, hd⟩) x)) *
        g (hermitianOfFinCoordinates d
          (physicalSelectedSimpleDecode R ⟨0, hd⟩ (physicalChartCoupling C ⟨0, hd⟩)
            (physicalChartPotential V ⟨0, hd⟩) x)).1)

open Classical in
/-- The fiber form of the chart integrand at `(E, z, b)`. -/
def fiberChartIntegrand (hd : 1 ≤ d) (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (t : ℝ≥0)
    (g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (p : ChartSpace d) : ℝ≥0∞ :=
  let E := p.1
  let z := p.2.1
  let B := (hermitianOfFinCoordinates (d - 1) p.2.2).1
  let H_R := (hermitianOfFinCoordinates dR R).1
  let F := BlockBand.Coarea.physicalCoareaF H_R C V E
  let v := chartVector (⟨0, hd⟩ : Fin d) z
  let U := chartFrame (⟨0, hd⟩ : Fin d) z
  let A := Uᴴ * F * U
  (if (R, E) ∈ coareaExteriorPoleFree dR then 1 else 0) *
    ENNReal.ofReal (((1 + ProjectiveHaar.chartSq z) ^ d)⁻¹) *
    ENNReal.ofReal (gueNormalizer (d - 1) t / gueNormalizer d t) *
    (ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq (B - A) / (2 * t)) /
        gueNormalizer (d - 1) t) *
      fiberIntegrand U F E v (negativeCount (H_R - (E : ℂ) • 1)) α
        (regressionFactor t E v F *
          (star v ⬝ᵥ (BlockBand.Coarea.physicalCoareaD H_R C E *ᵥ v)).re) g (B - A))

theorem det_eigenpairGapMatrix_normSq {n : Type*} [Fintype n] [DecidableEq n] (E : ℝ)
    (B : Matrix n n ℂ) :
    Complex.normSq (eigenpairGapMatrix E B).det = Complex.normSq (B - (E : ℂ) • 1).det := by
  unfold eigenpairGapMatrix
  rw [show (E : ℂ) • (1 : Matrix n n ℂ) - B = -(B - (E : ℂ) • 1) by abel, Matrix.det_neg,
    Complex.normSq_mul, map_pow, Complex.normSq_neg, Complex.normSq_one, one_pow,
    one_mul]

/-- **Pointwise chart identity** (Gaussian norm splitting with the rank sector). -/
theorem decoderChartIntegrand_chartEquiv_symm (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    (g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (p : ChartSpace d) :
    decoderChartIntegrand hd α R C V t g ((chartEquiv d ⟨0, hd⟩).symm p) =
      fiberChartIntegrand hd α R C V t g p := by
  classical
  unfold decoderChartIntegrand fiberChartIntegrand
  simp only
  set i0 : Fin d := ⟨0, hd⟩
  set x := (chartEquiv d i0).symm p
  have hinc := eigenpairIncidenceCoordinates_chartEquiv_symm d i0 p
  set E := p.1
  set z := p.2.1
  set B := (hermitianOfFinCoordinates (d - 1) p.2.2).1
  set H_R := (hermitianOfFinCoordinates dR R).1
  have hHR : H_R.IsHermitian := (hermitianOfFinCoordinates dR R).2
  set F := BlockBand.Coarea.physicalCoareaF H_R C V E
  have hF : F.IsHermitian := physicalCoareaF_isHermitian' hHR C hV E
  set v := chartVector i0 z
  set U := chartFrame i0 z
  have hU : IsFrameOf v U := isFrameOf_chartFrame i0 z
  have hv : star v ⬝ᵥ v = 1 := star_chartVector_dotProduct i0 z
  set A := Uᴴ * F * U
  set sp := (star v ⬝ᵥ (BlockBand.Coarea.physicalCoareaD H_R C E *ᵥ v)).re
  have hsp : 0 ≤ sp := clockSpeed_nonneg' H_R C E v
  have hcard : Fintype.card (Fin d) = Fintype.card (Fin (d - 1)) + 1 := by
    simp only [Fintype.card_fin]; omega
  -- the decoded matrix
  have hG : (hermitianOfFinCoordinates d (physicalSelectedSimpleDecode R i0
      (physicalChartCoupling C i0) (physicalChartPotential V i0) x)).1 =
      (E : ℂ) • vecMulVec v (star v) + U * (Uᴴ * F * U + (B - A)) * Uᴴ - F := by
    rw [hermitianOfFinCoordinates_physicalSelectedSimpleDecode R C V hV i0 x, hinc]
    simp only [A, add_sub_cancel]
    rfl
  have hM : Uᴴ * F * U + (B - A) - (E : ℂ) • 1 = B - (E : ℂ) • 1 := by
    simp only [A]; abel
  have hρ : physicalSchurDecoderDensity i0
      (CoareaNative.BlockBand.physicalCoareaT H_R (physicalChartCoupling C i0)) x =
      ((1 + ProjectiveHaar.chartSq z) ^ d)⁻¹ * Complex.normSq (B - (E : ℂ) • 1).det * sp := by
    unfold physicalSchurDecoderDensity
    rw [hinc, physicalEigenpairCrossingQuadratic_eq, canonicalProjectiveAffineDensity_eq hd,
      det_eigenpairGapMatrix_normSq]
  have hHS : hilbertSchmidtNormSq ((E : ℂ) • vecMulVec v (star v) +
      U * (Uᴴ * F * U + (B - A)) * Uᴴ - F) =
      ((E - (star v ⬝ᵥ (F *ᵥ v)).re) ^ 2 + 2 * l2Norm (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ^ 2) +
        hilbertSchmidtNormSq (B - A) := by
    rw [hilbertSchmidtNormSq_reconstructed hcard hv hU hF E (B - A)]
  have hmem : x ∈ physicalSelectedSimpleSource α R i0 ↔
      (Complex.normSq (B - (E : ℂ) • 1).det ≠ 0 ∧
        negativeCount (H_R - (E : ℂ) • 1) + negativeCount (B - (E : ℂ) • 1) = α) ∧
      (R, E) ∈ coareaExteriorPoleFree dR := by
    change ((eigenpairGapMatrix (eigenpairIncidenceCoordinates i0 x).1
        (eigenpairIncidenceCoordinates i0 x).2.2.1).det ≠ 0 ∧
      physicalEigenpairFixedRank α R (eigenpairIncidenceCoordinates i0 x).1
        (eigenpairIncidenceCoordinates i0 x).2.2 ∧
      (R, (eigenpairIncidenceCoordinates i0 x).1) ∈ coareaExteriorPoleFree dR) ↔ _
    rw [hinc, physicalEigenpairFixedRank_iff]
    have h1 : (eigenpairGapMatrix E B).det ≠ 0 ↔ Complex.normSq (B - (E : ℂ) • 1).det ≠ 0 := by
      rw [← det_eigenpairGapMatrix_normSq, ne_eq, ne_eq, Complex.normSq_eq_zero]
    rw [h1]
    tauto
  have hZ : 0 < gueNormalizer d t := by unfold gueNormalizer; positivity
  have hZ' : 0 < gueNormalizer (d - 1) t := by unfold gueNormalizer; positivity
  have ht' : (0 : ℝ) < t := ht
  rw [Set.indicator_apply]
  by_cases hpf : (R, E) ∈ coareaExteriorPoleFree dR
  · simp only [hpf, ite_true, one_mul]
    unfold fiberIntegrand
    rw [hM]
    by_cases hS : x ∈ physicalSelectedSimpleSource α R i0
    · simp only [hS, ↓reduceIte]
      obtain ⟨⟨_, hrank⟩, _⟩ := hmem.1 hS
      have hrank' : negativeCount (B - (E : ℂ) • 1) + negativeCount (H_R - (E : ℂ) • 1) = α := by
        omega
      simp only [hrank', ↓reduceIte, mul_one]
      rw [hρ, hermitianGUEDensity, hG, hHS]
      have hsplit : Real.exp (-((((E - (star v ⬝ᵥ (F *ᵥ v)).re) ^ 2 +
          2 * l2Norm (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ^ 2) +
            hilbertSchmidtNormSq (B - A))) / (2 * t)) / gueNormalizer d t =
          gueNormalizer (d - 1) t / gueNormalizer d t *
            (Real.exp (-hilbertSchmidtNormSq (B - A) / (2 * t)) / gueNormalizer (d - 1) t) *
            regressionFactor t E v F := by
        unfold regressionFactor
        simp only
        rw [show -((((E - (star v ⬝ᵥ (F *ᵥ v)).re) ^ 2 +
            2 * l2Norm (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ^ 2) +
              hilbertSchmidtNormSq (B - A))) / (2 * t) =
            -((E - (star v ⬝ᵥ (F *ᵥ v)).re) ^ 2 +
              2 * l2Norm (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) ^ 2) / (2 * t) +
            -hilbertSchmidtNormSq (B - A) / (2 * t) by ring, Real.exp_add]
        field_simp
      rw [hsplit]
      have hR0 : 0 ≤ regressionFactor t E v F := by unfold regressionFactor; positivity
      have he0 : 0 ≤ Real.exp (-hilbertSchmidtNormSq (B - A) / (2 * t)) /
          gueNormalizer (d - 1) t := by positivity
      have hq0 : 0 ≤ gueNormalizer (d - 1) t / gueNormalizer d t := by positivity
      have hn0 : 0 ≤ Complex.normSq (B - (E : ℂ) • 1).det := Complex.normSq_nonneg _
      have hp0 : 0 ≤ ((1 + ProjectiveHaar.chartSq z) ^ d)⁻¹ := by
        have := ProjectiveHaar.chartSq_nonneg z; positivity
      rw [ENNReal.ofReal_mul (mul_nonneg hp0 hn0), ENNReal.ofReal_mul hp0,
        ENNReal.ofReal_mul (mul_nonneg hq0 he0), ENNReal.ofReal_mul hq0,
        ENNReal.ofReal_mul (mul_nonneg hR0 hsp), ENNReal.ofReal_mul hR0]
      ring
    · simp only [hS, ↓reduceIte]
      have hnot : ¬ (Complex.normSq (B - (E : ℂ) • 1).det ≠ 0 ∧
          negativeCount (H_R - (E : ℂ) • 1) + negativeCount (B - (E : ℂ) • 1) = α) := by
        intro h; exact hS (hmem.2 ⟨h, hpf⟩)
      by_cases hrank : negativeCount (H_R - (E : ℂ) • 1) + negativeCount (B - (E : ℂ) • 1) = α
      · have hdet0 : Complex.normSq (B - (E : ℂ) • 1).det = 0 := by
          by_contra h; exact hnot ⟨h, hrank⟩
        rw [hdet0, mul_zero, ENNReal.ofReal_zero]
        simp
      · have hrank' : ¬ negativeCount (B - (E : ℂ) • 1) + negativeCount (H_R - (E : ℂ) • 1) = α := by
          omega
        simp only [hrank', ↓reduceIte, mul_zero, zero_mul]
  · have hS : x ∉ physicalSelectedSimpleSource α R i0 := fun h => hpf (hmem.1 h).2
    simp [hS, hpf]

end ChartZero

end BlockBand.Coarea.FixedOmega
