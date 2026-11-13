module

public import BlockBand.Coarea.Native.BlockBand.Coarea.GaussianSplitLaw
public import BlockBand.Coarea.Native.BlockBand.Coarea.GaussianDensityFactor
public import BlockBand.Coarea.Native.BlockBand.Coarea.HermitianSimpleSpectrum
public import Mathlib.Probability.Independence.Integration

/-!
# Physical finite-product Hermitian Gaussian split

This module upgrades the scalar variance split to an explicit finite product.
The fresh variable is carried by the product of the diagonal `N(0,t)` laws and
the two strict-upper `N(0,t/2)` laws.  Reconstruction therefore gives an
explicit Hermitian GUE matrix.
On the product with residual and exterior data we define `H_SS = V + G`, prove
the exact identity and independence, and give the Tonelli formula used when
fixed-exterior coarea is applied.

The density convention is
`Z_d(t)⁻¹ exp (-Tr(G²)/(2t))`, with the exact normalizer
`Z_d(t) = gueNormalizer d t`.  All statements are at fixed finite `d` and
positive `t`; no limiting or uniformity assertion is present.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Variance of one real finite Hermitian coordinate in a GUE block: `t` on
its diagonal and `t/2` on each real or imaginary strict-upper coordinate. -/
def hermitianGUEFinCoordinateVariance (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) : NNReal :=
  match (hermitianCoordinateEquivFin d).symm k with
  | .inl _ => ⟨t, ht⟩
  | .inr _ => ⟨t / 2, div_nonneg ht (by norm_num)⟩

/-- The explicit finite product of all real GUE coordinate laws. -/
def hermitianGUECoordinateMeasure (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure (HermitianCoordinateSpace d) :=
  Measure.pi fun k => gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht k)

instance hermitianGUECoordinateMeasure.instIsProbabilityMeasure
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IsProbabilityMeasure (hermitianGUECoordinateMeasure d t ht) := by
  unfold hermitianGUECoordinateMeasure
  infer_instance

/-- The fresh Hermitian GUE matrix reconstructed from the independent real
coordinates. -/
def hermitianGUEBlock (d : ℕ) (x : HermitianCoordinateSpace d) :
    HermitianMatrix (Fin d) :=
  hermitianOfFinCoordinates d x

/-- The fresh block is Hermitian pointwise. -/
theorem hermitianGUEBlock_isHermitian (d : ℕ)
    (x : HermitianCoordinateSpace d) :
    (hermitianGUEBlock d x).1.IsHermitian :=
  (hermitianGUEBlock d x).2

/-- Reconstruction of the finite-product GUE block is Borel measurable. -/
theorem measurable_hermitianGUEBlock (d : ℕ) :
    Measurable (hermitianGUEBlock d) :=
  measurable_hermitianOfFinCoordinates d

/-- Every finite real coordinate has the required centered Gaussian marginal. -/
theorem hermitianGUECoordinate_hasLaw (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) :
    HasLaw (fun x : HermitianCoordinateSpace d => x k)
      (gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht k))
      (hermitianGUECoordinateMeasure d t ht) := by
  refine ⟨measurable_pi_apply k |>.aemeasurable, ?_⟩
  exact (measurePreserving_eval
    (fun j => gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht j)) k).map_eq

/-- The complete real coordinate family of the explicit GUE block is mutually
independent. -/
theorem iIndepFun_hermitianGUECoordinates (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iIndepFun (fun k (x : HermitianCoordinateSpace d) => x k)
      (hermitianGUECoordinateMeasure d t ht) := by
  unfold hermitianGUECoordinateMeasure
  apply iIndepFun_pi
    (X := fun _ : Fin (Fintype.card (HermitianCoordinate d)) => id)
  intro k
  exact measurable_id.aemeasurable

/-- The exact matrix density in the paper's normalization.  The product
construction above supplies its probability normalization coordinate by
coordinate; this expression records the equivalent GUE matrix convention used
by coarea. -/
def hermitianGUEDensity (d : ℕ) (t : ℝ)
    (G : HermitianMatrix (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-hilbertSchmidtNormSq G.1 / (2 * t)) / gueNormalizer d t)

/-- The GUE density displays exactly `Z_d(t)` and the Hilbert–Schmidt
quadratic exponent. -/
theorem hermitianGUEDensity_eq (d : ℕ) (t : ℝ)
    (G : HermitianMatrix (Fin d)) :
    hermitianGUEDensity d t G =
      ENNReal.ofReal
        (Real.exp (-hilbertSchmidtNormSq G.1 / (2 * t)) /
          ((2 * Real.pi * t) ^ ((d : ℝ) / 2) *
            (Real.pi * t) ^ (((d : ℝ) * ((d : ℝ) - 1)) / 2))) := by
  rfl

/-- A strict-upper coordinate of the two-block exposed pair lies either
inside one of the two `W × W` diagonal blocks or in the bond between them. -/
def exposedPairSamePhysicalBlock {W : ℕ}
    (ij : StrictUpperIndex (2 * W)) : Prop :=
  (ij.1.1.val < W) = (ij.1.2.val < W)

instance {W : ℕ} (ij : StrictUpperIndex (2 * W)) :
    Decidable (exposedPairSamePhysicalBlock ij) := by
  unfold exposedPairSamePhysicalBlock
  infer_instance

/-- Residual variance of every real coordinate of the physical two-block
Hermitian exposed pair. -/
def physicalExposedPairResidualCoordinateVariance
    (p : Params) {s : ℝ} (_hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) : NNReal :=
  match (hermitianCoordinateEquivFin (2 * p.W)).symm k with
  | .inl _ => coareaDiagonalResidualVarianceNNReal p hsc
  | .inr (.inl ij) =>
      if exposedPairSamePhysicalBlock ij then
        coareaDiagonalResidualVarianceNNReal p hsc / 2
      else coareaBondResidualVarianceNNReal p hsb / 2
  | .inr (.inr ij) =>
      if exposedPairSamePhysicalBlock ij then
        coareaDiagonalResidualVarianceNNReal p hsc / 2
      else coareaBondResidualVarianceNNReal p hsb / 2

/-- Original physical variance of every real coordinate of the two-block
Hermitian exposed pair. -/
def physicalExposedPairCoordinateVariance
    (p : Params)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) : NNReal :=
  match (hermitianCoordinateEquivFin (2 * p.W)).symm k with
  | .inl _ => ⟨p.diagonalVariance, p.diagonalVariance_pos.le⟩
  | .inr (.inl ij) =>
      if exposedPairSamePhysicalBlock ij then
        ⟨p.diagonalVariance / 2, div_nonneg p.diagonalVariance_pos.le (by norm_num)⟩
      else ⟨p.bondVariance / 2, div_nonneg p.bondVariance_pos.le (by norm_num)⟩
  | .inr (.inr ij) =>
      if exposedPairSamePhysicalBlock ij then
        ⟨p.diagonalVariance / 2, div_nonneg p.diagonalVariance_pos.le (by norm_num)⟩
      else ⟨p.bondVariance / 2, div_nonneg p.bondVariance_pos.le (by norm_num)⟩

/-- Coordinatewise, physical residual variance plus the fresh GUE variance is
exactly the original two-block Hermitian variance.  This is the finite-product
upgrade of the two scalar laws in `GaussianSplitLaw`. -/
theorem physicalExposedPairResidual_add_fresh
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) :
    physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k +
        hermitianGUEFinCoordinateVariance (2 * p.W)
          (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) k =
      physicalExposedPairCoordinateVariance p k := by
  generalize hc : (hermitianCoordinateEquivFin (2 * p.W)).symm k = c
  rcases c with i | c
  · simp only [physicalExposedPairResidualCoordinateVariance,
      hermitianGUEFinCoordinateVariance, physicalExposedPairCoordinateVariance,
      hc]
    change coareaDiagonalResidualVarianceNNReal p hsc +
        coareaGUEVarianceNNReal p hs0 =
      ⟨p.diagonalVariance, p.diagonalVariance_pos.le⟩
    exact coareaDiagonalResidualVarianceNNReal_add p hs0 hsc
  · rcases c with ij | ij
    · by_cases h : exposedPairSamePhysicalBlock ij
      · simp only [physicalExposedPairResidualCoordinateVariance,
          hermitianGUEFinCoordinateVariance, physicalExposedPairCoordinateVariance,
          hc, h, ↓reduceIte]
        apply NNReal.eq
        change coareaDiagonalResidualVariance p s / 2 +
            coareaGUEVariance p s / 2 = p.diagonalVariance / 2
        unfold coareaDiagonalResidualVariance
        ring
      · simp only [physicalExposedPairResidualCoordinateVariance,
          hermitianGUEFinCoordinateVariance, physicalExposedPairCoordinateVariance,
          hc, h, ↓reduceIte]
        apply NNReal.eq
        change coareaBondResidualVariance p s / 2 +
            coareaGUEVariance p s / 2 = p.bondVariance / 2
        unfold coareaBondResidualVariance
        ring
    · by_cases h : exposedPairSamePhysicalBlock ij
      · simp only [physicalExposedPairResidualCoordinateVariance,
          hermitianGUEFinCoordinateVariance, physicalExposedPairCoordinateVariance,
          hc, h, ↓reduceIte]
        apply NNReal.eq
        change coareaDiagonalResidualVariance p s / 2 +
            coareaGUEVariance p s / 2 = p.diagonalVariance / 2
        unfold coareaDiagonalResidualVariance
        ring
      · simp only [physicalExposedPairResidualCoordinateVariance,
          hermitianGUEFinCoordinateVariance, physicalExposedPairCoordinateVariance,
          hc, h, ↓reduceIte]
        apply NNReal.eq
        change coareaBondResidualVariance p s / 2 +
            coareaGUEVariance p s / 2 = p.bondVariance / 2
        unfold coareaBondResidualVariance
        ring

/-- Explicit finite product law of the physical residual exposed pair. -/
def physicalExposedPairResidualMeasure
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b) :
    Measure (HermitianCoordinateSpace (2 * p.W)) :=
  Measure.pi fun k => gaussianReal 0
    (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k)

instance physicalExposedPairResidualMeasure.instIsProbabilityMeasure
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b) :
    IsProbabilityMeasure
      (physicalExposedPairResidualMeasure p hs0 hsc hsb) := by
  unfold physicalExposedPairResidualMeasure
  infer_instance

/-- Every real coordinate of `V + G` has exactly its original physical
Gaussian law.  Mutual finite-product independence is built into the two
explicit product measures; the only probabilistic input is Mathlib's scalar
Gaussian convolution theorem already used in `GaussianSplitLaw`. -/
theorem physicalExposedPairCoordinate_add_hasLaw
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) :
    HasLaw
      (fun z : HermitianCoordinateSpace (2 * p.W) ×
          HermitianCoordinateSpace (2 * p.W) => z.1 k + z.2 k)
      (gaussianReal 0 (physicalExposedPairCoordinateVariance p k))
      ((physicalExposedPairResidualMeasure p hs0 hsc hsb).prod
        (hermitianGUECoordinateMeasure (2 * p.W) (coareaGUEVariance p s)
          (coareaGUEVariance_nonneg p hs0))) := by
  let μV := physicalExposedPairResidualMeasure p hs0 hsc hsb
  let μG := hermitianGUECoordinateMeasure (2 * p.W)
    (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0)
  have hVbase : HasLaw
      (fun x : HermitianCoordinateSpace (2 * p.W) => x k)
      (gaussianReal 0
        (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k)) μV := by
    exact (measurePreserving_eval
      (fun j => gaussianReal 0
        (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb j)) k).hasLaw
  have hGbase : HasLaw
      (fun x : HermitianCoordinateSpace (2 * p.W) => x k)
      (gaussianReal 0
        (hermitianGUEFinCoordinateVariance (2 * p.W)
          (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) k)) μG := by
    exact (measurePreserving_eval
      (fun j => gaussianReal 0
        (hermitianGUEFinCoordinateVariance (2 * p.W)
          (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) j)) k).hasLaw
  have hV : HasLaw
      (fun z : HermitianCoordinateSpace (2 * p.W) ×
          HermitianCoordinateSpace (2 * p.W) => z.1 k)
      (gaussianReal 0
        (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k))
      (μV.prod μG) :=
    hVbase.fun_comp (measurePreserving_fst.hasLaw)
  have hG : HasLaw
      (fun z : HermitianCoordinateSpace (2 * p.W) ×
          HermitianCoordinateSpace (2 * p.W) => z.2 k)
      (gaussianReal 0
        (hermitianGUEFinCoordinateVariance (2 * p.W)
          (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) k))
      (μV.prod μG) :=
    hGbase.fun_comp (measurePreserving_snd.hasLaw)
  have hind : IndepFun
      (fun z : HermitianCoordinateSpace (2 * p.W) ×
          HermitianCoordinateSpace (2 * p.W) => z.1 k)
      (fun z : HermitianCoordinateSpace (2 * p.W) ×
          HermitianCoordinateSpace (2 * p.W) => z.2 k)
      (μV.prod μG) :=
    indepFun_prod (measurable_pi_apply k) (measurable_pi_apply k)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hV hG
  rw [physicalExposedPairResidual_add_fresh p hs0 hsc hsb k] at hsum
  refine ⟨((measurable_pi_apply k).comp measurable_fst).add
    ((measurable_pi_apply k).comp measurable_snd) |>.aemeasurable, ?_⟩
  change Measure.map ((fun z => z.1 k) + fun z => z.2 k) (μV.prod μG) =
    gaussianReal 0 (physicalExposedPairCoordinateVariance p k)
  convert hsum using 1
  norm_num

/-- Sample space for the physical split: residual Hermitian coordinates,
exterior data, and an independently adjoined fresh GUE coordinate vector. -/
abbrev PhysicalHermitianSplitSample (d : ℕ) (Ξ : Type*) :=
  (HermitianCoordinateSpace d × Ξ) × HermitianCoordinateSpace d

/-- Addition in the real vector space of Hermitian matrices, packaged without
leaving the Hermitian subtype. -/
def hermitianMatrixAdd {d : ℕ}
    (A B : HermitianMatrix (Fin d)) : HermitianMatrix (Fin d) :=
  ⟨A.1 + B.1, A.2.add B.2⟩

/-- Product law of residual coordinates, exterior data, and fresh GUE noise. -/
def physicalHermitianSplitMeasure {Ξ : Type*} [MeasurableSpace Ξ]
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (residualLaw : Measure (HermitianCoordinateSpace d))
    (exteriorLaw : Measure Ξ) : Measure (PhysicalHermitianSplitSample d Ξ) :=
  (residualLaw.prod exteriorLaw).prod (hermitianGUECoordinateMeasure d t ht)

/-- Residual Hermitian matrix `V` in the exposed-pair split. -/
def physicalHermitianResidual {d : ℕ} {Ξ : Type*}
    (ω : PhysicalHermitianSplitSample d Ξ) : HermitianMatrix (Fin d) :=
  hermitianOfFinCoordinates d ω.1.1

/-- Fresh GUE matrix `G` in the exposed-pair split. -/
def physicalHermitianFreshGUE {d : ℕ} {Ξ : Type*}
    (ω : PhysicalHermitianSplitSample d Ξ) : HermitianMatrix (Fin d) :=
  hermitianGUEBlock d ω.2

/-- The assembled exposed-pair block `H_SS = V + G`. -/
def physicalHermitianExposedPair {d : ℕ} {Ξ : Type*}
    (ω : PhysicalHermitianSplitSample d Ξ) : HermitianMatrix (Fin d) :=
  hermitianMatrixAdd (physicalHermitianResidual ω) (physicalHermitianFreshGUE ω)

/-- Matrix-level exposed-pair assembly identity. -/
theorem physicalHermitianExposedPair_eq_residual_add_fresh
    {d : ℕ} {Ξ : Type*} (ω : PhysicalHermitianSplitSample d Ξ) :
    physicalHermitianExposedPair ω =
      hermitianMatrixAdd (physicalHermitianResidual ω)
        (physicalHermitianFreshGUE ω) := rfl

/-- The fresh Hermitian GUE block is jointly independent of the entire
residual/exterior datum under the concrete product construction. -/
theorem indepFun_residualExterior_freshGUE
    {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (t : ℝ) (ht : 0 ≤ t)
    (residualLaw : Measure (HermitianCoordinateSpace d))
    (exteriorLaw : Measure Ξ)
    [IsProbabilityMeasure residualLaw] [IsProbabilityMeasure exteriorLaw] :
    IndepFun
      (fun ω : PhysicalHermitianSplitSample d Ξ => ω.1)
      (physicalHermitianFreshGUE (d := d) (Ξ := Ξ))
      (physicalHermitianSplitMeasure d t ht residualLaw exteriorLaw) := by
  unfold physicalHermitianSplitMeasure physicalHermitianFreshGUE
  exact indepFun_prod measurable_id (measurable_hermitianGUEBlock d)

/-- The residual exposed matrix is independent of exterior data before the
fresh GUE variable is adjoined.  Thus the construction uses the same physical
finite-coordinate product independence as the scalar split. -/
theorem indepFun_residual_exterior
    {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (residualLaw : Measure (HermitianCoordinateSpace d))
    (exteriorLaw : Measure Ξ)
    [IsProbabilityMeasure residualLaw] [IsProbabilityMeasure exteriorLaw] :
    IndepFun
      (fun z : HermitianCoordinateSpace d × Ξ => hermitianOfFinCoordinates d z.1)
      (fun z : HermitianCoordinateSpace d × Ξ => z.2)
      (residualLaw.prod exteriorLaw) := by
  exact indepFun_prod (measurable_hermitianOfFinCoordinates d) measurable_id

/-- Matrix-level integral splitting used by fixed-exterior coarea.  It is an
exact Tonelli identity for the concrete finite-product GUE law: after fixing
both residual matrix and exterior datum, the inner integral is solely over the
fresh Hermitian GUE block. -/
theorem lintegral_physicalHermitianExposedPair_split
    {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (t : ℝ) (ht : 0 ≤ t)
    (residualLaw : Measure (HermitianCoordinateSpace d))
    (exteriorLaw : Measure Ξ)
    (Φ : HermitianMatrix (Fin d) → Ξ → ℝ≥0∞)
    (hΦ : AEMeasurable
      (fun ω : PhysicalHermitianSplitSample d Ξ =>
        Φ (physicalHermitianExposedPair ω) ω.1.2)
      (physicalHermitianSplitMeasure d t ht residualLaw exteriorLaw)) :
    (∫⁻ ω, Φ (physicalHermitianExposedPair ω) ω.1.2
        ∂physicalHermitianSplitMeasure d t ht residualLaw exteriorLaw) =
      ∫⁻ z, (∫⁻ g,
          Φ (hermitianMatrixAdd (hermitianOfFinCoordinates d z.1)
            (hermitianGUEBlock d g)) z.2
            ∂hermitianGUECoordinateMeasure d t ht)
        ∂(residualLaw.prod exteriorLaw) := by
  exact MeasureTheory.lintegral_prod _ hΦ

/-- Physical two-block specialization of the matrix integral split.  Both the
residual law and the fresh variance are now the explicit laws dictated by
`p`, `s ≤ c`, and `s ≤ b`; the only remaining measure is the fixed exterior
data being conditioned upon. -/
theorem lintegral_physicalExposedPairGaussian_split
    {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (exteriorLaw : Measure Ξ)
    (Φ : HermitianMatrix (Fin (2 * p.W)) → Ξ → ℝ≥0∞)
    (hΦ : AEMeasurable
      (fun ω : PhysicalHermitianSplitSample (2 * p.W) Ξ =>
        Φ (physicalHermitianExposedPair ω) ω.1.2)
      (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw)) :
    (∫⁻ ω, Φ (physicalHermitianExposedPair ω) ω.1.2
      ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw) =
      ∫⁻ z, (∫⁻ g,
          Φ (hermitianMatrixAdd (hermitianOfFinCoordinates (2 * p.W) z.1)
            (hermitianGUEBlock (2 * p.W) g)) z.2
          ∂hermitianGUECoordinateMeasure (2 * p.W)
            (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0))
        ∂((physicalExposedPairResidualMeasure p hs0 hsc hsb).prod exteriorLaw) := by
  exact lintegral_physicalHermitianExposedPair_split
    (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0)
    (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw Φ hΦ

end CoareaNative.BlockBand
