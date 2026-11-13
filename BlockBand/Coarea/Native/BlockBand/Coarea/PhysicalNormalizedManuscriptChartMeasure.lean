module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalFreshGUEDensity

/-!
# Normalization-correct chart measure

`PhysicalFreshGUEDensity` shows that the paper's chart density
`physicalSchurManuscriptDensity`, integrated against raw Lebesgue measure on
the incidence coordinates, is too large by the factor
`κ_d(t) = c_{d,t} Z_d(t) = π^{d-1}/(d-1)! · Z_{d-1}(t)`.

This file defines the normalization-correct chart base measure
`κ_d(t)⁻¹ · volume` (equivalently the density
`physicalSchurNormalizedManuscriptDensity = κ_d(t)⁻¹ · physicalSchurManuscriptDensity`,
whose Gaussian constant is exactly `Z_d(t)⁻¹`), and proves:

* for the general Schur readback `(H_R, C, V)`, the exact normalized chart
  weight `Z_d(t)⁻¹ exp(-‖M - F(E)‖²/(2t)) ⟨v, 𝒟(E) v⟩`: the law of the Schur
  matrix `M = F(E) + G` (`physicalSchurNormalizedOuterWeight_eq_matrixForm`);
* for the uncoupled readback `C = 0`, the fresh GUE chart equality with no
  extraneous factor, on the decoded union and, conditionally on a named
  a.e.-cover hypothesis, on the whole space;
* for `C ≠ 0` the identification with the fresh-GUE density of `V₀ + G` is
  false: an explicit `d = 1` decoded point where the normalized weight is
  `2/Z_1(1)` and the fresh density is `e^{-1/2}/Z_1(1)`.

All dimensions,
ranks, exterior data and pole charts are fixed; no limit or uniformity is
asserted.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped ENNReal MatrixOrder

/-- The normalization ratio `κ_d(t)` is positive for positive variance. -/
theorem chartGUENormalizationRatio_pos (d : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < chartGUENormalizationRatio d t := by
  unfold chartGUENormalizationRatio coareaGaussianDensityConstant
  have := gueNormalizer_pos (d := d) ht
  positivity

/-- The normalization-correct chart base measure `κ_d(t)⁻¹ · volume` on the
incidence coordinates.  It is the
raw Lebesgue measure rescaled so that the paper's density constant
`c_{d,t}` becomes the GUE normalizer `Z_d(t)⁻¹`. -/
def normalizedManuscriptChartBaseMeasure (d : ℕ) (t : ℝ) :
    Measure (HermitianCoordinateSpace d) :=
  ENNReal.ofReal (chartGUENormalizationRatio d t)⁻¹ • volume

/-- The paper's chart density with respect to raw Lebesgue measure after
absorbing the normalization: `κ_d(t)⁻¹ · physicalSchurManuscriptDensity`. -/
def physicalSchurNormalizedManuscriptDensity
    {r d : ℕ} (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (i : Fin d) (x : HermitianCoordinateSpace d) : ℝ≥0∞ :=
  ENNReal.ofReal (chartGUENormalizationRatio d t)⁻¹ *
    physicalSchurManuscriptDensity t H_R C V i x

/-- The normalized outer (Gaussian/regression/crossing) weight. -/
def physicalSchurNormalizedOuterWeight
    {r d : ℕ} (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (i : Fin d) (x : HermitianCoordinateSpace d) : ℝ≥0∞ :=
  ENNReal.ofReal (chartGUENormalizationRatio d t)⁻¹ *
    physicalSchurOuterWeight t H_R C V i x

/-- Integrating the raw density against the normalized base
measure is integrating the normalized density against Lebesgue measure. -/
theorem setLIntegral_normalizedManuscriptChartBaseMeasure
    {r d : ℕ} (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (i : Fin d) (s : Set (HermitianCoordinateSpace d))
    (g : HermitianCoordinateSpace d → ℝ≥0∞) (_hg : Measurable g) :
    ∫⁻ x in s, physicalSchurManuscriptDensity t H_R C V i x * g x
        ∂normalizedManuscriptChartBaseMeasure d t =
      ∫⁻ x in s, physicalSchurNormalizedManuscriptDensity t H_R C V i x * g x := by
  unfold normalizedManuscriptChartBaseMeasure physicalSchurNormalizedManuscriptDensity
  rw [Measure.restrict_smul, lintegral_smul_measure]
  simp_rw [mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-- The normalized constant is exactly the GUE normalizer:
`κ_d(t)⁻¹ c_{d,t} = Z_d(t)⁻¹` for `0 < t`. -/
theorem ofReal_ratio_inv_mul_coareaGaussianDensityConstant (d : ℕ) {t : ℝ}
    (ht : 0 < t) :
    ENNReal.ofReal (chartGUENormalizationRatio d t)⁻¹ *
        ENNReal.ofReal (coareaGaussianDensityConstant d t) =
      ENNReal.ofReal (gueNormalizer d t)⁻¹ := by
  have hκ := chartGUENormalizationRatio_pos d ht
  have hZ := gueNormalizer_pos (d := d) ht
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]
  congr 1
  have hc : coareaGaussianDensityConstant d t ≠ 0 := by
    unfold coareaGaussianDensityConstant
    positivity
  unfold chartGUENormalizationRatio
  field_simp

/-- **Normalized chart weight, general Schur readback**.  For `0 < t`, Hermitian `H_R`, `V`, arbitrary coupling
`C`, every chart `i` and incidence point `x`, with `M` the decoded matrix and
`F̃(E)` the chart-`i` unreindexing of `F(E) = V - Cᴴ(H_R-E)⁻¹C`:
`weight = Z_d(t)⁻¹ exp(-‖M - F̃(E)‖²_HS/(2t)) · ⟨v, 𝒟(E) v⟩`.
This is the density, with respect to Lebesgue measure in `M`, of the Schur
matrix `M = F(E(M)) + G` with `G` fresh GUE (Jacobian `⟨v, 𝒟(E) v⟩`). -/
theorem physicalSchurNormalizedOuterWeight_eq_matrixForm {r d : ℕ} {t : ℝ}
    (ht : 0 < t)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hR : H_R.IsHermitian) (hV : V.IsHermitian)
    (i : Fin d) (x : HermitianCoordinateSpace d) :
    physicalSchurNormalizedOuterWeight t H_R C V i x =
      ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
          ((hermitianOfFinCoordinates d (selectedEigenpairFinCoordinateChartDecode i x)).1 -
            Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm
              (physicalCoareaF H_R C V (eigenpairIncidenceCoordinates i x).1)) / (2 * t)) /
          gueNormalizer d t) *
        ENNReal.ofReal (physicalEigenpairCrossingQuadratic
          (physicalCoareaT H_R C (eigenpairIncidenceCoordinates i x).1)
          (eigenpairIncidenceCoordinates i x).2.1) := by
  unfold physicalSchurNormalizedOuterWeight
  rw [physicalSchurOuterWeight_eq_matrixForm ht H_R C V hR hV i x, ← mul_assoc,
    ← mul_assoc, ofReal_ratio_inv_mul_coareaGaussianDensityConstant d ht,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (gueNormalizer_pos ht).le),
    mul_comm (gueNormalizer d t)⁻¹]
  simp only [div_eq_mul_inv]

/-- **Normalized chart coarea, general Schur readback.**  For every finite
pole/chart cover and arbitrary `(H_R, C, V)`, the decoded-piece integrals of
the transported normalized weight equal the source integrals of the
normalized density.  No extraneous factor appears. -/
theorem lintegral_normalizedManuscriptChart_finiteCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α R)
    (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∑ a : κ, ∑ rank : HermitianEigenRank d,
      ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 ''
          cover.source a rank p,
        eigenpairChartTransportWeight (ofLex p).1 (cover.source a rank p)
          (physicalSchurNormalizedOuterWeight t H_R C V (ofLex p).1) K *
            phaseFreeOrderedProjectorObservable ρ Ψ K) =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurNormalizedManuscriptDensity t H_R C V (ofLex p).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  have hT : ∀ (i : Fin d) (s : Set (HermitianCoordinateSpace d))
      (K : HermitianCoordinateSpace d),
      eigenpairChartTransportWeight i s (physicalSchurNormalizedOuterWeight t H_R C V i) K =
        ENNReal.ofReal (chartGUENormalizationRatio d t)⁻¹ *
          eigenpairChartTransportWeight i s (physicalSchurOuterWeight t H_R C V i) K := by
    intro i s K
    classical
    unfold eigenpairChartTransportWeight physicalSchurNormalizedOuterWeight
    split_ifs <;> simp
  simp_rw [hT, mul_assoc, physicalSchurNormalizedManuscriptDensity, mul_assoc]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [← Finset.mul_sum]
  rw [lintegral_physicalSchurCoarea_manuscript_finiteCover α R cover t H_R C V ρ Ψ hΨ]

/-- **Exact fresh GUE chart equality, uncoupled readback, decoded union**.

Hypotheses: `0 < t`; coupling `C = 0`; `H_R`, `V` Hermitian; and the named
per-chart consistency hypothesis `hVz`: for every chart index `i` the
chart-`i` unreindexing of `V` is the residual block `H(z₀)`.  The theorem is
conditional on `hVz` (the paper's chart sum uses one `V` for every chart).
Then the Lebesgue integral of the fresh GUE density of `K - z₀` against the
phase-free observable over the decoded union equals the normalized
chart sum, with no extraneous factor. -/
theorem lintegral_decodedUnion_freshGUE_eq_normalizedChartSum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α R)
    {t : ℝ} (ht : 0 < t)
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hR : H_R.IsHermitian)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    (z₀ : HermitianCoordinateSpace d)
    (hVz : ∀ i : Fin d,
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm V =
        (hermitianOfFinCoordinates d z₀).1)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ K in cover.decodedUnion,
        hermitianGUEDensity d t (hermitianOfFinCoordinates d (K - z₀)) *
          phaseFreeOrderedProjectorObservable ρ Ψ K =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurNormalizedManuscriptDensity t H_R 0 V (ofLex p).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  have hκ := chartGUENormalizationRatio_pos d ht
  simp_rw [physicalSchurNormalizedManuscriptDensity, mul_assoc]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [← Finset.mul_sum]
  rw [← lintegral_decodedUnion_freshGUE_eq_manuscriptChartSum α R cover ht H_R hR V hV
    z₀ hVz ρ Ψ hΨ, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le),
    inv_mul_cancel₀ hκ.ne', ENNReal.ofReal_one, one_mul]

/-- **Exact fresh GUE = normalized chart sum, uncoupled readback,
conditional on an a.e. cover**.

Conditional integration theorem: besides the hypotheses of
`lintegral_decodedUnion_freshGUE_eq_normalizedChartSum` (including the named
per-chart consistency `hVz`), it assumes the named hypothesis `hcover` that the
decoded cover pieces exhaust Lebesgue-almost every total-block coordinate;
`PhysicalCoareaPoleChartCover` does not supply it.  Then the fresh GUE average
of the phase-free observable of `V₀ + G`, `V₀ = H(z₀)`, is the normalized
chart sum. -/
theorem freshGUE_eq_normalizedChartSum_of_aeCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α R)
    (hcover : volume (cover.decodedUnionᶜ) = 0)
    {t : ℝ} (ht : 0 < t)
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hR : H_R.IsHermitian)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    (z₀ : HermitianCoordinateSpace d)
    (hVz : ∀ i : Fin d,
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm V =
        (hermitianOfFinCoordinates d z₀).1)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ g, physicalMatrixPhaseFreeObservable ρ Ψ
        (hermitianMatrixAdd (hermitianOfFinCoordinates d z₀) (hermitianGUEBlock d g))
        ∂hermitianGUECoordinateMeasure d t ht.le =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurNormalizedManuscriptDensity t H_R 0 V (ofLex p).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  rw [← lintegral_decodedUnion_freshGUE_eq_normalizedChartSum α R cover ht H_R hR V hV
    z₀ hVz ρ Ψ hΨ, lintegral_hermitianGUE_residual_translate d ht,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcover)]
  refine lintegral_congr fun x => ?_
  unfold physicalMatrixPhaseFreeObservable
  rw [hermitianFinCoordinateReadback_hermitianOfFinCoordinates]

/-!
### The coupled readback: failure of the fresh-GUE identification
-/

/-- The unit exterior coupling of a one-dimensional exposed block to a
one-dimensional exterior. -/
def unitExteriorCoupling : Matrix (Fin 1) (Unit ⊕ Fin (1 - 1)) ℂ := fun _ _ => 1

/-- The incidence point with energy `1`, zero projective coordinate and empty
complementary block, in the unique chart of a `1 × 1` block. -/
def unitEnergyIncidencePoint : HermitianCoordinateSpace 1 :=
  (selectedEigenpairFinCoordinateLinearEquiv (0 : Fin 1)).symm (1, (0, 0))

/-- A matrix on the one-point index `Unit ⊕ Fin 0` is `1` iff its entry is `1`. -/
theorem one_eq_of_unit_fin_zero
    (A : Matrix (Unit ⊕ Fin (1 - 1)) (Unit ⊕ Fin (1 - 1)) ℂ)
    (h : A (Sum.inl ()) (Sum.inl ()) = 1) : A = 1 := by
  ext a b
  rcases a with ⟨⟩ | a
  · rcases b with ⟨⟩ | b
    · simpa using h
    · exact b.elim0
  · exact a.elim0

/-- The identity on the one-point index has Hilbert–Schmidt norm `1`. -/
theorem hilbertSchmidtNormSq_one_unit_fin_zero :
    hilbertSchmidtNormSq (1 : Matrix (Unit ⊕ Fin (1 - 1)) (Unit ⊕ Fin (1 - 1)) ℂ) = 1 := by
  simp [hilbertSchmidtNormSq, Fintype.sum_sum_type]

/-- **The coupled readback does not give the fresh GUE density**.

Take `d = 1`, `t = 1`, exterior `H_R = 0 ∈ ℂ^{1×1}`, coupling `C = 1`,
`V = 0`, residual `z₀ = 0`, and the decoded chart point of energy `E = 1`.
Then `F(1) = V - Cᴴ(H_R - 1)⁻¹C = 1`, `𝒟(1) = 2`, so the normalized
transported chart weight is `2 / Z_1(1)`, while the fresh GUE density of
`K - z₀` is `e^{-1/2} / Z_1(1)`.  Hence for `C ≠ 0` the normalized
chart measure is not the fresh-GUE law of `V₀ + G`: it is the law of the Schur
matrix `F(E) + G` (`physicalSchurNormalizedOuterWeight_eq_matrixForm`). -/
theorem normalizedChartWeight_ne_freshGUEDensity_coupled :
    eigenpairChartTransportWeight (0 : Fin 1) {unitEnergyIncidencePoint}
        (physicalSchurNormalizedOuterWeight 1 (0 : Matrix (Fin 1) (Fin 1) ℂ)
          unitExteriorCoupling 0 0)
        (selectedEigenpairFinCoordinateChartDecode 0 unitEnergyIncidencePoint) ≠
      hermitianGUEDensity 1 1 (hermitianOfFinCoordinates 1
        (selectedEigenpairFinCoordinateChartDecode 0 unitEnergyIncidencePoint - 0)) := by
  set x := unitEnergyIncidencePoint
  have hy : eigenpairIncidenceCoordinates (0 : Fin 1) x = (1, (0, 0)) :=
    LinearEquiv.apply_symm_apply _ _
  have hE : (eigenpairIncidenceCoordinates (0 : Fin 1) x).1 = 1 := by rw [hy]
  set U := physicalCoareaFrame (eigenpairIncidenceCoordinates (0 : Fin 1) x).2.1
  have hU : Uᴴ * U = 1 := physicalCoareaFrame_unitary _
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hD : Matrix.fromBlocks
      (((eigenpairIncidenceCoordinates (0 : Fin 1) x).1 : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0
      (eigenpairIncidenceCoordinates (0 : Fin 1) x).2.2.1 = 1 := by
    apply one_eq_of_unit_fin_zero
    rw [hy]
    simp
  have hM : (hermitianOfFinCoordinates 1 (selectedEigenpairFinCoordinateChartDecode 0 x)).1 =
      Matrix.reindex (selectedCoordinateEquiv (0 : Fin 1)).symm
        (selectedCoordinateEquiv (0 : Fin 1)).symm 1 := by
    rw [hermitianOfFinCoordinates_selectedEigenpairFinCoordinateChartDecode, hD,
      Matrix.mul_one, hU']
  have hinv : ((0 : Matrix (Fin 1) (Fin 1) ℂ) - ((1 : ℝ) : ℂ) • 1)⁻¹ = -1 := by
    apply Matrix.inv_eq_left_inv
    simp
  have hCC : unitExteriorCouplingᴴ * unitExteriorCoupling = 1 := by
    apply one_eq_of_unit_fin_zero
    simp [unitExteriorCoupling, Matrix.mul_apply]
  have hF : physicalCoareaF 0 unitExteriorCoupling 0 1 = 1 := by
    unfold physicalCoareaF physicalCoareaResolvent
    rw [hinv]
    simp [Matrix.mul_neg, hCC]
  have hT : schurClock (physicalCoareaT 0 unitExteriorCoupling 1) = 1 + 1 := by
    unfold schurClock physicalCoareaT physicalCoareaResolvent
    rw [hinv]
    simp [Matrix.conjTranspose_neg, hCC]
  have hcross : physicalEigenpairCrossingQuadratic
      (physicalCoareaT 0 unitExteriorCoupling 1)
      (eigenpairIncidenceCoordinates (0 : Fin 1) x).2.1 = 2 := by
    have h1 := physicalEigenpairCrossingQuadratic_zero (r := 1)
      (eigenpairIncidenceCoordinates (0 : Fin 1) x).2.1
    unfold physicalEigenpairCrossingQuadratic at h1 ⊢
    rw [hT, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    have h0 : schurClock (0 : Matrix (Fin 1) (Unit ⊕ Fin (1 - 1)) ℂ) = 1 := by
      simp [schurClock]
    rw [h0] at h1
    rw [h1]
    norm_num
  rw [eigenpairChartTransportWeight_decode _ {x} _ (Set.injOn_singleton _ _) rfl,
    physicalSchurNormalizedOuterWeight_eq_matrixForm one_pos _ _ _
      Matrix.isHermitian_zero Matrix.isHermitian_zero 0 x,
    hE, hF, hM, sub_self, hcross, sub_zero, hermitianGUEDensity, hM]
  have hHS1 : hilbertSchmidtNormSq (Matrix.reindex (selectedCoordinateEquiv (0 : Fin 1)).symm
      (selectedCoordinateEquiv (0 : Fin 1)).symm
        (1 : Matrix (Unit ⊕ Fin (1 - 1)) (Unit ⊕ Fin (1 - 1)) ℂ)) = 1 := by
    rw [hilbertSchmidtNormSq_reindex, hilbertSchmidtNormSq_one_unit_fin_zero]
  have hHS1' : hilbertSchmidtNormSq (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    simpa using hHS1
  simp only [Matrix.reindex_apply, Matrix.submatrix_one_equiv] at *
  try rw [hHS1']
  have hZ := gueNormalizer_pos (d := 1) one_pos
  rw [← ENNReal.ofReal_mul (by positivity),
    Ne, ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
  intro h
  have he : Real.exp (-1 / (2 * 1)) < 2 := by
    have : Real.exp (-1 / (2 * 1)) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_strictMono (by norm_num)
    linarith
  have hHS0 : hilbertSchmidtNormSq
      (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by simp [hilbertSchmidtNormSq]
  rw [hHS0] at h
  field_simp at h
  norm_num at h he
  linarith

end CoareaNative.BlockBand
