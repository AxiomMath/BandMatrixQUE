module

public import BlockBand.Coarea.FixedOmegaChartIntegral

/-!
# Fixed-`ω` coarea: one chart suffices, and the GUE integral is the pivot-`0` chart integral

The projective charts cover the good set without double counting, so a single chart computes
the GUE integral. Support for the fixed-`ω` coarea formula `CoareaContract.formula_fixed`.

*Measures.* Lebesgue measure on the coordinates `HermitianCoordinateSpace d` and
`GUE_d(t) = gueMeasure (Fin d) t`, `t > 0`.
*Domain.* `d ≥ 1`, exterior coordinates `R`, any coupling `C`, Hermitian `V`, zero-based
rank `α`, measurable `g ≥ 0`.

## Main results

* `crossing_of_mem_source`: a point of the chart-`i` source decodes to a matrix with a
  selected-simple crossing at its own incidence energy (the explicit forward half of
  `mem_physicalSelectedSimpleDecode_image_iff`).
* `mem_image_zero_of_chartVector_ne_zero`: a chart-`i` source point whose eigenvector has
  nonzero `0`-th coordinate is decoded by chart `0`.
* `volume_goodSet_diff_image_zero`: the good set minus the chart-`0` image is
  Lebesgue-null (the remaining part lives on a proper linear subspace of each chart).
* `lintegral_gueMeasure_eq_decoderChartIntegrand`: if the good set is Lebesgue-conull
  (an explicit hypothesis on `ω`), `∫ g dGUE_d(t)` is the pivot-`0` chart integral.
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

/-- The explicit forward half of `mem_physicalSelectedSimpleDecode_image_iff`: the crossing
happens at the incidence energy of the source point. -/
theorem crossing_of_mem_source (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    {x : HermitianCoordinateSpace d} (hx : x ∈ physicalSelectedSimpleSource α R i) :
    PhysicalSelectedSimpleCrossing α R i C V (physicalSelectedSimpleDecode R i C V x)
      (eigenpairIncidenceCoordinates i x).1 := by
  set K := physicalSelectedSimpleDecode R i C V x
  set H_R := (hermitianOfFinCoordinates dR R).1 with hHRdef
  have hH : H_R.IsHermitian := (hermitianOfFinCoordinates dR R).property
  set F := CoareaNative.BlockBand.physicalCoareaF H_R C V with hFdef
  have hFH (E : ℝ) : (F E).IsHermitian :=
    CoareaNative.BlockBand.physicalCoareaF_isHermitian H_R C V hH hV E
  set Kr := (selectedCoordinateHermitianReindex i (hermitianFinCoordinatesLinearEquiv d K)).1
    with hKr
  have hKrH : Kr.IsHermitian :=
    (selectedCoordinateHermitianReindex i (hermitianFinCoordinatesLinearEquiv d K)).2
  have hMdef (E : ℝ) : physicalSelectedReducedMatrix R i C V K E = Kr + F E := rfl
  set y := eigenpairIncidenceCoordinates i x with hydef
  refine ⟨hx.2.2, ?_⟩
  have hG := physicalSchurFinCoordinateDecode_eq_read i F x
  rw [← hydef] at hG
  have hxK : physicalSchurFinCoordinateDecode i F x = K := rfl
  rw [hxK, ← selectedMatrixFinCoordinateReadCLM_reindex i K, ← hKr] at hG
  have hKreq : Kr = (canonicalEigenpairChartDecode y).1 - F y.1 :=
    selectedMatrixFinCoordinateReadCLM_injective_hermitian i hKrH
      ((canonicalEigenpairChartDecode y).2.sub (hFH _)) hG
  have hM : physicalSelectedReducedMatrix R i C V K y.1 =
      (canonicalEigenpairChartDecode y).1 := by
    rw [hMdef, hKreq, sub_add_cancel]
  refine ⟨⇑(canonicalProjectiveUnitVector y.2.1), ?_, ?_, ?_, ?_⟩
  · intro h0
    have h2 := canonicalProjectiveUnitVector_selected_re_pos y.2.1
    rw [show (canonicalProjectiveUnitVector y.2.1) (Sum.inl Unit.unit) = 0 from h0] at h2
    simp at h2
  · rw [hM]
    exact canonicalEigenpairChartDecode_mulVec_unitVector y
  · intro w hw
    rw [hM] at hw
    exact canonicalEigenpairChartDecode_eigenvector_eq_smul y hx.1 w hw
  · refine ⟨hM ▸ (canonicalEigenpairChartDecode y).2, ?_⟩
    have hB : (y.2.2.1 - (y.1 : ℂ) • 1).IsHermitian :=
      y.2.2.2.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
    have hdecE : ((canonicalEigenpairChartDecode y).1 - (y.1 : ℂ) • 1).IsHermitian :=
      (canonicalEigenpairChartDecode y).2.sub
        (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
    rw [eigenCount_Iio_eq_negativeEigenvalueCount_of_eq _ y.1 hM hdecE,
      negativeEigenvalueCount_canonicalDecode_sub y hdecE hB,
      ← shiftedInertia_complement_eq_negativeEigenvalueCount y.1 y.2.2 hB]
    have hrank := hx.2.1
    rw [← hydef] at hrank
    unfold physicalEigenpairFixedRank coareaRankIndex at hrank
    simp only at hrank
    omega

/-- The chart-free reduced matrix at the decoded point is `E vvᴴ + U B Uᴴ`. -/
theorem physicalGlobalReducedMatrix_decode (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian)
    (i : Fin d) (x : HermitianCoordinateSpace d) :
    physicalGlobalReducedMatrix R C V (physicalSelectedSimpleDecode R i (physicalChartCoupling C i)
        (physicalChartPotential V i) x) (eigenpairIncidenceCoordinates i x).1 =
      ((eigenpairIncidenceCoordinates i x).1 : ℂ) •
          vecMulVec (chartVector i (eigenpairIncidenceCoordinates i x).2.1)
            (star (chartVector i (eigenpairIncidenceCoordinates i x).2.1)) +
        chartFrame i (eigenpairIncidenceCoordinates i x).2.1 *
          (eigenpairIncidenceCoordinates i x).2.2.1 *
          (chartFrame i (eigenpairIncidenceCoordinates i x).2.1)ᴴ := by
  unfold physicalGlobalReducedMatrix
  rw [hermitianOfFinCoordinates_physicalSelectedSimpleDecode R C V hV i x]
  have : (V - Cᴴ * CoareaNative.BlockBand.physicalCoareaResolvent (hermitianOfFinCoordinates dR R).1
      (eigenpairIncidenceCoordinates i x).1 * C) =
      BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V
        (eigenpairIncidenceCoordinates i x).1 := rfl
  rw [this, sub_add_cancel]

theorem vecMulVec_mulVec' {ι : Type*} [Fintype ι] (u v w : ι → ℂ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

theorem chartVector_ne_zero (i : Fin d) (z : Fin (d - 1) → ℂ) : chartVector i z i ≠ 0 := by
  intro h0
  have h2 := canonicalProjectiveUnitVector_selected_re_pos z
  unfold chartVector at h0
  rw [selectedCoordinateEquiv_apply_selected] at h0
  rw [show (canonicalProjectiveUnitVector z) (Sum.inl Unit.unit) = 0 from h0] at h2
  simp at h2

/-- A chart-`i` source point whose eigenvector has nonzero `0`-th coordinate is decoded by
chart `0`. -/
theorem mem_image_zero_of_chartVector_ne_zero (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) (i : Fin d)
    {x : HermitianCoordinateSpace d} (hx : x ∈ physicalSelectedSimpleSource α R i)
    (h0 : chartVector i (eigenpairIncidenceCoordinates i x).2.1 ⟨0, hd⟩ ≠ 0) :
    physicalSelectedSimpleDecode R i (physicalChartCoupling C i) (physicalChartPotential V i) x ∈
      physicalSelectedSimpleImage α R (physicalChartCoupling C) (physicalChartPotential V)
        ⟨0, hd⟩ := by
  set K := physicalSelectedSimpleDecode R i (physicalChartCoupling C i)
    (physicalChartPotential V i) x
  set E := (eigenpairIncidenceCoordinates i x).1
  set w := chartVector i (eigenpairIncidenceCoordinates i x).2.1
  have hcross := crossing_of_mem_source α R i (physicalChartCoupling C i)
    (physicalChartPotential V i) (physicalChartPotential_isHermitian hV i) hx
  obtain ⟨hpole, u, _, hMu, hsimp, hM, hcount⟩ :=
    (physicalSelectedSimpleCrossing_iff_global α R C V i K E).1 hcross
  have hMw : physicalGlobalReducedMatrix R C V K E *ᵥ w = (E : ℂ) • w := by
    have hfr := isFrameOf_chartFrame i (eigenpairIncidenceCoordinates i x).2.1
    have hv := star_chartVector_dotProduct i (eigenpairIncidenceCoordinates i x).2.1
    rw [physicalGlobalReducedMatrix_decode R C hV i x, Matrix.add_mulVec, Matrix.smul_mulVec,
      vecMulVec_mulVec', hv, one_smul, ← Matrix.mulVec_mulVec, hfr.2, Matrix.mulVec_zero,
      add_zero]
  obtain ⟨c, hc⟩ := hsimp w hMw
  have hu0 : u ⟨0, hd⟩ ≠ 0 := by
    intro h; apply h0
    rw [hc, Pi.smul_apply, h, smul_zero]
  exact (mem_physicalSelectedSimpleDecode_image_iff α R ⟨0, hd⟩ _ _
    (physicalChartPotential_isHermitian hV _) K).2
    ⟨E, (physicalSelectedSimpleCrossing_iff_global α R C V ⟨0, hd⟩ K E).2
      ⟨hpole, u, hu0, hMu, hsimp, hM, hcount⟩⟩

/-!
## Nullity of the chart-`i` locus where the `0`-th coordinate vanishes
-/

theorem volume_chartVector_eq_zero (hd : 1 ≤ d) (i : Fin d) :
    volume {x : HermitianCoordinateSpace d |
      chartVector i (eigenpairIncidenceCoordinates i x).2.1 ⟨0, hd⟩ = 0} = 0 := by
  rcases hsel : selectedCoordinateEquiv i ⟨0, hd⟩ with u | k
  · have hempty : {x : HermitianCoordinateSpace d |
        chartVector i (eigenpairIncidenceCoordinates i x).2.1 ⟨0, hd⟩ = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hi : (⟨0, hd⟩ : Fin d) = i := by
        apply (selectedCoordinateEquiv i).injective
        rw [hsel, selectedCoordinateEquiv_apply_selected]
      apply chartVector_ne_zero i (eigenpairIncidenceCoordinates i x).2.1
      have h' := h
      rw [hi] at h'
      exact h'
    rw [hempty, measure_empty]
  · let ℓ : HermitianCoordinateSpace d →ₗ[ℝ] ℂ :=
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d - 1) => ℂ) k).comp
        ((LinearMap.fst ℝ (Fin (d - 1) → ℂ) (HermitianCoordinateSpace (d - 1))).comp
          ((LinearMap.snd ℝ ℝ ((Fin (d - 1) → ℂ) × HermitianCoordinateSpace (d - 1))).comp
            (chartEquiv d i).toLinearMap))
    have hsub : {x : HermitianCoordinateSpace d |
        chartVector i (eigenpairIncidenceCoordinates i x).2.1 ⟨0, hd⟩ = 0} ⊆
        (LinearMap.ker ℓ : Set (HermitianCoordinateSpace d)) := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      rw [chartVector, hsel, canonicalProjectiveUnitVector_apply] at hx
      have hq := ProjectiveHaar.chartSq_nonneg (eigenpairIncidenceCoordinates i x).2.1
      have hs : ((Real.sqrt (1 + ProjectiveHaar.chartSq
          (eigenpairIncidenceCoordinates i x).2.1))⁻¹ : ℂ) ≠ 0 := by
        have : 0 < Real.sqrt (1 + ProjectiveHaar.chartSq (eigenpairIncidenceCoordinates i x).2.1) :=
          Real.sqrt_pos.2 (by linarith)
        exact inv_ne_zero (Complex.ofReal_ne_zero.2 this.ne')
      have hk := (mul_eq_zero.1 hx).resolve_left hs
      simp only [projectiveEigenvectorReconstruction, reduceCtorEq, ↓reduceDIte,
        canonicalProjectiveChartCoordinates_inr] at hk
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      exact hk
    have hne : LinearMap.ker ℓ ≠ ⊤ := by
      intro htop
      have hx0 : (chartEquiv d i).symm (0, Pi.single k 1, 0) ∈ LinearMap.ker ℓ := by
        rw [htop]; exact Submodule.mem_top
      rw [LinearMap.mem_ker] at hx0
      simp [ℓ] at hx0
    exact measure_mono_null hsub (Measure.addHaar_submodule volume _ hne)

theorem volume_image_decode_null (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Fin d) ℂ) {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian)
    {s : Set (HermitianCoordinateSpace d)} (hs : MeasurableSet s)
    (hsub : s ⊆ physicalSelectedSimpleSource α R i) (h0 : volume s = 0) :
    volume (physicalSelectedSimpleDecode R i (physicalChartCoupling C i)
      (physicalChartPotential V i) '' s) = 0 := by
  have h := lintegral_image_physicalSelectedSimpleDecode α R i (physicalChartCoupling C i)
    (physicalChartPotential V i) (physicalChartPotential_isHermitian hV i) hs hsub (fun _ => 1)
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    one_mul, mul_one] at h
  rw [h]
  exact setLIntegral_measure_zero s _ h0

/-- **One chart suffices**: the good set minus the chart-`0` image is Lebesgue-null. -/
theorem volume_goodSet_diff_image_zero (hd : 1 ≤ d) (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) :
    volume (physicalSelectedSimpleGoodSet α R C V \
      physicalSelectedSimpleImage α R (physicalChartCoupling C) (physicalChartPotential V)
        ⟨0, hd⟩) = 0 := by
  set Z : Fin d → Set (HermitianCoordinateSpace d) := fun i =>
    physicalSelectedSimpleSource α R i ∩
      {x | chartVector i (eigenpairIncidenceCoordinates i x).2.1 ⟨0, hd⟩ = 0}
  have hZm : ∀ i, MeasurableSet (Z i) := by
    intro i
    refine (measurableSet_physicalSelectedSimpleSource α R i).inter ?_
    have hy := measurable_eigenpairIncidenceCoordinates_complete (d := d) i
    have hz : Measurable fun x : HermitianCoordinateSpace d =>
        (eigenpairIncidenceCoordinates i x).2.1 := measurable_fst.comp (measurable_snd.comp hy)
    exact measurableSet_eq_fun
      ((measurable_canonicalProjectiveUnitVector_apply _).comp hz) measurable_const
  have hsub : physicalSelectedSimpleGoodSet α R C V \
      physicalSelectedSimpleImage α R (physicalChartCoupling C) (physicalChartPotential V)
        ⟨0, hd⟩ ⊆ ⋃ i, physicalSelectedSimpleDecode R i (physicalChartCoupling C i)
          (physicalChartPotential V i) '' Z i := by
    rintro K ⟨hK, hK0⟩
    rw [← iUnion_physicalSelectedSimpleImage_eq_goodSet α R C V hV, Set.mem_iUnion] at hK
    obtain ⟨i, x, hx, rfl⟩ := hK
    refine Set.mem_iUnion.2 ⟨i, x, ⟨hx, ?_⟩, rfl⟩
    by_contra hne
    exact hK0 (mem_image_zero_of_chartVector_ne_zero hd α R C hV i hx hne)
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine volume_image_decode_null α R i C hV (hZm i) Set.inter_subset_left ?_
  exact measure_mono_null Set.inter_subset_right (volume_chartVector_eq_zero hd i)

/-!
## The GUE integral is the pivot-`0` chart integral
-/

/-- **`∫ g dGUE_d(t)` is the pivot-`0` chart integral** when the good set is
Lebesgue-conull (`t > 0`, `g` measurable). -/
theorem lintegral_gueMeasure_eq_decoderChartIntegrand (hd : 1 ≤ d) (α : ℕ)
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hV : V.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {g : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hg : Measurable g)
    (hgood : volume (physicalSelectedSimpleGoodSet α R C V)ᶜ = 0) :
    ∫⁻ G, g G ∂gueMeasure (Fin d) t = ∫⁻ x, decoderChartIntegrand hd α R C V t g x := by
  set S := physicalSelectedSimpleGoodSet α R C V
  set I0 := physicalSelectedSimpleImage α R (physicalChartCoupling C) (physicalChartPotential V)
    ⟨0, hd⟩
  set φ : HermitianCoordinateSpace d → ℝ≥0∞ := fun K =>
    hermitianGUEDensity d t (hermitianOfFinCoordinates d K) * g (hermitianOfFinCoordinates d K).1
  rw [lintegral_gueMeasure d ht hg]
  change ∫⁻ x, φ x = _
  have hI0S : I0 ⊆ S := by
    intro K hK
    have h := iUnion_physicalSelectedSimpleImage_eq_goodSet α R C V hV
    change K ∈ physicalSelectedSimpleGoodSet α R C V
    rw [← h]
    exact Set.mem_iUnion.2 ⟨⟨0, hd⟩, hK⟩
  have hae : I0 =ᵐ[volume] (Set.univ : Set (HermitianCoordinateSpace d)) := by
    rw [ae_eq_univ]
    have h1 : I0ᶜ ⊆ Sᶜ ∪ (S \ I0) := by
      intro K hK
      by_cases hKS : K ∈ S
      · exact Or.inr ⟨hKS, hK⟩
      · exact Or.inl hKS
    exact measure_mono_null h1 (measure_union_null hgood
      (volume_goodSet_diff_image_zero hd α R C hV))
  rw [← setLIntegral_univ, ← setLIntegral_congr hae]
  have himg := lintegral_image_physicalSelectedSimpleDecode α R ⟨0, hd⟩
    (physicalChartCoupling C ⟨0, hd⟩) (physicalChartPotential V ⟨0, hd⟩)
    (physicalChartPotential_isHermitian hV _)
    (measurableSet_physicalSelectedSimpleSource α R ⟨0, hd⟩) subset_rfl φ
  change ∫⁻ x in I0, φ x = _ at himg ⊢
  rw [himg, ← lintegral_indicator (measurableSet_physicalSelectedSimpleSource α R ⟨0, hd⟩)]
  rfl

end BlockBand.Coarea.FixedOmega
