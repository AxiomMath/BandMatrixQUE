module

public import BlockBand.Endpoints.Poisson.PhaseFractionalCollar

/-!
# The fresh collar: probability, Hermitian samples, contraction, measurability

Law: `collarLaw W b` of the collar kernel theorem (three `GUE_W(c/W)` diagonals, two Ginibre
bonds of variance `b/W`).

* `isProbabilityMeasure_collarLaw`;
* `ae_collar_hermitian`: almost surely the three diagonal blocks are Hermitian (the GUE
  sample map is Hermitian-valued);
* `isContraction_collarScattering`: for Hermitian blocks, a common height `ν ≥ 0` and `η > 0`,
  `U = I - 2iη(K_c + iη)⁻¹` is a contraction (`Im K_c ⪰ 0`);
* `measurable_collarScattering`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexOrder ComplexConjugate

/-!
## Contraction of Cayley transforms
-/

theorem quadNorm_add_sub_sub {κ : Type*} [Fintype κ] (a b : κ → ℂ) :
    quadNorm (a + b) - quadNorm (a - b) = 4 * (star a ⬝ᵥ b).re := by
  have h : star (a + b) ⬝ᵥ (a + b) - star (a - b) ⬝ᵥ (a - b) =
      2 * (star a ⬝ᵥ b) + 2 * (star b ⬝ᵥ a) := by
    simp only [star_add, star_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
      dotProduct_sub]
    ring
  have hre : (star b ⬝ᵥ a).re = (star a ⬝ᵥ b).re := by
    rw [← conj_dotProduct a b, Complex.conj_re]
  rw [quadNorm, quadNorm, ← Complex.sub_re, h]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  linarith

/-- If `Im(y* K y) ≥ 0` for every `y` and `η > 0`, then `K + iη` is invertible and
`I - 2iη (K + iη)⁻¹` is a contraction. -/
theorem isContraction_cayley {κ : Type*} [Fintype κ] [DecidableEq κ] {K : Matrix κ κ ℂ}
    (hK : ∀ y, 0 ≤ (star y ⬝ᵥ (K *ᵥ y)).im) {η : ℝ} (hη : 0 < η) :
    IsUnit (K + ((η : ℂ) * Complex.I) • 1).det ∧
      IsContraction (1 - (2 * (η : ℂ) * Complex.I) • (K + ((η : ℂ) * Complex.I) • 1)⁻¹) := by
  set Z := K + ((η : ℂ) * Complex.I) • (1 : Matrix κ κ ℂ) with hZ
  have hZim : ∀ y, η * quadNorm y ≤ (star y ⬝ᵥ (Z *ᵥ y)).im := by
    intro y
    rw [hZ, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      star_dotProduct_self_eq, Complex.add_im, smul_eq_mul]
    have := hK y
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.mul_re]
    nlinarith
  have hunit : IsUnit Z.det := by
    rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
    intro a b hab
    by_contra hne
    have hx : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : Z *ᵥ (a - b) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hab
    have := hZim (a - b)
    rw [h0] at this
    have := quadNorm_pos hx
    simp at *
    nlinarith
  refine ⟨hunit, fun x => ?_⟩
  set y := Z⁻¹ *ᵥ x with hy
  have hZy : Z *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
  have hx : x = K *ᵥ y + ((η : ℂ) * Complex.I) • y := by
    rw [← hZy, hZ, add_mulVec, smul_mulVec, one_mulVec]
  have hUx : (1 - (2 * (η : ℂ) * Complex.I) • Z⁻¹) *ᵥ x =
      K *ᵥ y - ((η : ℂ) * Complex.I) • y := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, ← hy]
    conv_lhs => rw [hx]
    module
  rw [hUx]
  conv_rhs => rw [hx]
  have h4 := quadNorm_add_sub_sub (K *ᵥ y) (((η : ℂ) * Complex.I) • y)
  have h5 : (star (K *ᵥ y) ⬝ᵥ (((η : ℂ) * Complex.I) • y)).re =
      η * (star y ⬝ᵥ (K *ᵥ y)).im := by
    rw [dotProduct_smul, smul_eq_mul, ← conj_dotProduct y (K *ᵥ y)]
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have := hK y
  rw [h5] at h4
  nlinarith

/-!
## `Im K_c ⪰ 0` for Hermitian samples
-/

theorem im_quad_hermitian_eq_zero {κ : Type*} [Fintype κ] {M : Matrix κ κ ℂ}
    (hM : M.IsHermitian) (y : κ → ℂ) : (star y ⬝ᵥ (M *ᵥ y)).im = 0 := by
  have h : conj (star y ⬝ᵥ (M *ᵥ y)) = star y ⬝ᵥ (M *ᵥ y) := by
    rw [conj_dotProduct, star_mulVec, ← dotProduct_mulVec, hM.eq]
  have := congrArg Complex.im h
  simp at this
  linarith

/-- For Hermitian `G` and `ν ≥ 0`: `Im(u*(G - (e+s) + iν)⁻¹u) ≤ 0`. -/
theorem im_quad_inv_shift_nonpos {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (e s : ℝ) {ν : ℝ} (hν : 0 ≤ ν) (u : κ → ℂ) :
    (star u ⬝ᵥ ((G - collarShift e s ν • 1)⁻¹ *ᵥ u)).im ≤ 0 := by
  by_cases hZ : IsUnit (G - collarShift e s ν • (1 : Matrix κ κ ℂ)).det
  · set w := (G - collarShift e s ν • (1 : Matrix κ κ ℂ))⁻¹ *ᵥ u with hw
    have hu : u = (G - collarShift e s ν • (1 : Matrix κ κ ℂ)) *ᵥ w := by
      rw [hw, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]
    have h1 : star u ⬝ᵥ w = conj (star w ⬝ᵥ ((G - collarShift e s ν • 1) *ᵥ w)) := by
      rw [conj_dotProduct, ← hu]
    rw [h1, Complex.conj_im, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, star_dotProduct_self_eq, Complex.sub_im, im_quad_hermitian_eq_zero hG,
      smul_eq_mul, collarShift]
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.sub_re]
    nlinarith [quadNorm_nonneg w]
  · rw [nonsing_inv_apply_not_isUnit _ hZ]
    simp

theorem blockDiag_isHermitian {W : ℕ} {A : Fin 2 → Matrix (Fin W) (Fin W) ℂ}
    (hA : ∀ j, (A j).IsHermitian) : (BlockBand.Internal.Contracts.Layers.blockDiag A).IsHermitian := by
  ext x y
  rw [conjTranspose_apply]
  unfold BlockBand.Internal.Contracts.Layers.blockDiag
  by_cases h : x.1 = y.1
  · have h' : y.1 = x.1 := h.symm
    simp only [h, ↓reduceIte]
    exact (hA y.1).apply _ _
  · have h' : ¬ y.1 = x.1 := fun h'' => h h''.symm
    simp only [h, h', ↓reduceIte, star_zero]

/-- `Im(y* K_c y) ≥ 0`: Hermitian diagonals, common height `ν ≥ 0`. -/
theorem im_quad_collarReaction_nonneg (b e s : ℝ) {ν : ℝ} (hν : 0 ≤ ν) {W : ℕ}
    {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (y : Fin 2 × Fin W → ℂ) : 0 ≤ (star y ⬝ᵥ (collarReaction b e s ν ω *ᵥ y)).im := by
  rw [collarReaction]
  set B := bondMatrix .common ω.1.2
  have hB : star y ⬝ᵥ ((B * (ω.2 - collarShift e s ν • 1)⁻¹ * Bᴴ) *ᵥ y) =
      star (Bᴴ *ᵥ y) ⬝ᵥ ((ω.2 - collarShift e s ν • 1)⁻¹ *ᵥ (Bᴴ *ᵥ y)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      conjTranspose_conjTranspose]
  rw [sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, hB, smul_mulVec, one_mulVec,
    dotProduct_smul, star_dotProduct_self_eq, Complex.sub_im, Complex.sub_im,
    im_quad_hermitian_eq_zero (blockDiag_isHermitian hA), smul_eq_mul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  have hsh : (collarShift e s ν + ((boundaryZ b e).re : ℂ)).im = -ν := by
    simp [collarShift]
  rw [hsh]
  have h1 := im_quad_inv_shift_nonpos hG e s hν (Bᴴ *ᵥ y)
  nlinarith [quadNorm_nonneg y]

/-- The collar scattering matrix is a contraction for Hermitian samples (`η > 0`, `ν ≥ 0`). -/
theorem isContraction_collarScattering {b e s ν : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hν : 0 ≤ ν) {W : ℕ} {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian)
    (hG : ω.2.IsHermitian) : IsContraction (collarScattering b e s ν ω) :=
  (isContraction_cayley (im_quad_collarReaction_nonneg b e s hν hA hG) hη).2

/-!
## The law
-/

theorem isProbabilityMeasure_collarLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (collarLaw W b) := by
  unfold collarLaw layerLaw gueMeasure ginibreMeasure
    BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

theorem gueSample_isHermitian {ι : Type*} (t : NNReal) (X : ι × ι → ℂ) :
    (gueSample t X).IsHermitian := by
  ext a b
  simp [gueSample, conjTranspose_apply, Complex.conj_ofReal, add_comm]

theorem measurableSet_isHermitian {κ : Type*} [Fintype κ] :
    MeasurableSet {A : Matrix κ κ ℂ | A.IsHermitian} :=
  (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet

theorem measurable_gueSample {κ : Type*} (t : NNReal) :
    Measurable (gueSample (ι := κ) t) := by
  rw [Matrix.measurable_iff]
  intro a b
  simp only [gueSample, Matrix.of_apply]
  exact measurable_const.mul ((measurable_pi_apply _).add
    (Complex.continuous_conj.measurable.comp (measurable_pi_apply _)))

theorem ae_gue_isHermitian (κ : Type*) [Fintype κ] (t : NNReal) :
    ∀ᵐ A ∂gueMeasure κ t, A.IsHermitian :=
  (ae_map_iff (measurable_gueSample t).aemeasurable measurableSet_isHermitian).mpr
    (Eventually.of_forall (gueSample_isHermitian t))

theorem isProbabilityMeasure_gueMeasure' (κ : Type*) [Fintype κ] (t : NNReal) :
    IsProbabilityMeasure (gueMeasure κ t) := by
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

theorem isProbabilityMeasure_ginibreMeasure' (κ κ' : Type*) [Fintype κ] [Fintype κ']
    (t : NNReal) : IsProbabilityMeasure (ginibreMeasure κ κ' t) := by
  unfold ginibreMeasure
  infer_instance

/-- Almost surely the three collar diagonals are Hermitian. -/
theorem ae_collar_hermitian (W : ℕ) (b : ℝ) :
    ∀ᵐ ω ∂collarLaw W b, (∀ j, (ω.1.1 j).IsHermitian) ∧ ω.2.IsHermitian := by
  have : ∀ κ : Type, ∀ [Fintype κ], ∀ t, IsProbabilityMeasure (gueMeasure κ t) :=
    fun κ _ t => isProbabilityMeasure_gueMeasure' κ t
  have : ∀ t, IsProbabilityMeasure (ginibreMeasure (Fin W) (Fin W) t) :=
    fun t => isProbabilityMeasure_ginibreMeasure' _ _ t
  have hpi : ∀ᵐ A ∂(Measure.pi fun _ : Fin 2 =>
      gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))), ∀ j, (A j).IsHermitian := by
    rw [ae_all_iff]
    intro j
    exact Measure.tendsto_eval_ae_ae.eventually (ae_gue_isHermitian _ _)
  have h1 : ∀ᵐ ω ∂layerLaw W b .common, ∀ j, (ω.1 j).IsHermitian :=
    Measure.quasiMeasurePreserving_fst.ae hpi
  have h2 : ∀ᵐ ω ∂collarLaw W b, ∀ j, (ω.1.1 j).IsHermitian :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h3 : ∀ᵐ ω ∂collarLaw W b, ω.2.IsHermitian :=
    Measure.quasiMeasurePreserving_snd.ae (ae_gue_isHermitian _ _)
  filter_upwards [h2, h3] with ω h2 h3
  exact ⟨h2, h3⟩

/-!
## Measurability
-/

theorem measurable_matrix_inv' {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Measurable (fun N : Matrix κ κ ℂ => N⁻¹) := by
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).mul
    ((continuous_apply_apply i j).comp continuous_id.matrix_adjugate).measurable

theorem measurable_blockDiag_collar (W : ℕ) :
    Measurable (fun ω : CollarSample W => BlockBand.Internal.Contracts.Layers.blockDiag ω.1.1) := by
  rw [Matrix.measurable_iff]
  intro x y
  by_cases h : x.1 = y.1
  · simp only [BlockBand.Internal.Contracts.Layers.blockDiag, h, ↓reduceIte]
    fun_prop
  · simp only [BlockBand.Internal.Contracts.Layers.blockDiag, h, ↓reduceIte]
    exact measurable_const

theorem measurable_bondMatrix_collar (W : ℕ) :
    Measurable (fun ω : CollarSample W => bondMatrix .common ω.1.2) := by
  rw [Matrix.measurable_iff]
  intro x y
  simp only [bondMatrix, LayerShape.incident, ↓reduceIte]
  fun_prop

section MatrixMeasurability

variable {Ω : Type*} [MeasurableSpace Ω] {m n o : Type*} [Fintype n]

theorem measurable_matrix_sub {f g : Ω → Matrix m o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω - g ω) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simp only [Matrix.sub_apply]
  exact (hf i j).sub (hg i j)

theorem measurable_matrix_add {f g : Ω → Matrix m o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω + g ω) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simp only [Matrix.add_apply]
  exact (hf i j).add (hg i j)

theorem measurable_matrix_smul {f : Ω → Matrix m o ℂ} (c : ℂ) (hf : Measurable f) :
    Measurable (fun ω => c • f ω) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simpa only [Matrix.smul_apply, smul_eq_mul] using (hf i j).const_mul c

theorem measurable_matrix_mul {f : Ω → Matrix m n ℂ} {g : Ω → Matrix n o ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun ω => f ω * g ω) := by
  rw [Matrix.measurable_iff] at *
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (hf i k).mul (hg k j)

end MatrixMeasurability

theorem measurable_collarScattering (b e s ν : ℝ) (W : ℕ) :
    Measurable (fun ω : CollarSample W => collarScattering b e s ν ω) := by
  unfold collarScattering collarReaction
  have hB := measurable_bondMatrix_collar W
  have hBH : Measurable (fun ω : CollarSample W => (bondMatrix .common ω.1.2)ᴴ) :=
    (continuous_id.matrix_conjTranspose).measurable.comp hB
  have hG : Measurable (fun ω : CollarSample W => (ω.2 - collarShift e s ν • 1)⁻¹) :=
    measurable_matrix_inv'.comp (measurable_matrix_sub measurable_snd measurable_const)
  apply measurable_matrix_sub measurable_const
  apply measurable_matrix_smul
  apply measurable_matrix_inv'.comp
  apply measurable_matrix_add _ measurable_const
  apply measurable_matrix_sub (measurable_matrix_sub (measurable_blockDiag_collar W)
    measurable_const)
  exact measurable_matrix_mul (measurable_matrix_mul hB hG) hBH

end BlockBand.Endpoints.PhaseFractional
