module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBP
public import BlockBand.Native.CEH.ETH.BlockBand.Analysis.CauchyResolventBound
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Matrix aggregation for finite-coordinate GUE integration by parts

This module discharges the analytic side conditions of the coordinatewise
identity and recombines the diagonal and paired strict-upper real coordinates
with their exact normalized variances.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ComplexOrder
  Matrix.Norms.L2Operator

private theorem norm_matrix_entry_le_l2_opNorm
    {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ‖M i j‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (Pi.single j 1)
  let y : EuclideanSpace ℂ (Fin N) :=
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M e
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop := (Matrix.toEuclideanCLM
    (n := Fin N) (𝕜 := ℂ) M).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hyi : y.ofLp i = M i j := by simp [y, e]
  calc
    ‖M i j‖ = ‖y.ofLp i‖ := congrArg norm hyi.symm
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M‖ * ‖e‖ := hop
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, he, mul_one]

/-- A Hermitian resolvent entry is uniformly bounded along every Hermitian
real affine line.  The intentionally non-sharp factor-free estimate is the
usual `|Im z|⁻¹` bound. -/
theorem norm_coordinateHermitianResolvent_entry_le
    {N : ℕ} (H D : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.IsHermitian) (hD : D.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) (x : ℝ) :
    ‖coordinateResolvent
      (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) D x i j‖ ≤
      |z.im|⁻¹ := by
  let Hx := H + (x : ℂ) • D
  have hHx : Hx.IsHermitian :=
    hH.add (hD.smul (RCLike.conj_ofReal x))
  have hpencil :
      coordinatePencil
          (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) D x =
        Hx - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    ext p q
    simp [coordinatePencil, Hx]
    ring
  rw [coordinateResolvent, hpencil]
  apply (norm_matrix_entry_le_l2_opNorm _ i j).trans
  have hzero : (0 : Matrix (Fin N) (Fin N) ℂ).PosSemidef :=
    ⟨Matrix.isHermitian_zero, by intro u; simp⟩
  by_cases hzpos : 0 < z.im
  · let A := Hx - (z.re : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
    have hA : A.IsHermitian :=
      hHx.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re))
    have hshape :
        cauchyResolventPencil A 0 z.im 0 =
          (Hx - z • (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hHx.eq]
      ext p q
      by_cases hpq : p = q
      · subst q
        simp [A, cauchyResolventPencil, Complex.ext_iff]
      · simp [A, cauchyResolventPencil, hpq]
    have hb := norm_cauchyResolventPencil_nonsing_inv_le
      A 0 hA hzero hzpos (show 0 ≤ (0 : ℂ).im by simp)
    rw [hshape] at hb
    rw [← Matrix.conjTranspose_nonsing_inv,
      Matrix.l2_opNorm_conjTranspose] at hb
    simpa [abs_of_pos hzpos] using hb
  · have hzneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
    let A := Hx - (z.re : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
    have hA : A.IsHermitian :=
      hHx.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal z.re))
    have hshape :
        cauchyResolventPencil A 0 (-z.im) 0 =
          Hx - z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      ext p q
      by_cases hpq : p = q
      · subst q
        simp [A, Hx, cauchyResolventPencil, Complex.ext_iff]
        ring
      · simp [A, Hx, cauchyResolventPencil, hpq]
    have hb := norm_cauchyResolventPencil_nonsing_inv_le
      A 0 hA hzero (neg_pos.mpr hzneg)
      (show 0 ≤ (0 : ℂ).im by simp)
    rw [hshape] at hb
    simpa [abs_of_neg hzneg] using hb

/-- Every pencil on a Hermitian affine line is nonsingular off the real
axis. -/
theorem isUnit_det_coordinateHermitianPencil
    {N : ℕ} (H D : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.IsHermitian) (hD : D.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    IsUnit (coordinatePencil
      (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) D x).det := by
  let Hx := H + (x : ℂ) • D
  have hHx : Hx.IsHermitian :=
    hH.add (hD.smul (RCLike.conj_ofReal x))
  have hu := CEHNative.BlockBand.isUnit_resolventPencil
    Hx hHx hz
  have hpencil :
      coordinatePencil
          (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) D x =
        -(z • (1 : Matrix (Fin N) (Fin N) ℂ) - Hx) := by
    ext p q
    simp [coordinatePencil, Hx]
    ring
  rw [hpencil]
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    ((IsUnit.neg_iff _).2 hu)

/-- The two-resolvent derivative observable has an explicit uniform bound
along a Hermitian coordinate line. -/
theorem norm_coordinateHermitianResolvent_derivative_le
    {N : ℕ} (H D : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.IsHermitian) (hD : D.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) (x : ℝ) :
    ‖(coordinateResolvent
        (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) D x *
      D * coordinateResolvent
        (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) D x) i j‖ ≤
      |z.im|⁻¹ ^ 2 * ∑ a : Fin N, ∑ b : Fin N, ‖D a b‖ := by
  let G := coordinateResolvent
    (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) D x
  simp only [Matrix.mul_apply]
  calc
    ‖∑ b, (∑ a, G i a * D a b) * G b j‖
        ≤ ∑ b, ‖(∑ a, G i a * D a b) * G b j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b, ∑ a, |z.im|⁻¹ ^ 2 * ‖D a b‖ := by
      apply Finset.sum_le_sum
      intro b hb
      calc
        ‖(∑ a, G i a * D a b) * G b j‖
            ≤ ‖∑ a, G i a * D a b‖ * ‖G b j‖ := norm_mul_le _ _
        _ ≤ (∑ a, ‖G i a * D a b‖) * ‖G b j‖ := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ (∑ a, |z.im|⁻¹ * ‖D a b‖) * |z.im|⁻¹ := by
          gcongr
          · exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right
                (norm_coordinateHermitianResolvent_entry_le
                  H D hH hD hz i a x) (norm_nonneg _))
          · exact norm_coordinateHermitianResolvent_entry_le
              H D hH hD hz b j x
        _ = ∑ a, |z.im|⁻¹ ^ 2 * ‖D a b‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = |z.im|⁻¹ ^ 2 * ∑ a, ∑ b, ‖D a b‖ := by
      rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

/-- The first absolute moment of a nondegenerate centered Gaussian density is
Lebesgue-integrable, in the exact density form used by Gaussian IBP. -/
theorem integrable_mul_centeredGaussianPDFReal
    (v : NNReal) (hv : v ≠ 0) :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 v x) := by
  rw [gaussianPDFReal_def]
  have hvR : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hkernel :
      Integrable (fun x : ℝ => x *
        Real.exp (-((2 * (v : ℝ))⁻¹) * x ^ 2)) :=
    integrable_mul_exp_neg_mul_sq (by positivity)
  convert hkernel.const_mul
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ using 1
  funext x
  simp only [sub_zero]
  field_simp

/-- **Coordinate GUE IBP with all density hypotheses discharged.**  A fixed
Hermitian background shifted by a nonreal spectral parameter supplies the
uniform resolvent bounds needed for each of the three whole-line density
integrals. -/
theorem normalizedGUECoordinateHermitianResolventEntry_IBP
    {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N))) (i j : Fin N) :
    (∫ x : ℝ, (x : ℂ) *
        coordinateResolvent
          (H - z • (1 : Matrix (Fin N) (Fin N) ℂ))
          (gueCoordinateDirection N k) x i j
      ∂gaussianReal 0
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℝ) *
        ∫ x : ℝ,
          (-(coordinateResolvent
              (H - z • (1 : Matrix (Fin N) (Fin N) ℂ))
              (gueCoordinateDirection N k) x *
            gueCoordinateDirection N k *
            coordinateResolvent
              (H - z • (1 : Matrix (Fin N) (Fin N) ℂ))
              (gueCoordinateDirection N k) x) i j)
        ∂gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k) := by
  let D := gueCoordinateDirection N k
  let B := H - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  let v := hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
    (by positivity) k
  have hD : D.IsHermitian := gueCoordinateDirection_isHermitian N k
  have hinv (x : ℝ) : IsUnit (coordinatePencil B D x).det :=
    isUnit_det_coordinateHermitianPencil H D hH hD hz x
  have hv : v ≠ 0 := ne_of_gt
    (hermitianGUEFinCoordinateVariance_pos N
      (show 0 < 1 / (N : ℝ) by positivity) k)
  have hcontG (p q : Fin N) :
      Continuous (fun x : ℝ => coordinateResolvent B D x p q) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (differentiableAt_coordinateResolvent B D p q x
      (hinv x)).continuousAt
  have hmeasG (p q : Fin N) :
      AEStronglyMeasurable
        (fun x : ℝ => coordinateResolvent B D x p q) :=
    (hcontG p q).aestronglyMeasurable
  have hboundG (p q : Fin N) :
      ∀ᵐ x : ℝ, ‖coordinateResolvent B D x p q‖ ≤ |z.im|⁻¹ :=
    ae_of_all _ fun x =>
      norm_coordinateHermitianResolvent_entry_le H D hH hD hz p q x
  have hpdfC : Integrable
      (fun x : ℝ => ((gaussianPDFReal 0 v x : ℝ) : ℂ)) :=
    (integrable_gaussianPDFReal 0 v).ofReal
  have hxpdfC : Integrable
      (fun x : ℝ => ((x * gaussianPDFReal 0 v x : ℝ) : ℂ)) :=
    (integrable_mul_centeredGaussianPDFReal v hv).ofReal
  have hf : Integrable (fun x : ℝ =>
      ((gaussianPDFReal 0 v x : ℝ) : ℂ) *
        coordinateResolvent B D x i j) :=
    hpdfC.mul_bdd (hmeasG i j) (hboundG i j)
  have hxf : Integrable (fun x : ℝ =>
      ((x * gaussianPDFReal 0 v x : ℝ) : ℂ) *
        coordinateResolvent B D x i j) :=
    hxpdfC.mul_bdd (hmeasG i j) (hboundG i j)
  have hcontDeriv : Continuous (fun x : ℝ =>
      -(coordinateResolvent B D x * D *
        coordinateResolvent B D x) i j) := by
    simp only [Matrix.mul_apply]
    fun_prop
  have hboundDeriv :
      ∀ᵐ x : ℝ,
        ‖-(coordinateResolvent B D x * D *
          coordinateResolvent B D x) i j‖ ≤
          |z.im|⁻¹ ^ 2 * ∑ a : Fin N, ∑ b : Fin N, ‖D a b‖ :=
    ae_of_all _ fun x => by
      rw [norm_neg]
      exact norm_coordinateHermitianResolvent_derivative_le
        H D hH hD hz i j x
  have hdf : Integrable (fun x : ℝ =>
      ((gaussianPDFReal 0 v x : ℝ) : ℂ) *
        (-(coordinateResolvent B D x * D *
          coordinateResolvent B D x) i j)) :=
    hpdfC.mul_bdd hcontDeriv.aestronglyMeasurable hboundDeriv
  exact normalizedGUECoordinateResolventEntry_IBP hN B k i j
    hinv hxf hdf hf

/-- The normalized finite-coordinate covariance contraction. -/
def normalizedGUECovarianceContraction (N : ℕ)
    (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun p q => ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
      (by positivity) k : ℂ) *
      (gueCoordinateDirection N k * X * gueCoordinateDirection N k) p q

@[simp] theorem piSingle_hermitianCoordinateEquivFin_comp (N : ℕ)
    (c : HermitianCoordinate N) :
    Pi.single ((hermitianCoordinateEquivFin N) c) (1 : ℝ) ∘
        (hermitianCoordinateEquivFin N) =
      Pi.single c 1 := by
  funext c'
  simp [Pi.single_apply]

@[simp] theorem sum_eqIndicator_mul_eqIndicator
    {α : Type*} [Fintype α] [DecidableEq α]
    (w u v : ℂ) (c d : α) :
    (∑ x : α, w * ((if c = x then 1 else 0) : ℂ) * u *
      (((if d = x then 1 else 0) : ℂ) * v)) =
      if c = d then w * u * v else 0 := by
  by_cases h : c = d
  · subst d
    simp
  · simp [h]

@[simp] theorem ofReal_eqIndicator (P : Prop) [Decidable P] :
    (((if P then 1 else 0) : ℝ) : ℂ) =
      if P then 1 else 0 := by
  split <;> simp_all

@[simp] theorem coe_nnreal_mk_complex (r : ℝ) (hr : 0 ≤ r) :
    (((⟨r, hr⟩ : NNReal) : ℝ) : ℂ) = (r : ℂ) := rfl

@[simp] theorem star_eqIndicator_mul_I (P : Prop) [Decidable P] :
    star ((if P then Complex.I else 0) : ℂ) =
      if P then -Complex.I else 0 := by
  split <;> simp_all

@[simp] theorem normalizedVariance_equiv_inl {N : ℕ} (hN : 0 < N)
    (i : Fin N) :
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ)) (by positivity)
      ((hermitianCoordinateEquivFin N) (.inl i)) : ℂ) =
      ((1 / (N : ℝ) : ℝ) : ℂ) := by
  exact_mod_cast normalizedCoordinateVariance_diagonal hN
    ((hermitianCoordinateEquivFin N) (.inl i)) i
    ((hermitianCoordinateEquivFin N).symm_apply_apply (.inl i))

@[simp] theorem normalizedVariance_equiv_inr {N : ℕ} (hN : 0 < N)
    (c : StrictUpperIndex N ⊕ StrictUpperIndex N) :
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ)) (by positivity)
      ((hermitianCoordinateEquivFin N) (.inr c)) : ℂ) =
      ((1 / (2 * (N : ℝ)) : ℝ) : ℂ) := by
  exact_mod_cast normalizedCoordinateVariance_offDiagonal hN
    ((hermitianCoordinateEquivFin N) (.inr c)) c
    ((hermitianCoordinateEquivFin N).symm_apply_apply (.inr c))

@[simp] theorem sum_weight_mul_eqIndicator_mul_eqIndicator
    {α : Type*} [Fintype α] [DecidableEq α]
    (w : ℂ) (c d : α) :
    (∑ x : α, w * ((if c = x then 1 else 0) : ℂ) *
      ((if d = x then 1 else 0) : ℂ)) =
      if c = d then w else 0 := by
  by_cases h : c = d
  · subst d
    simp
  · simp [h]

@[simp] theorem sum_weight_mul_eqIndicator_I_mul_eqIndicator_I
    {α : Type*} [Fintype α] [DecidableEq α]
    (w : ℂ) (c d : α) :
    (∑ x : α, w * (((if c = x then 1 else 0) : ℂ) * Complex.I) *
      (((if d = x then 1 else 0) : ℂ) * Complex.I)) =
      if c = d then -w else 0 := by
  by_cases h : c = d
  · subst d
    simp
    calc
      w * Complex.I * Complex.I = w * (Complex.I * Complex.I) := by ring
      _ = -w := by rw [Complex.I_mul_I]; ring
  · simp [h]

/-- Coordinate form of the normalized GUE covariance tensor. -/
theorem normalizedGUECoordinateKernel {N : ℕ} (hN : 0 < N)
    (p a b q : Fin N) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate N)),
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℂ) *
        gueCoordinateDirection N k p a * gueCoordinateDirection N k b q) =
      if p = q ∧ a = b then (N : ℂ)⁻¹ else 0 := by
  rw [← (hermitianCoordinateEquivFin N).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [gueCoordinateDirection, hermitianGUEBlock,
    hermitianOfFinCoordinates, hermitianOfCoordinates]
  simp_rw [piSingle_hermitianCoordinateEquivFin_comp]
  unfold hermitianMatrixOfCoordinates hermitianUpperEntry
  simp_rw [normalizedVariance_equiv_inl hN,
    normalizedVariance_equiv_inr hN]
  by_cases hpq : p = q <;> by_cases hab : a = b
  · subst q
    subst b
    by_cases hpa : p = a
    · subst a
      simp [Pi.single_apply]
    · by_cases hlt : p < a
      · simp [Pi.single_apply, hpa, Ne.symm hpa, hlt,
          not_lt_of_ge (le_of_lt hlt)]
        field_simp [show (N : ℂ) ≠ 0 by
          exact_mod_cast (Nat.ne_of_gt hN)]
        rw [Complex.I_sq]
        norm_num
      · have halt : a < p := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpa)
        simp [Pi.single_apply, hpa, Ne.symm hpa, hlt,
          halt]
        field_simp [show (N : ℂ) ≠ 0 by
          exact_mod_cast (Nat.ne_of_gt hN)]
        rw [Complex.I_sq]
        norm_num
  · simp [hpq, hab, Pi.single_apply]
    split_ifs at * <;> simp_all
  · simp [hpq, hab, Pi.single_apply]
    split_ifs at * <;> simp_all
  · simp [hpq, hab, Pi.single_apply]
    split_ifs at * <;> simp_all
    all_goals
      calc
        _ = (N : ℂ)⁻¹ * 2⁻¹ *
            (1 + Complex.I * Complex.I) := by ring
        _ = 0 := by rw [Complex.I_mul_I]; ring

/-- The diagonal plus paired real/imaginary strict-upper coordinates recombine
to the normalized GUE covariance `N⁻¹ Tr(X) I`. -/
theorem normalizedGUECovarianceContraction_eq {N : ℕ} (hN : 0 < N)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    normalizedGUECovarianceContraction N X =
      ((N : ℂ)⁻¹ * X.trace) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext p q
  unfold normalizedGUECovarianceContraction
  simp_rw [Matrix.mul_apply]
  have hreorder :
      (∑ k, (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
        ∑ b, (∑ a, gueCoordinateDirection N k p a * X a b) *
          gueCoordinateDirection N k b q) =
      ∑ b, ∑ a, X a b * ∑ k,
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          gueCoordinateDirection N k p a *
          gueCoordinateDirection N k b q := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hreorder]
  simp_rw [normalizedGUECoordinateKernel hN]
  by_cases hpq : p = q
  · subst q
    simp [Matrix.trace]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp [hpq]

/-- Integration under the product of two normalized full-matrix GUE laws is
exactly integration over the repository's independent paired real-coordinate
model.  This is the product-law transport used after coordinatewise IBP. -/
theorem integral_normalizedGUEProduct_eq_pairCoordinates
    {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : HermitianMatrix (Fin N) × HermitianMatrix (Fin N) → E)
    (hΦ : AEStronglyMeasurable Φ
      ((CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))).prod
        (CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))))) :
    (∫ P, Φ P
      ∂((CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))).prod
        (CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))))) =
      ∫ x : CEHNative.BlockBand.CEH.GUEPairSample N,
        Φ (CEHNative.BlockBand.CEH.guePairFirstBlock x,
          CEHNative.BlockBand.CEH.guePairSecondBlock x)
      ∂CEHNative.BlockBand.CEH.guePairMeasure
        N (1 / (N : ℝ)) (by positivity) := by
  let pairMap :
      CEHNative.BlockBand.CEH.GUEPairSample N →
        HermitianMatrix (Fin N) × HermitianMatrix (Fin N) :=
    fun x =>
      (CEHNative.BlockBand.CEH.guePairFirstBlock x,
        CEHNative.BlockBand.CEH.guePairSecondBlock x)
  have hmap :
      Measure.map pairMap
          (CEHNative.BlockBand.CEH.guePairMeasure
            N (1 / (N : ℝ)) (by positivity)) =
        ((CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
            N 1 : Measure (HermitianMatrix (Fin N))).prod
          (CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
            N 1 : Measure (HermitianMatrix (Fin N)))) := by
    exact CEHNative.BlockBand.CEH.guePairBlocks_joint_map_eq_normalized_prod
      N (by norm_num)
  have hpair : Measurable pairMap :=
    (CEHNative.BlockBand.CEH.measurable_guePairFirstBlock).prodMk
      (CEHNative.BlockBand.CEH.measurable_guePairSecondBlock)
  have hΦmap : AEStronglyMeasurable Φ
      (Measure.map pairMap
        (CEHNative.BlockBand.CEH.guePairMeasure
          N (1 / (N : ℝ)) (by positivity))) := by
    rw [hmap]
    exact hΦ
  rw [← hmap]
  exact integral_map hpair.aemeasurable hΦmap

/-- **Normalized product-law covariance aggregate.**  After transporting to
the paired coordinate law, the complete diagonal plus paired real/imaginary
GUE covariance sum is exactly `N⁻¹ Tr(X) I`, pointwise inside the matrix
integral. -/
theorem integral_normalizedGUECovarianceContraction_eq_pairCoordinates
    {N : ℕ} (hN : 0 < N)
    (X : HermitianMatrix (Fin N) × HermitianMatrix (Fin N) →
      Matrix (Fin N) (Fin N) ℂ)
    (hX : AEStronglyMeasurable
      (fun P => normalizedGUECovarianceContraction N (X P))
      ((CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))).prod
        (CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))))) :
    (∫ P, normalizedGUECovarianceContraction N (X P)
      ∂((CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))).prod
        (CEHNative.BlockBand.CEH.normalizedHermitianGUEMatrixLaw
          N 1 : Measure (HermitianMatrix (Fin N))))) =
      ∫ x : CEHNative.BlockBand.CEH.GUEPairSample N,
        ((N : ℂ)⁻¹ *
          (X (CEHNative.BlockBand.CEH.guePairFirstBlock x,
            CEHNative.BlockBand.CEH.guePairSecondBlock x)).trace) •
          (1 : Matrix (Fin N) (Fin N) ℂ)
      ∂CEHNative.BlockBand.CEH.guePairMeasure
        N (1 / (N : ℝ)) (by positivity) := by
  rw [integral_normalizedGUEProduct_eq_pairCoordinates
    (fun P => normalizedGUECovarianceContraction N (X P)) hX]
  apply integral_congr_ae
  filter_upwards with x
  exact normalizedGUECovarianceContraction_eq hN _

end CEHNative.BlockBand.External.CEH
