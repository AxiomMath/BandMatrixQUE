module

public import BlockBand.Critical.Collar.DilationVariance.CauchyPoissonBounded
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Dilation resolvents, their exact Cauchy mean, and the matrix variance identities

Setting: a finite index type `ι`; `Xh` Hermitian, `Y ⪰ 0` (`Matrix.PosSemidef`), `z : ℂ` with
`η = Im z > 0`; `t` is a standard real Cauchy variable, i.e. the law
`ProbabilityTheory.cauchyMeasure 0 1` (density `1/(π(1+t²))`). Expectations of matrices are
entrywise Bochner integrals; integrability of every entry is part of each conclusion.

* `absorbedResolvent Xh Y z = (z - Xh + iY)⁻¹` is `R` (`X = Xh - iY`);
* `dilationResolvent Xh Y z t = (z - Xh - tY)⁻¹` is `R_t`.

Proof: `w ↦ (z - Xh + wY)⁻¹` is analytic and bounded by `η⁻¹` on the closed upper half-plane
(no normality of `X`, no commutation of `Xh` and `Y`), so the bounded Cauchy–Poisson formula
of `CauchyPoissonBounded` evaluates its Cauchy average at `w = i`; `t ↦ -t` preserves the
Cauchy law. The two variance identities follow from the Ward identities
`R_tᴴ - R_t = 2iη R_tᴴ R_t = 2iη R_t R_tᴴ` and
`Rᴴ - R = 2i Rᴴ(η + Y)R = 2i R(η + Y)Rᴴ` and linearity of the mean (no product of two
random matrices is ever averaged).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace BlockBand.Critical.Collar

open CoareaNative.BlockBand (standardCauchyWeight cauchyResolventPencil
  isUnit_cauchyResolventPencil norm_cauchyResolventPencil_nonsing_inv_le)

/-- The standard real Cauchy law (location `0`, scale `1`, density `1/(π(1+t²))`). -/
abbrev stdCauchy : Measure ℝ := ProbabilityTheory.cauchyMeasure 0 1

/-!
### Scalar Cauchy means
-/

/-- `IsCauchyMean f v`: `f` is integrable for the standard Cauchy law and its mean is `v`. -/
def IsCauchyMean (f : ℝ → ℂ) (v : ℂ) : Prop :=
  Integrable f stdCauchy ∧ ∫ t, f t ∂stdCauchy = v

namespace IsCauchyMean

theorem const (c : ℂ) : IsCauchyMean (fun _ => c) c :=
  ⟨integrable_const c, by simp⟩

theorem add {f g : ℝ → ℂ} {a b : ℂ} (hf : IsCauchyMean f a) (hg : IsCauchyMean g b) :
    IsCauchyMean (fun t => f t + g t) (a + b) :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2]⟩

theorem neg {f : ℝ → ℂ} {a : ℂ} (hf : IsCauchyMean f a) :
    IsCauchyMean (fun t => -f t) (-a) :=
  ⟨hf.1.neg, by rw [integral_neg, hf.2]⟩

theorem sub {f g : ℝ → ℂ} {a b : ℂ} (hf : IsCauchyMean f a) (hg : IsCauchyMean g b) :
    IsCauchyMean (fun t => f t - g t) (a - b) :=
  ⟨hf.1.sub hg.1, by rw [integral_sub hf.1 hg.1, hf.2, hg.2]⟩

theorem const_mul {f : ℝ → ℂ} {a : ℂ} (hf : IsCauchyMean f a) (c : ℂ) :
    IsCauchyMean (fun t => c * f t) (c * a) :=
  ⟨hf.1.const_mul c, by rw [integral_const_mul, hf.2]⟩

theorem mul_const {f : ℝ → ℂ} {a : ℂ} (hf : IsCauchyMean f a) (c : ℂ) :
    IsCauchyMean (fun t => f t * c) (a * c) :=
  ⟨hf.1.mul_const c, by rw [integral_mul_const, hf.2]⟩

theorem star {f : ℝ → ℂ} {a : ℂ} (hf : IsCauchyMean f a) :
    IsCauchyMean (fun t => (starRingEnd ℂ) (f t)) ((starRingEnd ℂ) a) :=
  ⟨(RCLike.conjCLE (K := ℂ)).toContinuousLinearMap.integrable_comp hf.1,
    by rw [integral_conj, hf.2]⟩

theorem sum {κ : Type*} (s : Finset κ) {f : κ → ℝ → ℂ} {a : κ → ℂ}
    (hf : ∀ k ∈ s, IsCauchyMean (f k) (a k)) :
    IsCauchyMean (fun t => ∑ k ∈ s, f k t) (∑ k ∈ s, a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (0 : ℂ)
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k (Finset.mem_insert_self k s)).add
      (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))

theorem congr {f g : ℝ → ℂ} {a b : ℂ} (hf : IsCauchyMean f a) (hfg : ∀ t, f t = g t)
    (hab : a = b) : IsCauchyMean g b := by
  have : f = g := funext hfg
  subst this hab
  exact hf

end IsCauchyMean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise Cauchy mean of a random matrix. -/
def IsCauchyMatrixMean (F : ℝ → Matrix ι ι ℂ) (M : Matrix ι ι ℂ) : Prop :=
  ∀ i j, IsCauchyMean (fun t => F t i j) (M i j)

namespace IsCauchyMatrixMean

theorem const (M : Matrix ι ι ℂ) : IsCauchyMatrixMean (fun _ => M) M :=
  fun i j => IsCauchyMean.const (M i j)

theorem add {F G : ℝ → Matrix ι ι ℂ} {A B : Matrix ι ι ℂ}
    (hF : IsCauchyMatrixMean F A) (hG : IsCauchyMatrixMean G B) :
    IsCauchyMatrixMean (fun t => F t + G t) (A + B) :=
  fun i j => (hF i j).add (hG i j)

theorem sub {F G : ℝ → Matrix ι ι ℂ} {A B : Matrix ι ι ℂ}
    (hF : IsCauchyMatrixMean F A) (hG : IsCauchyMatrixMean G B) :
    IsCauchyMatrixMean (fun t => F t - G t) (A - B) :=
  fun i j => (hF i j).sub (hG i j)

theorem smul {F : ℝ → Matrix ι ι ℂ} {A : Matrix ι ι ℂ}
    (hF : IsCauchyMatrixMean F A) (c : ℂ) :
    IsCauchyMatrixMean (fun t => c • F t) (c • A) :=
  fun i j => by simpa using (hF i j).const_mul c

theorem const_mul {F : ℝ → Matrix ι ι ℂ} {A : Matrix ι ι ℂ}
    (hF : IsCauchyMatrixMean F A) (B : Matrix ι ι ℂ) :
    IsCauchyMatrixMean (fun t => B * F t) (B * A) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact IsCauchyMean.sum _ fun k _ => (hF k j).const_mul (B i k)

theorem mul_const {F : ℝ → Matrix ι ι ℂ} {A : Matrix ι ι ℂ}
    (hF : IsCauchyMatrixMean F A) (B : Matrix ι ι ℂ) :
    IsCauchyMatrixMean (fun t => F t * B) (A * B) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact IsCauchyMean.sum _ fun k _ => (hF i k).mul_const (B k j)

theorem conjTranspose {F : ℝ → Matrix ι ι ℂ} {A : Matrix ι ι ℂ}
    (hF : IsCauchyMatrixMean F A) :
    IsCauchyMatrixMean (fun t => (F t)ᴴ) Aᴴ := by
  intro i j
  simpa [Matrix.conjTranspose_apply] using (hF j i).star

theorem congr {F G : ℝ → Matrix ι ι ℂ} {A B : Matrix ι ι ℂ}
    (hF : IsCauchyMatrixMean F A) (hFG : ∀ t, F t = G t) (hAB : A = B) :
    IsCauchyMatrixMean G B := by
  have : F = G := funext hFG
  subst this hAB
  exact hF

end IsCauchyMatrixMean

/-!
### The pencil and the two resolvents
-/

/-- The affine matrix pencil `w ↦ z - Xh + wY` (`w : ℂ`). -/
def dilationPencil (Xh Y : Matrix ι ι ℂ) (z w : ℂ) : Matrix ι ι ℂ :=
  z • (1 : Matrix ι ι ℂ) - Xh + w • Y

/-- The dilated resolvent `R_t = (z - Xh - tY)⁻¹`, `t` real. -/
def dilationResolvent (Xh Y : Matrix ι ι ℂ) (z : ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  (z • (1 : Matrix ι ι ℂ) - Xh - (t : ℂ) • Y)⁻¹

/-- The absorbed resolvent `R = (z - Xh + iY)⁻¹ = (z - X)⁻¹`, `X = Xh - iY`. -/
def absorbedResolvent (Xh Y : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  (z • (1 : Matrix ι ι ℂ) - Xh + Complex.I • Y)⁻¹

theorem dilationResolvent_eq_pencil (Xh Y : Matrix ι ι ℂ) (z : ℂ) (t : ℝ) :
    dilationResolvent Xh Y z t = (dilationPencil Xh Y z (-(t : ℂ)))⁻¹ := by
  simp [dilationResolvent, dilationPencil, sub_eq_add_neg, neg_smul]

theorem absorbedResolvent_eq_pencil (Xh Y : Matrix ι ι ℂ) (z : ℂ) :
    absorbedResolvent Xh Y z = (dilationPencil Xh Y z Complex.I)⁻¹ := rfl

theorem dilationPencil_eq_cauchyResolventPencil (Xh Y : Matrix ι ι ℂ) (z w : ℂ) :
    dilationPencil Xh Y z w =
      cauchyResolventPencil ((z.re : ℂ) • (1 : Matrix ι ι ℂ) - Xh) Y z.im w := by
  ext i j
  simp only [dilationPencil, cauchyResolventPencil, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · simp
    linear_combination -(Complex.re_add_im z)
  · simp

theorem isHermitian_re_smul_one_sub (Xh : Matrix ι ι ℂ) (hXh : Xh.IsHermitian) (r : ℝ) :
    ((r : ℂ) • (1 : Matrix ι ι ℂ) - Xh).IsHermitian := by
  refine IsHermitian.sub ?_ hXh
  simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]

variable {Xh Y : Matrix ι ι ℂ} {z : ℂ}

theorem isUnit_dilationPencil (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) (hz : 0 < z.im)
    {w : ℂ} (hw : 0 ≤ w.im) : IsUnit (dilationPencil Xh Y z w) := by
  rw [dilationPencil_eq_cauchyResolventPencil]
  exact isUnit_cauchyResolventPencil _ Y (isHermitian_re_smul_one_sub Xh hXh z.re) hY hz hw

/-- Sharp operator-norm bound `‖(z - Xh + wY)⁻¹‖ ≤ (Im z)⁻¹` on the closed upper half-plane
`0 ≤ Im w` (Euclidean operator norm). -/
theorem norm_dilationPencil_inv_le (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) (hz : 0 < z.im)
    {w : ℂ} (hw : 0 ≤ w.im) : ‖(dilationPencil Xh Y z w)⁻¹‖ ≤ z.im⁻¹ := by
  rw [dilationPencil_eq_cauchyResolventPencil]
  exact norm_cauchyResolventPencil_nonsing_inv_le _ Y
    (isHermitian_re_smul_one_sub Xh hXh z.re) hY hz hw

/-- Entries are bounded by the Euclidean operator norm. -/
theorem norm_entry_le_l2_opNorm (M : Matrix ι ι ℂ) (i j : ι) : ‖M i j‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  let y : EuclideanSpace ℂ ι := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M e
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hyi : y.ofLp i = M i j := by simp [y, e]
  calc
    ‖M i j‖ = ‖y.ofLp i‖ := congrArg norm hyi.symm
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖ * ‖e‖ := hop
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, he, mul_one]

/-- Each entry of `w ↦ (z - Xh + wY)⁻¹` is analytic at every point of the closed upper
half-plane. -/
theorem analyticAt_dilationPencil_inv_apply (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) {w : ℂ} (hw : 0 ≤ w.im) (i j : ι) :
    AnalyticAt ℂ (fun w => (dilationPencil Xh Y z w)⁻¹ i j) w := by
  have hU := isUnit_dilationPencil hXh hY hz hw
  have hp : AnalyticAt ℂ (dilationPencil Xh Y z) w := by
    unfold dilationPencil
    fun_prop
  have hinv : AnalyticAt ℂ Ring.inverse (dilationPencil Xh Y z w) := by
    rw [← hU.unit_spec]
    exact analyticAt_inverse (𝕜 := ℂ) hU.unit
  let e : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h := (e.analyticAt _).comp (hinv.comp hp)
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact h

/-- Continuity of each entry of `t ↦ R_t`. -/
theorem continuous_dilationResolvent_apply (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) (i j : ι) :
    Continuous (fun t : ℝ => dilationResolvent Xh Y z t i j) := by
  rw [continuous_iff_continuousAt]
  intro t
  simp_rw [dilationResolvent_eq_pencil]
  have h := (analyticAt_dilationPencil_inv_apply hXh hY hz
    (w := -(t : ℂ)) (by simp) i j).continuousAt
  have hc : Continuous (fun s : ℝ => -(s : ℂ)) := by fun_prop
  exact h.comp (f := fun s : ℝ => -(s : ℂ)) hc.continuousAt

theorem continuous_dilationResolvent (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) : Continuous (fun t : ℝ => dilationResolvent Xh Y z t) :=
  continuous_pi fun i => continuous_pi fun j => continuous_dilationResolvent_apply hXh hY hz i j

theorem norm_dilationResolvent_le (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) (t : ℝ) : ‖dilationResolvent Xh Y z t‖ ≤ z.im⁻¹ := by
  rw [dilationResolvent_eq_pencil]
  exact norm_dilationPencil_inv_le hXh hY hz (by simp)

theorem norm_absorbedResolvent_le (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) : ‖absorbedResolvent Xh Y z‖ ≤ z.im⁻¹ := by
  rw [absorbedResolvent_eq_pencil]
  exact norm_dilationPencil_inv_le hXh hY hz (by simp)

/-- **Part (i) of the dilation variance lemma, entrywise.** For every entry `(i, j)`,
`t ↦ (R_t)ᵢⱼ` is integrable for the standard Cauchy law and `E_t (R_t)ᵢⱼ = Rᵢⱼ`. -/
theorem isCauchyMatrixMean_dilationResolvent (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) :
    IsCauchyMatrixMean (dilationResolvent Xh Y z) (absorbedResolvent Xh Y z) := by
  intro i j
  let F : ℂ → ℂ := fun w => (dilationPencil Xh Y z w)⁻¹ i j
  have hFA : ∀ w : ℂ, 0 ≤ w.im → AnalyticAt ℂ F w := fun w hw =>
    analyticAt_dilationPencil_inv_apply hXh hY hz hw i j
  have hFM : ∀ w : ℂ, 0 ≤ w.im → ‖F w‖ ≤ z.im⁻¹ := fun w hw =>
    (norm_entry_le_l2_opNorm _ i j).trans (norm_dilationPencil_inv_le hXh hY hz hw)
  refine ⟨?_, ?_⟩
  · refine Integrable.of_bound
      (continuous_dilationResolvent_apply hXh hY hz i j).aestronglyMeasurable z.im⁻¹
      (Filter.Eventually.of_forall fun t => ?_)
    exact (norm_entry_le_l2_opNorm _ i j).trans (norm_dilationResolvent_le hXh hY hz t)
  · have hneg : (fun t : ℝ => dilationResolvent Xh Y z t i j) = fun t : ℝ => F (-(t : ℂ)) := by
      funext t
      rw [dilationResolvent_eq_pencil]
    rw [hneg]
    have h1 := integral_cauchyMeasure_comp_neg (fun t : ℝ => F (t : ℂ))
    simp only [Complex.ofReal_neg] at h1
    rw [h1, integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul,
      integral_standardCauchyWeight_smul_eq_of_analyticAt F hFA _ hFM]
    rfl

/-!
### Ward identities
-/

/-- Abstract Ward identity: for invertible `P` with `Q = P⁻¹`,
`Qᴴ - Q = Qᴴ (P - Pᴴ) Q`. -/
theorem conjTranspose_inv_sub_inv_eq_left (P : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    (P⁻¹)ᴴ - P⁻¹ = (P⁻¹)ᴴ * (P - Pᴴ) * P⁻¹ := by
  have h1 : P * P⁻¹ = 1 := P.mul_nonsing_inv hP
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h1, Matrix.mul_one, h2,
    Matrix.one_mul]

/-- Abstract Ward identity, other order: `Qᴴ - Q = Q (P - Pᴴ) Qᴴ`. -/
theorem conjTranspose_inv_sub_inv_eq_right (P : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    (P⁻¹)ᴴ - P⁻¹ = P⁻¹ * (P - Pᴴ) * (P⁻¹)ᴴ := by
  have h1 : P⁻¹ * P = 1 := P.nonsing_inv_mul hP
  have h2 : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
    Matrix.mul_one]

theorem dilationPencil_sub_conjTranspose (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) (w : ℂ) :
    dilationPencil Xh Y z w - (dilationPencil Xh Y z w)ᴴ =
      ((2 * z.im : ℝ) * Complex.I) • (1 : Matrix ι ι ℂ) +
        ((2 * w.im : ℝ) * Complex.I) • Y := by
  have hYh : Yᴴ = Y := hY.isHermitian.eq
  have hXe : Xhᴴ = Xh := hXh.eq
  simp only [dilationPencil, conjTranspose_add, conjTranspose_sub, conjTranspose_smul,
    conjTranspose_one, hYh, hXe]
  have hz' : z - star z = ((2 * z.im : ℝ) * Complex.I) := by
    apply Complex.ext <;> simp; ring
  have hw' : w - star w = ((2 * w.im : ℝ) * Complex.I) := by
    apply Complex.ext <;> simp; ring
  rw [← hz', ← hw', sub_smul, sub_smul]
  abel

theorem isUnit_det_dilationPencil (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) (hz : 0 < z.im)
    {w : ℂ} (hw : 0 ≤ w.im) : IsUnit (dilationPencil Xh Y z w).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_dilationPencil hXh hY hz hw)

/-- Ward identity for `R_t` (both orders): `R_tᴴ - R_t = 2iη R_tᴴ R_t = 2iη R_t R_tᴴ`. -/
theorem dilationResolvent_ward (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) (hz : 0 < z.im)
    (t : ℝ) :
    (dilationResolvent Xh Y z t)ᴴ - dilationResolvent Xh Y z t =
        ((2 * z.im : ℝ) * Complex.I) •
          ((dilationResolvent Xh Y z t)ᴴ * dilationResolvent Xh Y z t) ∧
      (dilationResolvent Xh Y z t)ᴴ - dilationResolvent Xh Y z t =
        ((2 * z.im : ℝ) * Complex.I) •
          (dilationResolvent Xh Y z t * (dilationResolvent Xh Y z t)ᴴ) := by
  have hdet := isUnit_det_dilationPencil hXh hY hz (w := -(t : ℂ)) (by simp)
  have hd := dilationPencil_sub_conjTranspose (z := z) hXh hY (-(t : ℂ))
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, mul_zero, Complex.ofReal_zero,
    zero_mul, zero_smul, add_zero] at hd
  rw [dilationResolvent_eq_pencil]
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_inv_sub_inv_eq_left _ hdet, hd, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  · rw [conjTranspose_inv_sub_inv_eq_right _ hdet, hd, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]

/-- Ward identity for `R` (both orders): `Rᴴ - R = 2i Rᴴ(η + Y)R = 2i R(η + Y)Rᴴ`. -/
theorem absorbedResolvent_ward (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) (hz : 0 < z.im) :
    (absorbedResolvent Xh Y z)ᴴ - absorbedResolvent Xh Y z =
        ((2 * z.im : ℝ) * Complex.I) •
            ((absorbedResolvent Xh Y z)ᴴ * absorbedResolvent Xh Y z) +
          (2 * Complex.I) •
            ((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z) ∧
      (absorbedResolvent Xh Y z)ᴴ - absorbedResolvent Xh Y z =
        ((2 * z.im : ℝ) * Complex.I) •
            (absorbedResolvent Xh Y z * (absorbedResolvent Xh Y z)ᴴ) +
          (2 * Complex.I) •
            (absorbedResolvent Xh Y z * Y * (absorbedResolvent Xh Y z)ᴴ) := by
  have hdet := isUnit_det_dilationPencil hXh hY hz (w := Complex.I) (by simp)
  have hd := dilationPencil_sub_conjTranspose (z := z) hXh hY Complex.I
  simp only [Complex.I_im, mul_one, Complex.ofReal_ofNat] at hd
  rw [absorbedResolvent_eq_pencil]
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_inv_sub_inv_eq_left _ hdet, hd, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [conjTranspose_inv_sub_inv_eq_right _ hdet, hd, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]

/-!
### Exact matrix variances
-/

/-- **Part (ii) of the dilation variance lemma, entrywise.**
Law:
`t ~ stdCauchy = ProbabilityTheory.cauchyMeasure 0 1` (density `1/(π(1+t²))`).
Domain: any finite `ι`, `Xh` Hermitian, `Y ⪰ 0` (possibly singular; it need not commute with `Xh`),
`z: ℂ` with `η = Im z > 0`;
`R = (z - Xh + iY)⁻¹`, `R_t = (z - Xh - tY)⁻¹`.
Conclusion: every entry of `(R_t - R)ᴴ (R_t - R)` is `stdCauchy`-integrable and
`E_t (R_t - R)ᴴ (R_t - R) = η⁻¹ Rᴴ Y R` entrywise.
No hypothesis beyond those displayed. The proof uses `isUnit_cauchyResolventPencil`,
`norm_cauchyResolventPencil_nonsing_inv_le` and, through `CauchyPoissonBounded`, the Cayley-map
lemmas.
-/
theorem isCauchyMatrixMean_variance_left (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) :
    IsCauchyMatrixMean
      (fun t => (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)ᴴ *
        (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z))
      ((z.im : ℂ)⁻¹ • ((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z)) := by
  set R := absorbedResolvent Xh Y z
  set c : ℂ := ((2 * z.im : ℝ) * Complex.I)⁻¹
  have hc0 : ((2 * z.im : ℝ) * Complex.I) ≠ 0 := by
    have : (2 * z.im : ℝ) ≠ 0 := by positivity
    exact mul_ne_zero (by exact_mod_cast this) Complex.I_ne_zero
  have hmean := isCauchyMatrixMean_dilationResolvent hXh hY hz
  have hstar := hmean.conjTranspose
  -- pointwise expansion via the Ward identity for `R_t`
  have hpt : ∀ t, c • ((dilationResolvent Xh Y z t)ᴴ - dilationResolvent Xh Y z t) -
      (dilationResolvent Xh Y z t)ᴴ * R - Rᴴ * dilationResolvent Xh Y z t + Rᴴ * R =
      (dilationResolvent Xh Y z t - R)ᴴ * (dilationResolvent Xh Y z t - R) := by
    intro t
    rw [(dilationResolvent_ward hXh hY hz t).1, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    abel
  have h := (((hmean.conjTranspose.sub hmean).smul c).sub
    (hstar.mul_const R)).sub (hmean.const_mul Rᴴ) |>.add (IsCauchyMatrixMean.const (Rᴴ * R))
  refine h.congr hpt ?_
  rw [(absorbedResolvent_ward hXh hY hz).1, smul_add, smul_smul, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]
  have : c * (2 * Complex.I) = (z.im : ℂ)⁻¹ := by
    simp only [c]
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    push_cast
    field_simp
  rw [this]
  abel

/-- **Part (iii) of the dilation variance lemma, entrywise.**
Law:
`t ~ stdCauchy = ProbabilityTheory.cauchyMeasure 0 1` (density `1/(π(1+t²))`).
Domain: any finite `ι`, `Xh` Hermitian, `Y ⪰ 0` (possibly singular; it need not commute with `Xh`),
`z: ℂ` with `η = Im z > 0`;
`R = (z - Xh + iY)⁻¹`, `R_t = (z - Xh - tY)⁻¹`.
Conclusion: every entry of `(R_t - R)(R_t - R)ᴴ` is `stdCauchy`-integrable and
`E_t (R_t - R)(R_t - R)ᴴ = η⁻¹ R Y Rᴴ` entrywise.
No hypothesis beyond those displayed. The proof uses `isUnit_cauchyResolventPencil`,
`norm_cauchyResolventPencil_nonsing_inv_le` and, through `CauchyPoissonBounded`, the Cayley-map
lemmas.
-/
theorem isCauchyMatrixMean_variance_right (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) :
    IsCauchyMatrixMean
      (fun t => (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z) *
        (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)ᴴ)
      ((z.im : ℂ)⁻¹ • (absorbedResolvent Xh Y z * Y * (absorbedResolvent Xh Y z)ᴴ)) := by
  set R := absorbedResolvent Xh Y z
  set c : ℂ := ((2 * z.im : ℝ) * Complex.I)⁻¹
  have hc0 : ((2 * z.im : ℝ) * Complex.I) ≠ 0 := by
    have : (2 * z.im : ℝ) ≠ 0 := by positivity
    exact mul_ne_zero (by exact_mod_cast this) Complex.I_ne_zero
  have hmean := isCauchyMatrixMean_dilationResolvent hXh hY hz
  have hstar := hmean.conjTranspose
  have hpt : ∀ t, c • ((dilationResolvent Xh Y z t)ᴴ - dilationResolvent Xh Y z t) -
      dilationResolvent Xh Y z t * Rᴴ - R * (dilationResolvent Xh Y z t)ᴴ + R * Rᴴ =
      (dilationResolvent Xh Y z t - R) * (dilationResolvent Xh Y z t - R)ᴴ := by
    intro t
    rw [(dilationResolvent_ward hXh hY hz t).2, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    abel
  have h := (((hmean.conjTranspose.sub hmean).smul c).sub
    (hmean.mul_const Rᴴ)).sub (hstar.const_mul R) |>.add (IsCauchyMatrixMean.const (R * Rᴴ))
  refine h.congr hpt ?_
  rw [(absorbedResolvent_ward hXh hY hz).2, smul_add, smul_smul, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]
  have : c * (2 * Complex.I) = (z.im : ℂ)⁻¹ := by
    simp only [c]
    have : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    push_cast
    field_simp
  rw [this]
  abel

end BlockBand.Critical.Collar
