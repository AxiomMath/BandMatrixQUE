module

public import BlockBand.Coarea.GUELaw
public import BlockBand.Wegner.ProjectedWegnerBasic

/-!
# Rank-one spectral averaging for `GUE_N(t)` at positive height

*Law.* `G ~ gueMeasure (Fin N) t` (diagonal variance `t`, `E|G_ab|² = t`), any `t > 0` (only
`lintegral_norm_sq_mulVec_gue` allows `t = 0`). *Domain.* every `N`, every deterministic
Hermitian `F` (no norm bound), every `z` with `Im z > 0`, every deterministic vector `y`.
Euclidean norms `∑ ‖y a‖²`. Exact finite-`N` statements; the constants depend on `t` only.

## Main results

* `lintegral_im_resolvent_gue_le`: `E Im⟨y, (F + G - z)⁻¹ y⟩ ≤ √(π/(2t)) ‖y‖²`
  (`= π · (2πt)^{-1/2} ‖y‖²`, the bounded density of the diagonal entry in the direction of `y`
  times the exact rank-one integral `∫ Im⟨v,(H + g vv* - z)⁻¹v⟩ dg = π`).
* `lintegral_norm_sq_mulVec_gue`: `E ‖G q‖² = N t ‖q‖²`.

## Proof

1. *Rotation* (`exists_unitary_mulVec_eq`, `gueMeasure_map_unitary_conj`): a unitary `W` with
   `W y = ‖y‖ e_k`; `GUE` is invariant under `G ↦ W G W*`, so `y` may be replaced by `‖y‖ e_k`
   and `F` by `W F W*`.
2. *Coordinates* (`gueMeasure_eq_map_hermitianMatrixOfCoordinates`): the diagonal coordinate
   `G_kk ~ N(0,t)` is independent of the others; it is integrated first (`lmarginal_insert'`),
   the other coordinates being fixed in a Hermitian `H`.
3. *One entry of a rank-one perturbation* (`inv_add_single_apply`): with `a = ((H - z)⁻¹)_kk`,
   `Im a > 0`, `((H + g E_kk - z)⁻¹)_kk = a/(1 + g a)`, whose imaginary part is
   `β/((1+gα)² + g²β²)`, `a = α + iβ`; its Lebesgue integral is exactly `π`
   (`integral_cauchy_profile`). The Gaussian density is at most `(2πt)^{-1/2}`.
4. *Second moment*: after the rotation `‖G q‖² = ‖q‖² Σ_a |G_ak|²`, and each coordinate has the
   stated variance (`t` on the diagonal, `t/2 + t/2` off the diagonal).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.WeightedDensity

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open CoareaNative.BlockBand (StrictUpperIndex HermitianCoordinate hermitianUpperEntry
  hermitianMatrixOfCoordinates)
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

/-!
## Deterministic resolvent facts
-/

/-- For Hermitian `H`, `z • 1 - H` has imaginary margin `Im z`. -/
theorem hasImMargin_smul_one_sub {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (z : ℂ) :
    BlockBand.Wegner.HasImMargin z.im (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H) := by
  intro v
  have h1 : (star v ⬝ᵥ v).im = 0 := by
    have := BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian
      (isHermitian_one (n := Fin N) (α := ℂ)) v
    rwa [one_mulVec] at this
  rw [sub_mulVec, dotProduct_sub, Complex.sub_im,
    BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian hH, sub_zero, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.mul_im, h1, mul_zero, zero_add]

/-- `H - z` is invertible for Hermitian `H` and `Im z > 0`. -/
theorem isUnit_det_sub_smul_one {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) : IsUnit (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
  have h := (hasImMargin_smul_one_sub hH z).isUnit_det hz
  have heq : H - z • (1 : Matrix (Fin N) (Fin N) ℂ) = -(z • 1 - H) := by abel
  rw [heq, det_neg]
  exact (isUnit_one.neg.pow _).mul h

/-- `Im ⟨y, (H - z)⁻¹ y⟩ = Im z ‖(H - z)⁻¹ y‖²` for Hermitian `H`, `Im z > 0`. -/
theorem im_dotProduct_inv_mulVec {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (y : Fin N → ℂ) :
    (star y ⬝ᵥ ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y)).im =
      z.im * (star ((H - z • 1)⁻¹ *ᵥ y) ⬝ᵥ ((H - z • 1)⁻¹ *ᵥ y)).re := by
  set A := H - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hAu : IsUnit A.det := isUnit_det_sub_smul_one hH hz
  set w := A⁻¹ *ᵥ y
  have hAw : A *ᵥ w = y := by
    show A *ᵥ (A⁻¹ *ᵥ y) = y
    rw [mulVec_mulVec, mul_nonsing_inv _ hAu, one_mulVec]
  have hAH : Aᴴ = H - (star z) • 1 := by
    simp only [A, conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
  have h1 : star y ⬝ᵥ w = star w ⬝ᵥ (Aᴴ *ᵥ w) := by
    rw [← hAw, star_mulVec, ← dotProduct_mulVec]
  have hr : (star w ⬝ᵥ (H *ᵥ w)).im = 0 :=
    BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian hH w
  have hr1 : (star w ⬝ᵥ w).im = 0 := by
    have := BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian
      (isHermitian_one (n := Fin N) (α := ℂ)) w
    rwa [one_mulVec] at this
  rw [h1, hAH, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.sub_im, hr, Complex.mul_im, hr1]
  simp

/-- `Im ⟨y, (H - z)⁻¹ y⟩ ≥ 0`. -/
theorem im_dotProduct_inv_mulVec_nonneg {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (y : Fin N → ℂ) :
    0 ≤ (star y ⬝ᵥ ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y)).im := by
  rw [im_dotProduct_inv_mulVec hH hz]
  refine mul_nonneg hz.le ?_
  rw [BlockBand.Wegner.re_star_dotProduct_self]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The diagonal resolvent entry has strictly positive imaginary part. -/
theorem im_inv_apply_self_pos {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (k : Fin N) :
    0 < ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ k k).im := by
  set A := H - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have he : star (Pi.single k (1 : ℂ)) ⬝ᵥ (A⁻¹ *ᵥ Pi.single k 1) = A⁻¹ k k := by
    simp [mulVec_single, dotProduct, Pi.single_apply]
  have h := im_dotProduct_inv_mulVec hH hz (Pi.single k (1 : ℂ))
  rw [he] at h
  rw [h]
  refine mul_pos hz ?_
  rw [BlockBand.Wegner.re_star_dotProduct_self]
  have hAu : IsUnit A.det := isUnit_det_sub_smul_one hH hz
  set w := A⁻¹ *ᵥ Pi.single k (1 : ℂ)
  have hAw : A *ᵥ w = Pi.single k 1 := by
    show A *ᵥ (A⁻¹ *ᵥ Pi.single k (1 : ℂ)) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hAu, one_mulVec]
  have hw : w ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero] at hAw
    have := congrFun hAw k
    simp at this
  obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := Function.ne_iff.1 hw
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < ‖w b‖ ^ 2)
    (Finset.single_le_sum (f := fun a => ‖w a‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b))

/-- **One entry of a rank-one perturbation** (Sherman–Morrison):
`((H + g E_kk - z)⁻¹)_kk = a/(1 + g a)` with `a = ((H - z)⁻¹)_kk`. -/
theorem inv_add_single_apply {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (k : Fin N) (g : ℝ) :
    (H + (g : ℂ) • single k k (1 : ℂ) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ k k =
      (H - z • 1)⁻¹ k k / (1 + g * (H - z • 1)⁻¹ k k) := by
  set A := H - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hE : (single k k (1 : ℂ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_single, star_one]
  have hH' : (H + (g : ℂ) • single k k (1 : ℂ)).IsHermitian :=
    hH.add (hE.smul (Complex.conj_ofReal g))
  set B := H + (g : ℂ) • single k k (1 : ℂ) - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hA := isUnit_det_sub_smul_one hH hz
  have hB := isUnit_det_sub_smul_one hH' hz
  have hBA : B = A + (g : ℂ) • single k k 1 := by simp only [A, B]; abel
  -- resolvent identity
  have hres : A⁻¹ - B⁻¹ = (g : ℂ) • (A⁻¹ * single k k 1 * B⁻¹) := by
    have : (g : ℂ) • (A⁻¹ * single k k 1 * B⁻¹) = A⁻¹ * (B - A) * B⁻¹ := by
      rw [hBA, add_sub_cancel_left, Matrix.mul_smul, Matrix.smul_mul]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, mul_nonsing_inv _ hB,
      Matrix.mul_one, nonsing_inv_mul _ hA, Matrix.one_mul]
  have hkk := congrFun (congrFun hres k) k
  have hprod : (A⁻¹ * single k k (1 : ℂ) * B⁻¹) k k = A⁻¹ k k * B⁻¹ k k := by
    simp [Matrix.mul_apply, single_apply, ite_and]
  rw [Matrix.sub_apply, Matrix.smul_apply, hprod, smul_eq_mul] at hkk
  have hne : 1 + (g : ℂ) * A⁻¹ k k ≠ 0 := by
    by_cases hg : g = 0
    · simp [hg]
    · intro h0
      have := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, zero_add, add_zero, Complex.zero_im] at this
      exact (mul_ne_zero hg (im_inv_apply_self_pos hH hz k).ne') this
  rw [eq_div_iff hne]
  linear_combination -hkk

/-- `Im (a/(1 + g a)) = Im a / ((1 + g Re a)² + (g Im a)²)`. -/
theorem im_div_one_add_mul (a : ℂ) (g : ℝ) :
    (a / (1 + (g : ℂ) * a)).im = a.im / ((1 + g * a.re) ^ 2 + (g * a.im) ^ 2) := by
  have hn : Complex.normSq (1 + (g : ℂ) * a) = (1 + g * a.re) ^ 2 + (g * a.im) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im,
      zero_add]
    ring
  rw [Complex.div_im, hn]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im,
    zero_add]
  rw [← sub_div]
  congr 1
  ring

/-!
## The exact rank-one integral
-/

/-- `∫ β/((1+gα)² + (gβ)²) dg = π` for `β > 0`. -/
theorem integral_cauchy_profile (α β : ℝ) (hβ : 0 < β) :
    ∫ g : ℝ, β / ((1 + g * α) ^ 2 + (g * β) ^ 2) = Real.pi := by
  set s := α ^ 2 + β ^ 2 with hs
  have hs0 : 0 < s := by positivity
  set c := s / β
  have hc : 0 < c := div_pos hs0 hβ
  set d := α / β
  have hfun : ∀ g : ℝ, β / ((1 + g * α) ^ 2 + (g * β) ^ 2) =
      c * (1 + (c * (g + d / c)) ^ 2)⁻¹ := by
    intro g
    have hD : 0 < (1 + g * α) ^ 2 + (g * β) ^ 2 := by
      rcases eq_or_ne g 0 with h | h
      · simp [h]
      · have : 0 < (g * β) ^ 2 := by positivity
        positivity
    have hcd : c * (g + d / c) = (s * g + α) / β := by
      simp only [c, d]; field_simp
    rw [hcd]
    have h2 : 1 + ((s * g + α) / β) ^ 2 = s * ((1 + g * α) ^ 2 + (g * β) ^ 2) / β ^ 2 := by
      field_simp
      simp only [hs]
      ring
    rw [h2]
    simp only [c]
    field_simp
  simp_rw [hfun]
  rw [integral_const_mul,
    integral_add_right_eq_self (fun x : ℝ => (1 + (c * x) ^ 2)⁻¹) (d / c),
    Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) c,
    integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.2 hc), smul_eq_mul]
  field_simp

/-- The rank-one profile is Lebesgue integrable. -/
theorem integrable_cauchy_profile (α β : ℝ) (hβ : 0 < β) :
    Integrable fun g : ℝ => β / ((1 + g * α) ^ 2 + (g * β) ^ 2) := by
  by_contra h
  have := integral_undef h
  rw [integral_cauchy_profile α β hβ] at this
  exact Real.pi_pos.ne' this

/-- Gaussian average of the rank-one profile: at most `√(π/(2t))`. -/
theorem lintegral_gaussian_im_le (a : ℂ) (ha : 0 < a.im) {t : ℝ≥0} (ht : t ≠ 0) :
    ∫⁻ g, ENNReal.ofReal ((a / (1 + (g : ℂ) * a)).im) ∂gaussianReal 0 t ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t))) := by
  have htpos : (0 : ℝ) < t := by positivity
  set h : ℝ → ℝ := fun g => a.im / ((1 + g * a.re) ^ 2 + (g * a.im) ^ 2)
  have hmeas : Measurable h := by
    simp only [h]; fun_prop
  simp_rw [im_div_one_add_mul]
  show ∫⁻ g, (fun g => ENNReal.ofReal (h g)) g ∂gaussianReal 0 t ≤ _
  rw [gaussianReal_of_var_ne_zero 0 ht,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 t)
      hmeas.ennreal_ofReal]
  set K : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹
  have hpdf : ∀ g, gaussianPDF 0 t g ≤ ENNReal.ofReal K := by
    intro g
    rw [gaussianPDF, gaussianPDFReal_def]
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-(g - 0) ^ 2 / (2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ (g - 0) ^ 2 / (2 * (t : ℝ)) := by positivity
      linarith [neg_div (2 * (t : ℝ)) ((g - 0) ^ 2)])
    exact (mul_le_mul_of_nonneg_left he (inv_nonneg.2 (Real.sqrt_nonneg _))).trans_eq (mul_one _)
  have hint : ∫⁻ g, ENNReal.ofReal (h g) = ENNReal.ofReal Real.pi := by
    rw [← integral_cauchy_profile a.re a.im ha,
      ofReal_integral_eq_lintegral_ofReal (integrable_cauchy_profile a.re a.im ha)
        (Filter.Eventually.of_forall fun g => by
          have : 0 < (1 + g * a.re) ^ 2 + (g * a.im) ^ 2 := by
            rcases eq_or_ne g 0 with hg | hg
            · simp [hg]
            · have : 0 < (g * a.im) ^ 2 := by positivity
              positivity
          exact div_nonneg ha.le this.le)]
  calc ∫⁻ g, (gaussianPDF 0 t * fun g => ENNReal.ofReal (h g)) g
      ≤ ∫⁻ g, ENNReal.ofReal K * ENNReal.ofReal (h g) :=
        lintegral_mono fun g => mul_le_mul_left (hpdf g) _
    _ = ENNReal.ofReal K * ENNReal.ofReal Real.pi := by
        rw [lintegral_const_mul _ hmeas.ennreal_ofReal, hint]
    _ = ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t))) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _))]
        congr 1
        have hsq : Real.pi / (2 * t) = (K * Real.pi) ^ 2 := by
          simp only [K]
          rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
          field_simp
        rw [hsq, Real.sqrt_sq (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
          Real.pi_pos.le)]

/-!
## Rotation of a vector to a coordinate axis
-/

/-- A unitary `W` with `W y = ‖y‖ e_k`. -/
theorem exists_unitary_mulVec_eq (y : Fin N → ℂ) (k : Fin N) :
    ∃ W ∈ unitaryGroup (Fin N) ℂ,
      W *ᵥ y = Pi.single k ((Real.sqrt (∑ a, ‖y a‖ ^ 2) : ℝ) : ℂ) := by
  by_cases hy : y = 0
  · refine ⟨1, one_mem _, ?_⟩
    subst hy
    simp
  set r := Real.sqrt (∑ a, ‖y a‖ ^ 2)
  have hr : 0 < r := by
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hy
    apply Real.sqrt_pos.2
    exact lt_of_lt_of_le (by have := norm_pos_iff.2 hb; positivity : (0 : ℝ) < ‖y b‖ ^ 2)
      (Finset.single_le_sum (f := fun a => ‖y a‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ b))
  set v : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (((r⁻¹ : ℝ) : ℂ) • y)
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [v, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos hr, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (inv_nonneg.2 hr.le)]
    exact inv_mul_cancel₀ hr.ne'
  have hon : Orthonormal ℂ (({k} : Set (Fin N)).domRestrict fun _ : Fin N => v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subsingleton.elim i j
    subst this
    simp only [Set.domRestrict_apply, ite_true]
    rw [inner_self_eq_norm_sq_to_K, hv]
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace])
  set U := (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.toMatrix b
  have hU : U ∈ unitaryGroup (Fin N) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
  have hUk : U *ᵥ Pi.single k 1 = ((r⁻¹ : ℝ) : ℂ) • y := by
    rw [mulVec_single_one]
    funext i
    simp only [U, col_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, hb k (Set.mem_singleton k), v]
  refine ⟨star U, Unitary.star_mem hU, ?_⟩
  have hy' : y = (r : ℂ) • (U *ᵥ Pi.single k 1) := by
    rw [hUk, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one,
      one_smul]
  rw [hy', mulVec_smul, mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.1 hU, one_mulVec]
  funext i
  simp [Pi.single_apply]

/-!
## The coordinate of one diagonal entry
-/

/-- Changing the diagonal coordinate `k` of a Hermitian reconstruction is a rank-one update. -/
theorem hermitianMatrixOfCoordinates_update_inl (x : HermitianCoordinate N → ℝ) (k : Fin N)
    (g : ℝ) :
    hermitianMatrixOfCoordinates (Function.update x (.inl k) g) =
      hermitianMatrixOfCoordinates (Function.update x (.inl k) 0) + (g : ℂ) • single k k 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hik : i = k
    · subst hik; simp [hermitianMatrixOfCoordinates]
    · simp [hermitianMatrixOfCoordinates, hik, Ne.symm hik, Function.update_of_ne]
  · simp [hermitianMatrixOfCoordinates, hermitianUpperEntry, single_apply, hij]
    intro h1 h2
    exact absurd (h1.symm.trans h2) hij

/-!
## Rank-one spectral averaging
-/

/-- Resolvent entries `G ↦ ((F + G - z)⁻¹)_ab` are Borel measurable. -/
theorem measurable_resolvent_entry (F : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (a b : Fin N) :
    Measurable fun G : Matrix (Fin N) (Fin N) ℂ => (F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ a b := by
  have h1 : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ) :=
    ((continuous_const.add continuous_id).sub continuous_const).measurable
  have h2 := (BlockBand.Wegner.measurable_matrix_inv (n := Fin N)).comp h1
  exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp h2)

/-- Diagonal resolvent entry: `E Im((F + G - z)⁻¹)_kk ≤ √(π/(2t))`. -/
theorem lintegral_im_resolvent_apply_self_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) (k : Fin N) :
    ∫⁻ G, ENNReal.ofReal (((F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ k k).im)
        ∂gueMeasure (Fin N) t ≤ ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t))) := by
  set C := ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t)))
  set f : (HermitianCoordinate N → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((F + hermitianMatrixOfCoordinates q - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹
      k k).im)
  have hf : Measurable f :=
    (Complex.measurable_im.comp ((measurable_resolvent_entry F z k k).comp
      (measurable_hermitianMatrixOfCoordinates N))).ennreal_ofReal
  have hg : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (((F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ k k).im) :=
    (Complex.measurable_im.comp (measurable_resolvent_entry F z k k)).ennreal_ofReal
  rw [gueMeasure_eq_map_hermitianMatrixOfCoordinates,
    lintegral_map hg (measurable_hermitianMatrixOfCoordinates N)]
  change ∫⁻ q, f q ∂hermCoordGaussian N t ≤ C
  unfold hermCoordGaussian
  classical
  rw [lintegral_eq_lmarginal_univ (0 : HermitianCoordinate N → ℝ),
    ← Finset.insert_erase (Finset.mem_univ (Sum.inl k : HermitianCoordinate N)),
    lmarginal_insert' f hf (Finset.notMem_erase _ _)]
  have hin : ∀ x : HermitianCoordinate N → ℝ,
      ∫⁻ g, f (Function.update x (.inl k) g) ∂gaussianReal 0 (hermCoordVariance t (.inl k)) ≤ C := by
    intro x
    set H := F + hermitianMatrixOfCoordinates (Function.update x (.inl k) 0)
    have hH : H.IsHermitian :=
      hF.add (CoareaNative.BlockBand.hermitianMatrixOfCoordinates_isHermitian _)
    have hpt : ∀ g : ℝ, f (Function.update x (.inl k) g) =
        ENNReal.ofReal (((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ k k /
          (1 + (g : ℂ) * (H - z • 1)⁻¹ k k)).im) := by
      intro g
      simp only [f]
      rw [hermitianMatrixOfCoordinates_update_inl, ← add_assoc,
        inv_add_single_apply hH hz k g]
    simp_rw [hpt]
    exact lintegral_gaussian_im_le _ (im_inv_apply_self_pos hH hz k) ht.ne'
  calc (∫⋯∫⁻_(Finset.univ.erase (Sum.inl k)), (fun x =>
          ∫⁻ g, f (Function.update x (.inl k) g) ∂gaussianReal 0 (hermCoordVariance t (.inl k)))
          ∂fun k => gaussianReal 0 (hermCoordVariance t k)) 0
      ≤ (∫⋯∫⁻_(Finset.univ.erase (Sum.inl k)), (fun _ => C)
          ∂fun k => gaussianReal 0 (hermCoordVariance t k)) 0 := lmarginal_mono hin 0
    _ = C := by
        simp [lmarginal, lintegral_const]

/-- Conjugating a resolvent quadratic form by a unitary. -/
theorem dotProduct_inv_unitary_conj {W : Matrix (Fin N) (Fin N) ℂ}
    (hW : W ∈ unitaryGroup (Fin N) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) :
    star y ⬝ᵥ (A⁻¹ *ᵥ y) = star (W *ᵥ y) ⬝ᵥ ((W * A * star W)⁻¹ *ᵥ (W *ᵥ y)) := by
  have h1 : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hW
  have h2 : W * star W = 1 := Matrix.mem_unitaryGroup_iff.1 hW
  have hinv : (W * A * star W)⁻¹ = W * A⁻¹ * star W := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv h2,
      Matrix.inv_eq_left_inv h1, Matrix.mul_assoc]
  rw [hinv, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    ← star_eq_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one,
    ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **Rank-one spectral averaging at positive height.** Law `G ~ gueMeasure (Fin N) t`, `t > 0`;
every `N`, every deterministic Hermitian `F` (no norm bound), every `z` with `Im z > 0`, every
deterministic `y`: `E Im⟨y, (F + G - z)⁻¹ y⟩ ≤ √(π/(2t)) ‖y‖²` (`= π (2πt)^{-1/2} ‖y‖²`).
Uniform in `F`, `z`, `N`. -/
theorem lintegral_im_resolvent_gue_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) (y : Fin N → ℂ) :
    ∫⁻ G, ENNReal.ofReal ((star y ⬝ᵥ ((F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y)).im)
        ∂gueMeasure (Fin N) t ≤
      ENNReal.ofReal (Real.sqrt (Real.pi / (2 * t)) * ∑ a, ‖y a‖ ^ 2) := by
  by_cases hy : y = 0
  · subst hy; simp
  obtain ⟨b, -⟩ := Function.ne_iff.1 hy
  obtain ⟨W, hW, hWy⟩ := exists_unitary_mulVec_eq y b
  set r := Real.sqrt (∑ a, ‖y a‖ ^ 2)
  set F' := W * F * star W
  have hF' : F'.IsHermitian := by
    simp only [F', star_eq_conjTranspose]
    exact isHermitian_mul_mul_conjTranspose W hF
  have h2 : W * star W = 1 := Matrix.mem_unitaryGroup_iff.1 hW
  have hconj : ∀ G : Matrix (Fin N) (Fin N) ℂ,
      W * (F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ)) * star W = F' + W * G * star W - z • 1 := by
    intro G
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, h2]
  have hpt : ∀ G : Matrix (Fin N) (Fin N) ℂ,
      (star y ⬝ᵥ ((F + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y)).im =
        r ^ 2 * ((F' + W * G * star W - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ b b).im := by
    intro G
    rw [dotProduct_inv_unitary_conj hW, hconj, hWy]
    have : ∀ M : Matrix (Fin N) (Fin N) ℂ,
        star (Pi.single b (r : ℂ)) ⬝ᵥ (M *ᵥ Pi.single b (r : ℂ)) = ((r ^ 2 : ℝ) : ℂ) * M b b := by
      intro M
      simp [mulVec_single, dotProduct, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul,
        Finset.sum_ite_eq']
      ring
    rw [this, Complex.im_ofReal_mul]
  simp_rw [hpt]
  have hψ : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (r ^ 2 * ((F' + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ b b).im) :=
    (measurable_const.mul (Complex.measurable_im.comp
      (measurable_resolvent_entry F' z b b))).ennreal_ofReal
  have hc : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => W * G * star W :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  rw [← lintegral_map hψ hc, gueMeasure_map_unitary_conj t hW]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg r)]
  have hm : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal ((F' + G - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ b b).im :=
    (Complex.measurable_im.comp (measurable_resolvent_entry F' z b b)).ennreal_ofReal
  rw [lintegral_const_mul _ hm, mul_comm (Real.sqrt _),
    ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hr2 : r ^ 2 = ∑ a, ‖y a‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hr2]
  exact mul_le_mul_right (lintegral_im_resolvent_apply_self_le hF' ht hz b) _

/-!
## Second moment of `G q`
-/

/-- `E u² = v` for `u ~ N(0, v)`. -/
theorem lintegral_sq_gaussianReal (v : ℝ≥0) :
    ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂gaussianReal 0 v = ENNReal.ofReal v := by
  have hint : Integrable (fun u : ℝ => u ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun u => sq_nonneg u)]
  congr 1
  have h := variance_eq_integral (X := id) (μ := gaussianReal 0 v) measurable_id.aemeasurable
  rw [variance_id_gaussianReal] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  exact h.symm

/-- Each GUE coordinate has its stated variance. -/
theorem lintegral_coord_sq_hermCoordGaussian (t : ℝ≥0) (i : HermitianCoordinate N) :
    ∫⁻ q, ENNReal.ofReal (q i ^ 2) ∂hermCoordGaussian N t =
      ENNReal.ofReal (hermCoordVariance t i) := by
  unfold hermCoordGaussian
  rw [(measurePreserving_eval (fun k => gaussianReal 0 (hermCoordVariance t k)) i).lintegral_comp
    (f := fun u => ENNReal.ofReal (u ^ 2)) (by fun_prop)]
  exact lintegral_sq_gaussianReal _

/-- `E|G_ab|² = t` for every entry of `G ~ GUE_N(t)`. -/
theorem lintegral_norm_sq_apply_gue (t : ℝ≥0) (a b : Fin N) :
    ∫⁻ G, ENNReal.ofReal (‖G a b‖ ^ 2) ∂gueMeasure (Fin N) t = ENNReal.ofReal t := by
  have hm : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => ENNReal.ofReal (‖G a b‖ ^ 2) := by
    have : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => G a b :=
      (measurable_pi_apply b).comp (measurable_pi_apply a)
    exact (this.norm.pow_const 2).ennreal_ofReal
  rw [gueMeasure_eq_map_hermitianMatrixOfCoordinates,
    lintegral_map hm (measurable_hermitianMatrixOfCoordinates N)]
  by_cases hab : a = b
  · subst hab
    have : ∀ q : HermitianCoordinate N → ℝ,
        ‖hermitianMatrixOfCoordinates q a a‖ ^ 2 = q (.inl a) ^ 2 := by
      intro q; simp [hermitianMatrixOfCoordinates]
    simp_rw [this]
    exact lintegral_coord_sq_hermCoordGaussian t _
  · have key : ∀ (ij : StrictUpperIndex N) (q : HermitianCoordinate N → ℝ),
        ENNReal.ofReal (‖hermitianUpperEntry q ij‖ ^ 2) =
          ENNReal.ofReal (q (.inr (.inl ij)) ^ 2) + ENNReal.ofReal (q (.inr (.inr ij)) ^ 2) := by
      intro ij q
      rw [hermitianUpperEntry, Complex.sq_norm, Complex.normSq_add_mul_I,
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    have hsum : ∀ ij : StrictUpperIndex N,
        ∫⁻ q, ENNReal.ofReal (‖hermitianUpperEntry q ij‖ ^ 2) ∂hermCoordGaussian N t =
          ENNReal.ofReal t := by
      intro ij
      simp_rw [key]
      rw [lintegral_add_left ((measurable_pi_apply _).pow_const 2).ennreal_ofReal,
        lintegral_coord_sq_hermCoordGaussian, lintegral_coord_sq_hermCoordGaussian,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      simp [hermCoordVariance]
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have : ∀ q : HermitianCoordinate N → ℝ, hermitianMatrixOfCoordinates q a b =
          hermitianUpperEntry q ⟨(a, b), hlt⟩ := by
        intro q; simp [hermitianMatrixOfCoordinates, hab, hlt]
      simp_rw [this]
      exact hsum _
    · have : ∀ q : HermitianCoordinate N → ℝ, ‖hermitianMatrixOfCoordinates q a b‖ =
          ‖hermitianUpperEntry q ⟨(b, a), hgt⟩‖ := by
        intro q
        simp [hermitianMatrixOfCoordinates, hab, not_lt.2 hgt.le]
      simp_rw [this]
      exact hsum _

/-- Unitaries preserve the Euclidean norm. -/
theorem sum_norm_sq_unitary_mulVec {W : Matrix (Fin N) (Fin N) ℂ}
    (hW : W ∈ unitaryGroup (Fin N) ℂ) (v : Fin N → ℂ) :
    ∑ a, ‖(W *ᵥ v) a‖ ^ 2 = ∑ a, ‖v a‖ ^ 2 := by
  rw [← BlockBand.Wegner.re_star_dotProduct_self, ← BlockBand.Wegner.re_star_dotProduct_self,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.1 hW, one_mulVec]

/-- **Second moment** (in the application, `E G₁² = (c/2) I`): for `G ~ gueMeasure (Fin N) t`, any
`t ≥ 0`, every `N` and deterministic `q`, `E ‖G q‖² = N t ‖q‖²`. -/
theorem lintegral_norm_sq_mulVec_gue (t : ℝ≥0) (q : Fin N → ℂ) :
    ∫⁻ G, ENNReal.ofReal (∑ a, ‖(G *ᵥ q) a‖ ^ 2) ∂gueMeasure (Fin N) t =
      ENNReal.ofReal (N * t * ∑ a, ‖q a‖ ^ 2) := by
  by_cases hq : q = 0
  · subst hq; simp
  obtain ⟨b, -⟩ := Function.ne_iff.1 hq
  obtain ⟨W, hW, hWq⟩ := exists_unitary_mulVec_eq q b
  set r := Real.sqrt (∑ a, ‖q a‖ ^ 2)
  have h1 : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hW
  have hpt : ∀ G : Matrix (Fin N) (Fin N) ℂ,
      ∑ a, ‖(G *ᵥ q) a‖ ^ 2 = r ^ 2 * ∑ a, ‖(W * G * star W) a b‖ ^ 2 := by
    intro G
    rw [← sum_norm_sq_unitary_mulVec hW, mulVec_mulVec]
    have : (W * G) *ᵥ q = (W * G * star W) *ᵥ (W *ᵥ q) := by
      rw [mulVec_mulVec, Matrix.mul_assoc (W * G), h1, Matrix.mul_one]
    rw [this, hWq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mulVec_single]
    simp [mul_pow, mul_comm]
  simp_rw [hpt]
  have hψ : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (r ^ 2 * ∑ a, ‖G a b‖ ^ 2) := by
    refine (measurable_const.mul (Finset.measurable_sum _ fun a _ => ?_)).ennreal_ofReal
    exact (((measurable_pi_apply b).comp (measurable_pi_apply a)).norm.pow_const 2)
  have hc : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => W * G * star W :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  rw [← lintegral_map hψ hc, gueMeasure_map_unitary_conj t hW]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg r),
    ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg ‖_‖)]
  have hmi : ∀ a : Fin N, Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (‖G a b‖ ^ 2) := fun a =>
    (((measurable_pi_apply b).comp (measurable_pi_apply a)).norm.pow_const 2).ennreal_ofReal
  have hms : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ∑ a, ENNReal.ofReal (‖G a b‖ ^ 2) := Finset.measurable_sum _ fun a _ => hmi a
  rw [lintegral_const_mul _ hms, lintegral_finsetSum _ fun a _ => hmi a]
  simp_rw [lintegral_norm_sq_apply_gue]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg r),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  ring

end BlockBand.Critical.WeightedDensity
