module

public import BlockBand.Palm.CoarseRelativeGaussMoment

/-!
# Coarse relative local law: directional resolvent bounds

* `resolvent_conj_nsq`: normality `‖M* q‖ = ‖M q‖` for `M = (F - w)⁻¹`.
* `resolvent_vec_bound`: from `A - B = -A (cG + (b - a)) B` (that is,
  `G_s M_s⁻¹ = I - G_s(√s G + s m_s)`), `‖A q‖ ≤ ‖B q‖ + |Im a|⁻¹ (|c| ‖G B q‖ + |b - a| ‖B q‖)`.
* `coordRes_vec_nsq_le`, `coordRes_conj_vec_nsq_le`: `‖G_s q‖², ‖G_s* q‖² ≤ 8 η⁻² (‖v‖² + ‖G v‖²)`
  with `v = M_s q`, resp. `v = M_s* q` (`‖v‖ = ‖M_s q‖`).
* `quadFn_fderiv`, `quadFn_grad_le`: `q* G_s q` is `C¹` in the Gaussian coordinates and its
  weighted gradient is `√(st) ‖G_s* q‖ ‖G_s q‖ ≤ √(st)(‖G_s* q‖² + ‖G_s q‖²)/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexConjugate NNReal ENNReal

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem nsq_eq_quad (A : Matrix ι ι ℂ) (q : ι → ℂ) :
    nsq (A *ᵥ q) = (star q ⬝ᵥ ((Aᴴ * A) *ᵥ q)).re := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dotProduct_self_eq,
    Complex.ofReal_re]

omit [DecidableEq ι] in
theorem nsq_neg (x : ι → ℂ) : nsq (-x) = nsq x := by
  unfold nsq; simp

omit [DecidableEq ι] in
theorem sqrt_nsq_sub_le (x y : ι → ℂ) :
    Real.sqrt (nsq (x - y)) ≤ Real.sqrt (nsq x) + Real.sqrt (nsq y) := by
  have h := sqrt_nsq_add_le x (-y)
  rwa [nsq_neg, ← sub_eq_add_neg] at h

omit [DecidableEq ι] in
theorem sqrt_nsq_smul (c : ℂ) (x : ι → ℂ) :
    Real.sqrt (nsq (c • x)) = ‖c‖ * Real.sqrt (nsq x) := by
  rw [nsq_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem hermitian_resolvent_sqrt_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) (y : ι → ℂ) :
    Real.sqrt (nsq ((H - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ y)) ≤ |w.im|⁻¹ * Real.sqrt (nsq y) := by
  have h := hermitian_resolvent_nsq_le hH hw y
  have h2 : (w.im ^ 2)⁻¹ = (|w.im|⁻¹) ^ 2 := by rw [inv_pow, sq_abs]
  rw [h2] at h
  calc Real.sqrt (nsq ((H - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ y))
      ≤ Real.sqrt ((|w.im|⁻¹) ^ 2 * nsq y) := Real.sqrt_le_sqrt h
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- Normality of a Hermitian resolvent: `‖M* q‖ = ‖M q‖`. -/
theorem resolvent_conj_nsq {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {w : ℂ} (hw : w.im ≠ 0)
    (q : ι → ℂ) :
    nsq (((F - w • (1 : Matrix ι ι ℂ))⁻¹)ᴴ *ᵥ q) = nsq ((F - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ q) := by
  set M := (F - w • (1 : Matrix ι ι ℂ))⁻¹ with hM
  have hwc : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
  have h1 := hermitian_resolvent_sub hF hw hwc
  have h2 := hermitian_resolvent_sub hF hwc hw
  rw [← hermitian_resolvent_conjTranspose hF w] at h1 h2
  have hne : w - conj w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    exact hw (by linarith)
  have hcomm : M * Mᴴ = Mᴴ * M := by
    have h3 : (w - conj w) • (M * Mᴴ) = (w - conj w) • (Mᴴ * M) := by
      rw [← h1]
      have h3 := congrArg Neg.neg h2
      rw [neg_sub, ← neg_smul, neg_sub] at h3
      exact h3
    exact smul_right_injective _ hne h3
  rw [nsq_eq_quad, nsq_eq_quad, conjTranspose_conjTranspose, hcomm]

/-- **Resolvent comparison.** `A = (F + cG - a)⁻¹`, `B = (F - b)⁻¹`. -/
theorem resolvent_vec_bound {F G : Matrix ι ι ℂ} (hF : F.IsHermitian) (hG : G.IsHermitian)
    (c : ℝ) {a b : ℂ} (ha : a.im ≠ 0) (hb : b.im ≠ 0) (q : ι → ℂ) :
    Real.sqrt (nsq ((F + (c : ℂ) • G - a • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ q)) ≤
      Real.sqrt (nsq ((F - b • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ q)) + |a.im|⁻¹ *
        (|c| * Real.sqrt (nsq (G *ᵥ ((F - b • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ q))) +
          ‖b - a‖ * Real.sqrt (nsq ((F - b • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ q))) := by
  have hH : (F + (c : ℂ) • G).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, hF.eq, hG.eq, Complex.star_def, Complex.conj_ofReal]
  set A := (F + (c : ℂ) • G - a • (1 : Matrix ι ι ℂ))⁻¹
  set B := (F - b • (1 : Matrix ι ι ℂ))⁻¹
  have hu : IsUnit (F + (c : ℂ) • G - a • (1 : Matrix ι ι ℂ)) ↔
      IsUnit (F - b • (1 : Matrix ι ι ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det]
    exact ⟨fun _ => hermitian_shift_det_isUnit hF hb, fun _ => hermitian_shift_det_isUnit hH ha⟩
  have hdiff : A - B = A * ((F - b • (1 : Matrix ι ι ℂ)) - (F + (c : ℂ) • G - a • 1)) * B :=
    Matrix.inv_sub_inv hu
  have hmid : (F - b • (1 : Matrix ι ι ℂ)) - (F + (c : ℂ) • G - a • 1) =
      -((c : ℂ) • G + (b - a) • (1 : Matrix ι ι ℂ)) := by
    rw [sub_smul]; abel
  rw [hmid] at hdiff
  have hAq : A *ᵥ q = B *ᵥ q - A *ᵥ ((c : ℂ) • (G *ᵥ (B *ᵥ q)) + (b - a) • (B *ᵥ q)) := by
    have : A = B + A * -((c : ℂ) • G + (b - a) • (1 : Matrix ι ι ℂ)) * B := by
      rw [← hdiff]; abel
    conv_lhs => rw [this]
    rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, neg_mulVec, mulVec_neg, add_mulVec,
      smul_mulVec, smul_mulVec, one_mulVec]
    exact (sub_eq_add_neg _ _).symm
  rw [hAq]
  refine (sqrt_nsq_sub_le _ _).trans ?_
  refine add_le_add le_rfl ?_
  refine (hermitian_resolvent_sqrt_le hH ha _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (sqrt_nsq_add_le _ _).trans ?_
  rw [sqrt_nsq_smul, sqrt_nsq_smul, Complex.norm_real, Real.norm_eq_abs]

end General

variable {N : ℕ}

/-- `|s m_s| ≤ 1` (from `|m|² ≤ 1/s`, `s ≤ 1`). -/
theorem fresh_s_mul_norm_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : ℂ} (hz : 0 ≤ z.im) (hm : 0 < (freshDyson F s z).im) :
    s * ‖freshDyson F s z‖ ≤ 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact certificate_dyson_s_mul_norm_le_one hF.eigenvalues hs hs1 hz hm
    (freshDyson_residual_eq_zero hF hs hz hm)

/-- Common form of the two vector bounds. -/
theorem vec_bound_square {x g r η : ℝ} (hx : 0 ≤ x) (hg : 0 ≤ g) (hη : 0 < η) (hη1 : η ≤ 1)
    {c d : ℝ} (hc1 : c ≤ 1) (hd1 : d ≤ 1)
    (h : r ≤ x + η⁻¹ * (c * g + d * x)) (hr : 0 ≤ r) :
    r ^ 2 ≤ 8 * (η⁻¹) ^ 2 * (x ^ 2 + g ^ 2) := by
  have hi : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.mpr hη1
  have h1 : r ≤ 2 * η⁻¹ * (x + g) := by
    have : η⁻¹ * (c * g + d * x) ≤ η⁻¹ * (g + x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith
  have h2 : r ^ 2 ≤ (2 * η⁻¹ * (x + g)) ^ 2 := pow_le_pow_left₀ hr h1 2
  nlinarith [sq_nonneg (x - g)]

/-- **Resolvent vector bound.** `‖G_s q‖² ≤ 8η⁻²(‖M_s q‖² + ‖G M_s q‖²)` on `0 < η ≤ 1`. -/
theorem coordRes_vec_nsq_le {F G : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hG : G.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : ℂ}
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hm : 0 < (freshDyson F s z).im) (q : Fin N → ℂ) :
    nsq (coarseResolvent F G s z *ᵥ q) ≤
      8 * (z.im⁻¹) ^ 2 * (nsq (freshM F s z *ᵥ q) + nsq (G *ᵥ (freshM F s z *ᵥ q))) := by
  have hw : (freshW F s z).im ≠ 0 := (add_ofReal_mul_im_pos hs hz.le hm).ne'
  have h := resolvent_vec_bound hF hG (Real.sqrt s) hz.ne' hw q
  rw [← freshM_eq] at h
  have hba : ‖freshW F s z - z‖ = s * ‖freshDyson F s z‖ := by
    unfold freshW
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [hba, abs_of_pos hz, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hsq := vec_bound_square (Real.sqrt_nonneg (nsq (freshM F s z *ᵥ q)))
    (Real.sqrt_nonneg (nsq (G *ᵥ (freshM F s z *ᵥ q)))) hz hz1
    (by rw [Real.sqrt_le_one]; exact hs1) (fresh_s_mul_norm_le hF hN hs hs1 hz.le hm)
    h (Real.sqrt_nonneg _)
  rwa [Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at hsq

/-- **Adjoint resolvent vector bound.** `‖G_s* q‖² ≤ 8η⁻²(‖M_s* q‖² + ‖G M_s* q‖²)`. -/
theorem coordRes_conj_vec_nsq_le {F G : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hG : G.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : ℂ}
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) (hm : 0 < (freshDyson F s z).im) (q : Fin N → ℂ) :
    nsq ((coarseResolvent F G s z)ᴴ *ᵥ q) ≤
      8 * (z.im⁻¹) ^ 2 * (nsq ((freshM F s z)ᴴ *ᵥ q) + nsq (G *ᵥ ((freshM F s z)ᴴ *ᵥ q))) := by
  have hH := coarse_hermitian hF hG s
  have hw : (freshW F s z).im ≠ 0 := (add_ofReal_mul_im_pos hs hz.le hm).ne'
  have hzc : (conj z).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hz.ne'
  have hwc : (conj (freshW F s z)).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
  have hR : (coarseResolvent F G s z)ᴴ =
      (F + (Real.sqrt s : ℂ) • G - conj z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ :=
    hermitian_resolvent_conjTranspose hH z
  have hM : (freshM F s z)ᴴ = (F - conj (freshW F s z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
    rw [freshM_eq]; exact hermitian_resolvent_conjTranspose hF _
  have h := resolvent_vec_bound hF hG (Real.sqrt s) hzc hwc q
  rw [← hR, ← hM] at h
  have hba : ‖conj (freshW F s z) - conj z‖ = s * ‖freshDyson F s z‖ := by
    rw [← map_sub, Complex.norm_conj]
    unfold freshW
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [hba, Complex.conj_im, abs_neg, abs_of_pos hz, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hsq := vec_bound_square (Real.sqrt_nonneg (nsq ((freshM F s z)ᴴ *ᵥ q)))
    (Real.sqrt_nonneg (nsq (G *ᵥ ((freshM F s z)ᴴ *ᵥ q)))) hz hz1
    (by rw [Real.sqrt_le_one]; exact hs1) (fresh_s_mul_norm_le hF hN hs hs1 hz.le hm)
    h (Real.sqrt_nonneg _)
  rwa [Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at hsq

/-!
## The quadratic form `Q(y) = q* G_s q` in Gaussian coordinates
-/

/-- The real-linear functional `A ↦ q* A q`. -/
def quadLin (q : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℂ where
  toFun A := star q ⬝ᵥ (A *ᵥ q)
  map_add' A B := by simp [add_mulVec, dotProduct_add]
  map_smul' r A := by simp [smul_mulVec, dotProduct_smul]

/-- `Q(y) = q* R(y) q`. -/
def quadFn (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (t : ℝ≥0) (q : Fin N → ℂ)
    (y : ((Fin N × Fin N) × Fin 2) → ℝ) : ℂ :=
  star q ⬝ᵥ (coordRes F s z t y *ᵥ q)

theorem quadFn_eq (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (t : ℝ≥0) (q : Fin N → ℂ) :
    quadFn F s z t q = fun y => quadLin q
      (((F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) + (Real.sqrt s • gueCoordLin t) y)⁻¹) := by
  funext y
  unfold quadFn
  rw [coordRes_eq]
  rfl

theorem quadFn_contDiff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (t : ℝ≥0) (q : Fin N → ℂ) : ContDiff ℝ 1 (quadFn F s z t q) := by
  rw [quadFn_eq]
  exact linInv_contDiff _ _ _ (coarse_shift_det_isUnit hF s hz t)

theorem quadFn_fderiv {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (t : ℝ≥0) (q : Fin N → ℂ) (y v : ((Fin N × Fin N) × Fin 2) → ℝ) :
    fderiv ℝ (quadFn F s z t q) y v =
      -((Real.sqrt s : ℂ) * (star ((coordRes F s z t y)ᴴ *ᵥ q) ⬝ᵥ
        (gueCoord t v *ᵥ (coordRes F s z t y *ᵥ q)))) := by
  obtain ⟨D, hD, hDv⟩ := linInv_hasFDerivAt (F - z • (1 : Matrix (Fin N) (Fin N) ℂ))
    (Real.sqrt s • gueCoordLin t) (quadLin q) (coarse_shift_det_isUnit hF s hz t) y
  rw [quadFn_eq, hD.fderiv, hDv, ← coordRes_eq, LinearMap.smul_apply]
  change -(star q ⬝ᵥ ((coordRes F s z t y * (Real.sqrt s • gueCoord t v) * coordRes F s z t y) *ᵥ q))
    = _
  rw [← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul, smul_mulVec, dotProduct_smul,
    smul_eq_mul, star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec]

theorem sqrt_mul_le_half_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (a - b)]

/-- **Gradient bound.** `|∇Q| ≤ √(st) (‖R* q‖² + ‖R q‖²)/2`. -/
theorem quadFn_grad_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ≥0) (q : Fin N → ℂ) (y : ((Fin N × Fin N) × Fin 2) → ℝ) :
    weightedGradientNorm (fun _ => (1 : ℝ≥0)) (quadFn F s z t q) y ≤
      Real.sqrt (s * t) * ((nsq ((coordRes F s z t y)ᴴ *ᵥ q) + nsq (coordRes F s z t y *ᵥ q)) / 2) := by
  unfold weightedGradientNorm
  have hsum : ∑ j, (((fun _ => (1 : ℝ≥0)) j : ℝ≥0) : ℝ) *
      ‖fderiv ℝ (quadFn F s z t q) y (Pi.single j 1)‖ ^ 2 =
      s * ((t : ℝ) * (nsq ((coordRes F s z t y)ᴴ *ᵥ q) * nsq (coordRes F s z t y *ᵥ q))) := by
    simp only [NNReal.coe_one, one_mul, quadFn_fderiv hF s hz t q y, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hs]
    rw [← Finset.mul_sum, sum_dot_gueCoord_sq]
  rw [hsum, ← mul_assoc, Real.sqrt_mul (mul_nonneg hs (NNReal.coe_nonneg _))]
  exact mul_le_mul_of_nonneg_left (sqrt_mul_le_half_add (nsq_nonneg _) (nsq_nonneg _))
    (Real.sqrt_nonneg _)

theorem quadFn_bound {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ) {z : ℂ}
    (hz : 0 < z.im) (t : ℝ≥0) (q : Fin N → ℂ) (y : ((Fin N × Fin N) × Fin 2) → ℝ) :
    ‖quadFn F s z t q y‖ ≤ z.im⁻¹ * nsq q := by
  have hH := coarse_hermitian hF (gueCoord_isHermitian t y) s
  apply norm_quad_le_of_nsq_le _ (by positivity)
  intro v
  have := hermitian_resolvent_nsq_le hH hz.ne' v
  rwa [inv_pow]

end BlockBand.Palm.CoarseRelative
