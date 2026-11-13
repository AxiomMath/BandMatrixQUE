module

public import BlockBand.Palm.CoarseRelativeAlgebra

/-!
# Coarse relative local law: the deterministic fresh Dyson root

Deterministic properties of the root `m_s(z)` of the fresh Dyson equation and of
`M_s(z) = (F - z - s m_s(z))⁻¹`, with no measure or limit.

## Main results

* `freshDyson_eq_certificate`: `freshDyson` is the eigenvalue-form certificate root
  `certificateCanonicalDyson hF.eigenvalues s z` whenever `s > 0`, `Im z ≥ 0`.
* `freshM_nsq_le`, `freshM_quad_im`: `‖M_s y‖ ≤ (Im w)⁻¹‖y‖`,
  `Im(q* M_s q) = (η + s Im m_s)‖M_s q‖²`.
* `freshStability_eq`, `freshStability_lower`:
  `Re(1 - s⟨M_s²⟩) = η/(η + s Im m) + 2 s ⟨(Im M_s)²⟩ ≥ 2 s (Im m)²`.
* `freshM_quad_im_lower`: `Im(q* M_s q) ≥ c N^{-2max(A,1)} ‖q‖²` under `‖F‖ ≤ N^A`, `Im m ≥ v₀`,
  with no bound on `E`.
* `resolvent_trace_lipschitz`, `resolvent_quad_lipschitz`, `freshDyson_lipschitz`: Lipschitz
  bounds in `z` for the resolvent, `m_s` and `M_s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open scoped ComplexConjugate

variable {N : ℕ}

/-- The spectral parameter `w = z + s m_s(z)` of `M_s(z) = (F - w)⁻¹`. -/
def freshW (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  z + (s : ℂ) * freshDyson F s z

theorem freshM_eq (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) :
    freshM F s z = (F - freshW F s z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl

theorem add_ofReal_mul_im (z m : ℂ) (s : ℝ) : (z + (s : ℂ) * m).im = z.im + s * m.im := by
  simp

theorem freshW_im (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) :
    (freshW F s z).im = z.im + s * (freshDyson F s z).im :=
  add_ofReal_mul_im _ _ _

theorem add_ofReal_mul_im_pos {s : ℝ} {z m : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) (hm : 0 < m.im) :
    0 < (z + (s : ℂ) * m).im := by
  rw [add_ofReal_mul_im]
  exact add_pos_of_nonneg_of_pos hz (mul_pos hs hm)

/-- Normalized trace of a Hermitian resolvent is the spectral average. -/
theorem trace_resolvent_eq_average {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    (N : ℂ)⁻¹ * ((H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace =
      certificateAverage (fun i => certificateScalarResolvent (hH.eigenvalues i) w) := by
  have h := certificateMatrixTrace_eq_average H hH hw
  unfold certificateMatrixTrace certificateMatrixResolvent at h
  rw [Fintype.card_fin] at h
  rw [← h, div_eq_inv_mul]

/-- The trace equation for `m` is the certificate's spectral residual equation. -/
theorem trace_eq_iff_residual {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ}
    {z m : ℂ} (hw : (z + (s : ℂ) * m).im ≠ 0) :
    m = (N : ℂ)⁻¹ * ((F - (z + (s : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace ↔
      certificateDysonResidual hF.eigenvalues s z m = 0 := by
  rw [trace_resolvent_eq_average hF hw, certificateDysonResidual_eq_zero_iff]

/-- A root with positive imaginary part satisfies the trace equation. -/
theorem freshDyson_spec_of_im_pos (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ)
    (h : 0 < (freshDyson F s z).im) :
    freshDyson F s z = (N : ℂ)⁻¹ *
      ((F - (z + (s : ℂ) * freshDyson F s z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace := by
  classical
  by_cases hex : ∃ m : ℂ, 0 < m.im ∧
      m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹.trace
  · have hd : freshDyson F s z = Classical.choose hex := by
      unfold freshDyson
      simp only [hex, ↓reduceDIte]
    rw [hd]
    exact (Classical.choose_spec hex).2
  · have hd : freshDyson F s z = 0 := by
      unfold freshDyson
      simp only [hex, ↓reduceDIte]
    rw [hd] at h
    simp at h

/-- The positive root solves the certificate's spectral residual equation. -/
theorem freshDyson_residual_eq_zero {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {s : ℝ} {z : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) (h : 0 < (freshDyson F s z).im) :
    certificateDysonResidual hF.eigenvalues s z (freshDyson F s z) = 0 :=
  (trace_eq_iff_residual hF (add_ofReal_mul_im_pos hs hz h).ne').mp
    (freshDyson_spec_of_im_pos F s z h)

/-- The trace-form root `freshDyson` is the Palm certificate root (eigenvalue form),
for every Hermitian `F`, `N ≥ 1`, `s > 0`, `Im z ≥ 0` (including the real axis). -/
theorem freshDyson_eq_certificate {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (hN : 0 < N) {s : ℝ} {z : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) :
    freshDyson F s z = certificateCanonicalDyson hF.eigenvalues s z := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  by_cases hex : ∃ m : ℂ, 0 < m.im ∧
      m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹.trace
  · have hd : freshDyson F s z = Classical.choose hex := by
      unfold freshDyson
      simp only [hex, ↓reduceDIte]
    obtain ⟨him, heq⟩ := Classical.choose_spec hex
    have hres := (trace_eq_iff_residual hF (add_ofReal_mul_im_pos hs hz him).ne').mp heq
    rw [hd, certificateCanonicalDyson_eq hF.eigenvalues hs hz him hres]
  · have hd : freshDyson F s z = 0 := by
      unfold freshDyson
      simp only [hex, ↓reduceDIte]
    have hnot : ¬ ∃ m : ℂ, 0 < m.im ∧ certificateDysonResidual hF.eigenvalues s z m = 0 := by
      rintro ⟨m, him, hres⟩
      exact hex ⟨m, him, (trace_eq_iff_residual hF (add_ofReal_mul_im_pos hs hz him).ne').mpr hres⟩
    rw [hd]
    unfold certificateCanonicalDyson
    simp only [hnot, ↓reduceDIte]

/-!
## The fixed constants and the coarse domain
-/

/-- The variance window: `0 < c₀ - s₀ ≤ s < 1`. -/
theorem fresh_s_bounds {c₀ r₀ s₀ v₀ s : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀)
    (hs : s ∈ Set.Icc (c₀ - s₀) c₀) : 0 < c₀ - s₀ ∧ c₀ - s₀ ≤ s ∧ s < 1 := by
  obtain ⟨hc0, hc1, -, hs0, hs0c, -⟩ := hK
  exact ⟨by linarith, hs.1, lt_of_le_of_lt hs.2 hc1⟩

/-- The fresh regularity bounds on the coarse domain (any `0 ≤ η ≤ 1`, `|x-E| ≤ r₀`). -/
theorem fresh_regular_bounds {F : Matrix (Fin N) (Fin N) ℂ} {c₀ E r₀ s₀ v₀ s : ℝ}
    (hR : FreshRegular F c₀ E r₀ s₀ v₀) (hs : s ∈ Set.Icc (c₀ - s₀) c₀) {z : ℂ}
    (hx : |z.re - E| ≤ r₀) (hη : 0 ≤ z.im) (hη1 : z.im ≤ 1) :
    v₀ ≤ (freshDyson F s z).im ∧ (freshDyson F s z).im ≤ v₀⁻¹ := by
  have h := hR s hs z.re hx z.im ⟨hη, hη1⟩
  simpa using h

/-!
## Spectral form of `M_s`, operator bound and directional Ward identity
-/

/-- `⟨M_s²⟩` in spectral form. -/
theorem freshM_sq_trace_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} {z : ℂ}
    (hw : (freshW F s z).im ≠ 0) :
    (N : ℂ)⁻¹ * (freshM F s z * freshM F s z).trace =
      certificateAverage (fun i => certificateScalarResolvent (hF.eigenvalues i)
        (freshW F s z) ^ 2) := by
  have hM : freshM F s z = profileSpectralAut F hF (Matrix.diagonal
      (fun i => certificateScalarResolvent (hF.eigenvalues i) (freshW F s z))) :=
    certificateMatrixResolvent_eq_spectral F hF hw
  rw [hM, ← map_mul, Matrix.diagonal_mul_diagonal, certificate_trace_spectralAut,
    Matrix.trace_diagonal]
  unfold certificateAverage
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_inv_mul]
  simp only [pow_two]

/-- Operator bound `‖M_s y‖² ≤ (Im w)⁻² ‖y‖²`. -/
theorem freshM_nsq_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} {z : ℂ}
    (hw : (freshW F s z).im ≠ 0) (y : Fin N → ℂ) :
    nsq (freshM F s z *ᵥ y) ≤ (((freshW F s z).im) ^ 2)⁻¹ * nsq y :=
  hermitian_resolvent_nsq_le hF hw y

/-- Directional Ward identity: `q* Im M_s q = (η + s Im m_s) ‖M_s q‖²`. -/
theorem freshM_quad_im {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} {z : ℂ}
    (hw : (freshW F s z).im ≠ 0) (q : Fin N → ℂ) :
    (star q ⬝ᵥ (freshM F s z *ᵥ q)).im =
      (z.im + s * (freshDyson F s z).im) * nsq (freshM F s z *ᵥ q) := by
  rw [freshM_eq, hermitian_resolvent_quad_im hF hw, freshW_im]

/-- **Stability identity.** `Re(1 - s⟨M_s²⟩) = η/(η + s Im m) + 2s⟨(Im M_s)²⟩`. -/
theorem freshStability_eq {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {s : ℝ} {z : ℂ}
    (hs : 0 < s) (hz : 0 ≤ z.im) (hm : 0 < (freshDyson F s z).im) :
    (1 - (s : ℂ) * ((N : ℂ)⁻¹ * (freshM F s z * freshM F s z).trace)).re =
      z.im / (z.im + s * (freshDyson F s z).im) + 2 * s * certificateRealAverage
        (fun i => (certificateScalarResolvent (hF.eigenvalues i) (freshW F s z)).im ^ 2) := by
  set m := freshDyson F s z with hmdef
  have hwpos : 0 < (freshW F s z).im := add_ofReal_mul_im_pos hs hz hm
  have hres := freshDyson_residual_eq_zero hF hs hz hm
  have hward := certificate_dyson_ward hF.eigenvalues s z m hres
  rw [freshM_sq_trace_eq hF hwpos.ne']
  set r : Fin N → ℂ := fun i => certificateScalarResolvent (hF.eigenvalues i) (freshW F s z)
    with hr
  have hre : (1 - (s : ℂ) * certificateAverage (fun i => r i ^ 2)).re =
      1 - s * certificateRealAverage (fun i => Complex.normSq (r i)) +
        2 * s * certificateRealAverage (fun i => (r i).im ^ 2) := by
    rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, certificateAverage_re]
    have hs2 : ∀ x : ℂ, (x ^ 2).re = Complex.normSq x - 2 * x.im ^ 2 := by
      intro x
      simp [pow_two, Complex.normSq_apply]
      ring
    simp_rw [hs2]
    simp only [certificateRealAverage, Finset.expect_sub_distrib, ← Finset.mul_expect]
    ring
  rw [hre]
  have hpos : 0 < z.im + s * m.im := by rw [← freshW_im]; exact hwpos
  have hA : s * certificateRealAverage (fun i => Complex.normSq (r i)) =
      1 - z.im / (z.im + s * m.im) := by
    have hward' : m.im = (z.im + s * m.im) *
        certificateRealAverage (fun i => Complex.normSq (r i)) := hward
    have hx : z.im / (z.im + s * m.im) =
        1 - s * certificateRealAverage (fun i => Complex.normSq (r i)) := by
      rw [div_eq_iff hpos.ne']
      linear_combination (-s) * hward'
    linarith
  rw [hA]
  ring

/-- **Stability bound.** `Re(1 - s⟨M_s²⟩) ≥ 2 s (Im m_s)²` (Jensen). -/
theorem freshStability_lower {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} {z : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) (hm : 0 < (freshDyson F s z).im) :
    2 * s * (freshDyson F s z).im ^ 2 ≤
      (1 - (s : ℂ) * ((N : ℂ)⁻¹ * (freshM F s z * freshM F s z).trace)).re := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [freshStability_eq hF hs hz hm]
  have hres := freshDyson_residual_eq_zero hF hs hz hm
  have hmean : (freshDyson F s z).im = certificateRealAverage
      (fun i => (certificateScalarResolvent (hF.eigenvalues i) (freshW F s z)).im) := by
    rw [← certificateAverage_im]
    exact congrArg Complex.im
      ((certificateDysonResidual_eq_zero_iff hF.eigenvalues s z _).mp hres)
  have hj := certificate_jensen
    (fun i => (certificateScalarResolvent (hF.eigenvalues i) (freshW F s z)).im)
  rw [← hmean] at hj
  have hpos : 0 < z.im + s * (freshDyson F s z).im := by
    rw [← freshW_im]; exact add_ofReal_mul_im_pos hs hz hm
  have h0 : 0 ≤ z.im / (z.im + s * (freshDyson F s z).im) := div_nonneg hz hpos.le
  nlinarith

/-- Stability bound on the domain: `Re(1 - s⟨M_s²⟩) ≥ 2(c₀ - s₀) v₀²` under the fresh regularity
bounds. -/
theorem freshStability_domain {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {c₀ E r₀ s₀ v₀ s : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hR : FreshRegular F c₀ E r₀ s₀ v₀)
    (hs : s ∈ Set.Icc (c₀ - s₀) c₀) {z : ℂ} (hx : |z.re - E| ≤ r₀) (hη : 0 ≤ z.im)
    (hη1 : z.im ≤ 1) :
    2 * (c₀ - s₀) * v₀ ^ 2 ≤
      (1 - (s : ℂ) * ((N : ℂ)⁻¹ * (freshM F s z * freshM F s z).trace)).re := by
  obtain ⟨hs0, hss, -⟩ := fresh_s_bounds hK hs
  obtain ⟨hv, -⟩ := fresh_regular_bounds hR hs hx hη hη1
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  have hm : 0 < (freshDyson F s z).im := lt_of_lt_of_le hv0 hv
  have h := freshStability_lower hF hN (lt_of_lt_of_le hs0 hss) hη hm
  have hsq : v₀ ^ 2 ≤ (freshDyson F s z).im ^ 2 := pow_le_pow_left₀ hv0.le hv 2
  have : 2 * (c₀ - s₀) * v₀ ^ 2 ≤ 2 * s * (freshDyson F s z).im ^ 2 := by
    apply mul_le_mul (by linarith) hsq (by positivity) (by linarith)
  linarith

/-!
## The directional lower bound `q* Im M_s q ≥ c N^{-2max(A,1)} ‖q‖²`
-/

/-- Eigenvalues are bounded by the operator norm bound `‖F‖ ≤ N^A`. -/
theorem eigenvalue_abs_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {A : ℝ}
    (hB : NormBound F A) (i : Fin N) : |hF.eigenvalues i| ≤ (N : ℝ) ^ A := by
  set u : Fin N → ℂ := (hF.eigenvectorBasis i).ofLp with hu
  have hev : F *ᵥ u = ((hF.eigenvalues i : ℝ) : ℂ) • u := by
    rw [hu, hF.mulVec_eigenvectorBasis i]
    ext k
    simp [Complex.real_smul]
  have hnorm : nsq u = 1 := by
    rw [nsq_eq_euclidean, hu, WithLp.toLp_ofLp, (hF.eigenvectorBasis).orthonormal.1 i, one_pow]
  have h := hB u
  rw [hev, l2Norm_eq_sqrt_nsq, l2Norm_eq_sqrt_nsq, nsq_smul, hnorm, mul_one, Real.sqrt_one,
    mul_one, Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- `|Re w| ≤ N^A + v₀⁻¹` from `Im m ≥ v₀` and `‖F‖ ≤ N^A` (no bound on `E` is needed). -/
theorem freshW_re_abs_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {A s v₀ : ℝ} {z : ℂ} (hB : NormBound F A) (hs : 0 < s) (hz : 0 ≤ z.im) (hv0 : 0 < v₀)
    (hv : v₀ ≤ (freshDyson F s z).im) :
    |(freshW F s z).re| ≤ (N : ℝ) ^ A + v₀⁻¹ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hm : 0 < (freshDyson F s z).im := lt_of_lt_of_le hv0 hv
  have hres := freshDyson_residual_eq_zero hF hs hz hm
  have heq := (certificateDysonResidual_eq_zero_iff hF.eigenvalues s z _).mp hres
  by_contra hcon'
  have hcon := not_le.mp hcon'
  set d := |(freshW F s z).re| - (N : ℝ) ^ A with hd
  have hdv : v₀⁻¹ < d := by rw [hd]; linarith
  have hdpos : 0 < d := lt_trans (inv_pos.mpr hv0) hdv
  have hpt : ∀ i, ‖certificateScalarResolvent (hF.eigenvalues i) (freshW F s z)‖ ≤ d⁻¹ := by
    intro i
    unfold certificateScalarResolvent
    rw [norm_inv]
    refine inv_anti₀ hdpos ?_
    have hlam := eigenvalue_abs_le hF hB i
    have h1 := Complex.abs_re_le_norm (((hF.eigenvalues i : ℝ) : ℂ) - freshW F s z)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have h2 : |(freshW F s z).re| - |hF.eigenvalues i| ≤ |hF.eigenvalues i - (freshW F s z).re| := by
      have := abs_sub_abs_le_abs_sub (freshW F s z).re (hF.eigenvalues i)
      rw [abs_sub_comm] at this
      exact this
    rw [hd]
    linarith
  have havg := certificateAverage_norm_le_const _ _ hpt
  have hw' : (fun i => certificateScalarResolvent (hF.eigenvalues i)
      (z + s * freshDyson F s z)) =
      (fun i => certificateScalarResolvent (hF.eigenvalues i) (freshW F s z)) := rfl
  have hmn : ‖freshDyson F s z‖ ≤ d⁻¹ := by
    rw [heq]
    exact havg
  have him := (Complex.im_le_norm (freshDyson F s z)).trans hmn
  have : d⁻¹ < v₀ := by
    rw [inv_lt_comm₀ hdpos hv0]
    exact hdv
  linarith

/-- `‖(F - w)y‖ ≤ (N^A + |w|)‖y‖`. -/
theorem shift_sqrt_nsq_le {F : Matrix (Fin N) (Fin N) ℂ} {A : ℝ} (hB : NormBound F A) (w : ℂ)
    (y : Fin N → ℂ) :
    Real.sqrt (nsq ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ y)) ≤
      ((N : ℝ) ^ A + ‖w‖) * Real.sqrt (nsq y) := by
  have hsplit : (F - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ y = F *ᵥ y + (-w) • y := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, neg_smul, sub_eq_add_neg]
  rw [hsplit]
  have h1 := sqrt_nsq_add_le (F *ᵥ y) ((-w) • y)
  have h2 : Real.sqrt (nsq (F *ᵥ y)) ≤ (N : ℝ) ^ A * Real.sqrt (nsq y) := hB y
  have h3 : Real.sqrt (nsq ((-w) • y)) = ‖w‖ * Real.sqrt (nsq y) := by
    rw [nsq_smul, norm_neg, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rw [h3] at h1
  linarith

/-- The constant `c_low = (c₀ - s₀) v₀ (3 + 2/v₀)⁻²` of the directional lower bound. -/
def lowConst (c₀ s₀ v₀ : ℝ) : ℝ := (c₀ - s₀) * v₀ / (3 + 2 / v₀) ^ 2

theorem rpow_neg_two_mul (N : ℕ) (a : ℝ) :
    (N : ℝ) ^ (-(2 * a)) = (((N : ℝ) ^ a) ^ 2)⁻¹ := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Real.rpow_neg hN0, mul_comm, Real.rpow_mul hN0, Real.rpow_two]

/-- **Directional lower bound.** `q* Im M_s q ≥ c_low N^{-2max(A,1)} ‖q‖²` on `0 ≤ η ≤ 1`,
`|x - E| ≤ r₀`. -/
theorem freshM_quad_im_lower {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c₀ E r₀ s₀ v₀ s : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀)
    (hC : FreshClass F A c₀ E r₀ s₀ v₀) (hs : s ∈ Set.Icc (c₀ - s₀) c₀) {z : ℂ}
    (hx : |z.re - E| ≤ r₀) (hη : 0 ≤ z.im) (hη1 : z.im ≤ 1) (q : Fin N → ℂ) :
    lowConst c₀ s₀ v₀ * (N : ℝ) ^ (-(2 * max A 1)) * nsq q ≤
      (star q ⬝ᵥ (freshM F s z *ᵥ q)).im := by
  obtain ⟨hF, hB, hR⟩ := hC
  obtain ⟨hs0, hss, hs1⟩ := fresh_s_bounds hK hs
  have hv0 : 0 < v₀ := hK.2.2.2.2.2
  obtain ⟨hv, hv'⟩ := fresh_regular_bounds hR hs hx hη hη1
  have hspos : 0 < s := lt_of_lt_of_le hs0 hss
  have hm : 0 < (freshDyson F s z).im := lt_of_lt_of_le hv0 hv
  have hwpos : 0 < (freshW F s z).im := add_ofReal_mul_im_pos hspos hη hm
  -- |w| ≤ N^A + 1 + 2/v₀
  have hre := freshW_re_abs_le hF hN hB hspos hη hv0 hv
  have himw : (freshW F s z).im ≤ 1 + v₀⁻¹ := by
    rw [freshW_im]
    have : s * (freshDyson F s z).im ≤ v₀⁻¹ := by
      calc s * (freshDyson F s z).im ≤ 1 * v₀⁻¹ :=
            mul_le_mul hs1.le hv' hm.le zero_le_one
        _ = v₀⁻¹ := one_mul _
    linarith
  have hwn : ‖freshW F s z‖ ≤ (N : ℝ) ^ A + 1 + 2 * v₀⁻¹ := by
    have := Complex.norm_le_abs_re_add_abs_im (freshW F s z)
    rw [abs_of_pos hwpos] at this
    linarith
  -- N^A ≤ N^a, 1 ≤ N^a
  set a := max A 1 with ha
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNa : (N : ℝ) ^ A ≤ (N : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have hNa1 : (1 : ℝ) ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1 (by rw [ha]; positivity)
  have hNA0 : 0 ≤ (N : ℝ) ^ A := Real.rpow_nonneg (Nat.cast_nonneg N) A
  set K := (3 + 2 / v₀) * (N : ℝ) ^ a with hKdef
  have hKpos : 0 < K := by positivity
  have hbound : (N : ℝ) ^ A + ‖freshW F s z‖ ≤ K := by
    rw [hKdef, add_mul, div_eq_mul_inv]
    nlinarith
  -- ‖q‖ ≤ K ‖M q‖
  have hq : Real.sqrt (nsq q) ≤ K * Real.sqrt (nsq (freshM F s z *ᵥ q)) := by
    have h := shift_sqrt_nsq_le hB (freshW F s z) (freshM F s z *ᵥ q)
    rw [freshM_eq, mulVec_mulVec, hermitian_shift_mul_inv hF hwpos.ne', one_mulVec] at h
    rw [← freshM_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg _))
  have hq2 : nsq q ≤ K ^ 2 * nsq (freshM F s z *ᵥ q) := by
    have h0 := Real.sqrt_nonneg (nsq q)
    have hsq := pow_le_pow_left₀ h0 hq 2
    rw [Real.sq_sqrt (nsq_nonneg _), mul_pow, Real.sq_sqrt (nsq_nonneg _)] at hsq
    exact hsq
  rw [freshM_quad_im hF hwpos.ne', ← freshW_im]
  have hsv : (c₀ - s₀) * v₀ ≤ (freshW F s z).im := by
    rw [freshW_im]
    have : (c₀ - s₀) * v₀ ≤ s * (freshDyson F s z).im :=
      mul_le_mul hss hv hv0.le hspos.le
    linarith
  have hlow : lowConst c₀ s₀ v₀ * (N : ℝ) ^ (-(2 * a)) = (c₀ - s₀) * v₀ / K ^ 2 := by
    rw [lowConst, rpow_neg_two_mul N, hKdef]
    field_simp
  rw [hlow]
  have hMq := nsq_nonneg (freshM F s z *ᵥ q)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc (c₀ - s₀) * v₀ * nsq q ≤ (freshW F s z).im * (K ^ 2 * nsq (freshM F s z *ᵥ q)) :=
        mul_le_mul hsv hq2 (nsq_nonneg _) hwpos.le
    _ = _ := by ring

/-!
## Lipschitz bounds in `z`
-/

/-- `|⟨R(z)⟩ - ⟨R(z')⟩| ≤ |z - z'| h⁻²` for `Im z, Im z' ≥ h > 0`. -/
theorem resolvent_trace_lipschitz {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hN : 0 < N) {h : ℝ} (hh : 0 < h) {z z' : ℂ} (hz : h ≤ z.im) (hz' : h ≤ z'.im) :
    ‖(N : ℂ)⁻¹ * ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace -
        (N : ℂ)⁻¹ * ((H - z' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace‖ ≤
      ‖z - z'‖ * h⁻¹ ^ 2 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [trace_resolvent_eq_average hH (hh.trans_le hz).ne',
    trace_resolvent_eq_average hH (hh.trans_le hz').ne']
  unfold certificateAverage
  rw [← Finset.expect_sub_distrib]
  apply certificateAverage_norm_le_const
  intro i
  exact certificateScalarResolvent_lipschitz _ hh hz hz'

/-- `|q*(R(w) - R(w'))q| ≤ |w - w'| h⁻² ‖q‖²` for `Im w, Im w' ≥ h > 0`. -/
theorem resolvent_quad_lipschitz {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    {h : ℝ} (hh : 0 < h) {w w' : ℂ} (hw : h ≤ w.im) (hw' : h ≤ w'.im) (q : Fin N → ℂ) :
    ‖star q ⬝ᵥ (((H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        (H - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) *ᵥ q)‖ ≤
      ‖w - w'‖ * h⁻¹ ^ 2 * nsq q := by
  have hwi : w.im ≠ 0 := (hh.trans_le hw).ne'
  have hwi' : w'.im ≠ 0 := (hh.trans_le hw').ne'
  rw [hermitian_resolvent_sub hH hwi hwi']
  apply norm_quad_le_of_nsq_le _ (by positivity)
  intro y
  rw [smul_mulVec, nsq_smul, ← mulVec_mulVec]
  have h1 := hermitian_resolvent_nsq_le hH hwi ((H - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y)
  have h2 := hermitian_resolvent_nsq_le hH hwi' y
  have hb : ∀ v : ℂ, h ≤ v.im → (v.im ^ 2)⁻¹ ≤ h⁻¹ ^ 2 := by
    intro v hv
    rw [inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hh.le hv 2)
  have hy := nsq_nonneg y
  have hy' := nsq_nonneg ((H - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y)
  have hb1 := hb w hw
  have hb2 := hb w' hw'
  have hinv0 : 0 ≤ (w.im ^ 2)⁻¹ := by positivity
  have k1 : nsq ((H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ
      ((H - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y)) ≤ h⁻¹ ^ 2 * (h⁻¹ ^ 2 * nsq y) := by
    calc _ ≤ (w.im ^ 2)⁻¹ * nsq ((H - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y) := h1
      _ ≤ h⁻¹ ^ 2 * ((w'.im ^ 2)⁻¹ * nsq y) := mul_le_mul hb1 h2 hy' (by positivity)
      _ ≤ h⁻¹ ^ 2 * (h⁻¹ ^ 2 * nsq y) := by gcongr
  calc ‖w - w'‖ ^ 2 * nsq _ ≤ ‖w - w'‖ ^ 2 * (h⁻¹ ^ 2 * (h⁻¹ ^ 2 * nsq y)) :=
        mul_le_mul_of_nonneg_left k1 (by positivity)
    _ = (‖w - w'‖ * h⁻¹ ^ 2) ^ 2 * nsq y := by ring

/-- Lipschitz bound for the Dyson root: if `δ₀ ≤ η/(η + s Im m)` at both points then
`|m(z) - m(z')| ≤ |z - z'|/(s δ₀)` (Dyson subtraction + Ward + Cauchy–Schwarz). -/
theorem freshDyson_lipschitz {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z z' : ℂ} (hz : 0 ≤ z.im) (hz' : 0 ≤ z'.im)
    (hm : 0 < (freshDyson F s z).im) (hm' : 0 < (freshDyson F s z').im) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hδ : δ₀ ≤ z.im / (z.im + s * (freshDyson F s z).im))
    (hδ' : δ₀ ≤ z'.im / (z'.im + s * (freshDyson F s z').im)) :
    ‖freshDyson F s z - freshDyson F s z'‖ ≤ ‖z - z'‖ / (s * δ₀) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set m := freshDyson F s z with hmdef
  set m' := freshDyson F s z' with hm'def
  have hwpos : 0 < (z + (s : ℂ) * m).im := add_ofReal_mul_im_pos hs hz hm
  have hwpos' : 0 < (z' + (s : ℂ) * m').im := add_ofReal_mul_im_pos hs hz' hm'
  have hres := freshDyson_residual_eq_zero hF hs hz hm
  have hres' := freshDyson_residual_eq_zero hF hs hz' hm'
  set r : Fin N → ℂ := fun i => certificateScalarResolvent (hF.eigenvalues i) (z + s * m)
  set r' : Fin N → ℂ := fun i => certificateScalarResolvent (hF.eigenvalues i) (z' + s * m')
  have heq : m = certificateAverage r :=
    (certificateDysonResidual_eq_zero_iff hF.eigenvalues s z m).mp hres
  have heq' : m' = certificateAverage r' :=
    (certificateDysonResidual_eq_zero_iff hF.eigenvalues s z' m').mp hres'
  set T := certificateAverage (fun i => r i * r' i) with hT
  -- (m - m') (1 - sT) = (z - z') T
  have hdiff0 : certificateAverage r - certificateAverage r' =
      ((z + s * m) - (z' + s * m')) * T := by
    rw [hT]
    unfold certificateAverage
    rw [← Finset.expect_sub_distrib, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro i _
    show certificateScalarResolvent (hF.eigenvalues i) (z + s * m) -
        certificateScalarResolvent (hF.eigenvalues i) (z' + s * m') =
      ((z + s * m) - (z' + s * m')) * (certificateScalarResolvent (hF.eigenvalues i) (z + s * m) *
        certificateScalarResolvent (hF.eigenvalues i) (z' + s * m'))
    rw [certificate_scalar_resolvent_sub _ hwpos.ne' hwpos'.ne']
    ring
  have hdiff : m - m' = ((z + s * m) - (z' + s * m')) * T := by
    calc m - m' = certificateAverage r - certificateAverage r' := by rw [← heq, ← heq']
      _ = _ := hdiff0
  have hkey : (m - m') * (1 - (s : ℂ) * T) = (z - z') * T := by
    linear_combination hdiff
  -- Ward: s A = 1 - η/(η + s Im m)
  have hward := certificate_dyson_ward hF.eigenvalues s z m hres
  have hward' := certificate_dyson_ward hF.eigenvalues s z' m' hres'
  set Aa := certificateRealAverage (fun i => Complex.normSq (r i))
  set Ab := certificateRealAverage (fun i => Complex.normSq (r' i))
  have hAa0 : 0 ≤ Aa := Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hAb0 : 0 ≤ Ab := Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hp : 0 < z.im + s * m.im := by rw [← add_ofReal_mul_im]; exact hwpos
  have hp' : 0 < z'.im + s * m'.im := by rw [← add_ofReal_mul_im]; exact hwpos'
  have hwa : m.im = (z.im + s * m.im) * Aa := hward
  have hwb : m'.im = (z'.im + s * m'.im) * Ab := hward'
  have hsA : s * Aa ≤ 1 - δ₀ := by
    have h1 : z.im / (z.im + s * m.im) = 1 - s * Aa := by
      rw [div_eq_iff hp.ne']
      linear_combination (-s) * hwa
    linarith
  have hsB : s * Ab ≤ 1 - δ₀ := by
    have h1 : z'.im / (z'.im + s * m'.im) = 1 - s * Ab := by
      rw [div_eq_iff hp'.ne']
      linear_combination (-s) * hwb
    linarith
  have hδ1 : 0 ≤ 1 - δ₀ := le_trans (mul_nonneg hs.le hAa0) hsA
  have hTsq : ‖T‖ ^ 2 ≤ Aa * Ab := certificateAverage_mul_normSq_le r r'
  have hsT : s * ‖T‖ ≤ 1 - δ₀ := by
    have hsq : (s * ‖T‖) ^ 2 ≤ (1 - δ₀) ^ 2 := by
      calc (s * ‖T‖) ^ 2 = s ^ 2 * ‖T‖ ^ 2 := by ring
        _ ≤ s ^ 2 * (Aa * Ab) := mul_le_mul_of_nonneg_left hTsq (by positivity)
        _ = (s * Aa) * (s * Ab) := by ring
        _ ≤ (1 - δ₀) * (1 - δ₀) :=
            mul_le_mul hsA hsB (mul_nonneg hs.le hAb0) hδ1
        _ = (1 - δ₀) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hδ1 two_ne_zero).mp hsq
  have hlow : δ₀ ≤ ‖1 - (s : ℂ) * T‖ := by
    have h1 : ‖(s : ℂ) * T‖ = s * ‖T‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have h2 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * T)
    rw [norm_one, h1] at h2
    linarith
  have hT : ‖T‖ ≤ s⁻¹ := by
    have h1 : s * ‖T‖ ≤ 1 := by linarith
    calc ‖T‖ = s⁻¹ * (s * ‖T‖) := by field_simp
      _ ≤ s⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = s⁻¹ := mul_one _
  have hnorm := congrArg norm hkey
  rw [norm_mul, norm_mul] at hnorm
  have h3 : ‖m - m'‖ * δ₀ ≤ ‖z - z'‖ * s⁻¹ := by
    calc ‖m - m'‖ * δ₀ ≤ ‖m - m'‖ * ‖1 - (s : ℂ) * T‖ :=
          mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = ‖z - z'‖ * ‖T‖ := hnorm
      _ ≤ ‖z - z'‖ * s⁻¹ := mul_le_mul_of_nonneg_left hT (norm_nonneg _)
  rw [le_div_iff₀ (mul_pos hs hδ₀)]
  calc ‖m - m'‖ * (s * δ₀) = s * (‖m - m'‖ * δ₀) := by ring
    _ ≤ s * (‖z - z'‖ * s⁻¹) := mul_le_mul_of_nonneg_left h3 hs.le
    _ = ‖z - z'‖ := by field_simp

end BlockBand.Palm.CoarseRelative
