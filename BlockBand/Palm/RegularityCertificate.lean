module
public import BlockBand.Palm.RegularityUniformLocal
public import BlockBand.Palm.RegularityDescent
/-!
# The regularity certificate from one trace

If the normalized resolvent trace of a Hermitian `F` at the single point `E`, variance `c`, is
close to a reference value `μ` (`‖certificateChi F c E μ‖ ≤ ε`), then on a fixed rectangle of
variances `s`, energies `x` and heights `0 ≤ η ≤ 1` the positive root of the scalar Dyson
equation exists, solves the matrix trace equation, and has imaginary part in `[v₀, v₀⁻¹]`; at
`(c, E)` it is within `C ‖certificateChi‖` of `μ`, and the zero-height covariance operators are
comparable in the Loewner order. Everything is deterministic.

## Main results

* `certificate_full_uniform`: the certificate for a general reference `μ` with `Im μ ≥ V`,
  `|μ| ≤ 1`.
* `certificate_semicircle_full`: the certificate for the semicircle reference on a compact bulk
  interval `|E| ≤ 2 - θ`.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Palm
open Matrix
open scoped BigOperators ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The imaginary part of the scalar resolvent is strictly positive above the real axis. -/
theorem certificate_scalar_im_pos (d : ℝ) {a : ℂ} (ha : 0 < a.im) :
    0 < (certificateScalarResolvent d a).im := by
  rw [certificate_scalar_ward]
  apply mul_pos ha
  apply Complex.normSq_pos.mpr
  unfold certificateScalarResolvent
  apply inv_ne_zero
  intro heq
  have hzero : a.im = 0 := by
    simpa only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub, neg_eq_zero]
      using congrArg Complex.im heq
  exact ha.ne' hzero

omit [DecidableEq ι] in
/-- Roots with positive imaginary part are unique, also at `η = 0`. -/
theorem certificate_dyson_unique_nonnegative (spectrum : ι → ℝ) {s : ℝ} {z m n : ℂ}
    (hs : 0 < s) (hz : 0 ≤ z.im) (hmim : 0 < m.im) (hnim : 0 < n.im)
    (hm : certificateDysonResidual spectrum s z m = 0)
    (hn : certificateDysonResidual spectrum s z n = 0) : m = n := by
  let f : ι → ℂ := fun i => certificateScalarResolvent (spectrum i) (z + s * m)
  let g : ι → ℂ := fun i => certificateScalarResolvent (spectrum i) (z + s * n)
  have hma : 0 < (z + s * m).im := by simpa using add_pos_of_nonneg_of_pos hz (mul_pos hs hmim)
  have hna : 0 < (z + s * n).im := by simpa using add_pos_of_nonneg_of_pos hz (mul_pos hs hnim)
  have hA := certificate_dyson_ward_le spectrum hs hz hmim hm
  have hB := certificate_dyson_ward_le spectrum hs hz hnim hn
  let A := certificateRealAverage (fun i => Complex.normSq (f i))
  let B := certificateRealAverage (fun i => Complex.normSq (g i))
  let C := certificateRealAverage (fun i => ‖f i‖ * ‖g i‖)
  have hA0 : 0 ≤ A := Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hB0 : 0 ≤ B := Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hC0 : 0 ≤ C := Finset.expect_nonneg (fun _ _ => by positivity)
  have hAB : A * B ≤ s⁻¹ * s⁻¹ := mul_le_mul hA hB hB0 (inv_nonneg.mpr hs.le)
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => ‖f i‖) (fun i => ‖g i‖)
  simp only [← Complex.normSq_eq_norm_sq] at hCS
  have hC : C ≤ s⁻¹ := by
    have hsq : C ^ 2 ≤ s⁻¹ * s⁻¹ := hCS.trans hAB
    nlinarith [inv_pos.mpr hs]
  have hpoint : ∀ i, (f i * g i).re < ‖f i‖ * ‖g i‖ := by
    intro i
    have hfim : 0 < (f i).im := certificate_scalar_im_pos _ hma
    have hgim : 0 < (g i).im := certificate_scalar_im_pos _ hna
    have hre : (f i).re * (g i).re ≤ ‖f i‖ * ‖g i‖ := by
      calc
        _ ≤ |(f i).re * (g i).re| := le_abs_self _
        _ = |(f i).re| * |(g i).re| := abs_mul _ _
        _ ≤ _ := mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          (abs_nonneg _) (norm_nonneg _)
    rw [Complex.mul_re]
    linarith [mul_pos hfim hgim]
  have hreal : (certificateAverage (fun i => f i * g i)).re < C := by
    rw [certificateAverage_re]
    obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
    exact Finset.expect_lt_expect (fun j _ => (hpoint j).le) ⟨i, hi, hpoint i⟩
  have hfactor : 1 - (s : ℂ) * certificateAverage (fun i => f i * g i) ≠ 0 := by
    have hr := mul_lt_mul_of_pos_left (hreal.trans_le hC) hs
    rw [mul_inv_cancel₀ hs.ne'] at hr
    intro heq
    have hzero := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hzero
    linarith
  have hsub := certificate_dyson_sub spectrum s z hma.ne' hna.ne'
  rw [hm, hn, sub_self] at hsub
  have hmn : m - n = 0 := (mul_eq_zero.mp hsub.symm).resolve_right hfactor
  exact sub_eq_zero.mp hmn

omit [DecidableEq ι] [Nonempty ι] in
/-- The positive Dyson root, chosen by classical selection where the scalar reciprocal equation
has a solution with positive imaginary part. -/
def certificateCanonicalDyson (spectrum : ι → ℝ) (s : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if h : ∃ m : ℂ, 0 < m.im ∧ certificateDysonResidual spectrum s z m = 0 then
    Classical.choose h else 0

omit [DecidableEq ι] [Nonempty ι] in
/-- The selected root solves the equation whenever a positive solution exists. -/
theorem certificateCanonicalDyson_spec (spectrum : ι → ℝ) (s : ℝ) (z : ℂ)
    (h : ∃ m : ℂ, 0 < m.im ∧ certificateDysonResidual spectrum s z m = 0) :
    0 < (certificateCanonicalDyson spectrum s z).im ∧
      certificateDysonResidual spectrum s z (certificateCanonicalDyson spectrum s z) = 0 := by
  unfold certificateCanonicalDyson
  rw [dite_eq_left h]
  exact Classical.choose_spec h

omit [DecidableEq ι] in
/-- The selected root equals every root with positive imaginary part, for `η ≥ 0`. -/
theorem certificateCanonicalDyson_eq (spectrum : ι → ℝ) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 ≤ z.im) (hmim : 0 < m.im)
    (hm : certificateDysonResidual spectrum s z m = 0) :
    certificateCanonicalDyson spectrum s z = m := by
  have hspec := certificateCanonicalDyson_spec spectrum s z ⟨m, hmim, hm⟩
  exact certificate_dyson_unique_nonnegative spectrum hs hz hspec.1 hmim hspec.2 hm

omit [DecidableEq ι] in
/-- Uniform upper bound on `Im m` in the variance interval `c/2 ≤ s ≤ 1`. -/
theorem certificate_dyson_im_upper (spectrum : ι → ℝ) {c s : ℝ} {z m : ℂ}
    (hc : 0 < c) (hc1 : c < 1) (hs : c / 2 ≤ s) (hz : 0 ≤ z.im)
    (hmim : 0 < m.im) (hm : certificateDysonResidual spectrum s z m = 0) :
    m.im ≤ 2 / c := by
  have hspos : 0 < s := by linarith
  have hsq := certificate_dyson_normSq_le spectrum hspos hz hmim hm
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hinv : s⁻¹ ≤ 2 / c := by
    have hh := inv_anti₀ (by positivity : 0 < c / 2) hs
    convert hh using 1
    field_simp [hc.ne']
  have hnormsq : ‖m‖ ^ 2 ≤ 2 / c := hsq.trans hinv
  have hL : 1 ≤ 2 / c := by rw [le_div_iff₀ hc]; linarith
  have hnorm : ‖m‖ ≤ 2 / c := by nlinarith [norm_nonneg m]
  exact (Complex.im_le_norm m).trans hnorm

omit [Nonempty ι] in
/-- Both Loewner bounds between covariance operators, with one common relative constant. -/
theorem certificate_covariance_symmetric
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c E ε : ℝ} {μ m : ℂ}
    (hc : 0 < c) (hμ : 0 < μ.im) (he : 0 ≤ ε) (he4 : ε ≤ 1 / 4)
    (hm : ‖m - μ‖ ≤ ε * μ.im) :
    (zeroHeightOperator F E c m.re m.im -
      ((1 - 8 * ε : ℝ) : ℂ) • zeroHeightOperator F E c μ.re μ.im).PosSemidef ∧
    (((1 + 8 * ε : ℝ) : ℂ) • zeroHeightOperator F E c μ.re μ.im -
      zeroHeightOperator F E c m.re m.im).PosSemidef := by
  refine ⟨?_, certificate_covariance_upper F hF hc hμ he he4 hm⟩
  have hlo := certificate_covariance_lower F hF (E := E) hc hμ he he4 hm
  have hz := (zeroHeightOperator_posDef F hF (x := E) (u := μ.re) hc hμ).posSemidef
  have hscale := hz.smul (α := ℂ) (Complex.zero_le_real.mpr (show 0 ≤ 4 * ε by positivity))
  have hsum := hlo.add hscale
  convert hsum using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  push_cast
  ring

/-- Uniform lower bound on `Im m` at a fixed positive height, from the reference trace and the
Ward identity. -/
theorem certificate_uniform_positive_height_lower
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {c V E s : ℝ} {μ z m : ℂ}
    (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) (hVμ : V ≤ μ.im) (hμnorm : ‖μ‖ ≤ 1)
    (hchi : ‖certificateChi F c E μ‖ ≤ V / 2)
    (hs : 0 < s) (hs1 : s ≤ 1) (hz : 0 < z.im) (hzE : ‖z - (E : ℂ)‖ ≤ 2)
    (hmim : 0 < m.im) (hm : certificateDysonResidual hF.eigenvalues s z m = 0) :
    z.im * (1 + 4 / (c * V))⁻¹ ^ 2 * (2 * c)⁻¹ ≤ m.im := by
  have hsm := certificate_dyson_s_mul_norm_le_one hF.eigenvalues hs hs1 hz.le hmim hm
  have hcm : c * ‖μ‖ ≤ 1 := (mul_le_mul_of_nonneg_left hμnorm hc.le).trans (by simpa using hc1.le)
  have hshift : ‖z + s * m - ((E : ℂ) + c * μ)‖ ≤ 4 := by
    have heq : z + s * m - ((E : ℂ) + c * μ) = (z - (E : ℂ)) + (s : ℂ) * m - (c : ℂ) * μ := by ring
    rw [heq]
    calc
      _ ≤ ‖z - (E : ℂ)‖ + ‖(s : ℂ) * m‖ + ‖(c : ℂ) * μ‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖z - (E : ℂ)‖ + s * ‖m‖ + c * ‖μ‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hs, abs_of_pos hc]
      _ ≤ 4 := by linarith
  have hza : 0 < (z + s * m).im := by simpa using add_pos hz (mul_pos hs hmim)
  have h₀ : c * V ≤ ((E : ℂ) + c * μ).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add]
    exact mul_le_mul_of_nonneg_left hVμ hc.le
  have hA := certificate_average_shift_lower hF.eigenvalues (mul_pos hc hV)
    (by norm_num : (0 : ℝ) ≤ 4) h₀ hza hshift
  have hA₀ := certificate_reference_average_lower F hF hc (hV.trans_le hVμ)
    (by linarith : ‖certificateChi F c E μ‖ ≤ μ.im / 2)
  have hlow := (mul_le_mul_of_nonneg_left hA₀ (sq_nonneg ((1 + 4 / (c * V))⁻¹))).trans hA
  have hward := certificate_dyson_ward hF.eigenvalues s z m hm
  have hAvg0 : 0 ≤ certificateRealAverage (fun i => Complex.normSq
      (certificateScalarResolvent (hF.eigenvalues i) (z + s * m))) :=
    Finset.expect_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hlow hz.le
  have hother := mul_nonneg (mul_pos hs hmim).le hAvg0
  nlinarith

omit [Nonempty ι] in
/-- A positive root of the spectral equation solves the normalized matrix trace equation,
including at `η = 0`. -/
theorem certificate_actual_matrix_dyson_of_zero
    (F : Matrix ι ι ℂ) (hF : F.IsHermitian) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 ≤ z.im) (hmim : 0 < m.im)
    (hm : certificateDysonResidual hF.eigenvalues s z m = 0) :
    m = certificateMatrixTrace F (z + s * m) := by
  have ha : 0 < (z + s * m).im := by
    simpa using add_pos_of_nonneg_of_pos hz (mul_pos hs hmim)
  rw [certificateMatrixTrace_eq_average F hF ha.ne']
  exact (certificateDysonResidual_eq_zero_iff hF.eigenvalues s z m).mp hm

universe u

/-- **Regularity certificate.** The constants are chosen from `c, V` before the dimension, the
Hermitian matrix `F`, `E` and the reference `μ` with `Im μ ≥ V` and `|μ| ≤ 1`. If
`‖certificateChi F c E μ‖ ≤ ε`, then on the rectangle `c - s₀ ≤ s ≤ c`, `|x - E| ≤ r`,
`0 ≤ η ≤ 1` the root solves the trace equation with `v₀ ≤ Im m ≤ v₀⁻¹`, the root at `(c, E)` is
within `C ‖certificateChi‖` of `μ`, and the two Loewner bounds between the zero-height
covariance operators hold. -/
theorem certificate_full_uniform {c V : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) :
    ∃ ε r s₀ v₀ C : ℝ, 0 < ε ∧ 0 < r ∧ 0 < s₀ ∧ s₀ < c / 2 ∧
      0 < v₀ ∧ 0 < C ∧
      ∀ (κ : Type u) [Fintype κ] [DecidableEq κ] [Nonempty κ]
        (F : Matrix κ κ ℂ) (hF : F.IsHermitian) (E : ℝ) (μ : ℂ),
        V ≤ μ.im → ‖μ‖ ≤ 1 → ‖certificateChi F c E μ‖ ≤ ε →
        (∀ s : ℝ, c - s₀ ≤ s → s ≤ c →
          ∀ x : ℝ, |x - E| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
          certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η) =
            certificateMatrixTrace F (((x : ℂ) + Complex.I * η) +
              s * certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η)) ∧
          v₀ ≤ (certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η)).im ∧
          (certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η)).im ≤ v₀⁻¹) ∧
        ‖certificateCanonicalDyson hF.eigenvalues c (E : ℂ) - μ‖ ≤
          C * ‖certificateChi F c E μ‖ ∧
        (zeroHeightOperator F E c
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).re
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).im -
          ((1 - C * ‖certificateChi F c E μ‖ : ℝ) : ℂ) •
            zeroHeightOperator F E c μ.re μ.im).PosSemidef ∧
        (((1 + C * ‖certificateChi F c E μ‖ : ℝ) : ℂ) •
            zeroHeightOperator F E c μ.re μ.im -
          zeroHeightOperator F E c
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).re
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).im).PosSemidef := by
  let p := certificateLocalPlan hc hV
  let α : ℝ := p.r / 2
  let q : ℝ := (1 + 4 / (c * V))⁻¹ ^ 2 * (2 * c)⁻¹
  let v₀ : ℝ := min (3 * V / 4) (min (α * q) (c / 2))
  let C : ℝ := 64 / (c * V ^ 3)
  have hr := p.r_pos
  have hα : 0 < α := by dsimp [α]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hv : 0 < v₀ := by dsimp [v₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨p.ε, p.r, p.s₀, v₀, C, p.ε_pos, p.r_pos, p.s₀_pos,
    by linarith [p.s₀_c], hv, hC, ?_⟩
  intro κ _ _ _ F hF E μ hVμ hμnorm hchi
  have hμ : 0 < μ.im := hV.trans_le hVμ
  have hV1 : V ≤ 1 := hVμ.trans ((Complex.im_le_norm μ).trans hμnorm)
  have hsmall : ‖certificateChi F c E μ‖ ≤ V / 2 := hchi.trans p.ε_V
  have hvlow : v₀ ≤ 3 * V / 4 := min_le_left _ _
  have hvhigh : v₀ ≤ α * q := (min_le_right _ _).trans (min_le_left _ _)
  have hvc : v₀ ≤ c / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hupper : 2 / c ≤ v₀⁻¹ := by
    have hh := inv_anti₀ hv hvc
    convert hh using 1
    field_simp [hc.ne']
  refine ⟨?_, ?_⟩
  · intro s hslo hshi x hx η hη hη1
    let z : ℂ := (x : ℂ) + Complex.I * η
    have hz : z.im = η := by simp [z]
    have hs : 0 < s := by linarith [p.s₀_c]
    have hsHalf : c / 2 ≤ s := by linarith [p.s₀_c]
    have hex : ∃ m : ℂ, 0 < m.im ∧
        certificateDysonResidual hF.eigenvalues s z m = 0 ∧ v₀ ≤ m.im := by
      by_cases hlocal : η ≤ p.r
      · obtain ⟨hshift, hsc⟩ := certificate_local_rectangle_shift p hμnorm hslo hshi hx hη hlocal
        obtain ⟨m, him, hmzero, _, _⟩ := certificate_uniform_local_zero F hF hc hV hVμ p hchi
          hs.le (hshi.trans hc1.le) hshift hsc
        exact ⟨m, (by linarith : 0 < m.im), hmzero, hvlow.trans him⟩
      · have hηpos : 0 < η := by linarith [p.r_pos]
        have hηα : α ≤ η := by dsimp [α]; linarith
        obtain ⟨m, hmim, hmzero⟩ := certificate_positive_height_zero_exists hF.eigenvalues
          hc hc1 hα hs hshi hηα hη1
        have hzE : ‖z - (E : ℂ)‖ ≤ 2 := by
          have heq : z - (E : ℂ) = ((x - E : ℝ) : ℂ) + Complex.I * η := by
            dsimp [z]; push_cast; ring
          rw [heq]
          calc
            _ ≤ ‖((x - E : ℝ) : ℂ)‖ + ‖Complex.I * η‖ := norm_add_le _ _
            _ = |x - E| + η := by
              rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hη]
            _ ≤ 2 := by linarith [p.r_one]
        have hlow := certificate_uniform_positive_height_lower F hF hc hc1 hV hVμ hμnorm hsmall
          hs (hshi.trans hc1.le) (by simpa only [hz] using hηpos) hzE hmim hmzero
        have hαq : α * q ≤ m.im := by
          have hαη := mul_le_mul_of_nonneg_right hηα hq.le
          exact hαη.trans (by simpa only [hz, q, mul_assoc] using hlow)
        exact ⟨m, hmim, hmzero, hvhigh.trans hαq⟩
    obtain ⟨m, hmim, hmzero, hmlow⟩ := hex
    have hcanonical := certificateCanonicalDyson_eq hF.eigenvalues hs
      (by simpa only [hz] using hη) hmim hmzero
    change certificateCanonicalDyson hF.eigenvalues s z =
        certificateMatrixTrace F (z + s * certificateCanonicalDyson hF.eigenvalues s z) ∧
      v₀ ≤ (certificateCanonicalDyson hF.eigenvalues s z).im ∧
      (certificateCanonicalDyson hF.eigenvalues s z).im ≤ v₀⁻¹
    rw [hcanonical]
    exact ⟨certificate_actual_matrix_dyson_of_zero F hF hs (by simpa only [hz] using hη) hmim hmzero,
      hmlow, (certificate_dyson_im_upper hF.eigenvalues hc hc1 hsHalf
        (by simpa only [hz] using hη) hmim hmzero).trans hupper⟩
  · obtain ⟨m, him, hmzero, _, hmdist⟩ := certificate_chi_only_reference_zero F hF hc hc1 hV hVμ hchi
    have hmim : 0 < m.im := by linarith
    have hcanonical := certificateCanonicalDyson_eq hF.eigenvalues hc (by simp) hmim hmzero
    have hCdom : 8 / (c * V ^ 2) ≤ C := by
      dsimp [C]
      rw [div_le_div_iff₀ (by positivity : 0 < c * V ^ 2) (by positivity : 0 < c * V ^ 3)]
      have hbase : 8 * V ≤ 64 := by linarith
      nlinarith [mul_nonneg (mul_pos hc (sq_pos_of_pos hV)).le (show 0 ≤ 64 - 8 * V by linarith)]
    have hdistC := hmdist.trans (mul_le_mul_of_nonneg_right hCdom (norm_nonneg _))
    let e : ℝ := 8 * ‖certificateChi F c E μ‖ / (c * V ^ 3)
    have he : 0 ≤ e := by dsimp [e]; positivity
    have hχ64 : ‖certificateChi F c E μ‖ ≤ c * V ^ 3 / 64 := by
      have hp := hchi.trans p.ε_res
      rw [p.k_eq] at hp
      have hmul := mul_le_mul_of_nonneg_left p.ρ_V (by positivity : 0 ≤ c * V ^ 2 / 16)
      nlinarith
    have he8 : e ≤ 1 / 8 := by
      dsimp [e]
      rw [div_le_iff₀ (by positivity : 0 < c * V ^ 3)]
      nlinarith
    have hemu : ‖m - μ‖ ≤ e * μ.im := by
      have heV : 8 / (c * V ^ 2) * ‖certificateChi F c E μ‖ = e * V := by
        dsimp [e]; field_simp [hc.ne', hV.ne']
      rw [heV] at hmdist
      exact hmdist.trans (mul_le_mul_of_nonneg_left hVμ he)
    have hcov := certificate_covariance_symmetric F hF (E := E) hc hμ he (by linarith) hemu
    have heC : 8 * e = C * ‖certificateChi F c E μ‖ := by
      dsimp [e, C]; field_simp [hc.ne', hV.ne']; ring
    rw [heC] at hcov
    rw [hcanonical]
    exact ⟨hdistC, hcov.1, hcov.2⟩

/-- The semicircle reference `(-E + i√(4 - E²))/2`. -/
def certificateSemicircleReference (E : ℝ) : ℂ :=
  (-(E : ℂ) + Complex.I * (Real.sqrt (4 - E ^ 2) : ℂ)) / 2

/-- On the compact bulk `|E| ≤ 2 - θ`, the semicircle reference has imaginary part bounded below
uniformly and norm one. -/
theorem certificate_semicircle_compact_bulk {θ E : ℝ}
    (hθ : 0 < θ) (hθ2 : θ ≤ 2) (hE : |E| ≤ 2 - θ) :
    0 < Real.sqrt (θ * (4 - θ)) / 2 ∧
      Real.sqrt (θ * (4 - θ)) / 2 ≤ (certificateSemicircleReference E).im ∧
      ‖certificateSemicircleReference E‖ = 1 := by
  have hθrad : 0 < θ * (4 - θ) := mul_pos hθ (by linarith)
  have hElo := (abs_le.mp hE).1
  have hEhi := (abs_le.mp hE).2
  have hprod : 0 ≤ (2 - θ - E) * (2 - θ + E) :=
    mul_nonneg (by linarith) (by linarith)
  have hrad : θ * (4 - θ) ≤ 4 - E ^ 2 := by nlinarith
  have hradpos : 0 < 4 - E ^ 2 := hθrad.trans_le hrad
  have him : (certificateSemicircleReference E).im = Real.sqrt (4 - E ^ 2) / 2 := by
    simp [certificateSemicircleReference]
  have hre : (certificateSemicircleReference E).re = -E / 2 := by
    simp [certificateSemicircleReference]
  refine ⟨div_pos (Real.sqrt_pos.mpr hθrad) (by norm_num), ?_, ?_⟩
  · rw [him]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hrad) (by norm_num)
  · have hsq : Complex.normSq (certificateSemicircleReference E) = 1 := by
      rw [Complex.normSq_apply, hre, him]
      nlinarith [Real.sq_sqrt hradpos.le]
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg (certificateSemicircleReference E)]

/-- **Regularity certificate, semicircle reference**, uniformly on the compact bulk interval
`|E| ≤ 2 - θ` with `0 < θ ≤ 2` and fixed `0 < c < 1`. Every constant is chosen before the
dimension, `F` and `E`; `χ` is the normalized resolvent trace minus `(-E + i√(4 - E²))/2`. The
conclusions are those of `certificate_full_uniform`. -/
theorem certificate_semicircle_full {c θ : ℝ}
    (hc : 0 < c) (hc1 : c < 1) (hθ : 0 < θ) (hθ2 : θ ≤ 2) :
    ∃ ε r s₀ v₀ C : ℝ, 0 < ε ∧ 0 < r ∧ 0 < s₀ ∧ s₀ < c / 2 ∧
      0 < v₀ ∧ 0 < C ∧
      ∀ (κ : Type u) [Fintype κ] [DecidableEq κ] [Nonempty κ]
        (F : Matrix κ κ ℂ) (hF : F.IsHermitian) (E : ℝ),
        |E| ≤ 2 - θ →
        ‖certificateChi F c E (certificateSemicircleReference E)‖ ≤ ε →
        (∀ s : ℝ, c - s₀ ≤ s → s ≤ c →
          ∀ x : ℝ, |x - E| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
          certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η) =
            certificateMatrixTrace F (((x : ℂ) + Complex.I * η) +
              s * certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η)) ∧
          v₀ ≤ (certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η)).im ∧
          (certificateCanonicalDyson hF.eigenvalues s ((x : ℂ) + Complex.I * η)).im ≤ v₀⁻¹) ∧
        ‖certificateCanonicalDyson hF.eigenvalues c (E : ℂ) -
          certificateSemicircleReference E‖ ≤
          C * ‖certificateChi F c E (certificateSemicircleReference E)‖ ∧
        (zeroHeightOperator F E c
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).re
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).im -
          ((1 - C * ‖certificateChi F c E (certificateSemicircleReference E)‖ : ℝ) : ℂ) •
            zeroHeightOperator F E c (certificateSemicircleReference E).re
              (certificateSemicircleReference E).im).PosSemidef ∧
        (((1 + C * ‖certificateChi F c E (certificateSemicircleReference E)‖ : ℝ) : ℂ) •
            zeroHeightOperator F E c (certificateSemicircleReference E).re
              (certificateSemicircleReference E).im -
          zeroHeightOperator F E c
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).re
            (certificateCanonicalDyson hF.eigenvalues c (E : ℂ)).im).PosSemidef := by
  let V : ℝ := Real.sqrt (θ * (4 - θ)) / 2
  have hV : 0 < V := by
    dsimp [V]
    exact div_pos (Real.sqrt_pos.mpr (mul_pos hθ (by linarith))) (by norm_num)
  obtain ⟨ε, r, s₀, v₀, C, hε, hr, hs₀, hs₀c, hv₀, hC, hall⟩ :=
    certificate_full_uniform.{u} hc hc1 hV
  refine ⟨ε, r, s₀, v₀, C, hε, hr, hs₀, hs₀c, hv₀, hC, ?_⟩
  intro κ _ _ _ F hF E hE hchi
  have hbulk := certificate_semicircle_compact_bulk hθ hθ2 hE
  exact hall κ F hF E (certificateSemicircleReference E) hbulk.2.1 hbulk.2.2.le hchi

end BlockBand.Palm
