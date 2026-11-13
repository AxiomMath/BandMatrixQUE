module

public import BlockBand.Endpoints.Poisson.AbsorberLog
public import BlockBand.Transmission.PositiveResolvent
public import BlockBand.DeterminantScore.PointwiseJacobi

/-!
# Absorber monotonicity and the log-determinant path

Domain: a finite index type `ι`, complex matrices `A` Hermitian, absorbers
`Γ, P` positive semidefinite, a regulator `η > 0` (or `η → 0` with explicit
nonvanishing determinants), path parameters `s ≥ 0`. `‖·‖` is the complex
absolute value of a determinant; integrals in `s` are Lebesgue interval
integrals. All statements are exact and deterministic. Steps 2 and 3 are those of the proof of
the finite-log recovery lemma.

- Step 2: `hasDerivAt_absorberLogPath`, `absorberLogPath_deriv_nonneg`,
  `monotoneOn_absorberLogPath`: `s ↦ log ‖det(A + i(Γ + sP + ηI))‖` has derivative
  `-Im Tr(P (A + i(Γ + sP + ηI))⁻¹) ≥ 0` on `[0, ∞)`;
  `log_norm_det_ratio_nonneg_le_one` (unregulated, `det A ≠ 0`, `0 ≤ Q ≤ I`) and
  `positiveLogStatistic_nonneg`, `positiveLogStatistic_le_one`,
  `positiveLogStatistic_absorberProjector_nonneg_le_one`
  (`0 ≤ 𝓡_δ^C ≤ 𝓡_δ^I` for `f ≥ 0`).
- Step 3: `regulated_log_det_full_sub_partial_eq_integral` (FTC along the
  path on `B = C^c`), `tendsto_regulated_log_det_full_sub_partial` (regulator
  removal), `monotoneOn_log_norm_det_regulator` (monotone in `η`).

The derivative is computed with
`BlockBand.DeterminantScore.hasDerivAt_log_normSq_det_realAffineLine` and the positive-resolvent
facts of `BlockBand.Transmission.PositiveResolvent`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Set
open scoped ComplexOrder Matrix Topology
open BlockBand.Transmission (matrixImaginaryPart matrixImaginaryPart_add_I_smul
  isUnit_det_add_I_smul_add_pos_regulator neg_matrixImaginaryPart_nonsing_inv_posSemidef)

variable {ι : Type*} [Fintype ι]

/-!
### Jacobi score sign
-/

/-- The real trace pairing of two positive-semidefinite complex matrices is
nonnegative (no commutativity). -/
theorem re_trace_mul_nonneg_of_posSemidef
    {P Q : Matrix ι ι ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace.re := by
  rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hQ
  obtain ⟨m, v, rfl⟩ := hQ
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _hj
  rw [dotProduct_comm]
  exact hP.re_dotProduct_nonneg (v j)

/-- Pairing a Hermitian `Q` with `-Im M` gives `-Im Tr(M Q)` (any square `M`). -/
theorem re_trace_neg_matrixImaginaryPart_mul
    (M Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) :
    ((-matrixImaginaryPart M) * Q).trace.re = -(M * Q).trace.im := by
  rw [neg_mul, Matrix.trace_neg, Complex.neg_re, matrixImaginaryPart,
    Matrix.smul_mul, Matrix.trace_smul]
  have hstar : (Mᴴ * Q).trace = star ((M * Q).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hQ.eq,
      Matrix.trace_mul_comm]
  rw [Matrix.sub_mul, Matrix.trace_sub, hstar]
  simp
  ring

variable [DecidableEq ι]

/-- The real Jacobi score in the direction `iP` is `-Im Tr(P M⁻¹)`, for every
square complex `M` and `P`. -/
theorem re_trace_inv_mul_I_smul (M P : Matrix ι ι ℂ) :
    (M⁻¹ * (Complex.I • P)).trace.re = -(P * M⁻¹).trace.im := by
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_comm]
  simp

/-- **Sign in the log-monotonicity bound.** For `A` Hermitian, `Γ, P` positive semidefinite
and `A + iΓ` invertible: `0 ≤ -Im Tr(P (A + iΓ)⁻¹)`. -/
theorem neg_im_trace_mul_inv_nonneg {A Γ P : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hΓ : Γ.PosSemidef) (hP : P.PosSemidef) (hM : IsUnit (A + Complex.I • Γ).det) :
    0 ≤ -(P * (A + Complex.I • Γ)⁻¹).trace.im := by
  have him : (matrixImaginaryPart (A + Complex.I • Γ)).PosSemidef := by
    rwa [matrixImaginaryPart_add_I_smul A Γ hA hΓ.isHermitian]
  have hinv := neg_matrixImaginaryPart_nonsing_inv_posSemidef _ hM him
  have h := re_trace_mul_nonneg_of_posSemidef hinv hP
  rw [re_trace_neg_matrixImaginaryPart_mul _ P hP.isHermitian] at h
  rwa [Matrix.trace_mul_comm] at h

/-- For `A` Hermitian with `det A ≠ 0` and `Γ` positive semidefinite,
`det(A + iΓ) ≠ 0`. -/
theorem det_add_I_smul_ne_zero {A Γ : Matrix ι ι ℂ} (hA : A.IsHermitian) (hA0 : A.det ≠ 0)
    (hΓ : Γ.PosSemidef) : (A + Complex.I • Γ).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hq : star v ⬝ᵥ (A + Complex.I • Γ) *ᵥ v = 0 := by rw [hv, dotProduct_zero]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul] at hq
  have hAim := hA.im_star_dotProduct_mulVec_self v
  have hΓim := hΓ.isHermitian.im_star_dotProduct_mulVec_self v
  have him := congrArg Complex.im hq
  simp only [RCLike.im_to_complex] at hAim hΓim
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, hAim, Complex.zero_im] at him
  have hΓv : star v ⬝ᵥ Γ *ᵥ v = 0 := Complex.ext him hΓim
  have hΓv' : Γ *ᵥ v = 0 := hΓ.dotProduct_mulVec_zero_iff.mp hΓv
  apply hA0
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv0, ?_⟩
  have := hv
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, hΓv', smul_zero, add_zero] at this
  exact this

/-!
### Step 2: derivative and monotonicity along the regulated path
-/

/-- `log ‖z‖ = ½ log (normSq z)` for every complex `z`. -/
theorem log_norm_eq_half_log_normSq (z : ℂ) :
    Real.log ‖z‖ = (1 / 2 : ℝ) * Real.log (Complex.normSq z) := by
  rw [← Complex.sq_norm, Real.log_pow]
  push_cast
  ring

/-- Real derivative of `t ↦ log ‖det(M + tQ)‖` at any `s` where `M + sQ` is
invertible: `Re Tr((M + sQ)⁻¹ Q)` (Jacobi). -/
theorem hasDerivAt_log_norm_det_affine (M Q : Matrix ι ι ℂ) (s : ℝ)
    (hs : IsUnit (M + (s : ℂ) • Q).det) :
    HasDerivAt (fun t : ℝ => Real.log ‖(M + (t : ℂ) • Q).det‖)
      (((M + (s : ℂ) • Q)⁻¹ * Q).trace.re) s := by
  have h0 := BlockBand.DeterminantScore.hasDerivAt_log_normSq_det_realAffineLine
    (M + (s : ℂ) • Q) Q hs
  have h0' : HasDerivAt
      (fun t : ℝ => Real.log (Complex.normSq ((M + (s : ℂ) • Q + (t : ℂ) • Q).det)))
      (2 * ((M + (s : ℂ) • Q)⁻¹ * Q).trace.re) (s - s) := by
    rwa [sub_self]
  have h1 := (HasDerivAt.comp_sub_const s s h0').const_mul (1 / 2 : ℝ)
  have hmat : ∀ t : ℝ, M + (s : ℂ) • Q + ((t - s : ℝ) : ℂ) • Q = M + (t : ℂ) • Q := by
    intro t
    push_cast
    rw [add_assoc, ← add_smul, add_sub_cancel]
  convert h1 using 1
  · funext t
    rw [hmat t, log_norm_eq_half_log_normSq]
  · ring

/-- The regulated absorbed matrix `A + i(Γ + sP + ηI)`. -/
def regulatedAbsorber (A Γ P : Matrix ι ι ℂ) (η s : ℝ) : Matrix ι ι ℂ :=
  A + Complex.I • (Γ + s • P + η • (1 : Matrix ι ι ℂ))

/-- The regulated log-determinant path `s ↦ log ‖det(A + i(Γ + sP + ηI))‖`. -/
def absorberLogPath (A Γ P : Matrix ι ι ℂ) (η s : ℝ) : ℝ :=
  Real.log ‖(regulatedAbsorber A Γ P η s).det‖

/-- For `A` Hermitian, `Γ, P` positive semidefinite, `η > 0` and `s ≥ 0`, the
regulated absorbed matrix is invertible. -/
theorem isUnit_det_regulatedAbsorber {A Γ P : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hΓ : Γ.PosSemidef) (hP : P.PosSemidef) {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) :
    IsUnit (regulatedAbsorber A Γ P η s).det :=
  isUnit_det_add_I_smul_add_pos_regulator hA (hΓ.add (hP.smul hs)) hη

/-- **Log-monotonicity bound, derivative.** For `A` Hermitian, `Γ, P` positive
semidefinite, `η > 0` and every `s ≥ 0`, `absorberLogPath A Γ P η` has derivative
`-Im Tr(P (A + i(Γ + sP + ηI))⁻¹)` at `s`. -/
theorem hasDerivAt_absorberLogPath {A Γ P : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hΓ : Γ.PosSemidef) (hP : P.PosSemidef) {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) :
    HasDerivAt (absorberLogPath A Γ P η)
      (-(P * (regulatedAbsorber A Γ P η s)⁻¹).trace.im) s := by
  have hmat : ∀ t : ℝ, regulatedAbsorber A Γ P η t =
      (A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ))) + (t : ℂ) • (Complex.I • P) := by
    intro t
    ext i j
    simp [regulatedAbsorber]
    ring
  have hu := isUnit_det_regulatedAbsorber hA hΓ hP hη hs
  rw [hmat] at hu
  have h := hasDerivAt_log_norm_det_affine _ _ s hu
  rw [re_trace_inv_mul_I_smul, ← hmat] at h
  convert h using 1
  funext t
  rw [absorberLogPath, hmat]

/-- **Log-monotonicity bound, sign.** Under the hypotheses of
`hasDerivAt_absorberLogPath`, `0 ≤ -Im Tr(P (A + i(Γ + sP + ηI))⁻¹)`. -/
theorem absorberLogPath_deriv_nonneg {A Γ P : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hΓ : Γ.PosSemidef) (hP : P.PosSemidef) {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) :
    0 ≤ -(P * (regulatedAbsorber A Γ P η s)⁻¹).trace.im :=
  neg_im_trace_mul_inv_nonneg hA
    ((hΓ.add (hP.smul hs)).add (Matrix.PosSemidef.one.smul hη.le)) hP
    (isUnit_det_regulatedAbsorber hA hΓ hP hη hs)

/-- **Log-monotonicity bound, monotonicity.** For `A` Hermitian, `Γ, P` positive
semidefinite and `η > 0`, `s ↦ log ‖det(A + i(Γ + sP + ηI))‖` is monotone on
`[0, ∞)`. -/
theorem monotoneOn_absorberLogPath {A Γ P : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hΓ : Γ.PosSemidef) (hP : P.PosSemidef) {η : ℝ} (hη : 0 < η) :
    MonotoneOn (absorberLogPath A Γ P η) (Ici 0) := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (absorberLogPath A Γ P η)
      (-(P * (regulatedAbsorber A Γ P η s)⁻¹).trace.im) s :=
    fun s hs => hasDerivAt_absorberLogPath hA hΓ hP hη hs
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact (hd s (le_of_lt hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    rw [(hd s (le_of_lt hs)).deriv]
    exact absorberLogPath_deriv_nonneg hA hΓ hP hη (le_of_lt hs)

/-- **Regulated `0 ≤ Q ≤ I` comparison.** For `A` Hermitian, `Q` and `1 - Q`
positive semidefinite, `η > 0` and `a ≥ 0`:
`log ‖det(A + iηI)‖ ≤ log ‖det(A + i(aQ + ηI))‖ ≤ log ‖det(A + i(aI + ηI))‖`. -/
theorem regulated_log_norm_det_le_partial_le_full {A Q : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef) {η a : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) :
    Real.log ‖(A + Complex.I • (η • (1 : Matrix ι ι ℂ))).det‖ ≤
        Real.log ‖(A + Complex.I • (a • Q + η • (1 : Matrix ι ι ℂ))).det‖ ∧
      Real.log ‖(A + Complex.I • (a • Q + η • (1 : Matrix ι ι ℂ))).det‖ ≤
        Real.log ‖(A + Complex.I • (a • (1 : Matrix ι ι ℂ) + η • (1 : Matrix ι ι ℂ))).det‖ := by
  have h1 := monotoneOn_absorberLogPath hA Matrix.PosSemidef.zero hQ hη
    (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using ha) ha
  have h2 := monotoneOn_absorberLogPath hA (hQ.smul ha) hIQ hη
    (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using ha) ha
  simp only [absorberLogPath, regulatedAbsorber, zero_smul, add_zero, zero_add] at h1 h2
  refine ⟨h1, ?_⟩
  convert h2 using 5
  rw [smul_sub, add_sub_cancel]

/-- Regulator continuity: if `det M ≠ 0` and `D` is any complex matrix, then
`log ‖det(M + ηD)‖ → log ‖det M‖` as the real `η → 0`. -/
theorem tendsto_log_norm_det_add_smul (M D : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    Tendsto (fun η : ℝ => Real.log ‖(M + (η : ℂ) • D).det‖) (𝓝 0)
      (𝓝 (Real.log ‖M.det‖)) := by
  have hc : Continuous fun η : ℝ => (M + (η : ℂ) • D).det :=
    (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).matrix_det
  have h0 : (M + ((0 : ℝ) : ℂ) • D).det = M.det := by simp
  have hcont : ContinuousAt (fun η : ℝ => Real.log ‖(M + (η : ℂ) • D).det‖) 0 :=
    hc.norm.continuousAt.log (by rw [h0]; exact norm_ne_zero_iff.mpr hM)
  simpa [h0] using hcont.tendsto

/-- **Unregulated `0 ≤ Q ≤ I` comparison (Step 2, pointwise).** For `A`
Hermitian with `det A ≠ 0`, `Q` and `1 - Q` positive semidefinite and `a ≥ 0`:
`0 ≤ log (‖det(A + iaQ)‖/‖det A‖) ≤ log (‖det(A + iaI)‖/‖det A‖)`. -/
theorem log_norm_det_ratio_nonneg_le_one {A Q : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hA0 : A.det ≠ 0) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ Real.log (‖(A + Complex.I • (a • Q)).det‖ / ‖A.det‖) ∧
      Real.log (‖(A + Complex.I • (a • Q)).det‖ / ‖A.det‖) ≤
        Real.log (‖(A + Complex.I • (a • (1 : Matrix ι ι ℂ))).det‖ / ‖A.det‖) := by
  have hQ0 := det_add_I_smul_ne_zero hA hA0 (hQ.smul ha)
  have hI0 := det_add_I_smul_ne_zero hA hA0 (Matrix.PosSemidef.one.smul ha)
  have hmat : ∀ (R : Matrix ι ι ℂ) (η : ℝ),
      A + Complex.I • (R + η • (1 : Matrix ι ι ℂ)) =
        (A + Complex.I • R) + (η : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)) := by
    intro R η
    ext i j
    simp
    ring
  have hlimQ := tendsto_log_norm_det_add_smul _ (Complex.I • (1 : Matrix ι ι ℂ)) hQ0
  have hlimI := tendsto_log_norm_det_add_smul _ (Complex.I • (1 : Matrix ι ι ℂ)) hI0
  have hlim0 := tendsto_log_norm_det_add_smul _ (Complex.I • (1 : Matrix ι ι ℂ)) hA0
  have hev : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      Real.log ‖(A + (η : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ))).det‖ ≤
          Real.log ‖((A + Complex.I • (a • Q)) +
            (η : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ))).det‖ ∧
        Real.log ‖((A + Complex.I • (a • Q)) +
            (η : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ))).det‖ ≤
          Real.log ‖((A + Complex.I • (a • (1 : Matrix ι ι ℂ))) +
            (η : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ))).det‖ := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have h := regulated_log_norm_det_le_partial_le_full hA hQ hIQ (a := a) hη ha
    rw [hmat, hmat] at h
    have h0 : A + Complex.I • (η • (1 : Matrix ι ι ℂ)) =
        A + (η : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)) := by
      ext i j
      simp
      ring
    rwa [h0] at h
  have l0 := hlim0.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have lQ := hlimQ.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have lI := hlimI.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hle1 := le_of_tendsto_of_tendsto l0 lQ (hev.mono fun _ h => h.1)
  have hle2 := le_of_tendsto_of_tendsto lQ lI (hev.mono fun _ h => h.2)
  have hn0 : 0 < ‖A.det‖ := norm_pos_iff.mpr hA0
  rw [Real.log_div (norm_ne_zero_iff.mpr hQ0) hn0.ne',
    Real.log_div (norm_ne_zero_iff.mpr hI0) hn0.ne']
  constructor <;> linarith

/-!
### Step 2 for the positive log statistic
-/

/-- `absorbedShift H E Λ x a P = A_x + i(aP)` with `A_x = absorbedShift H E Λ x 0 1
= H - (E + x/Λ)`; for every square `H, P` and real `E, Λ, x, a`. -/
theorem absorbedShift_eq_add_I_smul (H P : Matrix ι ι ℂ) (E Λ x a : ℝ) :
    absorbedShift H E Λ x a P = absorbedShift H E Λ x 0 1 + Complex.I • (a • P) := by
  ext i j
  simp [absorbedShift]
  ring

/-- Regulated `absorbedShift`: for every square `H, P` and real `E, Λ, x, a, η`,
`absorbedShift H E Λ x a P + iηI = A_x + i(aP + ηI)`, `A_x = absorbedShift H E Λ x 0 1`. -/
theorem absorbedShift_add_regulator (H P : Matrix ι ι ℂ) (E Λ x a η : ℝ) :
    absorbedShift H E Λ x a P + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) =
      absorbedShift H E Λ x 0 1 + Complex.I • (a • P + η • (1 : Matrix ι ι ℂ)) := by
  ext i j
  simp [absorbedShift]
  ring

/-- For Hermitian `H` and real `E, Λ, x`, `absorbedShift H E Λ x 0 1` is Hermitian. -/
theorem absorbedShift_zero_one_isHermitian {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (E Λ x : ℝ) : (absorbedShift H E Λ x 0 1).IsHermitian := by
  unfold absorbedShift
  rw [Complex.ofReal_zero, zero_mul, zero_smul, add_zero]
  refine hH.sub ?_
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal]

/-- **Step 2, pointwise in `x`.** For Hermitian `H`, real `E`, `Λ > 0`, `δ ≥ 0`, `Q`
and `1 - Q` positive semidefinite, and `x ≠ Λ(λ_α - E)` for all increasing
eigenvalues:
`0 ≤ log (‖det(H - E - x/Λ + iδQ/Λ)‖/‖det(H - E - x/Λ)‖)
   ≤ log (‖det(H - E - x/Λ + iδ/Λ)‖/‖det(H - E - x/Λ)‖)`. -/
theorem log_det_ratio_absorbedShift_nonneg_le_one {H Q : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E : ℝ) {Λ δ x : ℝ} (hΛ : 0 < Λ) (hδ : 0 ≤ δ)
    (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef)
    (hx : ∀ α, x ≠ Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E)) :
    0 ≤ Real.log (‖(absorbedShift H E Λ x (δ / Λ) Q).det‖ /
        ‖(absorbedShift H E Λ x 0 Q).det‖) ∧
      Real.log (‖(absorbedShift H E Λ x (δ / Λ) Q).det‖ /
          ‖(absorbedShift H E Λ x 0 Q).det‖) ≤
        Real.log (‖(absorbedShift H E Λ x (δ / Λ) 1).det‖ /
          ‖(absorbedShift H E Λ x 0 1).det‖) := by
  have h0 : absorbedShift H E Λ x 0 Q = absorbedShift H E Λ x 0 1 := by
    rw [absorbedShift_eq_add_I_smul H Q, zero_smul, smul_zero, add_zero]
  rw [h0, absorbedShift_eq_add_I_smul H Q E Λ x (δ / Λ),
    absorbedShift_eq_add_I_smul H 1 E Λ x (δ / Λ)]
  exact log_norm_det_ratio_nonneg_le_one (absorbedShift_zero_one_isHermitian hH E Λ x)
    (det_absorbedShift_zero_ne_zero hH E hΛ.ne' hx) hQ hIQ (div_nonneg hδ hΛ.le)

/-- **Step 2, `0 ≤ 𝓡_δ^C(H; f)`.** For Hermitian `H`, real `E`, `Λ > 0`, `δ > 0`,
`Q` and `1 - Q` positive semidefinite, and every `f ≥ 0`:
`0 ≤ positiveLogStatistic H E Λ δ Q f`. -/
theorem positiveLogStatistic_nonneg {H Q : Matrix ι ι ℂ} (hH : H.IsHermitian) (E : ℝ)
    {Λ δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ positiveLogStatistic H E Λ δ Q f := by
  unfold positiveLogStatistic
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg_of_ae ?_)
  filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
  exact mul_nonneg (hf0 x)
    (log_det_ratio_absorbedShift_nonneg_le_one hH E hΛ hδ.le hQ hIQ hx).1

/-- **Step 2, `𝓡_δ^C(H; f) ≤ 𝓡_δ^I(H; f)`.** For Hermitian `H`, real `E`, `Λ > 0`,
`δ > 0`, `Q` and `1 - Q` positive semidefinite, and `f ≥ 0` continuous with
compact support: `positiveLogStatistic H E Λ δ Q f ≤ positiveLogStatistic H E Λ δ 1 f`. -/
theorem positiveLogStatistic_le_one {H Q : Matrix ι ι ℂ} (hH : H.IsHermitian) (E : ℝ)
    {Λ δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef)
    {f : ℝ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    positiveLogStatistic H E Λ δ Q f ≤ positiveLogStatistic H E Λ δ 1 f := by
  unfold positiveLogStatistic
  refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg ?_
    (integrable_positiveLogIntegrand_one hH E hΛ.ne' hδ.ne' hf hfs) ?_)
    (inv_nonneg.mpr (by positivity))
  · filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
    exact mul_nonneg (hf0 x)
      (log_det_ratio_absorbedShift_nonneg_le_one hH E hΛ hδ.le hQ hIQ hx).1
  · filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
    exact mul_le_mul_of_nonneg_left
      (log_det_ratio_absorbedShift_nonneg_le_one hH E hΛ hδ.le hQ hIQ hx).2 (hf0 x)

/-- The diagonal absorber projector `P_C = diag(1_{i ∈ C})` of a set `C` of indices. -/
def absorberProjector (C : Finset ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if i ∈ C then 1 else 0

omit [Fintype ι] in
/-- For every `C : Finset ι`, `P_C` is positive semidefinite. -/
theorem absorberProjector_posSemidef (C : Finset ι) : (absorberProjector C).PosSemidef := by
  unfold absorberProjector
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  split_ifs <;> simp

/-- For every `C : Finset ι`, `1 - P_C = P_{Cᶜ}` (the projector `P_B`, `B = C^c`). -/
theorem one_sub_absorberProjector (C : Finset ι) :
    1 - absorberProjector C = absorberProjector Cᶜ := by
  ext i j
  by_cases h : i = j
  · subst h
    by_cases hi : i ∈ C <;> simp [absorberProjector, hi]
  · simp [absorberProjector, h]

/-- **Step 2 for diagonal projectors.** For Hermitian `H`, real `E`, `Λ > 0`, `δ > 0`,
every `C : Finset ι` and `f ≥ 0` continuous with compact support:
`0 ≤ 𝓡_δ^C(H; f) ≤ 𝓡_δ^I(H; f)` with `P_C = absorberProjector C`. -/
theorem positiveLogStatistic_absorberProjector_nonneg_le_one {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E : ℝ) {Λ δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (C : Finset ι)
    {f : ℝ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ positiveLogStatistic H E Λ δ (absorberProjector C) f ∧
      positiveLogStatistic H E Λ δ (absorberProjector C) f ≤
        positiveLogStatistic H E Λ δ 1 f := by
  have hIQ : (1 - absorberProjector C).PosSemidef := by
    rw [one_sub_absorberProjector]
    exact absorberProjector_posSemidef _
  exact ⟨positiveLogStatistic_nonneg hH E hΛ hδ (absorberProjector_posSemidef C) hIQ hf0,
    positiveLogStatistic_le_one hH E hΛ hδ (absorberProjector_posSemidef C) hIQ hf hfs hf0⟩

/-!
### Step 3: the path on the missing blocks
-/

/-- **Step 3, regulated path identity.** For `A` Hermitian, `Q` (`= P_C`) and
`1 - Q` (`= P_B`) positive semidefinite, `η > 0` and `a ≥ 0`:
`log ‖det(A + i(aI + ηI))‖ - log ‖det(A + i(aQ + ηI))‖ =
 ∫_0^a -Im Tr((1 - Q)(A + i(aQ + s(1 - Q) + ηI))⁻¹) ds`; the integrand is `≥ 0`
(`absorberLogPath_deriv_nonneg`) and interval integrable. -/
theorem regulated_log_det_full_sub_partial_eq_integral {A Q : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef) {η a : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) :
    Real.log ‖(A + Complex.I • (a • (1 : Matrix ι ι ℂ) + η • (1 : Matrix ι ι ℂ))).det‖ -
        Real.log ‖(A + Complex.I • (a • Q + η • (1 : Matrix ι ι ℂ))).det‖ =
      ∫ s in (0 : ℝ)..a, -((1 - Q) *
        (A + Complex.I • (a • Q + s • (1 - Q) + η • (1 : Matrix ι ι ℂ)))⁻¹).trace.im := by
  have hd : ∀ s ∈ uIcc 0 a, HasDerivAt (absorberLogPath A (a • Q) (1 - Q) η)
      (-((1 - Q) * (regulatedAbsorber A (a • Q) (1 - Q) η s)⁻¹).trace.im) s := by
    intro s hs
    rw [uIcc_of_le ha] at hs
    exact hasDerivAt_absorberLogPath hA (hQ.smul ha) hIQ hη hs.1
  have hint : IntervalIntegrable
      (fun s => -((1 - Q) * (regulatedAbsorber A (a • Q) (1 - Q) η s)⁻¹).trace.im)
      volume 0 a := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (g := absorberLogPath A (a • Q) (1 - Q) η)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [min_eq_left ha, max_eq_right ha] at hs
      exact hd s (by rw [uIcc_of_le ha]; exact Ioo_subset_Icc_self hs)
    · intro s hs
      rw [min_eq_left ha, max_eq_right ha] at hs
      exact absorberLogPath_deriv_nonneg hA (hQ.smul ha) hIQ hη hs.1.le
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  unfold regulatedAbsorber at h
  rw [h]
  unfold absorberLogPath regulatedAbsorber
  rw [smul_sub, add_sub_cancel, zero_smul, add_zero]

/-- **Step 3, regulator removal.** For square complex `A, Q` and real `a`, if
`det(A + iaI) ≠ 0` and `det(A + iaQ) ≠ 0`, then as the real `η → 0`,
`log ‖det(A + i(aI + ηI))‖ - log ‖det(A + i(aQ + ηI))‖ →
 log ‖det(A + iaI)‖ - log ‖det(A + iaQ)‖`. (For `A` Hermitian with `det A ≠ 0`,
`Q ⪰ 0` and `a ≥ 0` both hypotheses hold by `det_add_I_smul_ne_zero`.) -/
theorem tendsto_regulated_log_det_full_sub_partial (A Q : Matrix ι ι ℂ) (a : ℝ)
    (hI : (A + Complex.I • (a • (1 : Matrix ι ι ℂ))).det ≠ 0)
    (hQ0 : (A + Complex.I • (a • Q)).det ≠ 0) :
    Tendsto (fun η : ℝ =>
        Real.log ‖(A + Complex.I • (a • (1 : Matrix ι ι ℂ) + η • (1 : Matrix ι ι ℂ))).det‖ -
          Real.log ‖(A + Complex.I • (a • Q + η • (1 : Matrix ι ι ℂ))).det‖) (𝓝 0)
      (𝓝 (Real.log ‖(A + Complex.I • (a • (1 : Matrix ι ι ℂ))).det‖ -
        Real.log ‖(A + Complex.I • (a • Q)).det‖)) := by
  have hmat : ∀ (R : Matrix ι ι ℂ) (η : ℝ),
      A + Complex.I • (R + η • (1 : Matrix ι ι ℂ)) =
        (A + Complex.I • R) + (η : ℂ) • (Complex.I • (1 : Matrix ι ι ℂ)) := by
    intro R η
    ext i j
    simp
    ring
  simp only [hmat]
  exact (tendsto_log_norm_det_add_smul _ _ hI).sub (tendsto_log_norm_det_add_smul _ _ hQ0)

/-- **Monotonicity in the regulator.** For `A` Hermitian and `Γ` positive
semidefinite, `η ↦ log ‖det(A + i(Γ + ηI))‖` is monotone on `(0, ∞)`. -/
theorem monotoneOn_log_norm_det_regulator {A Γ : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hΓ : Γ.PosSemidef) :
    MonotoneOn (fun η : ℝ => Real.log ‖(A + Complex.I • (Γ + η • (1 : Matrix ι ι ℂ))).det‖)
      (Ioi 0) := by
  intro η₁ h₁ η₂ _ h12
  have hm := monotoneOn_absorberLogPath hA hΓ Matrix.PosSemidef.one (mem_Ioi.mp h₁)
    (show (0 : ℝ) ∈ Ici 0 from le_refl 0) (show η₂ - η₁ ∈ Ici 0 from sub_nonneg.mpr h12)
    (sub_nonneg.mpr h12)
  simp only [absorberLogPath, regulatedAbsorber, zero_smul, add_zero] at hm
  rwa [add_assoc, ← add_smul, sub_add_cancel] at hm

end BlockBand.Endpoints
