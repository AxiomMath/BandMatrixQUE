module

public import BlockBand.Endpoints.Poisson.AbsorberLogPath
public import BlockBand.Endpoints.Poisson.LogSmoothing
public import BlockBand.Endpoints.Poisson.BlockModelCount
public import BlockBand.Model.Construction.OrderedSpectrum

/-!
# Physical finite-log recovery

Law and domain: a block model `M : BlockBand.Internal.Contracts.Inputs.BlockModel k W`
(`H = D + ⊕_j A_j` on `Fin k × Fin W`, `n = k` blocks) with `M.IsIndependent c`; `C` a union of
blocks, `B = Cᶜ`, `P_C = blockProjector C`; unfolding `Λ = kWρ`, `ρ > 0` standing for `ρ(E)`;
`f ≥ 0` smooth with compact support; Lebesgue measure on `ℝ`. The hypotheses are
`Inputs.ProjectedWegner` and `Inputs.ConditionalBlockGUECount`.

- `log_det_full_sub_partial_eq_integral`: unregulated Step 3 path identity
  `log ‖det(A + iaI)‖ - log ‖det(A + iaQ)‖ = ∫_0^a -Im Tr((1 - Q)(A + i(aQ + s(1 - Q)))⁻¹) ds`
  for `A` Hermitian invertible, `0 ⪯ Q ⪯ I`, `a ≥ 0`;
- `ofReal_positiveLogStatistic_one_sub_eq_lintegral`: its `x`-integrated form,
  `𝓡_δ^I - 𝓡_δ^Q = (πδ)⁻¹ ∫ f(x) ∫_0^{δ/Λ} (…) ds dx` in `ℝ≥0∞`;
- `positiveLogStatistic_one_eq_sum_logKernel_conv`: Step 1, `𝓡_δ^I = Σ_α (k_δ ⋆ f)(u_α)`;
- `blockProjector_eq_absorberProjector`, `one_sub_blockProjector`, `withAbsorber`,
  `isIndependent_withAbsorber`, `ofReal_projectedDensity_zero_le_liminf`,
  `lintegral_ofReal_partialAbsorberDensity_le`: projected Wegner (clause 3, boundary value)
  at every intermediate deterministic absorber `(δ/Λ)P_C + sP_B`;
- `lintegral_ofReal_positiveLogStatistic_sub_le`: Step 3 in expectation,
  `E(𝓡_δ^I - 𝓡_δ^C) ≤ ‖f‖₁ (C_W/√c) W |B| / Λ` (Tonelli in `(w, x, s)`);
- `integrable_abs_sub_and_integral_le`: assembly; `finiteLogRecovery`: the lemma.

Steps 1–3 are those of the proof of the finite-log recovery lemma. Step 3 is proved without a
regulator. For `x` off the unfolded spectrum the path
`s ↦ log ‖det(A_x + i((δ/Λ)P_C + sP_B))‖` is differentiable on `[0, ∞)`; the `η ↓ 0` limit is
handled by clause 3 of `BlockBand.Internal.Contracts.Inputs.ProjectedWegner` (its `liminf`
form), using
`ofReal(-Im Tr P_B G_0) ≤ liminf_{η↓0} ofReal(-Im Tr P_B G_η)` pointwise.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped ComplexOrder Matrix Topology ENNReal ContDiff

section Deterministic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Step 3 integrand `-Im Tr((1 - Q)(A + i(aQ + s(1 - Q)))⁻¹)` (absorber `a` on `Q = P_C`,
`s` on `1 - Q = P_B`, no regulator). -/
def partialAbsorberDensity (A Q : Matrix ι ι ℂ) (a s : ℝ) : ℝ :=
  -((1 - Q) * (A + Complex.I • (a • Q + s • (1 - Q)))⁻¹).trace.im

/-- For `A` Hermitian with `det A ≠ 0`, `Q` and `1 - Q` positive semidefinite, `a ≥ 0`,
`s ≥ 0`: the matrix `A + i(aQ + s(1 - Q))` is invertible. -/
theorem isUnit_det_partialAbsorber {A Q : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hA0 : A.det ≠ 0) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef) {a s : ℝ} (ha : 0 ≤ a)
    (hs : 0 ≤ s) : IsUnit (A + Complex.I • (a • Q + s • (1 - Q))).det :=
  isUnit_iff_ne_zero.mpr (det_add_I_smul_ne_zero hA hA0 ((hQ.smul ha).add (hIQ.smul hs)))

/-- Under the hypotheses of `isUnit_det_partialAbsorber`, `0 ≤ partialAbsorberDensity A Q a s`
(the log-monotonicity bound). -/
theorem partialAbsorberDensity_nonneg {A Q : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hA0 : A.det ≠ 0) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef) {a s : ℝ} (ha : 0 ≤ a)
    (hs : 0 ≤ s) : 0 ≤ partialAbsorberDensity A Q a s :=
  neg_im_trace_mul_inv_nonneg hA ((hQ.smul ha).add (hIQ.smul hs)) hIQ
    (isUnit_det_partialAbsorber hA hA0 hQ hIQ ha hs)

/-- **Step 3, unregulated path identity.** For `A` Hermitian with `det A ≠ 0`, `Q` and
`1 - Q` positive semidefinite and `a ≥ 0`: `s ↦ partialAbsorberDensity A Q a s` is interval
integrable on `[0, a]` and
`log ‖det(A + iaI)‖ - log ‖det(A + iaQ)‖ = ∫_0^a partialAbsorberDensity A Q a s ds`. -/
theorem log_det_full_sub_partial_eq_integral {A Q : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hA0 : A.det ≠ 0) (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef)
    {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable (partialAbsorberDensity A Q a) volume 0 a ∧
      Real.log ‖(A + Complex.I • (a • (1 : Matrix ι ι ℂ))).det‖ -
          Real.log ‖(A + Complex.I • (a • Q)).det‖ =
        ∫ s in (0 : ℝ)..a, partialAbsorberDensity A Q a s := by
  have hmat : ∀ t : ℝ, A + Complex.I • (a • Q + t • (1 - Q)) =
      (A + Complex.I • (a • Q)) + (t : ℂ) • (Complex.I • (1 - Q)) := by
    intro t
    ext i j
    simp
    ring
  have hd : ∀ s ∈ uIcc 0 a, HasDerivAt
      (fun t : ℝ => Real.log ‖((A + Complex.I • (a • Q)) +
        (t : ℂ) • (Complex.I • (1 - Q))).det‖)
      (partialAbsorberDensity A Q a s) s := by
    intro s hs
    rw [uIcc_of_le ha] at hs
    have hu := isUnit_det_partialAbsorber hA hA0 hQ hIQ ha hs.1
    rw [hmat] at hu
    have h := hasDerivAt_log_norm_det_affine _ _ s hu
    rwa [re_trace_inv_mul_I_smul, ← hmat] at h
  have hint : IntervalIntegrable (partialAbsorberDensity A Q a) volume 0 a := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (g := fun t : ℝ => Real.log ‖((A + Complex.I • (a • Q)) +
        (t : ℂ) • (Complex.I • (1 - Q))).det‖)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [min_eq_left ha, max_eq_right ha] at hs
      exact hd s (by rw [uIcc_of_le ha]; exact Ioo_subset_Icc_self hs)
    · intro s hs
      rw [min_eq_left ha, max_eq_right ha] at hs
      exact partialAbsorberDensity_nonneg hA hA0 hQ hIQ ha hs.1.le
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  rw [← hmat, ← hmat, smul_sub, add_sub_cancel, zero_smul, add_zero]

/-- Matrix inversion `N ↦ N⁻¹` is Borel measurable on square complex matrices. -/
theorem measurable_matrix_inv : Measurable (fun N : Matrix ι ι ℂ => N⁻¹) := by
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).mul
    ((continuous_apply_apply i j).comp continuous_id.matrix_adjugate).measurable

/-- For real `E, Λ, a`, a square `P` and continuous `f`, the integrand
`(H, x) ↦ f(x) log (‖det(H - E - x/Λ + iaP)‖/‖det(H - E - x/Λ)‖)` of
`positiveLogStatistic` is jointly Borel measurable. -/
theorem measurable_positiveLogIntegrand (E Λ a : ℝ) (P : Matrix ι ι ℂ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    Measurable (fun p : Matrix ι ι ℂ × ℝ => f p.2 * Real.log
      (‖(absorbedShift p.1 E Λ p.2 a P).det‖ / ‖(absorbedShift p.1 E Λ p.2 0 P).det‖)) := by
  have hc : ∀ b : ℝ, Continuous (fun p : Matrix ι ι ℂ × ℝ =>
      ‖(absorbedShift p.1 E Λ p.2 b P).det‖) := by
    intro b
    unfold absorbedShift
    fun_prop
  exact (hf.comp continuous_snd).measurable.mul
    (Real.measurable_log.comp ((hc a).measurable.div (hc 0).measurable))

/-- For a measurable random matrix `h`, real `E, Λ, δ`, square `P` and continuous `f`,
`w ↦ positiveLogStatistic (h w) E Λ δ P f` is measurable. -/
theorem measurable_positiveLogStatistic {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → Matrix ι ι ℂ} (hh : Measurable h) (E Λ δ : ℝ) (P : Matrix ι ι ℂ) {f : ℝ → ℝ}
    (hf : Continuous f) : Measurable (fun w => positiveLogStatistic (h w) E Λ δ P f) := by
  unfold positiveLogStatistic
  have hm := (measurable_positiveLogIntegrand E Λ (δ / Λ) P hf).comp
    ((hh.comp measurable_fst).prodMk measurable_snd)
  exact ((hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable).const_mul _

/-- **Step 3, integrated (`ℝ≥0∞` form).** For Hermitian `H`, real `E`, `Λ > 0`, `δ > 0`,
`Q` and `1 - Q` positive semidefinite, and `f ≥ 0` continuous with compact support:
`𝓡_δ^I - 𝓡_δ^Q = (πδ)⁻¹ ∫ f(x) ∫_0^{δ/Λ} -Im Tr((1 - Q) G_s(x)) ds dx`, with
`G_s(x) = (H - E - x/Λ + i((δ/Λ)Q + s(1 - Q)))⁻¹`, as an identity of `ofReal`s and
lower Lebesgue integrals (Lebesgue measure in `x` and in `s ∈ (0, δ/Λ]`). -/
theorem ofReal_positiveLogStatistic_one_sub_eq_lintegral {H Q : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E : ℝ) {Λ δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) (hQ : Q.PosSemidef)
    (hIQ : (1 - Q).PosSemidef) {f : ℝ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (positiveLogStatistic H E Λ δ 1 f - positiveLogStatistic H E Λ δ Q f) =
      ENNReal.ofReal ((Real.pi * δ)⁻¹) * ∫⁻ x, ENNReal.ofReal (f x) *
        ∫⁻ s in Ioc 0 (δ / Λ), ENNReal.ofReal
          (partialAbsorberDensity (absorbedShift H E Λ x 0 1) Q (δ / Λ) s) := by
  have ha : 0 ≤ δ / Λ := div_nonneg hδ.le hΛ.le
  set F1 : ℝ → ℝ := fun x => f x * Real.log
    (‖(absorbedShift H E Λ x (δ / Λ) 1).det‖ / ‖(absorbedShift H E Λ x 0 1).det‖) with hF1d
  set FQ : ℝ → ℝ := fun x => f x * Real.log
    (‖(absorbedShift H E Λ x (δ / Λ) Q).det‖ / ‖(absorbedShift H E Λ x 0 Q).det‖) with hFQd
  have hF1 : Integrable F1 := integrable_positiveLogIntegrand_one hH E hΛ.ne' hδ.ne' hf hfs
  have hFQm : Measurable FQ := (measurable_positiveLogIntegrand E Λ (δ / Λ) Q hf).comp
    (measurable_const.prodMk measurable_id)
  have hle := fun x (hx : ∀ α, x ≠ Λ *
      (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E)) =>
    log_det_ratio_absorbedShift_nonneg_le_one hH E hΛ hδ.le hQ hIQ hx
  have hFQ : Integrable FQ := by
    refine hF1.mono' hFQm.aestronglyMeasurable ?_
    filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 x) (hle x hx).1)]
    exact mul_le_mul_of_nonneg_left (hle x hx).2 (hf0 x)
  have hsub : positiveLogStatistic H E Λ δ 1 f - positiveLogStatistic H E Λ δ Q f =
      (Real.pi * δ)⁻¹ * ∫ x, (F1 x - FQ x) := by
    unfold positiveLogStatistic
    rw [← mul_sub, integral_sub hF1 hFQ]
  have hnn : 0 ≤ᵐ[volume] fun x => F1 x - FQ x := by
    filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left (hle x hx).2 (hf0 x))
  rw [hsub, ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity)),
    ofReal_integral_eq_lintegral_ofReal (f := fun x => F1 x - FQ x) (hF1.sub hFQ) hnn]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ne_unfoldedEigenvalue hH E Λ] with x hx
  set A := absorbedShift H E Λ x 0 1 with hAd
  have hAh : A.IsHermitian := absorbedShift_zero_one_isHermitian hH E Λ x
  have hA0 : A.det ≠ 0 := det_absorbedShift_zero_ne_zero hH E hΛ.ne' hx
  have h0 : absorbedShift H E Λ x 0 Q = A := by
    rw [absorbedShift_eq_add_I_smul H Q, zero_smul, smul_zero, add_zero]
  obtain ⟨hint, hftc⟩ := log_det_full_sub_partial_eq_integral hAh hA0 hQ hIQ ha
  have hnA : ‖A.det‖ ≠ 0 := norm_ne_zero_iff.mpr hA0
  have hn1 : ‖(A + Complex.I • ((δ / Λ) • (1 : Matrix ι ι ℂ))).det‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (det_add_I_smul_ne_zero hAh hA0 (Matrix.PosSemidef.one.smul ha))
  have hnQ : ‖(A + Complex.I • ((δ / Λ) • Q)).det‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (det_add_I_smul_ne_zero hAh hA0 (hQ.smul ha))
  have hdiff : F1 x - FQ x = f x * ∫ s in Ioc 0 (δ / Λ),
      partialAbsorberDensity A Q (δ / Λ) s := by
    rw [hF1d, hFQd]
    simp only
    rw [h0, absorbedShift_eq_add_I_smul H Q E Λ x (δ / Λ),
      absorbedShift_eq_add_I_smul H 1 E Λ x (δ / Λ), ← hAd,
      ← mul_sub, Real.log_div hn1 hnA, Real.log_div hnQ hnA, sub_sub_sub_cancel_right, hftc,
      intervalIntegral.integral_of_le ha]
  rw [hdiff, ENNReal.ofReal_mul (hf0 x), ofReal_integral_eq_lintegral_ofReal hint.1
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
      partialAbsorberDensity_nonneg hAh hA0 hQ hIQ ha hs.1.le)]

/-- **Step 1, convolution form.** For Hermitian `H`, real `E, δ`, `Λ ≠ 0` and `f` continuous
with compact support: `𝓡_δ^I(H; f) = Σ_α (k_δ ⋆ f)(u_α)` with `u_α = Λ(λ_α - E)` and
`(k_δ ⋆ f)(u) = ∫ k_δ(s) f(u - s) ds` (Lebesgue measure). -/
theorem positiveLogStatistic_one_eq_sum_logKernel_conv {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E δ : ℝ) {Λ : ℝ} (hΛ : Λ ≠ 0) {f : ℝ → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    positiveLogStatistic H E Λ δ 1 f =
      ∑ α, ∫ s, logKernel δ s * f
        (Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E) - s) := by
  rw [positiveLogStatistic_one_eq_sum_integral_logKernel hH E δ hΛ hf hfs]
  refine Finset.sum_congr rfl fun α _ => ?_
  set u := Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH α - E)
  rw [← integral_sub_left_eq_self (fun x => f x * logKernel δ (u - x)) volume u]
  simp only [sub_sub_cancel]
  exact integral_congr_ae (ae_of_all _ fun s => mul_comm _ _)

end Deterministic

/-!
### Block models
-/

section BlockModel

variable {k W : ℕ}

/-- `P_B = BlockBand.Internal.Contracts.Inputs.blockProjector B` is the diagonal `absorberProjector` of the sites
`{x | x.1 ∈ B}`. -/
theorem blockProjector_eq_absorberProjector (B : Finset (Fin k)) :
    (BlockBand.Internal.Contracts.Inputs.blockProjector B : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) =
      absorberProjector (Finset.univ.filter fun x : Fin k × Fin W => x.1 ∈ B) := by
  unfold BlockBand.Internal.Contracts.Inputs.blockProjector absorberProjector
  congr 1
  funext x
  simp

/-- `P_B` is positive semidefinite. -/
theorem blockProjector_posSemidef (B : Finset (Fin k)) :
    (BlockBand.Internal.Contracts.Inputs.blockProjector B : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ).PosSemidef := by
  rw [blockProjector_eq_absorberProjector]
  exact absorberProjector_posSemidef _

/-- `1 - P_C = P_{Cᶜ}` for unions of blocks. -/
theorem one_sub_blockProjector (C : Finset (Fin k)) :
    1 - (BlockBand.Internal.Contracts.Inputs.blockProjector C : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) =
      BlockBand.Internal.Contracts.Inputs.blockProjector Cᶜ := by
  rw [blockProjector_eq_absorberProjector, blockProjector_eq_absorberProjector,
    one_sub_absorberProjector]
  congr 1
  ext x
  simp

/-- The Hamiltonian `H = D + ⊕_j A_j` of a block model is measurable. -/
theorem measurable_blockModel_H (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) : Measurable M.H := by
  have hb : Measurable M.blockSum := by
    rw [Matrix.measurable_iff]
    intro x y
    by_cases hj : x.1 = y.1
    · simp only [BlockBand.Internal.Contracts.Inputs.BlockModel.blockSum, hj, ite_true]
      exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp M.measurable_A))
    · simp only [BlockBand.Internal.Contracts.Inputs.BlockModel.blockSum, hj, ite_false]
      exact measurable_const
  rw [Matrix.measurable_iff] at hb ⊢
  intro x y
  exact ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp M.measurable_D)).add
    (hb x y)

/-- The same model with the absorber replaced by a deterministic positive semidefinite `Y`. -/
def withAbsorber (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W)
    (Y : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) (hY : Y.PosSemidef) :
    BlockBand.Internal.Contracts.Inputs.BlockModel k W :=
  { M with Y := fun _ => Y, measurable_Y := measurable_const, posSemidef_Y := fun _ => hY }

/-- Replacing the absorber by a deterministic one preserves `IsIndependent c`. -/
theorem isIndependent_withAbsorber {M : BlockBand.Internal.Contracts.Inputs.BlockModel k W} {c : ℝ}
    (hM : M.IsIndependent c) (Y : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)
    (hY : Y.PosSemidef) : (withAbsorber M Y hY).IsIndependent c := by
  refine ⟨hM.1, hM.2.1, ?_⟩
  exact hM.2.2.comp (φ := fun p : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ ×
      Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ => (p.1, Y)) (ψ := id)
    (measurable_fst.prodMk measurable_const) measurable_id

/-- For every block model, union `B`, real `e` and outcome `w`, the boundary value `η = 0` of `-Im Tr P_B G_η` is at
most its `liminf` as `η ↓ 0`, in `ℝ≥0∞`. -/
theorem ofReal_projectedDensity_zero_le_liminf (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W)
    (B : Finset (Fin k)) (e : ℝ) (w : M.Ω) :
    ENNReal.ofReal (M.projectedDensity B e 0 w) ≤
      Filter.liminf (fun η => ENNReal.ofReal (M.projectedDensity B e η w)) (𝓝[>] (0 : ℝ)) := by
  set N := M.H w - (e : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) +
    Complex.I • M.Y w with hN
  have hres : ∀ η : ℝ, M.absorbedResolvent e η w =
      (N + (η : ℂ) • (Complex.I • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)))⁻¹ := by
    intro η
    unfold BlockBand.Internal.Contracts.Inputs.BlockModel.absorbedResolvent
    rw [hN, smul_smul]
  by_cases hdet : IsUnit N.det
  · have hc : ContinuousAt (fun η : ℝ => M.projectedDensity B e η w) 0 := by
      unfold BlockBand.Internal.Contracts.Inputs.BlockModel.projectedDensity
      simp_rw [hres]
      have hinv : ContinuousAt Inv.inv
          (N + ((0 : ℝ) : ℂ) • (Complex.I • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ))) := by
        refine continuousAt_matrix_inv _ ?_
        rw [Ring.inverse_eq_inv']
        refine continuousAt_inv₀ ?_
        simpa using hdet.ne_zero
      have hl : Continuous (fun η : ℝ =>
          N + (η : ℂ) • (Complex.I • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ))) := by
        fun_prop
      have := ContinuousAt.comp (x := (0 : ℝ)) hinv hl.continuousAt
      exact ((Complex.continuous_im.comp (continuous_const.mul continuous_id).matrix_trace
        ).continuousAt.comp this).neg
    have ht := (ENNReal.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    exact (ht.liminf_eq).ge
  · have h0 : M.projectedDensity B e 0 w = 0 := by
      unfold BlockBand.Internal.Contracts.Inputs.BlockModel.projectedDensity
      rw [hres, Complex.ofReal_zero, zero_smul, add_zero,
        Matrix.nonsing_inv_apply_not_isUnit _ hdet]
      simp
    rw [h0, ENNReal.ofReal_zero]
    exact zero_le

/-- The Step 3 integrand is jointly measurable in `(H, x, s)`. -/
theorem measurable_partialAbsorberDensity_absorbedShift {ι : Type*} [Fintype ι]
    [DecidableEq ι] (E Λ a : ℝ) (Q : Matrix ι ι ℂ) :
    Measurable (fun p : Matrix ι ι ℂ × ℝ × ℝ =>
      partialAbsorberDensity (absorbedShift p.1 E Λ p.2.1 0 1) Q a p.2.2) := by
  unfold partialAbsorberDensity
  have hN : Continuous (fun p : Matrix ι ι ℂ × ℝ × ℝ =>
      absorbedShift p.1 E Λ p.2.1 0 1 + Complex.I • (a • Q + p.2.2 • (1 - Q))) := by
    unfold absorbedShift
    fun_prop
  exact ((Complex.continuous_im.comp (continuous_const.mul continuous_id).matrix_trace
    ).measurable.comp (measurable_matrix_inv.comp hN.measurable)).neg

/-- The Step 3 integrand at `(x, s)` is the boundary-value projected density `η = 0` of the
same model with the deterministic absorber `Y = aP_C + sP_{Cᶜ}`, at `e = E + x/Λ`. -/
theorem partialAbsorberDensity_eq_projectedDensity (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W)
    (C : Finset (Fin k)) (E Λ x : ℝ) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (w : M.Ω) :
    partialAbsorberDensity (absorbedShift (M.H w) E Λ x 0 1) (BlockBand.Internal.Contracts.Inputs.blockProjector C) a s =
      (withAbsorber M (a • BlockBand.Internal.Contracts.Inputs.blockProjector C + s • BlockBand.Internal.Contracts.Inputs.blockProjector Cᶜ)
        ((blockProjector_posSemidef C).smul ha |>.add ((blockProjector_posSemidef Cᶜ).smul hs))
        ).projectedDensity Cᶜ (E + x / Λ) 0 w := by
  unfold partialAbsorberDensity BlockBand.Internal.Contracts.Inputs.BlockModel.projectedDensity
    BlockBand.Internal.Contracts.Inputs.BlockModel.absorbedResolvent
  rw [one_sub_blockProjector]
  have hH : (withAbsorber M (a • BlockBand.Internal.Contracts.Inputs.blockProjector C + s • BlockBand.Internal.Contracts.Inputs.blockProjector Cᶜ)
      ((blockProjector_posSemidef C).smul ha |>.add ((blockProjector_posSemidef Cᶜ).smul hs))
      ).H w = M.H w := rfl
  rw [hH]
  congr 5
  simp [absorbedShift, withAbsorber]

/-- **Projected Wegner at every intermediate absorber.** Let `CW` be a constant for which
clause 3 of `BlockBand.Internal.Contracts.Inputs.ProjectedWegner` holds at `(k, W, c)`. For every model with
`IsIndependent c`, union `C`, real `E, Λ, x` and `a, s ≥ 0`:
`E[-Im Tr(P_{Cᶜ} G_s(x))] ≤ π (CW/√c) W |Cᶜ|` in `ℝ≥0∞`. -/
theorem lintegral_ofReal_partialAbsorberDensity_le {c CW : ℝ}
    (hW3 : ∀ M' : BlockBand.Internal.Contracts.Inputs.BlockModel k W, M'.IsIndependent c → ∀ (e : ℝ) (B : Finset (Fin k)),
      (∫⁻ w, Filter.liminf (fun η => ENNReal.ofReal (M'.projectedDensity B e η w))
          (𝓝[>] (0 : ℝ)) ∂M'.P) ≤
        ENNReal.ofReal (Real.pi * (CW / Real.sqrt c) * (W : ℝ) * (B.card : ℝ)))
    {M : BlockBand.Internal.Contracts.Inputs.BlockModel k W} (hM : M.IsIndependent c) (C : Finset (Fin k))
    (E Λ x : ℝ) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∫⁻ w, ENNReal.ofReal (partialAbsorberDensity (absorbedShift (M.H w) E Λ x 0 1)
        (BlockBand.Internal.Contracts.Inputs.blockProjector C) a s) ∂M.P ≤
      ENNReal.ofReal (Real.pi * (CW / Real.sqrt c) * (W : ℝ) * ((Cᶜ).card : ℝ)) := by
  have hY := ((blockProjector_posSemidef (W := W) C).smul ha).add
    ((blockProjector_posSemidef (W := W) Cᶜ).smul hs)
  set M' := withAbsorber M _ hY with hM'
  have h := hW3 M' (isIndependent_withAbsorber hM _ hY) (E + x / Λ) Cᶜ
  refine le_trans (lintegral_mono fun w => ?_) h
  rw [partialAbsorberDensity_eq_projectedDensity M C E Λ x ha hs w]
  exact ofReal_projectedDensity_zero_le_liminf M' Cᶜ (E + x / Λ) w

/-- **Step 3 in expectation.** Under clause 3 of projected Wegner with constant `CW ≥ 0` at
`(k, W, c)`, for every model with `IsIndependent c`, union `C`, real `E`, `Λ > 0`, `δ > 0`
and `f ≥ 0` continuous with compact support:
`E (𝓡_δ^I - 𝓡_δ^C) ≤ ‖f‖₁ (CW/√c) W |Cᶜ| / Λ` (as an `ℝ≥0∞` bound on `E ofReal`). -/
theorem lintegral_ofReal_positiveLogStatistic_sub_le {c CW : ℝ} (hCW : 0 ≤ CW)
    (hW3 : ∀ M' : BlockBand.Internal.Contracts.Inputs.BlockModel k W, M'.IsIndependent c → ∀ (e : ℝ) (B : Finset (Fin k)),
      (∫⁻ w, Filter.liminf (fun η => ENNReal.ofReal (M'.projectedDensity B e η w))
          (𝓝[>] (0 : ℝ)) ∂M'.P) ≤
        ENNReal.ofReal (Real.pi * (CW / Real.sqrt c) * (W : ℝ) * (B.card : ℝ)))
    {M : BlockBand.Internal.Contracts.Inputs.BlockModel k W} (hM : M.IsIndependent c) (C : Finset (Fin k)) (E : ℝ)
    {Λ δ : ℝ} (hΛ : 0 < Λ) (hδ : 0 < δ) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ w, ENNReal.ofReal (positiveLogStatistic (M.H w) E Λ δ 1 f -
        positiveLogStatistic (M.H w) E Λ δ (BlockBand.Internal.Contracts.Inputs.blockProjector C) f) ∂M.P ≤
      ENNReal.ofReal ((∫ x, f x) * (CW / Real.sqrt c) * (W : ℝ) * ((Cᶜ).card : ℝ) / Λ) := by
  set Q : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ := BlockBand.Internal.Contracts.Inputs.blockProjector C with hQd
  have hQ : Q.PosSemidef := blockProjector_posSemidef C
  have hIQ : (1 - Q).PosSemidef := by
    rw [hQd, one_sub_blockProjector]
    exact blockProjector_posSemidef _
  have ha : 0 ≤ δ / Λ := div_nonneg hδ.le hΛ.le
  set Bw : ℝ := Real.pi * (CW / Real.sqrt c) * (W : ℝ) * ((Cᶜ).card : ℝ) with hBwd
  have hBw : 0 ≤ Bw := by positivity
  have hψm : Measurable (fun p : (M.Ω × ℝ) × ℝ =>
      partialAbsorberDensity (absorbedShift (M.H p.1.1) E Λ p.1.2 0 1) Q (δ / Λ) p.2) := by
    have hg : Measurable (fun p : (M.Ω × ℝ) × ℝ => (M.H p.1.1, p.1.2, p.2)) :=
      ((measurable_blockModel_H M).comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h := (measurable_partialAbsorberDensity_absorbedShift E Λ (δ / Λ) Q).comp hg
    exact h
  obtain ⟨G, hGd⟩ : ∃ G : M.Ω → ℝ → ℝ → ℝ≥0∞, G = fun w x s =>
      ENNReal.ofReal (f x) * ENNReal.ofReal
        (partialAbsorberDensity (absorbedShift (M.H w) E Λ x 0 1) Q (δ / Λ) s) := ⟨_, rfl⟩
  have hGm : Measurable (fun p : (M.Ω × ℝ) × ℝ => G p.1.1 p.1.2 p.2) := by
    have h := (ENNReal.measurable_ofReal.comp (hf.measurable.comp (measurable_snd.comp
      measurable_fst))).mul (ENNReal.measurable_ofReal.comp hψm)
    rw [hGd]
    exact h
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport hfs
  calc ∫⁻ w, ENNReal.ofReal (positiveLogStatistic (M.H w) E Λ δ 1 f -
          positiveLogStatistic (M.H w) E Λ δ Q f) ∂M.P
      = ∫⁻ w, ENNReal.ofReal ((Real.pi * δ)⁻¹) *
          (∫⁻ x, ∫⁻ s in Ioc 0 (δ / Λ), G w x s) ∂M.P := by
        refine lintegral_congr fun w => ?_
        rw [ofReal_positiveLogStatistic_one_sub_eq_lintegral
          (BlockModelCount.isHermitian_H M w) E hΛ hδ hQ hIQ hf hfs hf0]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [hGd, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((Real.pi * δ)⁻¹) *
          ∫⁻ x, ∫⁻ w, (∫⁻ s in Ioc 0 (δ / Λ), G w x s) ∂M.P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap]
        exact (hGm.lintegral_prod_right' (ν := volume.restrict (Ioc 0 (δ / Λ)))).aemeasurable
    _ = ENNReal.ofReal ((Real.pi * δ)⁻¹) *
          ∫⁻ x, ∫⁻ s in Ioc 0 (δ / Λ), ∫⁻ w, G w x s ∂M.P := by
        congr 1
        refine lintegral_congr fun x => ?_
        rw [lintegral_lintegral_swap]
        exact (hGm.comp ((measurable_fst.prodMk measurable_const).prodMk
          measurable_snd)).aemeasurable
    _ ≤ ENNReal.ofReal ((Real.pi * δ)⁻¹) *
          ∫⁻ x, ENNReal.ofReal (f x) * (ENNReal.ofReal Bw * ENNReal.ofReal (δ / Λ)) := by
        gcongr with x
        calc ∫⁻ s in Ioc 0 (δ / Λ), ∫⁻ w, G w x s ∂M.P
            ≤ ∫⁻ s in Ioc 0 (δ / Λ), ENNReal.ofReal (f x) * ENNReal.ofReal Bw := by
              refine setLIntegral_mono measurable_const fun s hs => ?_
              rw [hGd]
              simp only
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              gcongr
              exact lintegral_ofReal_partialAbsorberDensity_le hW3 hM C E Λ x ha hs.1.le
          _ = ENNReal.ofReal (f x) * (ENNReal.ofReal Bw * ENNReal.ofReal (δ / Λ)) := by
              rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_assoc]
    _ = ENNReal.ofReal ((Real.pi * δ)⁻¹) *
          (ENNReal.ofReal (∫ x, f x) * (ENNReal.ofReal Bw * ENNReal.ofReal (δ / Λ))) := by
        rw [lintegral_mul_const' _ _ (by finiteness),
          ← ofReal_integral_eq_lintegral_ofReal hfint (ae_of_all _ hf0)]
    _ = _ := by
        have hfi : 0 ≤ ∫ x, f x := integral_nonneg hf0
        rw [← ENNReal.ofReal_mul hBw, ← ENNReal.ofReal_mul hfi,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity))]
        congr 1
        rw [hBwd]
        field_simp

end BlockModel

/-!
### The lemma
-/

section Main

open BlockBand.Foundations.Spectral

variable {k W : ℕ}

/-- The unfolded eigenvalues `w ↦ (Λ(λ_α(H_w) - E))_α` of a block model are measurable. -/
theorem measurable_unfoldedEigenvalues (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (E Λ : ℝ) :
    Measurable (fun w α =>
      Λ * (increasingEigenvalue (BlockModelCount.isHermitian_H M w) α - E)) := by
  refine measurable_pi_iff.mpr fun α => ?_
  have hH : Measurable (fun w => (⟨M.H w, BlockModelCount.isHermitian_H M w⟩ :
      BlockBand.Model.Construction.HermitianMatrix (Fin k × Fin W))) :=
    (measurable_blockModel_H M).subtype_mk
  have h := (BlockBand.Model.Construction.measurable_increasingEigenvalue α).comp hH
  exact measurable_const.mul (h.sub measurable_const)

/-- Interval counts in unfolded units: for `Λ > 0`, `u_α = Λ(λ_α - E) ∈ [a, b]` iff
`λ_α ∈ [E + a/Λ, E + b/Λ]`. -/
theorem mul_sub_mem_Icc_iff {Λ : ℝ} (hΛ : 0 < Λ) (E l a b : ℝ) :
    Λ * (l - E) ∈ Icc a b ↔ l ∈ Icc (E + a / Λ) (E + b / Λ) := by
  simp only [mem_Icc]
  rw [← div_le_iff₀' hΛ, ← le_div_iff₀' hΛ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Assembly of Steps 1–3** on a finite measure space. Let `RC, RI, T, S` be measurable
real random variables with `0 ≤ RC ≤ RI` (Step 2), `RI = S` (Step 1), `S - T` integrable with
`E|S - T| ≤ e₁` (smoothing), and `E ofReal(RI - RC) ≤ ofReal e₂` with `e₂ ≥ 0` (Step 3).
Then `|RC - T|` is integrable and `E|RC - T| ≤ e₂ + e₁`. -/
theorem integrable_abs_sub_and_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {RC RI T S : Ω → ℝ} (hRCm : Measurable RC) (hRIm : Measurable RI)
    (hTm : Measurable T) (h2 : ∀ w, 0 ≤ RC w ∧ RC w ≤ RI w) (hS : ∀ w, RI w = S w)
    (hST : Integrable (fun w => S w - T w) P) {e₁ e₂ : ℝ}
    (hb1 : ∫ w, |S w - T w| ∂P ≤ e₁)
    (hlin : ∫⁻ w, ENNReal.ofReal (RI w - RC w) ∂P ≤ ENNReal.ofReal e₂) (he₂ : 0 ≤ e₂) :
    Integrable (fun w => |RC w - T w|) P ∧ ∫ w, |RC w - T w| ∂P ≤ e₂ + e₁ := by
  have hDm : Measurable fun w => RI w - RC w := hRIm.sub hRCm
  have hDnn : ∀ w, 0 ≤ RI w - RC w := fun w => sub_nonneg.mpr (h2 w).2
  have hD : Integrable (fun w => RI w - RC w) P := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hDnn _)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  have hX : ∀ w, |RC w - T w| ≤ (RI w - RC w) + |S w - T w| := by
    intro w
    have h := abs_sub_le (RC w) (RI w) (T w)
    rw [abs_sub_comm (RC w) (RI w), abs_of_nonneg (hDnn w)] at h
    rwa [← hS w]
  have hdom : Integrable (fun w => (RI w - RC w) + |S w - T w|) P := hD.add hST.abs
  have hint : Integrable (fun w => |RC w - T w|) P :=
    hdom.mono' (hRCm.sub hTm).abs.aestronglyMeasurable
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs, abs_abs]; exact hX w)
  refine ⟨hint, ?_⟩
  have hDle : ∫ w, (RI w - RC w) ∂P ≤ e₂ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hDnn) hDm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal he₂ hlin
  calc ∫ w, |RC w - T w| ∂P ≤ ∫ w, ((RI w - RC w) + |S w - T w|) ∂P :=
        integral_mono hint hdom hX
    _ = (∫ w, (RI w - RC w) ∂P) + ∫ w, |S w - T w| ∂P := integral_add hD hST.abs
    _ ≤ e₂ + e₁ := add_le_add hDle hb1

/-- **Finite-log recovery.** For smooth compactly supported `f ≥ 0` there is `Cf ≥ 0` such that,
for every independent block model with `k` blocks of size `W`, every `E`, `δ > 0` and every union
of blocks `C`, with `Λ = kWρ`: `E|𝓡_δ^C(H; f) - Tr f(Λ(H - E))| ≤ Cf (δ(1 + |log δ|) + |Cᶜ|/k)`
(and the left side is integrable). -/
theorem finiteLogRecovery
    (hWegner : BlockBand.Internal.Contracts.Inputs.ProjectedWegner) (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (c : ℝ) (hc : 0 < c) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (k W : ℕ), 0 < k → 0 < W → ∀ M : BlockBand.Internal.Contracts.Inputs.BlockModel k W,
      M.IsIndependent c →
      ∀ (E δ : ℝ), 0 < δ → ∀ C : Finset (Fin k),
        Integrable (fun w => |positiveLogStatistic (M.H w) E ((k * W : ℕ) * ρ) δ
            (BlockBand.Internal.Contracts.Inputs.blockProjector C) f -
          unfoldedSpectralSum (M.H w) (BlockModelCount.isHermitian_H M w) E
            ((k * W : ℕ) * ρ) f|) M.P ∧
        ∫ w, |positiveLogStatistic (M.H w) E ((k * W : ℕ) * ρ) δ
            (BlockBand.Internal.Contracts.Inputs.blockProjector C) f -
          unfoldedSpectralSum (M.H w) (BlockModelCount.isHermitian_H M w) E
            ((k * W : ℕ) * ρ) f| ∂M.P ≤
          Cf * (δ * (1 + |Real.log δ|) + ((Cᶜ).card : ℝ) / k) := by
  obtain ⟨CW, hCW, hWeg⟩ := hWegner
  obtain ⟨Cc, hCc, hcnt⟩ := BlockModelCount.blockModel_count_le hCount
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
  have hfc : Continuous f := hf.continuous
  obtain ⟨R0, hR0⟩ := hfs.isCompact.isBounded.subset_closedBall 0
  set R := max R0 0 with hRd
  have hR : 0 ≤ R := le_max_right _ _
  have hsupp : Function.support f ⊆ Icc (-R) R := by
    intro x hx
    have := hR0 (subset_tsupport f hx)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp (this.trans (le_max_left _ _))
  obtain ⟨Mf, hMf⟩ := hfc.bounded_above_of_compact_support hfs
  have hMf' : ∀ x, |f x| ≤ Mf := fun x => by simpa [Real.norm_eq_abs] using hMf x
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf' 0)
  set K : ℝ := Cc / Real.sqrt c / ρ with hKd
  have hK : 0 ≤ K := by positivity
  set A1 : ℝ := 8 * K * ((∫ x, |deriv f x|) + R * Mf + ∫ x, |f x|) with hA1d
  set A2 : ℝ := (∫ x, f x) * (CW / Real.sqrt c) / ρ with hA2d
  have hA1 : 0 ≤ A1 := by
    have h1 : 0 ≤ ∫ x, |deriv f x| := integral_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ ∫ x, |f x| := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hA2 : 0 ≤ A2 := by
    have h1 : 0 ≤ ∫ x, f x := integral_nonneg hf0
    positivity
  refine ⟨A1 + A2, add_nonneg hA1 hA2, ?_⟩
  intro k W hk hW M hM E δ hδ C
  have hkW : (0 : ℝ) < ((k * W : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos hk hW)
  have hΛ : (0 : ℝ) < ((k * W : ℕ) : ℝ) * ρ := mul_pos hkW hρ
  have hu := measurable_unfoldedEigenvalues M E (((k * W : ℕ) : ℝ) * ρ)
  have hcount : ∀ a b : ℝ, a ≤ b →
      ∫ w, ((Finset.univ.filter fun α => ((k * W : ℕ) : ℝ) * ρ *
          (increasingEigenvalue (BlockModelCount.isHermitian_H M w) α - E) ∈ Icc a b).card : ℝ)
        ∂M.P ≤ K * (b - a) := by
    intro a b hab
    have hab' : E + a / (((k * W : ℕ) : ℝ) * ρ) ≤ E + b / (((k * W : ℕ) : ℝ) * ρ) := by
      gcongr
    have h := (hcnt k W hW c hc M hM _ _ hab').2
    simp_rw [mul_sub_mem_Icc_iff hΛ]
    refine h.trans (le_of_eq ?_)
    rw [hKd]
    field_simp
    ring
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((hf1.differentiable one_ne_zero) x).hasDerivAt
  have hdint : Integrable (deriv f) :=
    (hf1.continuous_deriv le_rfl).integrable_of_hasCompactSupport hfs.deriv
  have hsupp' : ∀ x, x ∉ Icc (-R) R → f x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => hx (hsupp h)
  have hST := integrable_sum_logKernel_conv_sub hu hcount hK hδ hR hd hdint hsupp' hMf'
  have hb1 := integral_abs_sum_logKernel_conv_sub_le_of_contDiff hu hcount hK hδ hR hf1 hsupp hMf'
  have hW3 : ∀ M' : BlockBand.Internal.Contracts.Inputs.BlockModel k W, M'.IsIndependent c → ∀ (e : ℝ) (B : Finset (Fin k)),
      (∫⁻ w, Filter.liminf (fun η => ENNReal.ofReal (M'.projectedDensity B e η w))
          (𝓝[>] (0 : ℝ)) ∂M'.P) ≤
        ENNReal.ofReal (Real.pi * (CW / Real.sqrt c) * (W : ℝ) * (B.card : ℝ)) :=
    fun M' hM' e B => (hWeg k W hW c hc M').2.2.1 hM' e B
  have hlin := lintegral_ofReal_positiveLogStatistic_sub_le hCW.le hW3 hM C E hΛ hδ hfc hfs hf0
  have he2 : (∫ x, f x) * (CW / Real.sqrt c) * (W : ℝ) * ((Cᶜ).card : ℝ) /
      (((k * W : ℕ) : ℝ) * ρ) = A2 * (((Cᶜ).card : ℝ) / k) := by
    rw [hA2d]
    have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hW' : (0 : ℝ) < W := Nat.cast_pos.mpr hW
    push_cast
    field_simp
  rw [he2] at hlin
  have h2 : ∀ w, 0 ≤ positiveLogStatistic (M.H w) E (((k * W : ℕ) : ℝ) * ρ) δ
        (BlockBand.Internal.Contracts.Inputs.blockProjector C) f ∧
      positiveLogStatistic (M.H w) E (((k * W : ℕ) : ℝ) * ρ) δ (BlockBand.Internal.Contracts.Inputs.blockProjector C) f ≤
        positiveLogStatistic (M.H w) E (((k * W : ℕ) : ℝ) * ρ) δ 1 f := by
    intro w
    rw [blockProjector_eq_absorberProjector]
    exact positiveLogStatistic_absorberProjector_nonneg_le_one
      (BlockModelCount.isHermitian_H M w) E hΛ hδ _ hfc hfs hf0
  have hS : ∀ w, positiveLogStatistic (M.H w) E (((k * W : ℕ) : ℝ) * ρ) δ 1 f =
      ∑ α, ∫ s, logKernel δ s * f (((k * W : ℕ) : ℝ) * ρ *
        (increasingEigenvalue (BlockModelCount.isHermitian_H M w) α - E) - s) := fun w =>
    positiveLogStatistic_one_eq_sum_logKernel_conv (BlockModelCount.isHermitian_H M w) E δ
      hΛ.ne' hfc hfs
  have hTm : Measurable (fun w => unfoldedSpectralSum (M.H w)
      (BlockModelCount.isHermitian_H M w) E (((k * W : ℕ) : ℝ) * ρ) f) :=
    Finset.measurable_sum _ fun α _ => hfc.measurable.comp ((measurable_pi_apply α).comp hu)
  have hL : 0 ≤ δ * (1 + |Real.log δ|) := by positivity
  have hB : 0 ≤ ((Cᶜ).card : ℝ) / k := by positivity
  obtain ⟨hint, hle⟩ := integrable_abs_sub_and_integral_le
    (measurable_positiveLogStatistic (measurable_blockModel_H M) E _ δ _ hfc)
    (measurable_positiveLogStatistic (measurable_blockModel_H M) E _ δ 1 hfc) hTm h2 hS hST
    hb1 hlin (mul_nonneg hA2 hB)
  refine ⟨hint, hle.trans ?_⟩
  have : 8 * K * ((∫ x, |deriv f x|) + R * Mf + ∫ x, |f x|) * δ * (1 + |Real.log δ|) =
      A1 * (δ * (1 + |Real.log δ|)) := by rw [hA1d]; ring
  rw [this]
  nlinarith [mul_nonneg hA1 hB, mul_nonneg hA2 hL]

end Main

end BlockBand.Endpoints
