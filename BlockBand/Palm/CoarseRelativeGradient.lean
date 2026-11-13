module

public import BlockBand.Palm.CoarseRelativeStability

/-!
# Coarse relative local law: Gaussian gradient of the normalized trace

The normalized trace `f = ⟨(F + √s G - z)⁻¹⟩` is `C¹` in the real Gaussian coordinates of `G`,
with partial derivatives `∂_j f = -N⁻¹ √s tr(R² ∂_jG)`, and its weighted gradient is at most
`√s N⁻¹ η⁻²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open scoped ComplexConjugate NNReal ENNReal

section Calc

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Derivative of `y ↦ c tr (A₀ + L y)⁻¹` along an everywhere invertible affine family. -/
theorem traceInv_hasFDerivAt (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (c : ℂ)
    (hU : ∀ y, IsUnit (A₀ + L y).det) (y : V) :
    ∃ D : V →L[ℝ] ℂ, HasFDerivAt (fun y => c * ((A₀ + L y)⁻¹).trace) D y ∧
      ∀ v, D v = -(c * ((A₀ + L y)⁻¹ * L v * (A₀ + L y)⁻¹).trace) := by
  set L' := LinearMap.toContinuousLinearMap L
  set T := (Matrix.traceLinearMap ι ℝ ℂ).toContinuousLinearMap
  have hA : HasFDerivAt (fun y => A₀ + L y) L' y :=
    (L'.hasFDerivAt (x := y)).const_add A₀
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (hU y)
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinv
  have hc := (T.hasFDerivAt.comp y (hinv.comp y hA)).const_mul c
  have hfun : (fun y => c * ((A₀ + L y)⁻¹).trace) =
      (fun y => c * (T ∘ Ring.inverse ∘ fun y => A₀ + L y) y) := by
    funext w
    simp [T, Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  refine ⟨_, hc, ?_⟩
  intro v
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [← Ring.inverse_unit u, hu, ← Matrix.nonsing_inv_eq_ringInverse]
  change c * ((-((A₀ + L y)⁻¹ * L v * (A₀ + L y)⁻¹)).trace) = _
  rw [Matrix.trace_neg]
  ring

/-- `y ↦ c tr (A₀ + L y)⁻¹` is `C¹` along an everywhere invertible affine family. -/
theorem traceInv_contDiff (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (c : ℂ)
    (hU : ∀ y, IsUnit (A₀ + L y).det) :
    ContDiff ℝ 1 (fun y => c * ((A₀ + L y)⁻¹).trace) := by
  set T := (Matrix.traceLinearMap ι ℝ ℂ).toContinuousLinearMap
  have hL : ContDiff ℝ 1 (fun y => A₀ + L y) :=
    contDiff_const.add ((LinearMap.toContinuousLinearMap L).contDiff (n := 1))
  have hI : ContDiff ℝ 1 (fun y => (A₀ + L y)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (hU y)
    have h := contDiffAt_ringInverse ℝ (n := 1) u
    rw [hu] at h
    exact h.comp y hL.contDiffAt
  exact contDiff_const.mul ((T.contDiff (n := 1)).comp hI)

end Calc

section Coords

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `gueCoord t` as an `ℝ`-linear map. -/
def gueCoordLin (t : ℝ≥0) : (((ι × ι) × Fin 2) → ℝ) →ₗ[ℝ] Matrix ι ι ℂ where
  toFun := gueCoord t
  map_add' y y' := by
    ext k l
    simp only [gueCoord, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates, of_apply,
      Pi.add_apply, Matrix.add_apply]
    push_cast
    simp only [map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  map_smul' r y := by
    ext k l
    simp only [gueCoord, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates, of_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
    push_cast
    simp only [map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

omit [Fintype ι] in
theorem gueCoord_single0' (t : ℝ≥0) (a b : ι) :
    gueCoord t (Pi.single ((a, b), (0 : Fin 2)) (1 : ℝ)) =
      ((Real.sqrt (t / 2) / Real.sqrt 2 : ℝ) : ℂ) • (single a b 1 + single b a 1) := by
  ext k l
  simp only [gueCoord, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates, of_apply,
    Pi.single_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, Prod.mk.injEq]
  by_cases h1 : a = k <;> by_cases h2 : b = l <;> by_cases h3 : b = k <;> by_cases h4 : a = l <;>
    by_cases h5 : k = l <;> simp [h1, h2, h3, h4, h5, eq_comm] <;> ring1

omit [Fintype ι] in
theorem gueCoord_single1' (t : ℝ≥0) (a b : ι) :
    gueCoord t (Pi.single ((a, b), (1 : Fin 2)) (1 : ℝ)) =
      ((Real.sqrt (t / 2) / Real.sqrt 2 : ℝ) : ℂ) •
        (Complex.I • single a b 1 - Complex.I • single b a 1) := by
  ext k l
  simp only [gueCoord, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates, of_apply,
    Pi.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, Prod.mk.injEq]
  by_cases h1 : a = k <;> by_cases h2 : b = l <;> by_cases h3 : b = k <;> by_cases h4 : a = l <;>
    by_cases h5 : k = l <;> simp [h1, h2, h3, h4, h5, eq_comm] <;> first | ring1 | (ring_nf; simp)

omit [Fintype ι] in
theorem gueCoord_single0 (t : ℝ≥0) (u : ι × ι) :
    gueCoord t (Pi.single (u, (0 : Fin 2)) (1 : ℝ)) =
      ((Real.sqrt (t / 2) / Real.sqrt 2 : ℝ) : ℂ) • (single u.1 u.2 1 + single u.2 u.1 1) := by
  obtain ⟨a, b⟩ := u
  exact gueCoord_single0' t a b

omit [Fintype ι] in
theorem gueCoord_single1 (t : ℝ≥0) (u : ι × ι) :
    gueCoord t (Pi.single (u, (1 : Fin 2)) (1 : ℝ)) =
      ((Real.sqrt (t / 2) / Real.sqrt 2 : ℝ) : ℂ) •
        (Complex.I • single u.1 u.2 1 - Complex.I • single u.2 u.1 1) := by
  obtain ⟨a, b⟩ := u
  exact gueCoord_single1' t a b

theorem trace_mul_gueCoord_single0 (P : Matrix ι ι ℂ) (t : ℝ≥0) (u : ι × ι) :
    (P * gueCoord t (Pi.single (u, (0 : Fin 2)) (1 : ℝ))).trace =
      ((Real.sqrt (t / 2) / Real.sqrt 2 : ℝ) : ℂ) * (P u.2 u.1 + P u.1 u.2) := by
  rw [gueCoord_single0, Matrix.mul_smul, trace_smul, Matrix.mul_add, trace_add, trace_mul_single,
    trace_mul_single]
  simp

theorem trace_mul_gueCoord_single1 (P : Matrix ι ι ℂ) (t : ℝ≥0) (u : ι × ι) :
    (P * gueCoord t (Pi.single (u, (1 : Fin 2)) (1 : ℝ))).trace =
      ((Real.sqrt (t / 2) / Real.sqrt 2 : ℝ) : ℂ) *
        (Complex.I * P u.2 u.1 - Complex.I * P u.1 u.2) := by
  rw [gueCoord_single1, Matrix.mul_smul, trace_smul, Matrix.mul_sub, trace_sub, Matrix.mul_smul,
    Matrix.mul_smul, trace_smul, trace_smul, trace_mul_single, trace_mul_single]
  simp

/-- Exact Hilbert–Schmidt identity `Σ_j |tr(P ∂_jG)|² = t Σ_{ab}|P_ab|²`. -/
theorem sum_norm_trace_gueCoord_sq (P : Matrix ι ι ℂ) (t : ℝ≥0) :
    ∑ j : (ι × ι) × Fin 2, ‖(P * gueCoord t (Pi.single j (1 : ℝ))).trace‖ ^ 2 =
      (t : ℝ) * ∑ u : ι × ι, ‖P u.1 u.2‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, trace_mul_gueCoord_single0, trace_mul_gueCoord_single1]
  set κ : ℝ := Real.sqrt (t / 2) / Real.sqrt 2 with hκ
  have hκ2 : κ ^ 2 = (t : ℝ) / 4 := by
    rw [hκ, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    ring
  have hterm : ∀ u : ι × ι,
      ‖(κ : ℂ) * (P u.2 u.1 + P u.1 u.2)‖ ^ 2 +
        ‖(κ : ℂ) * (Complex.I * P u.2 u.1 - Complex.I * P u.1 u.2)‖ ^ 2 =
      (t : ℝ) / 2 * (‖P u.2 u.1‖ ^ 2 + ‖P u.1 u.2‖ ^ 2) := by
    intro u
    have hI : Complex.I * P u.2 u.1 - Complex.I * P u.1 u.2 =
        Complex.I * (P u.2 u.1 - P u.1 u.2) := by ring
    rw [hI, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, mul_pow, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hκ2]
    have hp := parallelogram_law_with_norm ℂ (P u.2 u.1) (P u.1 u.2)
    nlinarith [hp]
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hswap : ∑ u : ι × ι, ‖P u.2 u.1‖ ^ 2 = ∑ u : ι × ι, ‖P u.1 u.2‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.prodComm ι ι) _ _ (fun u => rfl)
  rw [hswap]
  ring

theorem nsq_single_one (b : ι) : nsq (Pi.single b (1 : ℂ)) = 1 := by
  unfold nsq
  rw [Finset.sum_eq_single b]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- `Σ_{ab}|(R²)_ab|² ≤ |ι| (Im z)^{-4}` for a Hermitian resolvent. -/
theorem resolvent_sq_hs_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ∑ u : ι × ι, ‖((H - z • (1 : Matrix ι ι ℂ))⁻¹ * (H - z • (1 : Matrix ι ι ℂ))⁻¹) u.1 u.2‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ((z.im ^ 2)⁻¹ * (z.im ^ 2)⁻¹) := by
  set R := (H - z • (1 : Matrix ι ι ℂ))⁻¹
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hcol : ∀ b : ι, ∑ a : ι, ‖(R * R) a b‖ ^ 2 = nsq ((R * R) *ᵥ Pi.single b 1) := by
    intro b
    unfold nsq
    simp
  simp_rw [hcol]
  have hb : ∀ b : ι, nsq ((R * R) *ᵥ Pi.single b 1) ≤ (z.im ^ 2)⁻¹ * (z.im ^ 2)⁻¹ := by
    intro b
    rw [← mulVec_mulVec]
    have h1 := hermitian_resolvent_nsq_le hH hz (R *ᵥ Pi.single b 1)
    have h2 := hermitian_resolvent_nsq_le hH hz (Pi.single b (1 : ℂ))
    rw [nsq_single_one, mul_one] at h2
    calc _ ≤ (z.im ^ 2)⁻¹ * nsq (R *ᵥ Pi.single b 1) := h1
      _ ≤ (z.im ^ 2)⁻¹ * (z.im ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc ∑ b : ι, nsq ((R * R) *ᵥ Pi.single b 1) ≤ ∑ _b : ι, (z.im ^ 2)⁻¹ * (z.im ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun b _ => hb b)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Coords

/-!
## The normalized trace in Gaussian coordinates
-/

variable {N : ℕ}

/-- `f(y) = ⟨(F + √s G(y) - z)⁻¹⟩` with `G(y) = gueCoord t y`. -/
def coarseTraceFn (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (t : ℝ≥0)
    (y : ((Fin N × Fin N) × Fin 2) → ℝ) : ℂ :=
  (N : ℂ)⁻¹ * (coarseResolvent F (gueCoord t y) s z).trace

theorem gueCoord_isHermitian {ι : Type} [Fintype ι] (t : ℝ≥0) (y : ((ι × ι) × Fin 2) → ℝ) :
    (gueCoord t y).IsHermitian :=
  gueSample_isHermitian t _

theorem coarse_shift_eq (F G : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (t : ℝ≥0)
    (y : ((Fin N × Fin N) × Fin 2) → ℝ) (hG : G = gueCoord t y) :
    F + (Real.sqrt s : ℂ) • G - z • (1 : Matrix (Fin N) (Fin N) ℂ) =
      (F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) + (Real.sqrt s • gueCoordLin t) y := by
  rw [LinearMap.smul_apply, hG]
  change _ = _ + Real.sqrt s • gueCoord t y
  rw [← Complex.coe_smul]
  abel

theorem coarseTraceFn_eq (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) (t : ℝ≥0) :
    coarseTraceFn F s z t = fun y => (N : ℂ)⁻¹ *
      (((F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) + (Real.sqrt s • gueCoordLin t) y)⁻¹).trace := by
  funext y
  unfold coarseTraceFn coarseResolvent
  rw [coarse_shift_eq F _ s z t y rfl]

theorem coarse_shift_det_isUnit {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ≥0) (y : ((Fin N × Fin N) × Fin 2) → ℝ) :
    IsUnit ((F - z • (1 : Matrix (Fin N) (Fin N) ℂ)) + (Real.sqrt s • gueCoordLin t) y).det := by
  rw [← coarse_shift_eq F _ s z t y rfl]
  exact hermitian_shift_det_isUnit (coarse_hermitian hF (gueCoord_isHermitian t y) s) hz

/-- The normalized trace is `C¹` in the Gaussian coordinates. -/
theorem coarseTraceFn_contDiff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ≥0) : ContDiff ℝ 1 (coarseTraceFn F s z t) := by
  rw [coarseTraceFn_eq]
  exact traceInv_contDiff _ _ _ (coarse_shift_det_isUnit hF s hz t)

/-- Explicit partial derivatives `∂_j f = -N⁻¹ √s tr(R² ∂_jG)`. -/
theorem coarseTraceFn_fderiv {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (t : ℝ≥0) (y v : ((Fin N × Fin N) × Fin 2) → ℝ) :
    fderiv ℝ (coarseTraceFn F s z t) y v =
      -((N : ℂ)⁻¹ * (Real.sqrt s : ℂ) *
        (coarseResolvent F (gueCoord t y) s z * coarseResolvent F (gueCoord t y) s z *
          gueCoord t v).trace) := by
  obtain ⟨D, hD, hDv⟩ := traceInv_hasFDerivAt (F - z • (1 : Matrix (Fin N) (Fin N) ℂ))
    (Real.sqrt s • gueCoordLin t) ((N : ℂ)⁻¹) (coarse_shift_det_isUnit hF s hz t) y
  rw [coarseTraceFn_eq, hD.fderiv, hDv, ← coarse_shift_eq F _ s z t y rfl]
  have hR : (F + (Real.sqrt s : ℂ) • gueCoord t y - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      coarseResolvent F (gueCoord t y) s z := rfl
  rw [hR, LinearMap.smul_apply]
  change -((N : ℂ)⁻¹ * (coarseResolvent F (gueCoord t y) s z *
      (Real.sqrt s • gueCoord t v) * coarseResolvent F (gueCoord t y) s z).trace) = _
  rw [← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul, trace_smul, trace_mul_cycle,
    smul_eq_mul]
  ring

/-- **Gradient bound.** `|∇⟨R⟩| ≤ √s N⁻¹ η⁻²` in the weighted-gradient norm of the Gaussian
coordinates of `GUE_N(1/N)`. -/
theorem coarseTraceFn_grad_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) (y : ((Fin N × Fin N) × Fin 2) → ℝ) :
    BlockBand.Internal.Contracts.Inputs.weightedGradientNorm (fun _ => (1 : ℝ≥0))
        (coarseTraceFn F s z (Real.toNNReal (1 / N))) y ≤
      Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹ := by
  set t := Real.toNNReal (1 / N) with htdef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (t : ℝ) = 1 / N := Real.coe_toNNReal _ (by positivity)
  set R := coarseResolvent F (gueCoord t y) s z with hRdef
  have hH := coarse_hermitian hF (gueCoord_isHermitian t y) s
  unfold BlockBand.Internal.Contracts.Inputs.weightedGradientNorm
  have hterm : ∀ j : (Fin N × Fin N) × Fin 2,
      (((fun _ => (1 : ℝ≥0)) j : ℝ≥0) : ℝ) *
        ‖fderiv ℝ (coarseTraceFn F s z t) y (Pi.single j 1)‖ ^ 2 =
      ((N : ℝ)⁻¹ ^ 2 * s) * ‖(R * R * gueCoord t (Pi.single j 1)).trace‖ ^ 2 := by
    intro j
    rw [coarseTraceFn_fderiv hF s hz.ne' t y, norm_neg, norm_mul, norm_mul, NNReal.coe_one,
      one_mul, norm_inv, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hs]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_norm_trace_gueCoord_sq]
  have hhs := resolvent_sq_hs_le hH hz.ne'
  rw [Fintype.card_fin] at hhs
  have hbound : (N : ℝ)⁻¹ ^ 2 * s * ((t : ℝ) * ∑ u : Fin N × Fin N, ‖(R * R) u.1 u.2‖ ^ 2) ≤
      (Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hs, ht]
    have h0 : 0 ≤ (N : ℝ)⁻¹ ^ 2 * s * (1 / N) := by positivity
    calc (N : ℝ)⁻¹ ^ 2 * s * (1 / N * ∑ u : Fin N × Fin N, ‖(R * R) u.1 u.2‖ ^ 2)
        = (N : ℝ)⁻¹ ^ 2 * s * (1 / N) * ∑ u : Fin N × Fin N, ‖(R * R) u.1 u.2‖ ^ 2 := by ring
      _ ≤ (N : ℝ)⁻¹ ^ 2 * s * (1 / N) * ((N : ℝ) * ((z.im ^ 2)⁻¹ * (z.im ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left hhs h0
      _ = s * (N : ℝ)⁻¹ ^ 2 * ((z.im ^ 2)⁻¹) ^ 2 := by field_simp
  calc Real.sqrt ((N : ℝ)⁻¹ ^ 2 * s * ((t : ℝ) * ∑ u : Fin N × Fin N, ‖(R * R) u.1 u.2‖ ^ 2))
      ≤ Real.sqrt ((Real.sqrt s * (N : ℝ)⁻¹ * (z.im ^ 2)⁻¹) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = _ := Real.sqrt_sq (by positivity)

end BlockBand.Palm.CoarseRelative
