module

public import BlockBand.DeterminantScore.SelectedIBP

/-!
# The gradient of `Tr G R_η` and the Gaussian `L^p` Poincaré bound

A step towards `SelectedResolvent.SelectedIBPStatement`. In the proof of the physical real-loop
proposition, Gaussian `L^p` Poincaré gives
`‖Tr G_dR_η - E_G Tr G_dR_η‖_{L^p} ≤ C_p √t ‖‖R_η - R_ηG_dR_η‖_HS‖_{L^p}`.

In the standard real coordinates `x` of `G = gueLin t x ~ GUE_ι(t)` (`SelectedIBP`), with
`X(x) = traceGRes K η t x = Tr(G R)`, `R = (K + G - iη)⁻¹`, Hermitian `K`, `η ≠ 0`:

* `contDiff_traceGRes`: `X` is `C^n` for every `n` (entries of `R` are `det⁻¹ · adj`).
* `fderiv_traceGRes`: `∂_j X = Tr(E_j (R - RGR))`, `E_j` the coordinate direction.
* `sum_norm_sq_trace_gueDir`: `Σ_j |Tr(E_j B)|² = t Σ_{ab} |B_ab|²` (covariance contraction).
* `weightedGradientNorm_traceGRes`: `|∇X| = √t ‖R - RGR‖_HS` exactly.
* `memLp_traceGRes`: `X ∈ L^q` for every `q` (`|X| ≤ C Σ_k |x_k|`).
* **`traceGRes_concentration`**: from `Inputs.GaussianLpGradient`, one absolute
  `C₀ > 0` with `‖X - E X‖_p ≤ C₀ √p ‖√t ‖R - RGR‖_HS‖_p` for all `p ≥ 1`, `ι`, `K`, `η`, `t`.

The only input is `Inputs.GaussianLpGradient` (hypothesis of `traceGRes_concentration` only).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedIBP

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped NNReal ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

theorem contDiff_det_of_entries {f : E → Matrix ι ι ℂ} (h : ∀ a b, ContDiff ℝ n fun x => f x a b) :
    ContDiff ℝ n fun x => (f x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_adjugate_apply {f : E → Matrix ι ι ℂ} (h : ∀ a b, ContDiff ℝ n fun x => f x a b)
    (i j : ι) : ContDiff ℝ n fun x => (f x).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det_of_entries fun a b => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact h a b

theorem contDiff_inv_apply {f : E → Matrix ι ι ℂ} (h : ∀ a b, ContDiff ℝ n fun x => f x a b)
    (hdet : ∀ x, (f x).det ≠ 0) (i j : ι) : ContDiff ℝ n fun x => (f x)⁻¹ i j := by
  have : (fun x => (f x)⁻¹ i j) = fun x => ((f x).det)⁻¹ * (f x).adjugate i j := by
    funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [this]
  exact ((contDiff_det_of_entries h).inv hdet).mul (contDiff_adjugate_apply h i j)

end Smooth

theorem contDiff_gueLin_apply (t : ℝ≥0) (a b : ι) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : GCoord ι → ℝ => gueLin t x a b := by
  simp only [gueLin_apply]
  have hc : ∀ k : GCoord ι, ContDiff ℝ n fun x : GCoord ι → ℝ => ((x k : ℝ) : ℂ) := fun k =>
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)
  exact contDiff_const.mul (((hc _).add ((hc _).mul contDiff_const)).add
    ((hc _).sub ((hc _).mul contDiff_const)))

theorem contDiff_res_apply {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) (a b : ι) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : GCoord ι → ℝ => res K η (gueLin t x) a b := by
  refine contDiff_inv_apply (fun c d => ?_) (fun x => det_res_ne_zero
    (hK.add (isHermitian_gueLin t x)) hη) a b
  simp only [Matrix.sub_apply, Matrix.add_apply]
  exact (contDiff_const.add (contDiff_gueLin_apply t c d)).sub contDiff_const

/-- `X(x) = Tr(G(x) R(G(x)))`. -/
def traceGRes (K : Matrix ι ι ℂ) (η : ℝ) (t : ℝ≥0) (x : GCoord ι → ℝ) : ℂ :=
  (gueLin t x * res K η (gueLin t x)).trace

theorem contDiff_traceGRes {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) {n : WithTop ℕ∞} : ContDiff ℝ n (traceGRes K η t) := by
  unfold traceGRes
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    (contDiff_gueLin_apply t a b).mul (contDiff_res_apply hK hη t b a)

/-- `B = R - R G R`, the gradient matrix of `Tr G R`. -/
def gradMat (K : Matrix ι ι ℂ) (η : ℝ) (G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  res K η G - res K η G * G * res K η G

theorem hasDerivAt_traceGRes_line {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ}
    (hη : η ≠ 0) (t : ℝ≥0) (x : GCoord ι → ℝ) (j : GCoord ι) (s : ℝ) :
    HasDerivAt (fun r => traceGRes K η t (Function.update x j r))
      (gueDir t j * gradMat K η (gueLin t (Function.update x j s))).trace s := by
  set y := Function.update x j s
  set R := res K η (gueLin t y)
  have hG : ∀ a b, HasDerivAt (fun r => gueLin t (Function.update x j r) a b) (gueDir t j a b) s := by
    intro a b
    have e : (fun r => gueLin t (Function.update x j r) a b) =
        fun r => gueLin t x a b + ((r - x j : ℝ) : ℂ) * gueDir t j a b := by
      funext r; rw [gueLin_update]; simp
    rw [e]
    have := ((((hasDerivAt_id s).sub_const (x j)).ofReal_comp).mul_const (gueDir t j a b)).const_add
      (gueLin t x a b)
    simpa using this
  have h : HasDerivAt (fun r => ∑ a, ∑ b, gueLin t (Function.update x j r) a b *
      res K η (gueLin t (Function.update x j r)) b a)
      (∑ a, ∑ b, (gueDir t j a b * R b a + gueLin t y a b * (-(R * gueDir t j * R)) b a)) s :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ =>
      (hG a b).mul (hasDerivAt_res_line hK hη t x j s b a)
  have e1 : (fun r => traceGRes K η t (Function.update x j r)) = fun r => ∑ a, ∑ b,
      gueLin t (Function.update x j r) a b * res K η (gueLin t (Function.update x j r)) b a := by
    funext r; simp [traceGRes, Matrix.trace, Matrix.mul_apply]
  have e2 : (gueDir t j * gradMat K η (gueLin t y)).trace =
      ∑ a, ∑ b, (gueDir t j a b * R b a + gueLin t y a b * (-(R * gueDir t j * R)) b a) := by
    have h1 : (gueDir t j * gradMat K η (gueLin t y)).trace =
        (gueDir t j * R).trace + (gueLin t y * (-(R * gueDir t j * R))).trace := by
      rw [gradMat, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_neg, Matrix.trace_neg,
        sub_eq_add_neg]
      congr 2
      rw [show gueDir t j * (R * gueLin t y * R) = (gueDir t j * R) * (gueLin t y * R) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
        show gueLin t y * R * (gueDir t j * R) = gueLin t y * (R * gueDir t j * R) by
          simp only [Matrix.mul_assoc]]
    rw [h1]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ← Finset.sum_add_distrib]
  rw [e1, e2]; exact h

theorem fderiv_traceGRes {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) (x : GCoord ι → ℝ) (j : GCoord ι) :
    fderiv ℝ (traceGRes K η t) x (Pi.single j 1) =
      (gueDir t j * gradMat K η (gueLin t x)).trace := by
  have hd : DifferentiableAt ℝ (traceGRes K η t) x :=
    ((contDiff_traceGRes hK hη t (n := 1)).differentiable one_ne_zero) x
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (x j) (hasDerivAt_update x j (x j))
    (Function.update_eq_self _ _).symm
  have h2 := hasDerivAt_traceGRes_line hK hη t x j (x j)
  rw [Function.update_eq_self] at h2
  exact h1.unique h2

theorem star_gueDir_apply (t : ℝ≥0) (j : GCoord ι) (a b : ι) :
    star (gueDir t j a b) = gueDir t j b a := by
  have h := isHermitian_gueLin t (Pi.single j 1)
  have := congrFun (congrFun h b) a
  simpa [Matrix.conjTranspose_apply, gueDir] using this

/-- `Σ_j |Tr(E_j B)|² = t Σ_{ab} |B_ab|²`. -/
theorem sum_norm_sq_trace_gueDir (t : ℝ≥0) (B : Matrix ι ι ℂ) :
    ∑ j, ‖(gueDir t j * B).trace‖ ^ 2 = (t : ℝ) * ∑ a, ∑ b, ‖B a b‖ ^ 2 := by
  have hz : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = z * star z := fun z => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  apply Complex.ofReal_injective
  push_cast
  simp only [hz]
  have htr : ∀ j, (gueDir t j * B).trace = ∑ a, ∑ b, gueDir t j a b * B b a := fun j => by
    simp [Matrix.trace, Matrix.mul_apply]
  have hst : ∀ j, star (gueDir t j * B).trace = ∑ c, ∑ d, gueDir t j d c * star (B d c) := by
    intro j
    rw [htr, star_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [star_mul', star_gueDir_apply]
  simp only [hst]
  simp only [htr]
  simp only [Finset.sum_mul_sum]
  have h1 : ∀ a b c d, ∑ j, gueDir t j a b * B b a * (gueDir t j d c * star (B d c)) =
      (if a = c ∧ b = d then (t : ℂ) else 0) * (B b a * star (B d c)) := by
    intro a b c d
    rw [← sum_gueDir_mul_gueDir t a b d c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, ∑ a, ∑ c, ∑ b, ∑ d, gueDir t j a b * B b a * (gueDir t j d c * star (B d c)) =
      ∑ a, ∑ c, ∑ b, ∑ d, ∑ j, gueDir t j a b * B b a * (gueDir t j d c * star (B d c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
  rw [h2]
  simp only [h1]
  rw [show ∑ a, ∑ b, B a b * star (B a b) = ∑ a, ∑ b, B b a * star (B b a) from
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single a (fun c hc => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero
    fun d _ => by rw [ite_eq_right (fun h => hc h.1.symm), zero_mul]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_eq_single b (fun d hd => by rw [ite_eq_right (fun h => hd h.2.symm), zero_mul])]
  simp only [and_self, ite_true]

/-- Hilbert–Schmidt norm `(Σ|B_ab|²)^{1/2}`. -/
def hsNorm (B : Matrix ι ι ℂ) : ℝ := Real.sqrt (∑ a, ∑ b, ‖B a b‖ ^ 2)

/-- **The gradient of `Tr G R`**: `|∇_x Tr(G R)| = √t ‖R - RGR‖_HS` in the
standard real coordinates. -/
theorem weightedGradientNorm_traceGRes {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ}
    (hη : η ≠ 0) (t : ℝ≥0) (x : GCoord ι → ℝ) :
    BlockBand.Internal.Contracts.Inputs.weightedGradientNorm (fun _ => (1 : ℝ≥0))
        (traceGRes K η t) x =
      Real.sqrt t * hsNorm (gradMat K η (gueLin t x)) := by
  unfold BlockBand.Internal.Contracts.Inputs.weightedGradientNorm hsNorm
  simp only [NNReal.coe_one, one_mul, fderiv_traceGRes hK hη t x, sum_norm_sq_trace_gueDir]
  rw [Real.sqrt_mul (NNReal.coe_nonneg t)]

theorem norm_gueLin_apply_le (t : ℝ≥0) (x : GCoord ι → ℝ) (a b : ι) :
    ‖gueLin t x a b‖ ≤ 2 * Real.sqrt t * ∑ k, |x k| := by
  have hk : ∀ k, |x k| ≤ ∑ k, |x k| := fun k =>
    Finset.single_le_sum (f := fun k => |x k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  rw [gueLin_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h4 : ‖((x ((a, b), 0) : ℂ) + (x ((a, b), 1) : ℂ) * Complex.I +
      ((x ((b, a), 0) : ℂ) - (x ((b, a), 1) : ℂ) * Complex.I))‖ ≤ 4 * ∑ k, |x k| := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) (norm_sub_le _ _)).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    linarith [hk ((a, b), 0), hk ((a, b), 1), hk ((b, a), 0), hk ((b, a), 1)]
  calc Real.sqrt t / 2 * ‖_‖ ≤ Real.sqrt t / 2 * (4 * ∑ k, |x k|) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 * Real.sqrt t * ∑ k, |x k| := by ring

theorem memLp_sum_abs_coord (q : ℝ≥0) :
    MemLp (fun x : GCoord ι → ℝ => ∑ k, |x k|) q (stdGauss ι) := by
  refine memLp_finsetSum (f := fun k (x : GCoord ι → ℝ) => |x k|) _ fun k _ => ?_
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) q).norm.comp_measurePreserving
    (measurePreserving_eval (fun _ : GCoord ι => gaussianReal 0 1) k)
  simp only [Function.comp_def, id, Real.norm_eq_abs] at h
  exact h

theorem memLp_traceGRes {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) (q : ℝ≥0) : MemLp (traceGRes K η t) q (stdGauss ι) := by
  have hb : ∀ x, ‖traceGRes K η t x‖ ≤ ((Fintype.card ι : ℝ) ^ 2 *
      ((Fintype.card ι : ℝ) ^ 2 * (2 * Real.sqrt t)) * |η|⁻¹) * ∑ k, |x k| := by
    intro x
    have h1 := norm_trace_mul_le (gueLin t x) (res K η (gueLin t x))
      (fun a b => norm_res_apply_le (hK.add (isHermitian_gueLin t x)) hη a b)
    have h2 : ∑ a, ∑ b, ‖gueLin t x a b‖ ≤
        (Fintype.card ι : ℝ) ^ 2 * (2 * Real.sqrt t * ∑ k, |x k|) := by
      refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        norm_gueLin_apply_le t x a b).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    refine h1.trans ?_
    have hη0 : 0 ≤ |η|⁻¹ := inv_nonneg.mpr (abs_nonneg η)
    calc (Fintype.card ι : ℝ) ^ 2 * ((∑ a, ∑ b, ‖gueLin t x a b‖) * |η|⁻¹)
        ≤ (Fintype.card ι : ℝ) ^ 2 * (((Fintype.card ι : ℝ) ^ 2 *
            (2 * Real.sqrt t * ∑ k, |x k|)) * |η|⁻¹) := by gcongr
      _ = _ := by ring
  exact ((memLp_sum_abs_coord q).const_mul _).mono'
    (contDiff_traceGRes hK hη t (n := 0)).continuous.aestronglyMeasurable (ae_of_all _ hb)

/-- **Gaussian `L^p` Poincaré for `Tr G R`**, from `Inputs.GaussianLpGradient`: one absolute
`C₀ > 0` such that for every `p ≥ 1`, finite `ι`, Hermitian `K`, `η ≠ 0` and `t`, in the
standard coordinates of `G ~ GUE_ι(t)`, `‖X - E X‖_p ≤ C₀ √p ‖√t ‖R - RGR‖_HS‖_p`,
`X = Tr(G R)`. -/
theorem traceGRes_concentration (hLp : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p : ℝ, 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (K : Matrix ι ι ℂ), K.IsHermitian → ∀ η : ℝ, η ≠ 0 → ∀ t : ℝ≥0,
        eLpNorm (fun x => traceGRes K η t x - ∫ y, traceGRes K η t y ∂stdGauss ι)
            (ENNReal.ofReal p) (stdGauss ι) ≤
          ENNReal.ofReal (C₀ * Real.sqrt p) *
            eLpNorm (fun x => Real.sqrt t * hsNorm (gradMat K η (gueLin t x)))
              (ENNReal.ofReal p) (stdGauss ι) := by
  obtain ⟨C₀, hC₀, h⟩ := hLp
  refine ⟨C₀, hC₀, fun p hp ι _ _ K hK η hη t => ?_⟩
  have hm : MemLp (traceGRes K η t) (ENNReal.ofReal p) (stdGauss ι) := by
    have := memLp_traceGRes hK hη t (Real.toNNReal p)
    simpa [ENNReal.ofReal] using this
  have := h p hp (GCoord ι) (fun _ => (1 : ℝ≥0)) (traceGRes K η t)
    (contDiff_traceGRes hK hη t) hm
  have he : BlockBand.Internal.Contracts.Inputs.weightedGradientNorm
      (fun _ => (1 : ℝ≥0)) (traceGRes K η t) =
      fun x => Real.sqrt t * hsNorm (gradMat K η (gueLin t x)) :=
    funext fun x => weightedGradientNorm_traceGRes hK hη t x
  rw [he] at this
  exact this

end BlockBand.DeterminantScore.SelectedIBP
