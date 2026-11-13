module

public import BlockBand.Angular.ConeDivergence
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Divergence identity on `ℂ^d` under the circular Gaussian law

For a vector field `Y : ℂ^ι → ℂ^ι` that is real-differentiable off the origin, tangent
(`Re Σ_a conj(z_a) Y_a(z) = 0`), with linear growth and bounded derivative, the real ambient
divergence `div Y = Σ_a Re ∂_{x_a} Y_a + Im ∂_{x_a} (I·) Y_a` (the trace of the real derivative)
has mean zero under the standard circular Gaussian law `CoareaPalm.circularVectorLaw`
(`integral_realDivergence_eq_zero`). For integrands invariant under positive real scaling,
the circular Gaussian mean equals the projective Haar mean `CoareaPalm.projectiveHaar`
(`integral_projectiveHaar_eq_of_scaleInvariant`): this is how sphere integrations by parts of
the paper are realized (degree-zero angular functions times degree-one tangent fields).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.ConeDivergence

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The complex vector with real coordinates `r (a,0)`, `r (a,1)`. -/
def toComplexVec (r : ι × Fin 2 → ℝ) : ι → ℂ :=
  fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I

/-- The real ambient divergence of a vector field on `ℂ^ι`, the trace of its real
derivative in the real basis `e_a, I e_a`. -/
def realDivergence (Y : (ι → ℂ) → (ι → ℂ)) (z : ι → ℂ) : ℝ :=
  ∑ a, ((fderiv ℝ Y z (Pi.single a 1) a).re + (fderiv ℝ Y z (Pi.single a Complex.I) a).im)

/-- The real basis direction attached to a real coordinate. -/
def coordDir : ι × Fin 2 → (ι → ℂ)
  | (a, k) => if k = 0 then Pi.single a 1 else Pi.single a Complex.I

/-- Real component `c` of a complex vector. -/
def realComp (w : ι → ℂ) : ι × Fin 2 → ℝ
  | (a, k) => if k = 0 then (w a).re else (w a).im

theorem measurable_toComplexVec : Measurable (toComplexVec (ι := ι)) := by
  apply Measurable.of_eval
  intro a
  exact (Complex.measurable_ofReal.comp (measurable_pi_apply (a, 0))).add
    ((Complex.measurable_ofReal.comp (measurable_pi_apply (a, 1))).mul_const _)

theorem toComplexVec_update (r : ι × Fin 2 → ℝ) (c : ι × Fin 2) (t : ℝ) :
    toComplexVec (Function.update r c t) = toComplexVec r + (t - r c) • coordDir c := by
  obtain ⟨a, k⟩ := c
  funext b
  simp only [toComplexVec, coordDir, Pi.add_apply, Pi.smul_apply]
  fin_cases k
  · by_cases hb : b = a
    · subst hb
      simp [Function.update_self, Function.update_of_ne, Complex.ext_iff]
    · simp [Function.update_of_ne, hb]
  · by_cases hb : b = a
    · subst hb
      simp [Function.update_self, Function.update_of_ne, Complex.ext_iff]
    · simp [Function.update_of_ne, hb]

theorem sum_realComp_mul (r : ι × Fin 2 → ℝ) (w : ι → ℂ) :
    (∑ c, r c * realComp w c) =
      (∑ a, starRingEnd ℂ (toComplexVec r a) * w a).re := by
  rw [Complex.re_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp [Fin.sum_univ_two, realComp, toComplexVec, Complex.mul_re]

theorem sum_realComp_fderiv (Y : (ι → ℂ) → (ι → ℂ)) (z : ι → ℂ) :
    (∑ c, realComp (fderiv ℝ Y z (coordDir c)) c) = realDivergence Y z := by
  rw [Fintype.sum_prod_type, realDivergence]
  apply Finset.sum_congr rfl
  intro a _
  simp [Fin.sum_univ_two, realComp, coordDir]

/-- The circular Gaussian law is the image of the real product law. -/
theorem circularVectorLaw_eq :
    circularVectorLaw ι =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map toComplexVec := rfl

/-- `realComp · c` as a continuous real-linear functional. -/
def realCompCLM (c : ι × Fin 2) : (ι → ℂ) →L[ℝ] ℝ :=
  (if c.2 = 0 then Complex.reCLM else Complex.imCLM).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) c.1)

theorem realCompCLM_apply (c : ι × Fin 2) (w : ι → ℂ) : realCompCLM c w = realComp w c := by
  obtain ⟨a, k⟩ := c
  fin_cases k <;> simp [realCompCLM, realComp]

theorem abs_realComp_le (w : ι → ℂ) (c : ι × Fin 2) : |realComp w c| ≤ ‖w‖ := by
  obtain ⟨a, k⟩ := c
  have h := norm_le_pi_norm w a
  fin_cases k
  · simpa [realComp] using (Complex.abs_re_le_norm (w a)).trans h
  · simpa [realComp] using (Complex.abs_im_le_norm (w a)).trans h

theorem norm_coordDir (c : ι × Fin 2) : ‖coordDir c‖ = 1 := by
  obtain ⟨a, k⟩ := c
  fin_cases k <;> simp [coordDir, Pi.norm_single]

theorem norm_toComplexVec_le (r : ι × Fin 2 → ℝ) : ‖toComplexVec r‖ ≤ ∑ j, |r j| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun a => ?_
  calc ‖toComplexVec r a‖ ≤ ‖(r (a, 0) : ℂ)‖ + ‖(r (a, 1) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |r (a, 0)| + |r (a, 1)| := by simp
    _ ≤ ∑ j, |r j| := by
      have h01 : ((a, 0) : ι × Fin 2) ≠ (a, 1) := by simp
      rw [← Finset.sum_pair (f := fun j => |r j|) h01]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        (fun j _ _ => abs_nonneg _)

theorem toComplexVec_eq_zero {r : ι × Fin 2 → ℝ} (h : toComplexVec r = 0) : r = 0 := by
  funext ⟨a, k⟩
  have ha := congrFun h a
  simp only [toComplexVec, Pi.zero_apply, Complex.ext_iff, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
    Complex.mul_im, Complex.zero_re, Complex.zero_im] at ha
  fin_cases k <;> simp_all

/-- Coordinates are integrable under the real Gaussian product law. -/
theorem integrable_coord (v : ℝ≥0) (j : ι × Fin 2) :
    Integrable (fun r : ι × Fin 2 → ℝ => r j) (Measure.pi fun _ => gaussianReal 0 v) := by
  have h := (measurePreserving_eval (fun _ : ι × Fin 2 => gaussianReal 0 v) j)
  exact h.integrable_comp_of_integrable ((memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable
    le_rfl)

theorem integrable_coord_mul (v : ℝ≥0) (i j : ι × Fin 2) :
    Integrable (fun r : ι × Fin 2 → ℝ => r i * r j) (Measure.pi fun _ => gaussianReal 0 v) := by
  have hm : ∀ k, MemLp (fun r : ι × Fin 2 → ℝ => r k) 2 (Measure.pi fun _ => gaussianReal 0 v) := by
    intro k
    have h := (measurePreserving_eval (fun _ : ι × Fin 2 => gaussianReal 0 v) k)
    exact (memLp_id_gaussianReal (μ := 0) (v := v) 2).comp_measurePreserving h
  exact (hm j).integrable_mul (hm i) |>.congr (ae_of_all _ fun r => by simp [mul_comm])

/-- **Divergence identity on `ℂ^ι`.** Under the standard circular Gaussian law
(density `π^{-d} e^{-‖z‖²}`), for a measurable vector field that is real-differentiable off
the origin with `‖Y z‖ ≤ C‖z‖` and `‖DY‖ ≤ C`:
`E[div Y] = 2 E[Re Σ_a conj(z_a) Y_a(z)]`. -/
theorem integral_realDivergence_eq [Nonempty ι] (Y : (ι → ℂ) → (ι → ℂ)) (C : ℝ)
    (hY : Measurable Y) (hdiff : ∀ z, z ≠ 0 → DifferentiableAt ℝ Y z)
    (hgrowth : ∀ z, ‖Y z‖ ≤ C * ‖z‖) (hbound : ∀ z, z ≠ 0 → ‖fderiv ℝ Y z‖ ≤ C) :
    (∫ z, realDivergence Y z ∂circularVectorLaw ι) =
      2 * ∫ z, (∑ a, starRingEnd ℂ (z a) * Y z a).re ∂circularVectorLaw ι := by
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  have : Nontrivial (ι × Fin 2) := ⟨⟨(a₀, 0), (a₀, 1), by simp⟩⟩
  set γ : Measure (ι × Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 (1 / 2 : ℝ≥0) with hγ
  have hdivm : Measurable (realDivergence Y) := by
    unfold realDivergence
    refine Finset.measurable_sum _ fun a _ => ?_
    exact ((Complex.measurable_re.comp ((measurable_pi_apply a).comp
      (measurable_fderiv_apply_const ℝ Y _))).add
      (Complex.measurable_im.comp ((measurable_pi_apply a).comp
      (measurable_fderiv_apply_const ℝ Y _))))
  rw [circularVectorLaw_eq, integral_map measurable_toComplexVec.aemeasurable
    hdivm.aestronglyMeasurable]
  set f : ι × Fin 2 → (ι × Fin 2 → ℝ) → ℝ := fun c r => realComp (Y (toComplexVec r)) c
  set f' : ι × Fin 2 → (ι × Fin 2 → ℝ) → ℝ :=
    fun c r => realComp (fderiv ℝ Y (toComplexVec r) (coordDir c)) c
  have hmf : ∀ c, Measurable (f c) := fun c => by
    have := (realCompCLM c).continuous.measurable.comp (hY.comp measurable_toComplexVec)
    convert this using 1
    funext r; simp [realCompCLM_apply, f]
  have hmf' : ∀ c, Measurable (f' c) := fun c => by
    have := (realCompCLM c).continuous.measurable.comp
      ((measurable_fderiv_apply_const ℝ Y (coordDir c)).comp measurable_toComplexVec)
    convert this using 1
    funext r; simp [realCompCLM_apply, f']
  have hsum : ∀ r, realDivergence Y (toComplexVec r) = ∑ c, f' c r :=
    fun r => (sum_realComp_fderiv Y (toComplexVec r)).symm
  simp_rw [hsum]
  rw [integral_finsetSum _ ?_]
  rotate_left
  · intro c _
    exact (integrable_const C).mono'
      (hmf' c).aestronglyMeasurable
      (by
        filter_upwards [ae_coord_ne_zero (fun _ : ι × Fin 2 => (1 / 2 : ℝ≥0)) (a₀, 0)
          (by norm_num)] with r hr
        have hz : toComplexVec r ≠ 0 := fun h => hr (by rw [toComplexVec_eq_zero h]; rfl)
        rw [Real.norm_eq_abs]
        calc |f' c r| ≤ ‖fderiv ℝ Y (toComplexVec r) (coordDir c)‖ := abs_realComp_le _ _
          _ ≤ ‖fderiv ℝ Y (toComplexVec r)‖ * ‖coordDir c‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ C := by rw [norm_coordDir, mul_one]; exact hbound _ hz)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound (Pi.single a₀ 1)
    (by simp))
  have hsumabs : Integrable (fun r : ι × Fin 2 → ℝ => ∑ j, |r j|) γ :=
    integrable_finsetSum _ fun j _ => (integrable_coord _ j).abs
  have hrhs : (∫ z, (∑ a, starRingEnd ℂ (z a) * Y z a).re ∂(Measure.map toComplexVec γ)) =
      ∫ r, ∑ c, r c * f c r ∂γ := by
    have hm : Measurable (fun z : ι → ℂ => (∑ a, starRingEnd ℂ (z a) * Y z a).re) :=
      Complex.measurable_re.comp (Finset.measurable_sum _ fun a _ =>
        ((Complex.continuous_conj.measurable.comp (measurable_pi_apply a)).mul
          ((measurable_pi_apply a).comp hY)))
    rw [integral_map measurable_toComplexVec.aemeasurable hm.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun r => (sum_realComp_mul r _).symm)
  rw [hrhs]
  have key := integral_sum_partial_eq (κ := ι × Fin 2) (1 / 2 : ℝ≥0) (by norm_num) f f' ?_ ?_ ?_ ?_
  · rw [key, hγ]; norm_num
  · intro c r hr
    have hz : toComplexVec r ≠ 0 := fun h => hr (toComplexVec_eq_zero h)
    have hD := (hdiff _ hz).hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => toComplexVec r + (t - r c) • coordDir c)
        (coordDir c) (r c) := by
      have := ((hasDerivAt_id (r c)).sub_const (r c)).smul_const (coordDir c)
      simpa using this.const_add (toComplexVec r)
    have hD' : HasFDerivAt Y (fderiv ℝ Y (toComplexVec r))
        (toComplexVec r + (r c - r c) • coordDir c) := by simpa using hD
    have hcomp := hD'.comp_hasDerivAt (r c) hline
    have := (realCompCLM c).hasFDerivAt.comp_hasDerivAt (r c) hcomp
    simp only [f, f']
    convert this using 1
    · funext t
      simp [toComplexVec_update, realCompCLM_apply]
    · simp [realCompCLM_apply]
  · intro c
    refine (hsumabs.const_mul C).mono'
      (hmf c).aestronglyMeasurable
      (ae_of_all _ fun r => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_realComp_le _ _).trans ((hgrowth _).trans
      (mul_le_mul_of_nonneg_left (norm_toComplexVec_le r) hC))
  · intro c
    exact (integrable_const C).mono'
      (hmf' c).aestronglyMeasurable
      (by
        filter_upwards [ae_coord_ne_zero (fun _ : ι × Fin 2 => (1 / 2 : ℝ≥0)) (a₀, 0)
          (by norm_num)] with r hr
        have hz : toComplexVec r ≠ 0 := fun h => hr (by rw [toComplexVec_eq_zero h]; rfl)
        rw [Real.norm_eq_abs]
        calc |f' c r| ≤ ‖fderiv ℝ Y (toComplexVec r) (coordDir c)‖ := abs_realComp_le _ _
          _ ≤ ‖fderiv ℝ Y (toComplexVec r)‖ * ‖coordDir c‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ C := by rw [norm_coordDir, mul_one]; exact hbound _ hz)
  · intro c
    have hint : Integrable (fun r : ι × Fin 2 → ℝ => C * ∑ j, |r c * r j|) γ :=
      (integrable_finsetSum _ fun j _ => (integrable_coord_mul _ c j).abs).const_mul C
    refine hint.mono' (((measurable_pi_apply c).mul (hmf c)).aestronglyMeasurable)
      (ae_of_all _ fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |f c r| ≤ C * ∑ j, |r j| :=
      (abs_realComp_le _ _).trans ((hgrowth _).trans
        (mul_le_mul_of_nonneg_left (norm_toComplexVec_le r) hC))
    calc |r c| * |f c r| ≤ |r c| * (C * ∑ j, |r j|) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = C * ∑ j, |r c * r j| := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; rw [abs_mul]; ring

/-- Tangent fields (`Re Σ_a conj(z_a) Y_a(z) = 0`) have divergence of mean zero. -/
theorem integral_realDivergence_eq_zero [Nonempty ι] (Y : (ι → ℂ) → (ι → ℂ)) (C : ℝ)
    (hY : Measurable Y) (hdiff : ∀ z, z ≠ 0 → DifferentiableAt ℝ Y z)
    (htan : ∀ z, (∑ a, starRingEnd ℂ (z a) * Y z a).re = 0)
    (hgrowth : ∀ z, ‖Y z‖ ≤ C * ‖z‖) (hbound : ∀ z, z ≠ 0 → ‖fderiv ℝ Y z‖ ≤ C) :
    (∫ z, realDivergence Y z ∂circularVectorLaw ι) = 0 := by
  rw [integral_realDivergence_eq Y C hY hdiff hgrowth hbound]
  simp [htan]

theorem measurable_l2Norm : Measurable (l2Norm (ι := ι)) := by
  unfold l2Norm
  exact (Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).norm.pow_const 2)).sqrt

/-- Almost surely the circular Gaussian vector is nonzero. -/
theorem ae_circular_ne_zero [Nonempty ι] : ∀ᵐ g ∂circularVectorLaw ι, g ≠ 0 := by
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  rw [circularVectorLaw_eq]
  have hs : MeasurableSet {g : ι → ℂ | g ≠ 0} :=
    (measurableSet_singleton (0 : ι → ℂ)).compl
  rw [ae_map_iff measurable_toComplexVec.aemeasurable hs]
  filter_upwards [ae_coord_ne_zero (fun _ : ι × Fin 2 => (1 / 2 : ℝ≥0)) (a₀, 0) (by norm_num)]
    with r hr hz
  exact hr (by rw [toComplexVec_eq_zero hz]; rfl)

theorem l2Norm_pos {g : ι → ℂ} (hg : g ≠ 0) : 0 < l2Norm g := by
  unfold l2Norm
  apply Real.sqrt_pos.2
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hg
  exact lt_of_lt_of_le (by positivity : 0 < ‖g k‖ ^ 2)
    (Finset.single_le_sum (f := fun k => ‖g k‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ k))

/-- **Projective Haar averages of scale-invariant integrands.** If `F` is Borel and
invariant under positive real scaling, its projective Haar mean equals its circular
Gaussian mean (`ν_d` is the law of `g/‖g‖`). -/
theorem integral_projectiveHaar_eq_of_scaleInvariant [Nonempty ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (F : (ι → ℂ) → E) (hF : Measurable F)
    (hinv : ∀ z (r : ℝ), 0 < r → F ((r : ℂ) • z) = F z) :
    (∫ z, F z ∂projectiveHaar ι) = ∫ z, F z ∂circularVectorLaw ι := by
  have hN : Measurable (fun g : ι → ℂ => ((l2Norm g)⁻¹ : ℂ) • g) := by
    have h1 : Measurable (fun g : ι → ℂ => ((l2Norm g)⁻¹ : ℂ)) :=
      (Complex.measurable_ofReal.comp measurable_l2Norm).inv
    exact h1.smul measurable_id
  unfold projectiveHaar
  rw [integral_map hN.aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_circular_ne_zero] with g hg
  have := hinv g (l2Norm g)⁻¹ (inv_pos.2 (l2Norm_pos hg))
  simpa using this

end BlockBand.Angular.ConeDivergence
