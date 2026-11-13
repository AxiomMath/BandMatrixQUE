module

public import Mathlib
public import BlockBand.Wegner.PoissonRepresentationMatrix
public import BlockBand.Wegner.PassiveLogCore.AbsorberRegulatorLimit

/-!
# Regulated Cauchy formula for the partial-absorber log

With a regulator `η > 0` and `L_η(ζ; s) = ½ log|det(X + ζY + isQ + iη)|²`, the increment
`L_η(ζ; a) - L_η(ζ; 0)` is the `s`-integral of a bounded score; the Poisson representation of the
score in `ζ` gives `π [L_η(i; a) - L_η(i; 0)] = ∫ (1+t²)⁻¹ [L_η(t; a) - L_η(t; 0)] dt`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open Matrix MeasureTheory Set
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

namespace PassiveLogCauchy

omit [DecidableEq n] in
/-- Adding `i P` with `P ⪰ 0` keeps the imaginary margin. -/
theorem hasImMargin_add_I_smul {η : ℝ} {N P : Matrix n n ℂ} (h : HasImMargin η N)
    (hP : P.PosSemidef) : HasImMargin η (N + Complex.I • P) := by
  intro v
  have h0 := hP.dotProduct_mulVec_nonneg v
  have hre : 0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re := (Complex.nonneg_iff.mp h0).1
  have hv := h v
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, Complex.add_im,
    smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- The score `-Im Tr[Q (X + isQ + ζY + iη)⁻¹]`. -/
def score (X Y Q : Matrix n n ℂ) (η s : ℝ) (ζ : ℂ) : ℝ :=
  -(resolventTrace Q (X + Complex.I • (s • Q)) Y η ζ).im

/-- For `s ≥ 0`, `Im ζ ≥ 0` the pencil `X + isQ + ζY + iη` has imaginary margin `η`. -/
theorem hasImMargin_pencil {X Y Q : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef)
    (hQ : Q.PosSemidef) (η : ℝ) {s : ℝ} (hs : 0 ≤ s) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    HasImMargin η (absorbedPencil (X + Complex.I • (s • Q)) Y η ζ) := by
  have h := hasImMargin_add_I_smul (hasImMargin_absorbedPencil hX hY η hζ) (hQ.smul hs)
  convert h using 1
  unfold absorbedPencil
  abel

/-- The score is bounded by `η⁻¹ Σ_{ab} |Q_ab|` on `s ≥ 0`, `Im ζ ≥ 0`. -/
theorem abs_score_le {X Y Q : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) {s : ℝ} (hs : 0 ≤ s) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    |score X Y Q η s ζ| ≤ (∑ a, ∑ b, ‖Q a b‖) * η⁻¹ := by
  unfold score
  rw [abs_neg]
  exact (Complex.abs_im_le_norm _).trans
    ((hasImMargin_pencil hX hY hQ η hs hζ).norm_trace_mul_inv_le hη Q)

/-- Joint Borel measurability of the score in `(s, ζ)`. -/
theorem measurable_score (X Y Q : Matrix n n ℂ) (η : ℝ) :
    Measurable (fun p : ℝ × ℂ => score X Y Q η p.1 p.2) := by
  have hP : Continuous (fun p : ℝ × ℂ => absorbedPencil (X + Complex.I • (p.1 • Q)) Y η p.2) := by
    unfold absorbedPencil
    fun_prop
  have hT : Continuous (fun B : Matrix n n ℂ => -(Q * B).trace.im) := by
    fun_prop
  exact hT.measurable.comp (measurable_matrix_inv.comp hP.measurable)

/-- Poisson representation of the score at fixed `s ≥ 0`. -/
theorem poisson_score {X Y Q : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹ * score X Y Q η s t) ∧
      ∫ t : ℝ, (1 + t ^ 2)⁻¹ * score X Y Q η s t = Real.pi * score X Y Q η s Complex.I := by
  have hP := poisson_upperHalfPlane_im (f := resolventTrace Q (X + Complex.I • (s • Q)) Y η)
    (M := (∑ a, ∑ b, ‖Q a b‖) * η⁻¹)
    (fun _ hz => differentiableAt_resolventTrace _ _ _ _
      ((hasImMargin_pencil hX hY hQ η hs hz).isUnit hη))
    (fun _ hz => (hasImMargin_pencil hX hY hQ η hs hz).norm_trace_mul_inv_le hη Q)
  refine ⟨?_, ?_⟩
  · simpa [score, mul_neg] using hP.1.neg
  · simp only [score, mul_neg, integral_neg, hP.2]

/-- The Jacobi score of the log path is `-Im Tr[Q M⁻¹]`. -/
theorem jacobi_re_eq (M Q : Matrix n n ℂ) :
    ((M⁻¹ * (Complex.I • Q)).trace).re = -((Q * M⁻¹).trace).im := by
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_comm, smul_eq_mul, Complex.I_mul_re]

omit [Fintype n] in

/-- The absorber matrix at real background `X + tY` is the pencil at `ζ = t`. -/
theorem regulatedAbsorberMatrix_real (X Y Q : Matrix n n ℂ) (η s t : ℝ) :
    PassiveLogCore.regulatedAbsorberMatrix (X + (t : ℂ) • Y) 0 Q η s =
      absorbedPencil (X + Complex.I • (s • Q)) Y η (t : ℂ) := by
  ext i j
  simp [PassiveLogCore.regulatedAbsorberMatrix, absorbedPencil]
  ring

omit [Fintype n] in

/-- The absorber matrix with base absorber `Y` is the pencil at `ζ = i`. -/
theorem regulatedAbsorberMatrix_imag (X Y Q : Matrix n n ℂ) (η s : ℝ) :
    PassiveLogCore.regulatedAbsorberMatrix X Y Q η s =
      absorbedPencil (X + Complex.I • (s • Q)) Y η Complex.I := by
  ext i j
  simp [PassiveLogCore.regulatedAbsorberMatrix, absorbedPencil]
  ring

/-- The score is interval integrable in `s ∈ [0, a]` (bounded and measurable). -/
theorem intervalIntegrable_score {X Y Q : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.PosSemidef) (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 ≤ a)
    {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    IntervalIntegrable (fun s => score X Y Q η s ζ) volume 0 a := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
  refine Measure.integrableOn_of_bounded (M := (∑ a, ∑ b, ‖Q a b‖) * η⁻¹)
    (by simp) ?_ ?_
  · exact ((measurable_score X Y Q η).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs]
    exact abs_score_le hX hY hQ hη hs.1.le hζ

/-- Fundamental theorem of calculus along an absorber path whose Jacobi score is given. -/
theorem logPath_sub_eq_integral {A Γ Q : Matrix n n ℂ} (hA : A.IsHermitian)
    (hΓ : Γ.PosSemidef) (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 ≤ a)
    (g : ℝ → ℝ)
    (hg : ∀ s, 0 ≤ s → ((PassiveLogCore.regulatedAbsorberMatrix A Γ Q η s)⁻¹ *
      (Complex.I • Q)).trace.re = g s)
    (hgi : IntervalIntegrable g volume 0 a) :
    PassiveLogCore.regulatedAbsorberLogPath A Γ Q η a - PassiveLogCore.regulatedAbsorberLogPath A Γ Q η 0 =
      ∫ s in (0 : ℝ)..a, g s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := PassiveLogCore.regulatedAbsorberLogPath A Γ Q η)]
  · intro s hs
    rw [uIcc_of_le ha] at hs
    rw [← hg s hs.1]
    exact PassiveLogCore.hasDerivAt_regulatedAbsorberLogPath A Γ Q hA hΓ hQ hη hs.1
  · exact hgi

/-- Real-background increment as an `s`-integral of the score. -/
theorem realIncrement_eq_integral {X Y Q : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.PosSemidef) (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 ≤ a)
    (t : ℝ) :
    PassiveLogCore.regulatedPassiveLogIncrement (X + (t : ℂ) • Y) Q η a =
      ∫ s in (0 : ℝ)..a, score X Y Q η s t := by
  have hXt : (X + (t : ℂ) • Y).IsHermitian :=
    hX.add (hY.1.smul (by simp [IsSelfAdjoint]))
  exact logPath_sub_eq_integral hXt Matrix.PosSemidef.zero hQ hη ha
    (fun s => score X Y Q η s t)
    (fun s _ => by rw [jacobi_re_eq, regulatedAbsorberMatrix_real]; rfl)
    (intervalIntegrable_score hX hY hQ hη ha (by simp))

/-- Imaginary-background (`ζ = i`) increment as an `s`-integral of the score. -/
theorem imagIncrement_eq_integral {X Y Q : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.PosSemidef) (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 ≤ a) :
    PassiveLogCore.regulatedAbsorberLogPath X Y Q η a - PassiveLogCore.regulatedAbsorberLogPath X Y Q η 0 =
      ∫ s in (0 : ℝ)..a, score X Y Q η s Complex.I :=
  logPath_sub_eq_integral hX hY hQ hη ha (fun s => score X Y Q η s Complex.I)
    (fun s _ => by rw [jacobi_re_eq, regulatedAbsorberMatrix_imag]; rfl)
    (intervalIntegrable_score hX hY hQ hη ha (by simp))

/-- The regulated Cauchy formula (deterministic): `X` Hermitian, `Y, Q ⪰ 0`, `η > 0`,
`a ≥ 0`, with `L_η(ζ; s) = ½ log|det(X + ζY + isQ + iη)|²`:
`t ↦ (1+t²)⁻¹ [L_η(t; a) - L_η(t; 0)]` is Lebesgue integrable and
`π [L_η(i; a) - L_η(i; 0)] = ∫ (1+t²)⁻¹ [L_η(t; a) - L_η(t; 0)] dt`. -/
theorem regulated_cauchy {X Y Q : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun t : ℝ =>
        (1 + t ^ 2)⁻¹ * PassiveLogCore.regulatedPassiveLogIncrement (X + (t : ℂ) • Y) Q η a) ∧
      Real.pi * (PassiveLogCore.regulatedAbsorberLogPath X Y Q η a -
          PassiveLogCore.regulatedAbsorberLogPath X Y Q η 0) =
        ∫ t : ℝ, (1 + t ^ 2)⁻¹ * PassiveLogCore.regulatedPassiveLogIncrement (X + (t : ℂ) • Y) Q η a := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 a)
  let F : ℝ → ℝ → ℝ := fun s t => (1 + t ^ 2)⁻¹ * score X Y Q η s t
  have hmeas : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun p : ℝ × ℝ => score X Y Q η p.1 (p.2 : ℂ)) :=
      (measurable_score X Y Q η).comp (f := fun p : ℝ × ℝ => (p.1, (p.2 : ℂ)))
        (measurable_fst.prodMk (Complex.measurable_ofReal.comp measurable_snd))
    have h2 : Measurable (fun p : ℝ × ℝ => (1 + p.2 ^ 2)⁻¹) :=
      ((measurable_snd.pow_const 2).const_add 1).inv
    exact h2.mul h1
  have hint : Integrable (Function.uncurry F) (μ.prod volume) := by
    have hb : Integrable (fun p : ℝ × ℝ => ((∑ a, ∑ b, ‖Q a b‖) * η⁻¹) * (1 + p.2 ^ 2)⁻¹)
        (μ.prod volume) :=
      (integrable_const ((∑ a, ∑ b, ‖Q a b‖) * η⁻¹)).mul_prod integrable_inv_one_add_sq
    refine hb.mono' hmeas.aestronglyMeasurable ?_
    have hfst : ∀ᵐ p : ℝ × ℝ ∂(μ.prod (volume : Measure ℝ)), p.1 ∈ Ioc (0 : ℝ) a :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure ℝ))).ae
        (p := fun s => s ∈ Ioc (0 : ℝ) a) (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hfst] with p hp
    simp only [Function.uncurry, F, norm_mul, Real.norm_eq_abs]
    have h1 : 0 < 1 + p.2 ^ 2 := by positivity
    rw [abs_of_pos (inv_pos.mpr h1), mul_comm ((∑ a, ∑ b, ‖Q a b‖) * η⁻¹)]
    exact mul_le_mul_of_nonneg_left (abs_score_le hX hY hQ hη hp.1.le (by simp))
      (inv_pos.mpr h1).le
  have hinner : ∀ t : ℝ, (∫ s, F s t ∂μ) =
      (1 + t ^ 2)⁻¹ * PassiveLogCore.regulatedPassiveLogIncrement (X + (t : ℂ) • Y) Q η a := by
    intro t
    rw [realIncrement_eq_integral hX hY hQ hη ha t, intervalIntegral.integral_of_le ha,
      ← integral_const_mul]
  refine ⟨?_, ?_⟩
  · have := hint.integral_prod_right
    simpa only [Function.uncurry, hinner] using this
  · rw [imagIncrement_eq_integral hX hY hQ hη ha, ← intervalIntegral.integral_const_mul]
    have hpo : ∀ s ∈ uIcc (0 : ℝ) a, Real.pi * score X Y Q η s Complex.I = ∫ t, F s t := by
      intro s hs
      rw [uIcc_of_le ha] at hs
      exact ((poisson_score hX hY hQ hη hs.1).2).symm
    rw [intervalIntegral.integral_congr hpo, intervalIntegral.integral_of_le ha]
    rw [integral_integral_swap hint]
    simp only [hinner]

end PassiveLogCauchy

end BlockBand.Wegner
