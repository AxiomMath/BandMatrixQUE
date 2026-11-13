module

public import BlockBand.QUE.Haar.TwoCoordinate

/-!
# Complex Haar second mass moments

For a fixed vector `v ∈ ℂ^A` and a Haar unitary `U`,
`E |(Uv)_c|² |(Uv)_d|² = (1 + δ_cd) ‖v‖⁴/(W(W+1))` (`integral_mulVec_fourth`,
`integral_mulVec_mass_product`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE.Haar

open Matrix MeasureTheory
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Continuity gives fourth-moment integrability on the Haar law. -/
theorem integrable_mulVec_fourth (v : A → ℂ) (c : A) :
    Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4) unitaryProbability := by
  apply Continuous.integrable_of_hasCompactSupport
    (((continuous_apply c).comp
      (continuous_subtype_val.matrix_mulVec continuous_const)).norm.pow 4)
  exact HasCompactSupport.of_compactSpace _

/-- Products of coordinate masses are integrable. -/
theorem integrable_mulVec_mass_product (v : A → ℂ) (c d : A) :
    Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
        ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2) unitaryProbability := by
  apply Continuous.integrable_of_hasCompactSupport
    ((((continuous_apply c).comp
      (continuous_subtype_val.matrix_mulVec continuous_const)).norm.pow 2).mul
      (((continuous_apply d).comp
      (continuous_subtype_val.matrix_mulVec continuous_const)).norm.pow 2))
  exact HasCompactSupport.of_compactSpace _

/-- Fourth moments are equal in all coordinates by Haar permutations. -/
theorem integral_mulVec_fourth_eq (v : A → ℂ) (c d : A) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 ∂unitaryProbability) =
    ∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 4 ∂unitaryProbability := by
  have h := integral_unitary_translate
    (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4)
    (permutationUnitary (Equiv.swap c d))
  have hrot (U : Matrix.unitaryGroup A ℂ) :
      (((permutationUnitary (Equiv.swap c d) * U : Matrix.unitaryGroup A ℂ) :
        Matrix A A ℂ) *ᵥ v) c = ((U : Matrix A A ℂ) *ᵥ v) d := by
    change (((Equiv.swap c d).permMatrix ℂ * (U : Matrix A A ℂ)) *ᵥ v) c = _
    rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
    simp
  simpa only [hrot] using h.symm

/-- Fourth moments of normalized phase mixtures are preserved by unitary translation. -/
theorem integral_phase_mixture_fourth (v : A → ℂ) (c d : A) (hcd : c ≠ d)
    (q : ℂ) (hq : q * star q = 1) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ‖(Real.sqrt (1 / 2) : ℂ) *
        (((U : Matrix A A ℂ) *ᵥ v) c + q * ((U : Matrix A A ℂ) *ᵥ v) d)‖ ^ 4
        ∂unitaryProbability) =
    ∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 ∂unitaryProbability := by
  have h := integral_unitary_translate
    (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4)
    (twoCoordinateUnitary c d hcd * phaseUnitary d q hq)
  have hrot (U : Matrix.unitaryGroup A ℂ) :
      ((((twoCoordinateUnitary c d hcd * phaseUnitary d q hq) * U :
        Matrix.unitaryGroup A ℂ) : Matrix A A ℂ) *ᵥ v) c =
      (Real.sqrt (1 / 2) : ℂ) *
        (((U : Matrix A A ℂ) *ᵥ v) c + q * ((U : Matrix A A ℂ) *ᵥ v) d) := by
    rw [Matrix.UnitaryGroup.mul_val, ← Matrix.mulVec_mulVec,
      twoCoordinate_phase_mulVec]
  simpa only [hrot] using h

/-- Normalized four-phase polarization with the complex coefficient. -/
theorem complex_normalized_fourth_polarization (x y : ℂ) :
    ‖(Real.sqrt (1 / 2) : ℂ) * (x + y)‖ ^ 4 +
      ‖(Real.sqrt (1 / 2) : ℂ) * (x - y)‖ ^ 4 +
      ‖(Real.sqrt (1 / 2) : ℂ) * (x + Complex.I * y)‖ ^ 4 +
      ‖(Real.sqrt (1 / 2) : ℂ) * (x - Complex.I * y)‖ ^ 4 =
      ‖x‖ ^ 4 + ‖y‖ ^ 4 + 4 * (‖x‖ ^ 2 * ‖y‖ ^ 2) := by
  have hr : (Real.sqrt (1 / 2)) ^ 4 = (1 : ℝ) / 4 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith [sq_nonneg ((Real.sqrt (1 / 2)) ^ 2 - 1 / 2)]
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hr]
  have h := complex_fourth_polarization x y
  linarith

/-- Normalized Haar fourth moments have diagonal-to-off-diagonal ratio two (by averaging over four
complex phases). -/
theorem integral_mulVec_fourth_eq_twice_product (v : A → ℂ) (c d : A)
    (hcd : c ≠ d) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 ∂unitaryProbability) =
    2 * ∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
        ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2 ∂unitaryProbability := by
  let F (q : ℂ) (U : Matrix.unitaryGroup A ℂ) : ℝ :=
    ‖(Real.sqrt (1 / 2) : ℂ) *
      (((U : Matrix A A ℂ) *ᵥ v) c + q * ((U : Matrix A A ℂ) *ᵥ v) d)‖ ^ 4
  have hc : Continuous (fun U : Matrix.unitaryGroup A ℂ =>
      ((U : Matrix A A ℂ) *ᵥ v) c) :=
    (continuous_apply c).comp (continuous_subtype_val.matrix_mulVec continuous_const)
  have hd : Continuous (fun U : Matrix.unitaryGroup A ℂ =>
      ((U : Matrix A A ℂ) *ᵥ v) d) :=
    (continuous_apply d).comp (continuous_subtype_val.matrix_mulVec continuous_const)
  have hint (q : ℂ) : Integrable (F q) unitaryProbability :=
    ((continuous_const.mul (hc.add (continuous_const.mul hd))).norm.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hphase (q : ℂ) (hq : q * star q = 1) :
      (∫ U, F q U ∂unitaryProbability) =
      ∫ U : Matrix.unitaryGroup A ℂ,
        ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 ∂unitaryProbability :=
    integral_phase_mixture_fourth v c d hcd q hq
  have h1 := hphase 1 (by simp)
  have hn1 := hphase (-1) (by simp)
  have hi := hphase Complex.I (by simp)
  have hni := hphase (-Complex.I) (by simp)
  have hpoint (U : Matrix.unitaryGroup A ℂ) :
      F 1 U + F (-1) U + F Complex.I U + F (-Complex.I) U =
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 +
        ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 4 +
          4 * (‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
            ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2) := by
    simpa [F, sub_eq_add_neg, neg_mul] using
      complex_normalized_fourth_polarization
        (((U : Matrix A A ℂ) *ᵥ v) c) (((U : Matrix A A ℂ) *ᵥ v) d)
  have h := integral_congr_ae (μ := unitaryProbability) (Filter.Eventually.of_forall hpoint)
  have hint2 : Integrable (fun U => F 1 U + F (-1) U) unitaryProbability :=
    (hint 1).add (hint (-1))
  have hint3 : Integrable (fun U => F 1 U + F (-1) U + F Complex.I U) unitaryProbability :=
    hint2.add (hint Complex.I)
  have hintr : Integrable (fun U : Matrix.unitaryGroup A ℂ =>
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 + ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 4)
      unitaryProbability := (integrable_mulVec_fourth v c).add (integrable_mulVec_fourth v d)
  rw [integral_add hint3 (hint (-Complex.I)), integral_add hint2 (hint Complex.I),
    integral_add (hint 1) (hint (-1)),
    integral_add hintr ((integrable_mulVec_mass_product v c d).const_mul 4),
    integral_add (integrable_mulVec_fourth v c) (integrable_mulVec_fourth v d),
    integral_const_mul, h1, hn1, hi, hni,
    ← integral_mulVec_fourth_eq v c d] at h
  linarith

/-- Diagonal fourth moment of every fixed complex vector, with the
full complex-sphere denominator `W(W+1)`, valid also at width one. -/
theorem integral_mulVec_fourth (v : A → ℂ) (c : A) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 ∂unitaryProbability) =
      2 * (∑ d : A, ‖v d‖ ^ 2) ^ 2 /
        ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) := by
  have : Nonempty A := ⟨c⟩
  have hpos : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  let D := ∫ U : Matrix.unitaryGroup A ℂ,
    ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4 ∂unitaryProbability
  let M (d : A) := ∫ U : Matrix.unitaryGroup A ℂ,
    ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
      ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2 ∂unitaryProbability
  have hm (d : A) : M d = D / 2 + if c = d then D / 2 else 0 := by
    by_cases hcd : c = d
    · subst d
      have hself : M c = D := by
        apply integral_congr_ae
        filter_upwards with U
        ring
      simp [hself]
    · have hratio := integral_mulVec_fourth_eq_twice_product v c d hcd
      change D = 2 * M d at hratio
      simp only [ite_eq_right hcd, add_zero]
      linarith
  have hsum : (∑ d : A, M d) =
      (∑ d : A, ‖v d‖ ^ 2) ^ 2 / (Fintype.card A : ℝ) := by
    calc
      _ = ∫ U : Matrix.unitaryGroup A ℂ,
          ∑ d : A, ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
            ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2 ∂unitaryProbability := by
        rw [integral_finsetSum _ (fun d _ => integrable_mulVec_mass_product v c d)]
      _ = ∫ U : Matrix.unitaryGroup A ℂ,
          ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
            (∑ d : A, ‖v d‖ ^ 2) ∂unitaryProbability := by
        simp_rw [← Finset.mul_sum, unitary_mulVec_mass]
      _ = _ := by
        rw [integral_mul_const, integral_mulVec_mass]
        ring
  simp_rw [hm] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hsum
  change D = _
  apply (eq_div_iff (mul_pos hpos (by positivity)).ne').2
  field_simp at hsum
  nlinarith

/-- The complex Haar second coordinate-mass moment of any fixed vector; the diagonal excess equals
the constant term. -/
theorem integral_mulVec_mass_product (v : A → ℂ) (c d : A) :
    (∫ U : Matrix.unitaryGroup A ℂ,
      ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
        ‖((U : Matrix A A ℂ) *ᵥ v) d‖ ^ 2 ∂unitaryProbability) =
      (∑ a : A, ‖v a‖ ^ 2) ^ 2 /
        ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) +
      if c = d then (∑ a : A, ‖v a‖ ^ 2) ^ 2 /
        ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) else 0 := by
  by_cases hcd : c = d
  · subst d
    have heq : (fun U : Matrix.unitaryGroup A ℂ =>
        ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2 *
          ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 2) =
        (fun U : Matrix.unitaryGroup A ℂ =>
          ‖((U : Matrix A A ℂ) *ᵥ v) c‖ ^ 4) := by
      funext U
      ring
    rw [heq, integral_mulVec_fourth]
    simp only [ite_true]
    ring
  · have hratio := integral_mulVec_fourth_eq_twice_product v c d hcd
    rw [integral_mulVec_fourth, mul_div_assoc] at hratio
    simp only [ite_eq_right hcd, add_zero]
    linarith

end BlockBand.QUE.Haar
