module

public import Mathlib
public import BlockBand.Wegner.PassiveLogCauchyRegulated
public import BlockBand.Wegner.PassiveLogDeterministic

/-!
# Removing the regulator in the Cauchy formula

For `B_a(A; Q) = log |det(A - e + iaQ)/det(A - e)|`, `A` Hermitian with `A - e` invertible,
`Y ⪰ 0` and `0 ⪯ Q ⪯ I`: `B_a(A + iY; Q) = ∫ B_a(A + tY; Q) dt/(π(1+t²))`, obtained from the
regulated formula `regulated_cauchy` by dominated convergence as the regulator `η ↓ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open Matrix MeasureTheory Set Filter
open scoped ComplexOrder Topology

variable {n : Type} [Fintype n] [DecidableEq n]

namespace PassiveLogCauchy

open Internal.Contracts.Inputs (passiveLog)

/-- `B_a(·; Q)` is a Borel function of the matrix. -/
theorem measurable_passiveLog (Q : Matrix n n ℂ) (a e : ℝ) :
    Measurable (fun A : Matrix n n ℂ => passiveLog A Q a e) := by
  unfold passiveLog
  have h1 : Continuous (fun A : Matrix n n ℂ =>
      (A - (e : ℂ) • (1 : Matrix n n ℂ) + ((a : ℂ) * Complex.I) • Q).det) :=
    Continuous.matrix_det (by fun_prop)
  have h2 : Continuous (fun A : Matrix n n ℂ => (A - (e : ℂ) • (1 : Matrix n n ℂ)).det) :=
    Continuous.matrix_det (by fun_prop)
  exact Real.measurable_log.comp (measurable_norm.comp (h1.measurable.div h2.measurable))

/-- An invertible base matrix stays invertible along `X + tY` except at finitely many `t`. -/
theorem ae_det_ne_zero {X : Matrix n n ℂ} (Y : Matrix n n ℂ) (hX : X.det ≠ 0) :
    ∀ᵐ t : ℝ, (X + (t : ℂ) • Y).det ≠ 0 := by
  have hp0 : PassiveLogCore.detLinePoly X Y ≠ 0 := by
    intro h
    apply hX
    have := PassiveLogCore.eval_detLinePoly X Y 0
    rw [h] at this
    simpa using this.symm
  have hsub : {t : ℝ | ¬ (X + (t : ℂ) • Y).det ≠ 0} ⊆
      Complex.re '' ((PassiveLogCore.detLinePoly X Y).roots.toFinset : Set ℂ) := by
    intro t ht
    have ht' : (X + (t : ℂ) • Y).det = 0 := by simpa using ht
    refine ⟨(t : ℂ), ?_, by simp⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot,
      PassiveLogCore.eval_detLinePoly]
    exact ht'
  rw [ae_iff]
  exact measure_mono_null hsub ((Set.Finite.image _ (Finset.finite_toSet _)).measure_zero _)

/-- `u ↦ ½ log |det(B + iu)|²` is nondecreasing on `u ≥ 0` for Hermitian invertible `B`. -/
theorem halfLog_full_mono {B : Matrix n n ℂ} (hB : B.IsHermitian) (hdet : B.det ≠ 0)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (1 / 2 : ℝ) * Real.log (Complex.normSq (B + (Complex.I * u) • (1 : Matrix n n ℂ)).det) ≤
      (1 / 2 : ℝ) * Real.log (Complex.normSq (B + (Complex.I * v) • (1 : Matrix n n ℂ)).det) := by
  rw [PassiveLogCore.normSq_det_add_I_smul_one_eq_prod hB, PassiveLogCore.normSq_det_add_I_smul_one_eq_prod hB]
  have hl : ∀ i, hB.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hB.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hpos : ∀ i, 0 < hB.eigenvalues i ^ 2 + u ^ 2 := fun i => by
    have := hl i
    positivity
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log (Finset.prod_pos fun i _ => hpos i)
  gcongr

omit [Fintype n] in

/-- The full-absorber matrix is `B + i(s + η)`. -/
theorem regulatedAbsorberMatrix_one (B : Matrix n n ℂ) (η s : ℝ) :
    PassiveLogCore.regulatedAbsorberMatrix B 0 1 η s =
      B + (Complex.I * ((s + η : ℝ) : ℂ)) • (1 : Matrix n n ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [PassiveLogCore.regulatedAbsorberMatrix, h]
  ring

/-- Domination of the regulated real-background increment, `0 < η ≤ 1`:
`0 ≤ B^η_a(B;
Q) ≤ B_{a+1}(B;
I)` (increments at the shifted matrix `B`).
-/
theorem regulatedIncrement_le {B Q : Matrix n n ℂ} (hB : B.IsHermitian) (hQ : Q.PosSemidef)
    (hIQ : (1 - Q).PosSemidef) (hdet : B.det ≠ 0) {η a : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (ha : 0 ≤ a) :
    0 ≤ PassiveLogCore.regulatedPassiveLogIncrement B Q η a ∧
      PassiveLogCore.regulatedPassiveLogIncrement B Q η a ≤ PassiveLogCore.passiveLogIncrement B 1 (a + 1) := by
  have h := PassiveLogCore.regulatedPassiveLogIncrement_nonneg_le_full B Q hB hQ hIQ hη ha
  have hfull : PassiveLogCore.regulatedPassiveLogIncrement B 1 η a =
      (1 / 2 : ℝ) * Real.log (Complex.normSq
          (B + (Complex.I * ((a + η : ℝ) : ℂ)) • (1 : Matrix n n ℂ)).det) -
        (1 / 2 : ℝ) * Real.log (Complex.normSq
          (B + (Complex.I * ((0 + η : ℝ) : ℂ)) • (1 : Matrix n n ℂ)).det) := by
    simp only [PassiveLogCore.regulatedPassiveLogIncrement, PassiveLogCore.regulatedAbsorberLogPath,
      regulatedAbsorberMatrix_one]
  have hinc : PassiveLogCore.passiveLogIncrement B 1 (a + 1) =
      (1 / 2 : ℝ) * Real.log (Complex.normSq
          (B + (Complex.I * ((a + 1 : ℝ) : ℂ)) • (1 : Matrix n n ℂ)).det) -
        (1 / 2 : ℝ) * Real.log (Complex.normSq
          (B + (Complex.I * ((0 : ℝ) : ℂ)) • (1 : Matrix n n ℂ)).det) := by
    have hm : B + Complex.I • ((a + 1) • (1 : Matrix n n ℂ)) =
        B + (Complex.I * ((a + 1 : ℝ) : ℂ)) • (1 : Matrix n n ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [h, Complex.real_smul]
    have hm0 : B + (Complex.I * ((0 : ℝ) : ℂ)) • (1 : Matrix n n ℂ) = B := by simp
    unfold PassiveLogCore.passiveLogIncrement
    rw [hm, hm0]
  have h1 := halfLog_full_mono hB hdet (u := a + η) (v := a + 1) (by linarith) (by linarith)
  have h2 := halfLog_full_mono hB hdet (u := 0) (v := 0 + η) le_rfl (by linarith)
  refine ⟨h.1, h.2.trans ?_⟩
  rw [hfull, hinc]
  linarith

/-- Regulator removal at the imaginary background `ζ = i`:
`L_η(i; a) - L_η(i; 0) → B_a(A + iY; Q)` as `η ↓ 0`, for `A - e` invertible. -/
theorem tendsto_imagIncrement {A Y Q : Matrix n n ℂ} (hA : A.IsHermitian) (hY : Y.PosSemidef)
    (hQ : Q.PosSemidef) (e : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hdet : (A - (e : ℂ) • (1 : Matrix n n ℂ)).det ≠ 0) :
    Tendsto (fun η : ℝ =>
        PassiveLogCore.regulatedAbsorberLogPath (A - (e : ℂ) • (1 : Matrix n n ℂ)) Y Q η a -
          PassiveLogCore.regulatedAbsorberLogPath (A - (e : ℂ) • (1 : Matrix n n ℂ)) Y Q η 0)
      (𝓝 0) (𝓝 (passiveLog (A + Complex.I • Y) Q a e)) := by
  set X := A - (e : ℂ) • (1 : Matrix n n ℂ) with hXdef
  have hX : X.IsHermitian := isHermitian_sub_smul_one hA e
  have hm : ∀ (η s : ℝ), PassiveLogCore.regulatedAbsorberMatrix X Y Q η s =
      (X + Complex.I • (Y + s • Q)) + Complex.I • (η • (1 : Matrix n n ℂ)) := by
    intro η s
    simp only [PassiveLogCore.regulatedAbsorberMatrix, smul_add]
    abel
  have hna : (X + Complex.I • (Y + a • Q)).det ≠ 0 := by
    have := det_add_I_smul_posSemidef_ne_zero hX (hY.add (hQ.smul ha)) zero_le_one hdet
    simpa using this
  have hn0 : (X + Complex.I • Y).det ≠ 0 := by
    have := det_add_I_smul_posSemidef_ne_zero hX hY zero_le_one hdet
    simpa using this
  have h1 := PassiveLogCore.tendsto_half_log_normSq_det_add_I_regulator _ hna
  have h0 := PassiveLogCore.tendsto_half_log_normSq_det_add_I_regulator _ hn0
  have hlim := h1.sub h0
  have hval : passiveLog (A + Complex.I • Y) Q a e =
      (1 / 2 : ℝ) * Real.log (Complex.normSq (X + Complex.I • (Y + a • Q)).det) -
        (1 / 2 : ℝ) * Real.log (Complex.normSq (X + Complex.I • Y).det) := by
    have e1 : A + Complex.I • Y - (e : ℂ) • (1 : Matrix n n ℂ) + ((a : ℂ) * Complex.I) • Q =
        X + Complex.I • (Y + a • Q) := by
      rw [hXdef]
      ext i j
      simp [Complex.real_smul]
      ring
    have e0 : A + Complex.I • Y - (e : ℂ) • (1 : Matrix n n ℂ) = X + Complex.I • Y := by
      rw [hXdef]
      abel
    unfold passiveLog
    rw [e1, e0, log_norm_div_eq _ _ hna hn0]
  rw [hval]
  refine hlim.congr fun η => ?_
  simp only [PassiveLogCore.regulatedAbsorberLogPath, hm, zero_smul, add_zero]

/-- The deterministic Cauchy formula, with the regulator removed.
`A` Hermitian, `Y ⪰ 0`, `0 ⪯ Q ⪯ I`, real `e`, `a ≥ 0`, `A - e` invertible, and the
dominating function `t ↦ (1+t²)⁻¹ B_{a+1}(A + tY; I)` Lebesgue integrable. Then
`t ↦ B_a(A + tY; Q)/(π(1+t²))` is integrable, `B_a(A + iY; Q)` equals its integral, and
`B_a(A + iY; Q) ≥ 0`. Proof: dominated convergence in `regulated_cauchy` along `η ↓ 0`. -/
theorem cauchy_formula {A Y Q : Matrix n n ℂ} (hA : A.IsHermitian) (hY : Y.PosSemidef)
    (hQ : Q.PosSemidef) (hIQ : (1 - Q).PosSemidef) (e : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hdet : (A - (e : ℂ) • (1 : Matrix n n ℂ)).det ≠ 0)
    (hdom : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹ * passiveLog (A + (t : ℂ) • Y) 1 (a + 1) e)) :
    Integrable (fun t : ℝ => passiveLog (A + (t : ℂ) • Y) Q a e / (Real.pi * (1 + t ^ 2))) ∧
      passiveLog (A + Complex.I • Y) Q a e =
        (∫ t : ℝ, passiveLog (A + (t : ℂ) • Y) Q a e / (Real.pi * (1 + t ^ 2))) ∧
      0 ≤ passiveLog (A + Complex.I • Y) Q a e := by
  set X := A - (e : ℂ) • (1 : Matrix n n ℂ) with hXdef
  have hX : X.IsHermitian := isHermitian_sub_smul_one hA e
  have hXt : ∀ t : ℝ, A + (t : ℂ) • Y - (e : ℂ) • (1 : Matrix n n ℂ) = X + (t : ℂ) • Y := by
    intro t
    rw [hXdef]
    abel
  have hXtH : ∀ t : ℝ, (X + (t : ℂ) • Y).IsHermitian := fun t =>
    hX.add (hY.1.smul (by simp [IsSelfAdjoint]))
  have hAtH : ∀ t : ℝ, (A + (t : ℂ) • Y).IsHermitian := fun t =>
    hA.add (hY.1.smul (by simp [IsSelfAdjoint]))
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  let G : ℝ → ℝ → ℝ := fun η t =>
    (1 + t ^ 2)⁻¹ * PassiveLogCore.regulatedPassiveLogIncrement (X + (t : ℂ) • Y) Q η a
  let L : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹ * passiveLog (A + (t : ℂ) • Y) Q a e
  let bd : ℝ → ℝ := fun t => (1 + t ^ 2)⁻¹ * passiveLog (A + (t : ℂ) • Y) 1 (a + 1) e
  have hgood := ae_det_ne_zero Y hdet
  -- pointwise limit and domination at good `t`
  have hconv : ∀ t : ℝ, (X + (t : ℂ) • Y).det ≠ 0 →
      Tendsto (fun η => G η t) l (𝓝 (L t)) := by
    intro t ht
    have hAa := det_add_I_smul_posSemidef_ne_zero (hXtH t) hQ ha ht
    have h := (PassiveLogCore.tendsto_regulatedPassiveLogIncrement _ Q a ht hAa).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    have hv : passiveLog (A + (t : ℂ) • Y) Q a e =
        PassiveLogCore.passiveLogIncrement (X + (t : ℂ) • Y) Q a := by
      rw [passiveLog_eq_increment _ Q a e (by rw [hXt]; exact ht) (by rw [hXt]; exact hAa), hXt]
    simp only [G, L]
    rw [hv]
    exact h.const_mul _
  have hbound : ∀ t : ℝ, (X + (t : ℂ) • Y).det ≠ 0 → ∀ η, 0 < η → η ≤ 1 →
      0 ≤ G η t ∧ ‖G η t‖ ≤ bd t := by
    intro t ht η hη hη1
    have hd := regulatedIncrement_le (hXtH t) hQ hIQ ht hη hη1 ha
    have hAa := det_add_I_smul_posSemidef_ne_zero (hXtH t) Matrix.PosSemidef.one
      (by linarith : (0 : ℝ) ≤ a + 1) ht
    have hv : passiveLog (A + (t : ℂ) • Y) 1 (a + 1) e =
        PassiveLogCore.passiveLogIncrement (X + (t : ℂ) • Y) 1 (a + 1) := by
      rw [passiveLog_eq_increment _ 1 (a + 1) e (by rw [hXt]; exact ht)
        (by rw [hXt]; exact hAa), hXt]
    have hw : 0 < (1 + t ^ 2)⁻¹ := inv_pos.mpr (by positivity)
    have hG0 : 0 ≤ G η t := mul_nonneg hw.le hd.1
    refine ⟨hG0, ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hG0]
    simp only [G, bd]
    rw [hv]
    exact mul_le_mul_of_nonneg_left hd.2 hw.le
  have hev1 : ∀ᶠ η in l, η ∈ Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
  -- limit function: nonnegative and dominated
  have hL : ∀ᵐ t : ℝ, 0 ≤ L t ∧ ‖L t‖ ≤ bd t := by
    filter_upwards [hgood] with t ht
    have hc := hconv t ht
    have hb : ∀ᶠ η in l, 0 ≤ G η t ∧ ‖G η t‖ ≤ bd t :=
      hev1.mono fun η hη => hbound t ht η hη.1 hη.2
    exact ⟨ge_of_tendsto hc (hb.mono fun _ h => h.1),
      le_of_tendsto hc.norm (hb.mono fun _ h => h.2)⟩
  have hLm : AEStronglyMeasurable L volume := by
    have h1 : Measurable (fun t : ℝ => passiveLog (A + (t : ℂ) • Y) Q a e) :=
      (measurable_passiveLog Q a e).comp (by fun_prop)
    exact ((((measurable_id.pow_const 2).const_add 1).inv).mul h1).aestronglyMeasurable
  have hLi : Integrable L := hdom.mono' hLm (hL.mono fun _ h => h.2)
  -- dominated convergence
  have hdct : Tendsto (fun η => ∫ t, G η t) l (𝓝 (∫ t, L t)) := by
    refine tendsto_integral_filter_of_dominated_convergence bd ?_ ?_ hdom ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (regulated_cauchy hX hY hQ hη ha).1.aestronglyMeasurable
    · filter_upwards [hev1] with η hη
      filter_upwards [hgood] with t ht
      exact (hbound t ht η hη.1 hη.2).2
    · filter_upwards [hgood] with t ht
      exact hconv t ht
  have himag : Tendsto (fun η => ∫ t, G η t) l
      (𝓝 (Real.pi * passiveLog (A + Complex.I • Y) Q a e)) := by
    have h := ((tendsto_imagIncrement hA hY hQ e ha hdet).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).const_mul Real.pi
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (regulated_cauchy hX hY hQ hη ha).2
  have hEq : Real.pi * passiveLog (A + Complex.I • Y) Q a e = ∫ t, L t :=
    tendsto_nhds_unique himag hdct
  have hfun : (fun t : ℝ => passiveLog (A + (t : ℂ) • Y) Q a e / (Real.pi * (1 + t ^ 2))) =
      fun t => Real.pi⁻¹ * L t := by
    funext t
    simp only [L]
    rw [div_eq_mul_inv, mul_inv]
    ring
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hval : passiveLog (A + Complex.I • Y) Q a e = Real.pi⁻¹ * ∫ t, L t := by
    rw [← hEq, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hLi.const_mul _
  · rw [hfun, integral_const_mul, hval]
  · rw [hval]
    exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      (integral_nonneg_of_ae (hL.mono fun _ h => h.1))

end PassiveLogCauchy

end BlockBand.Wegner
