module

public import Mathlib
public import BlockBand.Wegner.PassiveLogCauchyLimit
public import BlockBand.Wegner.SingularLogMoments

/-!
# The passive log bound

Proves `Internal.Contracts.Inputs.PassiveLog` for block models with independent GUE blocks.

Law and domain: any `BlockModel k W` with `W > 0` and `IsIndependent c` (`c > 0`):
independent `GUE_W(c/W)` blocks, `(D, Y)` jointly independent of the blocks, `D` Hermitian
and `Y ⪰ 0` with no norm bound; `H = D + ⊕_j A_j`; `0 ⪯ Q ⪯ I` fixed, real `e`, `a ≥ 0`.

* Clause 1 (the Cauchy formula). Almost surely `H - e` is invertible (first
  factorial moment of the count of `H` on the degenerate interval `[e, e]`,
  `SingularLogLaw.blockModel_countFactorial`). For each real `t`, `D + tY` is again a
  deformation independent of the blocks, so `SingularLogMoments` bounds
  `E[½ Σ_λ log(1 + (a+1)²/(λ-e)²)](H + tY) ≤ C` uniformly in `t`; by Tonelli the
  dominating function `t ↦ (1+t²)⁻¹ B_{a+1}(H + tY; I)` is a.s. integrable. The deterministic
  `PassiveLogCauchy.cauchy_formula` then gives the formula and nonnegativity.
* Clause 2 is the deterministic `passiveLog_partial_holds`.
* Clause 3. With `p = max r 1`, Jensen for the Cauchy probability measure
  `dt/(π(1+t²))` (monotonicity of `‖·‖_{L^q}` in `q`), clause 1, the pointwise bound
  `0 ≤ B_a(X; Q) ≤ ½ Σ_λ log(1 + a²/(λ-e)²)` (clause 2; both sides `≥ 0` and `B = 0` at a
  singular `X - e`), Tonelli and `SingularLogMoments` at order `p` for the shifted models,
  uniformly in `t`: `‖B_a(H+iY;Q)‖_r ≤ ‖B_a(H+iY;Q)‖_p ≤ C_{p,K,c}`, uniformly in `D, Y, Q`,
  `e`, `0 ≤ aN ≤ K` and `kW ≤ N`.

Only `PSSS.SourceContract` is used (through `singularLogMoments_holds` and
`blockModel_countFactorial`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory Set Filter
open BlockBand.External BlockBand.External.PSSS
open BlockBand.Internal.Contracts.Inputs (BlockModel passiveLog singularLogStatistic)
open BlockBand.Wegner.SingularLogLaw
open scoped ENNReal NNReal ComplexOrder

namespace PassiveLogProof

section Deterministic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `0 ≤ B_a(A; Q) ≤ ½ Σ_λ log(1 + a²/(λ-e)²)` for every Hermitian `A` (no invertibility:
at a singular `A - e`, `B_a` is defined to be `0`). -/
theorem passiveLog_nonneg_le {A Q : Matrix ι ι ℂ} (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hIQ : (1 - Q).PosSemidef) (a e : ℝ) (ha : 0 ≤ a) :
    0 ≤ passiveLog A Q a e ∧ passiveLog A Q a e ≤ singularLogStatistic A a e := by
  by_cases h0 : (A - (e : ℂ) • (1 : Matrix ι ι ℂ)).det = 0
  · have hz : passiveLog A Q a e = 0 := by
      unfold passiveLog
      rw [h0, div_zero, norm_zero, Real.log_zero]
    rw [hz]
    exact ⟨le_rfl, SingularLogMoments.statistic_nonneg A hA a e⟩
  · obtain ⟨h1, h2, h3⟩ := passiveLog_partial_holds ι A Q hA hQ hIQ e a ha h0
    exact ⟨h1, h2.trans h3.le⟩

/-- No eigenvalue at `e` forces `A - e` invertible. -/
theorem det_sub_ne_zero_of_eigenCount {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (e : ℝ)
    (h : eigenCount (⟨A, hA⟩ : HermitianMatrix ι) (Icc e e) = 0) :
    (A - (e : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
  intro h0
  have hz : A - (e : ℂ) • (1 : Matrix ι ι ℂ) = A + (-(e : ℂ)) • (1 : Matrix ι ι ℂ) := by
    rw [neg_smul, sub_eq_add_neg]
  rw [hz, PassiveLogCore.det_add_smul_one_eq_prod_eigenvalues hA] at h0
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h0
  have hie : hA.eigenvalues i = e := by
    have := congrArg Complex.re hi
    simp at this
    linarith
  have hie' : hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) = e := hie
  have hpos : 0 < eigenCount (⟨A, hA⟩ : HermitianMatrix ι) (Icc e e) := by
    unfold eigenCount
    refine Finset.card_pos.mpr
      ⟨((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).rev,
        (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mpr
          ⟨Finset.mem_univ _, ?_⟩⟩
    simp only [BlockBand.Foundations.Spectral.increasingEigenvalue, Fin.rev_rev, hie']
    exact ⟨le_rfl, le_rfl⟩
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- Entrywise measurability of `a ↦ F a + z a • G a` for matrix-valued `F, G`. -/
theorem measurable_add_smul {α : Type} [MeasurableSpace α] {F G : α → Matrix ι ι ℂ}
    {z : α → ℂ} (hF : Measurable F) (hG : Measurable G) (hz : Measurable z) :
    Measurable (fun x => F x + z x • G x) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)).add
    (hz.mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hG)))

end Deterministic

section Model

variable {k W : ℕ}

/-- The block model with deformation `D + tY` (same blocks, same absorber). -/
def shiftModel (M : BlockModel k W) (t : ℝ) : BlockModel k W where
  Ω := M.Ω
  P := M.P
  A := M.A
  D := fun w => M.D w + (t : ℂ) • M.Y w
  Y := M.Y
  measurable_A := M.measurable_A
  measurable_D := measurable_add_smul M.measurable_D M.measurable_Y measurable_const
  measurable_Y := M.measurable_Y
  hermitian_A := M.hermitian_A
  hermitian_D := fun w =>
    (M.hermitian_D w).add ((M.posSemidef_Y w).1.smul (by simp [IsSelfAdjoint]))
  posSemidef_Y := M.posSemidef_Y

/-- The shifted model has `H + tY` as its Hamiltonian. -/
theorem shiftModel_H (M : BlockModel k W) (t : ℝ) (w : M.Ω) :
    (shiftModel M t).H w = M.H w + (t : ℂ) • M.Y w := by
  show M.D w + (t : ℂ) • M.Y w + M.blockSum w = M.D w + M.blockSum w + (t : ℂ) • M.Y w
  abel

/-- `(D + tY, Y)` is still independent of the blocks: the shifted model is independent. -/
theorem shiftModel_isIndependent {M : BlockModel k W} {c : ℝ} (h : M.IsIndependent c)
    (t : ℝ) : (shiftModel M t).IsIndependent c := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hφ : Measurable (fun p : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ ×
      Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ => (p.1 + (t : ℂ) • p.2, p.2)) :=
    (measurable_add_smul measurable_fst measurable_snd measurable_const).prodMk measurable_snd
  exact h.2.2.comp hφ measurable_id

/-- `H + zY` is Hermitian for real `z`. -/
theorem hermitian_shift (M : BlockModel k W) (w : M.Ω) (z : ℝ) :
    (M.H w + (z : ℂ) • M.Y w).IsHermitian :=
  (H_isHermitian M w).add ((M.posSemidef_Y w).1.smul (by simp [IsSelfAdjoint]))

/-- Joint measurability of `(w, t) ↦ H(w) + tY(w)`. -/
theorem measurable_shiftPath (M : BlockModel k W) :
    Measurable (fun p : M.Ω × ℝ => M.H p.1 + (p.2 : ℂ) • M.Y p.1) :=
  measurable_add_smul ((measurable_H M).comp measurable_fst) (M.measurable_Y.comp measurable_fst)
    (Complex.measurable_ofReal.comp measurable_snd)

/-- Measurability of the singular log statistic of `H + tY`. -/
theorem measurable_shiftStatistic (M : BlockModel k W) (a e t : ℝ) :
    Measurable (fun w => singularLogStatistic (M.H w + (t : ℂ) • M.Y w) a e) := by
  have h := SingularLogMoments.measurable_modelStatistic (shiftModel M t) a e
  have e1 : (fun w => singularLogStatistic ((shiftModel M t).H w) a e) =
      fun w => singularLogStatistic (M.H w + (t : ℂ) • M.Y w) a e :=
    funext fun w => congrArg (fun X => singularLogStatistic X a e) (shiftModel_H M t w)
  rw [e1] at h
  exact h

/-- `SingularLogMoments` for the shifted models, uniformly in the shift `t`. -/
theorem eLpNorm_shift_le (source : PSSS.SourceContract.{0}) {p : ℝ} (hp : 0 < p) (K c : ℝ)
    (hc : 0 < c) :
    ∃ C : ℝ, ∀ (N k W : ℕ), 0 < W → k * W ≤ N → ∀ M : BlockModel k W, M.IsIndependent c →
      ∀ (e a : ℝ), 0 ≤ a → a * (N : ℝ) ≤ K → ∀ t : ℝ,
        eLpNorm (fun w => singularLogStatistic (M.H w + (t : ℂ) • M.Y w) a e)
          (ENNReal.ofReal p) M.P ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := singularLogMoments_holds source p hp K c hc
  refine ⟨C, fun N k W hW hkW M h e a ha haK t => ?_⟩
  have h1 := hC N k W hW hkW (shiftModel M t) (shiftModel_isIndependent h t) e a ha haK
  have e1 : (fun w => singularLogStatistic ((shiftModel M t).H w) a e) =
      fun w => singularLogStatistic (M.H w + (t : ℂ) • M.Y w) a e :=
    funext fun w => congrArg (fun X => singularLogStatistic X a e) (shiftModel_H M t w)
  rw [e1] at h1
  exact h1

/-- Almost surely `H - e` is invertible (first factorial moment of the count of `H` on
`[e, e]`, which vanishes). -/
theorem ae_det_H_sub_ne_zero (source : PSSS.SourceContract.{0}) (hW : 0 < W) {c : ℝ}
    (hc : 0 < c) (M : BlockModel k W) (h : M.IsIndependent c) (e : ℝ) :
    ∀ᵐ w ∂M.P, (M.H w - (e : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)).det ≠ 0 := by
  obtain ⟨C, -, hcnt⟩ := blockModel_countFactorial source
  obtain ⟨hI, hB⟩ := hcnt k W hW c hc M h e e le_rfl 1 le_rfl
  have hf : factorialCount
      (fun w => eigenCount (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) (Icc e e)) 1 =
      fun w => ((eigenCount (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) (Icc e e) : ℕ) :
        ℝ) := by
    funext w
    simp [factorialCount]
  rw [hf] at hI hB
  simp only [sub_self, mul_zero, pow_one] at hB
  have h0 : (∫ w, ((eigenCount (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _)
      (Icc e e) : ℕ) : ℝ) ∂M.P) = 0 :=
    le_antisymm hB (integral_nonneg fun w => Nat.cast_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun w => Nat.cast_nonneg _) hI).mp h0
  filter_upwards [hae] with w hw
  exact det_sub_ne_zero_of_eigenCount (H_isHermitian M w) e (by simpa using hw)

/-- Clause 1 of `PassiveLog`: almost surely `t ↦ B_a(H + tY; Q)/(π(1+t²))` is integrable,
`B_a(H + iY; Q)` equals its integral, and `B_a(H + iY; Q) ≥ 0`. -/
theorem passiveLog_formula_holds (source : PSSS.SourceContract.{0}) :
    ∀ (k W : ℕ), 0 < W → ∀ (c : ℝ), 0 < c → ∀ M : BlockModel k W, M.IsIndependent c →
      ∀ Q : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ, Q.PosSemidef → (1 - Q).PosSemidef →
        ∀ (e a : ℝ), 0 ≤ a →
          ∀ᵐ w ∂M.P,
            Integrable (fun t : ℝ =>
              passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e / (Real.pi * (1 + t ^ 2))) ∧
            passiveLog (M.H w + Complex.I • M.Y w) Q a e =
              (∫ t : ℝ, passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e / (Real.pi * (1 + t ^ 2))) ∧
            0 ≤ passiveLog (M.H w + Complex.I • M.Y w) Q a e := by
  intro k W hW c hc M h Q hQ hIQ e a ha
  obtain ⟨C, hC⟩ := eLpNorm_shift_le source one_pos ((a + 1) * ((k * W : ℕ) : ℝ)) c hc
  have hCt : ∀ t : ℝ, eLpNorm (fun w => singularLogStatistic (M.H w + (t : ℂ) • M.Y w)
      (a + 1) e) 1 M.P ≤ ENNReal.ofReal C := by
    intro t
    have := hC (k * W) k W hW le_rfl M h e (a + 1) (by linarith) le_rfl t
    simpa using this
  have hI1 : (1 - (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)).PosSemidef := by
    simpa using Matrix.PosSemidef.zero
  let bd : M.Ω → ℝ → ℝ := fun w t =>
    (1 + t ^ 2)⁻¹ * passiveLog (M.H w + (t : ℂ) • M.Y w) 1 (a + 1) e
  have hbd0 : ∀ w t, 0 ≤ bd w t := fun w t =>
    mul_nonneg (inv_pos.mpr (by positivity)).le
      (passiveLog_nonneg_le (hermitian_shift M w t) Matrix.PosSemidef.one hI1 (a + 1) e
        (by linarith)).1
  have hbdm : Measurable (Function.uncurry bd) :=
    (((measurable_snd.pow_const 2).const_add 1).inv).mul
      ((PassiveLogCauchy.measurable_passiveLog 1 (a + 1) e).comp (measurable_shiftPath M))
  have hbdm' : Measurable (fun p : M.Ω × ℝ => ENNReal.ofReal (bd p.1 p.2)) :=
    hbdm.ennreal_ofReal
  have hlin : (∫⁻ w, ∫⁻ t, ENNReal.ofReal (bd w t) ∂volume ∂M.P) < ∞ := by
    rw [lintegral_lintegral_swap hbdm'.aemeasurable]
    have hpt : ∀ t : ℝ, (∫⁻ w, ENNReal.ofReal (bd w t) ∂M.P) ≤
        ENNReal.ofReal ((1 + t ^ 2)⁻¹) * ENNReal.ofReal C := by
      intro t
      have hw : 0 ≤ (1 + t ^ 2)⁻¹ := (inv_pos.mpr (by positivity)).le
      calc (∫⁻ w, ENNReal.ofReal (bd w t) ∂M.P)
          = ∫⁻ w, ENNReal.ofReal ((1 + t ^ 2)⁻¹) *
              ENNReal.ofReal (passiveLog (M.H w + (t : ℂ) • M.Y w) 1 (a + 1) e) ∂M.P := by
            refine lintegral_congr fun w => ?_
            exact ENNReal.ofReal_mul hw
        _ = ENNReal.ofReal ((1 + t ^ 2)⁻¹) *
              ∫⁻ w, ENNReal.ofReal (passiveLog (M.H w + (t : ℂ) • M.Y w) 1 (a + 1) e) ∂M.P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal ((1 + t ^ 2)⁻¹) * ENNReal.ofReal C := by
            gcongr
            calc (∫⁻ w, ENNReal.ofReal (passiveLog (M.H w + (t : ℂ) • M.Y w) 1 (a + 1) e) ∂M.P)
                ≤ ∫⁻ w, ‖singularLogStatistic (M.H w + (t : ℂ) • M.Y w) (a + 1) e‖ₑ ∂M.P := by
                  refine lintegral_mono fun w => ?_
                  rw [Real.enorm_eq_ofReal_abs]
                  exact ENNReal.ofReal_le_ofReal ((passiveLog_nonneg_le (hermitian_shift M w t)
                    Matrix.PosSemidef.one hI1 (a + 1) e (by linarith)).2.trans (le_abs_self _))
              _ = eLpNorm (fun w => singularLogStatistic (M.H w + (t : ℂ) • M.Y w) (a + 1) e)
                    1 M.P := (eLpNorm_one_eq_lintegral_enorm
                      (measurable_shiftStatistic M (a + 1) e t).aestronglyMeasurable).symm
              _ ≤ ENNReal.ofReal C := hCt t
    calc (∫⁻ t, ∫⁻ w, ENNReal.ofReal (bd w t) ∂M.P ∂volume)
        ≤ ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2)⁻¹) * ENNReal.ofReal C ∂volume := lintegral_mono hpt
      _ = (∫⁻ t, ENNReal.ofReal ((1 + t ^ 2)⁻¹) ∂volume) * ENNReal.ofReal C :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top integrable_inv_one_add_sq.lintegral_lt_top ENNReal.ofReal_lt_top
  have hfin : ∀ᵐ w ∂M.P, (∫⁻ t, ENNReal.ofReal (bd w t) ∂volume) < ∞ :=
    ae_lt_top hbdm'.lintegral_prod_right' hlin.ne
  filter_upwards [ae_det_H_sub_ne_zero source hW hc M h e, hfin] with w hdet hw
  have hint : Integrable (fun t : ℝ =>
      (1 + t ^ 2)⁻¹ * passiveLog (M.H w + (t : ℂ) • M.Y w) 1 (a + 1) e) := by
    refine ⟨(hbdm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hbd0 w))]
    exact hw
  exact PassiveLogCauchy.cauchy_formula (H_isHermitian M w) (M.posSemidef_Y w) hQ hIQ e ha
    hdet hint

/-- The Cauchy density `1/(π(1+t²))`. -/
def cauchyDensity (t : ℝ) : ℝ := (Real.pi * (1 + t ^ 2))⁻¹

/-- `1/(π(1+t²)) = π⁻¹ (1+t²)⁻¹`. -/
theorem cauchyDensity_eq : cauchyDensity = fun t => Real.pi⁻¹ * (1 + t ^ 2)⁻¹ :=
  funext fun _ => mul_inv _ _

/-- The Cauchy density is nonnegative. -/
theorem cauchyDensity_nonneg (t : ℝ) : 0 ≤ cauchyDensity t :=
  (inv_pos.mpr (by positivity)).le

/-- The Cauchy density is measurable. -/
theorem measurable_cauchyDensity : Measurable (fun t => ENNReal.ofReal (cauchyDensity t)) := by
  rw [cauchyDensity_eq]
  exact (measurable_const.mul ((measurable_id.pow_const 2).const_add 1).inv).ennreal_ofReal

/-- The Cauchy probability measure `dt/(π(1+t²))`. -/
def cauchyMeasure : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (cauchyDensity t))

/-- The Cauchy measure has mass one (`∫ (1+t²)⁻¹ = π`). -/
instance : IsProbabilityMeasure cauchyMeasure := by
  constructor
  have hi : Integrable cauchyDensity := by
    rw [cauchyDensity_eq]
    exact integrable_inv_one_add_sq.const_mul _
  rw [cauchyMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ cauchyDensity_nonneg),
    cauchyDensity_eq, integral_const_mul, integral_univ_inv_one_add_sq,
    inv_mul_cancel₀ Real.pi_ne_zero, ENNReal.ofReal_one]

/-- `∫⁻ ‖f‖^p = ‖f‖_p^p` for `0 < p < ∞`. -/
theorem lintegral_rpow_eq {α : Type} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, one_div, ENNReal.rpow_inv_rpow hp.ne']

/-- Jensen for the Cauchy probability measure: `|∫ g dt/(π(1+t²))|^p ≤ ∫ |g|^p dt/(π(1+t²))`,
`p ≥ 1`, `g` measurable. -/
theorem enorm_cauchy_rpow_le {g : ℝ → ℝ} (hg : Measurable g) {p : ℝ} (hp : 1 ≤ p) :
    ‖∫ t : ℝ, g t / (Real.pi * (1 + t ^ 2))‖ₑ ^ p ≤ ∫⁻ t, ‖g t‖ₑ ^ p ∂cauchyMeasure := by
  have hp0 : 0 < p := by linarith
  have h1 : ‖∫ t : ℝ, g t / (Real.pi * (1 + t ^ 2))‖ₑ ≤ ∫⁻ t, ‖g t‖ₑ ∂cauchyMeasure := by
    rw [cauchyMeasure, lintegral_withDensity_eq_lintegral_mul _ measurable_cauchyDensity hg.enorm]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun t => ?_))
    simp only [Pi.mul_apply]
    rw [div_eq_mul_inv, enorm_mul, show (Real.pi * (1 + t ^ 2))⁻¹ = cauchyDensity t from rfl,
      Real.enorm_eq_ofReal (cauchyDensity_nonneg t), mul_comm]
  have h2 : ∫⁻ t, ‖g t‖ₑ ∂cauchyMeasure ≤ eLpNorm g (ENNReal.ofReal p) cauchyMeasure := by
    rw [← eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
    exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.mpr hp)
  rw [lintegral_rpow_eq hg.aestronglyMeasurable hp0]
  exact ENNReal.rpow_le_rpow (h1.trans h2) hp0.le

/-- Clause 3 of `PassiveLog`: `‖B_a(H+iY;Q)‖_r ≤ C_{r,K,c}` when `aN ≤ K`, uniformly in
`D, Y, Q`, `e` and `kW ≤ N` (`C` is the `SingularLogMoments` constant at order `max r 1`). -/
theorem passiveLog_moment_holds (source : PSSS.SourceContract.{0}) :
    ∀ (r : ℝ), 0 < r → ∀ (K c : ℝ), 0 < c → ∃ C : ℝ,
      ∀ (N k W : ℕ), 0 < W → k * W ≤ N → ∀ M : BlockModel k W, M.IsIndependent c →
        ∀ Q : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ, Q.PosSemidef → (1 - Q).PosSemidef →
          ∀ (e a : ℝ), 0 ≤ a → a * (N : ℝ) ≤ K →
            eLpNorm (fun w => passiveLog (M.H w + Complex.I • M.Y w) Q a e)
              (ENNReal.ofReal r) M.P ≤ ENNReal.ofReal C := by
  intro r hr K c hc
  obtain ⟨p, hp_def⟩ : ∃ p : ℝ, p = max r 1 := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := hp_def ▸ le_max_right r 1
  have hp0 : 0 < p := by linarith
  have hrp : r ≤ p := hp_def ▸ le_max_left r 1
  obtain ⟨C, hC⟩ := eLpNorm_shift_le source hp0 K c hc
  refine ⟨C, ?_⟩
  intro N k W hW hkW M h Q hQ hIQ e a ha haK
  refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hrp)).trans ?_
  have hgm : Measurable (fun q : M.Ω × ℝ => passiveLog (M.H q.1 + (q.2 : ℂ) • M.Y q.1) Q a e) :=
    (PassiveLogCauchy.measurable_passiveLog Q a e).comp (measurable_shiftPath M)
  have hfm : Measurable (fun w => passiveLog (M.H w + Complex.I • M.Y w) Q a e) :=
    (PassiveLogCauchy.measurable_passiveLog Q a e).comp
      (measurable_add_smul (measurable_H M) M.measurable_Y measurable_const)
  have hjensen : ∀ᵐ w ∂M.P, ‖passiveLog (M.H w + Complex.I • M.Y w) Q a e‖ₑ ^ p ≤
      ∫⁻ t, ‖passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e‖ₑ ^ p ∂cauchyMeasure := by
    filter_upwards [passiveLog_formula_holds source k W hW c hc M h Q hQ hIQ e a ha] with w hw
    rw [hw.2.1]
    exact enorm_cauchy_rpow_le (hgm.comp (measurable_const.prodMk measurable_id)) hp1
  have hmom : ∀ t : ℝ, ∫⁻ w, ‖passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e‖ₑ ^ p ∂M.P ≤
      ENNReal.ofReal C ^ p := by
    intro t
    have hs := hC N k W hW hkW M h e a ha haK t
    calc ∫⁻ w, ‖passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e‖ₑ ^ p ∂M.P
        ≤ ∫⁻ w, ‖singularLogStatistic (M.H w + (t : ℂ) • M.Y w) a e‖ₑ ^ p ∂M.P := by
          refine lintegral_mono fun w => ENNReal.rpow_le_rpow ?_ hp0.le
          obtain ⟨h0, h1⟩ := passiveLog_nonneg_le (hermitian_shift M w t) hQ hIQ a e ha
          rw [Real.enorm_eq_ofReal h0, Real.enorm_eq_ofReal (h0.trans h1)]
          exact ENNReal.ofReal_le_ofReal h1
      _ = eLpNorm (fun w => singularLogStatistic (M.H w + (t : ℂ) • M.Y w) a e)
            (ENNReal.ofReal p) M.P ^ p :=
          lintegral_rpow_eq (measurable_shiftStatistic M a e t).aestronglyMeasurable hp0
      _ ≤ ENNReal.ofReal C ^ p := ENNReal.rpow_le_rpow hs hp0.le
  have hjm : Measurable (fun q : M.Ω × ℝ =>
      ‖passiveLog (M.H q.1 + (q.2 : ℂ) • M.Y q.1) Q a e‖ₑ ^ p) := hgm.enorm.pow_const p
  have hint : ∫⁻ w, ‖passiveLog (M.H w + Complex.I • M.Y w) Q a e‖ₑ ^ p ∂M.P ≤
      ENNReal.ofReal C ^ p :=
    calc ∫⁻ w, ‖passiveLog (M.H w + Complex.I • M.Y w) Q a e‖ₑ ^ p ∂M.P
        ≤ ∫⁻ w, ∫⁻ t, ‖passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e‖ₑ ^ p ∂cauchyMeasure ∂M.P :=
          lintegral_mono_ae hjensen
      _ = ∫⁻ t, ∫⁻ w, ‖passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e‖ₑ ^ p ∂M.P ∂cauchyMeasure :=
          lintegral_lintegral_swap hjm.aemeasurable
      _ ≤ ∫⁻ _t, ENNReal.ofReal C ^ p ∂cauchyMeasure := lintegral_mono hmom
      _ = ENNReal.ofReal C ^ p := by rw [lintegral_const, measure_univ, mul_one]
  rw [lintegral_rpow_eq hfm.aestronglyMeasurable hp0] at hint
  exact (ENNReal.rpow_le_rpow_iff hp0).mp hint

end Model

end PassiveLogProof

/-- The passive log lemma `Internal.Contracts.Inputs.PassiveLog`. Law: any `BlockModel k W` with
`W > 0` and `IsIndependent c` (`c > 0`); `0 ⪯ Q ⪯ I`, real `e`, `a ≥ 0`. Clause 1 (a.s. Cauchy
formula and nonnegativity) is `PassiveLogProof.passiveLog_formula_holds`; clause 2 (deterministic,
every Hermitian `A` with `A - e` invertible) is `passiveLog_partial_holds`; clause 3 (the `L^r`
bound, `C_{r,K,c}` chosen before `N, k, W, M, Q, e, a`) is
`PassiveLogProof.passiveLog_moment_holds`. Only `PSSS.SourceContract` is used. -/
theorem passiveLog_holds (source : PSSS.SourceContract.{0}) :
    Internal.Contracts.Inputs.PassiveLog :=
  ⟨PassiveLogProof.passiveLog_formula_holds source, passiveLog_partial_holds,
    PassiveLogProof.passiveLog_moment_holds source⟩

end BlockBand.Wegner
