module

public import BlockBand.DeterminantScore.GelfandTsetlinContinuity

/-!
# The Gelfand–Tsetlin formula from the bordered-matrix law

`gelfandTsetlin_of_border : DiagonalBorderLawStatement → GelfandTsetlinStatement` (with
`c_m = ∏_{r<m} r!`).

Proof (Baryshnikov's bordering argument, disintegrated against the Weyl formula). Write
`I(λ) = ∫_{U(m)} exp(Σ_r k_r (U diag(λ) U*)_{rr}) dU` and `Φ(λ) = gtMarginal k λ`. For every
measurable `g ≥ 0`, the integral `∫ g(λ(H(x))) e^{Σ_r k_r H(x)_{rr}} dx` over `HermCoord m` equals
both `C_W ∫_𝒞 Δ(λ)² g(λ) I(λ) dλ` (Weyl formula, `weylIntegration_of_diagonalBorderLaw`, with
`λ(U diag(λ) U*) = λ`) and `C ∫_𝒞 Δ(λ) g(λ) Φ(λ) dλ` (`gtLaw_of_border`). Hence
`C_W Δ² I = C Δ Φ` a.e. on the chamber; both sides are continuous (`I` by continuity of parametric
integrals on the compact group, `Φ` by `continuous_gtMarginal`), so the identity holds on the whole
open chamber, i.e. `Δ(λ) I(λ) = (C / C_W) Φ(λ)` for every `λ ∈ 𝒞`. The constant `c = C / C_W` is
not computed (it equals `∏_{r<m} r!`). The only hypothesis is `DiagonalBorderLawStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GelfandTsetlin

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.QUE.Haar
open BlockBand.DeterminantScore.EigenDensity
open BlockBand.DeterminantScore.WeylIntegration
open BlockBand.DeterminantScore.SpectralConvexity (weylChamber isOpen_weylChamber vandermonde_pos)
open scoped ENNReal

variable {m : ℕ}

theorem continuous_diagPhase_exp (k : Fin m → ℝ) :
    Continuous fun p : (Fin m → ℝ) × Matrix.unitaryGroup (Fin m) ℂ =>
      Real.exp (diagPhase k p.1 (p.2 : Matrix (Fin m) (Fin m) ℂ)) :=
  (continuous_diagExp k).comp (continuous_conjDiag.comp continuous_swap)

theorem continuous_diagPhase_exp_right (k : Fin m → ℝ) (lam : Fin m → ℝ) :
    Continuous fun U : Matrix.unitaryGroup (Fin m) ℂ =>
      Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ)) := by
  have h : Continuous fun U : Matrix.unitaryGroup (Fin m) ℂ => conjDiag U lam :=
    continuous_conjDiag.comp (continuous_id.prodMk continuous_const)
  exact (continuous_diagExp k).comp h

/-- The orbital integral `I(λ) = ∫ exp(Σ_r k_r (U diag(λ) U*)_{rr}) dU`. -/
def orbitalExp (k : Fin m → ℝ) (lam : Fin m → ℝ) : ℝ :=
  ∫ U, Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ)) ∂(unitaryProbability (A := Fin m))

theorem continuous_orbitalExp (k : Fin m → ℝ) : Continuous (orbitalExp k) := by
  have := continuous_parametric_integral_of_continuous (μ := unitaryProbability (A := Fin m))
    (s := Set.univ) (f := fun lam (U : Matrix.unitaryGroup (Fin m) ℂ) =>
      Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ))) (continuous_diagPhase_exp k)
    isCompact_univ
  simp only [Measure.restrict_univ] at this
  exact this

theorem orbitalExp_nonneg (k : Fin m → ℝ) (lam : Fin m → ℝ) : 0 ≤ orbitalExp k lam :=
  integral_nonneg fun _ => (Real.exp_pos _).le

theorem lintegral_exp_diagPhase (k : Fin m → ℝ) (lam : Fin m → ℝ) :
    ∫⁻ U, ENNReal.ofReal (Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ)))
        ∂(unitaryProbability (A := Fin m)) = ENNReal.ofReal (orbitalExp k lam) := by
  have hc := continuous_diagPhase_exp_right k lam
  obtain ⟨B, -, hB⟩ := exists_norm_bound hc
  have hi : Integrable (fun U : Matrix.unitaryGroup (Fin m) ℂ =>
      Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ))) unitaryProbability :=
    Integrable.of_bound hc.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  rw [orbitalExp, ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]

/-- Both disintegrations of `∫ 1_s(λ(H)) e^{Σ k_r H_{rr}} dH`. -/
theorem weyl_eq_gt {C Cw : ℝ}
    (hlaw : ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g → ∀ k : Fin m → ℝ,
      ∫⁻ x : HermCoord m → ℝ, g (fun j => freshEigenvalue (hermOfCoord x) j) *
          ENNReal.ofReal (diagExp k (hermOfCoord x)) =
        ENNReal.ofReal C * ∫⁻ lam in weylChamber m,
          ENNReal.ofReal (SpectralConvexity.vandermonde lam) * g lam * gtMarginal k lam)
    (hW : ∀ f : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (hermOfCoord x) = ENNReal.ofReal Cw *
        ∫⁻ lam in weylChamber m,
          ENNReal.ofReal (SpectralConvexity.vandermonde lam ^ 2) *
            ∫⁻ U, f ((U : Matrix (Fin m) (Fin m) ℂ) * diagonal (fun i => (lam i : ℂ)) *
              star (U : Matrix (Fin m) (Fin m) ℂ)) ∂(unitaryProbability (A := Fin m)))
    (k : Fin m → ℝ) (s : Set (Fin m → ℝ)) (hs : MeasurableSet s) :
    ENNReal.ofReal Cw * ∫⁻ lam in weylChamber m,
        ENNReal.ofReal (SpectralConvexity.vandermonde lam ^ 2) *
          (s.indicator 1 lam * ENNReal.ofReal (orbitalExp k lam)) =
      ENNReal.ofReal C * ∫⁻ lam in weylChamber m,
        ENNReal.ofReal (SpectralConvexity.vandermonde lam) * s.indicator 1 lam *
          gtMarginal k lam := by
  have hg : Measurable (s.indicator (1 : (Fin m → ℝ) → ℝ≥0∞)) := measurable_one.indicator hs
  have hf : Measurable fun M : Matrix (Fin m) (Fin m) ℂ =>
      s.indicator 1 (fun j => freshEigenvalue M j) * ENNReal.ofReal (diagExp k M) :=
    (hg.comp measurable_freshEigs).mul
      (ENNReal.measurable_ofReal.comp (continuous_diagExp k).measurable)
  rw [← hlaw _ hg k, hW _ hf]
  congr 1
  refine setLIntegral_congr_fun isOpen_weylChamber.measurableSet fun lam hlam => ?_
  congr 1
  have hU : ∀ U : Matrix.unitaryGroup (Fin m) ℂ,
      s.indicator 1 (fun j => freshEigenvalue ((U : Matrix (Fin m) (Fin m) ℂ) *
          diagonal (fun i => (lam i : ℂ)) * star (U : Matrix (Fin m) (Fin m) ℂ)) j) *
        ENNReal.ofReal (diagExp k ((U : Matrix (Fin m) (Fin m) ℂ) *
          diagonal (fun i => (lam i : ℂ)) * star (U : Matrix (Fin m) (Fin m) ℂ))) =
      s.indicator 1 lam * ENNReal.ofReal (Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ))) := by
    intro U
    rw [freshEigenvalue_conj_diagonal U (show StrictMono lam from hlam).monotone]
    rfl
  have hm : Measurable fun U : Matrix.unitaryGroup (Fin m) ℂ =>
      ENNReal.ofReal (Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ))) :=
    ENNReal.measurable_ofReal.comp (continuous_diagPhase_exp_right k lam).measurable
  rw [lintegral_congr hU, lintegral_const_mul _ hm, lintegral_exp_diagPhase]

/-- **The Gelfand–Tsetlin formula from the diagonal-corner bordered law.** -/
theorem gelfandTsetlin_of_border (hD : DiagonalBorderLawStatement) :
    EigenDensity.GelfandTsetlinStatement := by
  intro m
  obtain ⟨C, hC, hlaw⟩ := gtLaw_of_border hD m
  obtain ⟨Cw, hCw, hW⟩ := weylIntegration_of_diagonalBorderLaw hD m
  refine ⟨C / Cw, div_pos hC hCw, fun lam hlam k => ?_⟩
  set ch := weylChamber m
  have hch : MeasurableSet ch := isOpen_weylChamber.measurableSet
  set G1 : (Fin m → ℝ) → ℝ := fun x =>
    Cw * (SpectralConvexity.vandermonde x ^ 2 * orbitalExp k x) with hG1
  set G2 : (Fin m → ℝ) → ℝ := fun x =>
    C * (SpectralConvexity.vandermonde x * (gtMarginal k x).toReal) with hG2
  have hG1c : Continuous G1 :=
    continuous_const.mul ((continuous_vandermonde.pow 2).mul (continuous_orbitalExp k))
  have hG2c : Continuous G2 := by
    refine continuous_const.mul (continuous_vandermonde.mul ?_)
    exact ENNReal.continuousOn_toReal.comp_continuous (continuous_gtMarginal k)
      fun x => gtMarginal_ne_top k x
  set F1 : (Fin m → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal Cw *
    (ENNReal.ofReal (SpectralConvexity.vandermonde x ^ 2) * ENNReal.ofReal (orbitalExp k x))
    with hF1
  set F2 : (Fin m → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal C *
    (ENNReal.ofReal (SpectralConvexity.vandermonde x) * gtMarginal k x) with hF2
  have hF1m : Measurable F1 := measurable_const.mul
    ((ENNReal.measurable_ofReal.comp (continuous_vandermonde.pow 2).measurable).mul
      (ENNReal.measurable_ofReal.comp (continuous_orbitalExp k).measurable))
  have hF2m : Measurable F2 := measurable_const.mul
    ((ENNReal.measurable_ofReal.comp continuous_vandermonde.measurable).mul
      (measurable_gtMarginal k))
  have hae : F1 =ᵐ[volume.restrict ch] F2 := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hF1m hF2m fun s hs _ => ?_
    rw [← lintegral_indicator hs, ← lintegral_indicator hs]
    have h1 : ∀ x, s.indicator F1 x = ENNReal.ofReal Cw *
        (ENNReal.ofReal (SpectralConvexity.vandermonde x ^ 2) *
          (s.indicator 1 x * ENNReal.ofReal (orbitalExp k x))) := by
      intro x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, mul_zero,
          mul_zero]
    have h2 : ∀ x, s.indicator F2 x = ENNReal.ofReal C *
        (ENNReal.ofReal (SpectralConvexity.vandermonde x) * s.indicator 1 x * gtMarginal k x) := by
      intro x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, zero_mul,
          mul_zero]
    simp_rw [h1, h2]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact weyl_eq_gt hlaw hW k s hs
  have hae' : (fun x => ENNReal.ofReal (G1 x)) =ᵐ[volume.restrict ch]
      fun x => ENNReal.ofReal (G2 x) := by
    have hA : ∀ x, F1 x = ENNReal.ofReal (G1 x) := fun x => by
      simp only [hF1, hG1]
      rw [ENNReal.ofReal_mul hCw.le, ENNReal.ofReal_mul (sq_nonneg _)]
    have hB : ∀ x ∈ ch, F2 x = ENNReal.ofReal (G2 x) := fun x hx => by
      simp only [hF2, hG2]
      rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul (vandermonde_pos hx).le,
        ENNReal.ofReal_toReal (gtMarginal_ne_top k x)]
    filter_upwards [hae, ae_restrict_mem hch] with x hx hxc
    rw [← hA x, ← hB x hxc, hx]
  have heq := Measure.eqOn_open_of_ae_eq hae' isOpen_weylChamber
    (ENNReal.continuous_ofReal.comp hG1c).continuousOn
    (ENNReal.continuous_ofReal.comp hG2c).continuousOn hlam
  have hpos := vandermonde_pos hlam
  have hG2nn : 0 ≤ G2 lam :=
    mul_nonneg hC.le (mul_nonneg hpos.le ENNReal.toReal_nonneg)
  have hreal : G1 lam = G2 lam :=
    (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg hCw.le
      (mul_nonneg (sq_nonneg _) (orbitalExp_nonneg k lam))) hG2nn).1 heq
  simp only [hG1, hG2] at hreal
  have hfinal : SpectralConvexity.vandermonde lam * orbitalExp k lam =
      C / Cw * (gtMarginal k lam).toReal := by
    field_simp
    nlinarith [hreal]
  change ENNReal.ofReal (SpectralConvexity.vandermonde lam * orbitalExp k lam) = _
  rw [hfinal, ENNReal.ofReal_mul (div_pos hC hCw).le,
    ENNReal.ofReal_toReal (gtMarginal_ne_top k lam)]
  rfl

end BlockBand.DeterminantScore.GelfandTsetlin
