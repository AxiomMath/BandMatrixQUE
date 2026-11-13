module

public import BlockBand.Window.SmallCritical.StationaryWeight
public import BlockBand.Window.Transfer.WindowTransfer
public import BlockBand.QUE.Fourier.PhysicalIntegrability

/-!
# Bridges from marked mark-functionals to the physical window expectation

* `physicalOrderedEigenvector_add_scalar`: the selected eigenvector is invariant under
  `H ↦ H + tI` for **every** raw matrix (Hermitian case: adopted
  `physicalOrderedEigenvector_gaussianSpectralTranslate`; otherwise both sides are the raw
  default); hence every function of the site masses is `IsScalarShiftInvariant`.
* `lintegral_le_windowExpectation`: if `g(ν_α) ≤ c A_α` a.s., then
  `E Σ_α ofReal(w(u_α) g(ν_α)) ≤ ofReal(c 𝒱_{n,W})`, `u_α = Nρ(E)(λ_α - E)`.
* `integral_physicalOrderedProfile`: on Hermitian simple-spectrum matrices,
  `∫ f dν_α = Σ_k p_{αk} f(k/n)`; `fourier_profile_eq_physicalMode`:
  `∫ e^{-2πimr} ν_α(dr) = A_{α,m}` (`physicalMode α m`, `m` reduced mod `n`).
* `modeSeparation_ge`: `d_m ≥ 4|m|/n` for integers `0 < 2|m| ≤ n`.
* continuity of `ν ↦ ∫ f dν` on `P(𝕋)` for bounded continuous real or complex `f`.

Law: the physical law `model.law` of every `GaussianRingModel`; all finite parameters.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.SmallCritical

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular BlockBand.QUE.Fourier
open scoped ENNReal NNReal

attribute [local instance] massProfile_opensMeasurableSpace

variable {p : Parameters}

/-!
### Scalar-shift invariance
-/

theorem physicalOrderedEigenvector_add_scalar (p : Parameters) (H : p.SiteMatrix) (t : ℝ)
    (α : Fin p.N) (x : p.Site) :
    physicalOrderedEigenvector p (H + (t : ℂ) • (1 : p.SiteMatrix)) α x =
      physicalOrderedEigenvector p H α x := by
  by_cases hH : H.IsHermitian
  · exact physicalOrderedEigenvector_gaussianSpectralTranslate p t H hH α x
  · have hH' : ¬ (H + (t : ℂ) • (1 : p.SiteMatrix)).IsHermitian := by
      intro h
      apply hH
      have := isHermitian_gaussianSpectralTranslate (-t) _ h
      simpa [gaussianSpectralTranslate, add_assoc] using this
    simp only [physicalOrderedEigenvector, rawOrderedColumnSelection, rawHermitianExtension,
      hH, hH', dite_false]

/-- Every function of the selected eigenvector is invariant under real scalar shifts. -/
theorem isScalarShiftInvariant_eigenvector (α : Fin p.N) (Φ : (p.Site → ℂ) → ℝ) :
    IsScalarShiftInvariant (fun H : p.SiteMatrix => Φ (physicalOrderedEigenvector p H α)) := by
  intro H t
  simp only
  congr 1
  funext x
  exact physicalOrderedEigenvector_add_scalar p H t α x

/-- Every function of the block masses is invariant under real scalar shifts. -/
theorem isScalarShiftInvariant_blockMass (α : Fin p.N) (Φ : (ZMod p.n → ℝ) → ℝ) :
    IsScalarShiftInvariant (fun H : p.SiteMatrix =>
      Φ (fun k => physicalOrderedBlockMass p H α k)) := by
  intro H t
  simp only [physicalOrderedBlockMass, physicalOrderedEigenvector_add_scalar]

/-!
### From mark functionals to the window expectation
-/

/-- If `0 ≤ g(ν_α) ≤ c A_α` almost surely for all ranks, the finite marked expectation is
bounded by `c` times the physical window expectation (`ρ = ρ_sc(E)`). -/
theorem lintegral_le_windowExpectation (model : p.GaussianRingModel) (E : ℝ)
    {w : ℝ → ℝ} (hwc : Continuous w) (hws : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u)
    {g : MassProfile → ℝ} (hg0 : ∀ ν, 0 ≤ g ν) (A : Fin p.N → p.SiteMatrix → ℝ) (hAm : ∀ α, Measurable (A α))
    (hA01 : ∀ α H, 0 ≤ A α H ∧ A α H ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (hgA : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ α,
      g (physicalOrderedProfile p H α) ≤ c * A α H) :
    ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal
        (w ((p.N : ℝ) * Parameters.semicircleDensity E * (physicalOrderedEigenvalue p H α - E)) *
          g (physicalOrderedProfile p H α)) ∂(model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (c * windowExpectation p model E (Parameters.semicircleDensity E) w A) := by
  set ρ := Parameters.semicircleDensity E
  set F : p.SiteMatrix → ℝ := fun H => ∑ α : Fin p.N,
      w ((p.N : ℝ) * ρ * (physicalOrderedEigenvalue p H α - E)) * A α H with hF
  obtain ⟨Mw, hMw⟩ := hws.exists_bound_of_continuous hwc
  have hFm : Measurable F := by
    refine Finset.measurable_sum _ fun α _ => ?_
    exact (hwc.measurable.comp (measurable_const.mul
      ((measurable_physicalOrderedEigenvalue p α).sub_const E))).mul (hAm α)
  have hF0 : ∀ H, 0 ≤ F H := fun H =>
    Finset.sum_nonneg fun α _ => mul_nonneg (hw0 _) (hA01 α H).1
  have hFb : ∀ H, ‖F H‖ ≤ (p.N : ℝ) * Mw := by
    intro H
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 H)]
    calc F H ≤ ∑ _α : Fin p.N, Mw := by
          refine Finset.sum_le_sum fun α _ => ?_
          have h1 := hMw ((p.N : ℝ) * ρ * (physicalOrderedEigenvalue p H α - E))
          rw [Real.norm_eq_abs, abs_of_nonneg (hw0 _)] at h1
          calc w _ * A α H ≤ w _ * 1 := mul_le_mul_of_nonneg_left (hA01 α H).2 (hw0 _)
            _ ≤ Mw := by rw [mul_one]; exact h1
      _ = (p.N : ℝ) * Mw := by simp
  have hFi : Integrable F (model.law : Measure p.SiteMatrix) :=
    (integrable_const ((p.N : ℝ) * Mw)).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall hFb)
  have hwin : windowExpectation p model E ρ w A = ∫ H, F H ∂(model.law : Measure p.SiteMatrix) :=
    rfl
  rw [hwin, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hFi.const_mul c)
    (Eventually.of_forall fun H => mul_nonneg hc (hF0 H))]
  apply lintegral_mono_ae
  filter_upwards [hgA] with H hH
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · apply ENNReal.ofReal_le_ofReal
    rw [hF, Finset.mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    calc w _ * g (physicalOrderedProfile p H α) ≤ w _ * (c * A α H) :=
          mul_le_mul_of_nonneg_left (hH α) (hw0 _)
      _ = c * (w _ * A α H) := by ring
  · intro α _
    exact mul_nonneg (hw0 _) (hg0 _)

/-!
### Profile integrals
-/

/-- On Hermitian simple-spectrum matrices the profile is the block-mass Dirac sum, so
`∫ f dν_α = Σ_k p_{αk} f(k/n)` for every `f` into a complete real normed space. -/
theorem integral_physicalOrderedProfile {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (H : p.SiteMatrix) (hH : H.IsHermitian) (hsep : H.charpoly.Separable)
    (α : Fin p.N) (f : Torus → F) :
    ∫ r, f r ∂(physicalOrderedProfile p H α : Measure Torus) =
      ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k • f (physicalProfileGrid p k) := by
  rw [physicalOrderedProfile_eq p H hH hsep α, physicalOrderedProfileMeasure,
    integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (physicalOrderedBlockMass_nonneg p H α k)]
  · intro k _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The Fourier coefficient of the profile mark is the physical Fourier mode:
`∫ e^{-2πimr} ν_α(dr) = Σ_k z_m^{-k} p_{αk} = A_{α,m}` with `m` reduced mod `n`. -/
theorem fourier_profile_eq_physicalMode (H : p.SiteMatrix) (hH : H.IsHermitian)
    (hsep : H.charpoly.Separable) (α : Fin p.N) (m : ℤ) :
    ∫ r, fourier (-m) r ∂(physicalOrderedProfile p H α : Measure Torus) =
      physicalMode p α (m : ZMod p.n) H := by
  have : NeZero p.n := ⟨p.n_pos.ne'⟩
  rw [integral_physicalOrderedProfile H hH hsep α]
  unfold physicalMode mode
  simp only [ZMod.dft_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.real_smul, mul_comm]
  congr 1
  rw [physicalProfileGrid, fourier_coe_apply, ZMod.stdAddChar_apply]
  have hk : (-(k * (m : ZMod p.n)) : ZMod p.n) = ((-((k.val : ℤ) * m) : ℤ) : ZMod p.n) := by
    push_cast [ZMod.natCast_zmod_val]
    ring
  rw [hk, ZMod.toCircle_intCast]
  congr 1
  push_cast
  ring

/-!
### Mode separation
-/

/-- `d_m = |1 - e^{2πim/n}| ≥ 4|m|/n` for integers `0 < 2|m| ≤ n`. -/
theorem modeSeparation_ge (p : Parameters) (m : ℤ) (hm : 2 * |(m : ℝ)| ≤ p.n) :
    4 * |(m : ℝ)| / p.n ≤ modeSeparation p (m : ZMod p.n) := by
  have : NeZero p.n := ⟨p.n_pos.ne'⟩
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  unfold modeSeparation
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_intCast]
  have hexp : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (p.n : ℂ)) =
      Complex.I * ((2 * Real.pi * m / p.n : ℝ) : ℂ) := by
    push_cast; ring
  rw [hexp, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_two]
  have hhalf : 2 * Real.pi * (m : ℝ) / p.n / 2 = Real.pi * m / p.n := by ring
  rw [hhalf]
  have hx0 : 0 ≤ Real.pi * |(m : ℝ)| / p.n := by positivity
  have hx1 : Real.pi * |(m : ℝ)| / p.n ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hn (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hx0 hx1
  have habs : |Real.sin (Real.pi * m / p.n)| = Real.sin (Real.pi * |(m : ℝ)| / p.n) := by
    rcases le_or_gt 0 (m : ℝ) with h | h
    · rw [abs_of_nonneg h] at hx0 hx1 ⊢
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos]))
    · rw [abs_of_neg h]
      have : Real.pi * (m : ℝ) / p.n = -(Real.pi * -(m : ℝ) / p.n) := by ring
      rw [this, Real.sin_neg, abs_neg]
      have h' : 0 ≤ -(m : ℝ) := by linarith
      rw [abs_of_neg h] at hx0 hx1
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos]))
  rw [habs]
  have heq : 2 / Real.pi * (Real.pi * |(m : ℝ)| / p.n) = 2 * |(m : ℝ)| / p.n := by
    field_simp
  rw [heq] at hs
  calc 4 * |(m : ℝ)| / p.n = 2 * (2 * |(m : ℝ)| / p.n) := by ring
    _ ≤ 2 * Real.sin (Real.pi * |(m : ℝ)| / p.n) := by gcongr

/-!
### Continuity of profile integrals
-/

theorem continuous_profile_integral_real (f : Torus → ℝ) (hf : Continuous f) :
    Continuous (fun ν : MassProfile => ∫ r, f r ∂(ν : Measure Torus)) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)

theorem continuous_profile_integral_complex (f : Torus → ℂ) (hf : Continuous f) :
    Continuous (fun ν : MassProfile => ∫ r, f r ∂(ν : Measure Torus)) := by
  rw [continuous_iff_continuousAt]
  intro ν
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ
    (μs := fun μ : MassProfile => μ) (F := 𝓝 ν) (μ := ν)).mp tendsto_id
    (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)
  exact h

end BlockBand.Window.SmallCritical
