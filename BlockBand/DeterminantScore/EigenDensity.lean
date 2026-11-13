module

public import BlockBand.DeterminantScore.SpectralConvexity
public import BlockBand.QUE.Haar.CompactUnitary
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The eigenvalue density of `K + G_m(t)` through the HCIZ integral

Let `I_K(λ) = ∫_{U(m)} exp(Re tr(diag(λ) U* K U)/t) dU` (normalized Haar measure; the
Harish-Chandra–Itzykson–Zuber integral, here only as an integral). Since `G_m(t)` has the
Lebesgue density `∝ exp(-tr H²/(2t))`, the Weyl integration formula gives the ordered eigenvalue
density `c Δ(λ)² e^{-|λ|²/(2t)} I_K(λ)` on the Weyl chamber, with `c > 0` (the factor
`e^{-tr K²/(2t)}` is absorbed in `c`). Hence `OrderedEigenDensityStatement` holds with
`S = c Δ I_K`, provided `Δ I_K` is log-concave on the chamber. The two analytic inputs are
isolated as intermediate `Prop`s:

* `WeylHCIZDensityStatement`: the Weyl/HCIZ form of the eigenvalue density, derived from
  `WeylIntegrationStatement` (`weylHCIZDensity_of`);
* `HCIZLogConcaveStatement`: `-log(Δ I_K)` is convex on the chamber, for every Hermitian `K`
  (repeated eigenvalues included), derived from Prékopa's theorem and `GelfandTsetlinStatement`
  (`hczLogConcave_of`).

## Results

* `contDiff_hcizIntegral`, `hcizIntegral_pos`: `I_K ∈ C²(ℝ^m)` (differentiation under the
  integral over the compact group) and `I_K > 0`.
* `orderedEigenDensity_of`: `WeylHCIZDensityStatement` and `HCIZLogConcaveStatement` imply
  `OrderedEigenDensityStatement` exactly (`S = c Δ I_K`; positivity, `C²` and convexity of
  `-log S` proved).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.EigenDensity

open MeasureTheory Matrix Metric BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.QUE.Haar
open BlockBand.DeterminantScore.SpectralConvexity (weylChamber isOpen_weylChamber vandermonde_pos
  OrderedEigenDensityStatement)
open scoped ENNReal NNReal

/-!
### Differentiation of exponential integrals over a compact space
-/

section ExpIntegral

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  (ℓ : X → StrongDual ℝ H)

omit [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem exists_norm_bound {E : Type*} [NormedAddCommGroup E] {f : X → E} (hf : Continuous f) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x (Set.mem_univ x)).trans (le_max_left _ _)⟩

omit [FiniteDimensional ℝ H] in
/-- Differentiation under the integral sign: `∂_λ ∫ e^{ℓ_x(λ)} P(x) dμ = ∫ e^{ℓ_x(λ)} ℓ_x ⊗ P(x) dμ`
for continuous `ℓ`, `P` on a compact space. -/
theorem hasFDerivAt_expIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hℓ : Continuous ℓ) {P : X → E} (hP : Continuous P) (lam₀ : H) :
    HasFDerivAt (fun lam => ∫ x, Real.exp (ℓ x lam) • P x ∂μ)
      (∫ x, Real.exp (ℓ x lam₀) • (ℓ x).smulRight (P x) ∂μ) lam₀ := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bound hℓ
  obtain ⟨Q, hQ0, hQ⟩ := exists_norm_bound hP
  have hsR : Continuous fun x => (ℓ x).smulRight (P x) :=
    (ContinuousLinearMap.smulRightL ℝ H E).continuous₂.comp₂ hℓ hP
  have hexp : ∀ lam : H, Continuous fun x => Real.exp (ℓ x lam) :=
    fun lam => Real.continuous_exp.comp (hℓ.clm_apply continuous_const)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball lam₀ 1)
    (F' := fun lam x => Real.exp (ℓ x lam) • (ℓ x).smulRight (P x))
    (bound := fun _ => Real.exp (L * (‖lam₀‖ + 1)) * (L * Q)) (ball_mem_nhds lam₀ one_pos)
    (Filter.Eventually.of_forall fun lam => ((hexp lam).smul hP).aestronglyMeasurable)
    ?_ ((hexp lam₀).smul hsR).aestronglyMeasurable ?_ (integrable_const _) ?_
  · obtain ⟨C, hC0, hC⟩ := exists_norm_bound ((hexp lam₀).smul hP)
    exact Integrable.of_bound ((hexp lam₀).smul hP).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  · refine Filter.Eventually.of_forall fun x lam hlam => ?_
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hlam' : ‖lam‖ ≤ ‖lam₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' lam lam₀
      rw [mem_ball, dist_eq_norm] at hlam
      linarith
    have h1 : ℓ x lam ≤ L * (‖lam₀‖ + 1) :=
      (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hL x) hlam' (norm_nonneg _) hL0))
    gcongr
    · exact hL x
    · exact hQ x
  · refine Filter.Eventually.of_forall fun x lam _ => ?_
    have h := ((ℓ x).hasFDerivAt (x := lam)).exp.smul_const (P x)
    convert h using 1
    ext v
    simp [smul_smul, mul_comm]

theorem continuous_expIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hℓ : Continuous ℓ) {P : X → E} (hP : Continuous P) :
    Continuous (fun lam => ∫ x, Real.exp (ℓ x lam) • P x ∂μ) := by
  have := continuous_parametric_integral_of_continuous (μ := μ) (s := Set.univ)
    (f := fun lam x => Real.exp (ℓ x lam) • P x) ?_ isCompact_univ
  · simpa using this
  exact (Real.continuous_exp.comp ((hℓ.comp continuous_snd).clm_apply continuous_fst)).smul
    (hP.comp continuous_snd)

/-- `λ ↦ ∫ e^{ℓ_x(λ)} dμ(x)` is `C²` for continuous `ℓ` on a compact space. -/
theorem contDiff_two_expIntegral (hℓ : Continuous ℓ) :
    ContDiff ℝ 2 (fun lam => ∫ x, Real.exp (ℓ x lam) ∂μ) := by
  have hP1 : Continuous fun x => (ℓ x).smulRight (1 : ℝ) :=
    (ContinuousLinearMap.smulRightL ℝ H ℝ).continuous₂.comp₂ hℓ continuous_const
  have hP2 : Continuous fun x => (ℓ x).smulRight ((ℓ x).smulRight (1 : ℝ)) :=
    (ContinuousLinearMap.smulRightL ℝ H (H →L[ℝ] ℝ)).continuous₂.comp₂ hℓ hP1
  have h0 : (fun lam => ∫ x, Real.exp (ℓ x lam) ∂μ) =
      fun lam => ∫ x, Real.exp (ℓ x lam) • (1 : ℝ) ∂μ := by simp
  rw [h0, show (2 : WithTop ℕ∞) = ((1 : ℕ) + 1 : ℕ) by norm_num]
  refine contDiff_succ_iff_hasFDerivAt.2 ?_
  refine ⟨_, ?_, hasFDerivAt_expIntegral μ ℓ hℓ continuous_const⟩
  refine (contDiff_one_iff_hasFDerivAt (𝕜 := ℝ)).2 ?_
  exact ⟨_, continuous_expIntegral μ ℓ hℓ hP2, hasFDerivAt_expIntegral μ ℓ hℓ hP1⟩

end ExpIntegral

/-!
### The HCIZ integral
-/

variable {m : ℕ}

/-- The phase `λ ↦ Re tr(diag(λ) U* K U)/t = Σ_i λ_i Re(U*KU)_{ii}/t`, a linear form. -/
def hcizPhase (t : ℝ) (K : Matrix (Fin m) (Fin m) ℂ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    StrongDual ℝ (Fin m → ℝ) :=
  ∑ i, ((((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * K * (U : Matrix (Fin m) (Fin m) ℂ)) i i).re / t) •
    ContinuousLinearMap.proj i

theorem hcizPhase_apply (t : ℝ) (K : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix.unitaryGroup (Fin m) ℂ) (lam : Fin m → ℝ) :
    hcizPhase t K U lam =
      ∑ i, (((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * K * (U : Matrix (Fin m) (Fin m) ℂ)) i i).re / t *
        lam i := by
  simp [hcizPhase]

theorem continuous_hcizPhase (t : ℝ) (K : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (hcizPhase t K) := by
  refine continuous_finsetSum _ fun i _ => ?_
  have hU : Continuous fun U : Matrix.unitaryGroup (Fin m) ℂ => (U : Matrix (Fin m) (Fin m) ℂ) :=
    continuous_subtype_val
  have hc : Continuous fun U : Matrix.unitaryGroup (Fin m) ℂ =>
      (((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * K * (U : Matrix (Fin m) (Fin m) ℂ)) i i).re / t :=
    (Complex.continuous_re.comp
      (((hU.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hU).matrix_elem i i)).div_const _
  exact hc.smul (continuous_const (y := (ContinuousLinearMap.proj i : StrongDual ℝ (Fin m → ℝ))))

/-- **The HCIZ integral** `I_K(λ) = ∫_{U(m)} exp(Re tr(diag(λ) U* K U)/t) dU` (normalized Haar
measure `unitaryProbability`). -/
def hcizIntegral (t : ℝ) (K : Matrix (Fin m) (Fin m) ℂ) (lam : Fin m → ℝ) : ℝ :=
  ∫ U, Real.exp (hcizPhase t K U lam) ∂(unitaryProbability (A := Fin m))

theorem contDiff_hcizIntegral (t : ℝ) (K : Matrix (Fin m) (Fin m) ℂ) :
    ContDiff ℝ 2 (hcizIntegral t K) :=
  contDiff_two_expIntegral _ _ (continuous_hcizPhase t K)

theorem hcizIntegral_pos (t : ℝ) (K : Matrix (Fin m) (Fin m) ℂ) (lam : Fin m → ℝ) :
    0 < hcizIntegral t K lam := by
  have hc : Continuous fun U => Real.exp (hcizPhase t K U lam) :=
    Real.continuous_exp.comp ((continuous_hcizPhase t K).clm_apply continuous_const)
  obtain ⟨C, -, hC⟩ := exists_norm_bound hc
  exact integral_exp_pos (Integrable.of_bound hc.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC))

/-!
### The two analytic inputs
-/

/-- **Weyl/HCIZ form of the eigenvalue density of `K + G_m(t)`** (unitary invariance of `G_m(t)`,
its Lebesgue density `∝ e^{-tr H²/(2t)}` and the Weyl integration formula `dH = c_m Δ(λ)² dλ dU`
on the chamber). For `t > 0` and Hermitian `K` there is `c > 0` (it contains `e^{-tr K²/(2t)}` and
the Weyl and Gaussian constants) such that the increasing eigenvalues of `K + G_m(t)` have the
density `c Δ(λ)² e^{-|λ|²/(2t)} I_K(λ)` on the chamber and do not charge its complement.
Derived from `WeylIntegrationStatement` as `weylHCIZDensity_of`. -/
def WeylHCIZDensityStatement : Prop :=
  ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ), 0 < t → K.IsHermitian →
    ∃ c : ℝ, 0 < c ∧ ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (orderedEigs K x) ∂hermGaussian m t =
        ∫⁻ lam in weylChamber m, ENNReal.ofReal (c * SpectralConvexity.vandermonde lam ^ 2 *
          Real.exp (-(∑ j, lam j ^ 2) / (2 * (t : ℝ))) * hcizIntegral t K lam) * g lam

/-- **Log-concavity of `Δ I_K` on the chamber.** Derived for every Hermitian `K` from Prékopa's
theorem and `GelfandTsetlinStatement` as `hczLogConcave_of` (no repeated-eigenvalue limit is
needed). -/
def HCIZLogConcaveStatement : Prop :=
  ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ), 0 < t → K.IsHermitian →
    ConvexOn ℝ (weylChamber m) fun lam =>
      -Real.log (SpectralConvexity.vandermonde lam * hcizIntegral t K lam)

/-!
### Assembly
-/

theorem contDiff_vandermonde : ContDiff ℝ 2 (SpectralConvexity.vandermonde (m := m)) := by
  unfold SpectralConvexity.vandermonde
  refine contDiff_prod fun i _ => contDiff_prod fun j _ => ?_
  split_ifs
  · exact ((contDiff_apply ℝ ℝ j).sub (contDiff_apply ℝ ℝ i))
  · exact contDiff_const

/-- **`OrderedEigenDensityStatement` from the Weyl/HCIZ density and log-concavity of `Δ I_K`**:
with `S = c Δ I_K`, `S > 0` and `S ∈ C²` on the chamber are proved, and
`-log S = -log c - log(Δ I_K)`. -/
theorem orderedEigenDensity_of (hW : WeylHCIZDensityStatement) (hL : HCIZLogConcaveStatement) :
    OrderedEigenDensityStatement := by
  refine ⟨fun m t K ht hK => ?_⟩
  obtain ⟨c, hc, hrep⟩ := hW m t K ht hK
  refine ⟨fun lam => c * (SpectralConvexity.vandermonde lam * hcizIntegral t K lam), ?_, ?_, ?_, ?_⟩
  · exact fun lam hlam => mul_pos hc (mul_pos (vandermonde_pos hlam) (hcizIntegral_pos _ _ _))
  · exact (contDiff_const.mul (contDiff_vandermonde.mul (contDiff_hcizIntegral _ K))).contDiffOn
  · refine ((hL m t K ht hK).add_const (-Real.log c)).congr fun lam hlam => ?_
    have h1 := vandermonde_pos hlam
    have h2 := hcizIntegral_pos (t : ℝ) K lam
    simp only [Pi.add_apply]
    rw [Real.log_mul hc.ne' (mul_pos h1 h2).ne']
    ring
  · intro g hg
    rw [hrep g hg]
    refine setLIntegral_congr_fun isOpen_weylChamber.measurableSet fun lam _ => ?_
    congr 2
    ring

end BlockBand.DeterminantScore.EigenDensity
