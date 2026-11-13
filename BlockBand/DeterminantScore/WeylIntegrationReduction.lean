module

public import BlockBand.DeterminantScore.EigenDensityWeyl

/-!
# Weyl integration: reduction to the eigenvalue law of Lebesgue measure

The Weyl integration formula for Hermitian matrices splits into two independent facts.

* **Angular part (proved here).** Lebesgue measure on the coordinates `HermCoord m` is invariant
  under every unitary conjugation (`lintegral_unitaryCoord`, derived from the unitary invariance of
  `G_m(1)`, `map_unitaryCoord_hermGaussian`, and the conjugation invariance of its density); the
  normalized Haar measure is right invariant (`map_mul_right_unitaryProbability`, by uniqueness of
  Haar probability measures on the compact group). Averaging over the orbit then gives
  `∫ f(H(x)) dx = ∫ F_f(λ(H(x))) dx` with `F_f(λ) = ∫_{U(m)} f(U diag(λ) U*) dU`.
* **Radial part (named `Prop`).** `WeylEigenLawStatement`: the increasing eigenvalues of `H(x)`
  under Lebesgue measure on `HermCoord m` have the density `C_m Δ(λ)²` on the open Weyl chamber.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory MeasureTheory.Measure Matrix BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.QUE.Haar
open BlockBand.DeterminantScore.SpectralConvexity (weylChamber)
open scoped ENNReal NNReal

variable {m : ℕ}

/-- **Eigenvalue law of Lebesgue measure on Hermitian matrices** (the radial half of the Weyl
integration formula; e.g. Anderson–Guionnet–Zeitouni, *An Introduction to Random Matrices*,
Thm. 2.5.2 and §4.1). For each `m` there is `C > 0` such that for every measurable `g ≥ 0` on
`ℝ^m`, `∫ g(λ(H(x))) dx = C ∫_𝒞 Δ(λ)² g(λ) dλ`, Lebesgue measure on the coordinates `HermCoord m`,
`λ = freshEigenvalue` the increasing eigenvalues, `𝒞` the open chamber `StrictMono`. -/
def WeylEigenLawStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
    ∫⁻ x, g (fun k => freshEigenvalue (hermOfCoord x) k) =
      ENNReal.ofReal C * ∫⁻ lam in weylChamber m, ENNReal.ofReal (SpectralConvexity.vandermonde lam ^ 2) * g lam

/-- `U diag(λ) U*`. -/
def conjDiag (U : Matrix.unitaryGroup (Fin m) ℂ) (lam : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  (U : Matrix (Fin m) (Fin m) ℂ) * diagonal (fun i => (lam i : ℂ)) *
    star (U : Matrix (Fin m) (Fin m) ℂ)

theorem continuous_conjDiag :
    Continuous fun p : Matrix.unitaryGroup (Fin m) ℂ × (Fin m → ℝ) => conjDiag p.1 p.2 := by
  unfold conjDiag
  have hU : Continuous fun p : Matrix.unitaryGroup (Fin m) ℂ × (Fin m → ℝ) =>
      ((p.1 : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hD : Continuous fun p : Matrix.unitaryGroup (Fin m) ℂ × (Fin m → ℝ) =>
      diagonal (fun i => (p.2 i : ℂ)) := by
    refine continuous_matrix fun a b => ?_
    simp only [diagonal_apply]
    split_ifs
    · exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_snd)
    · exact continuous_const
  exact (hU.matrix_mul hD).matrix_mul hU.star

/-- The orbit average `F_f(λ) = ∫_{U(m)} f(U diag(λ) U*) dU`. -/
def orbitAverage (f : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞) (lam : Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ U, f (conjDiag U lam) ∂(unitaryProbability (A := Fin m))

theorem measurable_orbitAverage {f : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (orbitAverage f) := by
  have hj : Measurable fun p : (Fin m → ℝ) × Matrix.unitaryGroup (Fin m) ℂ =>
      f (conjDiag p.2 p.1) :=
    hf.comp (continuous_conjDiag.comp continuous_swap).measurable
  exact hj.lintegral_prod_right'

/-!
## Right invariance of the normalized Haar measure
-/

/-- The normalized Haar measure of the compact group `U(m)` is right invariant. -/
theorem map_mul_right_unitaryProbability (V : Matrix.unitaryGroup (Fin m) ℂ) :
    (unitaryProbability (A := Fin m)).map (· * V) = unitaryProbability := by
  set μ := unitaryProbability (A := Fin m)
  have hR : Measurable fun U : Matrix.unitaryGroup (Fin m) ℂ => U * V := measurable_mul_const V
  have : IsProbabilityMeasure (μ.map (· * V)) := inferInstance
  have : IsMulLeftInvariant (μ.map (· * V)) := by
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_mul g) hR]
    have : ((g * ·) ∘ (· * V) : Matrix.unitaryGroup (Fin m) ℂ → _) = (· * V) ∘ (g * ·) := by
      funext U; simp [mul_assoc]
    rw [this, ← Measure.map_map hR (measurable_const_mul g), map_mul_left_eq_self]
  have : IsHaarMeasure μ := by unfold μ unitaryProbability; infer_instance
  have h := isMulInvariant_eq_smul_of_compactSpace (μ.map (· * V)) μ
  have h1 := congrArg (fun ν : Measure (Matrix.unitaryGroup (Fin m) ℂ) => ν Set.univ) h
  simp only [measure_univ, Measure.smul_apply] at h1
  rw [h, show haarScalarFactor (μ.map (· * V)) μ = 1 by
    have h2 : (haarScalarFactor (μ.map (· * V)) μ : ℝ≥0∞) = 1 := by
      rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h1; exact h1.symm
    exact_mod_cast h2, one_smul]

theorem lintegral_mul_right_unitary {g : Matrix.unitaryGroup (Fin m) ℂ → ℝ≥0∞}
    (hg : Measurable g) (V : Matrix.unitaryGroup (Fin m) ℂ) :
    ∫⁻ U, g (U * V) ∂(unitaryProbability (A := Fin m)) = ∫⁻ U, g U ∂unitaryProbability := by
  conv_rhs => rw [← map_mul_right_unitaryProbability V]
  rw [lintegral_map hg (measurable_mul_const V)]

/-!
## Unitary invariance of Lebesgue measure on `HermCoord m`
-/

open BlockBand.Angular.DetFactor in
theorem trace_sq_unitaryCoord {V : Matrix (Fin m) (Fin m) ℂ} (hV : Vᴴ * V = 1)
    (x : HermCoord m → ℝ) :
    (hermOfCoord (unitaryCoord V x) * hermOfCoord (unitaryCoord V x)).trace =
      (hermOfCoord x * hermOfCoord x).trace := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  rw [hermOfCoord_unitaryCoord]
  set H := hermOfCoord x
  rw [show Vᴴ * H * V * (Vᴴ * H * V) = Vᴴ * (H * (V * Vᴴ) * H * V) by simp only [Matrix.mul_assoc],
    hV', Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, hV', Matrix.mul_one]

open BlockBand.Angular.DetFactor in
/-- **Lebesgue measure on `HermCoord m` is invariant under unitary conjugation.** -/
theorem lintegral_unitaryCoord {f : (HermCoord m → ℝ) → ℝ≥0∞} (hf : Measurable f)
    {V : Matrix (Fin m) (Fin m) ℂ} (hV : Vᴴ * V = 1) :
    ∫⁻ x, f (unitaryCoord V x) = ∫⁻ x, f x := by
  have h1 : (0 : ℝ≥0) < 1 := one_pos
  set ρ : (HermCoord m → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (EigenDensity.hermGaussianDensity m 1 x) with hρ
  have hρm : Measurable ρ := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact Finset.measurable_prod _ fun c _ =>
      (ProbabilityTheory.measurable_gaussianPDFReal _ _).comp (measurable_pi_apply c)
  have hρpos : ∀ x, ρ x ≠ 0 := fun x => by
    simp only [hρ, ne_eq, ENNReal.ofReal_eq_zero, not_le, EigenDensity.hermGaussianDensity_eq h1]
    exact mul_pos (EigenDensity.hermGaussianConst_pos h1) (Real.exp_pos _)
  have hρtop : ∀ x, ρ x ≠ ⊤ := fun x => ENNReal.ofReal_ne_top
  have hρinv : ∀ x, ρ (unitaryCoord V x) = ρ x := fun x => by
    simp only [hρ, EigenDensity.hermGaussianDensity_eq h1, trace_sq_unitaryCoord hV]
  have hγ : ∀ h : (HermCoord m → ℝ) → ℝ≥0∞, Measurable h →
      ∫⁻ x, h x = ∫⁻ x, h x * (ρ x)⁻¹ ∂(hermGaussian m 1) := by
    intro h hh
    rw [EigenDensity.hermGaussian_eq_withDensity h1]
    rw [show (fun x => h x * (ρ x)⁻¹) = h * ρ⁻¹ from rfl,
      lintegral_withDensity_eq_lintegral_mul _ hρm (hh.mul hρm.inv)]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm, mul_assoc, Pi.inv_apply, ENNReal.inv_mul_cancel (hρpos x) (hρtop x), mul_one]
  have hL : Measurable (unitaryCoord V) := (continuous_unitaryCoord V).measurable
  rw [show (fun x => f (unitaryCoord V x)) = f ∘ unitaryCoord V from rfl, hγ _ (hf.comp hL),
    hγ _ hf]
  conv_rhs => rw [← map_unitaryCoord_hermGaussian 1 hV]
  rw [lintegral_map (f := fun x => f x * (ρ x)⁻¹) (hf.mul hρm.inv) hL]
  simp only [hρinv, Function.comp_apply]

/-!
## Orbit averaging
-/

/-- The unitary matrix `V` with columns permuted by `e`. -/
def permCols (V : Matrix.unitaryGroup (Fin m) ℂ) (e : Fin m ≃ Fin m) :
    Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨(V : Matrix (Fin m) (Fin m) ℂ).submatrix id e, by
    rw [Matrix.mem_unitaryGroup_iff']
    have h := Matrix.UnitaryGroup.star_mul_self V
    ext i j
    have hij := congrFun (congrFun h (e i)) (e j)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, id] at hij ⊢
    rw [hij]
    simp [Matrix.one_apply, e.injective.eq_iff]⟩

/-- Every Hermitian `H` is `W diag(λ(H)) W*` for a unitary `W`, `λ = freshEigenvalue`. -/
theorem exists_conjDiag_freshEigenvalue {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    ∃ W : Matrix.unitaryGroup (Fin m) ℂ, H = conjDiag W (fun k => freshEigenvalue H k) := by
  obtain ⟨e, he⟩ := SpectralConvexity.exists_equiv_freshEigenvalue hH
  refine ⟨permCols hH.eigenvectorUnitary e, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  ext i j
  simp only [conjDiag, permCols, he, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    Matrix.submatrix_apply, id, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact (Equiv.sum_comp e (fun l => (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) i l *
    ((hH.eigenvalues l : ℝ) : ℂ) * star ((hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) j l))).symm

/-- The orbit integral of a Hermitian `H` depends only on its increasing eigenvalues. -/
theorem lintegral_conj_eq_orbitAverage {f : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞} (hf : Measurable f)
    {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    ∫⁻ U, f ((U : Matrix (Fin m) (Fin m) ℂ) * H * star (U : Matrix (Fin m) (Fin m) ℂ))
        ∂(unitaryProbability (A := Fin m)) =
      orbitAverage f (fun k => freshEigenvalue H k) := by
  obtain ⟨W, hW⟩ := exists_conjDiag_freshEigenvalue hH
  set lam := fun k => freshEigenvalue H k
  have hconj : ∀ U : Matrix.unitaryGroup (Fin m) ℂ,
      (U : Matrix (Fin m) (Fin m) ℂ) * H * star (U : Matrix (Fin m) (Fin m) ℂ) =
        conjDiag (U * W) lam := by
    intro U
    rw [hW]
    simp only [conjDiag, Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  simp_rw [hconj]
  exact lintegral_mul_right_unitary
    (hf.comp ((continuous_conjDiag.comp (continuous_id.prodMk continuous_const)).measurable)) W

/-- **Reduction of the Weyl integration formula to the eigenvalue law of Lebesgue measure.** -/
theorem weylIntegration_of_eigenLaw (hE : WeylEigenLawStatement) :
    EigenDensity.WeylIntegrationStatement := by
  intro m
  obtain ⟨C, hC, hlaw⟩ := hE m
  refine ⟨C, hC, fun f hf => ?_⟩
  have hHm : Measurable (hermOfCoord (m := m)) := continuous_hermOfCoord.measurable
  -- Step 1: average the conjugation-invariant Lebesgue integral over the Haar probability.
  have hstep1 : ∫⁻ x, f (hermOfCoord x) = ∫⁻ U, ∫⁻ x, f ((U : Matrix (Fin m) (Fin m) ℂ) *
      hermOfCoord x * star (U : Matrix (Fin m) (Fin m) ℂ)) ∂volume
        ∂(unitaryProbability (A := Fin m)) := by
    have hU : ∀ U : Matrix.unitaryGroup (Fin m) ℂ,
        ∫⁻ x, f ((U : Matrix (Fin m) (Fin m) ℂ) * hermOfCoord x *
          star (U : Matrix (Fin m) (Fin m) ℂ)) = ∫⁻ x, f (hermOfCoord x) := by
      intro U
      set V : Matrix (Fin m) (Fin m) ℂ := star (U : Matrix (Fin m) (Fin m) ℂ)
      have hVH : Vᴴ = (U : Matrix (Fin m) (Fin m) ℂ) := by
        simp [V, Matrix.star_eq_conjTranspose]
      have hV : Vᴴ * V = 1 := by rw [hVH]; exact Matrix.mem_unitaryGroup_iff.1 U.2
      have := lintegral_unitaryCoord (hf.comp hHm) hV
      simp only [Function.comp_apply, BlockBand.Angular.DetFactor.hermOfCoord_unitaryCoord,
        hVH] at this
      exact this
    simp_rw [hU]
    rw [lintegral_const, measure_univ, mul_one]
  -- Step 2: Tonelli.
  have hjoint : Measurable fun p : Matrix.unitaryGroup (Fin m) ℂ × (HermCoord m → ℝ) =>
      f ((p.1 : Matrix (Fin m) (Fin m) ℂ) * hermOfCoord p.2 *
        star (p.1 : Matrix (Fin m) (Fin m) ℂ)) := by
    refine hf.comp (Continuous.measurable ?_)
    have hU : Continuous fun p : Matrix.unitaryGroup (Fin m) ℂ × (HermCoord m → ℝ) =>
        ((p.1 : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
      continuous_subtype_val.comp continuous_fst
    exact (hU.matrix_mul (continuous_hermOfCoord.comp continuous_snd)).matrix_mul hU.star
  rw [hstep1, lintegral_lintegral_swap hjoint.aemeasurable]
  -- Step 3: the orbit integral is a function of the eigenvalues.
  simp_rw [lintegral_conj_eq_orbitAverage hf (isHermitian_hermOfCoord _)]
  -- Step 4: the eigenvalue law.
  rw [hlaw _ (measurable_orbitAverage hf)]
  rfl

end BlockBand.DeterminantScore.WeylIntegration
