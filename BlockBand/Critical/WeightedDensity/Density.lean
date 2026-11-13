module

public import BlockBand.Critical.WeightedDensity.Spectral
public import BlockBand.Critical.PointDensity.MeanDensity

/-!
# The expected matrix spectral density `Σ_F(e)` of `F + G`

Support for the global weighted density lemma and the relative matrix density lemma.
`Σ_F(e)` is the expected matrix spectral density of `F + G`, `G` the `N`-dimensional GUE with
entry variance `c/N`; thus `∫_I Σ_F(e) de = E 1_I(F+G)`.

*Law.* `G ~ freshGUE N c = gueMeasure (Fin N) (c/N)`; the exact scalar split `G = A⁰ + ζ I`,
`A⁰ ~ freshTracelessLaw N c`, `ζ ~ N(0, c/N²)` independent (`scalarShiftLaw_fin_eq_gueMeasure`).
*Representation.* `E 1_B(F+G)` is the entrywise expectation of the Mathlib functional calculus
`cfc (B.indicator 1) (F + G)` (`expectedSpectralProjector`). A matrix spectral density is a
function `S : ℝ → Matrix` with `∫_{[a,b]} S_ij = E[1_{[a,b]}(F+G)]_ij` for all `a ≤ b` and all
entries (`IsMatrixSpectralDensity`). The canonical version is
`sigma F c e = Σ_ℓ E_{A⁰}[w_{ℓ,e} u_ℓ u_ℓ*]` with the scalar Palm weight
`w_{ℓ,e} = palmWeight F c e ℓ A⁰` and the fixed eigenvector selection `u_ℓ` of `F + A⁰`.
*Domain.* every `N ≥ 1`, every Hermitian `F` (no norm bound), every `c > 0`, every Borel set
`B`, every `e ∈ ℝ`. Exact identities; no limit, norm or uniformity statement.

## Main results

* `continuous_sigma_apply`, `sigma_isHermitian`: the canonical version is continuous and
  Hermitian.
* `setIntegral_sigma_apply`: `∫_B Σ_F(e)_ij de = E[1_B(F+G)]_ij` for **every** Borel `B`
  (with integrability); `isMatrixSpectralDensity_sigma`.
* `eq_sigma_of_isMatrixSpectralDensity`: every continuous matrix spectral density equals the
  canonical one everywhere.
* `ofReal_quadForm_sigma`: `q* Σ_F(e) q = Σ_ℓ E_{A⁰}[w_{ℓ,e} |q* u_ℓ|²]` (as extended reals).
* `lintegral_sigmaKernel_eq`: the eigenpair kernel identity
  `∫ de Σ_ℓ E_{A⁰}[w_{ℓ,e} Ψ(e, u_ℓ)] = E_G Σ_ℓ Ψ(λ_ℓ(F+G), u_ℓ(F+G))` for measurable `Ψ ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.WeightedDensity

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.FreshPalm BlockBand.Coarea.GUELaw
  BlockBand.Coarea.PoleExclusion BlockBand.Critical.PointDensity
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

/-!
## Definitions
-/

/-- The fresh Gaussian law `GUE_N(c/N)` (entry variance `c/N`). -/
abbrev freshGUE (N : ℕ) (c : ℝ) : Measure (Matrix (Fin N) (Fin N) ℂ) :=
  gueMeasure (Fin N) (Real.toNNReal (c / N))

/-- `E 1_B(F + G)`, `G ~ GUE_N(c/N)`: the entrywise expectation of the spectral projector
`1_B(F + G) = cfc (B.indicator 1) (F + G)`. -/
def expectedSpectralProjector (N : ℕ) (c : ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (B : Set ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ∫ G, cfc (B.indicator (1 : ℝ → ℝ)) (F + G) i j ∂freshGUE N c

/-- `S` is a matrix spectral density of `F + G`: `∫_{[a,b]} S(e) de = E 1_{[a,b]}(F + G)`
entrywise, for all `a ≤ b`. -/
def IsMatrixSpectralDensity (N : ℕ) (c : ℝ) (F : Matrix (Fin N) (Fin N) ℂ)
    (S : ℝ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∀ i j : Fin N,
    ∫ e in Set.Icc a b, S e i j = expectedSpectralProjector N c F (Set.Icc a b) i j

/-- The canonical version `Σ_F(e) = Σ_ℓ E_{A⁰}[w_{ℓ,e} u_ℓ u_ℓ*]` (entrywise Bochner integrals). -/
def sigma (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ∑ ℓ : Fin N,
    ∫ A0, (palmWeight F c e ℓ A0 : ℂ) * freshProjector (F + A0) ℓ i j ∂freshTracelessLaw N c

/-!
## Elementary bounds and measurability
-/

theorem palmWeight_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ palmWeight F c e ℓ A0 :=
  BlockBand.Palm.scalarWeight_nonneg _ _ _ _

theorem palmWeight_le (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : palmWeight F c e ℓ A0 ≤ densityBound c N :=
  BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _

theorem densityBound_nonneg (c : ℝ) (N : ℕ) : 0 ≤ densityBound c N :=
  inv_nonneg.2 (Real.sqrt_nonneg _)

theorem norm_freshEigenvector_apply_le (K : Matrix (Fin N) (Fin N) ℂ) (ℓ i : Fin N) :
    ‖freshEigenvector K ℓ i‖ ≤ 1 := by
  have h := BlockBand.Palm.FreshPalmAssembly.sum_norm_sq_freshEigenvector_le K ℓ
  have hi : ‖freshEigenvector K ℓ i‖ ^ 2 ≤ ∑ x, ‖freshEigenvector K ℓ x‖ ^ 2 :=
    Finset.single_le_sum (f := fun x => ‖freshEigenvector K ℓ x‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ‖freshEigenvector K ℓ i‖ ^ 2 ≤ 1 ^ 2 := by rw [one_pow]; exact hi.trans h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h2

theorem norm_freshProjector_apply_le (K : Matrix (Fin N) (Fin N) ℂ) (ℓ i j : Fin N) :
    ‖freshProjector K ℓ i j‖ ≤ 1 := by
  simp only [freshProjector, vecMulVec_apply, Pi.star_apply, norm_mul, norm_star]
  exact (mul_le_mul (norm_freshEigenvector_apply_le K ℓ i) (norm_freshEigenvector_apply_le K ℓ j)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem measurable_palmWeight_prod (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (ℓ : Fin N) :
    Measurable fun p : ℝ × Matrix (Fin N) (Fin N) ℂ => palmWeight F c p.1 ℓ p.2 := by
  unfold palmWeight BlockBand.Palm.scalarWeight
  exact (measurable_gaussianPDFReal _ _).comp (measurable_fst.sub
    ((measurable_freshEigenvalue ℓ).comp ((continuous_const.add continuous_id).measurable.comp
      measurable_snd)))

theorem measurable_freshProjector_add (F : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => freshProjector (F + A0) ℓ :=
  (measurable_freshProjector ℓ).comp (continuous_const.add continuous_id).measurable

theorem measurable_freshEigenvector_add (F : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => freshEigenvector (F + A0) ℓ := by
  refine measurable_pi_iff.2 fun x => ?_
  exact (BlockBand.Model.Construction.measurable_rawOrderedColumnSelection _ x).comp
    (continuous_const.add continuous_id).measurable

/-!
## Continuity and Hermitian symmetry of the canonical version
-/

/-- Each entry of `Σ_F` is continuous in `e` (dominated convergence; `|w P_ij| ≤ N/√(2πc)`). -/
theorem continuous_sigma_apply (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (i j : Fin N) :
    Continuous fun e => sigma F c e i j := by
  simp only [sigma, Matrix.of_apply]
  refine continuous_finsetSum _ fun ℓ _ => ?_
  refine continuous_of_dominated (bound := fun _ => densityBound c N) ?_ ?_ ?_ ?_
  · intro e
    exact ((Complex.continuous_ofReal.measurable.comp (measurable_palmWeight F c e ℓ)).mul
      ((Matrix.measurable_apply (i := i) (j := j)).comp
        (measurable_freshProjector_add F ℓ))).aestronglyMeasurable
  · intro e
    refine Eventually.of_forall fun A0 => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (palmWeight_nonneg F c e ℓ A0)]
    calc palmWeight F c e ℓ A0 * ‖freshProjector (F + A0) ℓ i j‖
        ≤ densityBound c N * 1 :=
          mul_le_mul (palmWeight_le F c e ℓ A0) (norm_freshProjector_apply_le _ ℓ i j)
            (norm_nonneg _) (densityBound_nonneg c N)
      _ = densityBound c N := mul_one _
  · exact integrable_const _
  · refine Eventually.of_forall fun A0 => ?_
    exact (Complex.continuous_ofReal.comp (continuous_palmWeight_E F c ℓ A0)).mul
      continuous_const

theorem continuous_sigma (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    Continuous (sigma F c) :=
  continuous_pi fun i => continuous_pi fun j => continuous_sigma_apply F c i j

theorem sigma_isHermitian (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) :
    (sigma F c e).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, sigma, Matrix.of_apply, star_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [show star (∫ A0, (palmWeight F c e ℓ A0 : ℂ) * freshProjector (F + A0) ℓ j i
      ∂freshTracelessLaw N c) = conj (∫ A0, (palmWeight F c e ℓ A0 : ℂ) *
        freshProjector (F + A0) ℓ j i ∂freshTracelessLaw N c) from rfl, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun A0 => ?_)
  simp only [freshProjector, vecMulVec_apply, Pi.star_apply, map_mul, Complex.conj_ofReal,
    RCLike.star_def, Complex.conj_conj]
  ring

/-!
## Quadratic forms
-/

theorem freshProjector_mulVec (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) (y : Fin N → ℂ) :
    freshProjector K ℓ *ᵥ y = (star (freshEigenvector K ℓ) ⬝ᵥ y) • freshEigenvector K ℓ := by
  ext i
  simp only [freshProjector, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem star_dotProduct_freshProjector_mulVec (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N)
    (y : Fin N → ℂ) :
    star y ⬝ᵥ (freshProjector K ℓ *ᵥ y) =
      ((‖star y ⬝ᵥ freshEigenvector K ℓ‖ ^ 2 : ℝ) : ℂ) := by
  rw [freshProjector_mulVec, dotProduct_smul, smul_eq_mul]
  have h : star (freshEigenvector K ℓ) ⬝ᵥ y = conj (star y ⬝ᵥ freshEigenvector K ℓ) := by
    conv_lhs => rw [← star_star y]
    rw [star_dotProduct_star]
    rfl
  rw [h, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `q* M q` for an entrywise integral `M = ∫ f`, with integrable entries. -/
theorem star_dotProduct_of_integral_mulVec {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → Matrix (Fin N) (Fin N) ℂ} (hf : ∀ i j, Integrable (fun ω => f ω i j) μ)
    (y : Fin N → ℂ) :
    star y ⬝ᵥ ((Matrix.of fun i j => ∫ ω, f ω i j ∂μ) *ᵥ y) =
      ∫ ω, star y ⬝ᵥ (f ω *ᵥ y) ∂μ := by
  have hint : ∀ i j, Integrable (fun ω => star y i * (f ω i j * y j)) μ := fun i j =>
    ((hf i j).mul_const (y j)).const_mul (star y i)
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [integral_finsetSum (f := fun i ω => ∑ j, star (y i) * (f ω i j * y j)) _
    fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum (f := fun j ω => star (y i) * (f ω i j * y j)) _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

theorem integrable_palmWeight_mul (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) (ℓ : Fin N)
    {f : Matrix (Fin N) (Fin N) ℂ → ℂ} (hf : Measurable f) {M : ℝ} (hM : ∀ A, ‖f A‖ ≤ M) :
    Integrable (fun A0 => (palmWeight F c e ℓ A0 : ℂ) * f A0) (freshTracelessLaw N c) := by
  refine Integrable.mono' (integrable_const (densityBound c N * M)) ?_
    (Eventually.of_forall fun A0 => ?_)
  · exact ((Complex.continuous_ofReal.measurable.comp (measurable_palmWeight F c e ℓ)).mul
      hf).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (palmWeight_nonneg F c e ℓ A0)]
    exact mul_le_mul (palmWeight_le F c e ℓ A0) (hM A0) (norm_nonneg _)
      (densityBound_nonneg c N)

theorem norm_star_dotProduct_freshEigenvector_le (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N)
    (y : Fin N → ℂ) : ‖star y ⬝ᵥ freshEigenvector K ℓ‖ ≤ ∑ a, ‖y a‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Pi.star_apply, norm_mul, norm_star]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_freshEigenvector_apply_le K ℓ a))

/-- `q* Σ_F(e) q = Σ_ℓ E_{A⁰}[w_{ℓ,e} |q* u_ℓ|²]` (complex form). -/
theorem star_dotProduct_sigma_mulVec (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) (y : Fin N → ℂ) :
    star y ⬝ᵥ (sigma F c e *ᵥ y) = ∑ ℓ : Fin N,
      ((∫ A0, palmWeight F c e ℓ A0 * ‖star y ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2
        ∂freshTracelessLaw N c : ℝ) : ℂ) := by
  have hint : ∀ ℓ (i j : Fin N), Integrable (fun A0 => (palmWeight F c e ℓ A0 : ℂ) *
      freshProjector (F + A0) ℓ i j) (freshTracelessLaw N c) := fun ℓ i j =>
    integrable_palmWeight_mul F c e ℓ ((Matrix.measurable_apply (i := i) (j := j)).comp
      (measurable_freshProjector_add F ℓ)) (fun A => norm_freshProjector_apply_le _ ℓ i j)
  have hsum : sigma F c e = ∑ ℓ : Fin N, Matrix.of fun i j => ∫ A0,
      (palmWeight F c e ℓ A0 : ℂ) * freshProjector (F + A0) ℓ i j ∂freshTracelessLaw N c := by
    ext i j
    simp [sigma, Matrix.sum_apply]
  have hlhs : star y ⬝ᵥ (sigma F c e *ᵥ y) = ∑ ℓ : Fin N, ∫ A0,
      (palmWeight F c e ℓ A0 : ℂ) * (star y ⬝ᵥ (freshProjector (F + A0) ℓ *ᵥ y))
        ∂freshTracelessLaw N c := by
    rw [hsum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [star_dotProduct_of_integral_mulVec (hint ℓ)]
    refine integral_congr_ae (Eventually.of_forall fun A0 => ?_)
    have hM : ((fun i j => (palmWeight F c e ℓ A0 : ℂ) * freshProjector (F + A0) ℓ i j) :
        Matrix (Fin N) (Fin N) ℂ) = (palmWeight F c e ℓ A0 : ℂ) • freshProjector (F + A0) ℓ := by
      ext i j; simp
    simp only [hM, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hlhs]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun A0 => ?_)
  simp only [star_dotProduct_freshProjector_mulVec, Complex.ofReal_mul]

/-- Real form: `q* Σ_F(e) q = Σ_ℓ E_{A⁰}[w_{ℓ,e} |q* u_ℓ|²]`. -/
theorem quadForm_sigma_eq (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) (y : Fin N → ℂ) :
    quadForm (sigma F c e) y = ∑ ℓ : Fin N,
      ∫ A0, palmWeight F c e ℓ A0 * ‖star y ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2
        ∂freshTracelessLaw N c := by
  rw [quadForm, star_dotProduct_sigma_mulVec, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- Extended-real form of `q* Σ_F(e) q`. -/
theorem ofReal_quadForm_sigma (F : Matrix (Fin N) (Fin N) ℂ) (c e : ℝ) (y : Fin N → ℂ) :
    ENNReal.ofReal (quadForm (sigma F c e) y) = ∑ ℓ : Fin N,
      ∫⁻ A0, ENNReal.ofReal (palmWeight F c e ℓ A0 * ‖star y ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2)
        ∂freshTracelessLaw N c := by
  have hmeas : ∀ ℓ, Measurable fun A0 => palmWeight F c e ℓ A0 *
      ‖star y ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2 := fun ℓ =>
    (measurable_palmWeight F c e ℓ).mul
      (((continuous_const.dotProduct continuous_id).norm.pow 2).measurable.comp
        (measurable_freshEigenvector_add F ℓ))
  have hnn : ∀ ℓ A0, 0 ≤ palmWeight F c e ℓ A0 * ‖star y ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2 :=
    fun ℓ A0 => mul_nonneg (palmWeight_nonneg F c e ℓ A0) (sq_nonneg _)
  have hq : quadForm (sigma F c e) y = ∑ ℓ : Fin N,
      ∫ A0, palmWeight F c e ℓ A0 * ‖star y ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2
        ∂freshTracelessLaw N c := by
    rw [quadForm, star_dotProduct_sigma_mulVec, Complex.re_sum]
    simp only [Complex.ofReal_re]
  rw [hq, ENNReal.ofReal_sum_of_nonneg fun ℓ _ => integral_nonneg fun A0 => hnn ℓ A0]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal]
  · refine Integrable.mono' (integrable_const (densityBound c N * (∑ a, ‖y a‖) ^ 2))
      (hmeas ℓ).aestronglyMeasurable (Eventually.of_forall fun A0 => ?_)
    rw [Real.norm_of_nonneg (hnn ℓ A0)]
    refine mul_le_mul (palmWeight_le F c e ℓ A0) ?_ (sq_nonneg _) (densityBound_nonneg c N)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_star_dotProduct_freshEigenvector_le _ ℓ y) 2
  · exact Eventually.of_forall fun A0 => hnn ℓ A0

/-!
## The eigenpair kernel identity (scalar split)
-/

section Kernel

variable (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c)
include hN hF hc

omit hF in
/-- Pushforward of the product `freshTracelessLaw ⊗ N(0, c/N²)` under `(A⁰, ζ) ↦ A⁰ + ζ I` is
`GUE_N(c/N)` (`scalarShiftLaw_fin_eq_gueMeasure`). -/
theorem freshGUE_eq_map_prod :
    freshGUE N c = ((freshTracelessLaw N c).prod
      (gaussianReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c) N))).map
        (fun y => y.1 + (y.2 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hσ : ((BlockBand.Palm.scalarVariance (Real.toNNReal c) N : ℝ≥0) : ℝ) =
      ((Real.toNNReal (c / N) : ℝ≥0) : ℝ) / N := by
    rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc.le,
      Real.coe_toNNReal _ (div_pos hc hNr).le]
    field_simp
  rw [freshGUE, ← scalarShiftLaw_fin_eq_gueMeasure hN _ _ hσ]
  rfl

omit hF in
/-- `∫ de w_{ℓ,e}(A⁰) = 1` for every `A⁰`. -/
theorem lintegral_ofReal_palmWeight (ℓ : Fin N) (A0 : Matrix (Fin N) (Fin N) ℂ) :
    ∫⁻ e, ENNReal.ofReal (palmWeight F c e ℓ A0) = 1 := by
  have hc' : Real.toNNReal c ≠ 0 := (Real.toNNReal_pos.2 hc).ne'
  have h := BlockBand.Palm.lintegral_scalarShift_eq_kernel hc' hN.ne'
    (freshEigenvalue (F + A0) ℓ) (ψ := fun _ => 1) measurable_const
  simp only [one_mul, lintegral_const, measure_univ] at h
  rw [h]
  refine lintegral_congr fun e => ?_
  rw [BlockBand.Palm.scalarWeightENN_eq_ofReal]
  rfl

/-- **Eigenpair kernel identity.** For every measurable `Ψ ≥ 0` of an energy and a vector,
`∫ de Σ_ℓ E_{A⁰}[w_{ℓ,e} Ψ(e, u_ℓ(F + A⁰))] = E_G Σ_ℓ Ψ(λ_ℓ(F+G), u_ℓ(F+G))`,
`G ~ GUE_N(c/N)`. -/
theorem lintegral_sigmaKernel_eq {Ψ : ℝ × (Fin N → ℂ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ e, ∑ ℓ : Fin N, ∫⁻ A0, ENNReal.ofReal (palmWeight F c e ℓ A0) *
        Ψ (e, freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c =
      ∫⁻ G, ∑ ℓ : Fin N, Ψ (freshEigenvalue (F + G) ℓ, freshEigenvector (F + G) ℓ)
        ∂freshGUE N c := by
  have hc' : Real.toNNReal c ≠ 0 := (Real.toNNReal_pos.2 hc).ne'
  set σ := BlockBand.Palm.scalarVariance (Real.toNNReal c) N
  have hadd : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => F + A0 :=
    (continuous_const.add continuous_id).measurable
  have hΦ : ∀ ℓ : Fin N, Measurable fun p : Matrix (Fin N) (Fin N) ℂ × ℝ =>
      Ψ (p.2, freshEigenvector (F + p.1) ℓ) := fun ℓ =>
    hΨ.comp (measurable_snd.prodMk ((measurable_freshEigenvector_add F ℓ).comp measurable_fst))
  have hν : ∀ ℓ : Fin N, Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ =>
      freshEigenvalue (F + A0) ℓ := fun ℓ => (measurable_freshEigenvalue ℓ).comp hadd
  have hg : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ∑ ℓ : Fin N, Ψ (freshEigenvalue (F + G) ℓ, freshEigenvector (F + G) ℓ) :=
    Finset.measurable_sum _ fun ℓ _ => hΨ.comp ((hν ℓ).prodMk (measurable_freshEigenvector_add F ℓ))
  rw [freshGUE_eq_map_prod hN hc, lintegral_map hg measurable_scalarAdd]
  have hcongr : (fun y : Matrix (Fin N) (Fin N) ℂ × ℝ =>
      ∑ ℓ : Fin N, Ψ (freshEigenvalue (F + (y.1 + (y.2 : ℂ) • 1)) ℓ,
        freshEigenvector (F + (y.1 + (y.2 : ℂ) • 1)) ℓ)) =ᵐ[(freshTracelessLaw N c).prod
          (gaussianReal 0 σ)]
      fun y => ∑ ℓ : Fin N, Ψ (freshEigenvalue (F + y.1) ℓ + y.2, freshEigenvector (F + y.1) ℓ) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := freshTracelessLaw N c)
      (ν := gaussianReal 0 σ)).ae (ae_freshTracelessLaw hN c)] with y hy
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← add_assoc, freshEigenvalue_add_smul_one (hF.add hy.1),
      BlockBand.Palm.FreshPalmAssembly.freshEigenvector_add_smul_one (hF.add hy.1)]
  rw [lintegral_congr_ae hcongr, lintegral_finsetSum (f := fun ℓ (y : Matrix (Fin N) (Fin N) ℂ × ℝ) =>
    Ψ (freshEigenvalue (F + y.1) ℓ + y.2, freshEigenvector (F + y.1) ℓ)) _ fun ℓ _ =>
    hΨ.comp ((((hν ℓ).comp measurable_fst).add measurable_snd).prodMk
      ((measurable_freshEigenvector_add F ℓ).comp measurable_fst))]
  have hmeasL : ∀ ℓ : Fin N, Measurable fun e => ∫⁻ A0, ENNReal.ofReal (palmWeight F c e ℓ A0) *
      Ψ (e, freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c := fun ℓ =>
    ((ENNReal.measurable_ofReal.comp (measurable_palmWeight_prod F c ℓ)).mul
      (hΨ.comp (measurable_fst.prodMk ((measurable_freshEigenvector_add F ℓ).comp
        measurable_snd)))).lintegral_prod_right'
  rw [lintegral_finsetSum _ fun ℓ _ => hmeasL ℓ]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [BlockBand.Palm.lintegral_dependentScalarShift_eq_kernel (freshTracelessLaw N c) hc' hN.ne'
    (hν ℓ) (hΦ ℓ)]
  refine lintegral_congr fun e => lintegral_congr fun A0 => ?_
  rw [BlockBand.Palm.scalarWeightENN_eq_ofReal, mul_comm]
  rfl

end Kernel

/-!
## The defining identity `∫_B Σ_F = E 1_B(F + G)`
-/

section Defining

variable (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c)

include hN hc in
/-- `(e, A⁰) ↦ w_{ℓ,e}(A⁰) f(A⁰)` is integrable on `Lebesgue ⊗ freshTracelessLaw` for bounded
measurable `f` (`|f| ≤ 1`). -/
theorem integrable_palmWeight_prod (ℓ : Fin N) {f : Matrix (Fin N) (Fin N) ℂ → ℂ}
    (hf : Measurable f) (hf1 : ∀ A, ‖f A‖ ≤ 1) :
    Integrable (fun p : ℝ × Matrix (Fin N) (Fin N) ℂ => (palmWeight F c p.1 ℓ p.2 : ℂ) * f p.2)
      ((volume : Measure ℝ).prod (freshTracelessLaw N c)) := by
  have hw : Measurable fun p : ℝ × Matrix (Fin N) (Fin N) ℂ => palmWeight F c p.1 ℓ p.2 :=
    measurable_palmWeight_prod F c ℓ
  have hwint : Integrable (fun p : ℝ × Matrix (Fin N) (Fin N) ℂ => palmWeight F c p.1 ℓ p.2)
      ((volume : Measure ℝ).prod (freshTracelessLaw N c)) := by
    refine ⟨hw.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => palmWeight_nonneg F c _ ℓ _),
      lintegral_prod_symm (fun p : ℝ × Matrix (Fin N) (Fin N) ℂ =>
        ENNReal.ofReal (palmWeight F c p.1 ℓ p.2)) (ENNReal.measurable_ofReal.comp hw).aemeasurable]
    simp_rw [lintegral_ofReal_palmWeight hN hc ℓ]
    simp
  refine hwint.mono' ((Complex.continuous_ofReal.measurable.comp hw).mul
    (hf.comp measurable_snd)).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (palmWeight_nonneg F c _ ℓ _)]
  exact mul_le_of_le_one_right (palmWeight_nonneg F c _ ℓ _) (hf1 _)

include hN hc in
theorem integrable_sigma_apply (i j : Fin N) : Integrable fun e => sigma F c e i j := by
  simp only [sigma, Matrix.of_apply]
  exact integrable_finsetSum _ fun ℓ _ => (integrable_palmWeight_prod hN hc ℓ
    ((Matrix.measurable_apply (i := i) (j := j)).comp (measurable_freshProjector_add F ℓ))
    (fun A => norm_freshProjector_apply_le _ ℓ i j)).integral_prod_left

include hN hc in
/-- `∫_B w_{ℓ,e}(A⁰) de = P(λ_ℓ(F + A⁰) + ζ ∈ B)`, `ζ ~ N(0, c/N²)`. -/
theorem setIntegral_palmWeight (ℓ : Fin N) {B : Set ℝ} (hB : MeasurableSet B)
    (A0 : Matrix (Fin N) (Fin N) ℂ) :
    ∫ e in B, palmWeight F c e ℓ A0 = ∫ g, B.indicator (1 : ℝ → ℝ) (freshEigenvalue (F + A0) ℓ + g)
      ∂gaussianReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c) N) := by
  have hc' : Real.toNNReal c ≠ 0 := (Real.toNNReal_pos.2 hc).ne'
  set ν := freshEigenvalue (F + A0) ℓ
  have hind : Measurable fun E : ℝ => ENNReal.ofReal (B.indicator (1 : ℝ → ℝ) E) :=
    ENNReal.measurable_ofReal.comp (measurable_const.indicator hB)
  have h := BlockBand.Palm.lintegral_scalarShift_eq_kernel hc' hN.ne' ν hind
  have hnn1 : ∀ x, 0 ≤ B.indicator (1 : ℝ → ℝ) x := fun x =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hpw : Measurable fun e => palmWeight F c e ℓ A0 :=
    (continuous_palmWeight_E F c ℓ A0).measurable
  have e1 : ∫ e in B, palmWeight F c e ℓ A0 = (∫⁻ e in B, ENNReal.ofReal (palmWeight F c e ℓ A0)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun e => palmWeight_nonneg F c e ℓ A0)
      hpw.aestronglyMeasurable
  have e2 : ∫ g, B.indicator (1 : ℝ → ℝ) (ν + g)
      ∂gaussianReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c) N) =
      (∫⁻ g, ENNReal.ofReal (B.indicator (1 : ℝ → ℝ) (ν + g))
        ∂gaussianReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c) N)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun g => hnn1 _)
      ((measurable_const.indicator hB).comp (measurable_const.add measurable_id)).aestronglyMeasurable
  rw [e1, e2, h]
  congr 1
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun e => ?_
  have hw : palmWeight F c e ℓ A0 = BlockBand.Palm.scalarWeight (Real.toNNReal c) N e ν := rfl
  rw [BlockBand.Palm.scalarWeightENN_eq_ofReal, ← hw]
  by_cases he : e ∈ B
  · rw [Set.indicator_of_mem he, Set.indicator_of_mem he, Pi.one_apply, ENNReal.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he, ENNReal.ofReal_zero, zero_mul]

include hN hF hc in
/-- **Defining identity.** For every Borel `B` and all entries,
`∫_B Σ_F(e)_ij de = E[1_B(F + G)]_ij`, `G ~ GUE_N(c/N)` (`N ≥ 1`, Hermitian `F`, `c > 0`). -/
theorem setIntegral_sigma_apply {B : Set ℝ} (hB : MeasurableSet B) (i j : Fin N) :
    ∫ e in B, sigma F c e i j = expectedSpectralProjector N c F B i j := by
  set σ := BlockBand.Palm.scalarVariance (Real.toNNReal c) N
  set μ0 := freshTracelessLaw N c
  set P : Fin N → Matrix (Fin N) (Fin N) ℂ → ℂ := fun ℓ A0 => freshProjector (F + A0) ℓ i j
    with hPdef
  have hP : ∀ ℓ, Measurable (P ℓ) := fun ℓ =>
    (Matrix.measurable_apply (i := i) (j := j)).comp (measurable_freshProjector_add F ℓ)
  have hP1 : ∀ ℓ A, ‖P ℓ A‖ ≤ 1 := fun ℓ A => norm_freshProjector_apply_le _ ℓ i j
  have hint := fun ℓ => integrable_palmWeight_prod (F := F) hN hc ℓ (hP ℓ) (hP1 ℓ)
  have hadd : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ => F + A0 :=
    (continuous_const.add continuous_id).measurable
  set χ : Fin N → Matrix (Fin N) (Fin N) ℂ × ℝ → ℂ := fun ℓ y =>
    ((B.indicator (1 : ℝ → ℝ) (freshEigenvalue (F + y.1) ℓ + y.2) : ℝ) : ℂ) * P ℓ y.1 with hχdef
  have hχm : ∀ ℓ, Measurable (χ ℓ) := fun ℓ =>
    (Complex.continuous_ofReal.measurable.comp ((measurable_const.indicator hB).comp
      ((((measurable_freshEigenvalue ℓ).comp hadd).comp measurable_fst).add measurable_snd))).mul
      ((hP ℓ).comp measurable_fst)
  have hind1 : ∀ x : ℝ, ‖((B.indicator (1 : ℝ → ℝ) x : ℝ) : ℂ)‖ ≤ 1 := fun x => by
    rw [Complex.norm_real]
    by_cases hx : x ∈ B
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hχint : ∀ ℓ, Integrable (χ ℓ) (μ0.prod (gaussianReal 0 σ)) := fun ℓ =>
    (integrable_const (1 : ℝ)).mono' (hχm ℓ).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [hχdef, norm_mul]
        exact (mul_le_mul (hind1 _) (hP1 ℓ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have step1 : ∀ ℓ, ∫ e in B, ∫ A0, (palmWeight F c e ℓ A0 : ℂ) * P ℓ A0 ∂μ0 =
      ∫ y, χ ℓ y ∂(μ0.prod (gaussianReal 0 σ)) := by
    intro ℓ
    have hres : (volume.restrict B).prod μ0 = ((volume : Measure ℝ).prod μ0).restrict
        (B ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hint' : Integrable (Function.uncurry fun e A0 => (palmWeight F c e ℓ A0 : ℂ) * P ℓ A0)
        ((volume.restrict B).prod μ0) := by
      rw [hres]; exact (hint ℓ).restrict
    rw [integral_integral_swap hint', integral_prod _ (hχint ℓ)]
    refine integral_congr_ae (Eventually.of_forall fun A0 => ?_)
    simp only [hχdef]
    rw [integral_mul_const, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      setIntegral_palmWeight hN hc ℓ hB A0]
  have hlhs : ∫ e in B, sigma F c e i j = ∑ ℓ : Fin N, ∫ e in B, ∫ A0,
      (palmWeight F c e ℓ A0 : ℂ) * P ℓ A0 ∂μ0 := by
    simp only [sigma, Matrix.of_apply]
    exact integral_finsetSum _ fun ℓ _ => (hint ℓ).integral_prod_left.integrableOn
  set g : Matrix (Fin N) (Fin N) ℂ → ℂ := fun G => ∑ ℓ : Fin N,
    ((B.indicator (1 : ℝ → ℝ) (freshEigenvalue (F + G) ℓ) : ℝ) : ℂ) * freshProjector (F + G) ℓ i j
    with hgdef
  have hg : Measurable g := Finset.measurable_sum _ fun ℓ _ =>
    (Complex.continuous_ofReal.measurable.comp ((measurable_const.indicator hB).comp
      ((measurable_freshEigenvalue ℓ).comp hadd))).mul (hP ℓ)
  have hcongr : (fun y : Matrix (Fin N) (Fin N) ℂ × ℝ => ∑ ℓ : Fin N, χ ℓ y) =ᵐ[μ0.prod
      (gaussianReal 0 σ)] fun y => g (y.1 + (y.2 : ℂ) • 1) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ0)
      (ν := gaussianReal 0 σ)).ae (ae_freshTracelessLaw hN c)] with y hy
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [hχdef, hPdef]
    rw [← add_assoc, freshEigenvalue_add_smul_one (hF.add hy.1)]
    congr 1
    simp only [freshProjector]
    rw [BlockBand.Palm.FreshPalmAssembly.freshEigenvector_add_smul_one (hF.add hy.1)]
  rw [hlhs, Finset.sum_congr rfl fun ℓ _ => step1 ℓ,
    ← integral_finsetSum _ fun ℓ _ => hχint ℓ, integral_congr_ae hcongr,
    ← integral_map measurable_scalarAdd.aemeasurable hg.aestronglyMeasurable,
    ← freshGUE_eq_map_prod hN hc]
  simp only [expectedSpectralProjector, Matrix.of_apply]
  have ht : 0 < Real.toNNReal (c / N) := Real.toNNReal_pos.2 (div_pos hc (by exact_mod_cast hN))
  refine integral_congr_ae ?_
  filter_upwards [ae_simpleSpectrum_add_gue hF ht] with G hG
  rw [hG.cfc_eq_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]

include hN hF hc in
/-- The canonical version is a matrix spectral density of `F + G`. -/
theorem isMatrixSpectralDensity_sigma : IsMatrixSpectralDensity N c F (sigma F c) :=
  fun _ _ _ i j => setIntegral_sigma_apply hN hF hc measurableSet_Icc i j

/-- A continuous complex function with vanishing integrals over all compact intervals vanishes. -/
theorem eq_zero_of_setIntegral_Icc_eq_zero {f : ℝ → ℂ} (hf : Continuous f)
    (h : ∀ a b : ℝ, a ≤ b → ∫ x in Set.Icc a b, f x = 0) (x : ℝ) : f x = 0 := by
  have hΦ : (fun u => ∫ y in (0 : ℝ)..u, f y) = fun _ => 0 := by
    funext u
    rcases le_total 0 u with hu | hu
    · rw [intervalIntegral.integral_of_le hu, ← integral_Icc_eq_integral_Ioc, h 0 u hu]
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hu,
        ← integral_Icc_eq_integral_Ioc, h u 0 hu, neg_zero]
  have hd := (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
  rw [hΦ] at hd
  exact hd.unique (hasDerivAt_const x 0)

include hN hF hc in
/-- **Uniqueness.** Every continuous matrix spectral density of `F + G` equals `Σ_F`. -/
theorem eq_sigma_of_isMatrixSpectralDensity {S : ℝ → Matrix (Fin N) (Fin N) ℂ}
    (hS : Continuous S) (h : IsMatrixSpectralDensity N c F S) : S = sigma F c := by
  funext e
  ext i j
  have hSij : Continuous fun e => S e i j :=
    (continuous_apply j).comp ((continuous_apply i).comp hS)
  have hfc : Continuous fun e => S e i j - sigma F c e i j :=
    hSij.sub (continuous_sigma_apply F c i j)
  refine sub_eq_zero.1 (eq_zero_of_setIntegral_Icc_eq_zero hfc (fun a b hab => ?_) e)
  rw [integral_sub (f := fun x => S x i j) (g := fun x => sigma F c x i j) hSij.integrableOn_Icc
    (continuous_sigma_apply F c i j).integrableOn_Icc,
    h a b hab i j, isMatrixSpectralDensity_sigma hN hF hc a b hab i j, sub_self]

end Defining

end BlockBand.Critical.WeightedDensity
