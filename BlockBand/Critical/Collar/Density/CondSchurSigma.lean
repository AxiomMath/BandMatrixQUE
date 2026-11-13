module

public import BlockBand.Critical.Collar.Density.CondSchurGaussian
public import BlockBand.Critical.Collar.Density.Regular

/-!
# Conditional Schur identity: the canonical density as a Gaussian average

Reindexing lemmas for the matrix functional calculus and quadratic forms, almost-sure simplicity of
the spectrum of `F + A⁰` under the traceless law `freshTracelessLaw N c`, and
`ofReal_quadForm_sigma_eq_lintegral_rawCfc`, which writes the quadratic form of the canonical
density `sigma F c 0` as an integral of a raw functional calculus of `F + A⁰` over that law.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Coarea.FreshPalm
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

/-!
## Reindexing the functional calculus
-/

theorem cfc_submatrix_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (A.submatrix e e) = (cfc f A).submatrix e e := by
  have hA' : (A.submatrix e e).IsHermitian := hA.submatrix e
  refine matrix_eq_of_mulVec_increasingEigenvector_eq ⟨_, hA'⟩ _ _ fun r => ?_
  change cfc f (A.submatrix e e) *ᵥ increasingEigenvector hA' r =
    (cfc f A).submatrix e e *ᵥ increasingEigenvector hA' r
  set b := increasingEigenvector hA' r
  set l := increasingEigenvalue hA' r
  have hb : A.submatrix e e *ᵥ b = (l : ℂ) • b := mulVec_increasingEigenvector hA' r
  have hb' : A *ᵥ (b ∘ e.symm) = (l : ℂ) • (b ∘ e.symm) := by
    have h := congrArg (fun v => v ∘ e.symm) hb
    simp only [submatrix_mulVec_equiv] at h
    funext i
    have := congrFun h i
    simpa [Function.comp] using this
  rw [cfc_mulVec_of_eigen hA' f hb, submatrix_mulVec_equiv, cfc_mulVec_of_eigen hA f hb']
  funext i
  simp [Function.comp]

theorem quadForm_submatrix_equiv {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    (M : Matrix ι ι ℂ) (y : ι → ℂ) : quadForm (M.submatrix e e) (y ∘ e) = quadForm M y := by
  unfold quadForm
  rw [submatrix_mulVec_equiv]
  congr 1
  have h : (y ∘ e) ∘ e.symm = y := by funext i; simp
  rw [h]
  simp only [dotProduct, Pi.star_apply, Function.comp]
  exact Equiv.sum_comp e (fun i => star (y i) * (M *ᵥ y) i)

theorem quadForm_neg_vec' {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (y : ι → ℂ) :
    quadForm M (-y) = quadForm M y := by
  unfold quadForm
  simp [mulVec_neg]

/-!
## Simple spectrum under the traceless law
-/

theorem simpleSpectrum_add_real_smul {N : ℕ} {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) (r : ℝ) : SimpleSpectrum (K + (r : ℂ) • 1) := by
  refine ⟨hK.1.add (isHermitian_one.smul (Complex.conj_ofReal r)), fun ℓ m h => ?_⟩
  rw [freshEigenvalue_add_smul_one hK.1, freshEigenvalue_add_smul_one hK.1] at h
  exact hK.2 (add_right_cancel h)

theorem ae_simpleSpectrum_add_traceless {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) (hN : 0 < N) :
    ∀ᵐ A0 ∂freshTracelessLaw N c, SimpleSpectrum (F + A0) := by
  have ht : 0 < Real.toNNReal (c / N) := Real.toNNReal_pos.2 (div_pos hc (by exact_mod_cast hN))
  have hS : MeasurableSet {A0 : Matrix (Fin N) (Fin N) ℂ | SimpleSpectrum (F + A0)} :=
    measurableSet_simpleSpectrum.preimage
      (continuous_const.add continuous_id).measurable
  unfold freshTracelessLaw
  rw [ae_map_iff BlockBand.Coarea.PoleExclusion.measurable_tracelessPart.aemeasurable hS]
  filter_upwards [ae_simpleSpectrum_add_gue hF ht,
    BlockBand.Coarea.GUELaw.ae_isHermitian_gueMeasure (ι := Fin N) _] with G hG hGh
  set r : ℝ := -((N : ℝ)⁻¹ * ∑ i, (G i i).re)
  have htr : G.trace = ((∑ i, (G i i).re : ℝ) : ℂ) := by
    rw [Matrix.trace, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (hGh.coe_re_apply_self i).symm
  have heq : F + tracelessPart G = (F + G) + (r : ℂ) • 1 := by
    unfold tracelessPart
    rw [htr, Fintype.card_fin]
    simp only [r]
    push_cast
    rw [neg_smul]
    abel
  show SimpleSpectrum (F + tracelessPart G)
  rw [heq]
  exact simpleSpectrum_add_real_smul hG r

theorem quadForm_freshProjector {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N)
    (y : Fin N → ℂ) :
    quadForm (freshProjector K ℓ) y = ‖star y ⬝ᵥ freshEigenvector K ℓ‖ ^ 2 := by
  unfold quadForm freshProjector
  rw [vecMulVec_mulVec, dotProduct_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  have h : star (freshEigenvector K ℓ) ⬝ᵥ y = star (star y ⬝ᵥ freshEigenvector K ℓ) := by
    rw [star_dotProduct]
  rw [h, Complex.star_def, mul_comm, Complex.conj_mul']
  norm_cast

theorem quadForm_sum_smul {ι : Type} [Fintype ι] {κ : Type} (s : Finset κ) (r : κ → ℝ)
    (P : κ → Matrix ι ι ℂ) (y : ι → ℂ) :
    quadForm (∑ k ∈ s, ((r k : ℝ) : ℂ) • P k) y = ∑ k ∈ s, r k * quadForm (P k) y := by
  unfold quadForm
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- `y* Σ_F(0) y = E_{A⁰} y* φ(-(F + A⁰)) y` (`φ` the scalar Gaussian density; a.e. simple
spectrum identifies the eigenvector selection `freshEigenvector` with the functional calculus).
-/
theorem ofReal_quadForm_sigma_eq_lintegral_rawCfc {N : ℕ} (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) (y : Fin N → ℂ) :
    ENNReal.ofReal (quadForm (sigma F c 0) y) = ∫⁻ A0, ENNReal.ofReal (quadForm
      (rawCfc (fun l => gaussianPDFReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c) N) (-l))
        (F + A0)) y) ∂freshTracelessLaw N c := by
  have hmeas : ∀ ℓ, Measurable fun A0 => ENNReal.ofReal (palmWeight F c 0 ℓ A0 *
      ‖star y ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2) := fun ℓ =>
    ENNReal.measurable_ofReal.comp ((measurable_palmWeight F c 0 ℓ).mul
      (((continuous_const.dotProduct continuous_id).norm.pow 2).measurable.comp
        (measurable_freshEigenvector_add F ℓ)))
  rw [ofReal_quadForm_sigma, ← lintegral_finsetSum _ fun ℓ _ => hmeas ℓ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_simpleSpectrum_add_traceless hF hc hN] with A0 hA0
  rw [rawCfc_eq_cfc hA0.1, hA0.cfc_eq_sum, quadForm_sum_smul,
    ENNReal.ofReal_sum_of_nonneg fun ℓ _ => mul_nonneg (gaussianPDFReal_nonneg _ _ _)
      (by rw [quadForm_freshProjector]; exact sq_nonneg _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [quadForm_freshProjector]
  congr 2
  unfold palmWeight BlockBand.Palm.scalarWeight
  rw [zero_sub]

end BlockBand.Critical.Collar.Density
