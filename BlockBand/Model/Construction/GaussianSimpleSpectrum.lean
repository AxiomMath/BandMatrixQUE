module

public import BlockBand.Model.Construction.GaussianActiveCoordinates
public import BlockBand.Model.Construction.GaussianDiscriminant

/-!
# Almost-sure simple spectrum of the sparse physical Gaussian law

Under every physical Gaussian block-band model, the characteristic polynomial of the matrix is
almost surely separable, so the spectrum is almost surely simple.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal

def gaussianUniversalMatrix (p : BlockBand.Parameters) :
    Matrix p.Site p.Site (MvPolynomial p.GaussianActiveCoordinate ℂ) := fun x y =>
  if x = y then p.gaussianActiveValue MvPolynomial.X (.inl x)
  else if p.siteIndex x < p.siteIndex y then
    p.gaussianActiveValue MvPolynomial.X (.inr (x, y, false)) +
      MvPolynomial.C Complex.I * p.gaussianActiveValue MvPolynomial.X (.inr (x, y, true))
  else
    p.gaussianActiveValue MvPolynomial.X (.inr (y, x, false)) -
      MvPolynomial.C Complex.I * p.gaussianActiveValue MvPolynomial.X (.inr (y, x, true))

theorem eval_gaussianActiveValue_X (p : BlockBand.Parameters)
    (z : p.GaussianActiveCoordinate → ℝ) (i : p.GaussianCoordinate) :
    MvPolynomial.eval (fun j => (z j : ℂ)) (p.gaussianActiveValue MvPolynomial.X i) =
      ((p.gaussianActiveValue z i : ℝ) : ℂ) := by
  unfold gaussianActiveValue
  split_ifs <;> simp

theorem gaussianUniversalMatrix_map_eval (p : BlockBand.Parameters)
    (z : p.GaussianActiveCoordinate → ℝ) :
    (p.gaussianUniversalMatrix.map (MvPolynomial.eval (fun j => (z j : ℂ)))) =
      p.gaussianActiveReconstruction z := by
  classical
  ext x y
  simp only [Matrix.map_apply, gaussianUniversalMatrix, gaussianActiveReconstruction,
    gaussianReconstruction]
  split_ifs <;> simp [eval_gaussianActiveValue_X]

/-- Positive diagonal real variance is retained in the active support. -/
theorem gaussianCoordinateVariance_diagonal_ne_zero (p : BlockBand.Parameters) (x : p.Site) :
    p.gaussianCoordinateVariance (.inl x) ≠ 0 := by
  have hv : 0 < (p.gaussianCoordinateVariance (.inl x) : ℝ) := by
    change 0 < p.entryVariance x x
    simp only [entryVariance, ite_true]
    exact div_pos p.c_pos (by exact_mod_cast p.W_pos)
  intro h
  have hz := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
  exact hv.ne' (by simpa using hz)

def distinctGaussianDiagonal (p : BlockBand.Parameters) : p.SiteMatrix :=
  Matrix.diagonal (fun x => (p.siteIndex x : ℂ))

/-- The distinct-diagonal witness lies in the physical sparse reconstruction
range. Only diagonal active coordinates are used. -/
theorem gaussianActiveReconstruction_distinctDiagonal (p : BlockBand.Parameters) :
    p.gaussianActiveReconstruction (p.gaussianActiveExtraction p.distinctGaussianDiagonal) =
      p.distinctGaussianDiagonal := by
  classical
  have hcoord : p.gaussianActiveValue (p.gaussianActiveExtraction p.distinctGaussianDiagonal) =
      p.gaussianExtraction p.distinctGaussianDiagonal := by
    funext i
    unfold gaussianActiveValue gaussianActiveExtraction
    split_ifs with hi
    · rfl
    · cases i with
      | inl x => exact False.elim (hi (p.gaussianCoordinateVariance_diagonal_ne_zero x))
      | inr xy =>
          rcases xy with ⟨x, y, b⟩
          by_cases hxy : x = y
          · subst y
            simp [gaussianExtraction]
          · simp [gaussianExtraction, distinctGaussianDiagonal, Matrix.diagonal_apply_ne _ hxy]
  rw [gaussianActiveReconstruction, hcoord]
  apply p.gaussianReconstruction_gaussianExtraction
  rw [distinctGaussianDiagonal, Matrix.isHermitian_diagonal_iff]
  intro x
  exact IsSelfAdjoint.natCast _

/-- Evaluation commutes with the characteristic discriminant of any finite
polynomial matrix family. -/
theorem gaussian_discr_map_eval {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (MvPolynomial σ ℂ)) (g : σ → ℂ) :
    (U.map (MvPolynomial.eval g)).discr = MvPolynomial.eval g U.discr := by
  rw [Matrix.discr, Matrix.discr, Matrix.charpoly_map]
  exact Polynomial.discr_map_of_monic _ _ (Matrix.charpoly_monic U)

/-- Almost-sure simplicity of the spectrum for every physical Gaussian law: the
characteristic polynomial is almost surely separable. This is the null exceptional set needed for
measurable ordered eigenline selection; no additional model hypothesis is used. -/
theorem GaussianRingModel.ae_charpoly_separable
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.charpoly.Separable := by
  let z₀ := p.gaussianActiveExtraction p.distinctGaussianDiagonal
  have hsep₀ : ((p.gaussianUniversalMatrix).map
      (MvPolynomial.eval fun i => (z₀ i : ℂ))).charpoly.Separable := by
    rw [p.gaussianUniversalMatrix_map_eval, p.gaussianActiveReconstruction_distinctDiagonal,
      distinctGaussianDiagonal, Matrix.charpoly_diagonal]
    apply Polynomial.separable_prod_X_sub_C_iff.mpr
    intro x y hxy
    exact p.siteIndex_injective (Nat.cast_injective (R := ℂ) hxy)
  have hw : MvPolynomial.eval (fun i => (z₀ i : ℂ)) (p.gaussianUniversalMatrix.discr) ≠ 0 := by
    rw [← gaussian_discr_map_eval, Matrix.discr]
    exact Polynomial.discr_ne_zero_of_monic_separable (Matrix.charpoly_monic _) hsep₀
  filter_upwards [model.ae_activePolynomial_ne_zero p.gaussianUniversalMatrix.discr z₀ hw,
    model.ae_gaussianActiveReconstruction_eq] with H hpoly hrec
  rw [← gaussian_discr_map_eval, p.gaussianUniversalMatrix_map_eval, hrec, Matrix.discr] at hpoly
  by_contra hns
  exact hpoly ((Polynomial.discr_eq_zero_iff_not_separable (Matrix.charpoly_monic _)).mpr hns)

end BlockBand.Parameters
