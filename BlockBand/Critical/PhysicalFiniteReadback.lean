module

public import BlockBand.Critical.EigenpairReadback
public import BlockBand.Model.Construction.GaussianSimpleSpectrum

/-!
# Physical finite Gaussian eigenpair readback

Under the Gaussian ring law and at a fixed real energy `E`, the base determinant
`det(H - E)` is almost surely nonzero and the spectrum is almost surely simple.  Hence,
almost surely, at every eigenvalue the normalized entire determinant has a nonzero energy
partial and its source ratios are the quadratic masses of the normalized eigenvector.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory
open scoped Matrix

/-- Every scalar real diagonal is in the nondegenerate active sparse range. -/
theorem gaussianActiveReconstruction_scalarDiagonal (p : BlockBand.Parameters) (r : ℝ) :
    p.gaussianActiveReconstruction
      (p.gaussianActiveExtraction (Matrix.diagonal fun _ : p.Site => (r : ℂ))) =
      Matrix.diagonal (fun _ : p.Site => (r : ℂ)) := by
  classical
  let H : p.SiteMatrix := Matrix.diagonal fun _ => (r : ℂ)
  have hcoord : p.gaussianActiveValue (p.gaussianActiveExtraction H) =
      p.gaussianExtraction H := by
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
          · simp [gaussianExtraction, H, Matrix.diagonal_apply_ne _ hxy]
  rw [gaussianActiveReconstruction, hcoord]
  apply p.gaussianReconstruction_gaussianExtraction
  change (Matrix.diagonal (fun _ : p.Site => (r : ℂ))).IsHermitian
  rw [Matrix.isHermitian_diagonal_iff]
  intro x
  simp [IsSelfAdjoint]

/-- The base determinant is nonzero almost surely for each fixed real energy under
the Gaussian ring law.  The polynomial witness is `(E+1) I` on the active
coordinates; absolute continuity on all Hermitian matrices is not needed. -/
theorem GaussianRingModel.ae_baseDeterminant_ne_zero
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (E : ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0 := by
  classical
  let U := p.gaussianUniversalMatrix -
    (MvPolynomial.C (E : ℂ) : MvPolynomial p.GaussianActiveCoordinate ℂ) • (1 : Matrix p.Site p.Site
      (MvPolynomial p.GaussianActiveCoordinate ℂ))
  have heval (z : p.GaussianActiveCoordinate → ℝ) :
      MvPolynomial.eval (fun i => (z i : ℂ)) U.det =
        (p.gaussianActiveReconstruction z - (E : ℂ) • (1 : p.SiteMatrix)).det := by
    rw [RingHom.map_det]
    congr 1
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [U, Matrix.map_apply, ← p.gaussianUniversalMatrix_map_eval z,
        Matrix.smul_apply, smul_eq_mul]
    · simp [U, Matrix.map_apply, ← p.gaussianUniversalMatrix_map_eval z,
        Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hxy]
  let z₀ := p.gaussianActiveExtraction
    (Matrix.diagonal fun _ : p.Site => ((E + 1 : ℝ) : ℂ))
  have hw : MvPolynomial.eval (fun i => (z₀ i : ℂ)) U.det ≠ 0 := by
    rw [heval, p.gaussianActiveReconstruction_scalarDiagonal]
    have hid : Matrix.diagonal (fun _ : p.Site => ((E + 1 : ℝ) : ℂ)) -
        (E : ℂ) • (1 : p.SiteMatrix) = 1 := by
      ext x y
      by_cases hxy : x = y
      · subst y
        simp
      · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]
    rw [hid, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [model.ae_activePolynomial_ne_zero U.det z₀ hw,
    model.ae_gaussianActiveReconstruction_eq] with H hpoly hrec
  rw [heval, hrec] at hpoly
  exact hpoly

/-- Physical readback at all eigenvalues, at a fixed deterministic energy `E`, almost
surely under `model.law`.  The sources are arbitrary finite matrices with `Q 0 = I`,
and the width is `W = p.W`; the identity is exact at every finite size. -/
theorem GaussianRingModel.ae_all_eigenpair_source_readback
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (E : ℝ) {m : ℕ}
    (Q : Fin (m + 1) → p.SiteMatrix) (hQ : Q 0 = 1) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ∃ hH : H.IsHermitian,
      ∃ hA : (H - (E : ℂ) • (1 : p.SiteMatrix)).det ≠ 0,
      ∀ k : p.Site,
        let A := H - (E : ℂ) • (1 : p.SiteMatrix)
        let z := -(p.W : ℂ)^2 * ((hH.eigenvalues k : ℂ)-(E : ℂ))
        BlockBand.Critical.finiteSourcePartial A Q p.W hA z 0 ≠ 0 ∧
          ∀ a : Fin (m + 1),
            BlockBand.Critical.finiteSourcePartial A Q p.W hA z a /
              BlockBand.Critical.finiteSourcePartial A Q p.W hA z 0 =
                dotProduct (star ⇑(hH.eigenvectorBasis k))
                  ((Q a) *ᵥ ⇑(hH.eigenvectorBasis k)) := by
  filter_upwards [model.isPhysical.1, model.ae_baseDeterminant_ne_zero E,
    model.ae_charpoly_separable] with H hH hA hsep
  refine ⟨hH, hA, ?_⟩
  have hinj : Function.Injective (fun k => (hH.eigenvalues k : ℂ)) := by
    rw [hH.charpoly_eq] at hsep
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep
  intro k
  apply BlockBand.Critical.hermitian_eigenpair_source_readback H hH k
  · intro j hj heq
    exact hj (hinj (congrArg (fun r : ℝ => (r : ℂ)) heq))
  · exact Nat.ne_of_gt p.W_pos
  · exact hQ

end BlockBand.Parameters
