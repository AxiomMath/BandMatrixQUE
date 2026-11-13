module

public import BlockBand.DeterminantScore.Sector.Cut

/-!
# The clauses of the sector integration-by-parts statement

The weak-derivative, integrability and integration-by-parts clauses of `SectorIBPStatement` for the
sector-cut functions `det(M)² 1{sector}` and `det(M)² (M⁻¹)_ab 1{sector}`, obtained by writing
them as cuts of the polynomials `P²` and `P C_ab` (`P = det`, `C = adj`) that vanish on `{P = 0}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory ProbabilityTheory MvPolynomial
open scoped NNReal
open BlockBand.Internal.Contracts

variable {m : ℕ}

/-- `P²` as a polynomial in the coordinates. -/
def detSqPoly (K : Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (HermCoord m) ℂ := detPoly K ^ 2

/-- `P · C_ab` as a polynomial in the coordinates. -/
def detAdjPoly (K : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) : MvPolynomial (HermCoord m) ℂ :=
  detPoly K * adjPoly K a b

theorem realEval_detSqPoly (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ) :
    realEval (detSqPoly K) x = (K + hermOfCoord x).det ^ 2 := by
  simp [detSqPoly, realEval_detPoly]

theorem realEval_detAdjPoly (K : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m)
    (x : HermCoord m → ℝ) :
    realEval (detAdjPoly K a b) x = (K + hermOfCoord x).det * (K + hermOfCoord x).adjugate a b := by
  simp [detAdjPoly, realEval_detPoly, realEval_adjPoly]

theorem vanishesOnDet_detSqPoly (K : Matrix (Fin m) (Fin m) ℂ) :
    VanishesOnDet K (detSqPoly K) := fun x hx => by
  rw [realEval_detSqPoly, hx]; ring

theorem vanishesOnDet_detAdjPoly (K : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    VanishesOnDet K (detAdjPoly K a b) := fun x hx => by
  rw [realEval_detAdjPoly, hx, zero_mul]

theorem coordDeriv_realEval (Q : MvPolynomial (HermCoord m) ℂ) (c : HermCoord m)
    (x : HermCoord m → ℝ) :
    coordDeriv (realEval Q) c x = realEval (pderiv c Q) x := by
  unfold coordDeriv
  have h := (hasDerivAt_realEval_update Q x c (x c)).deriv
  rw [Function.update_eq_self] at h
  exact h

theorem sectorDetSq_eq_cut (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) :
    sectorDetSq K ℓ = cut K ℓ (detSqPoly K) := by
  funext x
  simp [sectorDetSq, cut, realEval_detSqPoly]

theorem sectorDetAdj_eq_cut (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m) :
    sectorDetAdj K ℓ a b = cut K ℓ (detAdjPoly K a b) := by
  funext x
  simp [sectorDetAdj, cut, realEval_detAdjPoly]

theorem sectorDetSqDeriv_eq_cutDeriv (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (c : HermCoord m) :
    sectorDetSqDeriv K ℓ c = cutDeriv K ℓ (detSqPoly K) c := by
  funext x
  have h : (fun y : HermCoord m → ℝ => (K + hermOfCoord y).det ^ 2) =
      realEval (detSqPoly K) := funext fun y => (realEval_detSqPoly K y).symm
  simp only [sectorDetSqDeriv, cutDeriv, h, coordDeriv_realEval]

theorem sectorDetAdjDeriv_eq_cutDeriv (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m)
    (c : HermCoord m) :
    sectorDetAdjDeriv K ℓ a b c = cutDeriv K ℓ (detAdjPoly K a b) c := by
  funext x
  have h : (fun y : HermCoord m → ℝ =>
      (K + hermOfCoord y).det * (K + hermOfCoord y).adjugate a b) =
      realEval (detAdjPoly K a b) := funext fun y => (realEval_detAdjPoly K a b y).symm
  simp only [sectorDetAdjDeriv, cutDeriv, h, coordDeriv_realEval]

/-- Pole removal: `P² R_ab = P C_ab` pointwise, including on `{P = 0}`. -/
theorem sectorDetSqInv_eq (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m) :
    sectorDetSqInv K ℓ a b = sectorDetAdj K ℓ a b := by
  funext x
  simp only [sectorDetSqInv, sectorDetAdj]
  split_ifs
  · set A := K + hermOfCoord x
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    by_cases hA : A.det = 0
    · simp [hA]
    · rw [Ring.inverse_eq_inv']
      field_simp
  · rfl

theorem hermGaussian_eq (m : ℕ) (t : ℝ≥0) :
    hermGaussian m t = Measure.pi fun i => gaussianReal 0 (hermVariance m t i) := rfl

variable {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ)
include hK

theorem weak_detSq (c : HermCoord m) :
    Inputs.HasWeakCoordPartial c (sectorDetSq K ℓ) (sectorDetSqDeriv K ℓ c) := by
  rw [sectorDetSq_eq_cut, sectorDetSqDeriv_eq_cutDeriv]
  exact hasWeakCoordPartial_cut hK ℓ _ (vanishesOnDet_detSqPoly K) c

theorem weak_detAdj (a b : Fin m) (c : HermCoord m) :
    Inputs.HasWeakCoordPartial c (sectorDetAdj K ℓ a b) (sectorDetAdjDeriv K ℓ a b c) := by
  rw [sectorDetAdj_eq_cut, sectorDetAdjDeriv_eq_cutDeriv]
  exact hasWeakCoordPartial_cut hK ℓ _ (vanishesOnDet_detAdjPoly K a b) c

theorem ordinary_detSq (c : HermCoord m) (x : HermCoord m → ℝ)
    (hx : (K + hermOfCoord x).det ≠ 0) :
    HasDerivAt (fun s : ℝ => sectorDetSq K ℓ (Function.update x c s))
      (sectorDetSqDeriv K ℓ c x) (x c) := by
  rw [sectorDetSq_eq_cut, sectorDetSqDeriv_eq_cutDeriv]
  have h := hasDerivAt_cut_line hK ℓ (detSqPoly K) x c (x c)
    (by rwa [Function.update_eq_self])
  rwa [Function.update_eq_self] at h

theorem ordinary_detAdj (a b : Fin m) (c : HermCoord m) (x : HermCoord m → ℝ)
    (hx : (K + hermOfCoord x).det ≠ 0) :
    HasDerivAt (fun s : ℝ => sectorDetAdj K ℓ a b (Function.update x c s))
      (sectorDetAdjDeriv K ℓ a b c x) (x c) := by
  rw [sectorDetAdj_eq_cut, sectorDetAdjDeriv_eq_cutDeriv]
  have h := hasDerivAt_cut_line hK ℓ (detAdjPoly K a b) x c (x c)
    (by rwa [Function.update_eq_self])
  rwa [Function.update_eq_self] at h

theorem integrable_detSq (t : ℝ≥0) (c : HermCoord m) :
    Integrable (sectorDetSq K ℓ) (hermGaussian m t) ∧
      Integrable (sectorDetSqDeriv K ℓ c) (hermGaussian m t) ∧
      Integrable (fun x => x c • sectorDetSq K ℓ x) (hermGaussian m t) := by
  rw [sectorDetSq_eq_cut, sectorDetSqDeriv_eq_cutDeriv, hermGaussian_eq]
  exact ⟨integrable_cut hK ℓ _ _, integrable_cutDeriv hK ℓ _ _ c,
    integrable_coord_smul_cut hK ℓ _ _ c⟩

theorem integrable_detAdj (t : ℝ≥0) (a b : Fin m) (c : HermCoord m) :
    Integrable (sectorDetAdj K ℓ a b) (hermGaussian m t) ∧
      Integrable (sectorDetAdjDeriv K ℓ a b c) (hermGaussian m t) ∧
      Integrable (fun x => x c • sectorDetAdj K ℓ a b x) (hermGaussian m t) := by
  rw [sectorDetAdj_eq_cut, sectorDetAdjDeriv_eq_cutDeriv, hermGaussian_eq]
  exact ⟨integrable_cut hK ℓ _ _, integrable_cutDeriv hK ℓ _ _ c,
    integrable_coord_smul_cut hK ℓ _ _ c⟩

theorem ibp_one (t : ℝ≥0) (c : HermCoord m) :
    (∫ x, x c • sectorDetSq K ℓ x ∂hermGaussian m t) =
      (hermVariance m t c : ℝ) • ∫ x, sectorDetSqDeriv K ℓ c x ∂hermGaussian m t := by
  rw [sectorDetSq_eq_cut, sectorDetSqDeriv_eq_cutDeriv, hermGaussian_eq]
  exact gaussian_ibp_cut hK ℓ _ _ (vanishesOnDet_detSqPoly K) c

theorem ibp_inverse (t : ℝ≥0) (a b : Fin m) (c : HermCoord m) :
    (∫ x, x c • sectorDetSqInv K ℓ a b x ∂hermGaussian m t) =
      (hermVariance m t c : ℝ) • ∫ x, sectorDetAdjDeriv K ℓ a b c x ∂hermGaussian m t := by
  rw [sectorDetSqInv_eq, sectorDetAdj_eq_cut, sectorDetAdjDeriv_eq_cutDeriv, hermGaussian_eq]
  exact gaussian_ibp_cut hK ℓ _ _ (vanishesOnDet_detAdjPoly K a b) c

end BlockBand.DeterminantScore.Sector
