module
public import BlockBand.Internal.Contracts.Transmission
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Calculus for the Itô formula

* `covOf h = ∑_a h_a h_aᵀ`, the covariance density of a diffusion `(h_a)_a` in `ℝ^d`.
* `itoDrift_covOf`, `itoBracket_covOf`: the coordinate expressions `itoDrift`, `itoBracket` of
  the Itô formula `SemimartingaleItoFormula`, for a covariance `∑_a h_a h_aᵀ`, are the
  coordinate-free `∂_tφ + Dφ[β] + ½ ∑_a D²φ[h_a, h_a]` and `∑_a (Dφ[h_a])²` (derivatives in the
  space direction `(0, v)` of `ℝ × ℝ^d`).
* `fderiv_affineComp`, `fderiv_fderiv_affineComp`, `contDiff_affineComp`: first and second
  derivatives of `p ↦ ℓ (f (L p)) + λ p` for `C²` `f` and continuous linear `L, ℓ, λ`.
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ} {κ : Type*} [Fintype κ]

/-- The covariance matrix `∑_a h_a h_aᵀ` of a finite family of vectors. -/
def covOf (h : κ → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ a, h a i * h a j

theorem pair_zero_eq_sum (v : Fin d → ℝ) :
    ((0 : ℝ), v) = ∑ i, v i • ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin d → ℝ)) := by
  ext k
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

/-- `∑_i v_i ∂_iφ = Dφ[(0, v)]`. -/
theorem sum_mul_partialSpace (φ : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ))
    (v : Fin d → ℝ) : ∑ i, v i * partialSpace φ p i = fderiv ℝ φ p (0, v) := by
  rw [pair_zero_eq_sum v, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- `∑_{ij} v_i w_j ∂_i∂_jφ = D²φ[(0, v), (0, w)]`. -/
theorem sum_mul_partialSpace2 (φ : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ))
    (v w : Fin d → ℝ) :
    ∑ i, ∑ j, v i * w j * partialSpace2 φ p i j =
      fderiv ℝ (fderiv ℝ φ) p (0, v) (0, w) := by
  have h1 : fderiv ℝ (fderiv ℝ φ) p (0, v) =
      ∑ i, v i • fderiv ℝ (fderiv ℝ φ) p (0, Pi.single i 1) := by
    rw [pair_zero_eq_sum v, map_sum]
    simp only [map_smul]
  rw [h1]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [pair_zero_eq_sum w, map_sum]
  simp only [map_smul, smul_eq_mul, Finset.mul_sum, partialSpace2]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Itô drift for a covariance `∑_a h_a h_aᵀ`**, coordinate free. -/
theorem itoDrift_covOf (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0) (b : Fin d → ℝ)
    (h : κ → Fin d → ℝ) :
    itoDrift φ y t b (covOf h) =
      fderiv ℝ φ ((t : ℝ), y) ((1 : ℝ), (0 : Fin d → ℝ)) + fderiv ℝ φ ((t : ℝ), y) ((0 : ℝ), b) +
      (1 / 2 : ℝ) * ∑ a, fderiv ℝ (fderiv ℝ φ) ((t : ℝ), y) ((0 : ℝ), h a) ((0 : ℝ), h a) := by
  unfold itoDrift
  rw [sum_mul_partialSpace]
  congr 2
  simp_rw [← sum_mul_partialSpace2]
  simp only [covOf, Matrix.of_apply, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- **Itô bracket for a covariance `∑_a h_a h_aᵀ`**: `∑_a (Dφ[(0, h_a)])²`. -/
theorem itoBracket_covOf (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0)
    (h : κ → Fin d → ℝ) :
    itoBracket φ y t (covOf h) = ∑ a, (fderiv ℝ φ ((t : ℝ), y) ((0 : ℝ), h a)) ^ 2 := by
  unfold itoBracket
  simp_rw [← sum_mul_partialSpace, sq, Finset.sum_mul, Finset.mul_sum]
  simp only [covOf, Matrix.of_apply, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

section Affine
variable {P P' G G' : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup P'] [NormedSpace ℝ P'] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G']

/-- The map `p ↦ ℓ (f (L p)) + λ p`. -/
def affineComp (ℓ : G →L[ℝ] G') (f : P → G) (L : P' →L[ℝ] P) (lam : P' →L[ℝ] G') (p : P') : G' :=
  ℓ (f (L p)) + lam p

/-- The continuous linear map `M ↦ ℓ ∘ M ∘ L`. -/
def sandwich (ℓ : G →L[ℝ] G') (L : P' →L[ℝ] P) : (P →L[ℝ] G) →L[ℝ] (P' →L[ℝ] G') :=
  (ContinuousLinearMap.compL ℝ P' G G' ℓ).comp ((ContinuousLinearMap.compL ℝ P' P G).flip L)

theorem sandwich_apply (ℓ : G →L[ℝ] G') (L : P' →L[ℝ] P) (M : P →L[ℝ] G) (v : P') :
    sandwich ℓ L M v = ℓ (M (L v)) := rfl

variable {f : P → G} (hf : ContDiff ℝ 2 f) (ℓ : G →L[ℝ] G') (L : P' →L[ℝ] P) (lam : P' →L[ℝ] G')
include hf

theorem hasFDerivAt_affineComp (p : P') :
    HasFDerivAt (affineComp ℓ f L lam) (sandwich ℓ L (fderiv ℝ f (L p)) + lam) p := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h1 : HasFDerivAt (fun q => ℓ (f (L q))) (ℓ.comp ((fderiv ℝ f (L p)).comp L)) p :=
    ℓ.hasFDerivAt.comp p ((hd (L p)).hasFDerivAt.comp p L.hasFDerivAt)
  exact h1.add lam.hasFDerivAt

theorem fderiv_affineComp_eq :
    fderiv ℝ (affineComp ℓ f L lam) = fun p => sandwich ℓ L (fderiv ℝ f (L p)) + lam :=
  funext fun p => (hasFDerivAt_affineComp hf ℓ L lam p).fderiv

/-- First derivative of `ℓ ∘ f ∘ L + λ`. -/
theorem fderiv_affineComp (p v : P') :
    fderiv ℝ (affineComp ℓ f L lam) p v = ℓ (fderiv ℝ f (L p) (L v)) + lam v := by
  rw [fderiv_affineComp_eq hf]
  rfl

/-- Second derivative of `ℓ ∘ f ∘ L + λ`. -/
theorem fderiv_fderiv_affineComp (p v w : P') :
    fderiv ℝ (fderiv ℝ (affineComp ℓ f L lam)) p v w =
      ℓ (fderiv ℝ (fderiv ℝ f) (L p) (L v) (L w)) := by
  rw [fderiv_affineComp_eq hf]
  have hd1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ f) := hd1.differentiable (by norm_num)
  have h : HasFDerivAt (fun q => sandwich ℓ L (fderiv ℝ f (L q)) + lam)
      ((sandwich ℓ L).comp ((fderiv ℝ (fderiv ℝ f) (L p)).comp L)) p := by
    have := (sandwich ℓ L).hasFDerivAt.comp p ((hd (L p)).hasFDerivAt.comp p L.hasFDerivAt)
    simpa using this.add_const lam
  rw [h.fderiv]
  rfl

theorem contDiff_affineComp : ContDiff ℝ 2 (affineComp ℓ f L lam) :=
  (ℓ.contDiff.comp (hf.comp L.contDiff)).add lam.contDiff

end Affine

end BlockBand.SourceProcess.Stochastic.ItoNative
