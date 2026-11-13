module

public import BlockBand.DeterminantScore.Sector.Clauses
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# First derivative of the complete sector mass

The complete sector mass `Z_ℓ(K) = E[1{N_-(K + G_m(t)) = ℓ} det(K + G_m(t))²]` is differentiated
along a Hermitian parameter family by dominated differentiation of the translated sector cut:
`mass_hasFDerivAt` gives `∂Z_ℓ = 2 E[1{N_-=ℓ} P² Tr(R ∂K)]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory ProbabilityTheory MvPolynomial Filter Metric Matrix
open scoped NNReal Topology

variable {m : ℕ}

theorem norm_realEvalFDeriv_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ ℂ) (z : σ → ℝ) :
    ‖realEvalFDeriv P z‖ ≤ ∑ c, ‖realEval (pderiv c P) z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun c _ => norm_nonneg _) fun w => ?_
  rw [realEvalFDeriv_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w c) (norm_nonneg _)

theorem realEvalFDeriv_detSqPoly_eq_zero (K : Matrix (Fin m) (Fin m) ℂ) {z : HermCoord m → ℝ}
    (hz : (K + hermOfCoord z).det = 0) : realEvalFDeriv (detSqPoly K) z = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [realEvalFDeriv_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp [detSqPoly, pow_two, realEval_detPoly, hz]

/-- The derivative of `1{N_-(G(z))=ℓ} det(G(z))²`. -/
def cutFDeriv (ℓ : ℕ) (z : HermCoord m → ℝ) : (HermCoord m → ℝ) →L[ℝ] ℂ :=
  if InSector (0 : Matrix (Fin m) (Fin m) ℂ) ℓ z then realEvalFDeriv (detSqPoly 0) z else 0

/-- The sector-cut determinant square is Fréchet differentiable everywhere. -/
theorem hasFDerivAt_cut_zero (ℓ : ℕ) (z : HermCoord m → ℝ) :
    HasFDerivAt (cut 0 ℓ (detSqPoly 0)) (cutFDeriv ℓ z) z := by
  have h0 : (0 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := isHermitian_zero
  by_cases hdet : ((0 : Matrix (Fin m) (Fin m) ℂ) + hermOfCoord z).det = 0
  · have hD := realEvalFDeriv_detSqPoly_eq_zero 0 hdet
    have hval : realEval (detSqPoly 0) z = 0 := vanishesOnDet_detSqPoly 0 z hdet
    have hF := hasFDerivAt_realEval (detSqPoly (0 : Matrix (Fin m) (Fin m) ℂ)) z
    rw [hD] at hF
    have h := hasFDerivAt_ite_zero_of_hasFDerivAt_zero (InSector 0 ℓ)
      (realEval (detSqPoly 0)) hF hval
    have hc : cutFDeriv ℓ z = 0 := by simp [cutFDeriv, hD]
    rw [hc]
    exact h
  · have hev := eventually_cut_eq h0 ℓ (detSqPoly 0) hdet
    by_cases hx : InSector (0 : Matrix (Fin m) (Fin m) ℂ) ℓ z
    · simp only [hx, ↓reduceIte] at hev
      simp only [cutFDeriv, hx, ↓reduceIte]
      exact (hasFDerivAt_realEval _ z).congr_of_eventuallyEq hev
    · simp only [hx, ↓reduceIte] at hev
      simp only [cutFDeriv, hx, ↓reduceIte]
      exact (hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq hev

/-- The sector mass as a function of the coordinates of `K`. -/
def massCoord (m : ℕ) (t : ℝ≥0) (ℓ : ℕ) (y : HermCoord m → ℝ) : ℂ :=
  ∫ x, cut 0 ℓ (detSqPoly 0) (y + x) ∂hermGaussian m t

theorem hermOfCoord_coord_add {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (x : HermCoord m → ℝ) :
    (0 : Matrix (Fin m) (Fin m) ℂ) + hermOfCoord (coordOfMatrix K + x) = K + hermOfCoord x := by
  rw [hermOfCoord_add, hermOfCoord_coordOfMatrix hK, zero_add]

theorem cut_zero_coord_add {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ)
    (x : HermCoord m → ℝ) :
    cut 0 ℓ (detSqPoly 0) (coordOfMatrix K + x) = sectorDetSq K ℓ x := by
  simp only [cut, sectorDetSq, InSector, realEval_detSqPoly, hermOfCoord_coord_add hK]
  congr 1

theorem sectorMass_eq_massCoord (t : ℝ≥0) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (ℓ : ℕ) : sectorMass m t K ℓ = massCoord m t ℓ (coordOfMatrix K) := by
  unfold sectorMass massCoord
  simp only [cut_zero_coord_add hK]

/-- Majorant of the derivative on the unit ball around `y0`. -/
def massBound (R : ℝ) (x : HermCoord m → ℝ) : ℝ :=
  ∑ c, polyMajorant R (pderiv c (detSqPoly (0 : Matrix (Fin m) (Fin m) ℂ))) x

theorem norm_cutFDeriv_le (ℓ : ℕ) {R : ℝ} {y x : HermCoord m → ℝ} (hy : ‖y‖ ≤ R) :
    ‖cutFDeriv ℓ (y + x)‖ ≤ massBound (m := m) R x := by
  have h1 : ‖cutFDeriv ℓ (y + x)‖ ≤ ‖realEvalFDeriv (detSqPoly 0) (y + x)‖ := by
    unfold cutFDeriv
    split_ifs <;> simp
  refine h1.trans ((norm_realEvalFDeriv_le _ _).trans (Finset.sum_le_sum fun c _ => ?_))
  refine norm_realEval_le_polyMajorant _ fun i => ?_
  simp only [Pi.add_apply, add_sub_cancel_right]
  exact (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i : |y i| ≤ ‖y‖).trans hy

theorem integrable_massBound (t : ℝ≥0) (R : ℝ) :
    Integrable (massBound (m := m) R) (hermGaussian m t) := by
  unfold massBound
  exact integrable_finsetSum _ fun c _ => integrable_polyMajorant _ R _

theorem aestronglyMeasurable_cutFDeriv (t : ℝ≥0) (ℓ : ℕ) (y0 : HermCoord m → ℝ) :
    AEStronglyMeasurable (fun x => cutFDeriv ℓ (y0 + x)) (hermGaussian m t) := by
  have h0 : (0 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := isHermitian_zero
  have hS : MeasurableSet {x : HermCoord m → ℝ | InSector 0 ℓ (y0 + x)} :=
    (measurableSet_inSector h0 ℓ).preimage (measurable_const_add y0)
  have hc : Continuous fun x : HermCoord m → ℝ => realEvalFDeriv (detSqPoly 0) (y0 + x) :=
    (continuous_realEvalFDeriv _).comp (continuous_const.add continuous_id)
  exact (StronglyMeasurable.ite hS hc.stronglyMeasurable stronglyMeasurable_const).aestronglyMeasurable

theorem integrable_cutFDeriv (t : ℝ≥0) (ℓ : ℕ) (y0 : HermCoord m → ℝ) :
    Integrable (fun x => cutFDeriv ℓ (y0 + x)) (hermGaussian m t) :=
  (integrable_massBound t ‖y0‖).mono' (aestronglyMeasurable_cutFDeriv t ℓ y0)
    (ae_of_all _ fun _ => norm_cutFDeriv_le ℓ le_rfl)

/-- Dominated differentiation of the sector mass in the coordinates of `K`. -/
theorem hasFDerivAt_massCoord (t : ℝ≥0) (ℓ : ℕ) (y0 : HermCoord m → ℝ) :
    HasFDerivAt (massCoord m t ℓ) (∫ x, cutFDeriv ℓ (y0 + x) ∂hermGaussian m t) y0 := by
  have h0 : (0 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := isHermitian_zero
  have hcont := continuous_cut h0 ℓ (detSqPoly 0) (vanishesOnDet_detSqPoly 0)
  have hball : ∀ y ∈ ball y0 1, ‖y‖ ≤ ‖y0‖ + 1 := fun y hy => by
    rw [mem_ball_iff_norm] at hy
    have := norm_add_le (y - y0) y0
    rw [sub_add_cancel] at this
    linarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y x => cut 0 ℓ (detSqPoly 0) (y + x)) (F' := fun y x => cutFDeriv ℓ (y + x))
    (bound := massBound (‖y0‖ + 1)) (ball_mem_nhds y0 one_pos) ?_ ?_
    (aestronglyMeasurable_cutFDeriv t ℓ y0) ?_ (integrable_massBound t _) ?_
  · exact Eventually.of_forall fun _ =>
      (hcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · refine (integrable_polyMajorant (hermVariance m t) ‖y0‖ (detSqPoly 0)).mono'
      (hcont.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have h1 : ‖cut 0 ℓ (detSqPoly 0) (y0 + x)‖ ≤ ‖realEval (detSqPoly 0) (y0 + x)‖ := by
      unfold cut
      split_ifs <;> simp
    refine h1.trans (norm_realEval_le_polyMajorant _ fun i => ?_)
    simp only [Pi.add_apply, add_sub_cancel_right]
    simpa [Real.norm_eq_abs] using norm_le_pi_norm y0 i
  · exact ae_of_all _ fun x y hy => norm_cutFDeriv_le ℓ (hball y hy)
  · refine ae_of_all _ fun x y _ => ?_
    exact ((hasFDerivAt_cut_zero ℓ (y + x)).comp y ((hasFDerivAt_id y).add_const x)).congr_fderiv
      (ContinuousLinearMap.comp_id _)

/-!
## The parameter family
-/

/-- Jacobi's formula for the determinant square in a coordinate direction:
`D(P²)(z)[w] = 2 P² Tr(G(z)⁻¹ G(w))` (both sides vanish on `{P = 0}`). -/
theorem realEvalFDeriv_detSqPoly_apply (z w : HermCoord m → ℝ) :
    realEvalFDeriv (detSqPoly (0 : Matrix (Fin m) (Fin m) ℂ)) z w =
      2 * (hermOfCoord z).det ^ 2 * ((hermOfCoord z)⁻¹ * hermOfCoord w).trace := by
  set A := hermOfCoord z
  set H := hermOfCoord w
  have hl : HasDerivAt (fun r : ℝ => z + r • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  have h1 := (hasFDerivAt_realEval (detSqPoly (0 : Matrix (Fin m) (Fin m) ℂ)) z).comp_hasDerivAt_of_eq
    (0 : ℝ) hl (by simp)
  have hfun : (realEval (detSqPoly (0 : Matrix (Fin m) (Fin m) ℂ)) ∘ fun r : ℝ => z + r • w) =
      fun r : ℝ => (A + (r : ℂ) • H).det ^ 2 := by
    funext r
    simp only [Function.comp_apply, realEval_detSqPoly, zero_add, hermOfCoord_add,
      hermOfCoord_smul, A, H]
  rw [hfun] at h1
  have h2 : HasDerivAt (fun r : ℝ => (A + (r : ℂ) • H).det ^ 2)
      (2 * A.det ^ 2 * (A⁻¹ * H).trace) 0 := by
    by_cases hA : A.det = 0
    · have hd := (BlockBand.DeterminantScore.hasDerivAt_det_realAffineLine_general A H).pow 2
      convert hd using 1
      simp [hA]
    · have hd := (BlockBand.DeterminantScore.hasDerivAt_det_realAffineLine A H
        (isUnit_iff_ne_zero.2 hA)).pow 2
      convert hd using 1
      simp only [Complex.ofReal_zero, zero_smul, add_zero, Nat.cast_ofNat]
      ring
  exact h1.unique h2

/-- The derivative of the coordinate map along an entrywise differentiable family. -/
def coordFDerivComp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E → Matrix (Fin m) (Fin m) ℂ) (θ : E) (c : HermCoord m) : E →L[ℝ] ℝ :=
  if c.1 = c.2 then Complex.reCLM.comp (fderiv ℝ (fun θ' => K θ' c.1 c.1) θ)
  else if c.1 < c.2 then Complex.reCLM.comp (fderiv ℝ (fun θ' => K θ' c.1 c.2) θ)
  else Complex.imCLM.comp (fderiv ℝ (fun θ' => K θ' c.2 c.1) θ)

theorem hasFDerivAt_coordOfMatrix_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E → Matrix (Fin m) (Fin m) ℂ) (θ : E)
    (hK' : ∀ a b, DifferentiableAt ℝ (fun θ' => K θ' a b) θ) :
    HasFDerivAt (fun θ' => coordOfMatrix (K θ'))
      (ContinuousLinearMap.pi (coordFDerivComp K θ)) θ := by
  refine hasFDerivAt_pi.2 fun c => ?_
  unfold coordOfMatrix coordFDerivComp
  by_cases h1 : c.1 = c.2
  · simp only [h1, ↓reduceIte]
    exact Complex.reCLM.hasFDerivAt.comp θ (hK' _ _).hasFDerivAt
  · by_cases h2 : c.1 < c.2
    · simp only [h1, h2, ↓reduceIte]
      exact Complex.reCLM.hasFDerivAt.comp θ (hK' _ _).hasFDerivAt
    · simp only [h1, h2, ↓reduceIte]
      exact Complex.imCLM.hasFDerivAt.comp θ (hK' _ _).hasFDerivAt

theorem coordFDeriv_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E → Matrix (Fin m) (Fin m) ℂ) (θ h : E) :
    ContinuousLinearMap.pi (coordFDerivComp K θ) h = coordOfMatrix (paramDeriv K θ h) := by
  funext c
  simp only [ContinuousLinearMap.pi_apply, coordFDerivComp, coordOfMatrix, paramDeriv,
    Matrix.of_apply]
  split_ifs <;> rfl

/-- `∂K` is Hermitian when `K` is Hermitian near the base point. -/
theorem isHermitian_paramDeriv_of_eventually {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : E → Matrix (Fin m) (Fin m) ℂ) (θ h : E)
    (hKH : ∀ᶠ θ' in 𝓝 θ, (K θ').IsHermitian)
    (hK' : ∀ a b, DifferentiableAt ℝ (fun θ' => K θ' a b) θ) :
    (paramDeriv K θ h).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, paramDeriv, Matrix.of_apply]
  have hfun : (fun θ' => K θ' a b) =ᶠ[𝓝 θ] fun θ' => Complex.conjCLE (K θ' b a) := by
    filter_upwards [hKH] with θ' hθ'
    rw [Complex.conjCLE_apply]
    exact (hθ'.apply a b).symm
  have hd : fderiv ℝ (fun θ' => K θ' a b) θ =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (fun θ' => K θ' b a) θ) := by
    rw [hfun.fderiv_eq]
    exact (Complex.conjCLE.hasFDerivAt.comp θ (hK' b a).hasFDerivAt).fderiv
  rw [hd]
  simp

theorem isHermitian_paramDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E → Matrix (Fin m) (Fin m) ℂ) (θ h : E) (hKH : ∀ θ', (K θ').IsHermitian)
    (hK' : ∀ a b, DifferentiableAt ℝ (fun θ' => K θ' a b) θ) :
    (paramDeriv K θ h).IsHermitian :=
  isHermitian_paramDeriv_of_eventually K θ h (Eventually.of_forall hKH) hK'

/-- `mass_hasFDerivAt` under the weaker hypothesis that `K` is
Hermitian only near the base point `θ`.
-/
theorem mass_hasFDerivAt_of_eventually (t : ℝ≥0) (ℓ : ℕ) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : E → Matrix (Fin m) (Fin m) ℂ) (θ : E)
    (hKH : ∀ᶠ θ' in 𝓝 θ, (K θ').IsHermitian)
    (hK' : ∀ a b, DifferentiableAt ℝ (fun θ' => K θ' a b) θ) :
    ∃ L : E →L[ℝ] ℂ, HasFDerivAt (fun θ' => sectorMass m t (K θ') ℓ) L θ ∧
      ∀ h : E, L h = 2 * ∫ x, (if InSector (K θ) ℓ x then
          (K θ + hermOfCoord x).det ^ 2 *
            ((K θ + hermOfCoord x)⁻¹ * paramDeriv K θ h).trace
        else 0) ∂hermGaussian m t := by
  have hKθ : (K θ).IsHermitian := hKH.self_of_nhds
  set y0 := coordOfMatrix (K θ)
  have hcomp := (hasFDerivAt_massCoord t ℓ y0).comp θ (hasFDerivAt_coordOfMatrix_comp K θ hK')
  have hfun : (fun θ' => sectorMass m t (K θ') ℓ) =ᶠ[𝓝 θ]
      massCoord m t ℓ ∘ fun θ' => coordOfMatrix (K θ') := by
    filter_upwards [hKH] with θ' hθ'
    exact sectorMass_eq_massCoord t hθ' ℓ
  refine ⟨_, hcomp.congr_of_eventuallyEq hfun, fun h => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.integral_apply
    (integrable_cutFDeriv t ℓ y0), coordFDeriv_apply, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hM := hermOfCoord_coord_add hKθ x
  rw [zero_add] at hM
  have hS : InSector (0 : Matrix (Fin m) (Fin m) ℂ) ℓ (y0 + x) ↔ InSector (K θ) ℓ x := by
    simp only [InSector, zero_add, y0, hM]
  have hW := hermOfCoord_coordOfMatrix (isHermitian_paramDeriv_of_eventually K θ h hKH hK')
  simp only [cutFDeriv]
  by_cases hx : InSector (K θ) ℓ x
  · simp only [hS.2 hx, hx, ↓reduceIte]
    rw [realEvalFDeriv_detSqPoly_apply, hM, hW]
    ring
  · simp only [mt hS.1 hx, hx, ↓reduceIte]
    simp

/-- **The mass derivative** (the `mass_hasFDerivAt` clause of `SectorIBPStatement`):
`∂Z_ℓ = 2 E[1{N_-=ℓ} P² Tr(R ∂K)]`. -/
theorem mass_hasFDerivAt (t : ℝ≥0) (ℓ : ℕ) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : E → Matrix (Fin m) (Fin m) ℂ) (θ : E)
    (hKH : ∀ θ', (K θ').IsHermitian) (hK' : ∀ a b, DifferentiableAt ℝ (fun θ' => K θ' a b) θ) :
    ∃ L : E →L[ℝ] ℂ, HasFDerivAt (fun θ' => sectorMass m t (K θ') ℓ) L θ ∧
      ∀ h : E, L h = 2 * ∫ x, (if InSector (K θ) ℓ x then
          (K θ + hermOfCoord x).det ^ 2 *
            ((K θ + hermOfCoord x)⁻¹ * paramDeriv K θ h).trace
        else 0) ∂hermGaussian m t :=
  mass_hasFDerivAt_of_eventually t ℓ K θ (Eventually.of_forall hKH) hK'

end BlockBand.DeterminantScore.Sector
