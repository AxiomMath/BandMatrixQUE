module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEUnitaryTransport
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# The Jacobian-one bridge for fixed unitary GUE transport

This module supplies the measure-theoretic step deliberately left open by
`GUEUnitaryTransport`: after rescaling strict-upper coordinates by `√2`,
unitary conjugation becomes an ordinary Euclidean isometry.  Consequently its
real determinant has absolute value one, it preserves coordinate Lebesgue
volume, and the exact canonical coordinate and Hermitian pushforward GUE laws
are invariant under every fixed unitary conjugation.

The statements use the repository's canonical finite-product coordinate law;
they do not introduce the absent public `BlockBand.GUE` interface.  Arbitrary
unit-vector completion is a separate downstream step.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- The diagonal rescaling which converts the coordinate expression for the
Hilbert–Schmidt form into the standard sum of squares. -/
def gueCoordinateScaleFactor (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) : ℝ :=
  match (hermitianCoordinateEquivFin N).symm k with
  | .inl _ => 1
  | .inr _ => Real.sqrt 2

private theorem gueCoordinateScaleFactor_ne_zero (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    gueCoordinateScaleFactor N k ≠ 0 := by
  unfold gueCoordinateScaleFactor
  split <;> simp

/-- Coordinatewise multiplication by `1` on diagonal coordinates and `√2` on
strict-upper real and imaginary coordinates. -/
def gueCoordinateScale (N : ℕ) :
    HermitianCoordinateSpace N ≃ₗ[ℝ] HermitianCoordinateSpace N where
  toFun x k := gueCoordinateScaleFactor N k * x k
  invFun x k := (gueCoordinateScaleFactor N k)⁻¹ * x k
  left_inv x := by
    funext k
    field_simp [gueCoordinateScaleFactor_ne_zero N k]
  right_inv x := by
    funext k
    field_simp [gueCoordinateScaleFactor_ne_zero N k]
  map_add' x y := by
    funext k
    exact mul_add _ _ _
  map_smul' c x := by
    funext k
    simp [mul_left_comm]

@[simp] theorem gueCoordinateScale_apply (N : ℕ)
    (x : HermitianCoordinateSpace N)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    gueCoordinateScale N x k = gueCoordinateScaleFactor N k * x k := rfl

/-- The scaled Euclidean coordinate square is exactly the
Hilbert–Schmidt square of the reconstructed Hermitian matrix. -/
theorem sum_sq_gueCoordinateScale {N : ℕ}
    (x : HermitianCoordinateSpace N) :
    (∑ k, (gueCoordinateScale N x k) ^ 2) =
      hilbertSchmidtNormSq (hermitianGUEBlock N x).1 := by
  change (∑ k, (gueCoordinateScale N x k) ^ 2) =
    hilbertSchmidtNormSq (hermitianMatrixOfCoordinates
      (x ∘ hermitianCoordinateEquivFin N))
  rw [hilbertSchmidtNormSq_hermitianMatrixOfCoordinates]
  rw [← (hermitianCoordinateEquivFin N).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [gueCoordinateScale_apply, gueCoordinateScaleFactor,
    Equiv.symm_apply_apply, Function.comp_apply]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp_rw [mul_pow, hsqrt, one_pow, one_mul]
  rw [Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]

/-- The weighted coordinate chart as an equivalence with the standard
Euclidean space. -/
def gueCoordinateEuclideanLinearEquiv (N : ℕ) :
    HermitianCoordinateSpace N ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N))) :=
  (gueCoordinateScale N).trans (WithLp.linearEquiv 2 ℝ _).symm

/-- After the diagonal rescaling, the coordinate action of unitary conjugation
is an ordinary linear equivalence of Euclidean space. -/
def euclideanUnitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N))) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N))) :=
  ((gueCoordinateEuclideanLinearEquiv N).symm.trans
    (unitaryGUECoordinateLinearEquiv U hU)).trans
      (gueCoordinateEuclideanLinearEquiv N)

/-- The rescaled coordinate action preserves the standard Euclidean norm. -/
theorem norm_euclideanUnitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (x : EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N)))) :
    ‖euclideanUnitaryGUECoordinateLinearEquiv U hU x‖ = ‖x‖ := by
  have hsquares :
      ‖euclideanUnitaryGUECoordinateLinearEquiv U hU x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change (∑ k, (gueCoordinateScale N
      (unitaryGUECoordinateLinearEquiv U hU
        ((gueCoordinateScale N).symm x.ofLp)) k) ^ 2) = ∑ k, x.ofLp k ^ 2
    rw [sum_sq_gueCoordinateScale,
      hermitianGUEBlock_unitaryGUECoordinateLinearEquiv U hU,
      hilbertSchmidtNormSq_conjugateHermitian U hU]
    rw [← sum_sq_gueCoordinateScale ((gueCoordinateScale N).symm x.ofLp)]
    apply Finset.sum_congr rfl
    intro k _
    rw [LinearEquiv.apply_symm_apply]
  nlinarith [norm_nonneg x, norm_nonneg (euclideanUnitaryGUECoordinateLinearEquiv U hU x)]

/-- The rescaled coordinate change as a Euclidean linear isometric
equivalence. -/
def euclideanUnitaryGUECoordinateLinearIsometryEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N))) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N))) :=
  { euclideanUnitaryGUECoordinateLinearEquiv U hU with
    norm_map' := norm_euclideanUnitaryGUECoordinateLinearEquiv U hU }

/-- Fixed unitary conjugation has real Jacobian of absolute value one in the
canonical GUE coordinates. -/
theorem abs_det_unitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    |LinearMap.det (unitaryGUECoordinateLinearEquiv U hU :
      HermitianCoordinateSpace N →ₗ[ℝ] HermitianCoordinateSpace N)| = 1 := by
  let C := unitaryGUECoordinateLinearEquiv U hU
  let S := gueCoordinateEuclideanLinearEquiv N
  have hconj :
      LinearMap.det ((euclideanUnitaryGUECoordinateLinearEquiv U hU :
        EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N))) ≃ₗ[ℝ]
          EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N)))) :
            EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N))) →ₗ[ℝ]
              EuclideanSpace ℝ (Fin (Fintype.card (HermitianCoordinate N)))) =
        LinearMap.det (C : HermitianCoordinateSpace N →ₗ[ℝ]
          HermitianCoordinateSpace N) := by
    simpa [euclideanUnitaryGUECoordinateLinearEquiv, C, S]
      using LinearMap.det_conj (C : HermitianCoordinateSpace N →ₗ[ℝ]
        HermitianCoordinateSpace N) S
  rw [← hconj]
  rw [← LinearMap.normDet_eq_abs_det]
  exact LinearIsometry.normDet_eq_one
    (euclideanUnitaryGUECoordinateLinearIsometryEquiv U hU).toLinearIsometry

/-- The coordinate action of fixed unitary conjugation preserves the canonical
Lebesgue volume exactly. -/
theorem map_unitaryGUECoordinateLinearEquiv_volume {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    Measure.map (unitaryGUECoordinateLinearEquiv U hU)
      (volume : Measure (HermitianCoordinateSpace N)) = volume := by
  have habs := abs_det_unitaryGUECoordinateLinearEquiv U hU
  have hdet : LinearMap.det (unitaryGUECoordinateLinearEquiv U hU :
      HermitianCoordinateSpace N →ₗ[ℝ] HermitianCoordinateSpace N) ≠ 0 := by
    intro hz
    simp [hz] at habs
  change Measure.map (unitaryGUECoordinateLinearEquiv U hU :
    HermitianCoordinateSpace N →ₗ[ℝ] HermitianCoordinateSpace N) volume = volume
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet]
  rw [abs_inv, habs]
  simp

/-- Change of variables for an invariant density under the fixed unitary
coordinate action.  This local lemma makes explicit that the law-level result
uses only Jacobian one and the already proved pointwise density identity. -/
private theorem map_withDensity_unitaryGUECoordinateLinearEquiv {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (t : ℝ) :
    Measure.map (unitaryGUECoordinateLinearEquiv U hU)
        ((volume : Measure (HermitianCoordinateSpace N)).withDensity
          (fun x => hermitianGUEDensity N t (hermitianGUEBlock N x))) =
      volume.withDensity
        (fun x => hermitianGUEDensity N t (hermitianGUEBlock N x)) := by
  let C := unitaryGUECoordinateLinearEquiv U hU
  let ρ := fun x : HermitianCoordinateSpace N =>
    hermitianGUEDensity N t (hermitianGUEBlock N x)
  have hC : Measurable C := measurable_unitaryGUECoordinateLinearEquiv U hU
  have hρ : Measurable ρ :=
    PSSSNative.BlockBand.measurable_hermitianGUEDensity_comp_block N t
  have hρC : ∀ x, ρ (C x) = ρ x := fun x =>
    hermitianGUEDensity_unitaryGUECoordinateLinearEquiv U hU t x
  have hvol : Measure.map C (volume : Measure (HermitianCoordinateSpace N)) = volume :=
    map_unitaryGUECoordinateLinearEquiv_volume U hU
  ext s hs
  rw [Measure.map_apply hC hs, withDensity_apply _ (hC hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hC hs) ρ, ← lintegral_indicator hs ρ]
  have hpoint : ((C ⁻¹' s).indicator ρ) = fun x => s.indicator ρ (C x) := by
    funext x
    by_cases hx : C x ∈ s
    · simp [Set.indicator, hx, hρC]
    · simp [Set.indicator, hx]
  rw [hpoint, ← lintegral_map (hρ.indicator hs) hC, hvol]

/-- At zero variance the canonical coordinate product is the point mass at
zero. -/
theorem hermitianGUECoordinateMeasure_zero (N : ℕ) :
    hermitianGUECoordinateMeasure N 0 le_rfl =
      Measure.dirac (0 : HermitianCoordinateSpace N) := by
  unfold hermitianGUECoordinateMeasure
  have hvar : (fun k => gaussianReal 0
      (hermitianGUEFinCoordinateVariance N 0 le_rfl k)) =
      (fun _ => Measure.dirac (0 : ℝ)) := by
    funext k
    unfold hermitianGUEFinCoordinateVariance
    split
    · change gaussianReal 0 (0 : NNReal) = Measure.dirac 0
      exact gaussianReal_zero_var 0
    · rw [show (⟨0 / 2, by positivity⟩ : NNReal) = 0 by ext; norm_num]
      exact gaussianReal_zero_var 0
  rw [hvar]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.dirac_apply' _ (MeasurableSet.pi Set.countable_univ (fun i _ => hs i))]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  by_cases h : ∀ i, (0 : ℝ) ∈ s i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hz : (0 : HermitianCoordinateSpace N) ∉ Set.univ.pi s := by
      intro hz
      exact hi (hz i (Set.mem_univ i))
    simp [Set.indicator, hz, Finset.prod_eq_zero (Finset.mem_univ i), hi]

/-- For positive variance, the finite-product Hermitian GUE coordinate
law is invariant under every fixed unitary coordinate change. -/
theorem map_unitaryGUECoordinateLinearEquiv_hermitianGUECoordinateMeasure_pos
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    {t : ℝ} (ht : 0 < t) :
    Measure.map (unitaryGUECoordinateLinearEquiv U hU)
        (hermitianGUECoordinateMeasure N t ht.le) =
      hermitianGUECoordinateMeasure N t ht.le := by
  rw [PSSSNative.BlockBand.hermitianGUECoordinateMeasure_eq_withDensity N ht]
  exact map_withDensity_unitaryGUECoordinateLinearEquiv U hU t

/-- The finite-product Hermitian GUE coordinate law, including its
degenerate zero-variance endpoint, is invariant under every fixed unitary
coordinate change. -/
theorem map_unitaryGUECoordinateLinearEquiv_hermitianGUECoordinateMeasure
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Measure.map (unitaryGUECoordinateLinearEquiv U hU)
        (hermitianGUECoordinateMeasure N t ht) =
      hermitianGUECoordinateMeasure N t ht := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [hermitianGUECoordinateMeasure_zero,
      Measure.map_dirac' (measurable_unitaryGUECoordinateLinearEquiv U hU)]
    simp
  · exact
      map_unitaryGUECoordinateLinearEquiv_hermitianGUECoordinateMeasure_pos U hU ht

/-- Exact fixed-unitary invariance of the canonical Hermitian GUE pushforward
law for every nonnegative variance, including its point-mass endpoint. -/
theorem map_conjugate_canonicalHermitianGUEPushforward_invariant {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    Measure.map (conjugateHermitian U)
        (canonicalHermitianGUEPushforward N t ht) =
      canonicalHermitianGUEPushforward N t ht := by
  rw [map_conjugate_canonicalHermitianGUEPushforward U hU t ht,
    map_unitaryGUECoordinateLinearEquiv_hermitianGUECoordinateMeasure U hU t ht]
  rfl

end PSSSNative.BlockBand.PSSS
