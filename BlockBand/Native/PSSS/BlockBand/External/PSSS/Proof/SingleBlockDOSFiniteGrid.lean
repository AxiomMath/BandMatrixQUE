module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SingleBlockDOS
public import BlockBand.Native.PSSS.BlockBand.Coarea.CoareaGoodSet
public import BlockBand.Native.PSSS.BlockBand.Coarea.LagrangeProjectorCorrectness

/-!
# Deformed GUE simplicity and finite-grid occupancy

This module supplies the algebraic-null and measurable finite-grid layer used in the
sharp single-block density-of-states argument.  All statements use the exact public
`GUE_N(1/N)` normalization.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Collision-free ordered eigenvalues form a measurable matrix event. -/
theorem measurableSet_orderedEigenvalue_injective (N : ℕ) :
    MeasurableSet {H : HermitianMatrix (Fin N) |
      Function.Injective (orderedEigenvalue H)} := by
  change MeasurableSet {H : HermitianMatrix (Fin N) |
    ∀ i j, orderedEigenvalue H i = orderedEigenvalue H j → i = j}
  rw [show {H : HermitianMatrix (Fin N) |
      ∀ i j, orderedEigenvalue H i = orderedEigenvalue H j → i = j} =
      ⋂ i, ⋂ j, {H | orderedEigenvalue H i = orderedEigenvalue H j → i = j} by
    ext H
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using
      (isOpen_ne_fun (continuous_orderedEigenvalue i)
        (continuous_orderedEigenvalue j)).measurableSet

/-- Adding fixed Hermitian coordinates preserves the full-volume simple-spectrum
locus. -/
theorem ae_add_mem_hermitianSimpleSpectrumCoordinates
    (N : ℕ) (a : HermitianCoordinateSpace N) :
    ∀ᵐ x ∂(volume : Measure (HermitianCoordinateSpace N)),
      a + x ∈ hermitianSimpleSpectrumCoordinates N := by
  have h := ae_hermitianSimpleSpectrumCoordinates N
  have ht := (eventually_add_right_iff
    (volume : Measure (HermitianCoordinateSpace N)) a).2 h
  simpa only [add_comm] using ht

/-- Every deterministic Hermitian deformation of the positive-variance canonical
GUE has simple ordered spectrum almost surely. -/
theorem ae_canonicalGUE_addHermitian_orderedEigenvalue_injective
    {N : ℕ} (hN : 0 < N) (A : HermitianMatrix (Fin N)) :
    ∀ᵐ V ∂canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
      (canonicalGUEVariance_nonneg N),
      Function.Injective (orderedEigenvalue (addHermitian A V)) := by
  let a : HermitianCoordinateSpace N :=
    (hermitianFinCoordinatesLinearEquiv N).symm A
  have ht : 0 < canonicalGUEVariance N := by
    unfold canonicalGUEVariance
    positivity
  have hac := hermitianGUECoordinateMeasure_absolutelyContinuous N ht
  have hvol := ae_add_mem_hermitianSimpleSpectrumCoordinates N a
  have hcoord : ∀ᵐ x ∂hermitianGUECoordinateMeasure N
      (canonicalGUEVariance N) (canonicalGUEVariance_nonneg N),
      a + x ∈ hermitianSimpleSpectrumCoordinates N := hac.ae_le hvol
  unfold canonicalHermitianGUEPushforward
  apply (ae_map_iff (measurable_hermitianGUEBlock N).aemeasurable
    ((measurableSet_orderedEigenvalue_injective N).preimage
      (measurable_addHermitian A))).2
  filter_upwards [hcoord] with x hx
  have hadd : addHermitian A (hermitianGUEBlock N x) =
      hermitianOfFinCoordinates N (a + x) := by
    apply Subtype.ext
    have ha := congrArg Subtype.val
      ((hermitianFinCoordinatesLinearEquiv N).apply_symm_apply A)
    change A.1 + (hermitianGUEBlock N x).1 = _
    rw [← ha]
    exact congrArg Subtype.val
      ((hermitianFinCoordinatesLinearEquiv N).map_add a x).symm
  rw [hadd]
  exact orderedEigenvalue_injective_of_separable _ hx

/-- Public-law version of deformed almost-sure simplicity at variance `1/N`. -/
theorem ae_publicGUE_addHermitian_orderedEigenvalue_injective
    {N : ℕ} (hN : 0 < N) (A : HermitianMatrix (Fin N)) :
    ∀ᵐ V ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
      Measure (HermitianMatrix (Fin N))),
      Function.Injective (orderedEigenvalue (addHermitian A V)) := by
  have hvar : 0 ≤ (1 / (N : ℝ)) := by positivity
  rw [PSSSNative.BlockBand.GUE_toMeasure_eq_canonicalHermitianGUEPushforward
    N (1 / (N : ℝ)) hvar]
  simpa only [canonicalGUEVariance] using
    ae_canonicalGUE_addHermitian_orderedEigenvalue_injective hN A

/-- A finite grid records whether each half-open cell contains at least one ordered
eigenvalue. -/
def gridCellOccupied {N m : ℕ} (A : HermitianMatrix (Fin N))
    (a w : ℝ) (k : Fin m) : Prop :=
  ∃ i : Fin (Fintype.card (Fin N)),
    orderedEigenvalue A i ∈ Set.Ico (a + k * w) (a + (k + 1) * w)

/-- Number of occupied cells in a finite equal-width grid. -/
def gridOccupiedCount {N : ℕ} (A : HermitianMatrix (Fin N))
    (a w : ℝ) (m : ℕ) : ℕ := by
  classical
  exact ∑ k : Fin m, if gridCellOccupied A a w k then 1 else 0

/-- Cell occupancy is a measurable event under deterministic deformation. -/
theorem measurableSet_gridCellOccupied_addHermitian {N m : ℕ}
    (A : HermitianMatrix (Fin N)) (a w : ℝ) (k : Fin m) :
    MeasurableSet {V | gridCellOccupied (addHermitian A V) a w k} := by
  unfold gridCellOccupied
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_Ico.preimage
    ((measurable_orderedEigenvalue i).comp (measurable_addHermitian A))

/-- The finite occupied-cell count is measurable. -/
theorem measurable_gridOccupiedCount_addHermitian {N : ℕ}
    (A : HermitianMatrix (Fin N)) (a w : ℝ) (m : ℕ) :
    Measurable fun V => gridOccupiedCount (addHermitian A V) a w m := by
  classical
  unfold gridOccupiedCount
  apply Finset.measurable_sum
  intro k _hk
  exact Measurable.ite (measurableSet_gridCellOccupied_addHermitian A a w k)
    measurable_const measurable_const

/-- Every fixed real gridpoint is almost surely outside the spectrum of a
deterministically deformed public GUE block; the stronger determinant statement
is retained for the inverse-gap implication. -/
theorem ae_publicGUE_det_energyShift_add_ne_zero {N : ℕ} (hN : 0 < N)
    (A : HermitianMatrix (Fin N)) (x : ℝ) :
    ∀ᵐ V ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
      Measure (HermitianMatrix (Fin N))),
      (A.1 + V.1 - (x : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ)).det ≠ 0 := by
  have hvar : 0 < (1 / (N : ℝ)) := by positivity
  rw [PSSSNative.BlockBand.GUE_toMeasure_eq_canonicalHermitianGUEPushforward
    N (1 / (N : ℝ)) hvar.le]
  have h := ae_canonicalHermitianGUEPushforward_det_add_ne_zero N hvar
    (energyShiftHermitian A x).1 (energyShiftHermitian A x).2
  filter_upwards [h] with V hV
  simpa [energyShiftHermitian, add_assoc, add_comm, add_left_comm,
    sub_eq_add_neg] using hV

/-- **Sharp finite-cell estimate.**  One absolute inverse-tail constant controls
every occupied equal-width spectral cell.  The mesh condition `Nw ≤ 1` is
exactly the regime in which the inverse-tail theorem accepts
`t = 1/(Nw) ≥ 1`. -/
theorem exists_publicGUE_gridCellOccupied_le :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (N : ℕ), 0 < N → ∀ (A : HermitianMatrix (Fin N))
      (a w : ℝ), 0 < w → (N : ℝ) * w ≤ 1 →
      ∀ (m : ℕ) (k : Fin m),
      (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))
        {V | gridCellOccupied (addHermitian A V) a w k} ≤
      ENNReal.ofReal (K * N * w) := by
  obtain ⟨K, hK, htail⟩ := opNorm_inv_tail
  refine ⟨K, hK, ?_⟩
  intro N hN A a w hw hmesh m k
  let l : ℝ := a + k * w
  let t : ℝ := 1 / ((N : ℝ) * w)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) * w := mul_pos hNreal hw
  have ht : 1 ≤ t := by
    dsimp [t]
    exact (le_div_iff₀ hden).2 (by simpa using hmesh)
  have htail' := htail N hN A l t ht
  have hdet := ae_publicGUE_det_energyShift_add_ne_zero hN A l
  calc
    (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))
        {V | gridCellOccupied (addHermitian A V) a w k} ≤
      (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))
        {V | t * N ≤ ‖(A.1 + V.1 - (l : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖} := by
      apply measure_mono_ae
      filter_upwards [hdet] with V hdetV hocc
      rcases hocc with ⟨i, hi⟩
      have hunit : IsUnit
          ((addHermitian A V).1 - (l : ℂ) •
            (1 : Matrix (Fin N) (Fin N) ℂ)) := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        simpa [addHermitian] using hdetV
      have hzero : eigenCount (addHermitian A V) {l} = 0 :=
        eigenCount_singleton_eq_zero_of_det_energyShift_ne_zero
          (addHermitian A V) l (by simpa [addHermitian] using hdetV)
      have hne : orderedEigenvalue (addHermitian A V) i ≠ l :=
        (eigenCount_singleton_eq_zero_iff (addHermitian A V) l).1 hzero i
      have hg := inv_width_le_l2_opNorm_of_orderedEigenvalue_mem_Ico
        (addHermitian A V) i hw (by simpa [l, add_mul, add_assoc] using hi) hne hunit
      have htN : t * (N : ℝ) = w⁻¹ := by
        dsimp [t]
        field_simp
      rw [htN]
      simpa [addHermitian] using hg
    _ ≤ ENNReal.ofReal (K / t) := htail'
    _ = ENNReal.ofReal (K * N * w) := by
      congr 1
      dsimp [t]
      field_simp

/-- Finite Tonelli assembly of the sharp cell estimate.  The right side is
`K N` times the total grid length `m w`, with no additional dimension factor. -/
theorem exists_publicGUE_lintegral_gridOccupiedCount_le :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (N : ℕ), 0 < N → ∀ (A : HermitianMatrix (Fin N))
      (a w : ℝ), 0 < w → (N : ℝ) * w ≤ 1 → ∀ (m : ℕ),
      (∫⁻ V, (gridOccupiedCount (addHermitian A V) a w m : ℝ≥0∞)
        ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
          Measure (HermitianMatrix (Fin N)))) ≤
      ENNReal.ofReal (K * N * (m * w)) := by
  obtain ⟨K, hK, hcell⟩ := exists_publicGUE_gridCellOccupied_le
  refine ⟨K, hK, ?_⟩
  intro N hN A a w hw hmesh m
  let μ := (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
    Measure (HermitianMatrix (Fin N)))
  have hfun : (fun V =>
      (gridOccupiedCount (addHermitian A V) a w m : ℝ≥0∞)) =
      (fun V => ∑ k : Fin m,
        Set.indicator {V | gridCellOccupied (addHermitian A V) a w k}
          (fun _ => (1 : ℝ≥0∞)) V) := by
    funext V
    simp [gridOccupiedCount, Set.indicator]
  rw [hfun, MeasureTheory.lintegral_finsetSum]
  · calc
      (∑ k : Fin m, ∫⁻ V,
          Set.indicator {V | gridCellOccupied (addHermitian A V) a w k}
            (fun _ => (1 : ℝ≥0∞)) V ∂μ) =
          ∑ k : Fin m, μ {V | gridCellOccupied (addHermitian A V) a w k} := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [lintegral_indicator
              (measurableSet_gridCellOccupied_addHermitian A a w k)]
            simp
      _ ≤ ∑ _k : Fin m, ENNReal.ofReal (K * N * w) := by
        apply Finset.sum_le_sum
        intro k _hk
        exact hcell N hN A a w hw hmesh m k
      _ = ENNReal.ofReal (K * N * (m * w)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
        congr 1
        ring
  · intro k _hk
    exact (measurable_const.indicator
      (measurableSet_gridCellOccupied_addHermitian A a w k))

end PSSSNative.BlockBand.PSSS
