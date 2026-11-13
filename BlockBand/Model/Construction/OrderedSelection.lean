module

public import BlockBand.Model.Construction.OrderedProjector
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Data.Finset.Max

/-!
# Explicit measurable ordered column selection

The first positive diagonal chart of the phase-free Lagrange projector selects
a normalized column. The finite sum formulation avoids measurable choice.
This module proves Borel measurability of the selection; its unit norm,
eigen-equation and pairwise orthonormality require the separate simple-spectrum
projector correctness argument. No law or simplicity constructor is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open BlockBand.Foundations.Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive diagonal entry identifying a nonzero projector column. -/
def orderedColumnAvailable (i j : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) : Prop :=
  0 < (orderedProjector i A (increasingIndex j) (increasingIndex j)).re

/-- The Borel region where j is the first positive diagonal chart. -/
def orderedColumnRegion (i j : Fin (Fintype.card ι)) : Set (HermitianMatrix ι) :=
  {A | orderedColumnAvailable i j A ∧
    ∀ k : Fin (Fintype.card ι), k < j → ¬ orderedColumnAvailable i k A}

/-- A projector column divided by the square root of its diagonal entry. -/
def orderedNormalizedColumn (i j : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (x : ι) : ℂ :=
  orderedProjector i A x (increasingIndex j) /
    (Real.sqrt (orderedProjector i A (increasingIndex j) (increasingIndex j)).re : ℂ)

/-- Explicit first-chart selection, with zero when no positive chart exists. -/
def orderedColumnSelection (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (x : ι) : ℂ := by
  classical
  exact ∑ j : Fin (Fintype.card ι),
    if A ∈ orderedColumnRegion i j then orderedNormalizedColumn i j A x else 0

/-- Availability of each chart is Borel. -/
theorem measurableSet_orderedColumnAvailable (i j : Fin (Fintype.card ι)) :
    MeasurableSet {A : HermitianMatrix ι | orderedColumnAvailable i j A} := by
  exact measurableSet_lt measurable_const
    (Complex.continuous_re.measurable.comp
      ((measurable_pi_apply (increasingIndex j)).comp
        ((measurable_pi_apply (increasingIndex j)).comp (measurable_orderedProjector i))))

/-- First-chart regions are Borel. -/
theorem measurableSet_orderedColumnRegion (i j : Fin (Fintype.card ι)) :
    MeasurableSet (orderedColumnRegion (ι := ι) i j) := by
  have hm : MeasurableSet {A : HermitianMatrix ι |
      ∀ k : Fin (Fintype.card ι), k < j → ¬ orderedColumnAvailable i k A} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro _
    exact (measurableSet_orderedColumnAvailable i k).compl
  exact (measurableSet_orderedColumnAvailable i j).inter hm

/-- Every normalized-column coordinate is Borel, including inverse-zero defaults. -/
theorem measurable_orderedNormalizedColumn (i j : Fin (Fintype.card ι)) (x : ι) :
    Measurable (fun A : HermitianMatrix ι => orderedNormalizedColumn i j A x) := by
  have hd := Complex.continuous_re.measurable.comp
    ((measurable_pi_apply (increasingIndex j)).comp
      ((measurable_pi_apply (increasingIndex j)).comp (measurable_orderedProjector i)))
  have hn := (measurable_pi_apply (increasingIndex j)).comp
    ((measurable_pi_apply x).comp (measurable_orderedProjector i))
  simpa only [orderedNormalizedColumn] using! hn.div (Complex.continuous_ofReal.measurable.comp
    (Real.continuous_sqrt.measurable.comp hd))

/-- Every coordinate of the explicit finite first-chart selection is Borel. -/
theorem measurable_orderedColumnSelection (i : Fin (Fintype.card ι)) (x : ι) :
    Measurable (fun A : HermitianMatrix ι => orderedColumnSelection i A x) := by
  classical
  apply Finset.measurable_sum
  intro j _
  exact (measurable_orderedNormalizedColumn i j x).piecewise
    (measurableSet_orderedColumnRegion i j) measurable_const

/-- The projector diagonal equals the phase-free site mass on simple spectrum. -/
theorem orderedProjector_diagonal_re (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) (x : ι) :
    (orderedProjector i A x x).re = ‖increasingEigenvector A.property i x‖ ^ 2 := by
  rw [orderedProjector_eq_outerProduct i A hsimple]
  simp only [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- A positive projector chart exists at every simple-spectrum ordered rank. -/
theorem exists_orderedColumnAvailable (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    ∃ j, orderedColumnAvailable i j A := by
  have hx : ∃ x : ι, 0 < ‖increasingEigenvector A.property i x‖ ^ 2 := by
    by_contra h
    push Not at h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun x _ => h x)
    rw [sum_norm_sq_increasingEigenvector] at hh
    norm_num at hh
  obtain ⟨x, hx⟩ := hx
  refine ⟨increasingIndex.symm x, ?_⟩
  unfold orderedColumnAvailable
  rw [Equiv.apply_symm_apply, orderedProjector_diagonal_re i A hsimple]
  exact hx

/-- A first positive diagonal chart exists on the simple-spectrum locus. -/
theorem exists_orderedColumnRegion (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    ∃ j, A ∈ orderedColumnRegion i j := by
  classical
  let charts := Finset.univ.filter (fun j => orderedColumnAvailable i j A)
  have hn : charts.Nonempty := by
    obtain ⟨j, hj⟩ := exists_orderedColumnAvailable i A hsimple
    exact ⟨j, by simp [charts, hj]⟩
  refine ⟨charts.min' hn, ?_⟩
  have hmem := Finset.min'_mem charts hn
  refine ⟨(Finset.mem_filter.mp hmem).2, ?_⟩
  intro k hk hka
  have hkmem : k ∈ charts := by simp [charts, hka]
  exact (not_le_of_gt hk) (Finset.min'_le charts k hkmem)

/-- Two first-chart regions cannot overlap. -/
theorem orderedColumnRegion_unique (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) {j k : Fin (Fintype.card ι)}
    (hj : A ∈ orderedColumnRegion i j) (hk : A ∈ orderedColumnRegion i k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim (hk.2 j h hj.1)
  · exact h
  · exact False.elim (hj.2 k h hk.1)

/-- On a first-chart region the finite sum is exactly that normalized column. -/
theorem orderedColumnSelection_eq_column (i j : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hj : A ∈ orderedColumnRegion i j) (x : ι) :
    orderedColumnSelection i A x = orderedNormalizedColumn i j A x := by
  classical
  unfold orderedColumnSelection
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro k _ hkj
    have hk : A ∉ orderedColumnRegion i k := by
      intro hk
      exact hkj (orderedColumnRegion_unique i A hk hj)
    simp [hk]
  · simp

/-- A normalized projector column is a scalar phase times the current exact
ordered eigenvector on simple spectrum. -/
theorem orderedNormalizedColumn_eq_phase (i j : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) (x : ι) :
    orderedNormalizedColumn i j A x =
      (starRingEnd ℂ (increasingEigenvector A.property i (increasingIndex j)) /
        (‖increasingEigenvector A.property i (increasingIndex j)‖ : ℂ)) *
          increasingEigenvector A.property i x := by
  unfold orderedNormalizedColumn
  rw [orderedProjector_diagonal_re i A hsimple,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    orderedProjector_eq_outerProduct i A hsimple]
  ring

/-- Positive chart normalization produces a unit complex phase. -/
theorem norm_orderedColumnPhase (i j : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A))
    (hj : orderedColumnAvailable i j A) :
    ‖starRingEnd ℂ (increasingEigenvector A.property i (increasingIndex j)) /
      (‖increasingEigenvector A.property i (increasingIndex j)‖ : ℂ)‖ = 1 := by
  have hpos : 0 < ‖increasingEigenvector A.property i (increasingIndex j)‖ := by
    unfold orderedColumnAvailable at hj
    rw [orderedProjector_diagonal_re i A hsimple] at hj
    nlinarith [norm_nonneg (increasingEigenvector A.property i (increasingIndex j))]
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, div_self hpos.ne']

/-- Every selected site mass equals the canonical phase-free ordered mass on
simple spectrum; this bridges measurable selection to current finite algebra. -/
theorem norm_sq_orderedColumnSelection (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) (x : ι) :
    ‖orderedColumnSelection i A x‖ ^ 2 = ‖increasingEigenvector A.property i x‖ ^ 2 := by
  obtain ⟨j, hj⟩ := exists_orderedColumnRegion i A hsimple
  rw [orderedColumnSelection_eq_column i j A hj x,
    orderedNormalizedColumn_eq_phase i j A hsimple]
  exact norm_sq_phase_mul _ (norm_orderedColumnPhase i j A hsimple hj.1) _

/-- The explicit measurable choice is a unit phase times the canonical current
ordered eigenvector; phases may vary independently between ranks. -/
theorem orderedColumnSelection_eq_phase (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      orderedColumnSelection i A = z • increasingEigenvector A.property i := by
  obtain ⟨j, hj⟩ := exists_orderedColumnRegion i A hsimple
  refine ⟨_, norm_orderedColumnPhase i j A hsimple hj.1, ?_⟩
  funext x
  rw [orderedColumnSelection_eq_column i j A hj x,
    orderedNormalizedColumn_eq_phase i j A hsimple]
  rfl

/-- Every explicitly selected vector has unit total site mass on simple spectrum. -/
theorem sum_norm_sq_orderedColumnSelection (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    (∑ x, ‖orderedColumnSelection i A x‖ ^ 2) = 1 := by
  simp_rw [norm_sq_orderedColumnSelection i A hsimple]
  exact sum_norm_sq_increasingEigenvector A.property i

/-- The explicitly selected vector solves the exact raw-H increasing-rank
eigen-equation on simple spectrum. -/
theorem mulVec_orderedColumnSelection (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    A.val.mulVec (orderedColumnSelection i A) =
      (orderedEigenvalue A i : ℂ) • orderedColumnSelection i A := by
  obtain ⟨z, _, hz⟩ := orderedColumnSelection_eq_phase i A hsimple
  rw [hz, Matrix.mulVec_smul, mulVec_increasingEigenvector, smul_smul, smul_smul]
  rw [mul_comm]
  rfl

/-- The entire explicit measurable selection is orthonormal on simple spectrum,
with the exact conjugate-first coordinate convention of SpectralRealization. -/
theorem orderedColumnSelection_orthonormal (i j : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hsimple : Function.Injective (orderedEigenvalue A)) :
    (∑ x, starRingEnd ℂ (orderedColumnSelection i A x) * orderedColumnSelection j A x) =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    obtain ⟨z, hz, he⟩ := orderedColumnSelection_eq_phase i A hsimple
    simp_rw [he, Pi.smul_apply, smul_eq_mul, map_mul]
    have hterm : ∀ x,
        (starRingEnd ℂ z * starRingEnd ℂ (increasingEigenvector A.property i x)) *
          (z * increasingEigenvector A.property i x) =
        (starRingEnd ℂ z * z) *
          (starRingEnd ℂ (increasingEigenvector A.property i x) *
            increasingEigenvector A.property i x) := by intro x; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, increasingEigenvector_orthonormal]
    have hp : starRingEnd ℂ z * z = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
      norm_num
    simp [hp]
  · obtain ⟨z, _, he⟩ := orderedColumnSelection_eq_phase i A hsimple
    obtain ⟨w, _, hf⟩ := orderedColumnSelection_eq_phase j A hsimple
    simp_rw [he, hf, Pi.smul_apply, smul_eq_mul, map_mul]
    have hterm : ∀ x,
        (starRingEnd ℂ z * starRingEnd ℂ (increasingEigenvector A.property i x)) *
          (w * increasingEigenvector A.property j x) =
        (starRingEnd ℂ z * w) *
          (starRingEnd ℂ (increasingEigenvector A.property i x) *
            increasingEigenvector A.property j x) := by intro x; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, increasingEigenvector_orthonormal]
    simp [hij]

end BlockBand.Model.Construction
