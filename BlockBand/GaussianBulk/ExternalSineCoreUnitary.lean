module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineCoreGUE
public import BlockBand.QUE.Haar.ProjectorTransport
public import BlockBand.Internal.Contracts.Inputs

/-!
# Reduction to a diagonal source

By unitary invariance of `G_N` one may take `F = diag(d_1,…,d_N)`. Law: `deformedGUELaw N t F hF` of
`F + √t G_N` (Johansson coordinate law at `S = t/N`, `Johansson.sourceTime`). Domain: every
`N`, every `t ≥ 0`, every Hermitian `F` (no norm bound, no simple-spectrum hypothesis).

## Main results

All from `gueRawLaw_map_conj`.

* `deformedGUELaw_conj`: for unitary `U` and Hermitian `D`,
  `deformedGUELaw N t (U D U*) = (deformedGUELaw N t D).map (A ↦ U A U*)`;
* `deformedFactorialCorrelation_conj`: hence the factorial correlations of `U D U*` and `D`
  coincide (spectral tuples are conjugation invariant, `QUE.Haar.orderedEigenvalue_unitaryConjugate`);
* `exists_unitary_diagonal_spectralSource`: `F = U diag(d) U*` with `d = spectralSource F`
  the increasing ordered eigenvalues of `F` (with multiplicity), `Monotone d`;
* `deformedFactorialCorrelation_eq_johansson`: the factorial correlations of `F + √t G_N` are
  `Johansson.factorialCorrelationMeasure (t/N) (spectralSource F) k` for every `k`;
* `deformedFactorialCorrelation_eq_kernel_of_strictMono`: for simple spectrum,
  `Johansson.SourceContract` gives the determinantal formula with Johansson's double contour
  kernel at `d = spectralSource F`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Matrix
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- The Johansson Gaussian Hermitian sample law on the Hermitian subtype. -/
def gueHermLaw (N : ℕ) (S : ℝ≥0) : Measure (Johansson.HermitianMatrix N) :=
  (Johansson.coordinateMeasure N S).map Johansson.gaussianMatrix

/-- Measures on the Hermitian subtype are determined by their raw-matrix images. -/
theorem hermitian_measure_ext {N : ℕ} {μ ν : Measure (Johansson.HermitianMatrix N)}
    (h : μ.map Subtype.val = ν.map Subtype.val) : μ = ν := by
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := congrArg (fun m : Measure (Matrix (Fin N) (Fin N) ℂ) => m t) h
  simpa [Measure.map_apply measurable_subtype_coe ht] using this

/-- The raw-matrix image of `gueHermLaw N S` is `gueRawLaw N S`. -/
theorem gueHermLaw_map_val (N : ℕ) (S : ℝ≥0) :
    (gueHermLaw N S).map Subtype.val = gueRawLaw N S := by
  rw [gueHermLaw, Measure.map_map measurable_subtype_coe Johansson.measurable_gaussianMatrix]
  rfl

/-- Unitary conjugation on the Hermitian subtype is measurable. -/
theorem measurable_unitaryConjugate {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (QUE.Haar.unitaryConjugate U : Johansson.HermitianMatrix N → _) := by
  unfold QUE.Haar.unitaryConjugate
  exact ((continuous_conjMatrix U).measurable.comp measurable_subtype_coe).subtype_mk

/-- Unitary invariance of the Hermitian Johansson sample law. -/
theorem gueHermLaw_map_unitaryConjugate (N : ℕ) (S : ℝ≥0)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    (gueHermLaw N S).map (QUE.Haar.unitaryConjugate U) = gueHermLaw N S := by
  apply hermitian_measure_ext
  rw [Measure.map_map measurable_subtype_coe (measurable_unitaryConjugate U),
    show (Subtype.val ∘ QUE.Haar.unitaryConjugate U : Johansson.HermitianMatrix N → _) =
      conjMatrix U ∘ Subtype.val from rfl,
    ← Measure.map_map (continuous_conjMatrix U).measurable measurable_subtype_coe,
    gueHermLaw_map_val, gueRawLaw_map_conj]

/-- Translation by a Hermitian source on the Hermitian subtype. -/
def shiftHerm {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    (A : Johansson.HermitianMatrix N) : Johansson.HermitianMatrix N :=
  ⟨F + A.1, hF.add A.2⟩

/-- Translation by a Hermitian source is measurable on the Hermitian subtype. -/
theorem measurable_shiftHerm {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) :
    Measurable (shiftHerm F hF) :=
  ((continuous_const.add continuous_id).measurable.comp measurable_subtype_coe).subtype_mk

/-- The law `deformedGUELaw N t F` is the image of `gueHermLaw N (t/N)` by `A ↦ F + A`. -/
theorem deformedGUELaw_eq_map_shift (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) :
    deformedGUELaw N t F hF = (gueHermLaw N (Johansson.sourceTime N t)).map (shiftHerm F hF) := by
  rw [gueHermLaw, Measure.map_map (measurable_shiftHerm F hF) Johansson.measurable_gaussianMatrix]
  rfl

/-- Unitary covariance of the deformed GUE law: for every unitary `U` and Hermitian `D`,
`deformedGUELaw N t (U D U*)` is the image of `deformedGUELaw N t D` by `A ↦ U A U*`. -/
theorem deformedGUELaw_conj (N : ℕ) (t : ℝ≥0) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsHermitian) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian)
    (hFD : F = (U : Matrix (Fin N) (Fin N) ℂ) * D * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ) :
    deformedGUELaw N t F hF = (deformedGUELaw N t D hD).map (QUE.Haar.unitaryConjugate U) := by
  rw [deformedGUELaw_eq_map_shift, deformedGUELaw_eq_map_shift,
    Measure.map_map (measurable_unitaryConjugate U) (measurable_shiftHerm D hD)]
  have hcomm : QUE.Haar.unitaryConjugate U ∘ shiftHerm D hD =
      shiftHerm F hF ∘ QUE.Haar.unitaryConjugate U := by
    funext A
    apply Subtype.ext
    change (U : Matrix (Fin N) (Fin N) ℂ) * (D + A.1) * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ =
      F + (U : Matrix (Fin N) (Fin N) ℂ) * A.1 * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ
    rw [hFD, Matrix.mul_add, Matrix.add_mul]
  rw [hcomm, ← Measure.map_map (measurable_shiftHerm F hF) (measurable_unitaryConjugate U),
    gueHermLaw_map_unitaryConjugate]

/-- Spectral tuples are invariant under unitary conjugation. -/
theorem spectralTuple_comp_unitaryConjugate {N k : ℕ} (e : Fin k ↪ Fin N)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Johansson.spectralTuple e ∘ QUE.Haar.unitaryConjugate U = Johansson.spectralTuple e := by
  funext A
  unfold Johansson.spectralTuple
  rw [Function.comp_apply, QUE.Haar.orderedEigenvalue_unitaryConjugate]

/-- The factorial correlations of `U D U* + √t G_N` and `D + √t G_N` coincide. -/
theorem deformedFactorialCorrelation_conj (N : ℕ) (t : ℝ≥0) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsHermitian) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian)
    (hFD : F = (U : Matrix (Fin N) (Fin N) ℂ) * D * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ) (k : ℕ) :
    deformedFactorialCorrelation N t F hF k = deformedFactorialCorrelation N t D hD k := by
  unfold deformedFactorialCorrelation
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [deformedGUELaw_conj N t U D hD F hF hFD,
    Measure.map_map (Johansson.measurable_spectralTuple e) (measurable_unitaryConjugate U),
    spectralTuple_comp_unitaryConjugate]

/-- The increasing ordered eigenvalues of a Hermitian `F`, indexed by `Fin N`. -/
def spectralSource {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) : Fin N → ℝ :=
  fun i => Model.Construction.orderedEigenvalue (⟨F, hF⟩ : Johansson.HermitianMatrix N)
    (Fin.cast (Fintype.card_fin N).symm i)

/-- The increasing eigenvalues `spectralSource F` are monotone (multiplicities kept). -/
theorem spectralSource_monotone {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) :
    Monotone (spectralSource F hF) := by
  intro i j hij
  exact Foundations.Spectral.increasingEigenvalue_monotone hF (by simpa using hij)

/-- Permutation unitary `P_{a j} = [σ a = j]`. -/
def permUnitary {N : ℕ} (σ : Fin N ≃ Fin N) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨Matrix.of fun a j => if σ a = j then (1 : ℂ) else 0, by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    simp [Matrix.mul_apply, Matrix.one_apply, σ.injective.eq_iff]⟩

theorem permUnitary_diagonal {N : ℕ} (σ : Fin N ≃ Fin N) (lam : Fin N → ℂ) :
    (permUnitary σ : Matrix (Fin N) (Fin N) ℂ) * Matrix.diagonal lam *
        (permUnitary σ : Matrix (Fin N) (Fin N) ℂ)ᴴ = Matrix.diagonal (lam ∘ σ) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [permUnitary, Matrix.mul_apply, Matrix.diagonal_apply]
  · simp [permUnitary, Matrix.mul_apply, Matrix.diagonal_apply, σ.injective.eq_iff, h]

/-- Spectral decomposition with increasing ordered eigenvalues:
`F = U diag(spectralSource F) U*` for a unitary `U`. -/
theorem exists_unitary_diagonal_spectralSource {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) :
    ∃ U : Matrix.unitaryGroup (Fin N) ℂ,
      F = (U : Matrix (Fin N) (Fin N) ℂ) *
        Matrix.diagonal (fun i => (spectralSource F hF i : ℂ)) * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
  let σ : Fin N ≃ Fin N :=
    (finCongr (Fintype.card_fin N).symm).trans Foundations.Spectral.increasingIndex
  have hσ : (fun i => (spectralSource F hF i : ℂ)) =
      (RCLike.ofReal ∘ hF.eigenvalues : Fin N → ℂ) ∘ σ := by
    funext i
    simp only [Function.comp_apply, σ, Equiv.trans_apply, finCongr_apply,
      Foundations.Spectral.eigenvalue_increasingIndex]
    rfl
  let P := permUnitary σ
  let U0 := hF.eigenvectorUnitary
  have hD : Matrix.diagonal (RCLike.ofReal ∘ hF.eigenvalues : Fin N → ℂ) =
      (P : Matrix (Fin N) (Fin N) ℂ)ᴴ * Matrix.diagonal (fun i => (spectralSource F hF i : ℂ)) *
        (P : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hσ, ← permUnitary_diagonal]
    have h1 : (P : Matrix (Fin N) (Fin N) ℂ)ᴴ * (P : Matrix (Fin N) (Fin N) ℂ) = 1 :=
      Matrix.UnitaryGroup.star_mul_self P
    calc Matrix.diagonal (RCLike.ofReal ∘ hF.eigenvalues : Fin N → ℂ)
        = ((P : Matrix (Fin N) (Fin N) ℂ)ᴴ * (P : Matrix (Fin N) (Fin N) ℂ)) *
            Matrix.diagonal (RCLike.ofReal ∘ hF.eigenvalues : Fin N → ℂ) *
            ((P : Matrix (Fin N) (Fin N) ℂ)ᴴ * (P : Matrix (Fin N) (Fin N) ℂ)) := by
          rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]; rfl
  refine ⟨U0 * star P, ?_⟩
  have hspec := hF.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  conv_lhs => rw [hspec]
  rw [hD]
  rw [Matrix.UnitaryGroup.mul_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rfl

/-- For a general Hermitian source, the factorial correlations of `F + √t G_N` are those of
the Johansson law with diagonal source `spectralSource F` (increasing eigenvalues of `F`). -/
theorem deformedFactorialCorrelation_eq_johansson (N : ℕ) (t : ℝ≥0)
    (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) (k : ℕ) :
    deformedFactorialCorrelation N t F hF k =
      Johansson.factorialCorrelationMeasure (Johansson.sourceTime N t) (spectralSource F hF) k := by
  obtain ⟨U, hU⟩ := exists_unitary_diagonal_spectralSource F hF
  have hD : (Matrix.diagonal fun i => (spectralSource F hF i : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr (by intro i; simp [IsSelfAdjoint])
  rw [deformedFactorialCorrelation_conj N t U _ hD F hF hU k]
  rfl

/-- Simple spectrum: from `Johansson.SourceContract`, if the increasing
eigenvalues `d = spectralSource F` are distinct, then for `N > 0`, `t > 0`, admissible
contours `R, L` for `d` and `k ≤ N`, the factorial correlation measure of `F + √t G_N` has
density `Re det[K_N(x_i,x_j)]`, `K_N = Johansson.kernel (t/N) d R L`. -/
theorem deformedFactorialCorrelation_eq_kernel_of_strictMono (hJ : Johansson.SourceContract)
    {N : ℕ} (hN : 0 < N) (t : ℝ≥0) (ht : 0 < t) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) (hd : StrictMono (spectralSource F hF)) (R L : ℝ)
    (hC : Johansson.AdmissibleContours (spectralSource F hF) R L) (k : ℕ) (hk : k ≤ N) :
    deformedFactorialCorrelation N t F hF k =
      (volume : Measure (Fin k → ℝ)).withDensity (fun x => ENNReal.ofReal
        (Matrix.det (fun i j => Johansson.kernel (Johansson.sourceTime N t)
          (spectralSource F hF) R L (x i) (x j))).re) := by
  have hS : 0 < Johansson.sourceTime N t := by
    rw [Johansson.sourceTime]
    exact div_pos ht (by exact_mod_cast hN)
  rw [deformedFactorialCorrelation_eq_johansson]
  exact hJ.correlations hN _ hS _ hd R L hC k hk

end BlockBand.GaussianBulk
