module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEUnitaryTransport
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEFirstRowMarginal
public import BlockBand.Native.PSSS.BlockBand.Coarea.HermitianDiscriminant
public import BlockBand.Native.PSSS.BlockBand.Coarea.HermitianDiscriminantReal

/-!
# Fixed-point nullity for deterministically shifted GUE compressions

This module proves the PSSS "fixed-point eigenvalue nullity" omission recorded in
`docs/external/blockband/EXTERNAL_INPUT_AUDIT.md` §1.1 (PSSS Theorem 2/3 proof,
Schur-complement step).  For an arbitrary deterministic Hermitian matrix `D`
(the deterministic part of the compression, already shifted by the real spectral
parameter) and the repository's concrete GUE matrix `W`, the event
`det (D + W) = 0` is null; moreover, for every fixed nonzero vector `v`, the
quadratic form `⟪v, (D + W)⁻¹ v⟫` is almost surely nonzero.

Normalization: `W = hermitianGUEBlock n x` with `x ∼ hermitianGUECoordinateMeasure n t`,
i.e. diagonal entries `N(0,t)` and strict-upper real and imaginary parts
`N(0,t/2)`, all independent; the matrix law is `canonicalHermitianGUEPushforward n t`.
The PSSS normalized block is `t = 1/n`.  Every statement holds for each fixed
`n`, each `t > 0` (or `t = 1/n` in the normalized form), and each fixed `D`, `v`;
the quantifier order is "for all `D, v`, almost surely".  No uniformity or limit is
asserted.  We also prove the same statements for the principal compression
`W.submatrix σ σ` of an `m`-dimensional GUE matrix along any embedding
`σ : Fin n ↪ Fin m` (e.g. `Fin.succ` for the first-row Schur split).

Method: `det (D + W)` and `v* adj (D + W) v` are complex polynomials in the real
GUE coordinates.  Both are nonzero polynomials, witnessed by the coordinates of
`W = 1 - D` (where they evaluate to `1` and `‖v‖²`).  The squared modulus of a
nonzero complex polynomial is a nonzero real polynomial, whose zero set is
Lebesgue-null (`volume_mvPolynomial_zeroSet`), and the GUE coordinate law has a
Lebesgue density for `t > 0`.  The case `n = 0` also holds: the determinant of the
empty matrix is `1`, and there is no nonzero vector, so the quadratic-form
statements are vacuous there.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory MvPolynomial
open scoped ComplexOrder

/-!
## A general polynomial nullity statement for the GUE coordinate law
-/

/-- The concrete GUE coordinate law is absolutely continuous with respect to
Lebesgue measure for every positive variance `t`. -/
theorem hermitianGUECoordinateMeasure_absolutelyContinuous (d : ℕ) {t : ℝ}
    (ht : 0 < t) :
    hermitianGUECoordinateMeasure d t ht.le ≪ volume := by
  rw [hermitianGUECoordinateMeasure_eq_withDensity d ht]
  exact withDensity_absolutelyContinuous _ _

/-- **Polynomial nullity under the concrete GUE coordinate law.**  If a complex
polynomial in the real Hermitian coordinate labels does not vanish at one real
point, then, for every `t > 0`, it is almost surely nonzero at the GUE
coordinates `x ∘ hermitianCoordinateEquivFin d`. -/
theorem ae_eval_ne_zero_hermitianGUECoordinateMeasure (d : ℕ) {t : ℝ} (ht : 0 < t)
    (F : MvPolynomial (HermitianCoordinate d) ℂ) (x₀ : HermitianCoordinate d → ℝ)
    (h₀ : MvPolynomial.eval (fun c => (x₀ c : ℂ)) F ≠ 0) :
    ∀ᵐ x ∂hermitianGUECoordinateMeasure d t ht.le,
      MvPolynomial.eval (fun c => (x (hermitianCoordinateEquivFin d c) : ℂ)) F ≠ 0 := by
  set e := hermitianCoordinateEquivFin d
  let R : MvPolynomial (HermitianCoordinate d) ℝ :=
    mvPolynomialRealPart F ^ 2 + mvPolynomialImagPart F ^ 2
  have hR (y : HermitianCoordinate d → ℝ) :
      MvPolynomial.eval y R =
        Complex.normSq (MvPolynomial.eval (fun c => (y c : ℂ)) F) := by
    simp only [R, map_add, map_pow, eval_mvPolynomialRealPart,
      eval_mvPolynomialImagPart, Complex.normSq_apply]
    ring
  let Q : MvPolynomial (Fin (Fintype.card (HermitianCoordinate d))) ℝ :=
    MvPolynomial.rename e R
  have hQ (y : Fin (Fintype.card (HermitianCoordinate d)) → ℝ) :
      MvPolynomial.eval y Q = MvPolynomial.eval (y ∘ e) R :=
    MvPolynomial.eval_rename _ _ _
  have hQne : Q ≠ 0 := by
    intro hQ0
    have h := hQ (x₀ ∘ e.symm)
    rw [hQ0, map_zero, hR] at h
    apply h₀
    have hx : (fun c => (((x₀ ∘ e.symm) ∘ e) c : ℂ)) = fun c => (x₀ c : ℂ) := by
      funext c
      simp
    rw [hx] at h
    exact Complex.normSq_eq_zero.mp h.symm
  have hnull := volume_mvPolynomial_zeroSet _ Q hQne
  rw [ae_iff]
  refine measure_mono_null ?_
    (hermitianGUECoordinateMeasure_absolutelyContinuous d ht hnull)
  intro x hx
  simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hx ⊢
  rw [hQ, hR]
  simpa [Function.comp_def] using hx

/-!
## The shifted universal compression and its two polynomials
-/

/-- The principal compression along `σ : Fin n ↪ Fin m` of the universal
`m × m` Hermitian coordinate matrix, shifted by a deterministic complex `n × n`
matrix `D`. -/
def shiftedUniversalCompression {m n : ℕ} (σ : Fin n ↪ Fin m)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (HermitianCoordinate m) ℂ) :=
  D.map MvPolynomial.C + (universalHermitianMatrix m).submatrix σ σ

/-- Evaluating the shifted universal compression at real coordinates gives
`D + (hermitianMatrixOfCoordinates x).submatrix σ σ`. -/
theorem map_eval_shiftedUniversalCompression {m n : ℕ} (σ : Fin n ↪ Fin m)
    (D : Matrix (Fin n) (Fin n) ℂ) (x : HermitianCoordinate m → ℝ) :
    (shiftedUniversalCompression σ D).map (MvPolynomial.eval fun c => (x c : ℂ)) =
      D + (hermitianMatrixOfCoordinates x).submatrix σ σ := by
  ext i j
  have h := congrFun (congrFun (eval_universalHermitianMatrix x) (σ i)) (σ j)
  simp only [Matrix.map_apply] at h
  simp only [shiftedUniversalCompression, Matrix.map_apply, Matrix.add_apply,
    Matrix.submatrix_apply, map_add, MvPolynomial.eval_C, h]

/-- The determinant polynomial `det (D + W_σ)` in the real GUE coordinates. -/
def shiftedDetPolynomial {m n : ℕ} (σ : Fin n ↪ Fin m)
    (D : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (HermitianCoordinate m) ℂ :=
  (shiftedUniversalCompression σ D).det

theorem eval_shiftedDetPolynomial {m n : ℕ} (σ : Fin n ↪ Fin m)
    (D : Matrix (Fin n) (Fin n) ℂ) (x : HermitianCoordinate m → ℝ) :
    MvPolynomial.eval (fun c => (x c : ℂ)) (shiftedDetPolynomial σ D) =
      (D + (hermitianMatrixOfCoordinates x).submatrix σ σ).det := by
  rw [shiftedDetPolynomial, RingHom.map_det, RingHom.mapMatrix_apply,
    map_eval_shiftedUniversalCompression]

/-!
## Deterministic witness: a Hermitian matrix whose compression is `1 - D`
-/

/-- The `m × n` partial-isometry matrix of the embedding `σ`. -/
def embeddingMatrix {m n : ℕ} (σ : Fin n ↪ Fin m) : Matrix (Fin m) (Fin n) ℂ :=
  (1 : Matrix (Fin m) (Fin m) ℂ).submatrix id σ

/-- The Hermitian `m × m` matrix `P (1 - D) Pᴴ`, `P = embeddingMatrix σ`. -/
def extendedOneSub {m n : ℕ} (σ : Fin n ↪ Fin m) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.IsHermitian) : HermitianMatrix (Fin m) :=
  ⟨embeddingMatrix σ * (1 - D) * (embeddingMatrix σ)ᴴ,
    isHermitian_mul_mul_conjTranspose _ ((isHermitian_one).sub hD)⟩

theorem extendedOneSub_submatrix {m n : ℕ} (σ : Fin n ↪ Fin m)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    (extendedOneSub σ D hD).1.submatrix σ σ = 1 - D := by
  have hP : (embeddingMatrix σ).submatrix σ id = 1 := by
    rw [embeddingMatrix, submatrix_submatrix]
    exact submatrix_one_embedding σ
  have hPh : (embeddingMatrix σ)ᴴ.submatrix id σ = 1 := by
    rw [← conjTranspose_submatrix, hP, conjTranspose_one]
  change (embeddingMatrix σ * (1 - D) * (embeddingMatrix σ)ᴴ).submatrix σ σ = 1 - D
  rw [submatrix_mul _ _ σ id σ Function.bijective_id,
    submatrix_mul _ _ σ id id Function.bijective_id, hP, hPh, submatrix_id_id,
    one_mul, mul_one]

/-- Real coordinates of `extendedOneSub σ D hD`. -/
def oneSubCoordinates {m n : ℕ} (σ : Fin n ↪ Fin m) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.IsHermitian) : HermitianCoordinate m → ℝ :=
  coordinatesOfHermitian (extendedOneSub σ D hD)

theorem compression_oneSubCoordinates {m n : ℕ} (σ : Fin n ↪ Fin m)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    (hermitianMatrixOfCoordinates (oneSubCoordinates σ D hD)).submatrix σ σ = 1 - D := by
  have h := congrArg Subtype.val
    (hermitianOfCoordinates_coordinatesOfHermitian (extendedOneSub σ D hD))
  change hermitianMatrixOfCoordinates (oneSubCoordinates σ D hD) =
    (extendedOneSub σ D hD).1 at h
  rw [h, extendedOneSub_submatrix]

theorem shiftedDetPolynomial_witness {m n : ℕ} (σ : Fin n ↪ Fin m)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    MvPolynomial.eval (fun c => (oneSubCoordinates σ D hD c : ℂ))
      (shiftedDetPolynomial σ D) = 1 := by
  rw [eval_shiftedDetPolynomial, compression_oneSubCoordinates, add_sub_cancel, det_one]

/-!
## Main theorems in GUE coordinates: compressions of an `m`-dimensional GUE
-/

/-- **Determinant nullity for a shifted GUE compression, coordinate form.**  For all
`m, n`, `σ : Fin n ↪ Fin m`, `t > 0` and deterministic Hermitian `D`, almost surely
`det (D + W.submatrix σ σ) ≠ 0`.  (For `n = 0` this is the empty determinant `1`.) -/
theorem ae_compression_det_ne_zero {m n : ℕ} (σ : Fin n ↪ Fin m) {t : ℝ}
    (ht : 0 < t) (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    ∀ᵐ x ∂hermitianGUECoordinateMeasure m t ht.le,
      (D + (hermitianGUEBlock m x).1.submatrix σ σ).det ≠ 0 := by
  have h₁ := ae_eval_ne_zero_hermitianGUECoordinateMeasure m ht
    (shiftedDetPolynomial σ D) (oneSubCoordinates σ D hD)
    (by rw [shiftedDetPolynomial_witness]; exact one_ne_zero)
  filter_upwards [h₁] with x hx₁
  rwa [eval_shiftedDetPolynomial] at hx₁

/-!
## Main theorems in GUE coordinates: the full `n`-dimensional GUE
-/

/-- **Determinant nullity, coordinate form, full matrix.**  For every `n`, `t > 0`
and deterministic Hermitian `D`, `det (D + W) ≠ 0` almost surely. -/
theorem ae_det_add_hermitianGUEBlock_ne_zero (n : ℕ) {t : ℝ} (ht : 0 < t)
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    ∀ᵐ x ∂hermitianGUECoordinateMeasure n t ht.le,
      (D + (hermitianGUEBlock n x).1).det ≠ 0 :=
  ae_compression_det_ne_zero (Function.Embedding.refl _) ht D hD

/-!
## Matrix-law form under the canonical GUE pushforward
-/

theorem measurableSet_det_add_eq_zero {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    MeasurableSet {W : HermitianMatrix (Fin n) | (D + W.1).det = 0} := by
  have hc : Continuous fun W : HermitianMatrix (Fin n) => (D + W.1).det :=
    (continuous_const.add continuous_subtype_val).matrix_det
  exact hc.measurable (measurableSet_singleton 0)

/-- **Determinant nullity, matrix-law almost-sure form.** -/
theorem ae_canonicalHermitianGUEPushforward_det_add_ne_zero
    (n : ℕ) {t : ℝ} (ht : 0 < t) (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    ∀ᵐ W ∂canonicalHermitianGUEPushforward n t ht.le, (D + W.1).det ≠ 0 := by
  rw [canonicalHermitianGUEPushforward,
    ae_map_iff (measurable_hermitianGUEBlock n).aemeasurable
      (show MeasurableSet {W : HermitianMatrix (Fin n) | (D + W.1).det ≠ 0} from
        (measurableSet_det_add_eq_zero D).compl)]
  exact ae_det_add_hermitianGUEBlock_ne_zero n ht D hD

/-!
## Matrix-law form for compressions of the canonical GUE
-/

/-!
## PSSS normalization `t = 1/n`, including `n = 0`
-/

/-!
## The zeroth-coordinate Schur compression of `GUESchurConditionalReduction`
-/

/-- The canonical zeroth-coordinate compression is the `Fin.succ` principal
submatrix. -/
theorem zerothBlockCompression_eq_submatrix_succ {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    zerothBlockCompression H = H.submatrix Fin.succ Fin.succ := by
  ext i j
  have hi : zerothSplitEquiv n (Sum.inr i) = i.succ := by
    ext; simp [zerothSplitEquiv]
  have hj : zerothSplitEquiv n (Sum.inr j) = j.succ := by
    ext; simp [zerothSplitEquiv]
  simp [zerothBlockCompression, zerothBlockReindex, Matrix.reindex_apply, hi, hj]

/-- **Determinant nullity for the deterministically shifted Schur compression.**
Source: APSSS (2.9) / PSSS Proposition 2.1 proof (`W + D` invertible a.s.).  For
every `n`, every `t > 0` and every deterministic Hermitian `A` of size `n + 1`,
almost surely under `canonicalHermitianGUEPushforward (n + 1) t` the zeroth-coordinate
compression of `A + H` (the matrix `D + W` of the Schur split) has nonzero
determinant.  For `n = 0` the compression is empty and its determinant is `1`.
Quantifier order: for all `n, t, A`, almost surely; no uniformity is claimed. -/
theorem ae_zerothBlockCompression_add_det_ne_zero (n : ℕ) {t : ℝ} (ht : 0 < t)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) :
    ∀ᵐ H ∂canonicalHermitianGUEPushforward (n + 1) t ht.le,
      (zerothBlockCompression (A + H.1)).det ≠ 0 := by
  have hD : (A.submatrix Fin.succ Fin.succ).IsHermitian := hA.submatrix Fin.succ
  have hmeas : MeasurableSet {W : HermitianMatrix (Fin (n + 1)) |
      (A.submatrix Fin.succ Fin.succ + W.1.submatrix Fin.succ Fin.succ).det ≠ 0} := by
    have hc : Continuous fun W : HermitianMatrix (Fin (n + 1)) =>
        (A.submatrix Fin.succ Fin.succ + W.1.submatrix Fin.succ Fin.succ).det :=
      (continuous_const.add
        (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)).matrix_det
    exact (hc.measurable (measurableSet_singleton 0)).compl
  have h : ∀ᵐ W ∂canonicalHermitianGUEPushforward (n + 1) t ht.le,
      (A.submatrix Fin.succ Fin.succ + W.1.submatrix Fin.succ Fin.succ).det ≠ 0 := by
    rw [canonicalHermitianGUEPushforward,
      ae_map_iff (measurable_hermitianGUEBlock (n + 1)).aemeasurable hmeas]
    exact ae_compression_det_ne_zero (Fin.succEmb n) ht _ hD
  filter_upwards [h] with H hH
  rw [zerothBlockCompression_eq_submatrix_succ, Matrix.submatrix_add]
  exact hH

/-- **Normalized form** at the canonical variance `canonicalGUEVariance (n + 1) =
1/(n+1)` used by `GUEFirstRowMarginal`: for every deterministic Hermitian `A`,
almost surely `det (zerothBlockCompression (A + H)) ≠ 0`. -/
theorem ae_canonicalGUEVariance_zerothBlockCompression_add_det_ne_zero (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) :
    ∀ᵐ H ∂canonicalHermitianGUEPushforward (n + 1) (canonicalGUEVariance (n + 1))
        (canonicalGUEVariance_nonneg (n + 1)),
      (zerothBlockCompression (A + H.1)).det ≠ 0 :=
  ae_zerothBlockCompression_add_det_ne_zero n
    (by unfold canonicalGUEVariance; positivity) A hA

end PSSSNative.BlockBand.PSSS
