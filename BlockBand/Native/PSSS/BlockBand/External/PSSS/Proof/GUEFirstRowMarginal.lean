module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUESchurConditionalReduction

/-!
# Standardized first-row marginal of the canonical coordinate GUE

At canonical variance `1/N`, multiplying the diagonal coordinate by `√N` and
each real/imaginary strict-upper coordinate by `√(2N)` produces independent
standard real Gaussians.  This module proves the exact product law directly
from the coordinate product construction and packages the first row in the
real form consumed by `quadraticRatio_tail`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- Canonical positive GUE variance `1/N`. -/
def canonicalGUEVariance (N : ℕ) : ℝ := 1 / (N : ℝ)

/-- Nonnegativity of the canonical variance. -/
theorem canonicalGUEVariance_nonneg (N : ℕ) : 0 ≤ canonicalGUEVariance N := by
  unfold canonicalGUEVariance
  positivity

/-- Coordinate standardization: `√N` on the diagonal and `√(2N)` on each
real or imaginary strict-upper coordinate. -/
def standardizedGUECoordinateScale (N : ℕ)
    (k : Fin (Fintype.card (HermitianCoordinate N))) : ℝ :=
  match (hermitianCoordinateEquivFin N).symm k with
  | .inl _ => Real.sqrt N
  | .inr _ => Real.sqrt (2 * N)

/-- The standardized full real coordinate family. -/
def standardizedGUECoordinates (N : ℕ) (x : HermitianCoordinateSpace N) :
    HermitianCoordinateSpace N :=
  fun k => standardizedGUECoordinateScale N k * x k

/-- Exact variance cancellation behind standardization. -/
theorem standardizedGUECoordinateScale_variance {N : ℕ} (hN : 0 < N)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    NNReal.mk (standardizedGUECoordinateScale N k ^ 2)
        (sq_nonneg _) *
      hermitianGUEFinCoordinateVariance N (canonicalGUEVariance N)
        (canonicalGUEVariance_nonneg N) k = 1 := by
  rcases hc : (hermitianCoordinateEquivFin N).symm k with i | c
  · simp only [standardizedGUECoordinateScale,
      hermitianGUEFinCoordinateVariance, hc]
    apply NNReal.eq
    change Real.sqrt (N : ℝ) ^ 2 * (1 / (N : ℝ)) = 1
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp
  · simp only [standardizedGUECoordinateScale,
      hermitianGUEFinCoordinateVariance, hc]
    apply NNReal.eq
    change Real.sqrt (2 * (N : ℝ)) ^ 2 *
      (1 / (N : ℝ) / 2) = 1
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * N)]
    field_simp

/-- Every standardized coordinate is exactly `N(0,1)`. -/
theorem standardizedGUECoordinate_hasLaw {N : ℕ} (hN : 0 < N)
    (k : Fin (Fintype.card (HermitianCoordinate N))) :
    HasLaw (fun x : HermitianCoordinateSpace N =>
      standardizedGUECoordinates N x k) (gaussianReal 0 1)
      (hermitianGUECoordinateMeasure N (canonicalGUEVariance N)
        (canonicalGUEVariance_nonneg N)) := by
  have h := gaussianReal_const_mul
    (hermitianGUECoordinate_hasLaw N (canonicalGUEVariance N)
      (canonicalGUEVariance_nonneg N) k)
    (standardizedGUECoordinateScale N k)
  simpa only [standardizedGUECoordinates, mul_zero,
    standardizedGUECoordinateScale_variance hN k] using h

/-- A concrete index for the diagonal coordinate and the two real coordinates
of each strict-upper entry in the zeroth row of an `(n+1) × (n+1)` matrix. -/
abbrev ConcreteFirstRowCoordinate (n : ℕ) := Unit ⊕ (Fin n × Fin 2)

/-- Embed the concrete first-row indexing into Hermitian coordinates.  The
second `Fin 2` coordinate distinguishes real and imaginary parts. -/
def concreteFirstRowHermitianCoordinate (n : ℕ) :
    ConcreteFirstRowCoordinate n → HermitianCoordinate (n + 1)
  | .inl _ => .inl 0
  | .inr (j, q) =>
      if q = 0 then
        .inr (.inl ⟨(0, j.succ), by simp⟩)
      else
        .inr (.inr ⟨(0, j.succ), by simp⟩)

/-- The concrete diagonal/row-coordinate embedding has no collisions. -/
theorem concreteFirstRowHermitianCoordinate_injective (n : ℕ) :
    Function.Injective (concreteFirstRowHermitianCoordinate n) := by
  intro a b hab
  rcases a with _ | ⟨j, q⟩ <;> rcases b with _ | ⟨j', q'⟩
  · rfl
  · fin_cases q'
    all_goals simp [concreteFirstRowHermitianCoordinate] at hab
  · fin_cases q
    all_goals simp [concreteFirstRowHermitianCoordinate] at hab
  · fin_cases q <;> fin_cases q'
    all_goals simp [concreteFirstRowHermitianCoordinate] at hab ⊢
    all_goals exact hab

/-- Concrete finite-coordinate index used to read a first row from the
repository's coordinate product. -/
def concreteFirstRowFinCoordinate (n : ℕ) (a : ConcreteFirstRowCoordinate n) :
    Fin (Fintype.card (HermitianCoordinate (n + 1))) :=
  hermitianCoordinateEquivFin (n + 1) (concreteFirstRowHermitianCoordinate n a)

/-- The finite-coordinate version of the concrete embedding is injective. -/
theorem concreteFirstRowFinCoordinate_injective (n : ℕ) :
    Function.Injective (concreteFirstRowFinCoordinate n) :=
  (hermitianCoordinateEquivFin (n + 1)).injective.comp
    (concreteFirstRowHermitianCoordinate_injective n)

/-- The exact realification needed by the diagonal quadratic-ratio estimate:
one `√(n+1)`-scaled diagonal variable followed by the `√(2(n+1))`-scaled
real and imaginary parts of the `n` zeroth-row entries. -/
def concreteStandardizedFirstRow (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) :
    ConcreteFirstRowCoordinate n → ℝ :=
  fun a => standardizedGUECoordinates (n + 1) x
    (concreteFirstRowFinCoordinate n a)

/-- The distinguished diagonal is scaled by exactly `√(n+1)`. -/
theorem concreteStandardizedFirstRow_diagonal (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) :
    concreteStandardizedFirstRow n x (.inl ()) =
      Real.sqrt (n + 1) *
        x (hermitianCoordinateEquivFin (n + 1) (.inl 0)) := by
  simp [concreteStandardizedFirstRow, standardizedGUECoordinates,
    concreteFirstRowFinCoordinate, standardizedGUECoordinateScale,
    concreteFirstRowHermitianCoordinate]

/-- Each real strict-upper zeroth-row coordinate is scaled by exactly
`√(2(n+1))`. -/
theorem concreteStandardizedFirstRow_real (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) (j : Fin n) :
    concreteStandardizedFirstRow n x (.inr (j, 0)) =
      Real.sqrt (2 * (n + 1)) *
        x (hermitianCoordinateEquivFin (n + 1)
          (.inr (.inl ⟨(0, j.succ), by simp⟩))) := by
  simp [concreteStandardizedFirstRow, standardizedGUECoordinates,
    concreteFirstRowFinCoordinate, standardizedGUECoordinateScale,
    concreteFirstRowHermitianCoordinate]

/-- Each imaginary strict-upper zeroth-row coordinate is scaled by exactly
`√(2(n+1))`. -/
theorem concreteStandardizedFirstRow_imag (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) (j : Fin n) :
    concreteStandardizedFirstRow n x (.inr (j, 1)) =
      Real.sqrt (2 * (n + 1)) *
        x (hermitianCoordinateEquivFin (n + 1)
          (.inr (.inr ⟨(0, j.succ), by simp⟩))) := by
  simp [concreteStandardizedFirstRow, standardizedGUECoordinates,
    concreteFirstRowFinCoordinate, standardizedGUECoordinateScale,
    concreteFirstRowHermitianCoordinate]

/-- Exact diagonal plus `n` circular-complex realification law.  Every output
coordinate is `N(0,1)`, and all `1+2n` coordinates are mutually independent.
Thus pairing the two coordinates indexed by `(j,0)` and `(j,1)` and dividing
by `√2` gives a standard circular complex variable, while the undivided pair
is precisely the `√2` realification used by `quadraticRatio_tail`. -/
theorem hasLaw_concreteStandardizedFirstRow (n : ℕ) :
    HasLaw (concreteStandardizedFirstRow n)
      (Measure.pi fun _ : ConcreteFirstRowCoordinate n => gaussianReal 0 1)
      (hermitianGUECoordinateMeasure (n + 1)
        (canonicalGUEVariance (n + 1))
        (canonicalGUEVariance_nonneg (n + 1))) := by
  apply iIndepFun.hasLaw_pi
  · intro a
    exact standardizedGUECoordinate_hasLaw (Nat.zero_lt_succ n)
      (concreteFirstRowFinCoordinate n a)
  · exact ((iIndepFun_hermitianGUECoordinates (n + 1)
      (canonicalGUEVariance (n + 1))
      (canonicalGUEVariance_nonneg (n + 1))).precomp
        (concreteFirstRowFinCoordinate_injective n)).comp
      (fun a x => standardizedGUECoordinateScale (n + 1)
        (concreteFirstRowFinCoordinate n a) * x)
      (fun _ => by fun_prop)

/-- Read the standardized diagonal and zeroth-row realification directly from
a Hermitian matrix. -/
def matrixStandardizedFirstRow (n : ℕ)
    (H : HermitianMatrix (Fin (n + 1))) : ConcreteFirstRowCoordinate n → ℝ
  | .inl _ => Real.sqrt (n + 1) * (H.1 0 0).re
  | .inr (j, q) =>
      if q = 0 then Real.sqrt (2 * (n + 1)) * (H.1 0 j.succ).re
      else Real.sqrt (2 * (n + 1)) * (H.1 0 j.succ).im

/-- Direct matrix first-row extraction is Borel measurable. -/
theorem measurable_matrixStandardizedFirstRow (n : ℕ) :
    Measurable (matrixStandardizedFirstRow n) := by
  rw [measurable_pi_iff]
  intro a
  rcases a with _ | ⟨j, q⟩
  · change Measurable (fun H : HermitianMatrix (Fin (n + 1)) =>
      Real.sqrt (n + 1) * (H.1 0 0).re)
    exact (by fun_prop : Measurable (fun A : Matrix (Fin (n + 1))
      (Fin (n + 1)) ℂ => Real.sqrt (n + 1) * (A 0 0).re)).comp
      measurable_coe_hermitianMatrix
  · fin_cases q
    · change Measurable (fun H : HermitianMatrix (Fin (n + 1)) =>
        Real.sqrt (2 * (n + 1)) * (H.1 0 j.succ).re)
      exact (by fun_prop : Measurable (fun A : Matrix (Fin (n + 1))
        (Fin (n + 1)) ℂ =>
          Real.sqrt (2 * (n + 1)) * (A 0 j.succ).re)).comp
        measurable_coe_hermitianMatrix
    · change Measurable (fun H : HermitianMatrix (Fin (n + 1)) =>
        Real.sqrt (2 * (n + 1)) * (H.1 0 j.succ).im)
      exact (by fun_prop : Measurable (fun A : Matrix (Fin (n + 1))
        (Fin (n + 1)) ℂ =>
          Real.sqrt (2 * (n + 1)) * (A 0 j.succ).im)).comp
        measurable_coe_hermitianMatrix

/-- Reconstructing the canonical Hermitian matrix and then reading its first
row agrees exactly with the real-coordinate standardization. -/
theorem matrixStandardizedFirstRow_hermitianGUEBlock (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) :
    matrixStandardizedFirstRow n (hermitianGUEBlock (n + 1) x) =
      concreteStandardizedFirstRow n x := by
  funext a
  rcases a with _ | ⟨j, q⟩
  · exact (concreteStandardizedFirstRow_diagonal n x).symm
  · fin_cases q
    · change Real.sqrt (2 * (n + 1)) *
          ((hermitianGUEBlock (n + 1) x).1 0 j.succ).re =
        concreteStandardizedFirstRow n x (.inr (j, 0))
      have hj : (0 : Fin (n + 1)) ≠ j.succ := ne_of_lt (by simp)
      rw [concreteStandardizedFirstRow_real]
      congr 1
      simp [hermitianGUEBlock, hermitianOfFinCoordinates,
        hermitianOfCoordinates, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, hj]
    · change Real.sqrt (2 * (n + 1)) *
          ((hermitianGUEBlock (n + 1) x).1 0 j.succ).im =
        concreteStandardizedFirstRow n x (.inr (j, 1))
      have hj : (0 : Fin (n + 1)) ≠ j.succ := ne_of_lt (by simp)
      rw [concreteStandardizedFirstRow_imag]
      congr 1
      simp [hermitianGUEBlock, hermitianOfFinCoordinates,
        hermitianOfCoordinates, hermitianMatrixOfCoordinates,
        hermitianUpperEntry, hj]

/-- Concrete first-row marginal transport from the canonical Hermitian GUE
pushforward itself: the standardized diagonal and `√2`-realified row entries
have the independent standard-real product law. -/
theorem hasLaw_matrixStandardizedFirstRow (n : ℕ) :
    HasLaw (matrixStandardizedFirstRow n)
      (Measure.pi fun _ : ConcreteFirstRowCoordinate n => gaussianReal 0 1)
      (canonicalHermitianGUEPushforward (n + 1)
        (canonicalGUEVariance (n + 1))
        (canonicalGUEVariance_nonneg (n + 1))) := by
  refine ⟨(measurable_matrixStandardizedFirstRow n).aemeasurable, ?_⟩
  unfold canonicalHermitianGUEPushforward
  rw [Measure.map_map (measurable_matrixStandardizedFirstRow n)
    (measurable_hermitianGUEBlock (n + 1))]
  have hcomp : matrixStandardizedFirstRow n ∘ hermitianGUEBlock (n + 1) =
      concreteStandardizedFirstRow n := by
    funext x
    exact matrixStandardizedFirstRow_hermitianGUEBlock n x
  rw [hcomp, (hasLaw_concreteStandardizedFirstRow n).map_eq]

end PSSSNative.BlockBand.PSSS
