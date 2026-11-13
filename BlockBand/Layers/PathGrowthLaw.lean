module

public import BlockBand.Layers.PathGrowth
public import BlockBand.Layers.AbsorberCount
public import BlockBand.Model.Construction.GaussianPolynomialNull

/-!
# Almost-sure invertibility of the path and the unconditional growth law

For `b < 1/2` (GUE variance `(1-2b)/W > 0`) and every real `E`, `H_path - E` is
`pathLaw W r b`-a.s. invertible (`ae_isUnit_det_pathMatrix`): for fixed bonds the determinant is a
polynomial in the real Gaussian block coordinates (`gueMeasure_eq_map`), nonzero because at blocks
`s·I` it is the characteristic polynomial of `E - H_bonds` at `s√t`; its zero set is
Lebesgue-null (`Parameters.volume_mvPolynomial_zeroSet_fintype`), and Fubini over the bonds
concludes. This discharges the invertibility hypothesis of `BlockBand.Layers.PathGrowth`:
`map_grownSchur_growthLaw_of_lt`, `ae_grownSchur_eq_pathSchur_of_lt`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open BlockBand.SourceProcess (circularBrownianCoordinates)
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. Flat real coordinates of the path blocks
-/

/-- The `r` path blocks from flat real coordinates `x (k, ((a, b), s))`. -/
def pgBlocksOfCoords (W r : ℕ) (t : ℝ≥0) (x : Fin r × GaussCoord W → ℝ) :
    Fin r → Matrix (Fin W) (Fin W) ℂ :=
  fun k => gueOfCoords W t (fun g => x (k, g))

theorem measurable_pgBlocksOfCoords (W r : ℕ) (t : ℝ≥0) :
    Measurable (pgBlocksOfCoords W r t) := by
  refine measurable_pi_iff.mpr fun k => ?_
  exact (measurable_gueOfCoords W t).comp (measurable_pi_iff.mpr fun g => measurable_pi_apply _)

/-- `r` independent `GUE_W(t)` blocks are the image of i.i.d. standard real coordinates. -/
theorem pi_gueMeasure_eq_map (W r : ℕ) (t : ℝ≥0) :
    (Measure.pi fun _ : Fin r => gueMeasure (Fin W) t) =
      (Measure.pi fun _ : Fin r × GaussCoord W => gaussianReal 0 1).map
        (pgBlocksOfCoords W r t) := by
  have hcurry : (Measure.pi fun _ : Fin r × GaussCoord W => gaussianReal 0 1).map
      (MeasurableEquiv.curry (Fin r) (GaussCoord W) ℝ) =
      Measure.pi fun _ : Fin r => stdGaussCoordLaw (GaussCoord W) := by
    have h := Measure.infinitePi_map_curry (ι := Fin r) (κ := GaussCoord W) (X := ℝ)
      (fun _ _ => gaussianReal 0 1)
    simp only [Measure.infinitePi_eq_pi] at h
    exact h
  have hpi : (Measure.pi fun _ : Fin r => stdGaussCoordLaw (GaussCoord W)).map
      (fun x k => gueOfCoords W t (x k)) =
      Measure.pi fun _ : Fin r => gueMeasure (Fin W) t := by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    rw [Measure.pi_map_pi (fun _ => (measurable_gueOfCoords W t).aemeasurable)]
    simp only [← gueMeasure_eq_map]
  rw [← hpi, ← hcurry, Measure.map_map _ (MeasurableEquiv.curry _ _ _).measurable]
  · rfl
  · exact measurable_pi_iff.mpr fun k =>
      (measurable_gueOfCoords W t).comp (measurable_pi_apply k)

/-!
## 2. The determinant of the path as a polynomial in the block coordinates
-/

/-- The path matrix splits into its block-diagonal part and the bond part. -/
theorem pathMatrix_eq_blockDiag_add {W r : ℕ} (A : Fin r → Matrix (Fin W) (Fin W) ℂ)
    (y : (Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) × (Fin 2 → Matrix (Fin W) (Fin W) ℂ)) :
    pathMatrix (A, y) = Internal.Contracts.Layers.blockDiag A + pathMatrix (0, y) := by
  ext p q
  simp only [pathMatrix, Internal.Contracts.Layers.blockDiag, Matrix.add_apply]
  split_ifs <;> simp

/-- The entry `(a, b)` of the `k`-th block as a polynomial in the flat coordinates. -/
def pgGuePoly (W r : ℕ) (t : ℝ≥0) (k : Fin r) (a b : Fin W) :
    MvPolynomial (Fin r × GaussCoord W) ℂ :=
  MvPolynomial.C (Real.sqrt ((t : ℝ) / 2) : ℂ) *
    (MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
        (MvPolynomial.X (k, ((a, b), 0)) +
          MvPolynomial.X (k, ((a, b), 1)) * MvPolynomial.C Complex.I) +
      MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
        (MvPolynomial.X (k, ((b, a), 0)) -
          MvPolynomial.X (k, ((b, a), 1)) * MvPolynomial.C Complex.I))

theorem eval_pgGuePoly (W r : ℕ) (t : ℝ≥0) (x : Fin r × GaussCoord W → ℝ) (k : Fin r)
    (a b : Fin W) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (pgGuePoly W r t k a b) =
      pgBlocksOfCoords W r t x k a b := by
  simp only [pgGuePoly, pgBlocksOfCoords, gueOfCoords, gueSample, circularBrownianCoordinates,
    Matrix.of_apply, map_mul, map_add, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
    map_div₀, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Fixed bond coordinates of a path. -/
abbrev PgBonds (W r : ℕ) :=
  (Fin (r - 1) → Matrix (Fin W) (Fin W) ℂ) × (Fin 2 → Matrix (Fin W) (Fin W) ℂ)

/-- `H_path - E` with fixed bonds `y`, as a matrix of polynomials in the flat block
coordinates. -/
def pgPathPoly (W r : ℕ) (t : ℝ≥0) (E : ℝ) (y : PgBonds W r) :
    Matrix (Fin r × Fin W) (Fin r × Fin W) (MvPolynomial (Fin r × GaussCoord W) ℂ) :=
  fun p q => (if p.1 = q.1 then pgGuePoly W r t p.1 p.2 q.2 else 0) +
    MvPolynomial.C ((pathMatrix ((0 : Fin r → Matrix (Fin W) (Fin W) ℂ), y) - (E : ℂ) • 1) p q)

theorem eval_det_pgPathPoly (W r : ℕ) (t : ℝ≥0) (E : ℝ) (y : PgBonds W r)
    (x : Fin r × GaussCoord W → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (pgPathPoly W r t E y).det =
      (pathMatrix (pgBlocksOfCoords W r t x, y) - (E : ℂ) • 1).det := by
  rw [RingHom.map_det]
  congr 1
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, pathMatrix_eq_blockDiag_add]
  simp only [pgPathPoly, map_add, MvPolynomial.eval_C, Matrix.sub_apply, Matrix.add_apply,
    Internal.Contracts.Layers.blockDiag]
  split_ifs with h
  · rw [eval_pgGuePoly, h]; ring
  · simp

/-- Witness coordinates: real diagonal entries `s`, everything else `0`. -/
def pgWitness (W r : ℕ) (s : ℝ) : Fin r × GaussCoord W → ℝ :=
  fun i => if i.2.1.1 = i.2.1.2 ∧ i.2.2 = 0 then s else 0

theorem pgBlocksOfCoords_witness (W r : ℕ) (t : ℝ≥0) (s : ℝ) (k : Fin r) :
    pgBlocksOfCoords W r t (pgWitness W r s) k =
      ((Real.sqrt ((t : ℝ) / 2) : ℂ) * (2 / (Real.sqrt 2 : ℂ)) * s) • 1 := by
  ext a b
  simp only [pgBlocksOfCoords, gueOfCoords, gueSample, circularBrownianCoordinates, pgWitness,
    Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp; ring
  · have h' : ¬ b = a := fun e => h e.symm
    simp [h, h']

/-- For fixed bonds and `t > 0`, some block configuration makes `H_path - E` invertible. -/
theorem exists_det_pathMatrix_ne_zero (W r : ℕ) {t : ℝ≥0} (ht : t ≠ 0) (E : ℝ)
    (y : PgBonds W r) :
    ∃ x : Fin r × GaussCoord W → ℝ,
      (pathMatrix (pgBlocksOfCoords W r t x, y) - (E : ℂ) • 1).det ≠ 0 := by
  set N := pathMatrix ((0 : Fin r → Matrix (Fin W) (Fin W) ℂ), y) - (E : ℂ) • 1
  set c : ℂ := (Real.sqrt ((t : ℝ) / 2) : ℂ) * (2 / (Real.sqrt 2 : ℂ))
  have hc : c ≠ 0 := by
    have h1 : Real.sqrt ((t : ℝ) / 2) ≠ 0 := by
      have : (0 : ℝ) < (t : ℝ) / 2 := by
        have := (pos_iff_ne_zero.mpr ht : 0 < t); positivity
      exact (Real.sqrt_pos.mpr this).ne'
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    simp only [c]
    exact mul_ne_zero (by exact_mod_cast h1) (div_ne_zero two_ne_zero h2)
  have key : ∀ s : ℝ, (pathMatrix (pgBlocksOfCoords W r t (pgWitness W r s), y) -
      (E : ℂ) • 1).det = (-N).charpoly.eval (c * s) := by
    intro s
    rw [eval_charpoly, pathMatrix_eq_blockDiag_add]
    congr 1
    ext p q
    simp only [Matrix.sub_apply, Matrix.add_apply, Internal.Contracts.Layers.blockDiag,
      pgBlocksOfCoords_witness, Matrix.neg_apply, sub_neg_eq_add, N, Matrix.scalar_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    by_cases h : p = q
    · subst h; simp [c]; ring
    · have h2 : ¬ (p.1 = q.1 ∧ p.2 = q.2) := fun e => h (Prod.ext e.1 e.2)
      by_cases h1 : p.1 = q.1
      · have h3 : ¬ p.2 = q.2 := fun e => h2 ⟨h1, e⟩
        simp [h, h1, h3]
      · simp [h, h1]
  have hp : (-N).charpoly ≠ 0 := (charpoly_monic _).ne_zero
  have hfin : {s : ℝ | (-N).charpoly.IsRoot (c * s)}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hp).preimage fun a _ b _ hab => by
      have := mul_left_cancel₀ hc hab
      exact_mod_cast this
  obtain ⟨s, hs⟩ := hfin.exists_notMem
  exact ⟨pgWitness W r s, by rw [key]; exact hs⟩

/-!
## 3. Almost-sure invertibility
-/

theorem measurable_det_pathMatrix_sub (W r : ℕ) (E : ℝ) (y : PgBonds W r) :
    Measurable (fun A : Fin r → Matrix (Fin W) (Fin W) ℂ =>
      (pathMatrix (A, y) - (E : ℂ) • 1).det) := by
  have hM : Measurable (fun A : Fin r → Matrix (Fin W) (Fin W) ℂ =>
      pathMatrix (A, y) - (E : ℂ) • 1) := by
    refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
    simp only [Matrix.sub_apply]
    exact (pg_entry ((measurable_pathMatrix W r).comp (measurable_id.prodMk measurable_const))
      p q).sub measurable_const
  exact (continuous_id.matrix_det).measurable.comp hM

/-- For fixed bonds and `t > 0`, independent `GUE_W(t)` blocks make `H_path - E` singular with
probability zero (the determinant is a nonzero polynomial in the Gaussian coordinates). -/
theorem pi_gueMeasure_det_pathMatrix_null (W r : ℕ) {t : ℝ≥0} (ht : t ≠ 0) (E : ℝ)
    (y : PgBonds W r) :
    (Measure.pi fun _ : Fin r => gueMeasure (Fin W) t)
      {A | (pathMatrix (A, y) - (E : ℂ) • 1).det = 0} = 0 := by
  set Q := BlockBand.Parameters.mvPolynomialNormSq (pgPathPoly W r t E y).det
  have hQx : ∀ x, MvPolynomial.eval x Q =
      Complex.normSq (pathMatrix (pgBlocksOfCoords W r t x, y) - (E : ℂ) • 1).det := by
    intro x
    rw [BlockBand.Parameters.eval_mvPolynomialNormSq, eval_det_pgPathPoly]
  have hQ : Q ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_det_pathMatrix_ne_zero W r ht E y
    have h := hQx x
    rw [h0, map_zero] at h
    exact hx (Complex.normSq_eq_zero.mp h.symm)
  have hnull := BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype Q hQ
  have hac := BlockBand.Parameters.pi_absolutelyContinuous_volume
    (fun _ : Fin r × GaussCoord W => gaussianReal 0 1)
    (fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero)
  have hmeasS : MeasurableSet {A : Fin r → Matrix (Fin W) (Fin W) ℂ |
      (pathMatrix (A, y) - (E : ℂ) • 1).det = 0} :=
    measurableSet_eq_fun (measurable_det_pathMatrix_sub W r E y) measurable_const
  rw [pi_gueMeasure_eq_map, Measure.map_apply (measurable_pgBlocksOfCoords W r t) hmeasS]
  apply hac
  convert hnull using 2
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hQx, Complex.normSq_eq_zero]

/-- **Almost-sure invertibility of the path** (`b < 1/2`, so the GUE blocks have positive
variance `(1 - 2b)/W`): for every real `E`, `H_path - E` is invertible `pathLaw W r b`-a.s. -/
theorem ae_isUnit_det_pathMatrix (W r : ℕ) {b : ℝ} (hb : b < 1 / 2) (E : ℝ) :
    ∀ᵐ ω ∂pathLaw W r b, IsUnit (pathMatrix ω - (E : ℂ) • 1).det := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · exact Filter.Eventually.of_forall fun ω => by rw [Matrix.det_isEmpty]; exact isUnit_one
  have := fun t => isProbabilityMeasure_gueMeasure W t
  set t := Real.toNNReal ((1 - 2 * b) / W) with ht_def
  have ht : t ≠ 0 := by
    have hpos : (0 : ℝ) < (1 - 2 * b) / W := div_pos (by linarith) (by exact_mod_cast hW)
    exact (Real.toNNReal_pos.mpr hpos).ne'
  have hmeas : MeasurableSet {ω : PathSample W r | (pathMatrix ω - (E : ℂ) • 1).det = 0} := by
    have hM : Measurable (fun ω : PathSample W r => pathMatrix ω - (E : ℂ) • 1) := by
      refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun q => ?_
      simp only [Matrix.sub_apply]
      exact (pg_entry (measurable_pathMatrix W r) p q).sub measurable_const
    exact measurableSet_eq_fun ((continuous_id.matrix_det).measurable.comp hM) measurable_const
  rw [ae_iff]
  simp only [isUnit_iff_ne_zero, not_not]
  unfold pathLaw
  rw [Measure.prod_apply_symm hmeas]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  exact pi_gueMeasure_det_pathMatrix_null W r ht E y

/-- **Law of the grown Schur matrix, unconditional form** (`b < 1/2`): for `r₀ ≥ 1` and `k ≤ L`,
the law of `grownSchur E ω k` under `growthLaw W r₀ L b` is the law of `pathSchur E` under
`pathLaw W (r₀ + 2k) b`. -/
theorem map_grownSchur_growthLaw_of_lt {W r₀ L : ℕ} {b : ℝ} (hb : b < 1 / 2) (E : ℝ)
    (hr₀ : 1 ≤ r₀) {k : ℕ} (hk : k ≤ L) :
    (growthLaw W r₀ L b).map (fun ω => grownSchur E ω k) =
      (pathLaw W (r₀ + 2 * k) b).map (pathSchur E) :=
  map_grownSchur_growthLaw b E hr₀ (fun r _ => ae_isUnit_det_pathMatrix W r hb E) hk

/-- **Almost-sure growth identity, unconditional form** (`b < 1/2`): for `r₀ ≥ 1` and `k ≤ L`,
`growthLaw W r₀ L b`-a.s. `grownSchur E ω k = pathSchur E (pgPath ω k)`, where `pgPath ω k` is
distributed as `pathLaw W (r₀ + 2k) b` (`measurePreserving_pgPath`). -/
theorem ae_grownSchur_eq_pathSchur_of_lt {W r₀ L : ℕ} {b : ℝ} (hb : b < 1 / 2) (E : ℝ)
    (hr₀ : 1 ≤ r₀) {k : ℕ} (hk : k ≤ L) :
    ∀ᵐ ω ∂growthLaw W r₀ L b, grownSchur E ω k = pathSchur E (pgPath ω k) :=
  ae_grownSchur_eq_pathSchur b E hr₀ (fun r _ => ae_isUnit_det_pathMatrix W r hb E) hk

end BlockBand.Layers
