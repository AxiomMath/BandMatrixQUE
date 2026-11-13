module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEOneDimensionalFixedVector
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEShiftedCompressionNull

/-!
# Canonical fixed-vector inverse tail

This module integrates the deterministic Schur-compression estimate against the
complementary GUE block.  The first-row variables are never replaced by
an assumed conditional law: their product law and independence from the
compression are inherited from the concrete Hermitian coordinate product.

Normalization is the APSSS normalization `GUE_N(1/N)`, and the inverse-vector
event is `t * √N ≤ ‖(A+V)⁻¹ e₀‖`.  Constants are absolute, preceding all matrix,
dimension, and threshold quantifiers.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set

/-- The slightly enlarged normalized Schur event which results from the
`√(2N)` realification of a circular complex first row. -/
def enlargedRealSchurEvent {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ)
    (c : ℝ) (b : Fin m → ℝ) (t : ℝ) (p : ℝ × (Fin m → ℝ)) : Prop :=
  (t * |p.1 + c - dotProduct (p.2 + b) (Q *ᵥ (p.2 + b))|) ^ 2 ≤
    1 + 2 * ‖(WithLp.toLp 2 (Q *ᵥ (p.2 + b)) :
      EuclideanSpace ℝ (Fin m))‖ ^ 2

/-- The enlarged event splits into a scalar small interval and the
quadratic-ratio event, with the exact extra `√2` caused by realification. -/
theorem enlargedRealSchurEvent_split {m : ℕ}
    (Q : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) (b : Fin m → ℝ)
    (t : ℝ) (p : ℝ × (Fin m → ℝ))
    (h : enlargedRealSchurEvent Q c b t p) :
    t / 2 * |p.1 + c - dotProduct (p.2 + b) (Q *ᵥ (p.2 + b))| ≤ 1 ∨
      t / (2 * Real.sqrt 2) *
          |dotProduct (p.2 + b) (Q *ᵥ (p.2 + b)) - (p.1 + c)| ≤
        ‖(WithLp.toLp 2 (Q *ᵥ (p.2 + b)) :
          EuclideanSpace ℝ (Fin m))‖ := by
  have hs := schur_ratio_two_event_split
    (t := t)
    (s := |p.1 + c - dotProduct (p.2 + b) (Q *ᵥ (p.2 + b))|)
    (q := Real.sqrt 2 * ‖(WithLp.toLp 2 (Q *ᵥ (p.2 + b)) :
      EuclideanSpace ℝ (Fin m))‖)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (by
      simpa [enlargedRealSchurEvent, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using h)
  rcases hs with hs | hs
  · exact Or.inl hs
  · right
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    calc
      t / (2 * Real.sqrt 2) *
          |dotProduct (p.2 + b) (Q *ᵥ (p.2 + b)) - (p.1 + c)| =
          (t / 2 *
            |p.1 + c - dotProduct (p.2 + b) (Q *ᵥ (p.2 + b))|) /
            Real.sqrt 2 := by rw [abs_sub_comm]; field_simp
      _ ≤ (Real.sqrt 2 *
          ‖(WithLp.toLp 2 (Q *ᵥ (p.2 + b)) :
            EuclideanSpace ℝ (Fin m))‖) / Real.sqrt 2 :=
        div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _)
      _ = _ := by field_simp

/-- Uniform conditional estimate for the enlarged real Schur event.  This is
valid for every deterministic symmetric nonzero form and arbitrary scalar and
row shifts. -/
theorem enlargedRealSchurEvent_conditional_tail :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ), Q.IsSymm → Q ≠ 0 →
      ∀ (c : ℝ) (b : Fin m → ℝ) (t : ℝ), 1 ≤ t →
      ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => gaussianReal 0 1))
        {p | enlargedRealSchurEvent Q c b t p} ≤ ENNReal.ofReal (K / t) := by
  obtain ⟨C, hC, hquad⟩ := quadraticRatio_tail
  refine ⟨8 + 4 * C, by linarith, ?_⟩
  intro m Q hQ hQ0 c b t ht
  let μ := Measure.pi fun _ : Fin m => gaussianReal 0 1
  let S : Set (ℝ × (Fin m → ℝ)) := {p | enlargedRealSchurEvent Q c b t p}
  change (gaussianReal 0 1).prod μ S ≤ ENNReal.ofReal ((8 + 4 * C) / t)
  by_cases ht4 : 4 ≤ t
  · let S₀ : Set (ℝ × (Fin m → ℝ)) :=
      {p | t / 2 * |p.1 + c - dotProduct (p.2 + b) (Q *ᵥ (p.2 + b))| ≤ 1}
    let S₁ : Set (ℝ × (Fin m → ℝ)) :=
      {p | t / (2 * Real.sqrt 2) *
          |dotProduct (p.2 + b) (Q *ᵥ (p.2 + b)) - (p.1 + c)| ≤
        ‖(WithLp.toLp 2 (Q *ᵥ (p.2 + b)) : EuclideanSpace ℝ (Fin m))‖}
    have hmS₀ : MeasurableSet S₀ := by
      unfold S₀
      apply measurableSet_le <;> fun_prop
    have hmS₁ : MeasurableSet S₁ := by
      unfold S₁
      apply measurableSet_le <;> fun_prop
    have hsub : S ⊆ S₀ ∪ S₁ := by
      intro p hp
      exact enlargedRealSchurEvent_split Q c b t p hp
    have hscalar : (gaussianReal 0 1).prod μ S₀ ≤ ENNReal.ofReal (4 / t) := by
      apply prod_measure_le_of_fiber_le (gaussianReal 0 1) μ hmS₀
      intro y
      have hs := gaussianReal_scalarSchurBranch
        (dotProduct (y + b) (Q *ᵥ (y + b)) - c) t (by linarith)
      rw [show ((fun g => (g, y)) ⁻¹' S₀) =
          {g | t / 2 *
            |g - (dotProduct (y + b) (Q *ᵥ (y + b)) - c)| ≤ 1} by
        ext g
        simp only [S₀, Set.mem_preimage, Set.mem_ofPred_eq]
        ring]
      exact hs
    have hquadratic : (gaussianReal 0 1).prod μ S₁ ≤
        ENNReal.ofReal (2 * Real.sqrt 2 * C / t) := by
      rw [Measure.prod_apply hmS₁]
      calc
        (∫⁻ x, μ ((fun y => (x, y)) ⁻¹' S₁) ∂gaussianReal 0 1) ≤
            ∫⁻ _x, ENNReal.ofReal
              (C / (t / (2 * Real.sqrt 2))) ∂gaussianReal 0 1 := by
          apply lintegral_mono
          intro x
          have hparameter : 1 ≤ t / (2 * Real.sqrt 2) := by
            have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 :=
              Real.sq_sqrt (by norm_num)
            have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
            have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith
            apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)).2
            nlinarith
          have hq := hquad m Q hQ hQ0 b (x + c)
            (t / (2 * Real.sqrt 2)) hparameter
          simpa only [μ, S₁, Set.preimage_ofPred_eq] using hq
        _ = ENNReal.ofReal (2 * Real.sqrt 2 * C / t) := by
          rw [lintegral_const]
          simp only [measure_univ, mul_one]
          congr 1
          field_simp
    calc
      (gaussianReal 0 1).prod μ S ≤
          (gaussianReal 0 1).prod μ (S₀ ∪ S₁) := measure_mono hsub
      _ ≤ (gaussianReal 0 1).prod μ S₀ +
          (gaussianReal 0 1).prod μ S₁ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 / t) +
          ENNReal.ofReal (2 * Real.sqrt 2 * C / t) :=
        add_le_add hscalar hquadratic
      _ ≤ ENNReal.ofReal ((8 + 4 * C) / t) := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 4 / t)] <;> try positivity
        apply ENNReal.ofReal_le_ofReal
        have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 :=
          Real.sq_sqrt (by norm_num)
        have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith
        have hC0 : 0 ≤ C := by linarith
        have ht0 : 0 < t := by linarith
        calc
          4 / t + 2 * Real.sqrt 2 * C / t =
              (4 + 2 * Real.sqrt 2 * C) / t := by ring
          _ ≤ (8 + 4 * C) / t := by
            apply (div_le_div_iff_of_pos_right ht0).2
            nlinarith
  · have hprob : (gaussianReal 0 1).prod μ S ≤ 1 := by
      calc
        (gaussianReal 0 1).prod μ S ≤
            (gaussianReal 0 1).prod μ Set.univ :=
          measure_mono (Set.subset_univ S)
        _ = 1 := measure_univ
    calc
      (gaussianReal 0 1).prod μ S ≤ 1 := hprob
      _ ≤ ENNReal.ofReal ((8 + 4 * C) / t) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hC0 : 0 ≤ C := by linarith
        have htpos : 0 < t := by linarith
        apply (le_div_iff₀ htpos).2
        nlinarith

/-- Reindexing the zeroth coordinate into Schur coordinates preserves the
inverse-vector Euclidean norm. -/
theorem norm_zerothBlockReindex_inv_firstCoordinate {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ‖(WithLp.toLp 2 (H⁻¹ *ᵥ phaseFixedCoordinateVector (0 : Fin (n + 1))) :
        EuclideanSpace ℂ (Fin (n + 1)))‖ =
      ‖(WithLp.toLp 2 ((zerothBlockReindex H)⁻¹ *ᵥ schurFirstCoordinate) :
        EuclideanSpace ℂ (Unit ⊕ Fin n))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖(H⁻¹ *ᵥ phaseFixedCoordinateVector 0) i‖ ^ 2) =
    ∑ i, ‖((zerothBlockReindex H)⁻¹ *ᵥ schurFirstCoordinate) i‖ ^ 2
  unfold zerothBlockReindex
  rw [Matrix.inv_reindex]
  have hvec :
      Matrix.reindex (zerothSplitEquiv n).symm (zerothSplitEquiv n).symm H⁻¹ *ᵥ
          schurFirstCoordinate =
        fun i => (H⁻¹ *ᵥ phaseFixedCoordinateVector 0) (zerothSplitEquiv n i) := by
    have hs : (schurFirstCoordinate (n := n)) =
        Pi.single (Sum.inl () : Unit ⊕ Fin n) (1 : ℂ) := by
      funext i
      rcases i with i | i
      · cases i
        simp [schurFirstCoordinate]
      · simp [schurFirstCoordinate]
    rw [hs, Matrix.mulVec_single_one]
    change _ = fun i => (H⁻¹ *ᵥ Pi.single 0 1) (zerothSplitEquiv n i)
    rw [Matrix.mulVec_single_one]
    have hzero : zerothSplitEquiv n (Sum.inl ()) = (0 : Fin (n + 1)) := by
      ext
      simp [zerothSplitEquiv]
    ext i
    simp [Matrix.reindex_apply, hzero]
  rw [hvec]
  exact (Equiv.sum_comp (zerothSplitEquiv n)
    (fun i => ‖(H⁻¹ *ᵥ phaseFixedCoordinateVector 0) i‖ ^ 2)).symm

/-- A large canonical inverse vector forces the normalized complex Schur
inequality whenever the complementary block and Schur denominator are
nonsingular. -/
theorem inverse_firstCoordinate_implies_schur_event {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian)
    (hD : (zerothBlockCompression H).det ≠ 0)
    (hs : schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
      (zerothBlockCompression H) ≠ 0)
    (t : ℝ) (ht : 0 ≤ t)
    (hlarge : t * Real.sqrt (n + 1) ≤
      ‖(WithLp.toLp 2 (H⁻¹ *ᵥ phaseFixedCoordinateVector 0) :
        EuclideanSpace ℂ (Fin (n + 1)))‖) :
    (t * Real.sqrt (n + 1) *
        ‖schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
          (zerothBlockCompression H)‖) ^ 2 ≤
      1 + ∑ j : Fin n,
        ‖((zerothBlockCompression H)⁻¹ *ᵥ zerothBlockColumn H) j‖ ^ 2 := by
  let s := schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
    (zerothBlockCompression H)
  let q := ∑ j : Fin n,
    ‖((zerothBlockCompression H)⁻¹ *ᵥ zerothBlockColumn H) j‖ ^ 2
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm := norm_sq_zerothBlockReindex_inv_mulVec_firstCoordinate
    H hH hD hs
  rw [← norm_zerothBlockReindex_inv_firstCoordinate H] at hnorm
  change _ = ‖s⁻¹‖ ^ 2 * (1 + q) at hnorm
  have hinv : ‖s⁻¹‖ = 1 / ‖s‖ := by
    rw [norm_inv]
    exact (one_div _).symm
  rw [hinv] at hnorm
  have hsq : (t * Real.sqrt (n + 1)) ^ 2 ≤
      ‖(WithLp.toLp 2 (H⁻¹ *ᵥ phaseFixedCoordinateVector 0) :
        EuclideanSpace ℂ (Fin (n + 1)))‖ ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg ht (Real.sqrt_nonneg _))
      (norm_nonneg _)).2 hlarge
  rw [hnorm] at hsq
  change (t * Real.sqrt (n + 1) * ‖s‖) ^ 2 ≤ 1 + q
  have hs2 : 0 < ‖s‖ ^ 2 := sq_pos_of_pos hspos
  have hm := mul_le_mul_of_nonneg_right hsq hs2.le
  convert hm using 1 <;> field_simp

/-- Realification preserves the Hermitian quadratic form in its real part. -/
theorem dotProduct_complexRealification_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    dotProduct (complexVectorRealification z)
        (complexMatrixRealification A *ᵥ complexVectorRealification z) =
      (dotProduct (star z) (A *ᵥ z)).re := by
  rw [complexMatrixRealification_mulVec]
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_two, complexVectorRealification, Complex.mul_re]

/-- Realification preserves the sum of squared coordinate norms. -/
theorem sum_sq_complexVectorRealification {n : ℕ} (z : Fin n → ℂ) :
    ∑ p : Fin n × Fin 2, complexVectorRealification z p ^ 2 =
      ∑ j : Fin n, ‖z j‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_two, complexVectorRealification, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- Real and imaginary coordinates, relabelled by the canonical finite ordinal. -/
def reindexedComplexVectorRealification {n : ℕ} (z : Fin n → ℂ) :
    Fin (2 * n) → ℝ := fun k =>
  complexVectorRealification z ((complexRealCoordinateEquivFin n).symm k)

/-- The reindexed realification still intertwines matrix-vector multiplication. -/
theorem fixedCompressionRealMatrix_mulVec_reindexed {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    fixedCompressionRealMatrix D *ᵥ reindexedComplexVectorRealification z =
      reindexedComplexVectorRealification (D⁻¹ *ᵥ z) := by
  unfold fixedCompressionRealMatrix reindexedComplexVectorRealification
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply]
  change (∑ i, complexMatrixRealification D⁻¹
      ((complexRealCoordinateEquivFin n).symm k)
      ((complexRealCoordinateEquivFin n).symm i) *
        complexVectorRealification z ((complexRealCoordinateEquivFin n).symm i)) =
    complexVectorRealification (D⁻¹ *ᵥ z)
      ((complexRealCoordinateEquivFin n).symm k)
  calc
    _ = ∑ i, complexMatrixRealification D⁻¹
        ((complexRealCoordinateEquivFin n).symm k) i *
          complexVectorRealification z i :=
      (complexRealCoordinateEquivFin n).symm.sum_comp _
    _ = _ := congrFun (complexMatrixRealification_mulVec D⁻¹ z)
      ((complexRealCoordinateEquivFin n).symm k)

/-- Reindexing preserves the realified quadratic form. -/
theorem dotProduct_reindexedComplexRealification {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    dotProduct (reindexedComplexVectorRealification z)
        (fixedCompressionRealMatrix D *ᵥ reindexedComplexVectorRealification z) =
      (dotProduct (star z) (D⁻¹ *ᵥ z)).re := by
  rw [fixedCompressionRealMatrix_mulVec_reindexed]
  unfold reindexedComplexVectorRealification dotProduct
  calc
    (∑ i, complexVectorRealification z
        ((complexRealCoordinateEquivFin n).symm i) *
      complexVectorRealification (D⁻¹ *ᵥ z)
        ((complexRealCoordinateEquivFin n).symm i)) =
        ∑ i, complexVectorRealification z i *
          complexVectorRealification (D⁻¹ *ᵥ z) i :=
      (complexRealCoordinateEquivFin n).symm.sum_comp
        (fun i => complexVectorRealification z i *
          complexVectorRealification (D⁻¹ *ᵥ z) i)
    _ = _ := by
      simpa only [dotProduct, complexMatrixRealification_mulVec] using
        dotProduct_complexRealification_mulVec D⁻¹ z

/-- Reindexing preserves the squared Euclidean norm of a realified vector. -/
theorem sum_sq_reindexedComplexVectorRealification {n : ℕ} (z : Fin n → ℂ) :
    ∑ k : Fin (2 * n), reindexedComplexVectorRealification z k ^ 2 =
      ∑ j : Fin n, ‖z j‖ ^ 2 := by
  unfold reindexedComplexVectorRealification
  calc
    (∑ k, complexVectorRealification z
      ((complexRealCoordinateEquivFin n).symm k) ^ 2) =
        ∑ p, complexVectorRealification z p ^ 2 :=
      (complexRealCoordinateEquivFin n).symm.sum_comp
        (fun p => complexVectorRealification z p ^ 2)
    _ = _ := sum_sq_complexVectorRealification z

/-- The real quadratic form with the exact normalization produced by the
`√(2N)` first-row coordinates. -/
def normalizedCompressionRealMatrix (n : ℕ)
    (D : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  (1 / (2 * Real.sqrt (n + 1))) • fixedCompressionRealMatrix D

theorem normalizedCompressionRealMatrix_isSymm {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    (normalizedCompressionRealMatrix n D).IsSymm := by
  exact (fixedCompressionRealMatrix_isSymm D hD).smul _

theorem normalizedCompressionRealMatrix_ne_zero {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (hdet : D.det ≠ 0) :
    normalizedCompressionRealMatrix n D ≠ 0 := by
  apply smul_ne_zero
  · exact one_div_ne_zero (mul_ne_zero (by norm_num)
      (ne_of_gt (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < n + 1))))
  · exact fixedCompressionRealMatrix_ne_zero D hn hdet

/-- Exact quadratic scaling identity for a complex Schur column. -/
theorem normalizedCompression_dot_scaledRealification {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    dotProduct
        (Real.sqrt (2 * (n + 1)) • reindexedComplexVectorRealification z)
        (normalizedCompressionRealMatrix n D *ᵥ
          (Real.sqrt (2 * (n + 1)) • reindexedComplexVectorRealification z)) =
      Real.sqrt (n + 1) * (dotProduct (star z) (D⁻¹ *ᵥ z)).re := by
  let r := reindexedComplexVectorRealification z
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hsN : Real.sqrt (n + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  have hs2 : Real.sqrt (2 * (n + 1)) ^ 2 = 2 * (n + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [normalizedCompressionRealMatrix, Matrix.smul_mulVec,
    Matrix.mulVec_smul, smul_smul, dotProduct_comm, dotProduct_smul,
    dotProduct_comm, dotProduct_smul]
  rw [dotProduct_reindexedComplexRealification]
  simp only [smul_eq_mul]
  have hs1 : Real.sqrt (n + 1) ^ 2 = (n + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hcoef : Real.sqrt (2 * (n + 1)) *
      (1 / (2 * Real.sqrt (n + 1)) * Real.sqrt (2 * (n + 1))) =
      Real.sqrt (n + 1) := by
    field_simp
    nlinarith
  calc
    Real.sqrt (2 * (n + 1)) *
        (1 / (2 * Real.sqrt (n + 1)) * Real.sqrt (2 * (n + 1)) *
          (dotProduct (star z) (D⁻¹ *ᵥ z)).re) =
      (Real.sqrt (2 * (n + 1)) *
        (1 / (2 * Real.sqrt (n + 1)) * Real.sqrt (2 * (n + 1)))) *
          (dotProduct (star z) (D⁻¹ *ᵥ z)).re := by ring
    _ = _ := by rw [hcoef]

/-- Exact squared-norm scaling identity for the realified Schur numerator. -/
theorem normalizedCompression_norm_sq_scaledRealification {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    2 * ‖(WithLp.toLp 2
      (normalizedCompressionRealMatrix n D *ᵥ
        (Real.sqrt (2 * (n + 1)) • reindexedComplexVectorRealification z)) :
        EuclideanSpace ℝ (Fin (2 * n)))‖ ^ 2 =
      ∑ j : Fin n, ‖(D⁻¹ *ᵥ z) j‖ ^ 2 := by
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hsN : Real.sqrt (n + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  rw [EuclideanSpace.norm_sq_eq]
  change 2 * (∑ i, ‖(normalizedCompressionRealMatrix n D *ᵥ
    (Real.sqrt (2 * (n + 1)) • reindexedComplexVectorRealification z)) i‖ ^ 2) =
      ∑ j, ‖(D⁻¹ *ᵥ z) j‖ ^ 2
  rw [normalizedCompressionRealMatrix, Matrix.smul_mulVec,
    Matrix.mulVec_smul, smul_smul]
  simp_rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [← Finset.mul_sum]
  rw [fixedCompressionRealMatrix_mulVec_reindexed]
  have habssum :
      (∑ i, |reindexedComplexVectorRealification (D⁻¹ *ᵥ z) i| ^ 2) =
        ∑ i, reindexedComplexVectorRealification (D⁻¹ *ᵥ z) i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact sq_abs _
  rw [habssum]
  rw [sum_sq_reindexedComplexVectorRealification]
  have hs2 : Real.sqrt (2 * (n + 1)) ^ 2 = 2 * (n + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hs1 : Real.sqrt (n + 1) ^ 2 = (n + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have habs : |1 / (2 * Real.sqrt (n + 1)) * Real.sqrt (2 * (n + 1))| ^ 2 =
      1 / 2 := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
    nlinarith
  rw [habs]
  ring

/-- Deterministic final adapter from the exact Schur inequality to the enlarged
real event.  Its two equalities are the normalization identities proved above,
not probabilistic assumptions. -/
theorem enlargedRealSchurEvent_of_inverse_firstCoordinate {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian)
    (hD : (zerothBlockCompression H).det ≠ 0)
    (hs : schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
      (zerothBlockCompression H) ≠ 0)
    (c t g : ℝ) (b x : Fin (2 * n) → ℝ) (ht : 0 ≤ t)
    (hden : |g + c - dotProduct (x + b)
        (normalizedCompressionRealMatrix n (zerothBlockCompression H) *ᵥ (x + b))| =
      Real.sqrt (n + 1) *
        ‖schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
          (zerothBlockCompression H)‖)
    (hnum : 2 * ‖(WithLp.toLp 2
        (normalizedCompressionRealMatrix n (zerothBlockCompression H) *ᵥ (x + b)) :
          EuclideanSpace ℝ (Fin (2 * n)))‖ ^ 2 =
      ∑ j : Fin n,
        ‖((zerothBlockCompression H)⁻¹ *ᵥ zerothBlockColumn H) j‖ ^ 2)
    (hlarge : t * Real.sqrt (n + 1) ≤
      ‖(WithLp.toLp 2 (H⁻¹ *ᵥ phaseFixedCoordinateVector 0) :
        EuclideanSpace ℂ (Fin (n + 1)))‖) :
    enlargedRealSchurEvent
      (normalizedCompressionRealMatrix n (zerothBlockCompression H)) c b t (g, x) := by
  have h := inverse_firstCoordinate_implies_schur_event H hH hD hs t ht hlarge
  unfold enlargedRealSchurEvent
  rw [hden, hnum]
  simpa [mul_assoc] using h

/-- The scalar Schur denominator has exactly the normalization appearing in
`enlargedRealSchurEvent`. -/
theorem abs_realSchurDenominator_normalization {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian)
    (g c : ℝ) (y : Fin (2 * n) → ℝ)
    (hg : g + c = Real.sqrt (n + 1) * (zerothBlockScalar H).re)
    (hy : y = Real.sqrt (2 * (n + 1)) •
      reindexedComplexVectorRealification (zerothBlockColumn H)) :
    |g + c - dotProduct y
        (normalizedCompressionRealMatrix n (zerothBlockCompression H) *ᵥ y)| =
      Real.sqrt (n + 1) *
        ‖schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
          (zerothBlockCompression H)‖ := by
  let D := zerothBlockCompression H
  let z := zerothBlockColumn H
  let q := dotProduct (star z) (D⁻¹ *ᵥ z)
  have hR : (zerothBlockReindex H).IsHermitian := hH.submatrix (zerothSplitEquiv n)
  have hDherm : D.IsHermitian := by
    exact hR.submatrix Sum.inr
  have haim : (zerothBlockScalar H).im = 0 := by
    have ha := hR.coe_re_apply_self (Sum.inl ())
    exact congrArg Complex.im ha.symm
  have hqim : q.im = 0 := hDherm.inv.im_star_dotProduct_mulVec_self z
  have hqdot : dotProduct y (normalizedCompressionRealMatrix n D *ᵥ y) =
      Real.sqrt (n + 1) * q.re := by
    rw [hy]
    exact normalizedCompression_dot_scaledRealification D z
  have hsreal : ((zerothBlockScalar H).re - q.re : ℂ) =
      schurDenominator (zerothBlockScalar H) z D := by
    apply Complex.ext
    · simp [schurDenominator, q]
    · simp [schurDenominator, q, haim, hqim]
  have hsreal' : (((zerothBlockScalar H).re - q.re : ℝ) : ℂ) =
      schurDenominator (zerothBlockScalar H) z D := by
    simpa only [Complex.ofReal_sub] using hsreal
  rw [hqdot, hg]
  rw [← mul_sub]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  rw [hsreal']

/-- The standardized first *column* coordinates.  Imaginary coordinates acquire
the conjugation sign relative to `concreteStandardizedFirstRow`. -/
def concreteStandardizedFirstColumn (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) : ConcreteFirstRowCoordinate n → ℝ
  | .inl _ => concreteStandardizedFirstRow n x (.inl ())
  | .inr (j, q) =>
      if q = 0 then concreteStandardizedFirstRow n x (.inr (j, q))
      else -concreteStandardizedFirstRow n x (.inr (j, q))

/-- The standardized first column still has the independent standard-real
product law; the only change from the first row is Gaussian sign symmetry. -/
theorem hasLaw_concreteStandardizedFirstColumn (n : ℕ) :
    HasLaw (concreteStandardizedFirstColumn n)
      (Measure.pi fun _ : ConcreteFirstRowCoordinate n => gaussianReal 0 1)
      (hermitianGUECoordinateMeasure (n + 1)
        (canonicalGUEVariance (n + 1))
        (canonicalGUEVariance_nonneg (n + 1))) := by
  apply iIndepFun.hasLaw_pi
  · intro a
    rcases a with _ | ⟨j, q⟩
    · change HasLaw
        (fun x => standardizedGUECoordinates (n + 1) x
          (concreteFirstRowFinCoordinate n (.inl ())))
        (gaussianReal 0 1) _
      exact standardizedGUECoordinate_hasLaw (Nat.zero_lt_succ n)
        (concreteFirstRowFinCoordinate n (.inl ()))
    · fin_cases q
      · change HasLaw
          (fun x => standardizedGUECoordinates (n + 1) x
            (concreteFirstRowFinCoordinate n (.inr (j, 0))))
          (gaussianReal 0 1) _
        exact standardizedGUECoordinate_hasLaw (Nat.zero_lt_succ n)
          (concreteFirstRowFinCoordinate n (.inr (j, 0)))
      · change HasLaw
          (-(fun x => standardizedGUECoordinates (n + 1) x
            (concreteFirstRowFinCoordinate n (.inr (j, 1)))))
          (gaussianReal 0 1) _
        simpa only [neg_zero] using gaussianReal_neg
          (standardizedGUECoordinate_hasLaw (Nat.zero_lt_succ n)
            (concreteFirstRowFinCoordinate n (.inr (j, 1))))
  · have h := ((iIndepFun_hermitianGUECoordinates (n + 1)
      (canonicalGUEVariance (n + 1))
      (canonicalGUEVariance_nonneg (n + 1))).precomp
        (concreteFirstRowFinCoordinate_injective n)).comp
      (fun a x => match a with
        | .inl _ => standardizedGUECoordinateScale (n + 1)
            (concreteFirstRowFinCoordinate n a) * x
        | .inr (_, q) => if q = 0 then
            standardizedGUECoordinateScale (n + 1)
              (concreteFirstRowFinCoordinate n a) * x
          else -(standardizedGUECoordinateScale (n + 1)
            (concreteFirstRowFinCoordinate n a) * x))
      (fun a => by
        rcases a with _ | ⟨j, q⟩
        · fun_prop
        · fin_cases q
          · fun_prop
          · fun_prop)
    convert h using 1
    funext i x
    rcases i with _ | ⟨j, q⟩
    · rfl
    · fin_cases q <;> rfl

/-- Split a concrete column family into its diagonal scalar and canonically
reindexed real/imaginary tail. -/
def splitConcreteFirstColumn (n : ℕ)
    (u : ConcreteFirstRowCoordinate n → ℝ) : ℝ × (Fin (2 * n) → ℝ) :=
  (u (.inl ()), fun k => u (.inr ((complexRealCoordinateEquivFin n).symm k)))

/-- The deterministic split/reindex map preserves the standard product law. -/
theorem measurePreserving_splitConcreteFirstColumn (n : ℕ) :
    MeasurePreserving (splitConcreteFirstColumn n)
      (Measure.pi fun _ : ConcreteFirstRowCoordinate n => gaussianReal 0 1)
      ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1)) := by
  let s := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Unit ⊕ (Fin n × Fin 2) => ℝ)
  let e := complexRealCoordinateEquivFin n
  have hs := measurePreserving_concreteFirstRow_split n
  have hu := measurePreserving_eval (fun _ : Unit => gaussianReal 0 1) ()
  have he := measurePreserving_piCongrLeft
    (fun _ : Fin (2 * n) => gaussianReal 0 1) e
  have hp := hu.prod he
  have hc := hp.comp hs
  convert hc using 1
  funext u
  apply Prod.ext
  · rfl
  · funext k
    change u (.inr (e.symm k)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * n) => ℝ) e
        (fun p => u (.inr p))) k
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (2 * n) => ℝ) e
      (fun p => u (.inr p)) (e.symm k)
    simpa using h.symm

/-- The standardized first-column pair has the diagonal-plus-tail
standard Gaussian product law. -/
theorem hasLaw_standardizedFirstColumnPair (n : ℕ) :
    HasLaw (fun x => splitConcreteFirstColumn n
        (concreteStandardizedFirstColumn n x))
      ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1))
      (hermitianGUECoordinateMeasure (n + 1)
        (canonicalGUEVariance (n + 1))
        (canonicalGUEVariance_nonneg (n + 1))) :=
  (measurePreserving_splitConcreteFirstColumn n).hasLaw.comp
    (hasLaw_concreteStandardizedFirstColumn n)

/-- A concrete zeroth-row coordinate regarded as an element of the abstract
first-row restriction. -/
def concreteFirstRowSubtypeCoordinate (n : ℕ) (a : ConcreteFirstRowCoordinate n) :
    FirstRowGUECoordinate (n + 1) :=
  ⟨concreteFirstRowFinCoordinate n a, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold IsFirstRowGUECoordinate concreteFirstRowFinCoordinate
    rw [Equiv.symm_apply_apply]
    rcases a with _ | ⟨j, q⟩
    · rfl
    · fin_cases q <;> rfl⟩

/-- Standardize and conjugate the abstract first-row restriction into the
lower-column real coordinates. -/
def standardizedFirstColumnOfFirstRow (n : ℕ)
    (u : FirstRowGUECoordinate (n + 1) → ℝ) : ConcreteFirstRowCoordinate n → ℝ
  | .inl _ => standardizedGUECoordinateScale (n + 1)
      (concreteFirstRowFinCoordinate n (.inl ())) *
        u (concreteFirstRowSubtypeCoordinate n (.inl ()))
  | .inr (j, q) => if q = 0 then
      standardizedGUECoordinateScale (n + 1)
        (concreteFirstRowFinCoordinate n (.inr (j, q))) *
          u (concreteFirstRowSubtypeCoordinate n (.inr (j, q)))
    else -(standardizedGUECoordinateScale (n + 1)
      (concreteFirstRowFinCoordinate n (.inr (j, q))) *
        u (concreteFirstRowSubtypeCoordinate n (.inr (j, q))))

theorem measurable_standardizedFirstColumnOfFirstRow (n : ℕ) :
    Measurable (standardizedFirstColumnOfFirstRow n) := by
  rw [measurable_pi_iff]
  intro a
  rcases a with _ | ⟨j, q⟩
  · simp only [standardizedFirstColumnOfFirstRow]
    fun_prop
  · fin_cases q
    · simp only [standardizedFirstColumnOfFirstRow]
      fun_prop
    · simp only [standardizedFirstColumnOfFirstRow]
      fun_prop

theorem standardizedFirstColumnOfFirstRow_apply (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) :
    standardizedFirstColumnOfFirstRow n (firstRowGUECoordinates (n + 1) x) =
      concreteStandardizedFirstColumn n x := by
  funext a
  rcases a with _ | ⟨j, q⟩
  · rfl
  · fin_cases q <;> rfl

/-- Joint product law of the standardized lower first column and all
complementary coordinates. -/
theorem map_standardizedFirstColumnPair_compression_eq_prod (n : ℕ) :
    Measure.map
        (fun x : HermitianCoordinateSpace (n + 1) =>
          (splitConcreteFirstColumn n (concreteStandardizedFirstColumn n x),
            compressionGUECoordinates (n + 1) x))
        (hermitianGUECoordinateMeasure (n + 1)
          (canonicalGUEVariance (n + 1))
          (canonicalGUEVariance_nonneg (n + 1))) =
      ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1)).prod
        (Measure.map (compressionGUECoordinates (n + 1))
        (hermitianGUECoordinateMeasure (n + 1)
          (canonicalGUEVariance (n + 1))
          (canonicalGUEVariance_nonneg (n + 1)))) := by
  let P := hermitianGUECoordinateMeasure (n + 1)
    (canonicalGUEVariance (n + 1))
    (canonicalGUEVariance_nonneg (n + 1))
  let f := fun u => splitConcreteFirstColumn n
    (standardizedFirstColumnOfFirstRow n u)
  have hf : Measurable f := (measurePreserving_splitConcreteFirstColumn n).measurable.comp
    (measurable_standardizedFirstColumnOfFirstRow n)
  have hi0 := indepFun_firstRow_compression_GUECoordinates (n + 1)
    (canonicalGUEVariance (n + 1))
    (canonicalGUEVariance_nonneg (n + 1))
  have hi : IndepFun
      (fun x => f (firstRowGUECoordinates (n + 1) x))
      (compressionGUECoordinates (n + 1)) P := by
    have hi' : IndepFun
        (f ∘ firstRowGUECoordinates (n + 1))
        ((id : (CompressionGUECoordinate (n + 1) → ℝ) →
          (CompressionGUECoordinate (n + 1) → ℝ)) ∘
            compressionGUECoordinates (n + 1)) P :=
      hi0.comp (φ := f)
        (ψ := (id : (CompressionGUECoordinate (n + 1) → ℝ) →
          (CompressionGUECoordinate (n + 1) → ℝ))) hf measurable_id
    convert hi' using 1 <;> rfl
  have hprod := hi.map_prod_eq_prod_map_map
    (hf.comp (measurable_firstRowGUECoordinates (n + 1))).aemeasurable
    (measurable_compressionGUECoordinates (n + 1)).aemeasurable
  simp only [Function.comp_apply] at hprod
  have hfirst : Measure.map (fun x => f (firstRowGUECoordinates (n + 1) x)) P =
      (gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1) := by
    rw [show (fun x => f (firstRowGUECoordinates (n + 1) x)) =
        fun x => splitConcreteFirstColumn n
          (concreteStandardizedFirstColumn n x) by
      funext x
      exact congrArg (splitConcreteFirstColumn n)
        (standardizedFirstColumnOfFirstRow_apply n x)]
    exact (hasLaw_standardizedFirstColumnPair n).map_eq
  rw [show (f ∘ firstRowGUECoordinates (n + 1)) =
      fun x => f (firstRowGUECoordinates (n + 1) x) by rfl, hfirst] at hprod
  simpa only [P, f, id_eq, standardizedFirstColumnOfFirstRow_apply] using hprod

/-- The complementary coordinate reconstruction has exactly the same zeroth
principal compression as the original coordinate matrix. -/
theorem zerothBlockCompression_compressionGUEHermitian {n : ℕ}
    (x : HermitianCoordinateSpace (n + 1)) :
    zerothBlockCompression
        (compressionGUEHermitian (n + 1)
          (compressionGUECoordinates (n + 1) x)).1 =
      zerothBlockCompression (hermitianGUEBlock (n + 1) x).1 := by
  rw [zerothBlockCompression_eq_submatrix_succ,
    zerothBlockCompression_eq_submatrix_succ]
  have h := firstRowGUEHermitian_add_compressionGUEHermitian (n + 1) x
  ext i j
  have hij := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
    M i.succ j.succ) h
  have hzero : (firstRowGUEHermitian (n + 1)
      (firstRowGUECoordinates (n + 1) x)).1 i.succ j.succ = 0 := by
    simp [firstRowGUEHermitian, hermitianGUEBlock, hermitianOfFinCoordinates,
      hermitianOfCoordinates, hermitianMatrixOfCoordinates, hermitianUpperEntry,
      extendFirstRowGUECoordinates, IsFirstRowGUECoordinate]
  simpa [hzero] using hij

/-- Almost every complementary-coordinate reconstruction has invertible
shifted zeroth compression.  This is the coordinate-marginal form of the
proved determinant-null theorem. -/
theorem ae_compressionCoordinate_shifted_det_ne_zero {n : ℕ}
    (A : HermitianMatrix (Fin (n + 1))) :
    ∀ᵐ u ∂Measure.map (compressionGUECoordinates (n + 1))
        (hermitianGUECoordinateMeasure (n + 1)
          (canonicalGUEVariance (n + 1))
          (canonicalGUEVariance_nonneg (n + 1))),
      (zerothBlockCompression
        (A.1 + (compressionGUEHermitian (n + 1) u).1)).det ≠ 0 := by
  let P := hermitianGUECoordinateMeasure (n + 1)
    (canonicalGUEVariance (n + 1))
    (canonicalGUEVariance_nonneg (n + 1))
  let S : Set (CompressionGUECoordinate (n + 1) → ℝ) :=
    {u | (zerothBlockCompression
      (A.1 + (compressionGUEHermitian (n + 1) u).1)).det ≠ 0}
  have hS : MeasurableSet S := by
    unfold S
    let T : Set (HermitianMatrix (Fin (n + 1))) :=
      {H | (zerothBlockCompression (A.1 + H.1)).det ≠ 0}
    have hc : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
        (A.1 + H.1).submatrix Fin.succ Fin.succ :=
      continuous_const.add
        (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
    have hT : MeasurableSet T := by
      unfold T
      simp only [zerothBlockCompression_eq_submatrix_succ]
      exact ((measurableSet_singleton 0).preimage
        hc.matrix_det.measurable).compl
    exact hT.preimage (measurable_compressionGUEHermitian (n + 1))
  rw [ae_map_iff (measurable_compressionGUECoordinates (n + 1)).aemeasurable hS]
  have h := ae_canonicalGUEVariance_zerothBlockCompression_add_det_ne_zero n A.1 A.2
  have hT : MeasurableSet {H : HermitianMatrix (Fin (n + 1)) |
      (zerothBlockCompression (A.1 + H.1)).det ≠ 0} := by
    have hc : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
        (A.1 + H.1).submatrix Fin.succ Fin.succ :=
      continuous_const.add
        (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
    simp only [zerothBlockCompression_eq_submatrix_succ]
    exact ((measurableSet_singleton 0).preimage
      (hc.matrix_det.measurable)).compl
  rw [canonicalHermitianGUEPushforward,
    ae_map_iff (measurable_hermitianGUEBlock (n + 1)).aemeasurable hT] at h
  filter_upwards [h] with x hx
  have hcomp := zerothBlockCompression_compressionGUEHermitian x
  rw [zerothBlockCompression_eq_submatrix_succ, Matrix.submatrix_add] at hx ⊢
  simp only [Pi.add_apply] at hx ⊢
  rw [← zerothBlockCompression_eq_submatrix_succ
      (compressionGUEHermitian (n + 1)
        (compressionGUECoordinates (n + 1) x)).1]
  rw [← zerothBlockCompression_eq_submatrix_succ
      (hermitianGUEBlock (n + 1) x).1] at hx
  rw [hcomp]
  exact hx

/-- Measurability of the normalized real inverse-compression matrix along
a measurable complex matrix family. -/
theorem Measurable.normalizedCompressionRealMatrix {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} {D : Ω → Matrix (Fin n) (Fin n) ℂ}
    (hD : Measurable D) :
    Measurable (fun ω => normalizedCompressionRealMatrix n (D ω)) := by
  have hi := PSSSNative.BlockBand.Measurable.matrixNonsingInv hD
  rw [Matrix.measurable_iff] at hi ⊢
  intro i j
  unfold PSSSNative.BlockBand.PSSS.normalizedCompressionRealMatrix
    PSSSNative.BlockBand.PSSS.fixedCompressionRealMatrix
  let p := (complexRealCoordinateEquivFin n).symm i
  let q := (complexRealCoordinateEquivFin n).symm j
  change Measurable fun ω => (1 / (2 * Real.sqrt (n + 1))) *
    (if p.2 = 0 then
      if q.2 = 0 then ((D ω)⁻¹ p.1 q.1).re else -((D ω)⁻¹ p.1 q.1).im
    else if q.2 = 0 then ((D ω)⁻¹ p.1 q.1).im else ((D ω)⁻¹ p.1 q.1).re)
  split
  · split
    · exact measurable_const.mul (Complex.measurable_re.comp (hi _ _))
    · exact measurable_const.mul ((Complex.measurable_im.comp (hi _ _)).neg)
  · split
    · exact measurable_const.mul (Complex.measurable_im.comp (hi _ _))
    · exact measurable_const.mul (Complex.measurable_re.comp (hi _ _))

set_option maxHeartbeats 800000

/-- Tonelli assembly of the enlarged Schur estimate over the random
compression.  The exceptional singular compressions are removed only by the
proved determinant-null theorem. -/
theorem randomCompression_enlargedSchur_tail :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (n : ℕ), 0 < n → ∀ (A : HermitianMatrix (Fin (n + 1)))
      (c : ℝ) (b : Fin (2 * n) → ℝ) (t : ℝ), 1 ≤ t →
      let μ := (gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1)
      let ν := Measure.map (compressionGUECoordinates (n + 1))
        (hermitianGUECoordinateMeasure (n + 1)
          (canonicalGUEVariance (n + 1))
          (canonicalGUEVariance_nonneg (n + 1)))
      let D := fun u => zerothBlockCompression
        (A.1 + (compressionGUEHermitian (n + 1) u).1)
      μ.prod ν {z | enlargedRealSchurEvent
        (normalizedCompressionRealMatrix n (D z.2)) c b t z.1} ≤
        ENNReal.ofReal (K / t) := by
  obtain ⟨K, hK, htail⟩ := enlargedRealSchurEvent_conditional_tail
  refine ⟨K, hK, ?_⟩
  intro n hn A c b t ht μ ν D
  have hcD : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
      zerothBlockCompression (A.1 + H.1) := by
    rw [show (fun H : HermitianMatrix (Fin (n + 1)) =>
        zerothBlockCompression (A.1 + H.1)) =
      fun H => (A.1 + H.1).submatrix Fin.succ Fin.succ by
        funext H
        exact zerothBlockCompression_eq_submatrix_succ _]
    exact continuous_const.add
      (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
  have hmD : Measurable D := by
    unfold D
    exact hcD.measurable.comp (measurable_compressionGUEHermitian (n + 1))
  let Q := fun u => normalizedCompressionRealMatrix n (D u)
  have hmQ : Measurable Q :=
    PSSSNative.BlockBand.PSSS.Measurable.normalizedCompressionRealMatrix hmD
  let E : Set ((ℝ × (Fin (2 * n) → ℝ)) ×
      (CompressionGUECoordinate (n + 1) → ℝ)) :=
    {z | enlargedRealSchurEvent (Q z.2) c b t z.1}
  have hE : MeasurableSet E := by
    unfold E
    unfold enlargedRealSchurEvent
    let v := fun z : (ℝ × (Fin (2 * n) → ℝ)) ×
        (CompressionGUECoordinate (n + 1) → ℝ) => z.1.2 + b
    let w := fun z : (ℝ × (Fin (2 * n) → ℝ)) ×
        (CompressionGUECoordinate (n + 1) → ℝ) => Q z.2 *ᵥ v z
    have hv : Measurable v := by
      unfold v
      fun_prop
    have hw : Measurable w := by
      rw [measurable_pi_iff]
      intro i
      unfold w Matrix.mulVec dotProduct
      fun_prop
    have hdot : Measurable fun z => dotProduct (v z) (w z) := by
      unfold dotProduct
      fun_prop
    have hnorm : Measurable fun z =>
        ‖(WithLp.toLp 2 (w z) : EuclideanSpace ℝ (Fin (2 * n)))‖ := by
      fun_prop
    change MeasurableSet {z |
      (t * |z.1.1 + c - dotProduct (v z) (w z)|) ^ 2 ≤
        1 + 2 * ‖(WithLp.toLp 2 (w z) :
          EuclideanSpace ℝ (Fin (2 * n)))‖ ^ 2}
    apply measurableSet_le
    · fun_prop
    · fun_prop
  have hdet := ae_compressionCoordinate_shifted_det_ne_zero A
  rw [Measure.prod_apply_symm hE]
  calc
    (∫⁻ u, μ ((fun p => (p, u)) ⁻¹' E) ∂ν) ≤
        ∫⁻ _u, ENNReal.ofReal (K / t) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hdet] with u hu
      have hHerm : (D u).IsHermitian := by
        unfold D
        rw [zerothBlockCompression_eq_submatrix_succ]
        exact (A.2.add (compressionGUEHermitian (n + 1) u).2).submatrix Fin.succ
      have hQ := htail (2 * n) (normalizedCompressionRealMatrix n (D u))
        (normalizedCompressionRealMatrix_isSymm (D u) hHerm)
        (normalizedCompressionRealMatrix_ne_zero (D u) hn hu) c b t ht
      simpa only [E, Set.preimage_ofPred_eq] using hQ
    _ = ENNReal.ofReal (K / t) := by
      rw [lintegral_const]
      simp only [measure_univ, mul_one]

/-- Invertibility of the full Hermitian matrix and of its compression
forces nonvanishing of the scalar Schur denominator. -/
theorem schurDenominator_ne_zero_of_det_ne_zero {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian)
    (hD : (zerothBlockCompression H).det ≠ 0) (hdet : H.det ≠ 0) :
    schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
      (zerothBlockCompression H) ≠ 0 := by
  let D := zerothBlockCompression H
  let a := zerothBlockScalar H
  let b := zerothBlockColumn H
  have hDu : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  let _ : Invertible D := Matrix.invertibleOfIsUnitDet D hDu
  have hblock : (schurBlockMatrix a b D).det =
      D.det * (schurScalarMatrix a - schurRow b * ⅟D * schurColumn b).det :=
    Matrix.det_fromBlocks₂₂ _ _ _ _
  have hschur : schurScalarMatrix a - schurRow b * ⅟D * schurColumn b =
      schurScalarMatrix (schurDenominator a b D) := by
    ext i j
    cases i
    cases j
    change a - ((schurRow b * D⁻¹ * schurColumn b) () ()) =
      a - dotProduct (star b) (D⁻¹ *ᵥ b)
    congr 1
    change (schurRow b () ᵥ* D⁻¹) ⬝ᵥ b = (star b) ⬝ᵥ (D⁻¹ *ᵥ b)
    rw [Matrix.dotProduct_mulVec]
    rfl
  intro hs
  change schurDenominator a b D = 0 at hs
  have hz : (schurBlockMatrix a b D).det = 0 := by
    rw [hblock, hschur, hs]
    simp [schurScalarMatrix]
  have hreindex : (zerothBlockReindex H).det = H.det := by
    exact Matrix.det_reindex_self (zerothSplitEquiv n).symm H
  rw [zerothBlockReindex_eq_schurBlock H hH] at hreindex
  exact hdet (hreindex ▸ hz)

theorem zerothBlockScalar_eq_apply_zero {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    zerothBlockScalar H = H 0 0 := by
  unfold zerothBlockScalar zerothBlockReindex
  simp [Matrix.reindex_apply, zerothSplitEquiv]
  congr 2

theorem zerothBlockColumn_apply_eq_succ_zero {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin n) :
    zerothBlockColumn H j = H j.succ 0 := by
  unfold zerothBlockColumn zerothBlockReindex
  simp [Matrix.reindex_apply, zerothSplitEquiv]
  congr 1

/-- The split standardized lower column reads the exact scalar and complex
Schur-column normalizations from the reconstructed GUE matrix. -/
theorem splitConcreteFirstColumn_matrix_identities (n : ℕ)
    (x : HermitianCoordinateSpace (n + 1)) :
    let p := splitConcreteFirstColumn n (concreteStandardizedFirstColumn n x)
    let V := (hermitianGUEBlock (n + 1) x).1
    p.1 = Real.sqrt (n + 1) * (zerothBlockScalar V).re ∧
      p.2 = Real.sqrt (2 * (n + 1)) •
        reindexedComplexVectorRealification (zerothBlockColumn V) := by
  dsimp only
  constructor
  · simp [splitConcreteFirstColumn, concreteStandardizedFirstColumn,
      concreteStandardizedFirstRow_diagonal, zerothBlockScalar_eq_apply_zero,
      hermitianGUEBlock, hermitianOfFinCoordinates, hermitianOfCoordinates,
      hermitianMatrixOfCoordinates]
  · funext k
    let jq := (complexRealCoordinateEquivFin n).symm k
    have hk : complexRealCoordinateEquivFin n jq = k :=
      (complexRealCoordinateEquivFin n).apply_symm_apply k
    rw [← hk]
    rcases jq with ⟨j, q⟩
    fin_cases q
    · simp [splitConcreteFirstColumn, concreteStandardizedFirstColumn,
        concreteStandardizedFirstRow, standardizedGUECoordinates,
        standardizedGUECoordinateScale, concreteFirstRowFinCoordinate,
        concreteFirstRowHermitianCoordinate,
        reindexedComplexVectorRealification,
        complexVectorRealification, zerothBlockColumn_apply_eq_succ_zero,
        hermitianGUEBlock,
        hermitianOfFinCoordinates, hermitianOfCoordinates,
        hermitianMatrixOfCoordinates, hermitianUpperEntry,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    · simp [splitConcreteFirstColumn, concreteStandardizedFirstColumn,
        concreteStandardizedFirstRow, standardizedGUECoordinates,
        standardizedGUECoordinateScale, concreteFirstRowFinCoordinate,
        concreteFirstRowHermitianCoordinate,
        reindexedComplexVectorRealification,
        complexVectorRealification, zerothBlockColumn_apply_eq_succ_zero,
        hermitianGUEBlock,
        hermitianOfFinCoordinates, hermitianOfCoordinates,
        hermitianMatrixOfCoordinates, hermitianUpperEntry,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact deterministic identification of the random-compression coordinates
with the Schur data of the shifted matrix. -/
theorem canonicalCoordinate_schur_data {n : ℕ}
    (A : HermitianMatrix (Fin (n + 1)))
    (x : HermitianCoordinateSpace (n + 1)) :
    let V := (hermitianGUEBlock (n + 1) x).1
    let H := A.1 + V
    let p := splitConcreteFirstColumn n (concreteStandardizedFirstColumn n x)
    let u := compressionGUECoordinates (n + 1) x
    let D := zerothBlockCompression
      (A.1 + (compressionGUEHermitian (n + 1) u).1)
    let c := Real.sqrt (n + 1) * (zerothBlockScalar A.1).re
    let b := Real.sqrt (2 * (n + 1)) •
      reindexedComplexVectorRealification (zerothBlockColumn A.1)
    D = zerothBlockCompression H ∧
      p.1 + c = Real.sqrt (n + 1) * (zerothBlockScalar H).re ∧
      p.2 + b = Real.sqrt (2 * (n + 1)) •
        reindexedComplexVectorRealification (zerothBlockColumn H) := by
  dsimp only
  obtain ⟨hp0, hp1⟩ := splitConcreteFirstColumn_matrix_identities n x
  constructor
  · rw [zerothBlockCompression_eq_submatrix_succ,
      zerothBlockCompression_eq_submatrix_succ, Matrix.submatrix_add,
      Matrix.submatrix_add]
    simp only [Pi.add_apply]
    rw [← zerothBlockCompression_eq_submatrix_succ
        (compressionGUEHermitian (n + 1)
          (compressionGUECoordinates (n + 1) x)).1,
      zerothBlockCompression_compressionGUEHermitian x,
      zerothBlockCompression_eq_submatrix_succ]
  constructor
  · rw [hp0]
    simp only [zerothBlockScalar_eq_apply_zero, Matrix.add_apply,
      Complex.add_re]
    ring
  · rw [hp1]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      zerothBlockColumn_apply_eq_succ_zero, Matrix.add_apply,
      reindexedComplexVectorRealification, complexVectorRealification,
      Complex.add_re, Complex.add_im]
    split <;> ring

/-- Pointwise passage from the canonical inverse-vector event to the enlarged
real event on every nonsingular full matrix and compression. -/
theorem canonicalInverseEvent_implies_enlarged {n : ℕ}
    (A : HermitianMatrix (Fin (n + 1)))
    (x : HermitianCoordinateSpace (n + 1)) (t : ℝ) (ht : 0 ≤ t)
    (hD : (zerothBlockCompression
      (A.1 + (hermitianGUEBlock (n + 1) x).1)).det ≠ 0)
    (hfull : (A.1 + (hermitianGUEBlock (n + 1) x).1).det ≠ 0)
    (hlarge : t * Real.sqrt (n + 1) ≤
      ‖(WithLp.toLp 2 ((A.1 + (hermitianGUEBlock (n + 1) x).1)⁻¹ *ᵥ
        phaseFixedCoordinateVector 0) : EuclideanSpace ℂ (Fin (n + 1)))‖) :
    let p := splitConcreteFirstColumn n (concreteStandardizedFirstColumn n x)
    let u := compressionGUECoordinates (n + 1) x
    let D := zerothBlockCompression
      (A.1 + (compressionGUEHermitian (n + 1) u).1)
    let c := Real.sqrt (n + 1) * (zerothBlockScalar A.1).re
    let b := Real.sqrt (2 * (n + 1)) •
      reindexedComplexVectorRealification (zerothBlockColumn A.1)
    enlargedRealSchurEvent (normalizedCompressionRealMatrix n D) c b t p := by
  dsimp only
  let H := A.1 + (hermitianGUEBlock (n + 1) x).1
  let p := splitConcreteFirstColumn n (concreteStandardizedFirstColumn n x)
  let u := compressionGUECoordinates (n + 1) x
  let D := zerothBlockCompression
    (A.1 + (compressionGUEHermitian (n + 1) u).1)
  let c := Real.sqrt (n + 1) * (zerothBlockScalar A.1).re
  let b := Real.sqrt (2 * (n + 1)) •
    reindexedComplexVectorRealification (zerothBlockColumn A.1)
  obtain ⟨hDeq, hg, hy⟩ := canonicalCoordinate_schur_data A x
  have hH : H.IsHermitian := A.2.add (hermitianGUEBlock (n + 1) x).2
  have hs : schurDenominator (zerothBlockScalar H) (zerothBlockColumn H)
      (zerothBlockCompression H) ≠ 0 :=
    schurDenominator_ne_zero_of_det_ne_zero H hH hD hfull
  have hden := abs_realSchurDenominator_normalization H hH p.1 c
    (p.2 + b) hg hy
  have hnum := normalizedCompression_norm_sq_scaledRealification
    (zerothBlockCompression H) (zerothBlockColumn H)
  rw [← hy] at hnum
  rw [hDeq]
  exact enlargedRealSchurEvent_of_inverse_firstCoordinate H hH hD hs
    c t p.1 b p.2 ht hden hnum hlarge

set_option maxHeartbeats 800000

/-- **Canonical fixed-vector inverse tail, all positive dimensions.**  Source:
APSSS/PSSS fixed-vector estimate in the canonical `GUE_N(1/N)` normalization.
The constant precedes `N`, the deterministic deformation and `t`; the event is
`t√N ≤ ‖(A+V)⁻¹e₀‖`. -/
theorem canonicalGUE_fixedVector_inverse_tail :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (N : ℕ) (hN : 0 < N), ∀ (A : HermitianMatrix (Fin N))
      (t : ℝ), 1 ≤ t →
      canonicalHermitianGUEPushforward N (canonicalGUEVariance N)
        (canonicalGUEVariance_nonneg N)
        {V | t * Real.sqrt N ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ
            phaseFixedCoordinateVector ⟨0, hN⟩) :
              EuclideanSpace ℂ (Fin N))‖} ≤ ENNReal.ofReal (C / t) := by
  obtain ⟨K, hK, htail⟩ := randomCompression_enlargedSchur_tail
  refine ⟨K + 2, by linarith, ?_⟩
  intro N hN A t ht
  cases N with
  | zero => simp at hN
  | succ n =>
    by_cases hn : n = 0
    · subst n
      have h1 := canonicalGUE_one_fixedVector_inverse_tail A t ht
      have hconst : ENNReal.ofReal (2 / t) ≤
          ENNReal.ofReal ((K + 2) / t) := ENNReal.ofReal_le_ofReal (by
        have ht0 : 0 < t := by linarith
        apply (div_le_div_iff_of_pos_right ht0).2
        linarith)
      have hvec : phaseFixedCoordinateVector ⟨0, hN⟩ =
          canonicalUnitVectorOne := by
        funext i
        fin_cases i
        rfl
      simpa only [Nat.zero_add, Nat.cast_one, Real.sqrt_one, mul_one, hvec] using
        h1.trans hconst
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let P := hermitianGUECoordinateMeasure (n + 1)
        (canonicalGUEVariance (n + 1))
        (canonicalGUEVariance_nonneg (n + 1))
      let μ := (gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (2 * n) => gaussianReal 0 1)
      let ν := Measure.map (compressionGUECoordinates (n + 1)) P
      let F := fun x : HermitianCoordinateSpace (n + 1) =>
        (splitConcreteFirstColumn n (concreteStandardizedFirstColumn n x),
          compressionGUECoordinates (n + 1) x)
      let c := Real.sqrt (n + 1) * (zerothBlockScalar A.1).re
      let b := Real.sqrt (2 * (n + 1)) •
        reindexedComplexVectorRealification (zerothBlockColumn A.1)
      let D := fun u => zerothBlockCompression
        (A.1 + (compressionGUEHermitian (n + 1) u).1)
      have hcD : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
          zerothBlockCompression (A.1 + H.1) := by
        rw [show (fun H : HermitianMatrix (Fin (n + 1)) =>
            zerothBlockCompression (A.1 + H.1)) =
          fun H => (A.1 + H.1).submatrix Fin.succ Fin.succ by
            funext H
            exact zerothBlockCompression_eq_submatrix_succ _]
        exact continuous_const.add
          (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
      have hmD : Measurable D := hcD.measurable.comp
        (measurable_compressionGUEHermitian (n + 1))
      let Q := fun u => normalizedCompressionRealMatrix n (D u)
      have hmQ : Measurable Q :=
        PSSSNative.BlockBand.PSSS.Measurable.normalizedCompressionRealMatrix hmD
      let E : Set ((ℝ × (Fin (2 * n) → ℝ)) ×
          (CompressionGUECoordinate (n + 1) → ℝ)) :=
        {z | enlargedRealSchurEvent (Q z.2) c b t z.1}
      have hE : MeasurableSet E := by
        unfold E
        unfold enlargedRealSchurEvent
        let v := fun z : (ℝ × (Fin (2 * n) → ℝ)) ×
            (CompressionGUECoordinate (n + 1) → ℝ) => z.1.2 + b
        let w := fun z : (ℝ × (Fin (2 * n) → ℝ)) ×
            (CompressionGUECoordinate (n + 1) → ℝ) => Q z.2 *ᵥ v z
        have hv : Measurable v := by unfold v; fun_prop
        have hw : Measurable w := by
          rw [measurable_pi_iff]
          intro i
          unfold w Matrix.mulVec dotProduct
          fun_prop
        have hdot : Measurable fun z => dotProduct (v z) (w z) := by
          unfold dotProduct
          fun_prop
        have hnorm : Measurable fun z =>
            ‖(WithLp.toLp 2 (w z) : EuclideanSpace ℝ (Fin (2 * n)))‖ := by
          fun_prop
        change MeasurableSet {z |
          (t * |z.1.1 + c - dotProduct (v z) (w z)|) ^ 2 ≤
            1 + 2 * ‖(WithLp.toLp 2 (w z) :
              EuclideanSpace ℝ (Fin (2 * n)))‖ ^ 2}
        apply measurableSet_le <;> fun_prop
      let B : Set (HermitianMatrix (Fin (n + 1))) :=
        {V | t * Real.sqrt (n + 1) ≤
          ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ
            phaseFixedCoordinateVector ⟨0, hN⟩) :
            EuclideanSpace ℂ (Fin (n + 1)))‖}
      have hB : MeasurableSet B := by
        unfold B
        have hm : Measurable fun V : HermitianMatrix (Fin (n + 1)) =>
            (A.1 + V.1)⁻¹ :=
          PSSSNative.BlockBand.Measurable.matrixNonsingInv
            ((continuous_const.add continuous_subtype_val).measurable)
        have hv : Measurable fun V : HermitianMatrix (Fin (n + 1)) =>
            (A.1 + V.1)⁻¹ *ᵥ phaseFixedCoordinateVector 0 := by
          rw [measurable_pi_iff]
          intro i
          unfold Matrix.mulVec dotProduct
          fun_prop
        apply measurableSet_le
        · fun_prop
        · fun_prop
      have htvar : 0 < canonicalGUEVariance (n + 1) := by
        unfold canonicalGUEVariance
        positivity
      have hfull := ae_det_add_hermitianGUEBlock_ne_zero (n + 1)
        (t := canonicalGUEVariance (n + 1)) htvar A.1 A.2
      have hdetm := ae_compressionCoordinate_shifted_det_ne_zero A
      have hS : MeasurableSet {u : CompressionGUECoordinate (n + 1) → ℝ |
          (D u).det ≠ 0} := by
        let T : Set (HermitianMatrix (Fin (n + 1))) :=
          {H | (zerothBlockCompression (A.1 + H.1)).det ≠ 0}
        have hc : Continuous fun H : HermitianMatrix (Fin (n + 1)) =>
            (A.1 + H.1).submatrix Fin.succ Fin.succ :=
          continuous_const.add
            (continuous_subtype_val.matrix_submatrix Fin.succ Fin.succ)
        have hT : MeasurableSet T := by
          unfold T
          simp only [zerothBlockCompression_eq_submatrix_succ]
          exact ((measurableSet_singleton 0).preimage hc.matrix_det.measurable).compl
        exact hT.preimage (measurable_compressionGUEHermitian (n + 1))
      change ∀ᵐ u ∂ν, (D u).det ≠ 0 at hdetm
      rw [ae_map_iff (measurable_compressionGUECoordinates (n + 1)).aemeasurable hS] at hdetm
      have hsub : (hermitianGUEBlock (n + 1)) ⁻¹' B ≤ᵐ[P] F ⁻¹' E := by
        filter_upwards [hfull, hdetm] with x hxfull hxD hxB
        have hdata := canonicalCoordinate_schur_data A x
        have hDH : (zerothBlockCompression
            (A.1 + (hermitianGUEBlock (n + 1) x).1)).det ≠ 0 := by
          rw [← hdata.1]
          exact hxD
        exact canonicalInverseEvent_implies_enlarged A x t (by linarith)
          hDH hxfull hxB
      have hBtarget :
          {V : HermitianMatrix (Fin (n + 1)) |
            t * Real.sqrt ((n + 1 : ℕ) : ℝ) ≤
              ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ
                phaseFixedCoordinateVector ⟨0, hN⟩) :
                  EuclideanSpace ℂ (Fin (n + 1)))‖} = B := by
        unfold B
        simp only [Nat.cast_add, Nat.cast_one]
      rw [hBtarget]
      calc
        canonicalHermitianGUEPushforward (n + 1)
            (canonicalGUEVariance (n + 1))
            (canonicalGUEVariance_nonneg (n + 1)) B =
            P ((hermitianGUEBlock (n + 1)) ⁻¹' B) := by
          rw [canonicalHermitianGUEPushforward,
            Measure.map_apply (measurable_hermitianGUEBlock (n + 1)) hB]
        _ ≤ P (F ⁻¹' E) :=
          measure_mono_ae hsub
        _ = μ.prod ν E := by
          have hF : Measurable F := by
            unfold F
            exact (((measurePreserving_splitConcreteFirstColumn n).measurable.comp
              (measurable_standardizedFirstColumnOfFirstRow n)).comp
                (measurable_firstRowGUECoordinates (n + 1))).prodMk
              (measurable_compressionGUECoordinates (n + 1))
          rw [← Measure.map_apply hF hE]
          exact congrArg (fun M : Measure _ => M E)
            (map_standardizedFirstColumnPair_compression_eq_prod n)
        _ ≤ ENNReal.ofReal (K / t) := htail n hnpos A c b t ht
        _ ≤ ENNReal.ofReal ((K + 2) / t) := ENNReal.ofReal_le_ofReal (by
          have ht0 : 0 < t := by linarith
          apply (div_le_div_iff_of_pos_right ht0).2
          linarith)

set_option maxHeartbeats 200000

end PSSSNative.BlockBand.PSSS
