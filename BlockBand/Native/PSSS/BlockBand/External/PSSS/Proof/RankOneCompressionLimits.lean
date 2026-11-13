module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.CompressionSpectrum
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RankOneInterlacing
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Analytic and trace lemmas for rank-one compression limits

For a Hermitian matrix `K` and a unit vector `u`, the top eigenvalue of `K + τ u u*` satisfies
`λ₁ - τ → ⟪K u, u⟫` as `τ → ∞`, with an explicit `O(1/τ)` error bound. The file also collects
trace identities for `K + τ u u*` and for the compression of `K` to `u⊥`, and expresses eigenvalue
counts through the decreasingly ordered eigenvalues.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Filter
open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

universe u

/-- Quantitative continuity of a quadratic form.  This is the norm estimate
used after splitting a vector into its `u` and `u⊥` components. -/
theorem abs_re_inner_apply_self_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (x z : E) :
    |RCLike.re (inner ℂ (T x) x) - RCLike.re (inner ℂ (T z) z)| ≤
      ‖T‖ * ‖x - z‖ * ‖x‖ + ‖T‖ * ‖z‖ * ‖x - z‖ := by
  calc
    |RCLike.re (inner ℂ (T x) x) - RCLike.re (inner ℂ (T z) z)| =
        |RCLike.re (inner ℂ (T x) x - inner ℂ (T z) z)| := by
          rw [map_sub]
    _ ≤ ‖inner ℂ (T x) x - inner ℂ (T z) z‖ := RCLike.abs_re_le_norm _
    _ = ‖inner ℂ (T (x - z)) x + inner ℂ (T z) (x - z)‖ := by
      congr 1
      simp only [map_sub, inner_sub_left, inner_sub_right]
      abel
    _ ≤ ‖inner ℂ (T (x - z)) x‖ + ‖inner ℂ (T z) (x - z)‖ :=
      norm_add_le _ _
    _ ≤ (‖T (x - z)‖ * ‖x‖) + (‖T z‖ * ‖x - z‖) := by
      exact add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖T‖ * ‖x - z‖ * ‖x‖ + ‖T‖ * ‖z‖ * ‖x - z‖ := by
      gcongr
      · exact T.le_opNorm (x - z)
      · exact T.le_opNorm z

/-- On the unit ball, the quadratic form of a bounded operator is
`2 ‖T‖`-Lipschitz. -/
theorem abs_re_inner_apply_self_sub_le_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) {x z : E} (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |RCLike.re (inner ℂ (T x) x) - RCLike.re (inner ℂ (T z) z)| ≤
      2 * ‖T‖ * ‖x - z‖ := by
  calc
    _ ≤ ‖T‖ * ‖x - z‖ * ‖x‖ + ‖T‖ * ‖z‖ * ‖x - z‖ :=
      abs_re_inner_apply_self_sub_le T x z
    _ ≤ ‖T‖ * ‖x - z‖ + ‖T‖ * ‖x - z‖ := by
      apply add_le_add
      · calc
          ‖T‖ * ‖x - z‖ * ‖x‖ ≤ ‖T‖ * ‖x - z‖ * 1 := by gcongr
          _ = ‖T‖ * ‖x - z‖ := by ring
      · calc
          ‖T‖ * ‖z‖ * ‖x - z‖ ≤ ‖T‖ * 1 * ‖x - z‖ := by gcongr
          _ = ‖T‖ * ‖x - z‖ := by ring
    _ = 2 * ‖T‖ * ‖x - z‖ := by ring

/-- Pythagoras for the decomposition of a unit vector into its component
along a fixed unit vector and its orthogonal remainder. -/
theorem norm_sub_inner_smul_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u x : E} (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) :
    ‖x - inner ℂ u x • u‖ ^ 2 = 1 - ‖inner ℂ u x‖ ^ 2 := by
  let c : ℂ := inner ℂ u x
  let y : E := x - c • u
  have hyorth : inner ℂ (c • u) y = 0 := by
    rw [inner_smul_left]
    apply mul_eq_zero_of_right
    change inner ℂ u (x - c • u) = 0
    rw [inner_sub_right, inner_smul_right, inner_self_eq_one_of_norm_eq_one hu]
    simp [c]
  have hxy : c • u + y = x := by simp [y]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (c • u) y hyorth
  rw [hxy, hx, norm_smul, hu] at hpy
  change ‖y‖ ^ 2 = 1 - ‖c‖ ^ 2
  nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖c‖]

/-- The component of a unit vector along another unit vector lies in the unit
ball. -/
theorem norm_inner_smul_unit_le_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u x : E} (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) :
    ‖inner ℂ u x • u‖ ≤ 1 := by
  rw [norm_smul, hu, mul_one]
  calc
    ‖inner ℂ u x‖ ≤ ‖u‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [hu, hx, one_mul]

/-- Quantitative Rayleigh penalty estimate.  Once `τ` exceeds the
absolute Rayleigh quotient of `T` at `u`, every unit vector pays a quadratic
penalty for its `u⊥` component; Young's inequality leaves the displayed
`O((τ-|q|)⁻¹)` error. -/
theorem re_inner_rankOne_ray_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) {u x : E} (hu : ‖u‖ = 1) (hx : ‖x‖ = 1)
    {τ : ℝ}
    (hτ : |RCLike.re (inner ℂ (T u) u)| < τ) :
    RCLike.re (inner ℂ
        ((T + (τ : ℂ) • (InnerProductSpace.rankOne ℂ u u)) x) x) - τ ≤
      RCLike.re (inner ℂ (T u) u) +
        ‖T‖ ^ 2 / (τ - |RCLike.re (inner ℂ (T u) u)|) := by
  let c : ℂ := inner ℂ u x
  let z : E := c • u
  let y : E := x - z
  let q : ℝ := RCLike.re (inner ℂ (T u) u)
  let d : ℝ := τ - |q|
  have hd : 0 < d := sub_pos.mpr hτ
  have hz : ‖z‖ ≤ 1 := by
    exact norm_inner_smul_unit_le_one hu hx
  have hr : ‖y‖ ^ 2 = 1 - ‖c‖ ^ 2 := by
    exact norm_sub_inner_smul_sq hu hx
  have hqz : RCLike.re (inner ℂ (T z) z) = ‖c‖ ^ 2 * q := by
    simp only [z, q, map_smul, inner_smul_left, inner_smul_right]
    rw [← mul_assoc, Complex.mul_conj']
    have hcast : (↑‖c‖ : ℂ) ^ 2 = (↑(‖c‖ ^ 2) : ℂ) := by norm_cast
    rw [hcast]
    change Complex.re ((↑(‖c‖ ^ 2) : ℂ) * inner ℂ (T u) u) = _
    rw [Complex.re_ofReal_mul]
    rfl
  have hqx : RCLike.re (inner ℂ (T x) x) -
      RCLike.re (inner ℂ (T z) z) ≤ 2 * ‖T‖ * ‖y‖ := by
    apply le_trans (le_abs_self _)
    simpa [y] using abs_re_inner_apply_self_sub_le_unit T hx.le hz
  have hyoung : 2 * ‖T‖ * ‖y‖ ≤ d * ‖y‖ ^ 2 + d⁻¹ * ‖T‖ ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (two_mul_le_add_mul_sq (a := ‖y‖) (b := ‖T‖) hd)
  have hrank : RCLike.re (inner ℂ
      (((τ : ℂ) • (InnerProductSpace.rankOne ℂ u u)) x) x) =
      τ * ‖c‖ ^ 2 := by
    rw [smul_apply, inner_smul_left]
    rw [InnerProductSpace.inner_left_rankOne_apply]
    rw [← inner_conj_symm x u]
    change RCLike.re ((starRingEnd ℂ) (τ : ℂ) *
      ((starRingEnd ℂ) c * c)) = _
    rw [Complex.conj_mul', Complex.conj_ofReal]
    have hcast : (↑‖c‖ : ℂ) ^ 2 = (↑(‖c‖ ^ 2) : ℂ) := by norm_cast
    rw [hcast]
    change Complex.re ((τ : ℂ) * (↑(‖c‖ ^ 2) : ℂ)) = _
    rw [Complex.re_ofReal_mul]
    norm_cast
  rw [add_apply, inner_add_left, map_add, hrank]
  change RCLike.re (inner ℂ (T x) x) + τ * ‖c‖ ^ 2 - τ ≤
    q + ‖T‖ ^ 2 / d
  rw [div_eq_inv_mul]
  have hqabs : -|q| ≤ q := neg_abs_le q
  calc
    RCLike.re (inner ℂ (T x) x) + τ * ‖c‖ ^ 2 - τ
        ≤ RCLike.re (inner ℂ (T z) z) + 2 * ‖T‖ * ‖y‖ +
          τ * ‖c‖ ^ 2 - τ := by linarith
    _ = q + 2 * ‖T‖ * ‖y‖ - (τ + q) * ‖y‖ ^ 2 := by
      rw [hqz, hr]
      ring
    _ ≤ q + 2 * ‖T‖ * ‖y‖ - d * ‖y‖ ^ 2 := by
      have hcoef : d ≤ τ + q := by
        dsimp only [d]
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)]
    _ ≤ q + d⁻¹ * ‖T‖ ^ 2 := by linarith

/-- A unit vector in a Euclidean coordinate space supplies an index. -/
theorem nonempty_of_euclidean_norm_eq_one {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) : Nonempty ι := by
  classical
  by_contra hι
  have : IsEmpty ι := not_nonempty_iff.mp hι
  have hz : u = 0 := Subsingleton.elim _ _
  rw [hz, norm_zero] at hu
  norm_num at hu

/-- Upper bound `λ₁(K + τ u u*) - τ ≤ ⟪K u, u⟫ + ‖K‖² / (τ - |⟪K u, u⟫|)` for the top eigenvalue,
once `τ > |⟪K u, u⟫|`. -/
theorem eigenvalues₀_zero_rankOneShift_sub_le {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : HermitianMatrix ι) {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1)
    {τ : ℝ}
    (hτ : |RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u)| < τ) :
    (rankOneShift K u τ).2.eigenvalues₀ (0 : Fin (Fintype.card ι)) - τ ≤
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u) +
        ‖(Matrix.toEuclideanLin K.1).toContinuousLinearMap‖ ^ 2 /
          (τ - |RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u)|) := by
  let A := rankOneShift K u τ
  let hA := Matrix.isSymmetric_toEuclideanLin_iff.mpr A.2
  let x : EuclideanSpace ℂ ι :=
    hA.eigenvectorBasis finrank_euclideanSpace (0 : Fin (Fintype.card ι))
  have hx : ‖x‖ = 1 := by
    exact (hA.eigenvectorBasis finrank_euclideanSpace).norm_eq_one
      (0 : Fin (Fintype.card ι))
  have heig := hA.apply_eigenvectorBasis finrank_euclideanSpace
    (0 : Fin (Fintype.card ι))
  have hray : RCLike.re (inner ℂ
      (Matrix.toEuclideanLin (A : Matrix ι ι ℂ) x) x) =
      hA.eigenvalues finrank_euclideanSpace (0 : Fin (Fintype.card ι)) := by
    rw [heig, inner_smul_left]
    rw [inner_self_eq_one_of_norm_eq_one hx]
    simp
  have hpen := re_inner_rankOne_ray_sub_le
    (Matrix.toEuclideanLin K.1).toContinuousLinearMap hu hx hτ
  change RCLike.re (inner ℂ
      ((Matrix.toEuclideanLin K.1 + (τ : ℂ) •
        (InnerProductSpace.rankOne ℂ u u : EuclideanSpace ℂ ι →ₗ[ℂ]
          EuclideanSpace ℂ ι)) x) x) - τ ≤
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u) +
        ‖(Matrix.toEuclideanLin K.1).toContinuousLinearMap‖ ^ 2 /
          (τ - |RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u)|) at hpen
  rw [← toEuclideanLin_rankOneShift K u τ] at hpen
  change RCLike.re (inner ℂ
      (Matrix.toEuclideanLin (A : Matrix ι ι ℂ) x) x) - τ ≤ _ at hpen
  rw [hray] at hpen
  simpa [A, hA, Matrix.IsHermitian.eigenvalues₀] using hpen

/-- The top eigenvalue satisfies `λ₁(K + τ u u*) - τ → ⟪K u, u⟫` as `τ → ∞`. -/
theorem eigenvalues₀_zero_rankOneShift_sub_tendsto {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : HermitianMatrix ι) {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1) :
    Tendsto (fun τ : ℝ =>
      (rankOneShift K u τ).2.eigenvalues₀
        (0 : Fin (Fintype.card ι)) - τ) atTop
      (𝓝 (RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u))) := by
  let q : ℝ := RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u)
  let M : ℝ := ‖(Matrix.toEuclideanLin K.1).toContinuousLinearMap‖
  have hden : Tendsto (fun τ : ℝ => τ - |q|) atTop atTop := by
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right atTop (-|q|) tendsto_id
  have herr : Tendsto (fun τ : ℝ => M ^ 2 / (τ - |q|)) atTop (𝓝 0) :=
    hden.const_div_atTop (M ^ 2)
  have hlo : ∀ τ : ℝ, q ≤
      (rankOneShift K u τ).2.eigenvalues₀
        (0 : Fin (Fintype.card ι)) - τ := by
    intro τ
    have h := re_inner_le_eigenvalues₀_zero (rankOneShift K u τ) hu
    rw [re_inner_rankOneShift_unit K hu τ] at h
    dsimp only [q]
    linarith
  have hup : ∀ᶠ τ : ℝ in atTop,
      (rankOneShift K u τ).2.eigenvalues₀
          (0 : Fin (Fintype.card ι)) - τ ≤
        q + M ^ 2 / (τ - |q|) := by
    filter_upwards [eventually_gt_atTop |q|] with τ hτ
    exact eigenvalues₀_zero_rankOneShift_sub_le K hu hτ
  have hupper : Tendsto (fun τ : ℝ => q + M ^ 2 / (τ - |q|))
      atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds (x := q)).add herr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper (Eventually.of_forall hlo) hup

/-- Eigenvalue counts can be read directly from the characteristic roots of
a Hermitian matrix. -/
theorem eigenCount_eq_roots_countP {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (s : Set ℝ) :
    eigenCount A s = Multiset.countP (fun z : ℂ => RCLike.re z ∈ s)
      A.1.charpoly.roots := by
  classical
  rw [A.2.roots_charpoly_eq_eigenvalues₀]
  simp only [Multiset.countP_map, Function.comp_apply, RCLike.ofReal_re]
  rw [eigenCount_def]
  change (Finset.univ.filter fun i => orderedEigenvalue A i ∈ s).card =
    (Finset.univ.filter fun i => A.2.eigenvalues₀ i ∈ s).card
  apply Finset.card_bij (fun i _ => i.rev)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [orderedEigenvalue] using (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Fin.rev_injective hij
  · intro j hj
    refine ⟨j.rev, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [orderedEigenvalue] using (Finset.mem_filter.mp hj).2

/-- The ambient orthogonal compression and its restriction to `u⊥` have
the same trace; the missing one-dimensional block is exactly zero. -/
theorem trace_orthogonalCompression_eq_trace_restriction {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin
          (orthogonalCompression K u : Matrix ι ι ℂ)) =
      (LinearMap.trace ℂ ((ℂ ∙ u)ᗮ)) (compressionRestriction K u hu) := by
  rw [orthogonalCompression_eq_conj_prodMap K u hu]
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap']
  simp

/-- The sum of the compression eigenvalues is the real trace of the
ambient orthogonal compression. -/
theorem sum_compression_eigenvalues_eq_re_trace {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (∑ k : Fin (Fintype.card ι - 1),
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k) =
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin
          (orthogonalCompression K u : Matrix ι ι ℂ))) := by
  rw [trace_orthogonalCompression_eq_trace_restriction K u hu]
  exact ((compressionRestriction_isSymmetric K u hu).re_trace_eq_sum_eigenvalues
    (finrank_spanOrthogonal_eq_card_sub_one u hu)).symm

/-- The real trace of a rank-one ray is affine in the ray parameter. -/
theorem re_trace_rankOneShift {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ) :
    RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
      (Matrix.toEuclideanLin (rankOneShift K u τ : Matrix ι ι ℂ))) =
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin K.1)) + τ * ‖u‖ ^ 2 := by
  rw [toEuclideanLin_rankOneShift, map_add, map_smul]
  rw [InnerProductSpace.trace_rankOne]
  change Complex.re (_ + (τ : ℂ) • inner ℂ u u) = _
  rw [Complex.add_re, inner_self_eq_norm_sq_to_K]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  norm_cast

/-- The sum of the decreasingly ordered eigenvalues of a rank-one shift is
its affine trace. -/
theorem sum_eigenvalues₀_rankOneShift {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ) :
    (∑ i : Fin (Fintype.card ι),
      (rankOneShift K u τ).2.eigenvalues₀ i) =
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin K.1)) + τ * ‖u‖ ^ 2 := by
  rw [← re_trace_rankOneShift K u τ]
  exact ((Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (rankOneShift K u τ).2).re_trace_eq_sum_eigenvalues
      finrank_euclideanSpace).symm

/-- Matrix eigenvalue counts may equivalently use the decreasing Hermitian
ordering. -/
theorem eigenCount_eq_finiteSpectralCount_eigenvalues₀ {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (s : Set ℝ) :
    eigenCount A s = finiteSpectralCount A.2.eigenvalues₀ s := by
  classical
  rw [eigenCount_def]
  unfold finiteSpectralCount
  apply Finset.card_bij (fun i _ => i.rev)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [orderedEigenvalue] using (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact Fin.rev_injective hij
  · intro j hj
    refine ⟨j.rev, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [orderedEigenvalue] using (Finset.mem_filter.mp hj).2

/-- If the top decreasing eigenvalue is outside a set, the matrix count is
the count of its remaining `n-1` branches. -/
theorem eigenCount_eq_finiteBranches_of_top_not_mem {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : HermitianMatrix ι) (s : Set ℝ)
    (htop : A.2.eigenvalues₀ (0 : Fin (Fintype.card ι)) ∉ s) :
    eigenCount A s = finiteSpectralCount
      (fun k : Fin (Fintype.card ι - 1) => A.2.eigenvalues₀ (finPredSucc k)) s := by
  rw [eigenCount_eq_finiteSpectralCount_eigenvalues₀]
  rw [finiteSpectralCount_eq_sum, finiteSpectralCount_eq_sum]
  have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
  have hn : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  let f : Fin ((Fintype.card ι - 1) + 1) → ℕ := fun i =>
    if A.2.eigenvalues₀ (Fin.cast hn.symm i) ∈ s then 1 else 0
  have hsplit := Fin.sum_univ_succ f
  have hfull : (∑ i, f i) =
      ∑ i : Fin (Fintype.card ι),
        if A.2.eigenvalues₀ i ∈ s then 1 else 0 := by
    exact Fin.sum_congr' (fun i : Fin (Fintype.card ι) =>
      if A.2.eigenvalues₀ i ∈ s then (1 : ℕ) else 0) hn.symm
  calc
    _ = ∑ i, f i := hfull.symm
    _ = f 0 + ∑ k : Fin (Fintype.card ι - 1), f k.succ := hsplit
    _ = ∑ k : Fin (Fintype.card ι - 1), f k.succ := by
      rw [show f 0 = 0 by simp [f, htop]]
      exact zero_add _
    _ = _ := by rfl

end PSSSNative.BlockBand.PSSS
