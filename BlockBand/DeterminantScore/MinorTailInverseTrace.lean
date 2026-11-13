module

public import BlockBand.Internal.Contracts.Inputs
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Codimension interlacing for `Tr B⁻²`

`card_window_le_trace`: for Hermitian `A` on `ι`, an isometry `V : κ → ι` (`V*V = 1`) with
invertible compression `B = V*AV`, and `a > 0`:
`N_A([-a, a]) - (|ι| - |κ|) ≤ a² Tr B⁻²` (counting with multiplicity, `Inputs.spectralSum`).

Proof (no min-max): the eigenvectors of `A` with `|λ| ≤ a` span `X` (`‖Ax‖ ≤ a‖x‖` on `X`),
`Y = range V`; `dim (X ∩ Y) ≥ N + |κ| - |ι|`. An orthonormal basis `y_j` of `X ∩ Y` pulls back
to an orthonormal family `z_j = V*y_j` with `‖Bz_j‖ ≤ ‖Ay_j‖ ≤ a`, so
`1 = ⟨B⁻¹z_j, Bz_j⟩ ≤ a‖B⁻¹z_j‖`; Bessel gives `Σ_j ‖B⁻¹z_j‖² ≤ ‖B⁻¹‖²_HS = Tr B⁻²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTailInverse

open Matrix Module WithLp
open scoped InnerProductSpace ComplexOrder

section Euclid

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

theorem toE_apply (M : Matrix ι κ ℂ) (x : EuclideanSpace ℂ κ) :
    T M x = toLp 2 (M *ᵥ ofLp x) := rfl

theorem toE_toE {α β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (M : Matrix α β ℂ) (N : Matrix β γ ℂ) (x : EuclideanSpace ℂ γ) :
    T M (T N x) = T (M * N) x := by
  simp only [toE_apply, mulVec_mulVec]

/-- Adjoint of a matrix map: `⟪M*x, y⟫ = ⟪x, My⟫`. -/
theorem inner_toE_conjTranspose (M : Matrix ι κ ℂ) (x : EuclideanSpace ℂ ι)
    (y : EuclideanSpace ℂ κ) : ⟪T Mᴴ x, y⟫_ℂ = ⟪x, T M y⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, toE_apply, star_mulVec,
    conjTranspose_conjTranspose]
  rw [dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]

theorem toE_isometry_left {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) (u : EuclideanSpace ℂ κ) :
    T Vᴴ (T V u) = u := by
  rw [toE_toE, hV]; simp

theorem toE_range {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) {y : EuclideanSpace ℂ ι}
    (hy : y ∈ LinearMap.range (T V)) : T V (T Vᴴ y) = y := by
  obtain ⟨u, rfl⟩ := hy
  rw [toE_isometry_left hV]

theorem inner_pull {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) (y : EuclideanSpace ℂ ι)
    {y' : EuclideanSpace ℂ ι} (hy' : y' ∈ LinearMap.range (T V)) :
    ⟪T Vᴴ y, T Vᴴ y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
  rw [inner_toE_conjTranspose, toE_range hV hy']

theorem norm_toE_isometry {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) (u : EuclideanSpace ℂ κ) :
    ‖T V u‖ = ‖u‖ := by
  have h : ⟪T V u, T V u⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [← inner_toE_conjTranspose, toE_isometry_left hV]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) u, h]

theorem norm_toE_conjTranspose_le {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1)
    (w : EuclideanSpace ℂ ι) : ‖T Vᴴ w‖ ≤ ‖w‖ := by
  have h1 : ‖T Vᴴ w‖ ^ 2 = RCLike.re ⟪w, T V (T Vᴴ w)⟫_ℂ := by
    rw [← inner_toE_conjTranspose, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  have h2 : RCLike.re ⟪w, T V (T Vᴴ w)⟫_ℂ ≤ ‖w‖ * ‖T Vᴴ w‖ := by
    have := re_inner_le_norm (𝕜 := ℂ) w (T V (T Vᴴ w))
    rwa [norm_toE_isometry hV] at this
  have h0 : 0 ≤ ‖T Vᴴ w‖ := norm_nonneg _
  have h0' : 0 ≤ ‖w‖ := norm_nonneg _
  nlinarith

/-- Eigenvectors of a Hermitian matrix, as Euclidean vectors. -/
theorem toE_eigenvectorBasis {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (j : ι) :
    T A (hA.eigenvectorBasis j) = ((hA.eigenvalues j : ℝ) : ℂ) • hA.eigenvectorBasis j := by
  rw [toE_apply]
  have h := hA.mulVec_eigenvectorBasis j
  apply ofLp_injective (p := 2)
  rw [ofLp_toLp, ofLp_smul]
  rw [h]
  ext k
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- On the span of the eigenvectors with `|λ| ≤ a`, `‖Ax‖ ≤ a‖x‖`. -/
theorem norm_toE_le_of_mem {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {a : ℝ} (ha : 0 ≤ a)
    {x : EuclideanSpace ℂ ι}
    (hx : x ∈ (Submodule.span ℂ (Set.range fun j : {j // ¬ |hA.eigenvalues j| ≤ a} =>
      hA.eigenvectorBasis j.1))ᗮ) :
    ‖T A x‖ ≤ a * ‖x‖ := by
  set b := hA.eigenvectorBasis
  have hsym : (T A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hterm : ∀ j, ‖⟪b j, T A x⟫_ℂ‖ ^ 2 ≤ a ^ 2 * ‖⟪b j, x⟫_ℂ‖ ^ 2 := by
    intro j
    rw [← hsym (b j) x, toE_eigenvectorBasis hA j, inner_smul_left, norm_mul, Complex.conj_ofReal,
      Complex.norm_real, Real.norm_eq_abs, mul_pow]
    by_cases hj : |hA.eigenvalues j| ≤ a
    · have : |hA.eigenvalues j| ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hj 2
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · have h0 : ⟪b j, x⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span
          (Set.mem_range_self (f := fun j : {j // ¬ |hA.eigenvalues j| ≤ a} => b j.1) ⟨j, hj⟩)) hx
      rw [show hA.eigenvectorBasis j = b j from rfl, h0]
      simp
  have hsq : ‖T A x‖ ^ 2 ≤ (a * ‖x‖) ^ 2 := by
    rw [← b.sum_sq_norm_inner_right, mul_pow, ← b.sum_sq_norm_inner_right, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hterm j
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Bessel for `‖R‖²_HS` of a Hermitian `R`: `Σ_j ‖Rz_j‖² ≤ Tr R²` for orthonormal `z_j`. -/
theorem sum_norm_sq_le_trace {m : ℕ} {R : Matrix κ κ ℂ} (hR : R.IsHermitian)
    {z : Fin m → EuclideanSpace ℂ κ} (hz : Orthonormal ℂ z) :
    ∑ j, ‖T R (z j)‖ ^ 2 ≤ (R * R).trace.re := by
  classical
  let c : κ → EuclideanSpace ℂ κ := fun l => toLp 2 (fun k => star (R l k))
  have hc : ∀ l j, (T R (z j)) l = ⟪c l, z j⟫_ℂ := by
    intro l j
    simp only [c, toE_apply, EuclideanSpace.inner_eq_star_dotProduct, PiLp.toLp_apply,
      mulVec, dotProduct, Pi.star_apply, star_star]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have htr : (R * R).trace.re = ∑ l, ‖c l‖ ^ 2 := by
    simp only [trace, diag, mul_apply, Complex.re_sum, EuclideanSpace.norm_sq_eq, c,
      norm_star]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← hR.apply l k, Complex.star_def, Complex.conj_mul', Complex.norm_conj]
    norm_cast
  rw [htr]
  calc ∑ j, ‖T R (z j)‖ ^ 2 = ∑ l, ∑ j, ‖⟪z j, c l⟫_ℂ‖ ^ 2 := by
        simp only [EuclideanSpace.norm_sq_eq, hc]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
        rw [norm_inner_symm]
    _ ≤ ∑ l, ‖c l‖ ^ 2 :=
        Finset.sum_le_sum fun l _ => Orthonormal.sum_inner_products_le (c l) hz

end Euclid

/-- `spectralSum` of the window indicator counts the eigenvalues in `[-a, a]`. -/
theorem spectralSum_window {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (a : ℝ) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A (fun l => if |l| ≤ a then 1 else 0) =
      ((Finset.univ.filter fun j => |hA.eigenvalues j| ≤ a).card : ℝ) := by
  unfold BlockBand.Internal.Contracts.Inputs.spectralSum
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_map_val]
  simp [Finset.sum_boole]

/-- **Codimension interlacing for `Tr B⁻²`.** For Hermitian `A` on `ι`, an isometry `V`
(`V*V = 1`) with invertible `B = V*AV` and `a > 0`: `N_A([-a,a]) - (|ι| - |κ|) ≤ a² Tr B⁻²`. -/
theorem card_window_le_trace {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1)
    (hB : (Vᴴ * A * V).det ≠ 0) {a : ℝ} (ha : 0 < a) :
    BlockBand.Internal.Contracts.Inputs.spectralSum A (fun l => if |l| ≤ a then 1 else 0) -
        ((Fintype.card ι : ℝ) - Fintype.card κ) ≤
      a ^ 2 * (((Vᴴ * A * V)⁻¹ * (Vᴴ * A * V)⁻¹).trace.re) := by
  classical
  set B := Vᴴ * A * V with hBdef
  set R := B⁻¹
  have hBH : B.IsHermitian := isHermitian_conjTranspose_mul_mul V hA
  have hRH : R.IsHermitian := hBH.inv
  have hRB : R * B = 1 := nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB)
  rw [spectralSum_window hA a]
  set N := (Finset.univ.filter fun j => |hA.eigenvalues j| ≤ a).card
  set b := hA.eigenvectorBasis
  let X : Submodule ℂ (EuclideanSpace ℂ ι) :=
    (Submodule.span ℂ (Set.range fun j : {j // ¬ |hA.eigenvalues j| ≤ a} => b j.1))ᗮ
  let Y : Submodule ℂ (EuclideanSpace ℂ ι) := LinearMap.range (Matrix.toEuclideanLin V)
  let S : Submodule ℂ (EuclideanSpace ℂ ι) := X ⊓ Y
  -- dimension count
  have hdim : N + Fintype.card κ ≤ finrank ℂ S + Fintype.card ι := by
    have h1 : finrank ℂ (Submodule.span ℂ
        (Set.range fun j : {j // ¬ |hA.eigenvalues j| ≤ a} => b j.1)) + finrank ℂ X =
        finrank ℂ (EuclideanSpace ℂ ι) := Submodule.finrank_add_finrank_orthogonal _
    have h2 := finrank_range_le_card (R := ℂ)
      (fun j : {j // ¬ |hA.eigenvalues j| ≤ a} => b j.1)
    unfold Set.finrank at h2
    have h3 : Fintype.card {j // ¬ |hA.eigenvalues j| ≤ a} + N = Fintype.card ι := by
      rw [Fintype.card_subtype, add_comm]
      exact Finset.card_filter_add_card_filter_not _
    have hinj : Function.Injective (Matrix.toEuclideanLin (𝕜 := ℂ) V) := by
      intro u u' h
      have := congrArg (Matrix.toEuclideanLin (𝕜 := ℂ) Vᴴ) h
      rwa [toE_isometry_left hV, toE_isometry_left hV] at this
    have h4 : finrank ℂ Y = Fintype.card κ := by
      rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace]
    have h5 := Submodule.finrank_sup_add_finrank_inf_eq X Y
    have h6 := Submodule.finrank_le (X ⊔ Y)
    rw [finrank_euclideanSpace] at h1 h6
    show N + Fintype.card κ ≤ finrank ℂ ↥(X ⊓ Y) + Fintype.card ι
    omega
  -- the orthonormal family
  let ob := stdOrthonormalBasis ℂ S
  let y : Fin (finrank ℂ S) → EuclideanSpace ℂ ι := fun j => (ob j : EuclideanSpace ℂ ι)
  let z : Fin (finrank ℂ S) → EuclideanSpace ℂ κ := fun j => Matrix.toEuclideanLin Vᴴ (y j)
  have hyX : ∀ j, y j ∈ X := fun j => (ob j).2.1
  have hyY : ∀ j, y j ∈ Y := fun j => (ob j).2.2
  have hyo : Orthonormal ℂ y := ob.orthonormal.comp_linearIsometry (Submodule.subtypeₗᵢ S)
  have hzo : Orthonormal ℂ z := by
    rw [orthonormal_iff_ite] at hyo ⊢
    intro j k
    rw [← hyo j k]
    exact inner_pull hV (y j) (hyY k)
  have key : ∀ j, 1 ≤ a ^ 2 * ‖Matrix.toEuclideanLin R (z j)‖ ^ 2 := by
    intro j
    have hz1 : ‖z j‖ = 1 := hzo.1 j
    have hAy : ‖Matrix.toEuclideanLin A (y j)‖ ≤ a := by
      have := norm_toE_le_of_mem hA ha.le (hyX j)
      rwa [hyo.1 j, mul_one] at this
    have hBz : Matrix.toEuclideanLin B (z j) =
        Matrix.toEuclideanLin Vᴴ (Matrix.toEuclideanLin A (y j)) := by
      have e : Matrix.toEuclideanLin B (z j) = Matrix.toEuclideanLin Vᴴ
          (Matrix.toEuclideanLin A (Matrix.toEuclideanLin V (Matrix.toEuclideanLin Vᴴ (y j)))) := by
        simp only [z, toE_toE, hBdef, Matrix.mul_assoc]
      rw [e, toE_range hV (hyY j)]
    have hBn : ‖Matrix.toEuclideanLin B (z j)‖ ≤ a :=
      hBz ▸ (norm_toE_conjTranspose_le hV _).trans hAy
    have hone : (1 : ℝ) = RCLike.re ⟪Matrix.toEuclideanLin R (z j),
        Matrix.toEuclideanLin B (z j)⟫_ℂ := by
      have e : ⟪Matrix.toEuclideanLin R (z j), Matrix.toEuclideanLin B (z j)⟫_ℂ = ⟪z j, z j⟫_ℂ := by
        conv_lhs => rw [← hRH.eq]
        rw [inner_toE_conjTranspose, toE_toE, hRB]
        simp
      rw [e, inner_self_eq_norm_sq (𝕜 := ℂ), hz1]; norm_num
    have hle : (1 : ℝ) ≤ ‖Matrix.toEuclideanLin R (z j)‖ * a := by
      rw [hone]
      exact (re_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hBn (norm_nonneg _))
    have h0 : 0 ≤ ‖Matrix.toEuclideanLin R (z j)‖ := norm_nonneg _
    nlinarith
  have hbes := sum_norm_sq_le_trace hRH hzo
  have hsum : (finrank ℂ S : ℝ) ≤ a ^ 2 * (R * R).trace.re := by
    calc (finrank ℂ S : ℝ) = ∑ _j : Fin (finrank ℂ S), (1 : ℝ) := by simp
      _ ≤ ∑ j, a ^ 2 * ‖Matrix.toEuclideanLin R (z j)‖ ^ 2 := Finset.sum_le_sum fun j _ => key j
      _ = a ^ 2 * ∑ j, ‖Matrix.toEuclideanLin R (z j)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ a ^ 2 * (R * R).trace.re := mul_le_mul_of_nonneg_left hbes (by positivity)
  have hdimR : (N : ℝ) + Fintype.card κ ≤ finrank ℂ S + Fintype.card ι := by exact_mod_cast hdim
  linarith

end BlockBand.DeterminantScore.MinorTailInverse
