module

public import BlockBand.SourceProcess.Stochastic.Angular.Cross
public import BlockBand.SourceProcess.Stochastic.Angular.Laplacian

/-!
# Complex angular contract: unitary conjugation and the eigen-adapted basis

* `dysonEigenvalue_conj`, `dysonProjection_conj`: for a unitary `W`, the ordered eigenvalues of
  `W H W*` are those of `H` (equal characteristic polynomials and
  `sort_roots_charpoly_eq_eigenvalues₀`), and the Lagrange projections are conjugated.
* `phaseInv_of_proj`: a phase-invariant test sees any family `w` with `P_k = w_k w_k^*` as the
  canonical array.
* `eigMat`: the unitary of canonical eigenvectors, `vecHerm y = U diag(λ) U*`,
  `P_k = U E_kk U*`.
* `conjVec U M = hermVec (U M U*)` (a continuous `ℝ`-linear map) and
  `complete_conjVec`: the family `conjVec U E_x` is complete, `∑_x w_x ⊗ w_x = I`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Matrix Filter Topology
open scoped Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

/-!
### Unitary conjugation
-/

theorem eigenvalues₀_eq_of_charpoly {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  rw [← List.ofFn_inj, ← hA.sort_roots_charpoly_eq_eigenvalues₀,
    ← hB.sort_roots_charpoly_eq_eigenvalues₀, h]

theorem charpoly_conj {W : Matrix (Fin N) (Fin N) ℂ} (hW : star W * W = 1)
    (M : Matrix (Fin N) (Fin N) ℂ) : (W * M * star W).charpoly = M.charpoly := by
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]

/-- **Ordered eigenvalues are invariant under unitary conjugation.** -/
theorem dysonEigenvalue_conj {W : Matrix (Fin N) (Fin N) ℂ} (hW : star W * W = 1)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    dysonEigenvalue N (W * H * star W) = dysonEigenvalue N H := by
  have e : W * H * star W + (W * H * star W)ᴴ = W * (H + Hᴴ) * star W := by
    rw [conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star W), star_star,
      star_eq_conjTranspose W]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  funext i
  unfold dysonEigenvalue
  congr 1
  have h := eigenvalues₀_eq_of_charpoly (isHermitian_add_transpose_self (W * H * star W))
    (isHermitian_add_transpose_self H) (by rw [e, charpoly_conj hW])
  rw [h]

theorem hasSimpleSpectrum_conj {W : Matrix (Fin N) (Fin N) ℂ} (hW : star W * W = 1)
    {H : Matrix (Fin N) (Fin N) ℂ} (hs : HasSimpleSpectrum N H) :
    HasSimpleSpectrum N (W * H * star W) := by
  unfold HasSimpleSpectrum; rw [dysonEigenvalue_conj hW]; exact hs

/-- **Lagrange projections are conjugated.** -/
theorem dysonProjection_conj {W : Matrix (Fin N) (Fin N) ℂ} (hW : star W * W = 1)
    (hW' : W * star W = 1) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    dysonProjection N (W * H * star W) i = W * dysonProjection N H i * star W := by
  unfold dysonProjection
  rw [dysonEigenvalue_conj hW]
  have e : ∀ j : Fin N, ((dysonEigenvalue N H i - dysonEigenvalue N H j)⁻¹ : ℂ) •
      (W * H * star W - (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) =
      W * (((dysonEigenvalue N H i - dysonEigenvalue N H j)⁻¹ : ℂ) •
        (H - (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))) * star W := by
    intro j
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hW']
  simp_rw [e]
  exact conj_list_prod hW hW' _ _

/-!
### Phase identification
-/

/-- A phase-invariant test sees every family `w` with `P_k = w_k w_k^*` as the canonical array. -/
theorem phaseInv_of_proj {g : AngularArray N r → ℝ} (hg : IsPhaseInvariant g)
    (V : Matrix (Fin N) (Fin r) ℂ) {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (w : Fin N → Fin N → ℂ) (hw : ∀ k, proj N k y = vecMulVec (w k) (star (w k))) :
    g (arrZ V y) = g (angularArray V w) := by
  have hu : ∀ k, star (w k) ⬝ᵥ w k = 1 := fun k => by
    have h := trace_proj (vecHerm_isHermitian y) hy k
    change trace (proj N k y) = 1 at h
    rw [hw k, trace_vecMulVec, dotProduct_comm] at h
    exact h
  have key := fun k => eq_smul_of_vecMulVec_eq (hu k) (canon_unit hy k)
    ((hw k).symm.trans (proj_eq_canon hy k))
  have e : arrZ V y = fun k a => (star (w k) ⬝ᵥ canonEv N (vecHerm N y) k) *
      angularArray V w k a := by
    rw [← angularArray_smul, arrZ]
    congr 1; funext k; exact (key k).1
  rw [e, hg _ fun k => (key k).2]

/-!
### The eigenvector unitary
-/

/-- The unitary whose columns are the canonical eigenvectors. -/
def eigMat (N : ℕ) (y : Fin (N * N) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a k => canonEv N (vecHerm N y) k a

theorem eigMat_star_mul (y : Fin (N * N) → ℝ) : star (eigMat N y) * eigMat N y = 1 := by
  ext k l
  have h := congrFun (congrFun (specU_star_mul (vecHerm N y)) ((specPerm N).symm k))
    ((specPerm N).symm l)
  simp only [Matrix.mul_apply, Matrix.star_apply, eigMat, Matrix.of_apply, canonEv] at h ⊢
  rw [h, Matrix.one_apply, Matrix.one_apply]
  simp only [(specPerm N).symm.injective.eq_iff]

theorem eigMat_mul_star (y : Fin (N * N) → ℝ) : eigMat N y * star (eigMat N y) = 1 := by
  ext a b
  have h := congrFun (congrFun (specU_mul_star (vecHerm N y)) a) b
  simp only [Matrix.mul_apply, Matrix.star_apply, eigMat, Matrix.of_apply, canonEv] at h ⊢
  rw [← h]
  exact Equiv.sum_comp (specPerm N).symm
    (fun m => specU (vecHerm N y) a m * star (specU (vecHerm N y) b m))

/-- The diagonal matrix of eigenvalues. -/
def eigDiag (N : ℕ) (y : Fin (N * N) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun k => ((lam N k y : ℝ) : ℂ)

theorem eigDiag_conjTranspose (y : Fin (N * N) → ℝ) : star (eigDiag N y) = eigDiag N y := by
  rw [eigDiag, star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1; funext k; simp

/-- **Spectral decomposition** `vecHerm y = U diag(λ) U*`. -/
theorem vecHerm_eq_eig (y : Fin (N * N) → ℝ) :
    vecHerm N y = eigMat N y * eigDiag N y * star (eigMat N y) := by
  have h := spectral_eq (vecHerm_isHermitian y)
  ext a b
  have hab := congrFun (congrFun h a) b
  rw [hab]
  simp only [Matrix.mul_apply, Matrix.star_apply, eigMat, eigDiag, Matrix.of_apply, canonEv, lam,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => rw [← Equiv.sum_comp (specPerm N).symm]
  simp only [Equiv.apply_symm_apply]

/-- The outer product of a column: `M E_kk M* = m_k m_k^*`. -/
theorem mul_single_mul_star (M : Matrix (Fin N) (Fin N) ℂ) (k : Fin N) :
    M * single k k 1 * star M = vecMulVec (fun b => M b k) (star fun b => M b k) := by
  ext a b
  simp [Matrix.mul_apply, single_apply, vecMulVec_apply, Matrix.star_apply, ite_and, ite_mul]

theorem proj_eq_eig {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (k : Fin N) :
    proj N k y = eigMat N y * single k k 1 * star (eigMat N y) := by
  rw [mul_single_mul_star, proj_eq_canon hy k]; rfl

/-!
### The conjugated coordinates and completeness
-/

/-- `M ↦ hermVec (U M U*)` as a real-linear map. -/
def conjVecL (U : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] (Fin (N * N) → ℝ) where
  toFun M := hermVec N (U * M * star U)
  map_add' A B := by
    funext k
    simp [hermVec, hermCoord, Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    funext k
    simp [hermVec, hermCoord]

/-- `M ↦ hermVec (U M U*)` as a continuous real-linear map. -/
def conjVec (U : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℝ] (Fin (N * N) → ℝ) :=
  LinearMap.toContinuousLinearMap (conjVecL U)

theorem conjVec_apply (U M : Matrix (Fin N) (Fin N) ℂ) :
    conjVec U M = hermVec N (U * M * star U) := rfl

/-- `hermVec` is an isometry: `tr(vecHerm v · vecHerm w) = ⟨v, w⟩`. -/
theorem trace_vecHerm_mul (v w : Fin (N * N) → ℝ) :
    (trace (vecHerm N v * vecHerm N w)).re = ∑ k, v k * w k := by
  simp only [vecHerm, hermOfCoord, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, trace_sum, trace_smul, trace_hermBasis_mul_hermBasis, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Complex.re_sum]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  exact Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => mul_comm _ _)

theorem sum_hermVec_mul {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : ∑ k, hermVec N A k * hermVec N B k = (trace (A * B)).re := by
  rw [← trace_vecHerm_mul, vecHerm_hermVec hA, vecHerm_hermVec hB]

theorem isHermitian_conj (U : Matrix (Fin N) (Fin N) ℂ) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.IsHermitian) : (U * M * star U).IsHermitian := by
  rw [star_eq_conjTranspose]; exact isHermitian_mul_mul_conjTranspose U hM

/-- **Completeness of the conjugated basis**: `∑_x (w_x)_k (w_x)_l = δ_kl` for
`w_x = hermVec (U E_x U*)`, `U` unitary. -/
theorem complete_conjVec {U : Matrix (Fin N) (Fin N) ℂ} (hU : star U * U = 1) (k l : Fin (N * N)) :
    ∑ a, conjVec U (hermBasis (finProdFinEquiv.symm a)) k *
      conjVec U (hermBasis (finProdFinEquiv.symm a)) l = if k = l then 1 else 0 := by
  set O : Matrix (Fin (N * N)) (Fin (N * N)) ℝ :=
    Matrix.of fun k a => conjVec U (hermBasis (finProdFinEquiv.symm a)) k with hO
  have h1 : Oᵀ * O = 1 := by
    ext a b
    simp only [hO, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, conjVec_apply]
    rw [sum_hermVec_mul (isHermitian_conj U (hermBasis_isHermitian _))
      (isHermitian_conj U (hermBasis_isHermitian _))]
    have e : U * hermBasis (finProdFinEquiv.symm a) * star U *
        (U * hermBasis (finProdFinEquiv.symm b) * star U) =
        U * (hermBasis (finProdFinEquiv.symm a) * hermBasis (finProdFinEquiv.symm b)) *
          star U := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul]
    rw [e, trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
      trace_hermBasis_mul_hermBasis, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · have : finProdFinEquiv.symm a ≠ finProdFinEquiv.symm b := fun h =>
        hab (finProdFinEquiv.symm.injective h)
      simp only [this, hab, ↓reduceIte, Complex.zero_re]
  have h2 := congrArg (fun M => M k l) (mul_eq_one_comm.mp h1)
  simp only [hO, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.one_apply] at h2
  exact h2

end BlockBand.SourceProcess.Stochastic.ComplexAngular
