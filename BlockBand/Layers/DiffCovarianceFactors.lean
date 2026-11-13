module

public import BlockBand.Layers.TraceCovariance
public import BlockBand.Layers.GaussianAbsorption
public import BlockBand.Layers.BondMoments
public import BlockBand.Layers.ScalarRecursion

/-!
# Weighted factors of a source insertion

Step 4 of the proof of the differentiated-covariance lemma. Since `Ŝ` lives in the old-input
block and `S = K*YK`, `𝒢 Ŝ 𝒢 = (𝒢 𝒦*) Ŷ (𝒦 𝒢)`; by the weighted-layer lemma `K𝒢₁₁` and `𝒢₁₁K*`
have all fixed moments bounded, uniformly in the old path, and the port blocks of `𝒢` are
obtained from the top block by the block inverse equations, so the port factors also have bounded
moments.

Setting. One separate-port layer `layerLaw W b .separate` at `z = z_∂(E)`, `E ∈ bulkInterval κ`,
a deterministic Hermitian two-port `X`, `K = z - X`, `𝒢 = layerResolvent`. Norms: `ℓ²` operator
norm (`Matrix.Norms.L2Operator`); `dcvHS M = Σ |M_xy|²` is the squared Hilbert–Schmidt norm.

Contents.
1. Generic matrix facts (§1): Hilbert–Schmidt sums, `‖Y‖ ≤ Re Tr Y` and `Re Tr Y² ≤ (Re Tr Y)²`
   for `Y ⪰ 0`, the block embedding `dcvHat A = diag(A, 0)` with `‖dcvHat A‖ ≤ ‖A‖`, and the
   row/column block bounds `‖dcvHat K * G‖ ≤ ‖K G₁₁‖ + ‖K G₁₂‖`,
   `‖G * dcvHat K‖ ≤ ‖G₁₁ K‖ + ‖G₂₁ K‖`.
2. **Factorization** (§2): with `𝒦 = dcvHat K`, `Ŷ = dcvHat Y`, `S = K* Y K` gives
   `dcvHat S = 𝒦* Ŷ 𝒦`, hence `‖G Ŝ G‖ ≤ ‖Y‖ Θ(G)²` and `‖G Ŝ G‖²_HS ≤ ‖Y‖²_HS Θ(G)⁴` for
   **every** matrix `G`, where `Θ(G) = ‖G‖ + ‖G 𝒦*‖ + ‖𝒦 G‖` (`dcvTheta`).
3. **Regularization** (§3): for `G_κ = (N + c)⁻¹`, `G = N⁻¹`, `‖G_κ‖ ≤ |c|⁻¹`:
   `G_κ = G (1 - c G_κ) = (1 - c G_κ) G`, so `Θ(G_κ) ≤ 2 Θ(G)`.
4. **Moments** (§4): `‖Θ(𝒢)‖_{L^q} ≤ C_q` uniformly in Hermitian `X` and `E ∈ bulkInterval κ`,
   `W ≥ W₀(q)` (`dcv_theta_eLpNorm`), from `WeightedLayerContract.moments`
   (`K𝒢₁₁`, `𝒢₁₁K*`, `K𝒢₁₂`), the block inverse equation `𝒢₂₁ = -z⁻¹ B* 𝒢₁₁` (a.s.), the bond
   moments `bond_eLpNorm_le` and the Gaussian absorption lemma (`gaussianAbsorption_holds`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Generic matrix facts
-/

section Generic

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m]
  [DecidableEq n]

/-- The squared Hilbert–Schmidt norm `Σ |M_xy|²`. -/
def dcvHS (M : Matrix m n ℂ) : ℝ := ∑ x, ∑ y, ‖M x y‖ ^ 2

theorem dcvHS_nonneg (M : Matrix m n ℂ) : 0 ≤ dcvHS M := by unfold dcvHS; positivity

theorem dcvHS_conjTranspose (M : Matrix m n ℂ) : dcvHS Mᴴ = dcvHS M := by
  unfold dcvHS
  rw [Finset.sum_comm]
  simp [conjTranspose_apply]

theorem dcv_col_le (A : Matrix m n ℂ) (v : n → ℂ) :
    ∑ x, ‖(A *ᵥ v) x‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ y, ‖v y‖ ^ 2 := by
  have h := norm_toLp_mulVec_le A v
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

/-- `‖A B‖²_HS ≤ ‖A‖² ‖B‖²_HS`. -/
theorem dcvHS_mul_left_le (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    dcvHS (A * B) ≤ ‖A‖ ^ 2 * dcvHS B := by
  unfold dcvHS
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => ‖B x y‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := dcv_col_le A (fun k => B k y)
  convert h using 2
  rfl

/-- `‖B C‖²_HS ≤ ‖B‖²_HS ‖C‖²`. -/
theorem dcvHS_mul_right_le (B : Matrix l m ℂ) (C : Matrix m n ℂ) :
    dcvHS (B * C) ≤ dcvHS B * ‖C‖ ^ 2 := by
  rw [← dcvHS_conjTranspose, conjTranspose_mul, ← dcvHS_conjTranspose B]
  have := dcvHS_mul_left_le Cᴴ Bᴴ
  rw [l2_opNorm_conjTranspose] at this
  linarith

/-- `‖A + B‖²_HS ≤ 2 ‖A‖²_HS + 2 ‖B‖²_HS`. -/
theorem dcvHS_add_le (A B : Matrix m n ℂ) : dcvHS (A + B) ≤ 2 * dcvHS A + 2 * dcvHS B := by
  unfold dcvHS
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Matrix.add_apply]
  have h := norm_add_le (A x y) (B x y)
  have ha := norm_nonneg (A x y)
  have hb := norm_nonneg (B x y)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖A x y‖ - ‖B x y‖)]

/-- `Tr(M* M) = ‖M‖²_HS`. -/
theorem dcv_trace_conjTranspose_mul_self (M : Matrix m n ℂ) :
    (Mᴴ * M).trace = (dcvHS M : ℂ) := by
  unfold dcvHS
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- `‖A‖² ≤ ‖A‖²_HS`. -/
theorem dcv_opNorm_sq_le_hs (A : Matrix m n ℂ) : ‖A‖ ^ 2 ≤ dcvHS A := by
  have hb : ‖A‖ ≤ Real.sqrt (dcvHS A) := by
    rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    change ‖toEuclideanLin A v‖ ≤ _
    have hsq : ‖toEuclideanLin A v‖ ^ 2 ≤ dcvHS A * ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [toLpLin_apply, PiLp.toLp_apply]
      unfold dcvHS
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Matrix.mulVec, dotProduct]
      refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => ‖A x y‖)
        (fun y => ‖(WithLp.ofLp v) y‖)
      simpa only [norm_mul] using hcs
    have h2 : Real.sqrt (‖toEuclideanLin A v‖ ^ 2) ≤ Real.sqrt (dcvHS A * ‖v‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (dcvHS_nonneg A),
      Real.sqrt_sq (norm_nonneg _)] at h2
  calc ‖A‖ ^ 2 ≤ Real.sqrt (dcvHS A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = dcvHS A := Real.sq_sqrt (dcvHS_nonneg A)

/-- `‖A‖²_HS ≤ |n| ‖A‖²` for a square matrix. -/
theorem dcvHS_le_card (A : Matrix n n ℂ) : dcvHS A ≤ Fintype.card n * ‖A‖ ^ 2 :=
  tfl_hs_le A

open scoped MatrixOrder in
/-- A positive semidefinite matrix is a Gram matrix `B* B`. -/
theorem dcv_psd_eq {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : ∃ B : Matrix n n ℂ, Y = Bᴴ * B := by
  obtain ⟨X, hX, -, hXX⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hY.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hY.nonneg)
  refine ⟨X, ?_⟩
  have : Xᴴ = X := hX.star_eq
  rw [this]; exact hXX.symm

/-- `‖Y‖ ≤ Re Tr Y` for `Y ⪰ 0` (in the paper: `‖Y‖ ≤ Tr Y`). -/
theorem dcv_norm_le_trace {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : ‖Y‖ ≤ Y.trace.re := by
  obtain ⟨B, rfl⟩ := dcv_psd_eq hY
  rw [l2_opNorm_conjTranspose_mul_self, dcv_trace_conjTranspose_mul_self, Complex.ofReal_re]
  have := dcv_opNorm_sq_le_hs B
  nlinarith

/-- `‖Y‖²_HS = Re Tr Y²` and `0 ≤ Re Tr Y² ≤ (Re Tr Y)²` for `Y ⪰ 0`. -/
theorem dcv_hs_psd {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    dcvHS Y = (Y * Y).trace.re ∧ (Y * Y).trace.re ≤ Y.trace.re ^ 2 := by
  have hH : Yᴴ = Y := hY.isHermitian
  have e0 : dcvHS Y = (Y * Y).trace.re := by
    have := dcv_trace_conjTranspose_mul_self Y
    rw [hH] at this
    rw [this, Complex.ofReal_re]
  refine ⟨e0, ?_⟩
  rw [← e0]
  obtain ⟨B, rfl⟩ := dcv_psd_eq hY
  rw [dcv_trace_conjTranspose_mul_self, Complex.ofReal_re]
  have h1 := dcvHS_mul_left_le Bᴴ B
  have h2 := dcv_opNorm_sq_le_hs B
  rw [l2_opNorm_conjTranspose] at h1
  have hB := dcvHS_nonneg B
  nlinarith

/-- `‖1‖ ≤ 1`. -/
theorem dcv_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal]
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun _ => by simp

/-- The coordinate inclusion matrix of a map. -/
def dcvIncl {ι κ : Type*} (f : ι → κ) [DecidableEq κ] : Matrix ι κ ℂ :=
  Matrix.of fun x y => if y = f x then 1 else 0

theorem dcv_norm_incl_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {f : ι → κ} (hf : Function.Injective f) : ‖dcvIncl f‖ ≤ 1 := by
  have hJJ : dcvIncl f * (dcvIncl f)ᴴ = 1 := by
    ext x y
    simp only [Matrix.mul_apply, conjTranspose_apply, dcvIncl, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (f x)]
    · by_cases h : x = y
      · subst h; simp
      · have : f x ≠ f y := fun h' => h (hf h')
        simp [h, this]
    · intro c _ hc; simp [hc]
    · simp
  have h1 : ‖(dcvIncl f)ᴴ‖ * ‖(dcvIncl f)ᴴ‖ = ‖((dcvIncl f)ᴴ)ᴴ * (dcvIncl f)ᴴ‖ :=
    (l2_opNorm_conjTranspose_mul_self _).symm
  rw [conjTranspose_conjTranspose, hJJ, l2_opNorm_conjTranspose] at h1
  have h2 := dcv_norm_one_le (n := ι)
  have h0 := norm_nonneg (dcvIncl f)
  nlinarith

/-- `‖ι_f* A ι_g‖ ≤ ‖A‖` for injective `f, g`. -/
theorem dcv_norm_sandwich_le {ι ι' κ κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (A : Matrix ι ι' ℂ) {f : ι → κ} {g : ι' → κ'} (hf : Function.Injective f)
    (hg : Function.Injective g) : ‖(dcvIncl f)ᴴ * A * dcvIncl g‖ ≤ ‖A‖ := by
  calc ‖(dcvIncl f)ᴴ * A * dcvIncl g‖ ≤ ‖(dcvIncl f)ᴴ‖ * ‖A‖ * ‖dcvIncl g‖ :=
        (l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖A‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (dcv_norm_incl_le hf) (norm_nonneg _))
          (dcv_norm_incl_le hg) (norm_nonneg _) (by positivity)
    _ = ‖A‖ := by ring

theorem dcv_fromBlocks11_eq (A : Matrix n n ℂ) :
    (fromBlocks A 0 0 0 : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      (dcvIncl (Sum.inl : n → n ⊕ m))ᴴ * A * dcvIncl (Sum.inl : n → n ⊕ m) := by
  ext (x | x) (y | y) <;>
    simp [fromBlocks, dcvIncl, Matrix.mul_apply, conjTranspose_apply]

theorem dcv_fromBlocks12_eq (B : Matrix n m ℂ) :
    (fromBlocks 0 B 0 0 : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      (dcvIncl (Sum.inl : n → n ⊕ m))ᴴ * B * dcvIncl (Sum.inr : m → n ⊕ m) := by
  ext (x | x) (y | y) <;>
    simp [fromBlocks, dcvIncl, Matrix.mul_apply, conjTranspose_apply]

theorem dcv_fromBlocks21_eq (C : Matrix m n ℂ) :
    (fromBlocks 0 0 C 0 : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      (dcvIncl (Sum.inr : m → n ⊕ m))ᴴ * C * dcvIncl (Sum.inl : n → n ⊕ m) := by
  ext (x | x) (y | y) <;>
    simp [fromBlocks, dcvIncl, Matrix.mul_apply, conjTranspose_apply]

/-- The block embedding `Â = diag(A, 0)` of an old-input matrix into the augmented layer. -/
def dcvHat (A : Matrix n n ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks A 0 0 0

theorem dcv_norm_hat_le (A : Matrix n n ℂ) : ‖(dcvHat A : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖ ≤ ‖A‖ := by
  rw [dcvHat, dcv_fromBlocks11_eq]
  exact dcv_norm_sandwich_le A Sum.inl_injective Sum.inl_injective

theorem dcvHat_mul (A B : Matrix n n ℂ) :
    (dcvHat A : Matrix (n ⊕ m) (n ⊕ m) ℂ) * dcvHat B = dcvHat (A * B) := by
  rw [dcvHat, dcvHat, dcvHat, fromBlocks_multiply]; simp

theorem dcvHat_conjTranspose (A : Matrix n n ℂ) :
    (dcvHat A : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ = dcvHat Aᴴ := by
  rw [dcvHat, dcvHat, fromBlocks_conjTranspose]; simp

theorem dcvHS_hat (A : Matrix n n ℂ) : dcvHS (dcvHat A : Matrix (n ⊕ m) (n ⊕ m) ℂ) = dcvHS A := by
  unfold dcvHS dcvHat
  simp [Fintype.sum_sum_type, fromBlocks]

/-- The weighted row: `‖𝒦 G‖ ≤ ‖K G₁₁‖ + ‖K G₁₂‖`. -/
theorem dcv_hat_mul_le (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    ‖dcvHat K * G‖ ≤ ‖K * G.toBlocks₁₁‖ + ‖K * G.toBlocks₁₂‖ := by
  have e : dcvHat K * G = fromBlocks (K * G.toBlocks₁₁) 0 0 0 + fromBlocks 0 (K * G.toBlocks₁₂) 0 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [dcvHat, fromBlocks_multiply, fromBlocks_add]
    simp
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [dcv_fromBlocks11_eq]
    exact dcv_norm_sandwich_le _ Sum.inl_injective Sum.inl_injective
  · rw [dcv_fromBlocks12_eq]
    exact dcv_norm_sandwich_le _ Sum.inl_injective Sum.inr_injective

/-- The weighted column: `‖G 𝒦‖ ≤ ‖G₁₁ K‖ + ‖G₂₁ K‖`. -/
theorem dcv_mul_hat_le (K : Matrix n n ℂ) (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    ‖G * dcvHat K‖ ≤ ‖G.toBlocks₁₁ * K‖ + ‖G.toBlocks₂₁ * K‖ := by
  have e : G * dcvHat K = fromBlocks (G.toBlocks₁₁ * K) 0 0 0 + fromBlocks 0 0 (G.toBlocks₂₁ * K) 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [dcvHat, fromBlocks_multiply, fromBlocks_add]
    simp
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [dcv_fromBlocks11_eq]
    exact dcv_norm_sandwich_le _ Sum.inl_injective Sum.inl_injective
  · rw [dcv_fromBlocks21_eq]
    exact dcv_norm_sandwich_le _ Sum.inr_injective Sum.inl_injective

end Generic

/-!
## 2. The factorization `𝒢 Ŝ 𝒢 = (𝒢 𝒦*) Ŷ (𝒦 𝒢)` (the covariance factorization)
-/

section Factor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted size `Θ(G) = ‖G‖ + ‖G 𝒦*‖ + ‖𝒦 G‖` of a resolvent `G` for the weight `𝒦`. -/
def dcvTheta (Kh G : Matrix ι ι ℂ) : ℝ := ‖G‖ + ‖G * Khᴴ‖ + ‖Kh * G‖

theorem dcvTheta_nonneg (Kh G : Matrix ι ι ℂ) : 0 ≤ dcvTheta Kh G := by
  unfold dcvTheta; positivity

theorem dcv_norm_le_theta (Kh G : Matrix ι ι ℂ) : ‖G‖ ≤ dcvTheta Kh G := by
  unfold dcvTheta; linarith [norm_nonneg (G * Khᴴ), norm_nonneg (Kh * G)]

theorem dcv_continuous_theta (Kh : Matrix ι ι ℂ) : Continuous (dcvTheta Kh) := by
  unfold dcvTheta
  exact (continuous_norm.add (continuous_id.mul continuous_const).norm).add
    (continuous_const.mul continuous_id).norm

/-- **Factorization bound** (the covariance factorization): for every `G`,
`‖G (𝒦* Ŷ 𝒦) G‖ ≤ ‖Ŷ‖ Θ(G)²`. -/
theorem dcv_factor_le (Kh Yh G : Matrix ι ι ℂ) :
    ‖G * (Khᴴ * Yh * Kh) * G‖ ≤ ‖Yh‖ * dcvTheta Kh G ^ 2 := by
  have e : G * (Khᴴ * Yh * Kh) * G = (G * Khᴴ) * Yh * (Kh * G) := by
    simp only [Matrix.mul_assoc]
  rw [e]
  have h1 : ‖(G * Khᴴ) * Yh * (Kh * G)‖ ≤ ‖G * Khᴴ‖ * ‖Yh‖ * ‖Kh * G‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hT := dcvTheta_nonneg Kh G
  have ha : ‖G * Khᴴ‖ ≤ dcvTheta Kh G := by
    unfold dcvTheta; linarith [norm_nonneg G, norm_nonneg (Kh * G)]
  have hb : ‖Kh * G‖ ≤ dcvTheta Kh G := by
    unfold dcvTheta; linarith [norm_nonneg G, norm_nonneg (G * Khᴴ)]
  calc _ ≤ ‖G * Khᴴ‖ * ‖Yh‖ * ‖Kh * G‖ := h1
    _ ≤ dcvTheta Kh G * ‖Yh‖ * dcvTheta Kh G := by gcongr
    _ = ‖Yh‖ * dcvTheta Kh G ^ 2 := by ring

/-- Hilbert–Schmidt form: `‖G (𝒦* Ŷ 𝒦) G‖²_HS ≤ ‖Ŷ‖²_HS Θ(G)⁴`. -/
theorem dcv_factor_hs_le (Kh Yh G : Matrix ι ι ℂ) :
    dcvHS (G * (Khᴴ * Yh * Kh) * G) ≤ dcvHS Yh * dcvTheta Kh G ^ 4 := by
  have e : G * (Khᴴ * Yh * Kh) * G = (G * Khᴴ) * (Yh * (Kh * G)) := by
    simp only [Matrix.mul_assoc]
  rw [e]
  have hT := dcvTheta_nonneg Kh G
  have ha : ‖G * Khᴴ‖ ≤ dcvTheta Kh G := by
    unfold dcvTheta; linarith [norm_nonneg G, norm_nonneg (Kh * G)]
  have hb : ‖Kh * G‖ ≤ dcvTheta Kh G := by
    unfold dcvTheta; linarith [norm_nonneg G, norm_nonneg (G * Khᴴ)]
  have h1 := dcvHS_mul_left_le (G * Khᴴ) (Yh * (Kh * G))
  have h2 := dcvHS_mul_right_le Yh (Kh * G)
  have hY := dcvHS_nonneg Yh
  have ha2 : ‖G * Khᴴ‖ ^ 2 ≤ dcvTheta Kh G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hb2 : ‖Kh * G‖ ^ 2 ≤ dcvTheta Kh G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc _ ≤ ‖G * Khᴴ‖ ^ 2 * dcvHS (Yh * (Kh * G)) := h1
    _ ≤ ‖G * Khᴴ‖ ^ 2 * (dcvHS Yh * ‖Kh * G‖ ^ 2) := by gcongr
    _ ≤ dcvTheta Kh G ^ 2 * (dcvHS Yh * dcvTheta Kh G ^ 2) := by gcongr
    _ = dcvHS Yh * dcvTheta Kh G ^ 4 := by ring

/-- A bounded insertion: `‖G D₀ G‖ ≤ ‖D₀‖ Θ(G)²`. -/
theorem dcv_ins_le (Kh D₀ G : Matrix ι ι ℂ) : ‖G * D₀ * G‖ ≤ ‖D₀‖ * dcvTheta Kh G ^ 2 := by
  have hG := dcv_norm_le_theta Kh G
  have hT := dcvTheta_nonneg Kh G
  have h1 : ‖G * D₀ * G‖ ≤ ‖G‖ * ‖D₀‖ * ‖G‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  calc _ ≤ ‖G‖ * ‖D₀‖ * ‖G‖ := h1
    _ ≤ dcvTheta Kh G * ‖D₀‖ * dcvTheta Kh G := by gcongr
    _ = ‖D₀‖ * dcvTheta Kh G ^ 2 := by ring

/-- `‖G D₀ G‖²_HS ≤ |ι| ‖D₀‖² Θ(G)⁴`. -/
theorem dcv_ins_hs_le (Kh D₀ G : Matrix ι ι ℂ) :
    dcvHS (G * D₀ * G) ≤ Fintype.card ι * ‖D₀‖ ^ 2 * dcvTheta Kh G ^ 4 := by
  have h1 := dcvHS_le_card (G * D₀ * G)
  have h2 := dcv_ins_le Kh D₀ G
  have h3 : ‖G * D₀ * G‖ ^ 2 ≤ (‖D₀‖ * dcvTheta Kh G ^ 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  calc _ ≤ Fintype.card ι * ‖G * D₀ * G‖ ^ 2 := h1
    _ ≤ Fintype.card ι * (‖D₀‖ * dcvTheta Kh G ^ 2) ^ 2 := by gcongr
    _ = Fintype.card ι * ‖D₀‖ ^ 2 * dcvTheta Kh G ^ 4 := by ring

/-- **Source plus bounded insertion** (Step 6 of the proof in the paper): with
`Sh = 𝒦* Ŷ 𝒦 + D₀`, `‖G Sh G‖ ≤ (‖Ŷ‖ + ‖D₀‖) Θ(G)²`. -/
theorem dcv_dir_le (Kh Yh D₀ G : Matrix ι ι ℂ) :
    ‖G * (Khᴴ * Yh * Kh + D₀) * G‖ ≤ (‖Yh‖ + ‖D₀‖) * dcvTheta Kh G ^ 2 := by
  rw [Matrix.mul_add, Matrix.add_mul]
  refine (norm_add_le _ _).trans ?_
  have := dcv_factor_le Kh Yh G
  have := dcv_ins_le Kh D₀ G
  linarith

/-- `‖G Sh G‖²_HS ≤ (2‖Ŷ‖²_HS + 2|ι| ‖D₀‖²) Θ(G)⁴` for `Sh = 𝒦* Ŷ 𝒦 + D₀`. -/
theorem dcv_dir_hs_le (Kh Yh D₀ G : Matrix ι ι ℂ) :
    dcvHS (G * (Khᴴ * Yh * Kh + D₀) * G) ≤
      (2 * dcvHS Yh + 2 * (Fintype.card ι * ‖D₀‖ ^ 2)) * dcvTheta Kh G ^ 4 := by
  rw [Matrix.mul_add, Matrix.add_mul]
  refine (dcvHS_add_le _ _).trans ?_
  have := dcv_factor_hs_le Kh Yh G
  have := dcv_ins_hs_le Kh D₀ G
  nlinarith

end Factor

/-- `Ŝ = 𝒦* Ŷ 𝒦` for `S = K* Y K`. -/
theorem dcv_hat_source_eq {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {K Y S : Matrix n n ℂ} (h : S = Kᴴ * Y * K) :
    (dcvHat S : Matrix (n ⊕ m) (n ⊕ m) ℂ) = (dcvHat K)ᴴ * dcvHat Y * dcvHat K := by
  rw [h, dcvHat_conjTranspose, dcvHat_mul, dcvHat_mul]

/-!
## 3. Regularization: `Θ(G_κ) ≤ 2 Θ(G)`
-/

section Regular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G_c = G (1 - c G_c) = (1 - c G_c) G` for `G = N⁻¹`, `G_c = (N + c)⁻¹`. -/
theorem dcv_reg_factor {N : Matrix ι ι ℂ} {c : ℂ} (hN : IsUnit N.det)
    (hNc : IsUnit (N + c • (1 : Matrix ι ι ℂ)).det) :
    (N + c • (1 : Matrix ι ι ℂ))⁻¹ = N⁻¹ * (1 - c • (N + c • (1 : Matrix ι ι ℂ))⁻¹) ∧
      (N + c • (1 : Matrix ι ι ℂ))⁻¹ = (1 - c • (N + c • (1 : Matrix ι ι ℂ))⁻¹) * N⁻¹ := by
  set Gc := (N + c • (1 : Matrix ι ι ℂ))⁻¹ with hGc
  constructor
  · have h1 : N⁻¹ * (N + c • (1 : Matrix ι ι ℂ)) * Gc = N⁻¹ := by
      rw [Matrix.mul_assoc, mul_nonsing_inv _ hNc, Matrix.mul_one]
    have h2 : N⁻¹ * (N + c • (1 : Matrix ι ι ℂ)) * Gc = Gc + c • (N⁻¹ * Gc) := by
      rw [Matrix.mul_add, nonsing_inv_mul _ hN, Matrix.add_mul, Matrix.one_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    rw [h2] at h1
    exact eq_sub_iff_add_eq.mpr h1
  · have h1 : Gc * (N + c • (1 : Matrix ι ι ℂ)) * N⁻¹ = N⁻¹ := by
      rw [nonsing_inv_mul _ hNc, Matrix.one_mul]
    have h2 : Gc * (N + c • (1 : Matrix ι ι ℂ)) * N⁻¹ = Gc + c • (Gc * N⁻¹) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, mul_nonsing_inv _ hN, Matrix.mul_one,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [h2] at h1
    exact eq_sub_iff_add_eq.mpr h1

/-- **`Θ(G_c) ≤ 2 Θ(G)`** when `‖G_c‖ ≤ |c|⁻¹` (`‖1 - c G_c‖ ≤ 2`). -/
theorem dcv_theta_reg_le (Kh : Matrix ι ι ℂ) {N : Matrix ι ι ℂ} {c : ℂ} (hc : c ≠ 0)
    (hN : IsUnit N.det) (hNc : IsUnit (N + c • (1 : Matrix ι ι ℂ)).det)
    (hb : ‖(N + c • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ ‖c‖⁻¹) :
    dcvTheta Kh (N + c • (1 : Matrix ι ι ℂ))⁻¹ ≤ 2 * dcvTheta Kh N⁻¹ := by
  set Gc := (N + c • (1 : Matrix ι ι ℂ))⁻¹ with hGc
  obtain ⟨e1, e2⟩ := dcv_reg_factor hN hNc
  rw [← hGc] at e1 e2
  have hcp : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hR : ‖1 - c • Gc‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
    have h1 := dcv_norm_one_le (n := ι)
    have h2 : ‖c‖ * ‖Gc‖ ≤ ‖c‖ * ‖c‖⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    rw [mul_inv_cancel₀ hcp.ne'] at h2
    linarith
  have hG : ‖Gc‖ ≤ 2 * ‖N⁻¹‖ := tfl_inv_add_le_two hc hN hNc hb
  have hL : ‖Gc * Khᴴ‖ ≤ 2 * ‖N⁻¹ * Khᴴ‖ := by
    conv_lhs => rw [e2]
    rw [Matrix.mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hRt : ‖Kh * Gc‖ ≤ 2 * ‖Kh * N⁻¹‖ := by
    conv_lhs => rw [e1]
    rw [← Matrix.mul_assoc, mul_comm (2 : ℝ)]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  unfold dcvTheta
  linarith

end Regular

/-- **The regularized layer resolvent**: `Θ((𝒢⁻¹ + iκ)⁻¹) ≤ 2 Θ(𝒢)` wherever the layer matrix
is invertible (`κ > 0`, Hermitian `X` and diagonal blocks, `Im z ≥ 0`). -/
theorem dcv_theta_reg_layer {W : ℕ} (σ : LayerShape) (E : ℝ) {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ}
    (hκ : 0 < κ) (hN : IsUnit (layerMatrix σ E z X ω).det)
    (Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    dcvTheta Kh (tflReg κ (layerMatrix σ E z X ω))⁻¹ ≤
      2 * dcvTheta Kh (layerResolvent σ E z X ω) := by
  obtain ⟨hu, hb⟩ := tfl_reg_inv_le σ E hX ω hA hz hκ
  have hc : ((κ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hκ.ne') Complex.I_ne_zero
  have hnc : ‖(κ : ℂ) * Complex.I‖ = κ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  exact dcv_theta_reg_le Kh hc hN hu (by rw [hnc]; exact hb)

/-!
## 4. Moments of the weighted size `Θ(𝒢)`
-/

section Moments

/-- Hölder: `‖f g‖_p ≤ ‖f‖_{2p} ‖g‖_{2p}`. -/
theorem dcv_eLpNorm_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * p)) μ * eLpNorm g (ENNReal.ofReal (2 * p)) μ := by
  have hT : ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring⟩
  have h := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2 * p))
    (q := ENNReal.ofReal (2 * p)) (r := ENNReal.ofReal p) hf hg
  have e : (fun ω => f ω * g ω) = f • g := by funext ω; simp [smul_eq_mul]
  rw [e]
  exact h

theorem dcv_continuous_toBlocks11 {n m : Type*} :
    Continuous (fun M : Matrix (n ⊕ m) (n ⊕ m) ℂ => M.toBlocks₁₁) :=
  continuous_id.matrix_submatrix Sum.inl Sum.inl

theorem dcv_continuous_toBlocks12 {n m : Type*} :
    Continuous (fun M : Matrix (n ⊕ m) (n ⊕ m) ℂ => M.toBlocks₁₂) :=
  continuous_id.matrix_submatrix Sum.inl Sum.inr

/-- Uniform bulk data: `Im z_∂ ≥ η₀ > 0`, `|z_∂| ≤ 3`, `|E| ≤ 2` on `bulkInterval κ`. -/
theorem dcv_bulk {b κ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ E ∈ bulkInterval κ,
      η₀ ≤ (boundaryZ b E).im ∧ ‖boundaryZ b E‖ ≤ 3 ∧ |E| ≤ 2 := by
  obtain ⟨η, hη, hE⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  exact ⟨η, hη, fun E h =>
    ⟨(hE E h).1, norm_boundaryZ_le hb0.le (by linarith) (hE E h).2, (hE E h).2⟩⟩

theorem dcv_toBlocks21_one {n m : Type*} [DecidableEq n] [DecidableEq m] :
    (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ).toBlocks₂₁ = 0 := by
  ext i j; simp [toBlocks₂₁]

/-- **Block inverse equation**: `𝒢₂₁ = -z⁻¹ B* 𝒢₁₁` where the layer matrix
is invertible. -/
theorem dcv_G21_eq {W : ℕ} (σ : LayerShape) (E : ℝ) {z : ℂ} (hz : z ≠ 0)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ)
    (hN : IsUnit (layerMatrix σ E z X ω).det) :
    (layerResolvent σ E z X ω).toBlocks₂₁ =
      -(z⁻¹ • ((bondMatrix σ ω.2)ᴴ * (layerResolvent σ E z X ω).toBlocks₁₁)) := by
  set G := layerResolvent σ E z X ω with hG
  have h : layerMatrix σ E z X ω * G = 1 := mul_nonsing_inv _ hN
  have h2 := congrArg Matrix.toBlocks₂₁ h
  rw [dcv_toBlocks21_one, layerMatrix, ← fromBlocks_toBlocks G, fromBlocks_multiply,
    toBlocks_fromBlocks₂₁, Matrix.smul_mul, Matrix.one_mul] at h2
  have h3 : z • G.toBlocks₂₁ = -((bondMatrix σ ω.2)ᴴ * G.toBlocks₁₁) :=
    eq_neg_of_add_eq_zero_right h2
  calc G.toBlocks₂₁ = z⁻¹ • (z • G.toBlocks₂₁) := by
        rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
    _ = _ := by rw [h3, smul_neg]

/-- `‖𝒢₂₁ K*‖ ≤ |z|⁻¹ ‖B‖ ‖𝒢₁₁ K*‖` where the layer matrix is invertible. -/
theorem dcv_G21_norm_le {W : ℕ} (σ : LayerShape) (E : ℝ) {z : ℂ} (hz : z ≠ 0)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ)
    (hN : IsUnit (layerMatrix σ E z X ω).det) (K : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    ‖(layerResolvent σ E z X ω).toBlocks₂₁ * K‖ ≤
      ‖z‖⁻¹ * (‖bondMatrix σ ω.2‖ * ‖(layerResolvent σ E z X ω).toBlocks₁₁ * K‖) := by
  rw [dcv_G21_eq σ E hz X ω hN, Matrix.neg_mul, norm_neg, Matrix.smul_mul, norm_smul, norm_inv,
    Matrix.mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (l2_opNorm_mul _ _).trans ?_
  rw [l2_opNorm_conjTranspose]

/-- The weight `𝒦 = diag(K, 0)` of the separate-port layer, `K = z - X`. -/
abbrev dcvKh {W : ℕ} (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  dcvHat K

/-- **Moments of `Θ(𝒢)`** (Step 4 of the proof in the paper): for each `q ≥ 1` there are `C, W₀`; for
`W ≥ W₀`, every Hermitian two-port `X` and `E ∈ bulkInterval κ`,
`‖Θ(𝒢)‖_{L^q(layerLaw)} ≤ C`, `Θ(𝒢) = ‖𝒢‖ + ‖𝒢 𝒦*‖ + ‖𝒦 𝒢‖`, `𝒦 = diag(z - X, 0)`. -/
theorem dcv_theta_eLpNorm (hcount : ConditionalBlockGUECount) (hwl : WeightedLayerContract)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {q : ℝ} (hq : 1 ≤ q) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => dcvTheta (dcvKh (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W)
            (Fin 2 × Fin W) ℂ) - X)) (layerResolvent .separate E (boundaryZ b E) X ω))
          (ENNReal.ofReal q) (layerLaw W b .separate) ≤ ENNReal.ofReal C := by
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  obtain ⟨C1, W1, hm1⟩ := hwl.moments b hb0 hb1 κ hκ q hq
  obtain ⟨C2, W2, hm2⟩ := hwl.moments b hb0 hb1 κ hκ (2 * q) (by linarith)
  set CB := bondMomentConst b with hCB
  have hCB0 : 0 < CB := bondMomentConst_pos b
  set c := 1 + η₀⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨CA + c * (max C2 0 * CB) + max C1 0 + max C1 0,
    max (max W1 W2) (max ⌈q / ε₁⌉₊ ⌈2 * q⌉₊), by positivity, ?_⟩
  intro W hW hWW X hX E hE
  obtain ⟨hzim, hzM, -⟩ := hbulk E hE
  set z := boundaryZ b E with hzdef
  have hzpos : 0 < z.im := lt_of_lt_of_le hη₀ hzim
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hzpos; exact lt_irrefl 0 hzpos
  have hzn : η₀ ≤ ‖z‖ := hzim.trans (Complex.im_le_norm z)
  have hzinv : ‖z‖⁻¹ ≤ η₀⁻¹ := inv_anti₀ hη₀ hzn
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X with hK
  set μ := layerLaw W b .separate with hμ
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  have hW1 : W1 ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWW)
  have hW2 : W2 ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWW)
  have hWq : q ≤ ε₁ * W := by
    have h1 : q / ε₁ ≤ (W : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hWW))
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hW2q : 2 * q ≤ W :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hWW))
  obtain ⟨hinv, hmom⟩ := habs W hW .separate X hX E z hzim hzM
  have hA := hmom q hq hWq
  obtain ⟨h11, h11s, h12⟩ := hm1 W hW hW1 X hX E hE
  obtain ⟨-, h11s2, -⟩ := hm2 W hW hW2 X hX E hE
  have hB := bond_eLpNorm_le .separate hb0 (by linarith : (1 : ℝ) ≤ 2 * q) hW2q
  set G := fun ω => layerResolvent .separate E z X ω with hGdef
  have hGm : Measurable G := measurable_layerResolvent .separate E z X
  -- the four majorant pieces
  set f1 : LayerSample W .separate → ℝ := fun ω => ‖G ω‖ with hf1
  set f2 : LayerSample W .separate → ℝ := fun ω =>
    c * (‖(G ω).toBlocks₁₁ * Kᴴ‖ * (1 + ‖bondMatrix .separate ω.2‖)) with hf2
  set f3 : LayerSample W .separate → ℝ := fun ω => ‖K * (G ω).toBlocks₁₁‖ with hf3
  set f4 : LayerSample W .separate → ℝ := fun ω => ‖K * (G ω).toBlocks₁₂‖ with hf4
  have hc11 : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
      ‖M.toBlocks₁₁ * Kᴴ‖) :=
    (Continuous.matrix_mul dcv_continuous_toBlocks11 continuous_const).norm
  have hc3 : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
      ‖K * M.toBlocks₁₁‖) :=
    (Continuous.matrix_mul continuous_const dcv_continuous_toBlocks11).norm
  have hc4 : Continuous (fun M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ =>
      ‖K * M.toBlocks₁₂‖) :=
    (Continuous.matrix_mul continuous_const dcv_continuous_toBlocks12).norm
  have hm11 : Measurable (fun ω => ‖(G ω).toBlocks₁₁ * Kᴴ‖) := hc11.measurable.comp hGm
  have hm1 : AEStronglyMeasurable f1 μ := (continuous_norm.measurable.comp hGm).aestronglyMeasurable
  have hmB : Measurable (fun ω : LayerSample W .separate => 1 + ‖bondMatrix .separate ω.2‖) :=
    measurable_const.add (bond_measurable_opNorm .separate)
  have hm2 : AEStronglyMeasurable f2 μ :=
    ((hm11.mul hmB).const_mul c).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable f3 μ := (hc3.measurable.comp hGm).aestronglyMeasurable
  have hm4 : AEStronglyMeasurable f4 μ := (hc4.measurable.comp hGm).aestronglyMeasurable
  -- the pointwise majorant
  have hle : ∀ᵐ ω ∂μ, ‖dcvTheta (dcvKh K) (G ω)‖ ≤ ‖((f1 + f2) + f3 + f4) ω‖ := by
    filter_upwards [hinv] with ω hω
    have hT0 := dcvTheta_nonneg (dcvKh K) (G ω)
    have hp : 0 ≤ ((f1 + f2) + f3 + f4) ω := by
      simp only [Pi.add_apply, hf1, hf2, hf3, hf4]; positivity
    rw [Real.norm_of_nonneg hT0, Real.norm_of_nonneg hp]
    have hc1 : ‖G ω * (dcvKh K)ᴴ‖ ≤ ‖(G ω).toBlocks₁₁ * Kᴴ‖ + ‖(G ω).toBlocks₂₁ * Kᴴ‖ := by
      rw [dcvKh, dcvHat_conjTranspose]; exact dcv_mul_hat_le Kᴴ (G ω)
    have hc2 : ‖dcvKh K * G ω‖ ≤ ‖K * (G ω).toBlocks₁₁‖ + ‖K * (G ω).toBlocks₁₂‖ :=
      dcv_hat_mul_le K (G ω)
    have hc3 := dcv_G21_norm_le .separate E hz0 X ω hω Kᴴ
    have hb0' := norm_nonneg (bondMatrix .separate ω.2)
    have ha0 := norm_nonneg ((G ω).toBlocks₁₁ * Kᴴ)
    have hc4 : ‖z‖⁻¹ * (‖bondMatrix .separate ω.2‖ * ‖(G ω).toBlocks₁₁ * Kᴴ‖) ≤
        η₀⁻¹ * (‖bondMatrix .separate ω.2‖ * ‖(G ω).toBlocks₁₁ * Kᴴ‖) :=
      mul_le_mul_of_nonneg_right hzinv (by positivity)
    have hηi : 0 ≤ η₀⁻¹ := by positivity
    have hc5 : ‖(G ω).toBlocks₁₁ * Kᴴ‖ +
        η₀⁻¹ * (‖bondMatrix .separate ω.2‖ * ‖(G ω).toBlocks₁₁ * Kᴴ‖) ≤
        c * (‖(G ω).toBlocks₁₁ * Kᴴ‖ * (1 + ‖bondMatrix .separate ω.2‖)) := by
      rw [hc]; nlinarith [mul_nonneg hηi (mul_nonneg hb0' ha0), mul_nonneg hηi ha0,
        mul_nonneg hb0' ha0]
    simp only [Pi.add_apply, hf1, hf2, hf3, hf4, dcvTheta]
    linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by rw [ENNReal.one_le_ofReal]; exact hq
  refine (eLpNorm_mono_ae ((dcv_continuous_theta _).measurable.comp hGm).aestronglyMeasurable
    hle).trans ?_
  refine (eLpNorm_add_le hq1).trans ?_
  have e2 : f2 = c • (fun ω => ‖(G ω).toBlocks₁₁ * Kᴴ‖ * (1 + ‖bondMatrix .separate ω.2‖)) := by
    funext ω; simp [hf2, smul_eq_mul]
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hH := dcv_eLpNorm_mul_le (μ := μ) hm11.aestronglyMeasurable hmB.aestronglyMeasurable hq0
  have h2 : eLpNorm f2 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (c * (max C2 0 * CB)) := by
    rw [e2, eLpNorm_const_smul, Real.enorm_eq_ofReal hc0.le, ENNReal.ofReal_mul hc0.le,
      ENNReal.ofReal_mul (le_max_right _ _)]
    gcongr
    refine hH.trans (mul_le_mul' (h11s2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) hB)
  have h3 : eLpNorm f3 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (max C1 0) :=
    h11.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have h4 : eLpNorm f4 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (max C1 0) :=
    h12.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have h1 : eLpNorm f1 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal CA := hA
  calc eLpNorm (f1 + f2 + f3) (ENNReal.ofReal q) μ + eLpNorm f4 (ENNReal.ofReal q) μ
      ≤ (eLpNorm f1 (ENNReal.ofReal q) μ + eLpNorm f2 (ENNReal.ofReal q) μ +
          eLpNorm f3 (ENNReal.ofReal q) μ) + eLpNorm f4 (ENNReal.ofReal q) μ := by
        have h12' : eLpNorm (f1 + f2) (ENNReal.ofReal q) μ ≤
            eLpNorm f1 (ENNReal.ofReal q) μ + eLpNorm f2 (ENNReal.ofReal q) μ :=
          eLpNorm_add_le (f := f1) (g := f2) hq1
        have h123 : eLpNorm (f1 + f2 + f3) (ENNReal.ofReal q) μ ≤
            eLpNorm (f1 + f2) (ENNReal.ofReal q) μ + eLpNorm f3 (ENNReal.ofReal q) μ :=
          eLpNorm_add_le (f := f1 + f2) (g := f3) hq1
        exact add_le_add (h123.trans (add_le_add h12' le_rfl)) le_rfl
    _ ≤ ENNReal.ofReal CA + ENNReal.ofReal (c * (max C2 0 * CB)) + ENNReal.ofReal (max C1 0) +
          ENNReal.ofReal (max C1 0) :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = ENNReal.ofReal (CA + c * (max C2 0 * CB) + max C1 0 + max C1 0) := by
        have e0 : 0 ≤ c * (max C2 0 * CB) := mul_nonneg hc0.le (mul_nonneg (le_max_right _ _) hCB0.le)
        have e1 : 0 ≤ max C1 0 := le_max_right _ _
        rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hCA.le e0) e1) e1,
          ENNReal.ofReal_add (add_nonneg hCA.le e0) e1, ENNReal.ofReal_add hCA.le e0]

end Moments

/-!
## 5. The source family `X(h) = X - hS` (Step 1 of the proof in the paper)
-/

section Family

variable {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)

/-- `𝒢(h)⁻¹ = 𝒢⁻¹ + h Ŝ` for the old input `X(h) = X - hS`. -/
theorem dcv_layerMatrix_sub (X S : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (h : ℝ)
    (ω : LayerSample W σ) :
    layerMatrix σ E z (X - (h : ℂ) • S) ω = layerMatrix σ E z X ω + (h : ℂ) • dcvHat S := by
  rw [layerMatrix, layerMatrix, dcvHat, fromBlocks_smul, fromBlocks_add]
  congr 1
  · abel
  · simp
  · simp
  · simp

/-- **Step 1** (the resolvent derivative formula): `𝒢̇ = -𝒢 Ŝ 𝒢` at `h = 0`, wherever the layer
matrix is invertible (all fresh coordinates, `E` and `z` fixed). -/
theorem dcv_hasDerivAt_resolvent (X S : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (ω : LayerSample W σ) (hN : IsUnit (layerMatrix σ E z X ω).det) :
    HasDerivAt (fun h : ℝ => layerResolvent σ E z (X - (h : ℂ) • S) ω)
      (-(layerResolvent σ E z X ω * dcvHat S * layerResolvent σ E z X ω)) 0 := by
  set N := layerMatrix σ E z X ω with hNdef
  set P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := dcvHat S with hP
  have e : (fun h : ℝ => layerResolvent σ E z (X - (h : ℂ) • S) ω) =
      fun h : ℝ => Ring.inverse (N + h • P) := by
    funext h
    rw [layerResolvent, dcv_layerMatrix_sub, Matrix.nonsing_inv_eq_ringInverse, Complex.coe_smul]
  rw [e]
  have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hN
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit
  rw [IsUnit.unit_spec] at hinv
  have haff : HasDerivAt (fun h : ℝ => N + h • P) P 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const P).const_add N
    simpa using this
  have hinv' : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
        ↑hU.unit⁻¹ ↑hU.unit⁻¹)) ((fun h : ℝ => N + h • P) 0) := by
    simp only [zero_smul, add_zero]; exact hinv
  have h3 := hinv'.comp_hasDerivAt (0 : ℝ) haff
  have hinvN : (↑hU.unit⁻¹ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) =
      layerResolvent σ E z X ω := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec, layerResolvent, Matrix.nonsing_inv_eq_ringInverse]
  convert h3 using 1
  · rfl
  · rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hinvN]

end Family

/-!
## 6. The transported source `Y = K⁻* S K⁻¹`
-/

section Source

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `K = z - X` is invertible for Hermitian `X` and `Im z > 0`. -/
theorem dcv_K_isUnit {X : Matrix n n ℂ} (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    IsUnit (z • (1 : Matrix n n ℂ) - X).det := by
  have e : z • (1 : Matrix n n ℂ) - X =
      ((z.re : ℂ) • (1 : Matrix n n ℂ) - X) + Complex.I • diagonal (fun _ => ((z.im : ℝ) : ℂ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · conv_lhs => rw [← Complex.re_add_im z]
      ring
    · simp
  have hH : ((z.re : ℂ) • (1 : Matrix n n ℂ) - X).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq, Complex.star_def,
      Complex.conj_ofReal]
  refine (isUnit_det_and_norm_inv_le_of_lower hz fun ξ => ?_).1
  rw [e]
  exact tfl_lower_of_herm_add_diag hH (fun _ => z.im) (fun _ => le_rfl) ξ

/-- `S = K* Y K` for `Y = K⁻* S K⁻¹` and invertible `K`. -/
theorem dcv_source_eq {K S : Matrix n n ℂ} (hK : IsUnit K.det) :
    S = Kᴴ * ((K⁻¹)ᴴ * S * K⁻¹) * K := by
  have h1 : Kᴴ * (K⁻¹)ᴴ = 1 := by
    rw [← conjTranspose_mul, nonsing_inv_mul _ hK, conjTranspose_one]
  have h2 : K⁻¹ * K = 1 := nonsing_inv_mul _ hK
  calc S = (Kᴴ * (K⁻¹)ᴴ) * S * (K⁻¹ * K) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- `Y = K⁻* S K⁻¹ ⪰ 0` for `S ⪰ 0`. -/
theorem dcv_Y_posSemidef {K S : Matrix n n ℂ} (hS : S.PosSemidef) :
    ((K⁻¹)ᴴ * S * K⁻¹).PosSemidef :=
  hS.conjTranspose_mul_mul_same K⁻¹

/-- `0 ≤ Re Tr Y`, `‖Y‖ ≤ Re Tr Y` and `√(Re Tr Y²) ≤ Re Tr Y` for `Y ⪰ 0`. -/
theorem dcv_Y_bounds {Y : Matrix n n ℂ} (hY : Y.PosSemidef) :
    0 ≤ Y.trace.re ∧ ‖Y‖ ≤ Y.trace.re ∧ Real.sqrt (Y * Y).trace.re ≤ Y.trace.re ∧
      dcvHS Y = (Y * Y).trace.re := by
  have h1 := dcv_norm_le_trace hY
  have h0 : 0 ≤ Y.trace.re := (norm_nonneg _).trans h1
  obtain ⟨e, h2⟩ := dcv_hs_psd hY
  refine ⟨h0, h1, ?_, e⟩
  calc Real.sqrt (Y * Y).trace.re ≤ Real.sqrt (Y.trace.re ^ 2) := Real.sqrt_le_sqrt h2
    _ = Y.trace.re := Real.sqrt_sq h0

end Source

end BlockBand.Layers
