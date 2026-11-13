module

public import BlockBand.Critical.CommonPort.Regularized

/-!
# Common-port mean: the regularized bilinear observable and its gradient

* `cpq K u v N M = u*(K N₁₂)(K M₁₂)* v`, an `ℝ`-bilinear form (`cpqCLM`); `cpq_swap`
  (`cpq K u v M N = conj (cpq K v u N M)`), `cpq_eq_dot` and `cpq_GLG_eq_trace`
  (`cpq K u v (G Λ G) M = Tr(vecMulVec (G c) (a* G) Λ)`).
* `cpG κ x = (𝒢⁻¹ + iκ)⁻¹` at the coordinates, `cpF κ x = cpq K u v (cpG κ x) (cpG κ x)`,
  `K = matchedLeadK b e X`: `cpF_contDiff` (`C¹`) and `cpF_fderiv`
  (`dF(w) = q(G, -GΛ(w)G) + q(-GΛ(w)G, G)`).
* `cpF_gradient_le`: `(Σᵢ vᵢ |∂ᵢ F_κ|²)^{1/2} ≤ 4 ‖G‖ ‖K G₁₂‖ ‖K·topRows G‖ ‖u‖ ‖v‖ / √W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Layers
open BlockBand.Internal.Contracts.Inputs (weightedGradientNorm)
open scoped Matrix.Norms.L2Operator ComplexConjugate

/-- Euclidean norm of a coordinate vector. -/
def vnorm {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖

theorem vnorm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℂ) : 0 ≤ vnorm x := norm_nonneg _

theorem vnorm_sq {ι : Type*} [Fintype ι] (x : ι → ℂ) : vnorm x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold vnorm
  rw [EuclideanSpace.norm_sq_eq]

theorem vnorm_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (x : κ → ℂ) : vnorm (A *ᵥ x) ≤ ‖A‖ * vnorm x :=
  norm_toLp_mulVec_le A x

theorem vnorm_star {ι : Type*} [Fintype ι] (x : ι → ℂ) : vnorm (star x) = vnorm x := by
  have h : vnorm (star x) ^ 2 = vnorm x ^ 2 := by
    rw [vnorm_sq, vnorm_sq]
    exact Finset.sum_congr rfl fun i _ => by simp
  have := vnorm_nonneg (star x)
  have := vnorm_nonneg x
  nlinarith [sq_nonneg (vnorm (star x) - vnorm x), sq_nonneg (vnorm (star x) + vnorm x)]

/-- Cauchy–Schwarz: `|x* y| ≤ ‖x‖ ‖y‖`. -/
theorem norm_star_dot_le {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤ vnorm x * vnorm y := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 y : EuclideanSpace ℂ ι)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [vnorm, dotProduct_comm] using h

section Bilinear

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `q(N, M) = u* (K N₁₂)(K M₁₂)* v`. -/
def cpq (K : Matrix n n ℂ) (u v : n → ℂ) (N M : Matrix (n ⊕ m) (n ⊕ m) ℂ) : ℂ :=
  star u ⬝ᵥ (((K * N.toBlocks₁₂) * (K * M.toBlocks₁₂)ᴴ) *ᵥ v)

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem toBlocks12_add (N N' : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (N + N').toBlocks₁₂ = N.toBlocks₁₂ + N'.toBlocks₁₂ := rfl

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem toBlocks12_smul (c : ℂ) (N : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (c • N).toBlocks₁₂ = c • N.toBlocks₁₂ := rfl

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem toBlocks12_real_smul (r : ℝ) (N : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (r • N).toBlocks₁₂ = (r : ℂ) • N.toBlocks₁₂ := by
  ext i j; simp [Matrix.toBlocks₁₂]

/-- `q` as an `ℝ`-bilinear map. -/
def cpqLin (K : Matrix n n ℂ) (u v : n → ℂ) :
    Matrix (n ⊕ m) (n ⊕ m) ℂ →ₗ[ℝ] Matrix (n ⊕ m) (n ⊕ m) ℂ →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (cpq K u v)
    (fun N N' M => by
      simp only [cpq, toBlocks12_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec,
        dotProduct_add])
    (fun r N M => by
      simp only [cpq, toBlocks12_real_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec,
        dotProduct_smul]
      exact smul_eq_mul _ _)
    (fun N M M' => by
      simp only [cpq, toBlocks12_add, Matrix.mul_add, conjTranspose_add, Matrix.mul_add,
        Matrix.add_mulVec, dotProduct_add])
    (fun r N M => by
      simp only [cpq, toBlocks12_real_smul, Matrix.mul_smul, conjTranspose_smul, Matrix.mul_smul,
        Matrix.smul_mulVec, dotProduct_smul, Complex.star_def, Complex.conj_ofReal]
      exact smul_eq_mul _ _)

/-- `q` as a continuous `ℝ`-bilinear map. -/
def cpqCLM (K : Matrix n n ℂ) (u v : n → ℂ) :
    Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℝ] Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Matrix (n ⊕ m) (n ⊕ m) ℂ →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      cpqLin K u v)

omit [DecidableEq n] [DecidableEq m] in
theorem cpqCLM_apply (K : Matrix n n ℂ) (u v : n → ℂ) (N M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    cpqCLM K u v N M = cpq K u v N M := rfl

omit [DecidableEq n] in
theorem star_dot_mulVec_star (x y : n → ℂ) (P : Matrix n n ℂ) :
    star (star x ⬝ᵥ (P *ᵥ y)) = star y ⬝ᵥ (Pᴴ *ᵥ x) := by
  rw [Matrix.star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec]

omit [DecidableEq m] [DecidableEq n] in
/-- **Swap**: `q_{u,v}(M, N) = conj q_{v,u}(N, M)`. -/
theorem cpq_swap (K : Matrix n n ℂ) (u v : n → ℂ) (N M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    cpq K u v M N = star (cpq K v u N M) := by
  unfold cpq
  rw [star_dot_mulVec_star, Matrix.conjTranspose_mul (K * N.toBlocks₁₂),
    conjTranspose_conjTranspose]

/-- Extension of a physical vector by zero on the ports. -/
def extTop (y : n → ℂ) : n ⊕ m → ℂ := Sum.elim y 0

/-- Extension of a port vector by zero on the physical sites. -/
def extBot (w : m → ℂ) : n ⊕ m → ℂ := Sum.elim 0 w

omit [DecidableEq n] [DecidableEq m] in
theorem vnorm_extBot (w : m → ℂ) : vnorm (extBot (n := n) w) = vnorm w := by
  have h : vnorm (extBot (n := n) w) ^ 2 = vnorm w ^ 2 := by
    rw [vnorm_sq, vnorm_sq, Fintype.sum_sum_type]
    simp [extBot]
  have := vnorm_nonneg (extBot (n := n) w)
  have := vnorm_nonneg w
  nlinarith [sq_nonneg (vnorm (extBot (n := n) w) - vnorm w),
    sq_nonneg (vnorm (extBot (n := n) w) + vnorm w)]

omit [DecidableEq n] [DecidableEq m] in
/-- `q(N, M) = (ext₁ Kᴴu)* N ext₂((K M₁₂)* v)`. -/
theorem cpq_eq_dot (K : Matrix n n ℂ) (u v : n → ℂ) (N M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    cpq K u v N M = star (extTop (m := m) (Kᴴ *ᵥ u)) ⬝ᵥ
      (N *ᵥ extBot ((K * M.toBlocks₁₂)ᴴ *ᵥ v)) := by
  unfold cpq
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← star_star (star u ᵥ* K),
    star_vecMul, star_star]
  set w := (K * M.toBlocks₁₂)ᴴ *ᵥ v
  set y := Kᴴ *ᵥ u
  simp only [dotProduct, Fintype.sum_sum_type, extTop, extBot, Sum.elim_inl, Sum.elim_inr,
    Pi.star_apply, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.mulVec, Matrix.toBlocks₁₂, Matrix.of_apply, mul_zero, zero_add]

/-- `a* (G Λ G) c = Tr(vecMulVec (G c) (a* G) Λ)`. -/
theorem dot_GLG_eq_trace {ι : Type*} [Fintype ι] (a c : ι → ℂ) (G Λ : Matrix ι ι ℂ) :
    star a ⬝ᵥ ((G * Λ * G) *ᵥ c) = (vecMulVec (G *ᵥ c) (star a ᵥ* G) * Λ).trace := by
  have h1 : (vecMulVec (G *ᵥ c) (star a ᵥ* G) * Λ).trace =
      (star a ᵥ* G) ⬝ᵥ (Λ *ᵥ (G *ᵥ c)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct,
      Matrix.mulVec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [h1, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Hilbert–Schmidt mass of a rank-one matrix. -/
theorem hs_vecMulVec {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    ∑ p, ∑ q, ‖vecMulVec x y p q‖ ^ 2 = vnorm x ^ 2 * vnorm y ^ 2 := by
  rw [vnorm_sq, vnorm_sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [vecMulVec_apply, norm_mul, mul_pow]

theorem vnorm_star_vecMul {ι : Type*} [Fintype ι] (a : ι → ℂ) (G : Matrix ι ι ℂ) :
    vnorm (star a ᵥ* G) = vnorm (Gᴴ *ᵥ a) := by
  rw [← vnorm_star, star_vecMul, star_star]

omit [DecidableEq n] [DecidableEq m] in
/-- `Gᴴ (ext₁ Kᴴ u) = (K · topRows G)ᴴ u`. -/
theorem conjTranspose_mulVec_extTop (K : Matrix n n ℂ) (u : n → ℂ)
    (G : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    Gᴴ *ᵥ extTop (m := m) (Kᴴ *ᵥ u) = (K * topRows G)ᴴ *ᵥ u := by
  rw [conjTranspose_mul, ← Matrix.mulVec_mulVec]
  ext q
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, extTop, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, topRows,
    conjTranspose_apply, Matrix.submatrix_apply, id]

/-- The rank-one matrix `T = vecMulVec (G c) (a* G)` of the trace form, `a = ext₁(Kᴴ u)`,
`c = ext₂((K M₁₂)ᴴ v)`. -/
def cpT (K : Matrix n n ℂ) (u v : n → ℂ) (G M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  vecMulVec (G *ᵥ extBot (n := n) ((K * M.toBlocks₁₂)ᴴ *ᵥ v))
    (star (extTop (m := m) (Kᴴ *ᵥ u)) ᵥ* G)

omit [DecidableEq n] [DecidableEq m] in
/-- **Trace form of a resolvent-differentiated entry**: `q(G Λ G, M) = Tr(T Λ)` for every `Λ`. -/
theorem cpq_GLG_eq_trace (K : Matrix n n ℂ) (u v : n → ℂ) (G Λ M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    cpq K u v (G * Λ * G) M = (cpT K u v G M * Λ).trace := by
  rw [cpq_eq_dot, dot_GLG_eq_trace]
  rfl

/-- `HS(T)² ≤ (‖G‖ ‖K M₁₂‖ ‖v‖)² (‖K · topRows G‖ ‖u‖)²`. -/
theorem hs_cpT_le (K : Matrix n n ℂ) (u v : n → ℂ) (G M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    ∑ p, ∑ q, ‖cpT K u v G M p q‖ ^ 2 ≤
      (‖G‖ * ‖K * M.toBlocks₁₂‖ * vnorm v) ^ 2 * (‖K * topRows G‖ * vnorm u) ^ 2 := by
  unfold cpT
  rw [hs_vecMulVec]
  have h1 : vnorm (G *ᵥ extBot (n := n) ((K * M.toBlocks₁₂)ᴴ *ᵥ v)) ≤
      ‖G‖ * ‖K * M.toBlocks₁₂‖ * vnorm v := by
    refine (vnorm_mulVec_le G _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [vnorm_extBot]
    refine (vnorm_mulVec_le _ v).trans ?_
    rw [l2_opNorm_conjTranspose]
  have h2 : vnorm (star (extTop (m := m) (Kᴴ *ᵥ u)) ᵥ* G) ≤ ‖K * topRows G‖ * vnorm u := by
    rw [vnorm_star_vecMul, conjTranspose_mulVec_extTop]
    refine (vnorm_mulVec_le _ u).trans ?_
    rw [l2_opNorm_conjTranspose]
  exact mul_le_mul (pow_le_pow_left₀ (vnorm_nonneg _) h1 2)
    (pow_le_pow_left₀ (vnorm_nonneg _) h2 2) (by positivity) (by positivity)

omit [DecidableEq n] [DecidableEq m] in
theorem cpq_neg_left (K : Matrix n n ℂ) (u v : n → ℂ) (N M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    cpq K u v (-N) M = -cpq K u v N M := by
  rw [← cpqCLM_apply, ← cpqCLM_apply, map_neg]; rfl

omit [DecidableEq n] [DecidableEq m] in
theorem cpq_neg_right (K : Matrix n n ℂ) (u v : n → ℂ) (N M : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    cpq K u v N (-M) = -cpq K u v N M := by
  rw [← cpqCLM_apply, ← cpqCLM_apply, map_neg]

end Bilinear

section Coordinates

variable (W : ℕ) (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  (u v : Fin 2 × Fin W → ℂ)

/-- The regularized resolvent at the real coordinates `x`: `Ring.inverse (𝒢⁻¹(x) + iκ)`. -/
def cpG (κ : ℝ) (x : TflCoord W .common → ℝ) : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
  Ring.inverse (tflPsi W b .common e (commonZ b e) X κ x)

/-- The regularized observable `F_κ(x) = u*(L_κ L_κ*)v`, `L_κ = K 𝒢_κ,₁₂`. -/
def cpF (κ : ℝ) (x : TflCoord W .common → ℝ) : ℂ :=
  cpqCLM (matchedLeadK b e X) u v (cpG W b e X κ x) (cpG W b e X κ x)

variable {X} in
theorem cpG_hasFDerivAt (hX : X.IsHermitian) (hz : 0 ≤ (commonZ b e).im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W .common → ℝ) :
    HasFDerivAt (cpG W b e X κ)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
        (cpG W b e X κ x) (cpG W b e X κ x))).comp
        (LinearMap.toContinuousLinearMap (tflLinMap W b .common))) x := by
  set U := (tflPsi_isUnit W b .common e (commonZ b e) hX hz hκ x).unit with hU
  have hL : HasFDerivAt (tflPsi W b .common e (commonZ b e) X κ)
      (LinearMap.toContinuousLinearMap (tflLinMap W b .common)) x :=
    (ContinuousLinearMap.hasFDerivAt _).const_add _
  have h : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
        ↑U⁻¹ ↑U⁻¹)) (tflPsi W b .common e (commonZ b e) X κ x) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) U
    rwa [IsUnit.unit_spec] at this
  have hinv : (↑U⁻¹ : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) = cpG W b e X κ x := by
    rw [cpG, ← Ring.inverse_unit, IsUnit.unit_spec]
  rw [hinv] at h
  exact h.comp x hL

variable {X} in
theorem cpG_contDiff (hX : X.IsHermitian) (hz : 0 ≤ (commonZ b e).im) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (cpG W b e X κ) := by
  have hL : ContDiff ℝ 1 (tflPsi W b .common e (commonZ b e) X κ) :=
    contDiff_const.add (ContinuousLinearMap.contDiff _)
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := contDiffAt_ringInverse ℝ (n := 1)
    (tflPsi_isUnit W b .common e (commonZ b e) hX hz hκ x).unit
  rw [IsUnit.unit_spec] at h
  exact h.comp x hL.contDiffAt

variable {X} in
/-- `F_κ` is `C¹`. -/
theorem cpF_contDiff (hX : X.IsHermitian) (hz : 0 ≤ (commonZ b e).im) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (cpF W b e X u v κ) := by
  have hG := cpG_contDiff W b e hX hz hκ
  exact (cpqCLM (matchedLeadK b e X) u v).isBoundedBilinearMap.contDiff.comp (hG.prodMk hG)

variable {X} in
/-- **Derivative of `F_κ`**: `dF_κ(w) = q(G, -G Λ(w) G) + q(-G Λ(w) G, G)`. -/
theorem cpF_fderiv (hX : X.IsHermitian) (hz : 0 ≤ (commonZ b e).im) {κ : ℝ} (hκ : 0 < κ)
    (x w : TflCoord W .common → ℝ) :
    fderiv ℝ (cpF W b e X u v κ) x w =
      cpq (matchedLeadK b e X) u v (cpG W b e X κ x)
          (-(cpG W b e X κ x * tflLin W b .common w * cpG W b e X κ x)) +
        cpq (matchedLeadK b e X) u v
          (-(cpG W b e X κ x * tflLin W b .common w * cpG W b e X κ x)) (cpG W b e X κ x) := by
  have hG := cpG_hasFDerivAt W b e hX hz hκ x
  have h := (cpqCLM (matchedLeadK b e X) u v).hasFDerivAt_of_bilinear hG hG
  rw [show cpF W b e X u v κ = fun y => cpqCLM (matchedLeadK b e X) u v (cpG W b e X κ y)
    (cpG W b e X κ y) from rfl, h.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, LinearMap.coe_toContinuousLinearMap', cpqCLM_apply]
  rfl

variable {X} in
/-- **Gradient bound for `F_κ`.** For `W ≥ 1`, `0 < b < 1/2`, Hermitian
`X`, `Im z₀ ≥ 0`, `κ > 0`, at every point `x`, with `G = 𝒢_κ(x)`, `K = z_b - X`:
`(Σᵢ vᵢ |∂ᵢ F_κ|²)^{1/2} ≤ 4 ‖G‖ ‖K G₁₂‖ ‖K · topRows G‖ ‖u‖ ‖v‖ / √W`. -/
theorem cpF_gradient_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ (commonZ b e).im) {κ : ℝ} (hκ : 0 < κ) (x : TflCoord W .common → ℝ) :
    weightedGradientNorm (tflVar W b .common) (cpF W b e X u v κ) x ≤
      4 * (‖cpG W b e X κ x‖ * ‖matchedLeadK b e X * (cpG W b e X κ x).toBlocks₁₂‖ *
        ‖matchedLeadK b e X * topRows (cpG W b e X κ x)‖ * vnorm u * vnorm v) / Real.sqrt W := by
  set G := cpG W b e X κ x with hG
  set K := matchedLeadK b e X with hK
  set Q := ‖G‖ * ‖K * G.toBlocks₁₂‖ * ‖K * topRows G‖ * vnorm u * vnorm v with hQ
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; have := vnorm_nonneg u; have := vnorm_nonneg v; positivity
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set T₁ := cpT K u v G G
  set T₂ := cpT K v u G G
  have hder : ∀ i : TflCoord W .common,
      ‖fderiv ℝ (cpF W b e X u v κ) x (Pi.single i 1)‖ ^ 2 ≤
        2 * ‖(T₁ * tflLin W b .common (Pi.single i 1)).trace‖ ^ 2 +
          2 * ‖(T₂ * tflLin W b .common (Pi.single i 1)).trace‖ ^ 2 := by
    intro i
    set Λ := tflLin W b .common (Pi.single i 1)
    rw [cpF_fderiv W b e u v hX hz hκ x, cpq_neg_right, cpq_neg_left, ← hG, ← hK,
      cpq_swap K u v (G * Λ * G) G, cpq_GLG_eq_trace, cpq_GLG_eq_trace]
    set t₁ := (T₁ * Λ).trace
    set t₂ := (T₂ * Λ).trace
    have h1 : ‖-star t₂ + -t₁‖ ≤ ‖t₂‖ + ‖t₁‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_neg, norm_neg, norm_star]
    have h0 : 0 ≤ ‖-star t₂ + -t₁‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖t₂‖ - ‖t₁‖), norm_nonneg t₁, norm_nonneg t₂]
  obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
  have hc : 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) ≤ 4 / W := by
    have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
    rw [this]; linarith
  have hHS1 : ∑ p, ∑ q, ‖T₁ p q‖ ^ 2 ≤ Q ^ 2 := by
    refine (hs_cpT_le K u v G G).trans (le_of_eq ?_)
    rw [hQ]; ring
  have hHS2 : ∑ p, ∑ q, ‖T₂ p q‖ ^ 2 ≤ Q ^ 2 := by
    refine (hs_cpT_le K v u G G).trans (le_of_eq ?_)
    rw [hQ]; ring
  have hw1 := tfl_weighted_trace_le W b .common T₁
  have hw2 := tfl_weighted_trace_le W b .common T₂
  have hcoef : 0 ≤ 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) := by positivity
  have hsum : ∑ i, (tflVar W b .common i : ℝ) *
      ‖fderiv ℝ (cpF W b e X u v κ) x (Pi.single i 1)‖ ^ 2 ≤ 16 * Q ^ 2 / W := by
    calc ∑ i, (tflVar W b .common i : ℝ) * ‖fderiv ℝ (cpF W b e X u v κ) x (Pi.single i 1)‖ ^ 2
        ≤ ∑ i, (tflVar W b .common i : ℝ) *
            (2 * ‖(T₁ * tflLin W b .common (Pi.single i 1)).trace‖ ^ 2 +
              2 * ‖(T₂ * tflLin W b .common (Pi.single i 1)).trace‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hder i) (NNReal.coe_nonneg _)
      _ = 2 * ∑ i, (tflVar W b .common i : ℝ) *
              ‖(T₁ * tflLin W b .common (Pi.single i 1)).trace‖ ^ 2 +
            2 * ∑ i, (tflVar W b .common i : ℝ) *
              ‖(T₂ * tflLin W b .common (Pi.single i 1)).trace‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ 2 * ((4 / W) * Q ^ 2) + 2 * ((4 / W) * Q ^ 2) := by
          gcongr
          · exact hw1.trans (mul_le_mul hc hHS1 (by positivity) (by positivity))
          · exact hw2.trans (mul_le_mul hc hHS2 (by positivity) (by positivity))
      _ = 16 * Q ^ 2 / W := by ring
  unfold weightedGradientNorm
  have hsq : Real.sqrt (16 * Q ^ 2 / W) = 4 * Q / Real.sqrt W := by
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW'
    rw [show 16 * Q ^ 2 / (W : ℝ) = (4 * Q / Real.sqrt W) ^ 2 by
      rw [div_pow, Real.sq_sqrt hW'.le]; ring]
    exact Real.sqrt_sq (by positivity)
  calc Real.sqrt (∑ i, (tflVar W b .common i : ℝ) *
        ‖fderiv ℝ (cpF W b e X u v κ) x (Pi.single i 1)‖ ^ 2)
      ≤ Real.sqrt (16 * Q ^ 2 / W) := Real.sqrt_le_sqrt hsum
    _ = 4 * Q / Real.sqrt W := hsq

end Coordinates

end BlockBand.Critical.CommonPort
