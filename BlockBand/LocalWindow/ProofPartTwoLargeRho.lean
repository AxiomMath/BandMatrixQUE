module

public import BlockBand.LocalWindow.ProofPartTwoTransfer
public import BlockBand.LocalWindow.ProofPartTwoCompress

/-!
# The large rank-one parameter `|ρ| > W^H`

Deterministic bounds for an eigenvector of `M + ρww*` with `|ρ|` large: it is close to the
orthogonal complement of `w`, and window data for the compression transfer to it.

Coordinate-free form: `M` (the matrix `F_reg(E) + G - E` with `‖M‖ ≤ K`), a unit `w`, an
isometry `U : ℂ^κ → w^⊥` (`U*U = 1`, `U*w = 0`, `UU* + ww* = 1`), `B₀ = U*MU`, and a unit
eigenvector `v` of `M + ρww*` with eigenvalue `λ`, `|λ| ≤ K`; `x = w*v`, `y = U*v`.

## Main results

* `vnorm v = √(Σ|v_k|²)` with the triangle inequality, homogeneity and `vnorm (A v) ≤ ‖A‖ vnorm v`.
* **`largeRho_component_le`**: `|x| ≤ 2K/|ρ|`.
* **`largeRho_compressed_residual_le`**: `‖(B₀ - λ)y‖ ≤ K |x|` (hence `≤ 2K²/|ρ|`).
* `largeRho_overlap_le`: `|v*Jv - y*(U*JU)y| ≤ |x|(2 + |x|)` for a contraction `J`.
* **`window_transfer_approx`**: `ProofETH.window_transfer` for an *approximate* unit eigenvector
  (`‖(B - λ)y‖ ≤ r_a`, `‖B - Â‖ ≤ r_g`; the exact eigenvector of the rank-one correction
  `B - (B - λ)y y*`), with `τ = (r_g + r_a)/h`.
* **`largeRho_window_transfer`**: the full eigenvector `v` from compressed window data at a grid
  matrix `Â` of `w^⊥` (`4K ≤ |ρ|`): `|v*Jv - c₀| ≤ |S|ε + ε' + 2τ + (1 + |c₀|)τ² +
  (2K/|ρ|)(2 + 2K/|ρ|) + 2(2K/|ρ|)|c₀|`, `τ = (r_g + 4K²/|ρ|)/h`.
* `compressSample`, `measurableEmbedding_compressSample`, **`gue_compress_preimage_le`**: under
  `CompressedGUELawBridgeStatement`, `GUE_{2W}(s/2W){G : U*GU ∈ √s' · T} ≤ gueSourceLaw(2W-1)(T)`
  for every set `T` (no measurability needed).
* **`gue_compress_ethBad_le`**: `ExternalETH` on the compressed `(2W - 1)`-block at variance
  `s' = s(1 - 1/(2W))`: for a compressed deformation `F` on `Fin (2W-1)` satisfying the ETH
  hypotheses, the compressed fresh noise `U*GU` lies in `√s'·ethBadEvent` with `GUE`-probability
  at most `(2W-1)^{-D}`.

The hypotheses `CompressedGUELawBridgeStatement` and `ExternalETH` are used only by the last two
results; the rest is deterministic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH
open scoped ENNReal Matrix.Norms.L2Operator

section Vnorm

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Euclidean norm `√(Σ |v_k|²)`. -/
def vnorm (v : ι → ℂ) : ℝ := Real.sqrt (sqNorm v)

theorem vnorm_eq (v : ι → ℂ) : vnorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem vnorm_nonneg (v : ι → ℂ) : 0 ≤ vnorm v := Real.sqrt_nonneg _

theorem vnorm_sq (v : ι → ℂ) : vnorm v ^ 2 = sqNorm v := Real.sq_sqrt (sqNorm_nonneg v)

theorem vnorm_of_sqNorm_one {v : ι → ℂ} (h : sqNorm v = 1) : vnorm v = 1 := by
  unfold vnorm; rw [h, Real.sqrt_one]

theorem vnorm_add_le (u v : ι → ℂ) : vnorm (u + v) ≤ vnorm u + vnorm v := by
  rw [vnorm_eq, vnorm_eq, vnorm_eq, WithLp.toLp_add]; exact norm_add_le _ _

theorem vnorm_sub_le (u v : ι → ℂ) : vnorm (u - v) ≤ vnorm u + vnorm v := by
  rw [vnorm_eq, vnorm_eq, vnorm_eq, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem vnorm_smul (c : ℂ) (v : ι → ℂ) : vnorm (c • v) = ‖c‖ * vnorm v := by
  rw [vnorm_eq, vnorm_eq, WithLp.toLp_smul, norm_smul]

theorem vnorm_neg (v : ι → ℂ) : vnorm (-v) = vnorm v := by
  rw [vnorm_eq, vnorm_eq, WithLp.toLp_neg, norm_neg]

theorem vnorm_mulVec_le (A : Matrix κ ι ℂ) (v : ι → ℂ) : vnorm (A *ᵥ v) ≤ ‖A‖ * vnorm v := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  rw [vnorm_eq, vnorm_eq]; exact h

/-- An isometry `U*U = 1` is a contraction, and so is `U*`. -/
theorem opNorm_le_one_of_isometry {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) : ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have : U = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]; exact zero_le_one
  · have h := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [hU, norm_one] at h
    nlinarith [norm_nonneg U]

theorem opNorm_conjTranspose_le_one_of_isometry {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) :
    ‖Uᴴ‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]; exact opNorm_le_one_of_isometry hU

/-- `‖U y‖ = ‖y‖` for an isometry. -/
theorem vnorm_isometry {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) (y : κ → ℂ) :
    vnorm (U *ᵥ y) = vnorm y := by
  have h : sqNorm (U *ᵥ y) = sqNorm y := by
    have e1 := star_dotProduct_self (U *ᵥ y)
    have e2 := star_dotProduct_self y
    have e3 : star (U *ᵥ y) ⬝ᵥ (U *ᵥ y) = star y ⬝ᵥ y := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]
    rw [e1, e2] at e3
    exact_mod_cast e3
  unfold vnorm; rw [h]

/-- `(ww*) v = (w*v) w`. -/
theorem vecMulVec_star_mulVec (w v : ι → ℂ) :
    vecMulVec w (star w) *ᵥ v = (star w ⬝ᵥ v) • w := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

end Vnorm

/-!
## The block bounds
-/

section Block

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The component along `w`**: if `‖M‖ ≤ K`, `w, v` are unit vectors,
`ρ ≠ 0` and `(M + ρww*) v = λ v` with `|λ| ≤ K`, then `|w*v| ≤ 2K/|ρ|`. -/
theorem largeRho_component_le {M : Matrix ι ι ℂ} {K : ℝ} (hM : ‖M‖ ≤ K) {w v : ι → ℂ}
    (hw : sqNorm w = 1) (hv : sqNorm v = 1) {ρ lam : ℝ} (hρ : ρ ≠ 0) (hlam : |lam| ≤ K)
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (lam : ℂ) • v) :
    ‖star w ⬝ᵥ v‖ ≤ 2 * K / |ρ| := by
  have hρ0 : 0 < |ρ| := abs_pos.mpr hρ
  have e : ((ρ : ℂ) * (star w ⬝ᵥ v)) • w = (lam : ℂ) • v - M *ᵥ v := by
    rw [add_mulVec, smul_mulVec, vecMulVec_star_mulVec, smul_smul] at heig
    rw [← heig]; abel
  have h1 : vnorm (((ρ : ℂ) * (star w ⬝ᵥ v)) • w) = |ρ| * ‖star w ⬝ᵥ v‖ := by
    rw [vnorm_smul, vnorm_of_sqNorm_one hw, mul_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have h2 : vnorm ((lam : ℂ) • v - M *ᵥ v) ≤ 2 * K := by
    refine (vnorm_sub_le _ _).trans ?_
    rw [vnorm_smul, vnorm_of_sqNorm_one hv, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := (vnorm_mulVec_le M v).trans (by rw [vnorm_of_sqNorm_one hv, mul_one])
    linarith
  rw [e] at h1
  rw [le_div_iff₀ hρ0]
  linarith

/-- The decomposition `v = U(U*v) + (w*v) w` from `UU* + ww* = 1`. -/
theorem decomp_of_compl {U : Matrix ι κ ℂ} {w : ι → ℂ}
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (v : ι → ℂ) :
    v = U *ᵥ (Uᴴ *ᵥ v) + (star w ⬝ᵥ v) • w := by
  have h := congrArg (· *ᵥ v) hcompl
  rw [add_mulVec, ← mulVec_mulVec, vecMulVec_star_mulVec, one_mulVec] at h
  exact h.symm

/-- **The compressed residual**: with `U*U = 1`, `U*w = 0`, `UU* + ww* = 1`,
`w, v` unit, `‖M‖ ≤ K` and `(M + ρww*) v = λ v`: `‖(U*MU - λ)(U*v)‖ ≤ K |w*v|`. -/
theorem largeRho_compressed_residual_le {M : Matrix ι ι ℂ} {K : ℝ} (hM : ‖M‖ ≤ K)
    {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w v : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) {ρ lam : ℝ}
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (lam : ℂ) • v) :
    vnorm ((Uᴴ * M * U - (lam : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ (Uᴴ *ᵥ v)) ≤
      K * ‖star w ⬝ᵥ v‖ := by
  set x := star w ⬝ᵥ v
  set y := Uᴴ *ᵥ v
  have hdec := decomp_of_compl hcompl v
  have hUy : U *ᵥ y = v - x • w := by
    conv_rhs => rw [hdec]
    abel
  have h0 : Uᴴ *ᵥ (M *ᵥ v) = (lam : ℂ) • y := by
    have h := congrArg (Uᴴ *ᵥ ·) heig
    rw [add_mulVec, smul_mulVec, vecMulVec_star_mulVec, mulVec_add, mulVec_smul, mulVec_smul,
      hUw, smul_zero, smul_zero, add_zero, mulVec_smul] at h
    exact h
  have e : (Uᴴ * M * U - (lam : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y = -(x • (Uᴴ *ᵥ (M *ᵥ w))) := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hUy, mulVec_sub,
      mulVec_sub, mulVec_smul, mulVec_smul, h0]
    abel
  rw [e, vnorm_neg, vnorm_smul]
  have h1 : vnorm (Uᴴ *ᵥ (M *ᵥ w)) ≤ K := by
    refine (vnorm_mulVec_le _ _).trans ?_
    have h2 := (vnorm_mulVec_le M w).trans (by rw [vnorm_of_sqNorm_one hw, mul_one])
    have h3 := opNorm_conjTranspose_le_one_of_isometry hUU
    have h4 : 0 ≤ vnorm (M *ᵥ w) := vnorm_nonneg _
    nlinarith [norm_nonneg Uᴴ]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- `(U y)* J (U y) = y* (U*JU) y`. -/
theorem compress_quadratic (U : Matrix ι κ ℂ) (J : Matrix ι ι ℂ) (y : κ → ℂ) :
    star (U *ᵥ y) ⬝ᵥ (J *ᵥ (U *ᵥ y)) = star y ⬝ᵥ ((Uᴴ * J * U) *ᵥ y) := by
  rw [star_mulVec, ← dotProduct_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]

/-- **Overlap transfer to the compression**: if `v = U y + x w` (`v, w` unit) and `J`
is a contraction, `|v*Jv - y*(U*JU)y| ≤ |x|(2 + |x|)`. -/
theorem largeRho_overlap_le {U : Matrix ι κ ℂ} {J : Matrix ι ι ℂ}
    (hJ : ‖J‖ ≤ 1) {w v : ι → ℂ} (hw : sqNorm w = 1) (hv : sqNorm v = 1) {y : κ → ℂ} {x : ℂ}
    (hdec : v = U *ᵥ y + x • w) :
    ‖star v ⬝ᵥ (J *ᵥ v) - star y ⬝ᵥ ((Uᴴ * J * U) *ᵥ y)‖ ≤ ‖x‖ * (2 + ‖x‖) := by
  set u := U *ᵥ y
  rw [← compress_quadratic]
  have e : star v ⬝ᵥ (J *ᵥ v) - star u ⬝ᵥ (J *ᵥ u) =
      star (x • w) ⬝ᵥ (J *ᵥ v) + star u ⬝ᵥ (J *ᵥ (x • w)) := by
    rw [hdec]
    simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add]
    ring
  have hu : vnorm u ≤ 1 + ‖x‖ := by
    have : u = v - x • w := by rw [hdec]; abel
    rw [this]
    refine (vnorm_sub_le _ _).trans ?_
    rw [vnorm_of_sqNorm_one hv, vnorm_smul, vnorm_of_sqNorm_one hw, mul_one]
  have hxw : vnorm (x • w) = ‖x‖ := by rw [vnorm_smul, vnorm_of_sqNorm_one hw, mul_one]
  have b1 := bilinear_le_of_opNorm_le hJ (x • w) v
  have b2 := bilinear_le_of_opNorm_le hJ u (x • w)
  change ‖_‖ ≤ vnorm (x • w) * vnorm v at b1
  change ‖_‖ ≤ vnorm u * vnorm (x • w) at b2
  rw [hxw, vnorm_of_sqNorm_one hv] at b1
  rw [hxw] at b2
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have : vnorm u * ‖x‖ ≤ (1 + ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
  nlinarith [norm_nonneg x]

end Block

/-!
## Window transfer for an approximate eigenvector
-/

section Approx

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- **Window transfer for an approximate unit eigenvector**:
the hypotheses of `ProofETH.window_transfer` for `Â` (Hermitian, orthonormal eigenvectors `e_k`,
eigenvalues `μ_k`, window `S`, pair bounds `ε`, centre bounds `ε'`), a contraction `J`, and a
unit `y` with `‖(B - λ)y‖ ≤ r_a`, `‖B - Â‖ ≤ r_g`. Then, with `τ = (r_g + r_a)/h`,
`|y*Jy - c₀| ≤ |S|ε + ε' + 2τ + (1 + |c₀|)τ²` (`y` is an exact eigenvector of the rank-one
correction `B - (B - λ)y y*`). -/
theorem window_transfer_approx {B Ahat J : Matrix κ κ ℂ} (hAhat : Ahat.IsHermitian)
    {e : κ → κ → ℂ} (he : IsOrthonormalFamily e) {μ : κ → ℝ}
    (heig : ∀ k, Ahat *ᵥ e k = (μ k : ℂ) • e k) (hJ : ‖J‖ ≤ 1) {y : κ → ℂ}
    (hy : sqNorm y = 1) {lam ra rg h : ℝ} (hra : 0 ≤ ra) (hrg : 0 ≤ rg) (hh : 0 < h)
    (happrox : vnorm ((B - (lam : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y) ≤ ra)
    (hBA : ‖B - Ahat‖ ≤ rg) {S : Finset κ} (hS : ∀ k ∉ S, h ≤ |μ k - lam|) {c : κ → ℂ}
    {c₀ : ℂ} {ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hpair : ∀ k ∈ S, ∀ l ∈ S,
      ‖star (e k) ⬝ᵥ (J *ᵥ e l) - (if k = l then c k else 0)‖ ≤ ε)
    (hcen : ∀ k ∈ S, ‖c k - c₀‖ ≤ ε') :
    ‖star y ⬝ᵥ (J *ᵥ y) - c₀‖ ≤
      S.card * ε + ε' + 2 * ((rg + ra) / h) + (1 + ‖c₀‖) * ((rg + ra) / h) ^ 2 := by
  set z := (B - (lam : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y
  set A := B - vecMulVec z (star y)
  have hyy : star y ⬝ᵥ y = 1 := by rw [star_dotProduct_self, hy]; simp
  have hAy : A *ᵥ y = (lam : ℂ) • y := by
    have hz : z = B *ᵥ y - (lam : ℂ) • y := by
      simp only [z, sub_mulVec, smul_mulVec, one_mulVec]
    rw [sub_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hyy, one_smul, hz]
    abel
  have hpert : sqNorm ((A - Ahat) *ᵥ y) ≤ (rg + ra) ^ 2 := by
    have e1 : (A - Ahat) *ᵥ y = (B - Ahat) *ᵥ y - z := by
      rw [sub_mulVec, sub_mulVec, sub_mulVec, vecMulVec_mulVec, op_smul_eq_smul, hyy, one_smul]
      abel
    have h1 : vnorm ((A - Ahat) *ᵥ y) ≤ rg + ra := by
      rw [e1]
      refine (vnorm_sub_le _ _).trans (add_le_add ?_ happrox)
      refine (vnorm_mulVec_le _ _).trans ?_
      rw [vnorm_of_sqNorm_one hy, mul_one]; exact hBA
    rw [← vnorm_sq]
    exact pow_le_pow_left₀ (vnorm_nonneg _) h1 2
  exact window_transfer hAhat he heig (bilinear_le_of_opNorm_le hJ) hy hAy
    (add_nonneg hrg hra) hh hpert hS hε hε' hpair hcen

end Approx

/-!
## The full eigenvector from the compressed window
-/

section Full

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **From the compressed window to the full eigenvector**. Let `‖M‖ ≤ K`,
`w` unit, `U : ℂ^κ → ℂ^ι` with `U*U = 1`, `U*w = 0`, `UU* + ww* = 1`, `ρ` real with
`4K ≤ |ρ|` (`K > 0`), and `v` a unit eigenvector of `M + ρww*` with eigenvalue `λ`, `|λ| ≤ K`.
Let `Â` be a Hermitian grid matrix on `w^⊥` (`κ`) with `‖U*MU - Â‖ ≤ r_g` and the window data of
`ProofETH.window_transfer` for the compressed contraction `U*JU`. Then, with
`τ = (r_g + 4K²/|ρ|)/h`,
`|v*Jv - c₀| ≤ |S|ε + ε' + 2τ + (1 + |c₀|)τ² + (2K/|ρ|)(2 + 2K/|ρ|) + 2 (2K/|ρ|)|c₀|`. -/
theorem largeRho_window_transfer {M : Matrix ι ι ℂ} {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K)
    {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w v : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) (hv : sqNorm v = 1)
    {ρ lam : ℝ} (hρ : 4 * K ≤ |ρ|) (hlam : |lam| ≤ K)
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (lam : ℂ) • v)
    {J : Matrix ι ι ℂ} (hJ : ‖J‖ ≤ 1) {Ahat : Matrix κ κ ℂ} (hAhat : Ahat.IsHermitian)
    {e : κ → κ → ℂ} (he : IsOrthonormalFamily e) {μ : κ → ℝ}
    (heigA : ∀ k, Ahat *ᵥ e k = (μ k : ℂ) • e k) {rg h : ℝ} (hrg : 0 ≤ rg) (hh : 0 < h)
    (hBA : ‖Uᴴ * M * U - Ahat‖ ≤ rg) {S : Finset κ} (hS : ∀ k ∉ S, h ≤ |μ k - lam|)
    {c : κ → ℂ} {c₀ : ℂ} {ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hpair : ∀ k ∈ S, ∀ l ∈ S,
      ‖star (e k) ⬝ᵥ ((Uᴴ * J * U) *ᵥ e l) - (if k = l then c k else 0)‖ ≤ ε)
    (hcen : ∀ k ∈ S, ‖c k - c₀‖ ≤ ε') :
    ‖star v ⬝ᵥ (J *ᵥ v) - c₀‖ ≤
      S.card * ε + ε' + 2 * ((rg + 4 * K ^ 2 / |ρ|) / h) +
        (1 + ‖c₀‖) * ((rg + 4 * K ^ 2 / |ρ|) / h) ^ 2 +
        2 * K / |ρ| * (2 + 2 * K / |ρ|) + 2 * (2 * K / |ρ|) * ‖c₀‖ := by
  have hρ0 : 0 < |ρ| := by linarith
  have hρne : ρ ≠ 0 := abs_pos.mp hρ0
  set x := star w ⬝ᵥ v with hxdef
  set y := Uᴴ *ᵥ v with hydef
  set q := 2 * K / |ρ| with hq
  have hq0 : 0 ≤ q := by positivity
  have hq2 : q ≤ 1 / 2 := by
    rw [hq, div_le_iff₀ hρ0]; linarith
  have hx : ‖x‖ ≤ q := largeRho_component_le hM hw hv hρne hlam heig
  have hdec := decomp_of_compl hcompl v
  -- `σ = ‖y‖ ∈ [1 - |x|, 1]`
  set σ := vnorm y with hσ
  have hσ1 : σ ≤ 1 := by
    refine (vnorm_mulVec_le _ _).trans ?_
    rw [vnorm_of_sqNorm_one hv, mul_one]
    exact opNorm_conjTranspose_le_one_of_isometry hUU
  have hσlo : 1 - ‖x‖ ≤ σ := by
    have hUy : U *ᵥ y = v - x • w := by rw [hdec]; abel
    have h1 : vnorm v ≤ vnorm (U *ᵥ y) + vnorm (x • w) := by
      have := vnorm_add_le (U *ᵥ y) (x • w)
      rwa [← hdec] at this
    rw [vnorm_isometry hUU, vnorm_of_sqNorm_one hv, vnorm_smul, vnorm_of_sqNorm_one hw,
      mul_one] at h1
    linarith
  have hσ0 : 1 / 2 ≤ σ := by linarith
  have hσpos : 0 < σ := by linarith
  -- the normalized compressed vector
  set yh : κ → ℂ := ((σ⁻¹ : ℝ) : ℂ) • y with hyh
  have hyh1 : sqNorm yh = 1 := by
    rw [← vnorm_sq, hyh, vnorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hσpos), ← hσ, inv_mul_cancel₀ hσpos.ne']
    norm_num
  have hres := largeRho_compressed_residual_le hM hUU hUw hcompl hw heig
  rw [← hydef] at hres
  have happrox : vnorm ((Uᴴ * M * U - (lam : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ yh) ≤
      4 * K ^ 2 / |ρ| := by
    rw [hyh, mulVec_smul, vnorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hσpos)]
    have h1 : σ⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hσpos two_pos]; linarith
    have h2 : K * ‖x‖ ≤ K * q := mul_le_mul_of_nonneg_left hx hK.le
    have h3 : K * q = 2 * K ^ 2 / |ρ| := by rw [hq]; ring
    calc σ⁻¹ * vnorm ((Uᴴ * M * U - (lam : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y)
        ≤ 2 * (K * ‖x‖) :=
          mul_le_mul h1 hres (vnorm_nonneg _) (by norm_num)
      _ ≤ 2 * (2 * K ^ 2 / |ρ|) := by rw [← h3]; linarith
      _ = 4 * K ^ 2 / |ρ| := by ring
  have hJc : ‖Uᴴ * J * U‖ ≤ 1 := by
    have h1 := opNorm_conjTranspose_le_one_of_isometry hUU
    have h2 := opNorm_le_one_of_isometry hUU
    calc ‖Uᴴ * J * U‖ ≤ ‖Uᴴ * J‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖J‖) * ‖U‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * 1) * 1 := by gcongr
      _ = 1 := by norm_num
  have hwin := window_transfer_approx hAhat he heigA hJc hyh1 (by positivity) hrg hh happrox
    hBA hS hε hε' hpair hcen
  -- back from `yh` to `y`, then to `v`
  set Φ := S.card * ε + ε' + 2 * ((rg + 4 * K ^ 2 / |ρ|) / h) +
    (1 + ‖c₀‖) * ((rg + 4 * K ^ 2 / |ρ|) / h) ^ 2 with hΦ
  have hyq : star y ⬝ᵥ ((Uᴴ * J * U) *ᵥ y) =
      ((σ ^ 2 : ℝ) : ℂ) * (star yh ⬝ᵥ ((Uᴴ * J * U) *ᵥ yh)) := by
    rw [hyh, mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal]
    have hσne : (σ : ℂ) ≠ 0 := by exact_mod_cast hσpos.ne'
    push_cast
    field_simp
  have hy_le : ‖star y ⬝ᵥ ((Uᴴ * J * U) *ᵥ y) - c₀‖ ≤ Φ + 2 * q * ‖c₀‖ := by
    have e2 : star y ⬝ᵥ ((Uᴴ * J * U) *ᵥ y) - c₀ =
        ((σ ^ 2 : ℝ) : ℂ) * (star yh ⬝ᵥ ((Uᴴ * J * U) *ᵥ yh) - c₀) -
          ((1 - σ ^ 2 : ℝ) : ℂ) * c₀ := by
      rw [hyq]; push_cast; ring
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have hs2 : |σ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]; nlinarith
    have hs3 : |1 - σ ^ 2| ≤ 2 * q := by
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith [norm_nonneg x]
    have hΦ0 : 0 ≤ ‖star yh ⬝ᵥ ((Uᴴ * J * U) *ᵥ yh) - c₀‖ := norm_nonneg _
    have t1 : |σ ^ 2| * ‖star yh ⬝ᵥ ((Uᴴ * J * U) *ᵥ yh) - c₀‖ ≤ 1 * Φ :=
      mul_le_mul hs2 hwin hΦ0 zero_le_one
    have t2 : |1 - σ ^ 2| * ‖c₀‖ ≤ 2 * q * ‖c₀‖ :=
      mul_le_mul_of_nonneg_right hs3 (norm_nonneg _)
    linarith
  have hov := largeRho_overlap_le hJ hw hv hdec
  have hov' : ‖x‖ * (2 + ‖x‖) ≤ q * (2 + q) :=
    mul_le_mul hx (by linarith) (by positivity) hq0
  calc ‖star v ⬝ᵥ (J *ᵥ v) - c₀‖
      ≤ ‖star v ⬝ᵥ (J *ᵥ v) - star y ⬝ᵥ ((Uᴴ * J * U) *ᵥ y)‖ +
          ‖star y ⬝ᵥ ((Uᴴ * J * U) *ᵥ y) - c₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ q * (2 + q) + (Φ + 2 * q * ‖c₀‖) := add_le_add (hov.trans hov') hy_le
    _ = _ := by rw [hΦ, hq]; ring

end Full

/-!
## The compressed fresh noise
-/

section Law

variable (p : Parameters)

/-- The compressed variance `s' = s(1 - 1/(2W))`. -/
def compressVar (s : ℝ) : ℝ := s * (1 - 1 / (2 * (p.W : ℝ)))

theorem compressVar_pos {s : ℝ} (hs : 0 < s) : 0 < compressVar p s := by
  unfold compressVar
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have : 1 / (2 * (p.W : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have : 0 < 1 - 1 / (2 * (p.W : ℝ)) := by linarith
  positivity

/-- The scaled sample `W ↦ √s' W` on the compressed block `Fin (2W - 1)`. -/
def compressSample (s : ℝ) (W : CEH.SourceHermitian (2 * p.W - 1)) :
    Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ :=
  (((Real.sqrt (compressVar p s)) : ℝ) : ℂ) • W.1

theorem measurableEmbedding_compressSample {s : ℝ} (hs : 0 < s) :
    MeasurableEmbedding (compressSample p s) := by
  have hc : (((Real.sqrt (compressVar p s)) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (compressVar_pos p hs)).ne'
  have h1 : MeasurableEmbedding (Subtype.val : CEH.SourceHermitian (2 * p.W - 1) →
      Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ) :=
    MeasurableEmbedding.subtype_coe measurableSet_isHermitian
  exact (MeasurableEquiv.smul₀ _ hc).measurableEmbedding.comp h1

/-- **The compressed fresh noise** (`CompressedGUELawBridgeStatement`): for an
isometry `U : Fin (2W - 1) → PairSite` and every set `T` of Hermitian samples,
`GUE_{2W}(s/2W){G : U*GU ∈ √s' · T} ≤ gueSourceLaw (2W - 1) T`. -/
theorem gue_compress_preimage_le (hComp : CompressedGUELawBridgeStatement) (i : ZMod p.n)
    {s : ℝ} (hs : 0 < s) (U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ) (hU : Uᴴ * U = 1)
    (T : Set (CEH.SourceHermitian (2 * p.W - 1))) :
    gueMeasure (PairSite p i) (pairTime p s) {G | Uᴴ * G * U ∈ compressSample p s '' T} ≤
      gueSourceLaw (2 * p.W - 1) T := by
  have hf : Measurable fun G : PairMatrix p i => Uᴴ * G * U :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have h := Measure.le_map_apply (μ := gueMeasure (PairSite p i) (pairTime p s)) hf.aemeasurable
    (compressSample p s '' T)
  rw [hComp p i s hs U hU] at h
  have e : (gueSourceLaw (2 * p.W - 1)).map
      (fun W => (((Real.sqrt (s * (1 - 1 / (2 * (p.W : ℝ))))) : ℝ) : ℂ) • W.1) =
      (gueSourceLaw (2 * p.W - 1)).map (compressSample p s) := rfl
  rw [e, (measurableEmbedding_compressSample p hs).map_apply,
    (measurableEmbedding_compressSample p hs).injective.preimage_image] at h
  exact h

/-- **Eigenstate thermalization on the compressed block**, from `ExternalETH` at `N = 2W - 1`,
variance `s' = s(1 - 1/(2W))`, and `CompressedGUELawBridgeStatement`. Fixed
`A, C, [sLo, sHi], r, K_r` first; then `β₀`; then `0 < ξ < β < β₀`, `ε, D > 0`; then `N₀`.
Uniformly in `p, i` with `N₀ ≤ 2W - 1`, `s > 0` with `s' ∈ [sLo, sHi]`, compressed
deformations `F` with `s'^{-1/2}‖F‖ ≤ C (2W-1)^A`, MDE branches `M` with a regular window at `E₀`,
typical spacings, eigenpair selections, Hermitian contractions `J` and isometries `U`: the
compressed fresh noise `U*GU` (law `√s' · GUE`, `CompressedGUELawBridgeStatement`) lies in
`√s' · ethBadEvent` with `GUE_{2W}(s/2W)`-probability at most `(2W - 1)^{-D}`.
-/
theorem gue_compress_ethBad_le (hETH : ExternalETH) (hComp : CompressedGUELawBridgeStatement)
    (A C sLo sHi r Kr : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hKr : 0 < Kr) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ξ : ℝ, 0 < ξ → ξ < β → β < β₀ → ∀ ε D : ℝ, 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W - 1 → ∀ s : ℝ, 0 < s →
        compressVar p s ∈ Icc sLo sHi →
        ∀ F : CEH.SourceHermitian (2 * p.W - 1),
          (Real.sqrt (compressVar p s))⁻¹ * ‖F.1‖ ≤ C * ((2 * p.W - 1 : ℕ) : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt (compressVar p s)) F) (E₀ : ℝ),
          RegularWindow M E₀ r Kr →
        ∀ (spacing : CEH.TypicalSpacing M) (sel : CEH.EigenpairSelection (2 * p.W - 1))
          (J : CEH.SourceMatrix (2 * p.W - 1)), J.IsHermitian → ‖J‖ ≤ 1 →
        ∀ U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ, Uᴴ * U = 1 →
          gueMeasure (PairSite p i) (pairTime p s)
              {G | Uᴴ * G * U ∈ compressSample p s '' ethBadEvent M spacing sel E₀ β ξ ε J} ≤
            ENNReal.ofReal (((2 * p.W - 1 : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨β₀, hβ₀, hE⟩ := hETH A C sLo sHi r Kr hsLo hsHi hr hKr
  refine ⟨β₀, hβ₀, fun β ξ hξ hξβ hβ ε D hε hD => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hE β ξ hξ hξβ hβ ε D hε hD
  refine ⟨N₀, fun p i hN s hs hsI F hF M E₀ hreg spacing sel J hJ hJn U hU => ?_⟩
  exact (gue_compress_preimage_le p hComp i hs U hU _).trans
    (hN₀ (2 * p.W - 1) hN (compressVar p s) hsI F hF M E₀ hreg spacing sel J hJ hJn)

end Law

end BlockBand.LocalWindow.ProofPartTwo
