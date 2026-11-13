module

public import BlockBand.LocalWindow.ProofPartTwoLargeRho
public import BlockBand.LocalWindow.ProofPartTwoRankOne

/-!
# The limiting compression of the observables at large `ρ`

As the rank-one coupling `ρ` of `F(E) - E = M + ρww*` tends to `±∞`, a Lipschitz spectral
function of `M + ρww*` converges, with a polynomial rate, to its limiting compression; this
handles the large-`ρ` branch of part (ii) of the physical local-window lemma.

**The limiting compression.** Write `F(E) - E = M + ρww*` (`M = F_reg(E) - E` Hermitian,
`‖M‖ ≤ K`, `w` unit) and let `U : ℂ^κ → w^⊥` be an isometry (`U*U = 1`, `U*w = 0`,
`UU* + ww* = 1`). For `|f| ≤ 1` and `f` `L`-Lipschitz, as `ρ → ±∞`,
`f(M + ρww*) → f(±∞) ww* + U f(U*MU) U*` (`limitCompression U w f(±∞) f(U*MU)`). Its compression
to `w^⊥` is `f(U*MU)`, with the quantitative rate
`‖U* f(M + ρww*) U - f(U*MU)‖ ≤ √|ι| (3LK² + 4K)/|ρ|` for `6K ≤ |ρ|`, which needs neither the
limits `f(±∞)` nor smoothness beyond Lipschitz (the finite-limits clause of
`IsSpectralTest` is used only for the `w`-entry `w* f(·) w → f(±∞)`). The rate is polynomial
(`|ι| = 2W`). Proof: eigenvectors `v_a` of `M + ρww*` with `|μ_a| < 2K` have `|w*v_a| ≤ 3K/|ρ|`
and `‖(U*MU - μ_a)U*v_a‖ ≤ K|w*v_a|`; those with `|μ_a| ≥ 2K` have `|μ_a - ρ| ≤ 2K` (unless
`w*v_a = 0`) and `‖U*v_a‖ ≤ 2K|w*v_a|/|ρ|`; then `‖(f(U*MU) - f(μ_a))U*v_a‖ ≤ (3LK² + 4K)/|ρ|`
for every `a`, and summing over the eigenbasis costs `√|ι|`. (This eigenvector argument replaces
a resolvent representation; no gap condition.)

## Main results

* `vnorm_spectralFn_sub_smul_le`: `‖(f(B) - f(μ))y‖ ≤ L ‖(B - μ)y‖` (Hermitian `B`).
* `largeRho_component_le_general`, **`largeRho_far_eig_le`**: the near/far eigenvector bounds.
* **`vnorm_compress_spectralFn_eig_le`**: `‖(f(U*MU) - f(μ))U*v‖ ≤ (3LK² + 4K)/|ρ|`.
* `opNorm_compress_spectralFn_sub_le`: the eigenvector bounds give the operator bound.
* **`opNorm_compress_spectralFn_largeRho_le`**, **`opNorm_compress_spectralTest_largeRho_le`**:
  `‖U* f(M + ρww*) U - f(U*MU)‖ ≤ √|ι| (3LK² + 4K)/|ρ|` (`L = K₀` for spectral tests).
* **`vnorm_cross_spectralFn_largeRho_le`**: `‖U* f(M + ρww*) w‖ ≤ 3|ι|K/|ρ|`.
* **`norm_wcomp_spectralFn_largeRho_sub_le`**: `|w* f(M + ρww*) w - c| ≤ 18|ι|K²/ρ² + θ` when
  `|f - c| ≤ θ` on `[ρ - 2K, ρ + 2K]`; **`tendsto_wcomp_spectralFn_atTop`**,
  `tendsto_wcomp_spectralFn_atBot`:
  `w* f(M + ρww*) w → f(±∞)`.
* `limitCompression`, **`opNorm_sub_limitCompression_le`**,
  **`opNorm_spectralFn_sub_limitCompression_le`**: the operator distance to the limit.
* **`tendsto_spectralTest_limitCompression_atTop`**, `tendsto_spectralTest_limitCompression_atBot`:
  `f(M + ρww*) → f(±∞)ww* + Uf(U*MU)U*`.
* `compress_hermitian_contraction` (class (a): `U*BU` is a Hermitian contraction, no `ρ`).
* `largeRho_window_transfer_limit` (pair error `ε + δ`), **`largeRho_window_transfer_limit_add`**
  (additive error `δ + 8K/|ρ|`): `largeRho_window_transfer` with window data for a compressed
  contraction `J_c`, `‖U*JU - J_c‖ ≤ δ`.
* **`largeRho_window_transfer_spectralTest`**: the large-`ρ` branch for `J = f(M' + ρww*)` from
  the window data of `J_c = f(U*M'U)`, additive error `√|ι|(3K₀K'² + 4K')/|ρ| + 8K/|ρ|`.
* **`isWindowObservable_compress_largeRho`**: for an observable of `IsWindowObservable` at
  `(ω, E)` with `schurK0 ω E = M' + ρww*`: class (a) compresses to `U*B₀(ω)U` exactly, class (b)
  to `f(U*M'U)` within `√(2W)(3K₀K'² + 4K')/|ρ|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator

section Generic

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Cauchy–Schwarz: `|x*y| ≤ ‖x‖ ‖y‖`. -/
theorem norm_star_dotProduct_le (x y : ι → ℂ) : ‖star x ⬝ᵥ y‖ ≤ vnorm x * vnorm y := by
  have h : star x ⬝ᵥ y = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [h, vnorm_eq, vnorm_eq]
  exact norm_inner_le_norm _ _

/-- `|x*Ay| ≤ ‖A‖ ‖x‖ ‖y‖`. -/
theorem norm_bilinear_le (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    ‖star x ⬝ᵥ (A *ᵥ y)‖ ≤ ‖A‖ * vnorm x * vnorm y := by
  refine (norm_star_dotProduct_le x (A *ᵥ y)).trans ?_
  have := vnorm_mulVec_le A y
  have := vnorm_nonneg x
  nlinarith [vnorm_nonneg y, norm_nonneg A]

/-- `‖u‖ ≤ c‖v‖` from `‖u‖² ≤ c²‖v‖²`. -/
theorem vnorm_le_of_sqNorm_le {u v : ι → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : sqNorm u ≤ c ^ 2 * sqNorm v) : vnorm u ≤ c * vnorm v := by
  unfold vnorm
  calc Real.sqrt (sqNorm u) ≤ Real.sqrt (c ^ 2 * sqNorm v) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt (sqNorm v) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- `sqNorm ((V diag(d) V* - c) y) = Σ_b |d_b - c|² |(V* y)_b|²` for unitary `V`. -/
theorem sqNorm_conj_diagonal_sub_smul {V : Matrix κ κ ℂ} (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1)
    (d : κ → ℂ) (c : ℂ) (y : κ → ℂ) :
    sqNorm ((V * diagonal d * Vᴴ - c • (1 : Matrix κ κ ℂ)) *ᵥ y) =
      ∑ b, ‖d b - c‖ ^ 2 * ‖(Vᴴ *ᵥ y) b‖ ^ 2 := by
  have e : V * diagonal d * Vᴴ - c • (1 : Matrix κ κ ℂ) = V * diagonal (fun b => d b - c) * Vᴴ := by
    have : c • (1 : Matrix κ κ ℂ) = V * Matrix.diagonal (fun _ => c) * Vᴴ := by
      rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hV']
    rw [this, ← Matrix.sub_mul, ← Matrix.mul_sub, ← diagonal_sub]
  rw [e, ← mulVec_mulVec, ← mulVec_mulVec, sqNorm_unitary_mulVec hV]
  unfold sqNorm
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mulVec_diagonal, norm_mul, mul_pow]

/-- **Pointwise Lipschitz bound of the functional calculus**: for Hermitian `B`, an
`L`-Lipschitz `f` and a real `μ`, `‖(f(B) - f(μ)) y‖ ≤ L ‖(B - μ) y‖`. -/
theorem vnorm_spectralFn_sub_smul_le {B : Matrix κ κ ℂ} (hB : B.IsHermitian) {f : ℝ → ℝ}
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) (μ : ℝ) (y : κ → ℂ) :
    vnorm ((BlockBand.LocalWindow.spectralFn f B - ((f μ : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y) ≤
      L * vnorm ((B - (μ : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y) := by
  set V := (hB.eigenvectorUnitary : Matrix κ κ ℂ)
  have hBe : B = V * diagonal (fun a => ((hB.eigenvalues a : ℝ) : ℂ)) * Vᴴ := by
    conv_lhs => rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have e2 : (B - (μ : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y =
      (V * diagonal (fun a => ((hB.eigenvalues a : ℝ) : ℂ)) * Vᴴ - (μ : ℂ) • 1) *ᵥ y := by
    rw [← hBe]
  rw [spectralFn_of_isHermitian hB, cfc_eq_conj, e2]
  refine vnorm_le_of_sqNorm_le hL ?_
  rw [sqNorm_conj_diagonal_sub_smul (unitary_conj_mul_self hB) (unitary_mul_conj_self hB),
    sqNorm_conj_diagonal_sub_smul (unitary_conj_mul_self hB) (unitary_mul_conj_self hB),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hf _ _) 2

/-- The general component bound: `|ρ| |w*v| ≤ |μ| + K` for a unit eigenvector `v` of
`M + ρww*` with eigenvalue `μ` (`‖M‖ ≤ K`, `w` unit). -/
theorem largeRho_component_le_general {M : Matrix ι ι ℂ} {K : ℝ} (hM : ‖M‖ ≤ K) {w v : ι → ℂ}
    (hw : sqNorm w = 1) (hv : sqNorm v = 1) {ρ μ : ℝ}
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (μ : ℂ) • v) :
    |ρ| * ‖star w ⬝ᵥ v‖ ≤ |μ| + K := by
  have e : ((ρ : ℂ) * (star w ⬝ᵥ v)) • w = (μ : ℂ) • v - M *ᵥ v := by
    rw [add_mulVec, smul_mulVec, vecMulVec_star_mulVec, smul_smul] at heig
    rw [← heig]; abel
  have h1 : vnorm (((ρ : ℂ) * (star w ⬝ᵥ v)) • w) = |ρ| * ‖star w ⬝ᵥ v‖ := by
    rw [vnorm_smul, vnorm_of_sqNorm_one hw, mul_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
  have h2 : vnorm ((μ : ℂ) • v - M *ᵥ v) ≤ |μ| + K := by
    refine (vnorm_sub_le _ _).trans ?_
    rw [vnorm_smul, vnorm_of_sqNorm_one hv, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := (vnorm_mulVec_le M v).trans (by rw [vnorm_of_sqNorm_one hv, mul_one])
    linarith
  rw [e] at h1
  linarith

/-- The compression `U*MU` of a Hermitian `M` by an isometry is Hermitian with
`‖U*MU‖ ≤ ‖M‖`. -/
theorem opNorm_compress_le {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) (M : Matrix ι ι ℂ) :
    ‖Uᴴ * M * U‖ ≤ ‖M‖ := by
  have h1 := opNorm_conjTranspose_le_one_of_isometry hUU
  have h2 := opNorm_le_one_of_isometry hUU
  calc ‖Uᴴ * M * U‖ ≤ ‖Uᴴ * M‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Uᴴ‖ * ‖M‖) * ‖U‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖M‖) * 1 := by gcongr
    _ = ‖M‖ := by ring

/-- `‖(X - c) y‖ ≤ (1 + |c|) ‖y‖` for a contraction `X`. -/
theorem vnorm_sub_smul_le_of_contraction {X : Matrix κ κ ℂ} (hX : ‖X‖ ≤ 1) (c : ℝ)
    (y : κ → ℂ) :
    vnorm ((X - (c : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y) ≤ (1 + |c|) * vnorm y := by
  rw [sub_mulVec, smul_mulVec, one_mulVec]
  refine (vnorm_sub_le _ _).trans ?_
  rw [vnorm_smul, Complex.norm_real, Real.norm_eq_abs]
  have := vnorm_mulVec_le X y
  have : ‖X‖ * vnorm y ≤ 1 * vnorm y := mul_le_mul_of_nonneg_right hX (vnorm_nonneg y)
  linarith

/-- **The far eigenvectors**: with the hypotheses of the block bounds,
`6K ≤ |ρ|` and an eigenvalue `|μ| ≥ 2K`, `|ρ - μ| |w*v| ≤ 2K |w*v|` (so `|μ - ρ| ≤ 2K` unless
`w*v = 0`) and `‖U*v‖ ≤ 2K |w*v|/|ρ|`. -/
theorem largeRho_far_eig_le {M : Matrix ι ι ℂ} {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K)
    {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w v : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) {ρ μ : ℝ}
    (hρ : 6 * K ≤ |ρ|) (hμ : 2 * K ≤ |μ|)
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (μ : ℂ) • v) :
    |ρ - μ| * ‖star w ⬝ᵥ v‖ ≤ 2 * K * ‖star w ⬝ᵥ v‖ ∧
      vnorm (Uᴴ *ᵥ v) ≤ 2 * K * ‖star w ⬝ᵥ v‖ / |ρ| := by
  have hρ0 : 0 < |ρ| := by linarith
  set x := star w ⬝ᵥ v with hxdef
  set y := Uᴴ *ᵥ v with hydef
  set B₀ := Uᴴ * M * U with hB₀
  have hB₀n : ‖B₀‖ ≤ K := (opNorm_compress_le hUU M).trans hM
  have hres : vnorm ((B₀ - (μ : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y) ≤ K * ‖x‖ :=
    largeRho_compressed_residual_le hM hUU hUw hcompl hw heig
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hy0 : 0 ≤ vnorm y := vnorm_nonneg _
  -- `(|μ| - K) ‖y‖ ≤ K |x|`
  have hlow : (|μ| - K) * vnorm y ≤ K * ‖x‖ := by
    have e : (μ : ℂ) • y = B₀ *ᵥ y - (B₀ - (μ : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y := by
      rw [sub_mulVec, smul_mulVec, one_mulVec]; abel
    have h1 : |μ| * vnorm y ≤ K * vnorm y + K * ‖x‖ := by
      have h := vnorm_sub_le (B₀ *ᵥ y) ((B₀ - (μ : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y)
      rw [← e, vnorm_smul, Complex.norm_real, Real.norm_eq_abs] at h
      have h3 := vnorm_mulVec_le B₀ y
      have h4 : ‖B₀‖ * vnorm y ≤ K * vnorm y := mul_le_mul_of_nonneg_right hB₀n hy0
      linarith
    linarith
  have hyx : vnorm y ≤ ‖x‖ := by nlinarith
  -- the `w`-equation `(ρ - μ) x = -w*Mv`
  have hweq : |ρ - μ| * ‖x‖ ≤ 2 * K * ‖x‖ := by
    have hww : star w ⬝ᵥ w = 1 := by rw [star_dotProduct_self, hw]; simp
    have e1 : star w ⬝ᵥ (M *ᵥ v) + (ρ : ℂ) * x = (μ : ℂ) * x := by
      have h := congrArg (star w ⬝ᵥ ·) heig
      simp only [add_mulVec, smul_mulVec, vecMulVec_star_mulVec, dotProduct_add,
        dotProduct_smul, smul_eq_mul, hww, mul_one] at h
      rw [← hxdef] at h
      exact h
    have hdec := decomp_of_compl hcompl v
    rw [← hydef, ← hxdef] at hdec
    have e2 : ((ρ - μ : ℝ) : ℂ) * x = -(star w ⬝ᵥ (M *ᵥ (U *ᵥ y)) + x * (star w ⬝ᵥ (M *ᵥ w))) := by
      have : star w ⬝ᵥ (M *ᵥ v) = star w ⬝ᵥ (M *ᵥ (U *ᵥ y)) + x * (star w ⬝ᵥ (M *ᵥ w)) := by
        conv_lhs => rw [hdec]
        rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
      rw [← this]; push_cast; linear_combination e1
    have b1 := norm_bilinear_le M w (U *ᵥ y)
    rw [vnorm_of_sqNorm_one hw, vnorm_isometry hUU, mul_one] at b1
    have b2 := norm_bilinear_le M w w
    rw [vnorm_of_sqNorm_one hw, mul_one, mul_one] at b2
    have h := congrArg norm e2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg] at h
    have h3 : ‖star w ⬝ᵥ (M *ᵥ (U *ᵥ y)) + x * (star w ⬝ᵥ (M *ᵥ w))‖ ≤ K * vnorm y + ‖x‖ * K := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have : ‖M‖ * vnorm y ≤ K * vnorm y := mul_le_mul_of_nonneg_right hM hy0
      have : ‖x‖ * ‖star w ⬝ᵥ (M *ᵥ w)‖ ≤ ‖x‖ * K :=
        mul_le_mul_of_nonneg_left (b2.trans hM) hx0
      linarith
    nlinarith
  have hy2 : vnorm y ≤ 2 * K * ‖x‖ / |ρ| := by
    rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx] at hlow ⊢
      have : vnorm y ≤ 0 := by nlinarith
      simp only [mul_zero, zero_div]; exact this
    · have h1 : |ρ - μ| ≤ 2 * K := le_of_mul_le_mul_right hweq hx
      have h2 : |ρ| - 2 * K ≤ |μ| := by
        have := abs_sub_abs_le_abs_sub ρ μ
        linarith
      rw [le_div_iff₀ hρ0]
      nlinarith
  exact ⟨hweq, hy2⟩

/-- **One eigenvector of the large rank-one deformation.** Let `M` be Hermitian
with `‖M‖ ≤ K` (`K > 0`), `w` unit, `U` an isometry onto `w^⊥` (`U*U = 1`, `U*w = 0`,
`UU* + ww* = 1`), `6K ≤ |ρ|`, and `v` a unit eigenvector of `M + ρww*` with eigenvalue `μ`.
For `f` with `|f| ≤ 1` and Lipschitz constant `L ≥ 0`, with `B₀ = U*MU`,
`‖(f(B₀) - f(μ)) U*v‖ ≤ (3LK² + 4K)/|ρ|`.
(If `|μ| < 2K`: `|w*v| ≤ 3K/|ρ|` and `‖(B₀ - μ)U*v‖ ≤ K|w*v|`; if `|μ| ≥ 2K`: `|μ - ρ| ≤ 2K`
and `‖U*v‖ ≤ 2K|w*v|/|ρ|`.) -/
theorem vnorm_compress_spectralFn_eig_le {M : Matrix ι ι ℂ} (hMh : M.IsHermitian) {K : ℝ}
    (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w v : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    (hv : sqNorm v = 1) {ρ μ : ℝ} (hρ : 6 * K ≤ |ρ|)
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (μ : ℂ) • v) {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) (hf1 : ∀ x, |f x| ≤ 1) :
    vnorm ((BlockBand.LocalWindow.spectralFn f (Uᴴ * M * U) -
        ((f μ : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ (Uᴴ *ᵥ v)) ≤ (3 * L * K ^ 2 + 4 * K) / |ρ| := by
  have hρ0 : 0 < |ρ| := by linarith
  set x := star w ⬝ᵥ v with hxdef
  set y := Uᴴ *ᵥ v with hydef
  set B₀ := Uᴴ * M * U with hB₀
  have hB₀h : B₀.IsHermitian := isHermitian_conjTranspose_mul_mul U hMh
  have hB₀n : ‖B₀‖ ≤ K := (opNorm_compress_le hUU M).trans hM
  have hres : vnorm ((B₀ - (μ : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y) ≤ K * ‖x‖ :=
    largeRho_compressed_residual_le hM hUU hUw hcompl hw heig
  have hcomp := largeRho_component_le_general hM hw hv heig
  have hx1 : ‖x‖ ≤ 1 := by
    have := norm_star_dotProduct_le w v
    rwa [vnorm_of_sqNorm_one hw, vnorm_of_sqNorm_one hv, one_mul] at this
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have hy0 : 0 ≤ vnorm y := vnorm_nonneg _
  have hrhs : 0 ≤ 3 * L * K ^ 2 / |ρ| := by positivity
  rcases lt_or_ge |μ| (2 * K) with hμ | hμ
  · -- near eigenvalue
    have h1 := vnorm_spectralFn_sub_smul_le hB₀h hL hf μ y
    have hx3 : ‖x‖ ≤ 3 * K / |ρ| := by
      rw [le_div_iff₀ hρ0]; linarith
    have h2 : L * vnorm ((B₀ - (μ : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ y) ≤ L * (K * (3 * K / |ρ|)) :=
      mul_le_mul_of_nonneg_left (hres.trans (mul_le_mul_of_nonneg_left hx3 hK.le)) hL
    have e : L * (K * (3 * K / |ρ|)) = 3 * L * K ^ 2 / |ρ| := by ring
    have h4 : 0 ≤ 4 * K / |ρ| := by positivity
    rw [add_div]
    linarith
  · -- far eigenvalue
    obtain ⟨-, hy2⟩ := largeRho_far_eig_le hK hM hUU hUw hcompl hw hρ hμ heig
    have hf0 := vnorm_sub_smul_le_of_contraction
      (BlockBand.LocalWindow.ProofPartTwo.opNorm_spectralFn_le hf1 B₀) (f μ) y
    have hfμ : 1 + |f μ| ≤ 2 := by linarith [hf1 μ]
    have h5 : (1 + |f μ|) * vnorm y ≤ 2 * (2 * K * ‖x‖ / |ρ|) :=
      mul_le_mul hfμ hy2 hy0 (by norm_num)
    have h6 : 2 * (2 * K * ‖x‖ / |ρ|) ≤ 4 * K / |ρ| := by
      rw [show 2 * (2 * K * ‖x‖ / |ρ|) = 4 * K * ‖x‖ / |ρ| by ring]
      exact div_le_div_of_nonneg_right (by nlinarith) hρ0.le
    rw [add_div]
    linarith

/-- `y*(Zu) = (Zy)*u` for Hermitian `Z`. -/
theorem star_dotProduct_mulVec_herm {Z : Matrix κ κ ℂ} (hZ : Z.IsHermitian) (y u : κ → ℂ) :
    star y ⬝ᵥ (Z *ᵥ u) = star (Z *ᵥ y) ⬝ᵥ u := by
  rw [star_mulVec, ← dotProduct_mulVec, hZ.eq]

/-- `r • 1` is Hermitian for real `r`. -/
theorem isHermitian_real_smul_one (r : ℝ) : (((r : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- The rows of `V*` for `V` the eigenvector unitary: `(V* z)_a = e_a* z`. -/
theorem eigenvectorUnitary_conjTranspose_mulVec_apply {N : Matrix ι ι ℂ} (hN : N.IsHermitian)
    (z : ι → ℂ) (a : ι) :
    ((hN.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *ᵥ z) a = star ⇑(hN.eigenvectorBasis a) ⬝ᵥ z := by
  simp only [mulVec, dotProduct, conjTranspose_apply, IsHermitian.eigenvectorUnitary_apply,
    Pi.star_apply]

/-- **Compression of a spectral function from the eigenvector bounds**: for Hermitian `N` on `ι`
(eigenvalues `μ_a`, orthonormal eigenvectors `v_a`), an isometry `U` (`U*U = 1`) and Hermitian
`B` on `κ`, if `‖(f(B) - f(μ_a)) U*v_a‖ ≤ β` for every `a`, then
`‖U* f(N) U - f(B)‖ ≤ √|ι| β`. -/
theorem opNorm_compress_spectralFn_sub_le {N : Matrix ι ι ℂ} (hN : N.IsHermitian)
    {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {B : Matrix κ κ ℂ} (f : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ a, vnorm ((BlockBand.LocalWindow.spectralFn f B -
        ((f (hN.eigenvalues a) : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)) *ᵥ
          (Uᴴ *ᵥ ⇑(hN.eigenvectorBasis a))) ≤ β) :
    ‖Uᴴ * BlockBand.LocalWindow.spectralFn f N * U - BlockBand.LocalWindow.spectralFn f B‖ ≤
      Real.sqrt (Fintype.card ι) * β := by
  set V := (hN.eigenvectorUnitary : Matrix ι ι ℂ) with hV
  set X := BlockBand.LocalWindow.spectralFn f N with hX
  set F := BlockBand.LocalWindow.spectralFn f B with hF
  set d : ι → ℂ := fun a => ((f (hN.eigenvalues a) : ℝ) : ℂ) with hd
  have hXe : X = V * diagonal d * Vᴴ := by
    rw [hX, spectralFn_of_isHermitian hN, cfc_eq_conj]
  have hVX : Vᴴ * X = diagonal d * Vᴴ := by
    rw [hXe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, unitary_conj_mul_self hN, Matrix.one_mul]
  refine opNorm_le_of_sqNorm (by positivity) fun u => ?_
  set g := X *ᵥ (U *ᵥ u) - U *ᵥ (F *ᵥ u) with hg
  have e1 : (Uᴴ * X * U - F) *ᵥ u = Uᴴ *ᵥ g := by
    rw [hg, mulVec_sub, sub_mulVec, mulVec_mulVec (M := Uᴴ) (N := U), hUU, one_mulVec,
      mulVec_mulVec, mulVec_mulVec]
  have h1 : sqNorm (Uᴴ *ᵥ g) ≤ sqNorm g := by
    rw [← vnorm_sq, ← vnorm_sq]
    have := (vnorm_mulVec_le Uᴴ g).trans
      (mul_le_of_le_one_left (vnorm_nonneg g) (opNorm_conjTranspose_le_one_of_isometry hUU))
    exact pow_le_pow_left₀ (vnorm_nonneg _) this 2
  have h2 : sqNorm g = sqNorm (Vᴴ *ᵥ g) :=
    (sqNorm_unitary_mulVec (by rw [conjTranspose_conjTranspose]; exact unitary_mul_conj_self hN)
      g).symm
  have h3 : ∀ a, ‖(Vᴴ *ᵥ g) a‖ ≤ β * vnorm u := by
    intro a
    set va := ⇑(hN.eigenvectorBasis a)
    set Z := F - d a • (1 : Matrix κ κ ℂ) with hZ
    have hZh : Z.IsHermitian := (isHermitian_spectralFn f B).sub (isHermitian_real_smul_one _)
    have e2 : (Vᴴ *ᵥ g) a = -(star (Z *ᵥ (Uᴴ *ᵥ va)) ⬝ᵥ u) := by
      have e3 : (Vᴴ *ᵥ g) a = d a * (Vᴴ *ᵥ (U *ᵥ u)) a - (Vᴴ *ᵥ (U *ᵥ (F *ᵥ u))) a := by
        rw [hg, mulVec_sub, mulVec_mulVec (M := Vᴴ) (N := X), hVX, ← mulVec_mulVec, Pi.sub_apply,
          mulVec_diagonal]
      rw [e3, eigenvectorUnitary_conjTranspose_mulVec_apply,
        eigenvectorUnitary_conjTranspose_mulVec_apply, ← star_dotProduct_mulVec_herm hZh,
        star_mulVec, ← dotProduct_mulVec, conjTranspose_conjTranspose,
        hZ, sub_mulVec, smul_mulVec, one_mulVec, mulVec_sub, mulVec_smul, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      ring
    rw [e2, norm_neg]
    refine (norm_star_dotProduct_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (h a) (vnorm_nonneg u)
  rw [e1]
  refine h1.trans (h2 ▸ ?_)
  unfold sqNorm
  calc ∑ a, ‖(Vᴴ *ᵥ g) a‖ ^ 2 ≤ ∑ _a : ι, (β * vnorm u) ^ 2 :=
        Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (h3 a) 2
    _ = (Real.sqrt (Fintype.card ι) * β) ^ 2 * ∑ k, ‖u k‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow, mul_pow,
          Real.sq_sqrt (Nat.cast_nonneg _), vnorm_sq]
        unfold sqNorm; ring

/-- The eigenvectors of a Hermitian matrix are unit vectors. -/
theorem sqNorm_eigenvectorBasis {N : Matrix ι ι ℂ} (hN : N.IsHermitian) (a : ι) :
    sqNorm ⇑(hN.eigenvectorBasis a) = 1 := by
  have h := (hN.eigenvectorBasis.orthonormal.1 a)
  have e : vnorm ⇑(hN.eigenvectorBasis a) = 1 := by
    rw [vnorm_eq, WithLp.toLp_ofLp]; exact h
  rw [← vnorm_sq, e, one_pow]

/-- The eigenvector equation with a complex scalar. -/
theorem mulVec_eigenvectorBasis_ofReal_smul {N : Matrix ι ι ℂ} (hN : N.IsHermitian) (a : ι) :
    N *ᵥ ⇑(hN.eigenvectorBasis a) = ((hN.eigenvalues a : ℝ) : ℂ) • ⇑(hN.eigenvectorBasis a) := by
  rw [hN.mulVec_eigenvectorBasis a, ← Complex.coe_smul]

/-- **The limiting compression of a spectral function.** Let `M` be Hermitian on `ι` with `‖M‖ ≤ K` (`K > 0`), `w` a unit vector, `U`
an isometry onto `w^⊥` (`U*U = 1`, `U*w = 0`, `UU* + ww* = 1`), `ρ` real with `6K ≤ |ρ|`, and
`f` with `|f| ≤ 1` and `|f a - f b| ≤ L|a - b|` (`L ≥ 0`). Then
`‖U* f(M + ρww*) U - f(U*MU)‖ ≤ √|ι| (3LK² + 4K)/|ρ|`.
So the compression of `f(M + ρww*)` to `w^⊥` tends to `f(U*MU)` at rate `O(1/|ρ|)`, uniformly
in `M, w, U, f` for fixed `K, L, |ι|`. -/
theorem opNorm_compress_spectralFn_largeRho_le {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {ρ : ℝ} (hρ : 6 * K ≤ |ρ|) {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) (hf1 : ∀ x, |f x| ≤ 1) :
    ‖Uᴴ * BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) * U -
        BlockBand.LocalWindow.spectralFn f (Uᴴ * M * U)‖ ≤
      Real.sqrt (Fintype.card ι) * ((3 * L * K ^ 2 + 4 * K) / |ρ|) := by
  have hN : (M + (ρ : ℂ) • vecMulVec w (star w)).IsHermitian := hMh.add (isHermitian_rankOne ρ w)
  have hρ0 : 0 < |ρ| := by linarith
  refine opNorm_compress_spectralFn_sub_le hN hUU f (by positivity) fun a => ?_
  exact vnorm_compress_spectralFn_eig_le hMh hK hM hUU hUw hcompl hw (sqNorm_eigenvectorBasis hN a)
    hρ (mulVec_eigenvectorBasis_ofReal_smul hN a) hL hf hf1

/-- **The limiting compression for the spectral tests** of `IsWindowObservable` class (b)
(`IsSpectralTest k K₀ f`, `k ≥ 1`): `‖U* f(M + ρww*) U - f(U*MU)‖ ≤ √|ι| (3K₀K² + 4K)/|ρ|`
under the hypotheses of `opNorm_compress_spectralFn_largeRho_le`. -/
theorem opNorm_compress_spectralTest_largeRho_le {k : ℕ} {K₀ : ℝ} {f : ℝ → ℝ}
    (hft : BlockBand.LocalWindow.IsSpectralTest k K₀ f) (hk : 1 ≤ k) {M : Matrix ι ι ℂ}
    (hMh : M.IsHermitian) {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ}
    (hUU : Uᴴ * U = 1) {w : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) {ρ : ℝ}
    (hρ : 6 * K ≤ |ρ|) :
    ‖Uᴴ * BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) * U -
        BlockBand.LocalWindow.spectralFn f (Uᴴ * M * U)‖ ≤
      Real.sqrt (Fintype.card ι) * ((3 * K₀ * K ^ 2 + 4 * K) / |ρ|) :=
  opNorm_compress_spectralFn_largeRho_le hMh hK hM hUU hUw hcompl hw hρ
    (nonneg_of_isSpectralTest hft hk) (lipschitz_of_isSpectralTest hft hk) hft.2.1

/-- **Class (a)**: the compression `U*BU` of a Hermitian contraction is a Hermitian contraction
(no dependence on `ρ`; `largeRho_window_transfer` applies to `J = B` directly). -/
theorem compress_hermitian_contraction {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1)
    {B : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB1 : ‖B‖ ≤ 1) :
    (Uᴴ * B * U).IsHermitian ∧ ‖Uᴴ * B * U‖ ≤ 1 :=
  ⟨isHermitian_conjTranspose_mul_mul U hB, (opNorm_compress_le hUU B).trans hB1⟩

/-- **Window transfer through a limiting compression**: `ProofPartTwoLargeRho.
largeRho_window_transfer` with the window pair data given for a compressed observable `J_c` on
`w^⊥` with `‖U*JU - J_c‖ ≤ δ` (for class (b), `J_c = f(U*MU)`, `δ = O(1/|ρ|)`); the pair error
becomes `ε + δ`. -/
theorem largeRho_window_transfer_limit {M : Matrix ι ι ℂ} {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K)
    {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w v : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) (hv : sqNorm v = 1)
    {ρ lam : ℝ} (hρ : 4 * K ≤ |ρ|) (hlam : |lam| ≤ K)
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (lam : ℂ) • v)
    {J : Matrix ι ι ℂ} (hJ : ‖J‖ ≤ 1) {Jc : Matrix κ κ ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hJc : ‖Uᴴ * J * U - Jc‖ ≤ δ) {Ahat : Matrix κ κ ℂ} (hAhat : Ahat.IsHermitian)
    {e : κ → κ → ℂ} (he : IsOrthonormalFamily e) {μ : κ → ℝ}
    (heigA : ∀ k, Ahat *ᵥ e k = (μ k : ℂ) • e k) {rg h : ℝ} (hrg : 0 ≤ rg) (hh : 0 < h)
    (hBA : ‖Uᴴ * M * U - Ahat‖ ≤ rg) {S : Finset κ} (hS : ∀ k ∉ S, h ≤ |μ k - lam|)
    {c : κ → ℂ} {c₀ : ℂ} {ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hpair : ∀ k ∈ S, ∀ l ∈ S,
      ‖star (e k) ⬝ᵥ (Jc *ᵥ e l) - (if k = l then c k else 0)‖ ≤ ε)
    (hcen : ∀ k ∈ S, ‖c k - c₀‖ ≤ ε') :
    ‖star v ⬝ᵥ (J *ᵥ v) - c₀‖ ≤
      S.card * (ε + δ) + ε' + 2 * ((rg + 4 * K ^ 2 / |ρ|) / h) +
        (1 + ‖c₀‖) * ((rg + 4 * K ^ 2 / |ρ|) / h) ^ 2 +
        2 * K / |ρ| * (2 + 2 * K / |ρ|) + 2 * (2 * K / |ρ|) * ‖c₀‖ := by
  have hunit : ∀ k, vnorm (e k) = 1 := fun k => by
    have h1 : star (e k) ⬝ᵥ e k = 1 := by simpa using he k k
    rw [star_dotProduct_self] at h1
    exact vnorm_of_sqNorm_one (by exact_mod_cast h1)
  refine largeRho_window_transfer hK hM hUU hUw hcompl hw hv hρ hlam heig hJ hAhat he heigA hrg hh
    hBA hS (add_nonneg hε hδ) hε' (fun k hk l hl => ?_) hcen
  have e1 : star (e k) ⬝ᵥ ((Uᴴ * J * U) *ᵥ e l) - (if k = l then c k else 0) =
      (star (e k) ⬝ᵥ (Jc *ᵥ e l) - (if k = l then c k else 0)) +
        star (e k) ⬝ᵥ ((Uᴴ * J * U - Jc) *ᵥ e l) := by
    rw [sub_mulVec, dotProduct_sub]; ring
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add (hpair k hk l hl) ?_)
  have := norm_bilinear_le (Uᴴ * J * U - Jc) (e k) (e l)
  rw [hunit, hunit, mul_one, mul_one] at this
  exact this.trans hJc

/-- **The `w`-component of the limiting compression**: under the hypotheses of
`opNorm_compress_spectralFn_largeRho_le` (no Lipschitz bound needed), if `|c| ≤ 1` and
`|f t - c| ≤ θ` whenever `|ρ - t| ≤ 2K`, then `|w* f(M + ρww*) w - c| ≤ 18|ι|K²/ρ² + θ`.
With `c = f(+∞)` (resp. `f(-∞)`), `θ → 0` as `ρ → +∞` (resp. `-∞`): this is the `w`-entry
`f(±∞)` of the limiting compression `f(±∞) ww* + U f(U*MU) U*`. -/
theorem norm_wcomp_spectralFn_largeRho_sub_le {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {ρ : ℝ} (hρ : 6 * K ≤ |ρ|) {f : ℝ → ℝ} (hf1 : ∀ x, |f x| ≤ 1) {c θ : ℝ} (hc : |c| ≤ 1)
    (hθ : 0 ≤ θ) (hfar : ∀ t, |ρ - t| ≤ 2 * K → |f t - c| ≤ θ) :
    ‖star w ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ w) -
        c‖ ≤ 18 * Fintype.card ι * K ^ 2 / ρ ^ 2 + θ := by
  have hN : (M + (ρ : ℂ) • vecMulVec w (star w)).IsHermitian := hMh.add (isHermitian_rankOne ρ w)
  have hρ0 : 0 < |ρ| := by linarith
  set V := (hN.eigenvectorUnitary : Matrix ι ι ℂ) with hV
  set d : ι → ℂ := fun a => ((f (hN.eigenvalues a) : ℝ) : ℂ) with hd
  have hXe : BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) =
      V * diagonal d * Vᴴ := by
    rw [spectralFn_of_isHermitian hN, cfc_eq_conj]
  set z := Vᴴ *ᵥ w with hz
  have hVu : Vᴴᴴ * Vᴴ = 1 := by
    rw [conjTranspose_conjTranspose]; exact unitary_mul_conj_self hN
  have hz1 : sqNorm z = 1 := by
    rw [hz, sqNorm_unitary_mulVec hVu, hw]
  have e1 : star w ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ
      w) = ∑ a, d a * ((‖z a‖ ^ 2 : ℝ) : ℂ) := by
    rw [hXe, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← conjTranspose_conjTranspose V,
      ← star_mulVec, conjTranspose_conjTranspose, ← hz]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.ofReal_pow, ← Complex.conj_mul', Complex.star_def]; ring
  have e2 : (c : ℂ) = ∑ a, (c : ℂ) * ((‖z a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.mul_sum, ← Complex.ofReal_sum]
    unfold sqNorm at hz1
    rw [hz1]; simp
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a, ‖d a * ((‖z a‖ ^ 2 : ℝ) : ℂ) - (c : ℂ) * ((‖z a‖ ^ 2 : ℝ) : ℂ)‖ ≤
      18 * K ^ 2 / ρ ^ 2 + θ * ‖z a‖ ^ 2 := by
    intro a
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      hd, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hza : ‖z a‖ = ‖star w ⬝ᵥ ⇑(hN.eigenvectorBasis a)‖ := by
      rw [hz, eigenvectorUnitary_conjTranspose_mulVec_apply, ← norm_star, star_dotProduct,
        star_star, dotProduct_comm]
    have heig := mulVec_eigenvectorBasis_ofReal_smul hN a
    have hva := sqNorm_eigenvectorBasis hN a
    have hfc : |f (hN.eigenvalues a) - c| ≤ 2 := by
      have := hf1 (hN.eigenvalues a)
      have := abs_sub (f (hN.eigenvalues a)) c
      linarith
    have hz0 : 0 ≤ ‖z a‖ ^ 2 := by positivity
    have h18 : 0 ≤ 18 * K ^ 2 / ρ ^ 2 := by positivity
    rcases lt_or_ge |hN.eigenvalues a| (2 * K) with hμ | hμ
    · have hcomp := largeRho_component_le_general hM hw hva heig
      have hx3 : ‖z a‖ ≤ 3 * K / |ρ| := by
        rw [hza, le_div_iff₀ hρ0]; linarith
      have hsq : ‖z a‖ ^ 2 ≤ 9 * K ^ 2 / ρ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hx3 2
        rwa [div_pow, sq_abs, show (3 * K) ^ 2 = 9 * K ^ 2 by ring] at this
      have : |f (hN.eigenvalues a) - c| * ‖z a‖ ^ 2 ≤ 2 * (9 * K ^ 2 / ρ ^ 2) :=
        mul_le_mul hfc hsq hz0 (by norm_num)
      have : 2 * (9 * K ^ 2 / ρ ^ 2) = 18 * K ^ 2 / ρ ^ 2 := by ring
      nlinarith
    · obtain ⟨hweq, -⟩ := largeRho_far_eig_le hK hM hUU hUw hcompl hw hρ hμ heig
      rw [← hza] at hweq
      rcases eq_or_lt_of_le (norm_nonneg (z a)) with h0 | h0
      · rw [← h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
        positivity
      · have h1 : |ρ - hN.eigenvalues a| ≤ 2 * K := le_of_mul_le_mul_right hweq h0
        have := mul_le_mul_of_nonneg_right (hfar _ h1) hz0
        linarith
  calc ∑ a, ‖d a * ((‖z a‖ ^ 2 : ℝ) : ℂ) - (c : ℂ) * ((‖z a‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∑ a, (18 * K ^ 2 / ρ ^ 2 + θ * ‖z a‖ ^ 2) := Finset.sum_le_sum fun a _ => hterm a
    _ = 18 * Fintype.card ι * K ^ 2 / ρ ^ 2 + θ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
        unfold sqNorm at hz1
        rw [hz1]; ring

/-- The far-region estimate at a large parameter: if `R ≥ max(1, 36|ι|K²/ε + 1)`, `R ≥ 6K` and
`|f t - c| < ε/2` whenever `|R' - t| ≤ 2K` (`|R'| = R`), the `w`-entry is within `ε` of `c`. -/
theorem norm_wcomp_spectralFn_largeRho_lt {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {f : ℝ → ℝ} (hf1 : ∀ x, |f x| ≤ 1) {c ε : ℝ} (hc : |c| ≤ 1) (hε : 0 < ε) {ρ : ℝ}
    (hρ6 : 6 * K ≤ |ρ|) (hρ1 : 1 ≤ |ρ|) (hρε : 36 * Fintype.card ι * K ^ 2 / ε < |ρ|)
    (hfar : ∀ t, |ρ - t| ≤ 2 * K → |f t - c| ≤ ε / 2) :
    ‖star w ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ w) -
        c‖ < ε := by
  have h := norm_wcomp_spectralFn_largeRho_sub_le hMh hK hM hUU hUw hcompl hw hρ6 hf1 hc
    (by positivity) hfar
  have hρ0 : 0 < |ρ| := by linarith
  have hsq : |ρ| ≤ ρ ^ 2 := by rw [← sq_abs]; nlinarith
  have h1 : 36 * Fintype.card ι * K ^ 2 < ε * ρ ^ 2 := by
    rw [div_lt_iff₀ hε] at hρε; nlinarith
  have h2 : 18 * Fintype.card ι * K ^ 2 / ρ ^ 2 < ε / 2 := by
    rw [div_lt_iff₀ (lt_of_lt_of_le hρ0 hsq)]; linarith
  linarith

/-- **`w* f(M + ρww*) w → f(+∞)` as `ρ → +∞`** (the `w`-entry of the limiting compression;
`IsSpectralTest` supplies the limit `f(+∞)`). -/
theorem tendsto_wcomp_spectralFn_atTop {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {f : ℝ → ℝ} (hf1 : ∀ x, |f x| ≤ 1) {a : ℝ} (hfa : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun ρ : ℝ =>
        star w ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ w))
      atTop (𝓝 (a : ℂ)) := by
  have ha : |a| ≤ 1 := le_of_tendsto' hfa.abs hf1
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp hfa (ε / 2) (half_pos hε)
  refine ⟨max (max (6 * K) (T + 2 * K)) (max 1 (36 * Fintype.card ι * K ^ 2 / ε + 1)),
    fun ρ hρ => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hρ
  obtain ⟨⟨h6, hT2⟩, h1, hε2⟩ := hρ
  have hρa : |ρ| = ρ := abs_of_pos (by linarith)
  rw [dist_eq_norm]
  refine norm_wcomp_spectralFn_largeRho_lt hMh hK hM hUU hUw hcompl hw hf1 ha hε
    (by rw [hρa]; exact h6) (by rw [hρa]; exact h1) (by rw [hρa]; linarith) fun t ht => ?_
  have : T ≤ t := by
    have := (abs_le.mp ht).2
    linarith
  exact (hT t this).le

/-- **`w* f(M + ρww*) w → f(-∞)` as `ρ → -∞`**. -/
theorem tendsto_wcomp_spectralFn_atBot {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {f : ℝ → ℝ} (hf1 : ∀ x, |f x| ≤ 1) {b : ℝ} (hfb : Tendsto f atBot (𝓝 b)) :
    Tendsto (fun ρ : ℝ =>
        star w ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ w))
      atBot (𝓝 (b : ℂ)) := by
  have hb : |b| ≤ 1 := le_of_tendsto' hfb.abs hf1
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, hT⟩ := (atBot_basis.tendsto_iff Metric.nhds_basis_ball).mp hfb (ε / 2)
    (half_pos hε)
  rw [Filter.eventually_atBot]
  refine ⟨min (min (-(6 * K)) (T - 2 * K)) (min (-1) (-(36 * Fintype.card ι * K ^ 2 / ε + 1))),
    fun ρ hρ => ?_⟩
  simp only [le_min_iff] at hρ
  obtain ⟨⟨h6, hT2⟩, h1, hε2⟩ := hρ
  have hρa : |ρ| = -ρ := abs_of_neg (by linarith)
  rw [dist_eq_norm]
  refine norm_wcomp_spectralFn_largeRho_lt hMh hK hM hUU hUw hcompl hw hf1 hb hε
    (by rw [hρa]; linarith) (by rw [hρa]; linarith) (by rw [hρa]; linarith) fun t ht => ?_
  have : t ≤ T := by
    have := (abs_le.mp ht).1
    linarith
  have := hT.2 t (Set.mem_Iic.mpr this)
  rw [Metric.mem_ball, Real.dist_eq] at this
  exact this.le

/-- `f(N) z = Σ_a f(μ_a) (v_a* z) v_a` for Hermitian `N` (eigenvalues `μ_a`, eigenvectors `v_a`). -/
theorem spectralFn_mulVec_eq_sum {N : Matrix ι ι ℂ} (hN : N.IsHermitian) (f : ℝ → ℝ)
    (z : ι → ℂ) :
    BlockBand.LocalWindow.spectralFn f N *ᵥ z =
      ∑ a, (((f (hN.eigenvalues a) : ℝ) : ℂ) * (star ⇑(hN.eigenvectorBasis a) ⬝ᵥ z)) •
        ⇑(hN.eigenvectorBasis a) := by
  rw [spectralFn_of_isHermitian hN, cfc_eq_conj, ← mulVec_mulVec, ← mulVec_mulVec,
    mulVec_eq_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [op_smul_eq_smul, mulVec_diagonal, eigenvectorUnitary_conjTranspose_mulVec_apply,
    IsHermitian.eigenvectorUnitary_transpose_apply]

/-- **The cross term of the limiting compression**: under the hypotheses of
`opNorm_compress_spectralFn_largeRho_le` (`|f| ≤ 1`, no Lipschitz bound),
`‖U* f(M + ρww*) w‖ ≤ 3|ι|K/|ρ|`. -/
theorem vnorm_cross_spectralFn_largeRho_le {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {ρ : ℝ} (hρ : 6 * K ≤ |ρ|) {f : ℝ → ℝ} (hf1 : ∀ x, |f x| ≤ 1) :
    vnorm (Uᴴ *ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ w))
      ≤ 3 * Fintype.card ι * K / |ρ| := by
  have hN : (M + (ρ : ℂ) • vecMulVec w (star w)).IsHermitian := hMh.add (isHermitian_rankOne ρ w)
  have hρ0 : 0 < |ρ| := by linarith
  rw [spectralFn_mulVec_eq_sum hN, mulVec_sum]
  have hvsum : ∀ (t : Finset ι) (g : ι → κ → ℂ), vnorm (∑ a ∈ t, g a) ≤ ∑ a ∈ t, vnorm (g a) := by
    intro t g
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      rw [vnorm_eq]; simp
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (vnorm_add_le _ _).trans (by linarith)
  refine (hvsum _ _).trans ?_
  have hterm : ∀ a, vnorm (Uᴴ *ᵥ ((((f (hN.eigenvalues a) : ℝ) : ℂ) *
      (star ⇑(hN.eigenvectorBasis a) ⬝ᵥ w)) • ⇑(hN.eigenvectorBasis a))) ≤ 3 * K / |ρ| := by
    intro a
    set va := ⇑(hN.eigenvectorBasis a)
    have heig := mulVec_eigenvectorBasis_ofReal_smul hN a
    have hva := sqNorm_eigenvectorBasis hN a
    have hxa : ‖star va ⬝ᵥ w‖ = ‖star w ⬝ᵥ va‖ := by
      rw [← norm_star, star_dotProduct, star_star, dotProduct_comm]
    rw [mulVec_smul, vnorm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hxa]
    have hfa := hf1 (hN.eigenvalues a)
    have hx0 : 0 ≤ ‖star w ⬝ᵥ va‖ := norm_nonneg _
    have hy0 : 0 ≤ vnorm (Uᴴ *ᵥ va) := vnorm_nonneg _
    have hx1 : ‖star w ⬝ᵥ va‖ ≤ 1 := by
      have := norm_star_dotProduct_le w va
      rwa [vnorm_of_sqNorm_one hw, vnorm_of_sqNorm_one hva, one_mul] at this
    have hprod : ‖star w ⬝ᵥ va‖ * vnorm (Uᴴ *ᵥ va) ≤ 3 * K / |ρ| := by
      rcases lt_or_ge |hN.eigenvalues a| (2 * K) with hμ | hμ
      · have hcomp := largeRho_component_le_general hM hw hva heig
        have hx3 : ‖star w ⬝ᵥ va‖ ≤ 3 * K / |ρ| := by
          rw [le_div_iff₀ hρ0]; linarith
        have hy1 : vnorm (Uᴴ *ᵥ va) ≤ 1 := by
          refine (vnorm_mulVec_le _ _).trans ?_
          rw [vnorm_of_sqNorm_one hva, mul_one]
          exact opNorm_conjTranspose_le_one_of_isometry hUU
        calc ‖star w ⬝ᵥ va‖ * vnorm (Uᴴ *ᵥ va) ≤ 3 * K / |ρ| * 1 :=
              mul_le_mul hx3 hy1 hy0 (by positivity)
          _ = 3 * K / |ρ| := mul_one _
      · obtain ⟨-, hy2⟩ := largeRho_far_eig_le hK hM hUU hUw hcompl hw hρ hμ heig
        calc ‖star w ⬝ᵥ va‖ * vnorm (Uᴴ *ᵥ va) ≤ 1 * (2 * K * ‖star w ⬝ᵥ va‖ / |ρ|) :=
              mul_le_mul hx1 hy2 hy0 zero_le_one
          _ ≤ 3 * K / |ρ| := by
              rw [one_mul]
              exact div_le_div_of_nonneg_right (by nlinarith) hρ0.le
    calc |f (hN.eigenvalues a)| * ‖star w ⬝ᵥ va‖ * vnorm (Uᴴ *ᵥ va)
        = |f (hN.eigenvalues a)| * (‖star w ⬝ᵥ va‖ * vnorm (Uᴴ *ᵥ va)) := by ring
      _ ≤ 1 * (3 * K / |ρ|) := mul_le_mul hfa hprod (by positivity) zero_le_one
      _ = 3 * K / |ρ| := one_mul _
  calc ∑ a, vnorm (Uᴴ *ᵥ ((((f (hN.eigenvalues a) : ℝ) : ℂ) *
        (star ⇑(hN.eigenvectorBasis a) ⬝ᵥ w)) • ⇑(hN.eigenvectorBasis a)))
      ≤ ∑ _a : ι, 3 * K / |ρ| := Finset.sum_le_sum fun a _ => hterm a
    _ = 3 * Fintype.card ι * K / |ρ| := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- `‖A‖ ≤ c` from `‖A v‖ ≤ c ‖v‖`. -/
theorem opNorm_le_of_vnorm {A : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : ι → ℂ, vnorm (A *ᵥ v) ≤ c * vnorm v) : ‖A‖ ≤ c := by
  refine opNorm_le_of_sqNorm hc fun v => ?_
  rw [← vnorm_sq, ← vnorm_sq, ← mul_pow]
  exact pow_le_pow_left₀ (vnorm_nonneg _) (h v) 2

/-- The limiting operator `c ww* + U J U*` (`c = f(±∞)`, `J = f(U*MU)`). -/
def limitCompression (U : Matrix ι κ ℂ) (w : ι → ℂ) (c : ℝ) (J : Matrix κ κ ℂ) :
    Matrix ι ι ℂ :=
  (c : ℂ) • vecMulVec w (star w) + U * J * Uᴴ

/-- **Operator distance to the limiting compression**: for Hermitian `X` on `ι`, an isometry
`U` onto `w^⊥` (`U*U = 1`, `U*w = 0`, `UU* + ww* = 1`, `w` unit), `J` on `κ` and real `c`,
`‖X - (c ww* + UJU*)‖ ≤ ‖U*XU - J‖ + 2‖U*Xw‖ + |w*Xw - c|`. -/
theorem opNorm_sub_limitCompression_le {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) (J : Matrix κ κ ℂ)
    (c : ℝ) :
    ‖X - limitCompression U w c J‖ ≤
      ‖Uᴴ * X * U - J‖ + 2 * vnorm (Uᴴ *ᵥ (X *ᵥ w)) + ‖star w ⬝ᵥ (X *ᵥ w) - c‖ := by
  set A := ‖Uᴴ * X * U - J‖
  set r := vnorm (Uᴴ *ᵥ (X *ᵥ w))
  set D := ‖star w ⬝ᵥ (X *ᵥ w) - c‖
  have hww : star w ⬝ᵥ w = 1 := by rw [star_dotProduct_self, hw]; simp
  have hwU : ∀ y : κ → ℂ, star w ⬝ᵥ (U *ᵥ y) = 0 := fun y => by
    have : star w ᵥ* U = star (Uᴴ *ᵥ w) := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [dotProduct_mulVec, this, hUw, star_zero, zero_dotProduct]
  refine opNorm_le_of_vnorm (add_nonneg (add_nonneg (norm_nonneg _)
    (mul_nonneg zero_le_two (vnorm_nonneg _))) (norm_nonneg _)) fun v => ?_
  set y := Uᴴ *ᵥ v
  set x := star w ⬝ᵥ v
  have hdec : v = U *ᵥ y + x • w := decomp_of_compl hcompl v
  have hy : vnorm y ≤ vnorm v := by
    refine (vnorm_mulVec_le _ _).trans ?_
    exact mul_le_of_le_one_left (vnorm_nonneg v) (opNorm_conjTranspose_le_one_of_isometry hUU)
  have hx : ‖x‖ ≤ vnorm v := by
    have := norm_star_dotProduct_le w v
    rwa [vnorm_of_sqNorm_one hw, one_mul] at this
  -- the action of the limit
  have hLU : limitCompression U w c J *ᵥ (U *ᵥ y) = U *ᵥ (J *ᵥ y) := by
    unfold limitCompression
    rw [add_mulVec, smul_mulVec, vecMulVec_star_mulVec, hwU, zero_smul, smul_zero, zero_add,
      mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one, ← mulVec_mulVec]
  have hLw : limitCompression U w c J *ᵥ w = (c : ℂ) • w := by
    unfold limitCompression
    rw [add_mulVec, smul_mulVec, vecMulVec_star_mulVec, hww, one_smul, ← mulVec_mulVec,
      ← mulVec_mulVec, hUw, mulVec_zero, mulVec_zero, add_zero]
  -- `UU* + ww* = 1` applied to `X U y` and to `X w`
  set a := star w ⬝ᵥ (X *ᵥ (U *ᵥ y)) with ha
  set b := star w ⬝ᵥ (X *ᵥ w) with hb
  set q := Uᴴ *ᵥ (X *ᵥ w) with hq
  have hXUy : X *ᵥ (U *ᵥ y) = U *ᵥ ((Uᴴ * X * U) *ᵥ y) + a • w := by
    refine (decomp_of_compl hcompl (X *ᵥ (U *ᵥ y))).trans ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec]
  have hXw : X *ᵥ w = U *ᵥ q + b • w := decomp_of_compl hcompl (X *ᵥ w)
  have e : (X - limitCompression U w c J) *ᵥ v =
      U *ᵥ ((Uᴴ * X * U - J) *ᵥ y) + a • w + x • (U *ᵥ q) + (x * (b - c)) • w := by
    rw [sub_mulVec, hdec, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hLU, hLw, hXUy, hXw,
      sub_mulVec, mulVec_sub, smul_add, smul_smul, smul_smul, mul_sub, sub_smul]
    abel
  -- the cross bilinear term
  have hcross : ‖a‖ ≤ r * vnorm y := by
    have e2 : a = star q ⬝ᵥ y := by
      rw [ha, hq, star_mulVec, ← dotProduct_mulVec, conjTranspose_conjTranspose, star_mulVec,
        hX.eq, ← dotProduct_mulVec]
    rw [e2]; exact norm_star_dotProduct_le _ _
  have t1 : vnorm (U *ᵥ ((Uᴴ * X * U - J) *ᵥ y)) ≤ A * vnorm v := by
    rw [vnorm_isometry hUU]
    exact (vnorm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  have t2 : vnorm (a • w) ≤ r * vnorm v := by
    rw [vnorm_smul, vnorm_of_sqNorm_one hw, mul_one]
    exact hcross.trans (mul_le_mul_of_nonneg_left hy (vnorm_nonneg _))
  have t3 : vnorm (x • (U *ᵥ q)) ≤ r * vnorm v := by
    rw [vnorm_smul, vnorm_isometry hUU, mul_comm]
    exact mul_le_mul_of_nonneg_left hx (vnorm_nonneg _)
  have t4 : vnorm ((x * (b - c)) • w) ≤ D * vnorm v := by
    rw [vnorm_smul, vnorm_of_sqNorm_one hw, mul_one, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  rw [e]
  calc vnorm (U *ᵥ ((Uᴴ * X * U - J) *ᵥ y) + a • w + x • (U *ᵥ q) + (x * (b - c)) • w)
      ≤ vnorm (U *ᵥ ((Uᴴ * X * U - J) *ᵥ y)) + vnorm (a • w) + vnorm (x • (U *ᵥ q)) +
          vnorm ((x * (b - c)) • w) := by
        have := vnorm_add_le (U *ᵥ ((Uᴴ * X * U - J) *ᵥ y) + a • w + x • (U *ᵥ q))
          ((x * (b - c)) • w)
        have := vnorm_add_le (U *ᵥ ((Uᴴ * X * U - J) *ᵥ y) + a • w) (x • (U *ᵥ q))
        have := vnorm_add_le (U *ᵥ ((Uᴴ * X * U - J) *ᵥ y)) (a • w)
        linarith
    _ ≤ A * vnorm v + r * vnorm v + r * vnorm v + D * vnorm v := by linarith
    _ = (A + 2 * r + D) * vnorm v := by ring

/-- **The limiting compression, quantitative.** Let `M` be
Hermitian with `‖M‖ ≤ K` (`K > 0`), `w` unit, `U` an isometry onto `w^⊥`, `6K ≤ |ρ|`, `f` with
`|f| ≤ 1` and Lipschitz constant `L ≥ 0`, `|c| ≤ 1`, and `|f t - c| ≤ θ` whenever
`|ρ - t| ≤ 2K`. Then
`‖f(M + ρww*) - (c ww* + U f(U*MU) U*)‖ ≤ √|ι|(3LK² + 4K)/|ρ| + 6|ι|K/|ρ| + 18|ι|K²/ρ² + θ`. -/
theorem opNorm_spectralFn_sub_limitCompression_le {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {ρ : ℝ} (hρ : 6 * K ≤ |ρ|) {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ a b, |f a - f b| ≤ L * |a - b|) (hf1 : ∀ x, |f x| ≤ 1) {c θ : ℝ} (hc : |c| ≤ 1)
    (hθ : 0 ≤ θ) (hfar : ∀ t, |ρ - t| ≤ 2 * K → |f t - c| ≤ θ) :
    ‖BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) -
        limitCompression U w c (BlockBand.LocalWindow.spectralFn f (Uᴴ * M * U))‖ ≤
      Real.sqrt (Fintype.card ι) * ((3 * L * K ^ 2 + 4 * K) / |ρ|) +
        6 * Fintype.card ι * K / |ρ| + (18 * Fintype.card ι * K ^ 2 / ρ ^ 2 + θ) := by
  refine (opNorm_sub_limitCompression_le (isHermitian_spectralFn f _) hUU hUw hcompl hw _ c).trans
    ?_
  have h1 := opNorm_compress_spectralFn_largeRho_le hMh hK hM hUU hUw hcompl hw hρ hL hf hf1
  have h2 := vnorm_cross_spectralFn_largeRho_le hMh hK hM hUU hUw hcompl hw hρ hf1
  have h3 := norm_wcomp_spectralFn_largeRho_sub_le hMh hK hM hUU hUw hcompl hw hρ hf1 hc hθ hfar
  have e : 2 * (3 * (Fintype.card ι : ℝ) * K / |ρ|) = 6 * Fintype.card ι * K / |ρ| := by ring
  linarith

/-- The `1/|ρ|`-type error terms vanish along `ρ → ±∞`. -/
theorem tendsto_const_div_abs (C : ℝ) {l : Filter ℝ} (hl : Tendsto (fun ρ : ℝ => |ρ|) l atTop) :
    Tendsto (fun ρ : ℝ => C / |ρ|) l (𝓝 0) :=
  hl.const_div_atTop C

/-- **The limiting compression as `ρ → ±∞`**, generic filter version: if `|ρ| → ∞` along `l`
and `w* f(M + ρww*) w → c` along `l`, then `f(M + ρww*) → c ww* + U f(U*MU) U*` along `l`
(`|f| ≤ 1`, `f` Lipschitz). -/
theorem tendsto_spectralFn_limitCompression_of {M : Matrix ι ι ℂ} (hMh : M.IsHermitian)
    {K : ℝ} (hK : 0 < K) (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ}
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : ∀ a b, |f a - f b| ≤ L * |a - b|)
    (hf1 : ∀ x, |f x| ≤ 1) {c : ℝ} {l : Filter ℝ} (hl : Tendsto (fun ρ : ℝ => |ρ|) l atTop)
    (hwc : Tendsto (fun ρ : ℝ =>
        star w ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ w))
      l (𝓝 (c : ℂ))) :
    Tendsto (fun ρ : ℝ => BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)))
      l (𝓝 (limitCompression U w c (BlockBand.LocalWindow.spectralFn f (Uᴴ * M * U)))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hA := tendsto_const_div_abs (Real.sqrt (Fintype.card ι) * (3 * L * K ^ 2 + 4 * K)) hl
  have hB := tendsto_const_div_abs (6 * Fintype.card ι * K) hl
  have hD : Tendsto (fun ρ : ℝ =>
      ‖star w ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ w) -
        (c : ℂ)‖) l (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).mp hwc
  have hsum := (hA.add hB).add hD
  rw [add_zero, add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum
  filter_upwards [hl.eventually_ge_atTop (6 * K)] with ρ hρ
  refine (opNorm_sub_limitCompression_le (isHermitian_spectralFn f _) hUU hUw hcompl hw _ c).trans
    ?_
  have h1 := opNorm_compress_spectralFn_largeRho_le hMh hK hM hUU hUw hcompl hw hρ hL hf hf1
  have h2 := vnorm_cross_spectralFn_largeRho_le hMh hK hM hUU hUw hcompl hw hρ hf1
  have e1 : Real.sqrt (Fintype.card ι) * ((3 * L * K ^ 2 + 4 * K) / |ρ|) =
      Real.sqrt (Fintype.card ι) * (3 * L * K ^ 2 + 4 * K) / |ρ| := by ring
  have e2 : 2 * (3 * (Fintype.card ι : ℝ) * K / |ρ|) = 6 * Fintype.card ι * K / |ρ| := by ring
  linarith

/-- **The limiting compression at `ρ = +∞`** for a class (b) spectral test
(`IsSpectralTest k K₀ f`, `k ≥ 1`, limit `f(+∞) = a`): `f(M + ρww*) → a ww* + U f(U*MU) U*`. -/
theorem tendsto_spectralTest_limitCompression_atTop {k : ℕ} {K₀ : ℝ} {f : ℝ → ℝ}
    (hft : BlockBand.LocalWindow.IsSpectralTest k K₀ f) (hk : 1 ≤ k) {a : ℝ}
    (hfa : Tendsto f atTop (𝓝 a)) {M : Matrix ι ι ℂ} (hMh : M.IsHermitian) {K : ℝ} (hK : 0 < K)
    (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) :
    Tendsto (fun ρ : ℝ => BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)))
      atTop (𝓝 (limitCompression U w a (BlockBand.LocalWindow.spectralFn f (Uᴴ * M * U)))) :=
  tendsto_spectralFn_limitCompression_of hMh hK hM hUU hUw hcompl hw
    (nonneg_of_isSpectralTest hft hk) (lipschitz_of_isSpectralTest hft hk) hft.2.1
    tendsto_abs_atTop_atTop
    (tendsto_wcomp_spectralFn_atTop hMh hK hM hUU hUw hcompl hw hft.2.1 hfa)

/-- **The limiting compression at `ρ = -∞`** for a class (b) spectral test (limit
`f(-∞) = b`): `f(M + ρww*) → b ww* + U f(U*MU) U*`. -/
theorem tendsto_spectralTest_limitCompression_atBot {k : ℕ} {K₀ : ℝ} {f : ℝ → ℝ}
    (hft : BlockBand.LocalWindow.IsSpectralTest k K₀ f) (hk : 1 ≤ k) {b : ℝ}
    (hfb : Tendsto f atBot (𝓝 b)) {M : Matrix ι ι ℂ} (hMh : M.IsHermitian) {K : ℝ} (hK : 0 < K)
    (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) :
    Tendsto (fun ρ : ℝ => BlockBand.LocalWindow.spectralFn f (M + (ρ : ℂ) • vecMulVec w (star w)))
      atBot (𝓝 (limitCompression U w b (BlockBand.LocalWindow.spectralFn f (Uᴴ * M * U)))) :=
  tendsto_spectralFn_limitCompression_of hMh hK hM hUU hUw hcompl hw
    (nonneg_of_isSpectralTest hft hk) (lipschitz_of_isSpectralTest hft hk) hft.2.1
    tendsto_abs_atBot_atTop
    (tendsto_wcomp_spectralFn_atBot hMh hK hM hUU hUw hcompl hw hft.2.1 hfb)

/-- **Changing the observable away from the compression**: for a unit `v = Uy + xw` (`U`
isometry, `w` unit, `‖y‖ ≤ 1`) and matrices with `‖J - J'‖ ≤ 2`,
`|v*Jv - v*J'v| ≤ ‖U*JU - U*J'U‖ + 4|x|`. -/
theorem norm_quad_sub_le_compress {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {J J' : Matrix ι ι ℂ}
    (hJJ : ‖J - J'‖ ≤ 2) {w v : ι → ℂ} (hw : sqNorm w = 1) (hv : sqNorm v = 1) {y : κ → ℂ}
    {x : ℂ} (hy : vnorm y ≤ 1) (hdec : v = U *ᵥ y + x • w) :
    ‖star v ⬝ᵥ (J *ᵥ v) - star v ⬝ᵥ (J' *ᵥ v)‖ ≤ ‖Uᴴ * J * U - Uᴴ * J' * U‖ + 4 * ‖x‖ := by
  set D := J - J'
  have e0 : star v ⬝ᵥ (J *ᵥ v) - star v ⬝ᵥ (J' *ᵥ v) = star v ⬝ᵥ (D *ᵥ v) := by
    rw [sub_mulVec, dotProduct_sub]
  have eD : Uᴴ * J * U - Uᴴ * J' * U = Uᴴ * D * U := by
    simp only [D, Matrix.mul_sub, Matrix.sub_mul]
  have e1 : star v ⬝ᵥ (D *ᵥ v) = star (U *ᵥ y) ⬝ᵥ (D *ᵥ (U *ᵥ y)) +
      star (x • w) ⬝ᵥ (D *ᵥ v) + star (U *ᵥ y) ⬝ᵥ (D *ᵥ (x • w)) := by
    conv_lhs => rw [hdec]
    conv_rhs => rw [hdec]
    simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add]
    ring
  rw [e0, e1, eD, compress_quadratic]
  have hUy : vnorm (U *ᵥ y) ≤ 1 := by rw [vnorm_isometry hUU]; exact hy
  have hxw : vnorm (x • w) = ‖x‖ := by rw [vnorm_smul, vnorm_of_sqNorm_one hw, mul_one]
  have b1 := norm_bilinear_le (Uᴴ * D * U) y y
  have b2 := norm_bilinear_le D (x • w) v
  have b3 := norm_bilinear_le D (U *ᵥ y) (x • w)
  rw [hxw, vnorm_of_sqNorm_one hv, mul_one] at b2
  rw [hxw] at b3
  have hy0 := vnorm_nonneg y
  have t1 : ‖Uᴴ * D * U‖ * vnorm y * vnorm y ≤ ‖Uᴴ * D * U‖ := by
    have : vnorm y * vnorm y ≤ 1 := by nlinarith
    calc ‖Uᴴ * D * U‖ * vnorm y * vnorm y = ‖Uᴴ * D * U‖ * (vnorm y * vnorm y) := by ring
      _ ≤ ‖Uᴴ * D * U‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_one _
  have t2 : ‖D‖ * ‖x‖ ≤ 2 * ‖x‖ := mul_le_mul_of_nonneg_right hJJ (norm_nonneg _)
  have t3 : ‖D‖ * vnorm (U *ᵥ y) * ‖x‖ ≤ 2 * 1 * ‖x‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul hJJ hUy (vnorm_nonneg _) zero_le_two) (norm_nonneg _)
  have := norm_add_le (star (U *ᵥ y) ⬝ᵥ (D *ᵥ (U *ᵥ y)) + star (x • w) ⬝ᵥ (D *ᵥ v))
    (star (U *ᵥ y) ⬝ᵥ (D *ᵥ (x • w)))
  have := norm_add_le (star (U *ᵥ y) ⬝ᵥ (D *ᵥ (U *ᵥ y))) (star (x • w) ⬝ᵥ (D *ᵥ v))
  rw [compress_quadratic] at *
  linarith

/-- The embedded compressed observable `U J_c U*` is a contraction with `U*(U J_c U*)U = J_c`. -/
theorem embed_compress {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {Jc : Matrix κ κ ℂ}
    (hJc : ‖Jc‖ ≤ 1) : ‖U * Jc * Uᴴ‖ ≤ 1 ∧ Uᴴ * (U * Jc * Uᴴ) * U = Jc := by
  refine ⟨?_, ?_⟩
  · have h1 := opNorm_conjTranspose_le_one_of_isometry hUU
    have h2 := opNorm_le_one_of_isometry hUU
    calc ‖U * Jc * Uᴴ‖ ≤ ‖U * Jc‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖Jc‖) * ‖Uᴴ‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * 1) * 1 := by gcongr
      _ = 1 := by norm_num
  · rw [show Uᴴ * (U * Jc * Uᴴ) * U = (Uᴴ * U) * Jc * (Uᴴ * U) by simp only [Matrix.mul_assoc],
      hUU, Matrix.one_mul, Matrix.mul_one]

/-- **Window transfer through the limiting compression, additive form**: the hypotheses of
`largeRho_window_transfer`, except that the
window pair data are given for a contraction `J_c` on `w^⊥` with `‖U*JU - J_c‖ ≤ δ` (for class (b),
`J_c = f(U*M'U)`). Then the bound of `largeRho_window_transfer` holds for `v*Jv` with the extra
additive error `δ + 8K/|ρ|`. -/
theorem largeRho_window_transfer_limit_add {M : Matrix ι ι ℂ} {K : ℝ} (hK : 0 < K)
    (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w v : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) (hv : sqNorm v = 1)
    {ρ lam : ℝ} (hρ : 4 * K ≤ |ρ|) (hlam : |lam| ≤ K)
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (lam : ℂ) • v)
    {J : Matrix ι ι ℂ} (hJ : ‖J‖ ≤ 1) {Jc : Matrix κ κ ℂ} (hJc1 : ‖Jc‖ ≤ 1) {δ : ℝ}
    (hJc : ‖Uᴴ * J * U - Jc‖ ≤ δ) {Ahat : Matrix κ κ ℂ} (hAhat : Ahat.IsHermitian)
    {e : κ → κ → ℂ} (he : IsOrthonormalFamily e) {μ : κ → ℝ}
    (heigA : ∀ k, Ahat *ᵥ e k = (μ k : ℂ) • e k) {rg h : ℝ} (hrg : 0 ≤ rg) (hh : 0 < h)
    (hBA : ‖Uᴴ * M * U - Ahat‖ ≤ rg) {S : Finset κ} (hS : ∀ k ∉ S, h ≤ |μ k - lam|)
    {c : κ → ℂ} {c₀ : ℂ} {ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hpair : ∀ k ∈ S, ∀ l ∈ S,
      ‖star (e k) ⬝ᵥ (Jc *ᵥ e l) - (if k = l then c k else 0)‖ ≤ ε)
    (hcen : ∀ k ∈ S, ‖c k - c₀‖ ≤ ε') :
    ‖star v ⬝ᵥ (J *ᵥ v) - c₀‖ ≤
      S.card * ε + ε' + 2 * ((rg + 4 * K ^ 2 / |ρ|) / h) +
        (1 + ‖c₀‖) * ((rg + 4 * K ^ 2 / |ρ|) / h) ^ 2 +
        2 * K / |ρ| * (2 + 2 * K / |ρ|) + 2 * (2 * K / |ρ|) * ‖c₀‖ + (δ + 8 * K / |ρ|) := by
  have hρ0 : 0 < |ρ| := by linarith
  obtain ⟨hJt, hUJt⟩ := embed_compress hUU hJc1
  have hmain := largeRho_window_transfer hK hM hUU hUw hcompl hw hv hρ hlam heig hJt hAhat he
    heigA hrg hh hBA hS hε hε' (by rw [hUJt]; exact hpair) hcen
  have hdec := decomp_of_compl hcompl v
  have hy : vnorm (Uᴴ *ᵥ v) ≤ 1 := by
    refine (vnorm_mulVec_le _ _).trans ?_
    rw [vnorm_of_sqNorm_one hv, mul_one]
    exact opNorm_conjTranspose_le_one_of_isometry hUU
  have hJJ : ‖J - U * Jc * Uᴴ‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hq := norm_quad_sub_le_compress hUU hJJ hw hv hy hdec
  rw [hUJt] at hq
  have hx : ‖star w ⬝ᵥ v‖ ≤ 2 * K / |ρ| :=
    largeRho_component_le hM hw hv (abs_pos.mp hρ0) hlam heig
  have h8 : 4 * ‖star w ⬝ᵥ v‖ ≤ 8 * K / |ρ| := by
    have : 4 * (2 * K / |ρ|) = 8 * K / |ρ| := by ring
    linarith
  have := norm_sub_le_norm_sub_add_norm_sub (star v ⬝ᵥ (J *ᵥ v))
    (star v ⬝ᵥ ((U * Jc * Uᴴ) *ᵥ v)) c₀
  linarith

/-- **The large-`ρ` branch for a class (b) observable**: the full
eigenvector `v` of `M + ρww*` (`‖M‖ ≤ K`, `4K ≤ |ρ|`, `|λ| ≤ K`) against `J = f(M' + ρww*)`,
`f` a spectral test (`IsSpectralTest k K₀ f`, `k ≥ 1`) and `M'` Hermitian with `‖M'‖ ≤ K'`,
`6K' ≤ |ρ|` (`M' = F_reg(E) - E`, the regular part of `F(E) - E`), from the window data of the
limiting compression `J_c = f(U*M'U)` at a grid matrix `Â` of `w^⊥`: the bound of
`largeRho_window_transfer` plus the additive observable error
`√|ι| (3K₀K'² + 4K')/|ρ| + 8K/|ρ|`. -/
theorem largeRho_window_transfer_spectralTest {M : Matrix ι ι ℂ} {K : ℝ} (hK : 0 < K)
    (hM : ‖M‖ ≤ K) {U : Matrix ι κ ℂ} (hUU : Uᴴ * U = 1) {w v : ι → ℂ} (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) (hv : sqNorm v = 1)
    {ρ lam : ℝ} (hρ : 4 * K ≤ |ρ|) (hlam : |lam| ≤ K)
    (heig : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v = (lam : ℂ) • v)
    {k₀ : ℕ} {K₀ : ℝ} {f : ℝ → ℝ} (hft : BlockBand.LocalWindow.IsSpectralTest k₀ K₀ f)
    (hk : 1 ≤ k₀) {M' : Matrix ι ι ℂ} (hM'h : M'.IsHermitian) {K' : ℝ} (hK' : 0 < K')
    (hM' : ‖M'‖ ≤ K') (hρ' : 6 * K' ≤ |ρ|) {Ahat : Matrix κ κ ℂ} (hAhat : Ahat.IsHermitian)
    {e : κ → κ → ℂ} (he : IsOrthonormalFamily e) {μ : κ → ℝ}
    (heigA : ∀ k, Ahat *ᵥ e k = (μ k : ℂ) • e k) {rg h : ℝ} (hrg : 0 ≤ rg) (hh : 0 < h)
    (hBA : ‖Uᴴ * M * U - Ahat‖ ≤ rg) {S : Finset κ} (hS : ∀ k ∉ S, h ≤ |μ k - lam|)
    {c : κ → ℂ} {c₀ : ℂ} {ε ε' : ℝ} (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hpair : ∀ k ∈ S, ∀ l ∈ S,
      ‖star (e k) ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (Uᴴ * M' * U) *ᵥ e l) -
        (if k = l then c k else 0)‖ ≤ ε)
    (hcen : ∀ k ∈ S, ‖c k - c₀‖ ≤ ε') :
    ‖star v ⬝ᵥ (BlockBand.LocalWindow.spectralFn f (M' + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ v) -
        c₀‖ ≤
      S.card * ε + ε' + 2 * ((rg + 4 * K ^ 2 / |ρ|) / h) +
        (1 + ‖c₀‖) * ((rg + 4 * K ^ 2 / |ρ|) / h) ^ 2 +
        2 * K / |ρ| * (2 + 2 * K / |ρ|) + 2 * (2 * K / |ρ|) * ‖c₀‖ +
        (Real.sqrt (Fintype.card ι) * ((3 * K₀ * K' ^ 2 + 4 * K') / |ρ|) + 8 * K / |ρ|) := by
  exact largeRho_window_transfer_limit_add hK hM hUU hUw hcompl hw hv hρ hlam heig
    (opNorm_spectralFn_le hft.2.1 _) (opNorm_spectralFn_le hft.2.1 _)
    (opNorm_compress_spectralTest_largeRho_le hft hk hM'h hK' hM' hUU hUw hcompl hw hρ')
    hAhat he heigA hrg hh hBA hS hε hε' hpair hcen

end Generic

section Observable

variable {p : Parameters} {i : ZMod p.n}

/-- **The window observables at a large rank-one parameter.** Let `B` be a window observable
(`IsWindowObservable`) with derivative order `k ≥ 1`, and at `(ω, E)` let `schurK0 ω E = M' + ρww*`
with `M'` Hermitian, `‖M'‖ ≤ K'` (`K' > 0`), `w` unit, `6K' ≤ |ρ|`, and `U` an isometry onto `w^⊥`.
Then either (a) `B ω E = B₀(ω)` for a measurable family `B₀` of Hermitian contractions, and
`U*B₀(ω)U` is a Hermitian contraction; or (b) `B ω E = f(schurK0 ω E)` for a spectral test `f`,
`f(U*M'U)` is a Hermitian contraction and `‖U*(B ω E)U - f(U*M'U)‖ ≤ √(2W)(3K₀K'² + 4K')/|ρ|`. -/
theorem isWindowObservable_compress_largeRho {k : ℕ} {K₀ : ℝ}
    {B : SplitState p i → ℝ → PairMatrix p i}
    (hB : BlockBand.LocalWindow.IsWindowObservable p i k K₀ B) (hk : 1 ≤ k)
    (om : SplitState p i) (E : ℝ) {κ : Type} [Fintype κ] [DecidableEq κ]
    {M' : PairMatrix p i} (hM'h : M'.IsHermitian) {K' : ℝ} (hK' : 0 < K') (hM' : ‖M'‖ ≤ K')
    {w : PairSite p i → ℂ} {ρ : ℝ} (hρ' : 6 * K' ≤ |ρ|)
    (hdec : schurK0 p i om E = M' + (ρ : ℂ) • vecMulVec w (star w))
    {U : Matrix (PairSite p i) κ ℂ} (hUU : Uᴴ * U = 1) (hUw : Uᴴ *ᵥ w = 0)
    (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) (hw : sqNorm w = 1) :
    (∃ B₀ : SplitState p i → PairMatrix p i, Measurable B₀ ∧
        (∀ om', (B₀ om').IsHermitian ∧ ‖B₀ om'‖ ≤ 1) ∧ B om E = B₀ om ∧
        (Uᴴ * B₀ om * U).IsHermitian ∧ ‖Uᴴ * B₀ om * U‖ ≤ 1) ∨
      ∃ f : ℝ → ℝ, BlockBand.LocalWindow.IsSpectralTest k K₀ f ∧
        B om E = BlockBand.LocalWindow.spectralFn f (M' + (ρ : ℂ) • vecMulVec w (star w)) ∧
        (BlockBand.LocalWindow.spectralFn f (Uᴴ * M' * U)).IsHermitian ∧
        ‖BlockBand.LocalWindow.spectralFn f (Uᴴ * M' * U)‖ ≤ 1 ∧
        ‖Uᴴ * B om E * U - BlockBand.LocalWindow.spectralFn f (Uᴴ * M' * U)‖ ≤
          Real.sqrt (2 * (p.W : ℝ)) * ((3 * K₀ * K' ^ 2 + 4 * K') / |ρ|) := by
  rcases hB with ⟨B₀, hmeas, hB₀, hBE⟩ | ⟨f, hf, hBE⟩
  · refine Or.inl ⟨B₀, hmeas, hB₀, hBE om E, ?_⟩
    exact compress_hermitian_contraction hUU (hB₀ om).1 (hB₀ om).2
  · refine Or.inr ⟨f, hf, by rw [hBE, hdec], isHermitian_spectralFn f _,
      opNorm_spectralFn_le hf.2.1 _, ?_⟩
    have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
      rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
    rw [hBE, hdec, ← hcard]
    exact opNorm_compress_spectralTest_largeRho_le hf hk hM'h hK' hM' hUU hUw hcompl hw hρ'

end Observable

end BlockBand.LocalWindow.ProofPartTwo
