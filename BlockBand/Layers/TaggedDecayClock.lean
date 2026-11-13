module

public import BlockBand.Layers.TaggedTrace

/-!
# Tagged decay, deterministic part: the derivative trace and the tagged clock along the growth

Deterministic and almost-sure identities used by the decay recursion of `TaggedDecayStep`, for
the tagged decay bound of the tagged-trace lemma.

## The derivative trace

For a two-port Hermitian input `X`, `K = z_∂ - X`, `R = K⁻¹` and a source `S = K*YK` with `Y ⪰ 0`
("write the incoming source as `S = K*YK`"), the **derivative trace** is
`D_i(X, Y) = W⁻¹ Tr P_i R S R` (`tdcD`), the `h`-derivative of `-W⁻¹ Tr R_ii` along `X - hS`
(`tdc_hasDerivAt_input`). It is bounded by the clock, `|D_i| ≤ 3 W⁻¹ Tr Y` (`tdc_norm_D_le`).

## One untagged layer

For an untagged separate-port layer (`P = 0` in the tagged clock identity),
`X₊ = B*(A - E - X)⁻¹B` and
`Y₊ = L*YL`: `D_j(X₊, Y₊) = W⁻¹ Tr P_j 𝒢₂₁ S 𝒢₁₂` (`tdc_D_step`), which is
`-ġ_j = W⁻¹ Tr(Q_j 𝒢 Ŝ 𝒢)`, the derivative of the outgoing port trace along `X - hS`
(`tdc_D_step_eq_gdot`). Hence the incoming derivative of the next layer is exactly the outgoing
derivative of this one ("the derivative of the Schur input satisfies the tagged recursion").

## The tagged clock is the block-perturbation source

`tdc_coreSource_pgGrow` generalizes `clkCoreSource_pgGrow` (full clock) to an arbitrary tag:
one clock step with the layer tag maps the source `R* B_p*(H - E)⁻¹ P (H - E)⁻¹ B_p R` of a path to
that of the grown path. Along the growth (`tdc_clock_eq_source`), almost surely, the clock with
the core tag `T(· + L)` and the layer tags `T(L - 1 - k)`, `T(r₀ + L + k)` (`tdcCoreTag`,
`tdcLayerTag`) is the source of the final path with the position tag `T`. The derivative of the
final path Schur matrix along `t P_T` is `-(K*YK)`.

Combinatorics: `tdc_tagCount_le` (at most two tagged layers) and `tdc_layerTag_false` (no tag in
the last `ℓ` layers when every tagged position is at distance `≥ ℓ` from both path ends).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## 1. The derivative trace
-/

section DerivTrace

variable {W : ℕ}

/-- `K = z_∂ - X`. -/
def tdcK (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X

/-- **The derivative trace** `D_i(X, Y) = W⁻¹ Tr P_i R S R`, `S = K*YK`, `R = K⁻¹`. -/
def tdcD (b E : ℝ) (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) : ℂ :=
  blockTrace ((tdcK b E X)⁻¹ * ((tdcK b E X)ᴴ * Y * tdcK b E X) * (tdcK b E X)⁻¹) i

/-- `max_i |D_i(X, Y)|`. -/
def tdcMaxD (b E : ℝ) (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  max ‖tdcD b E X Y 0‖ ‖tdcD b E X Y 1‖

theorem tdcMaxD_nonneg (b E : ℝ) (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    0 ≤ tdcMaxD b E X Y :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem tdc_continuous_blockTrace (i : Fin 2) :
    Continuous (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => blockTrace M i) := by
  unfold blockTrace; fun_prop

theorem tdc_measurable_D {Ω : Type*} [MeasurableSpace Ω] (b E : ℝ)
    {Xf Yf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : Measurable Xf)
    (hY : Measurable Yf) (i : Fin 2) : Measurable (fun t => tdcD b E (Xf t) (Yf t) i) := by
  have hK : Measurable (fun t => tdcK b E (Xf t)) := measurable_const.sub hX
  have hR : Measurable (fun t => (tdcK b E (Xf t))⁻¹) := measurable_matrix_inv.comp hK
  exact (tdc_continuous_blockTrace i).measurable.comp
    (srec_measurable_mul (srec_measurable_mul hR (srec_measurable_mul (srec_measurable_mul
      (srec_measurable_conjTranspose hK) hY) hK)) hR)

theorem tdc_measurable_maxD {Ω : Type*} [MeasurableSpace Ω] (b E : ℝ)
    {Xf Yf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : Measurable Xf)
    (hY : Measurable Yf) : Measurable (fun t => tdcMaxD b E (Xf t) (Yf t)) :=
  ((tdc_measurable_D b E hX hY 0).norm).max (tdc_measurable_D b E hX hY 1).norm

/-- The block projection `P_i`. -/
def tdcProj (i : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal fun x => if x.1 = i then 1 else 0

theorem tdc_norm_proj_le (i : Fin 2) : ‖(tdcProj i : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ 1 := by
  rw [tdcProj, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun x => ?_
  split_ifs <;> simp

/-- `W⁻¹ Tr_{ii} M = W⁻¹ Tr(M P_i)`. -/
theorem tdc_blockTrace_eq (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    blockTrace M i = (W : ℂ)⁻¹ * (M * tdcProj i).trace := by
  unfold blockTrace tdcProj
  congr 1
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag, mul_diagonal, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- `‖(z - X)⁻¹‖ ≤ (Im z)⁻¹` for Hermitian `X`. -/
theorem tdc_norm_Kinv_le {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    ‖(tdcK b E X)⁻¹‖ ≤ ((boundaryZ b E).im)⁻¹ := by
  have heq : tdcK b E X = -X - diagonal (fun _ => -boundaryZ b E) := by
    ext i j
    simp only [tdcK, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp; ring
  rw [heq]
  exact lct_norm_shifted_inv_le (-X) hX.neg _ hz fun _ => by simp

theorem tdc_K_mul_inv {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    tdcK b E X * (tdcK b E X)⁻¹ = 1 :=
  mul_nonsing_inv _ (clk_K_isUnit hX hz)

theorem tdc_inv_mul_K {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    (tdcK b E X)⁻¹ * tdcK b E X = 1 :=
  nonsing_inv_mul _ (clk_K_isUnit hX hz)

/-- `R S R = R K* Y` for `S = K*YK`. -/
theorem tdc_RSR_eq {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (tdcK b E X)⁻¹ * ((tdcK b E X)ᴴ * Y * tdcK b E X) * (tdcK b E X)⁻¹ =
      (tdcK b E X)⁻¹ * (tdcK b E X)ᴴ * Y := by
  simp only [Matrix.mul_assoc, tdc_K_mul_inv hz hX, Matrix.mul_one]

/-- `‖R K*‖ ≤ 3`: `R K* = 1 + (z̄ - z) R`. -/
theorem tdc_norm_RKstar_le {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    ‖(tdcK b E X)⁻¹ * (tdcK b E X)ᴴ‖ ≤ 3 := by
  set z := boundaryZ b E
  have hKs : (tdcK b E X)ᴴ = tdcK b E X + (star z - z) • 1 := by
    unfold tdcK
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq, sub_smul]
    abel
  have e : (tdcK b E X)⁻¹ * (tdcK b E X)ᴴ = 1 + (star z - z) • (tdcK b E X)⁻¹ := by
    rw [hKs, Matrix.mul_add, tdc_inv_mul_K hz hX, Matrix.mul_smul, Matrix.mul_one]
  rw [e]
  have h1 := lct_norm_one_le (n := Fin 2 × Fin W)
  have h2 := tdc_norm_Kinv_le hz hX
  have h3 : ‖star z - z‖ = 2 * z.im := by
    have : star z - z = ((-2 * z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith)]; ring
  calc ‖1 + (star z - z) • (tdcK b E X)⁻¹‖ ≤ ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ +
        ‖star z - z‖ * ‖(tdcK b E X)⁻¹‖ := (norm_add_le _ _).trans (by rw [norm_smul])
    _ ≤ 1 + 2 * z.im * (z.im)⁻¹ := by
        rw [h3]; gcongr
    _ = 3 := by rw [mul_assoc, mul_inv_cancel₀ hz.ne']; norm_num

/-- **The derivative trace is bounded by the clock**: `|D_i(X, Y)| ≤ 3 W⁻¹ Tr Y`. -/
theorem tdc_norm_D_le {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef)
    (i : Fin 2) : ‖tdcD b E X Y i‖ ≤ 3 * clkTrace Y := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp [tdcD, blockTrace, clkTrace]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold tdcD
  rw [tdc_RSR_eq hz hX, tdc_blockTrace_eq]
  have e : ((tdcK b E X)⁻¹ * (tdcK b E X)ᴴ * Y * tdcProj i).trace =
      (Y * (tdcProj i * ((tdcK b E X)⁻¹ * (tdcK b E X)ᴴ))).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc]
  rw [e, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := wl_norm_trace_weight_le hY (tdcProj i * ((tdcK b E X)⁻¹ * (tdcK b E X)ᴴ))
  have h2 : ‖tdcProj (W := W) i * ((tdcK b E X)⁻¹ * (tdcK b E X)ᴴ)‖ ≤ 3 :=
    (norm_mul_le _ _).trans (by
      have := tdc_norm_proj_le (W := W) i
      have := tdc_norm_RKstar_le hz hX
      nlinarith [norm_nonneg ((tdcK b E X)⁻¹ * (tdcK b E X)ᴴ),
        norm_nonneg (tdcProj (W := W) i)])
  have h3 := wl_trace_re_nonneg hY
  unfold clkTrace
  calc (W : ℝ)⁻¹ * ‖(Y * (tdcProj i * ((tdcK b E X)⁻¹ * (tdcK b E X)ᴴ))).trace‖
      ≤ (W : ℝ)⁻¹ * (3 * Y.trace.re) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)
    _ = 3 * ((W : ℝ)⁻¹ * Y.trace.re) := by ring

theorem tdc_maxD_le {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef) :
    tdcMaxD b E X Y ≤ 3 * clkTrace Y :=
  max_le (tdc_norm_D_le hz hX hY 0) (tdc_norm_D_le hz hX hY 1)

theorem tdc_D_zero (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    tdcD b E X 0 i = 0 := by
  simp [tdcD, blockTrace]

theorem tdc_maxD_zero (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    tdcMaxD b E X 0 = 0 := by
  simp [tdcMaxD, tdc_D_zero]

/-- **`D` is the input derivative**: `h ↦ W⁻¹ Tr[(z - (X - hS))⁻¹]_{ii}` has derivative `-D_i(X, Y)`
at `0`, `S = K*YK` (the incoming derivative `d` of the paper). -/
theorem tdc_hasDerivAt_input {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    HasDerivAt (fun h : ℝ => blockTrace ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        - (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)))⁻¹) i) (-tdcD b E X Y i) 0 := by
  set S := (tdcK b E X)ᴴ * Y * tdcK b E X
  have hf : HasDerivAt (fun h : ℝ => tdcK b E X + (h : ℂ) • S) S 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const S).const_add (tdcK b E X)
    simpa [Complex.coe_smul] using this
  have hinv := tgt_hasDerivAt_inv_comp hf (by
    simp only [Complex.ofReal_zero, zero_smul, add_zero]; exact clk_K_isUnit hX hz)
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hinv
  have hT : HasDerivAt (fun h : ℝ => blockTrace ((tdcK b E X + (h : ℂ) • S)⁻¹) i)
      (blockTrace (-((tdcK b E X)⁻¹ * S * (tdcK b E X)⁻¹)) i) 0 := by
    let L : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M => blockTrace M i
          map_add' := fun A B => by
            simp only [blockTrace, Matrix.add_apply, Finset.sum_add_distrib, mul_add]
          map_smul' := fun r A => by
            simp only [blockTrace, Matrix.smul_apply, RingHom.id_apply, Complex.real_smul,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => by ring }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinv
  have hfun : (fun h : ℝ => blockTrace ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      - (X - (h : ℂ) • S))⁻¹) i) = fun h : ℝ => blockTrace ((tdcK b E X + (h : ℂ) • S)⁻¹) i := by
    funext h; unfold tdcK; congr 3; abel
  rw [hfun]
  convert hT using 1
  unfold tdcD blockTrace
  simp only [Matrix.neg_apply, Finset.sum_neg_distrib, mul_neg]
  rfl

end DerivTrace

/-!
## 2. One untagged layer: the outgoing derivative trace
-/

section LayerStep

variable {W : ℕ}

/-- Lower-left block of an inverse: `(N⁻¹)₂₁ = -(N⁻¹)₂₂ C A⁻¹` for `N = [[A, B], [C, D]]` with
`N` and `A` invertible. -/
theorem tdc_toBlocks21_inv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hN : IsUnit (fromBlocks A B C D).det) (hA : IsUnit A.det) :
    ((fromBlocks A B C D)⁻¹).toBlocks₂₁ = -(((fromBlocks A B C D)⁻¹).toBlocks₂₂ * C * A⁻¹) := by
  set G := (fromBlocks A B C D)⁻¹ with hG
  have h := nonsing_inv_mul (fromBlocks A B C D) hN
  rw [← hG, ← fromBlocks_toBlocks G, fromBlocks_multiply] at h
  have h21 : G.toBlocks₂₁ * A + G.toBlocks₂₂ * C = 0 := by
    have := congrArg Matrix.toBlocks₂₁ h
    rw [toBlocks_fromBlocks₂₁] at this
    rw [this]
    ext i j
    simp [toBlocks₂₁, one_apply]
  have hA' := mul_nonsing_inv A hA
  calc G.toBlocks₂₁ = (G.toBlocks₂₁ * A) * A⁻¹ := by rw [Matrix.mul_assoc, hA', Matrix.mul_one]
    _ = (-(G.toBlocks₂₂ * C)) * A⁻¹ := by rw [eq_neg_of_add_eq_zero_left h21]
    _ = -(G.toBlocks₂₂ * C * A⁻¹) := by rw [Matrix.neg_mul]

/-- **One untagged layer** (`P = 0` in the tagged clock identity): with `X₊ = B*(A - E - X)⁻¹B`,
`Y₊ = L*YL` and `S = K*YK`, `R₊ S₊ R₊ = 𝒢₂₁ S 𝒢₁₂` (`S₊ = K₊*Y₊K₊`), hence
`D_j(X₊, Y₊) = W⁻¹ Tr P_j 𝒢₂₁ S 𝒢₁₂`. -/
theorem tdc_D_step {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ℓ : LayerSample W .separate)
    (hℓ : ∀ j, (ℓ.1 j).IsHermitian)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - X).det)
    (hN : IsUnit (layerMatrix .separate E (boundaryZ b E) X ℓ).det) (j : Fin 2) :
    tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j =
      blockTrace ((layerResolvent .separate E (boundaryZ b E) X ℓ).toBlocks₂₁ *
        ((tdcK b E X)ᴴ * Y * tdcK b E X) *
          (layerResolvent .separate E (boundaryZ b E) X ℓ).toBlocks₁₂) j := by
  set G := layerResolvent .separate E (boundaryZ b E) X ℓ with hGdef
  set T := Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - X with hT
  set Bl := bondMatrix .separate ℓ.2 with hBl
  have hG : G = (fromBlocks T Bl Blᴴ (boundaryZ b E • 1))⁻¹ := rfl
  have hN' : IsUnit (fromBlocks T Bl Blᴴ (boundaryZ b E • 1)).det := hN
  have h12 : G.toBlocks₁₂ = -(T⁻¹ * Bl * G.toBlocks₂₂) := by
    rw [hG]; exact clk_toBlocks12_inv _ _ _ _ hN' hS
  have h21 : G.toBlocks₂₁ = -(G.toBlocks₂₂ * Blᴴ * T⁻¹) := by
    rw [hG]; exact tdc_toBlocks21_inv _ _ _ _ hN' hS
  have hR : (tdcK b E (layerSchur .separate E X ℓ))⁻¹ = G.toBlocks₂₂ :=
    srec_portResolvent E (boundaryZ b E) X ℓ hS
  have hXp := srec_layerSchur_isHermitian E hX ℓ hℓ
  have hKR := tdc_K_mul_inv hz hXp
  have hRK := tdc_inv_mul_K hz hXp
  have hTh : T.IsHermitian := by
    refine ((blockDiag_isHermitian hℓ).sub ?_).sub hX
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hTi : (T⁻¹)ᴴ = T⁻¹ := hTh.inv.eq
  set Kp := tdcK b E (layerSchur .separate E X ℓ) with hKp
  have hKG : Kpᴴ * G.toBlocks₂₂ᴴ = 1 := by
    rw [← conjTranspose_mul, ← hR, hRK, conjTranspose_one]
  have key : Kp⁻¹ * Kpᴴ * G.toBlocks₁₂ᴴ = G.toBlocks₂₁ := by
    rw [h12, h21, conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, hTi, Matrix.mul_neg]
    congr 1
    rw [show Kp⁻¹ * Kpᴴ * (G.toBlocks₂₂ᴴ * (Blᴴ * T⁻¹)) = Kp⁻¹ * (Kpᴴ * G.toBlocks₂₂ᴴ) * Blᴴ * T⁻¹ by
      simp only [Matrix.mul_assoc], hKG, Matrix.mul_one, hR]
  have hstep : clkStep b E (fun _ => false) X Y ℓ =
      (tdcK b E X * G.toBlocks₁₂)ᴴ * Y * (tdcK b E X * G.toBlocks₁₂) := by
    rw [clkStep, clkProj_eq_zero (fun _ => rfl), Matrix.mul_zero, Matrix.zero_mul, zero_add]
    rfl
  unfold tdcD
  rw [← hKp, hstep]
  congr 1
  calc Kp⁻¹ * (Kpᴴ * ((tdcK b E X * G.toBlocks₁₂)ᴴ * Y * (tdcK b E X * G.toBlocks₁₂)) * Kp) * Kp⁻¹
      = (Kp⁻¹ * Kpᴴ * G.toBlocks₁₂ᴴ) * ((tdcK b E X)ᴴ * Y * tdcK b E X) * G.toBlocks₁₂ *
          (Kp * Kp⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = G.toBlocks₂₁ * ((tdcK b E X)ᴴ * Y * tdcK b E X) * G.toBlocks₁₂ := by
        rw [key, hKR, Matrix.mul_one]

/-- `(𝒢 Ŝ 𝒢)_{ports} = 𝒢₂₁ S 𝒢₁₂` for `Ŝ = diag(S, 0)`. -/
theorem tdc_toBlocks22_sandwich {m n : Type*} [Fintype m] [Fintype n]
    (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) (S : Matrix m m ℂ) :
    (G * (dcvHat S : Matrix (m ⊕ n) (m ⊕ n) ℂ) * G).toBlocks₂₂ = G.toBlocks₂₁ * S * G.toBlocks₁₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks G]
  rw [dcvHat, fromBlocks_multiply, fromBlocks_multiply, toBlocks_fromBlocks₂₂]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- **The outgoing derivative trace is `-ġ_j`**: `W⁻¹ Tr P_j 𝒢₂₁ S 𝒢₁₂ = W⁻¹ Tr(Q_j 𝒢 Ŝ 𝒢)`, the
negative of the a.s. derivative `ġ` of `g_j = W⁻¹ Tr(Q_j 𝒢)` along `X - hS`
(`tgtCurvedClause`, `tgtNoiseClause` with `D = Q_j`). -/
theorem tdc_D_step_eq_gdot (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    blockTrace (G.toBlocks₂₁ * S * G.toBlocks₁₂) j =
      (W : ℂ)⁻¹ * (meqPortProj (σ := .separate) j * (G * dcvHat S * G)).trace := by
  rw [← lct_port_eq_trace, ← tdc_toBlocks22_sandwich]
  rfl

end LayerStep

/-!
## 3. The tagged clock is the source of the tagged block perturbation
-/

section ClockSource

variable {W : ℕ}

/-- `M* P M` is invariant under a simultaneous reindexing of the rows of `M` and of `P`. -/
theorem tdc_sandwich_reindex {m m' n : Type*} [Fintype m] [Fintype m'] (e : m' ≃ m)
    (M : Matrix m n ℂ) (P : Matrix m m ℂ) :
    Mᴴ * P * M = (M.submatrix e id)ᴴ * P.submatrix e e * M.submatrix e id := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

/-- The tag projection of the grown path in split coordinates. -/
theorem tdc_proj_pgSite {r : ℕ} (τ : Fin (r + 2) → Bool) :
    (clkProj (W := W) τ).submatrix (pgSite W r) (pgSite W r) =
      fromBlocks (clkProj (W := W) fun j => τ ((pgPos r).symm (.inl j))) 0 0
        (clkProj (W := W) fun i => τ ((pgPos r).symm (.inr i))) := by
  rw [clkProj, clkProj, clkProj, submatrix_diagonal_equiv, fromBlocks_diagonal]
  congr 1
  funext x
  rcases x with ⟨j, a⟩ | ⟨i, a⟩ <;> rfl

/-- **One tagged clock step is the block perturbation source of the grown path** (generalizing
`clkCoreSource_pgGrow` to an arbitrary tag `τ` of the grown path): for invertible `H - E`,
`A - E - X_r`, `𝒢⁻¹` and `K`, the clock step with the layer tag `τ ∘ (inl)` maps the source of
the old path with the tag `τ ∘ (inr)` to the source of the grown path with the tag `τ`. -/
theorem tdc_coreSource_pgGrow {r : ℕ} (hr : 1 ≤ r) (b E : ℝ) (τ : Fin (r + 2) → Bool)
    (ℓ : LayerSample W .separate) (ω : PathSample W r)
    (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det)
    (hN : IsUnit (layerMatrix .separate E (boundaryZ b E) (pathSchur E ω) ℓ).det)
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      pathSchur E ω).det) :
    clkCoreSource b E τ (pgGrow (ℓ, ω)) =
      clkStep b E (fun j => τ ((pgPos r).symm (.inl j))) (pathSchur E ω)
        (clkCoreSource b E (fun i => τ ((pgPos r).symm (.inr i))) ω) ℓ := by
  set D := pathMatrix ω - (E : ℂ) • 1 with hDdef
  set Bp := pathPortCoupling ω with hBp
  set A := Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 with hA
  set Bl := bondMatrix .separate ℓ.2 with hBl
  set G := layerResolvent .separate E (boundaryZ b E) (pathSchur E ω) ℓ with hG
  set T := A - pathSchur E ω with hT
  have h12 : G.toBlocks₁₂ = -(T⁻¹ * Bl * G.toBlocks₂₂) :=
    clk_toBlocks12_inv (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 -
      pathSchur E ω) Bl Blᴴ (boundaryZ b E • 1) hN hS
  have hR' : pathPortResolvent b E (pgGrow (ℓ, ω)) = G.toBlocks₂₂ :=
    pathPortResolvent_pgGrow hr b E ℓ ω hH hS
  let _ := invertibleOfIsUnitDet _ hH
  have hS' : IsUnit (A - Bpᴴ * ⅟D * Bp).det := by rw [invOf_eq_nonsing_inv]; exact hS
  let _ := invertibleOfIsUnitDet _ hS'
  let _ := fromBlocks₂₂Invertible A Bpᴴ Bp D
  have hF : (clkCoreFactor b E (pgGrow (ℓ, ω))).submatrix (pgSite W r) id =
      Matrix.fromRows (T⁻¹ * Bl) (-(D⁻¹ * Bp * T⁻¹ * Bl)) * G.toBlocks₂₂ := by
    unfold clkCoreFactor
    have hsub : ∀ {o : Type} [Fintype o] (M : Matrix (Fin (r + 2) × Fin W) o ℂ)
        (N : Matrix o (Fin 2 × Fin W) ℂ),
        (M * N).submatrix (pgSite W r) id = M.submatrix (pgSite W r) id * N := by
      intro o _ M N; ext i j; simp [Matrix.mul_apply]
    rw [hR', hsub, ← submatrix_mul_equiv _ _ (pgSite W r) (pgSite W r) id, ← inv_submatrix_equiv,
      pgGrow_pathMatrix_sub hr, pgGrow_portCoupling ℓ ω]
    congr 1
    change (fromBlocks A Bpᴴ Bp D)⁻¹ * fromRows Bl 0 = _
    rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, fromBlocks_mul_fromRows]
    simp only [Matrix.mul_zero, add_zero, invOf_eq_nonsing_inv]
    simp only [Matrix.neg_mul]; rfl
  have hRK : pathPortResolvent b E ω * (boundaryZ b E • 1 - pathSchur E ω) = 1 :=
    nonsing_inv_mul _ hK
  have hML : clkCoreFactor b E ω * clkL b E (pathSchur E ω) ℓ =
      -(D⁻¹ * Bp * T⁻¹ * Bl * G.toBlocks₂₂) := by
    unfold clkCoreFactor clkL clkG12
    rw [show D⁻¹ * Bp * pathPortResolvent b E ω * ((boundaryZ b E • 1 - pathSchur E ω) *
        G.toBlocks₁₂) = D⁻¹ * Bp * (pathPortResolvent b E ω * (boundaryZ b E • 1 -
          pathSchur E ω)) * G.toBlocks₁₂ by simp only [Matrix.mul_assoc], hRK, Matrix.mul_one, h12]
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
  set P₁ := clkProj (W := W) fun j => τ ((pgPos r).symm (.inl j))
  set P₂ := clkProj (W := W) fun i => τ ((pgPos r).symm (.inr i))
  set U := T⁻¹ * Bl * G.toBlocks₂₂
  set V := D⁻¹ * Bp * T⁻¹ * Bl * G.toBlocks₂₂
  have hlhs : clkCoreSource b E τ (pgGrow (ℓ, ω)) = Uᴴ * P₁ * U + Vᴴ * P₂ * V := by
    rw [clkCoreSource, tdc_sandwich_reindex (pgSite W r), hF, tdc_proj_pgSite]
    rw [conjTranspose_mul, conjTranspose_fromRows_eq_fromCols_conjTranspose]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (fromCols _ _),
      fromCols_mul_fromBlocks, ← Matrix.mul_assoc (fromCols _ _), fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, add_zero, zero_add, conjTranspose_neg,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_add, Matrix.add_mul]
    simp only [U, V, conjTranspose_mul, Matrix.mul_assoc]
    rfl
  have hrhs : clkStep b E (fun j => τ ((pgPos r).symm (.inl j))) (pathSchur E ω)
      (clkCoreSource b E (fun i => τ ((pgPos r).symm (.inr i))) ω) ℓ =
        Uᴴ * P₁ * U + Vᴴ * P₂ * V := by
    rw [clkStep, clkCoreSource]
    rw [show (clkL b E (pathSchur E ω) ℓ)ᴴ * ((clkCoreFactor b E ω)ᴴ * P₂ *
        clkCoreFactor b E ω) * clkL b E (pathSchur E ω) ℓ =
          (clkCoreFactor b E ω * clkL b E (pathSchur E ω) ℓ)ᴴ * P₂ *
            (clkCoreFactor b E ω * clkL b E (pathSchur E ω) ℓ) by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc], hML]
    change (G.toBlocks₁₂)ᴴ * P₁ * G.toBlocks₁₂ + _ = _
    rw [h12]
    simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [hlhs, hrhs]

end ClockSource

/-!
## 4. The tagged clock along the growth
-/

section Growth

variable {W : ℕ}

/-- Core tag of a final position tag `T` (final path of `r₀ + 2L` blocks): core block `i` sits
at the final position `i + L`. -/
def tdcCoreTag {r₀ : ℕ} (L : ℕ) (T : ℕ → Bool) : Fin r₀ → Bool := fun i => T (i.val + L)

/-- Layer tags of a final position tag `T`: layer `k` adds the final positions `L - 1 - k`
(its block `0`) and `r₀ + L + k` (its block `1`). -/
def tdcLayerTag (r₀ L : ℕ) (T : ℕ → Bool) : ℕ → Fin 2 → Bool :=
  fun k j => T (if j.val = 0 then L - 1 - k else r₀ + L + k)

/-- The tag of the path after `k` growth steps: its position `j` is the final position
`j + (L - k)`. -/
def tdcStageTag {r : ℕ} (L k : ℕ) (T : ℕ → Bool) : Fin r → Bool := fun j => T (j.val + (L - k))

theorem tdc_stageTag_succ {r₀ L k : ℕ} (hk : k < L) (T : ℕ → Bool) :
    (fun j : Fin 2 => tdcStageTag (r := r₀ + 2 * k + 2) L (k + 1) T ((pgPos (r₀ + 2 * k)).symm (.inl j)))
      = tdcLayerTag r₀ L T k ∧
    (fun i : Fin (r₀ + 2 * k) => tdcStageTag (r := r₀ + 2 * k + 2) L (k + 1) T
      ((pgPos (r₀ + 2 * k)).symm (.inr i))) = tdcStageTag L k T := by
  constructor
  · funext j
    rcases rng_fin2_cases j with rfl | rfl
    · simp only [tdcStageTag, tdcLayerTag, pgPos_symm_inl_zero, Fin.val_zero, ite_true]
      congr 1
      omega
    · simp only [tdcStageTag, tdcLayerTag, pgPos_symm_inl_one, Fin.val_one, one_ne_zero,
        ite_false]
      congr 1
      omega
  · funext i
    simp only [tdcStageTag, pgPos_symm_inr]
    congr 1
    omega

/-- **The tagged clock is the source of the final path** (generalizing `clk_fullClock_eq_source`):
almost surely under `growthLaw W r₀ L b`, for every `k ≤ L`, the clock with the core tag
`tdcCoreTag L T` and the layer tags `tdcLayerTag r₀ L T` is the block-perturbation source
`clkCoreSource b E (tdcStageTag L k T) (pgPath ω k)` of the grown path, whenever `Im z_∂ > 0`. -/
theorem tdc_clock_eq_source {r₀ L : ℕ} {b : ℝ} (hb1 : b < 1 / 2) (E : ℝ)
    (hz : 0 < (boundaryZ b E).im) (hr₀ : 1 ≤ r₀) (T : ℕ → Bool) :
    ∀ᵐ ω ∂growthLaw W r₀ L b, ∀ k, k ≤ L →
      clkClock b E (tdcCoreTag L T) (tdcLayerTag r₀ L T) ω k =
        clkCoreSource b E (tdcStageTag L k T) (pgPath ω k) := by
  have hinv : ∀ᵐ ω ∂growthLaw W r₀ L b,
      ∀ j : ℕ, j ≤ L → IsUnit (pathMatrix (pgPath ω j) - (E : ℂ) • 1).det := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j ≤ L
    · have hP := measurePreserving_pgPath (W := W) b hr₀ L j hj
      filter_upwards [hP.quasiMeasurePreserving.ae
        (ae_isUnit_det_pathMatrix W (r₀ + 2 * j) hb1 E)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  filter_upwards [hinv, clk_ae_good W r₀ L b] with ω hω hg
  intro k
  induction k with
  | zero =>
    intro _
    simp only [clkClock, pgPath]
    congr 1
  | succ k ih =>
    intro hk
    have hkL : k < L := by omega
    have ih' := ih (by omega)
    have hX := grownSchur_eq_pathSchur hr₀ E ω k (by omega) (fun j hj => hω j (by omega))
    have hH := hω k (by omega)
    have hG := hω (k + 1) hk
    rw [pgPath_succ ω hkL] at hG ⊢
    have hr : 1 ≤ r₀ + 2 * k := by omega
    have hS := (isUnit_det_pgGrow_iff hr E (ω.2 ⟨k, hkL⟩) (pgPath ω k) hH).mp hG
    have hXh : (pathSchur E (pgPath ω k)).IsHermitian := by
      rw [← hX]; exact clk_grownSchur_isHermitian E hg k
    have hK := clk_K_isUnit hXh hz
    have hN := clk_layerMatrix_isUnit E (boundaryZ b E) _ _ hS
      (clk_K_isUnit (srec_layerSchur_isHermitian E hXh _ (hg.2 _)) hz)
    simp only [clkClock, hkL, dite_true]
    rw [ih', hX]
    obtain ⟨h1, h2⟩ := tdc_stageTag_succ (r₀ := r₀) hkL T
    rw [tdc_coreSource_pgGrow hr b E _ (ω.2 ⟨k, hkL⟩) (pgPath ω k) hH hS hN hK, h1, h2]

/-- **The tagged source as `K*YK`**: for a path with Hermitian blocks and Hermitian Schur matrix,
`B_p*(H - E)⁻¹ P_τ (H - E)⁻¹ B_p = K* Y K` with `Y = clkCoreSource b E τ ω` and `K = z_∂ - X`
(`clkCoreSource_eq_source`, `K R = 1`). -/
theorem tdc_source_eq {r : ℕ} {b E : ℝ} (hz : 0 < (boundaryZ b E).im) (τ : Fin r → Bool)
    (ω : PathSample W r) (hH : (pathMatrix ω).IsHermitian)
    (hX : (pathSchur E ω).IsHermitian) :
    (pathPortCoupling ω)ᴴ * (pathMatrix ω - (E : ℂ) • 1)⁻¹ * clkProj (W := W) τ *
        (pathMatrix ω - (E : ℂ) • 1)⁻¹ * pathPortCoupling ω =
      (tdcK b E (pathSchur E ω))ᴴ * clkCoreSource b E τ ω * tdcK b E (pathSchur E ω) := by
  rw [clkCoreSource_eq_source b E τ ω hH]
  have hRK : pathPortResolvent b E ω * tdcK b E (pathSchur E ω) = 1 := tdc_inv_mul_K hz hX
  set S := (pathPortCoupling ω)ᴴ * (pathMatrix ω - (E : ℂ) • 1)⁻¹ * clkProj (W := W) τ *
    (pathMatrix ω - (E : ℂ) • 1)⁻¹ * pathPortCoupling ω
  calc S = (pathPortResolvent b E ω * tdcK b E (pathSchur E ω))ᴴ * S *
        (pathPortResolvent b E ω * tdcK b E (pathSchur E ω)) := by
          rw [hRK, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]

/-- With no tag the clock vanishes: the core injection and every untagged step are zero. -/
theorem tdc_clock_untagged {r₀ L : ℕ} (b E : ℝ) {τ₀ : Fin r₀ → Bool} {τ : ℕ → Fin 2 → Bool}
    (h₀ : ∀ i, τ₀ i = false) {K : ℕ} (h : ∀ k, k < K → ∀ i, τ k i = false)
    (ω : GrowthSample W r₀ L) : ∀ k, k ≤ K → clkClock b E τ₀ τ ω k = 0
  | 0, _ => by simp [clkClock, clkCoreSource, clkProj_eq_zero h₀]
  | k + 1, hk => by
    have ih := tdc_clock_untagged b E h₀ h ω k (by omega)
    simp only [clkClock]
    split_ifs
    · rw [ih, clkStep, clkProj_eq_zero (h k (by omega))]; simp
    · exact ih

/-!
## 5. Tag combinatorics
-/

/-- At most two tagged layers when at most two final positions are tagged. -/
theorem tdc_tagCount_le {r₀ L : ℕ} {T : ℕ → Bool} {j₁ j₂ : ℕ}
    (hT : ∀ j, T j = true → j = j₁ ∨ j = j₂) :
    clkTagCount (tdcLayerTag r₀ L T) L ≤ 2 := by
  let f : ℕ → ℕ := fun j => if j < L then L - 1 - j else j - r₀ - L
  have hsub : (Finset.range L).filter (fun k => ∃ i, tdcLayerTag r₀ L T k i = true) ⊆
      {f j₁, f j₂} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkL, i, hi⟩ := hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    unfold tdcLayerTag at hi
    have hkey : ∀ j, (if i.val = 0 then L - 1 - k else r₀ + L + k) = j → k = f j := by
      intro j hj
      simp only [f]
      split_ifs at hj <;> split_ifs <;> omega
    rcases hT _ hi with h | h
    · exact Or.inl (hkey _ h)
    · exact Or.inr (hkey _ h)
  unfold clkTagCount
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- **No tag in the last `ℓ` layers**: if every tagged final position `j < r₀ + 2L` satisfies
`ℓ ≤ j` and `ℓ + j + 1 ≤ r₀ + 2L` (distance `≥ ℓ` from both ends), the layers `k ≥ L - ℓ` are
untagged. -/
theorem tdc_layerTag_false {r₀ L ℓ : ℕ} {T : ℕ → Bool}
    (hℓ : ∀ j, j < r₀ + 2 * L → T j = true → ℓ ≤ j ∧ ℓ + j + 1 ≤ r₀ + 2 * L) {k : ℕ}
    (hk : L ≤ k + ℓ) (hkL : k < L) (i : Fin 2) : tdcLayerTag r₀ L T k i = false := by
  unfold tdcLayerTag
  by_contra h
  rw [Bool.not_eq_false] at h
  split_ifs at h
  · have := hℓ _ (by omega) h; omega
  · have := hℓ _ (by omega) h; omega

/-- A tagged position forces `ℓ ≤ L` (two cores: `r₀ ≤ 2`). -/
theorem tdc_le_of_tagged {r₀ L ℓ : ℕ} (hr₀ : r₀ ≤ 2) {T : ℕ → Bool}
    (hℓ : ∀ j, j < r₀ + 2 * L → T j = true → ℓ ≤ j ∧ ℓ + j + 1 ≤ r₀ + 2 * L) {j : ℕ}
    (hj : j < r₀ + 2 * L) (hTj : T j = true) : ℓ ≤ L := by
  have := hℓ j hj hTj; omega

end Growth

end BlockBand.Layers
