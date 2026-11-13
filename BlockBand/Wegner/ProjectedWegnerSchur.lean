module

public import Mathlib
public import BlockBand.Wegner.ProjectedWegnerBasic
public import BlockBand.Internal.Contracts.Inputs

/-!
# Schur-complement algebra for the projected Wegner estimate

With `E` the isometric embedding of block `j` and `S = (Eᴴ X₀⁻¹ E)⁻¹`, the identity
`Tr (P_{{j}} (X₀ + E a Eᴴ)⁻¹) = Tr ((a + S)⁻¹)` reduces the projected density to one block, and
`S` inherits the imaginary margin of `X₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open Matrix
open BlockBand.Internal.Contracts.Inputs
open scoped ComplexOrder

variable {k W : ℕ}

/-- Isometric embedding `E : ℂ^W → ℂ^{kW}` of block `j` (sites `Fin k × Fin W`):
`E_{(i,a),b} = 1` iff `i = j` and `a = b`. -/
def blockEmbed (j : Fin k) : Matrix (Fin k × Fin W) (Fin W) ℂ :=
  fun x b => if x.1 = j ∧ x.2 = b then 1 else 0

/-- Direct sum `⊕_i A_i` of a family of `W × W` blocks (so
`M.blockSum w = familyBlockSum (M.A w)` by `rfl`). -/
def familyBlockSum (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then A x.1 x.2 y.2 else 0

/-- Schur block `S = (Eᴴ X₀⁻¹ E)⁻¹` of `X₀` at block `j` (nonsingular inverses). -/
def schurBlock (X₀ : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) (j : Fin k) :
    Matrix (Fin W) (Fin W) ℂ :=
  ((blockEmbed (W := W) j)ᴴ * X₀⁻¹ * blockEmbed (W := W) j)⁻¹

/-- Entry form `E_{x,b} = [x = (j, b)]`. -/
theorem blockEmbed_apply' (j : Fin k) (x : Fin k × Fin W) (b : Fin W) :
    blockEmbed (W := W) j x b = if x = (j, b) then 1 else 0 := by
  simp [blockEmbed, Prod.ext_iff]

/-- `(Eᴴ M)_{b,y} = M_{(j,b),y}`. -/
theorem conjTranspose_blockEmbed_mul_apply {m : Type} [Fintype m] (j : Fin k)
    (M : Matrix (Fin k × Fin W) m ℂ) (b : Fin W) (y : m) :
    ((blockEmbed (W := W) j)ᴴ * M) b y = M (j, b) y := by
  simp [Matrix.mul_apply, conjTranspose_apply, blockEmbed_apply']

/-- `(M E)_{x,c} = M_{x,(j,c)}`. -/
theorem mul_blockEmbed_apply {m : Type} [Fintype m] (j : Fin k)
    (M : Matrix m (Fin k × Fin W) ℂ) (x : m) (c : Fin W) :
    (M * blockEmbed (W := W) j) x c = M x (j, c) := by
  simp [Matrix.mul_apply, blockEmbed_apply']

/-- `(E M)_{x,c} = [x.1 = j] M_{x.2,c}`. -/
theorem blockEmbed_mul_apply {m : Type} (j : Fin k)
    (M : Matrix (Fin W) m ℂ) (x : Fin k × Fin W) (c : m) :
    (blockEmbed (W := W) j * M) x c = if x.1 = j then M x.2 c else 0 := by
  by_cases hx : x.1 = j <;> simp [Matrix.mul_apply, blockEmbed, hx]

/-- `(M Eᴴ)_{x,y} = [y.1 = j] M_{x,y.2}`. -/
theorem mul_conjTranspose_blockEmbed_apply {m : Type} (j : Fin k)
    (M : Matrix m (Fin W) ℂ) (x : m) (y : Fin k × Fin W) :
    (M * (blockEmbed (W := W) j)ᴴ) x y = if y.1 = j then M x y.2 else 0 := by
  by_cases hy : y.1 = j <;> simp [Matrix.mul_apply, blockEmbed, conjTranspose_apply, hy]

/-- `Eᴴ E = 1`. -/
theorem conjTranspose_blockEmbed_mul_blockEmbed (j : Fin k) :
    (blockEmbed (W := W) j)ᴴ * blockEmbed (W := W) j = 1 := by
  ext b c
  rw [conjTranspose_blockEmbed_mul_apply, Matrix.one_apply]
  simp [blockEmbed]

/-- `(E w)_x = [x.1 = j] w_{x.2}`. -/
theorem blockEmbed_mulVec (j : Fin k) (w : Fin W → ℂ) :
    blockEmbed (W := W) j *ᵥ w = fun x => if x.1 = j then w x.2 else 0 := by
  funext x
  by_cases hx : x.1 = j <;> simp [Matrix.mulVec, dotProduct, blockEmbed, hx]

/-- `(Eᴴ v)_b = v_{(j,b)}`. -/
theorem conjTranspose_blockEmbed_mulVec (j : Fin k) (v : Fin k × Fin W → ℂ) :
    (blockEmbed (W := W) j)ᴴ *ᵥ v = fun b => v (j, b) := by
  funext b
  simp [Matrix.mulVec, dotProduct, conjTranspose_apply, blockEmbed_apply']

/-- `‖Eᴴ v‖ ≤ ‖v‖` in squared Euclidean form. -/
theorem re_star_dotProduct_conjTranspose_blockEmbed_le (j : Fin k) (v : Fin k × Fin W → ℂ) :
    (star ((blockEmbed (W := W) j)ᴴ *ᵥ v) ⬝ᵥ ((blockEmbed (W := W) j)ᴴ *ᵥ v)).re ≤
      (star v ⬝ᵥ v).re := by
  rw [re_star_dotProduct_self, re_star_dotProduct_self, conjTranspose_blockEmbed_mulVec,
    Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun i => ∑ b, ‖v (i, b)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- Adjoint identity `⟨z, E w⟩ = ⟨Eᴴ z, w⟩`. -/
theorem star_dotProduct_blockEmbed_mulVec (j : Fin k) (z : Fin k × Fin W → ℂ)
    (w : Fin W → ℂ) :
    star z ⬝ᵥ (blockEmbed (W := W) j *ᵥ w) = star ((blockEmbed (W := W) j)ᴴ *ᵥ z) ⬝ᵥ w := by
  rw [dotProduct_mulVec, Matrix.star_mulVec, conjTranspose_conjTranspose]

/-- `M.blockSum w` is the family direct sum of the blocks `M.A w`. -/
theorem blockSum_eq_familyBlockSum (M : BlockModel k W) (w : M.Ω) :
    M.blockSum w = familyBlockSum (M.A w) :=
  rfl

/-- A direct sum of Hermitian blocks is Hermitian. -/
theorem familyBlockSum_isHermitian {A : Fin k → Matrix (Fin W) (Fin W) ℂ}
    (hA : ∀ i, (A i).IsHermitian) : (familyBlockSum A).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, familyBlockSum]
  by_cases h : x.1 = y.1
  · simp only [h, ↓reduceIte]
    rw [← conjTranspose_apply, (hA y.1).eq]
  · simp [h, Ne.symm h]

/-- Splitting off block `j`: `⊕_i A_i = ⊕_i A_i 1_{i ≠ j} + E A_j Eᴴ`. -/
theorem familyBlockSum_split (A : Fin k → Matrix (Fin W) (Fin W) ℂ) (j : Fin k) :
    familyBlockSum A =
      familyBlockSum (fun i => if i = j then 0 else A i) +
        blockEmbed (W := W) j * A j * (blockEmbed (W := W) j)ᴴ := by
  ext x y
  rw [Matrix.add_apply, mul_conjTranspose_blockEmbed_apply, blockEmbed_mul_apply]
  simp only [familyBlockSum]
  by_cases hxy : x.1 = y.1
  · by_cases hx : x.1 = j
    · simp [hxy, ← hx]
    · simp [hxy, show ¬ y.1 = j from hxy ▸ hx]
  · by_cases hx : x.1 = j
    · have hy : ¬ y.1 = j := fun h => hxy (hx.trans h.symm)
      have hy' : ¬ j = y.1 := fun h => hy h.symm
      simp [hx, hy, hy']
    · simp [hxy, hx]

/-- `P_{{j}} = E Eᴴ`. -/
theorem blockProjector_singleton (j : Fin k) :
    blockProjector {j} = blockEmbed (W := W) j * (blockEmbed (W := W) j)ᴴ := by
  ext x y
  rw [mul_conjTranspose_blockEmbed_apply, blockEmbed_apply']
  simp only [blockProjector, Matrix.diagonal_apply, Finset.mem_singleton]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x.1 = j <;> simp [hx, Prod.ext_iff]
  · by_cases hy : y.1 = j
    · have : ¬ x = (j, y.2) := fun h => hxy (h.trans (by simp [← hy]))
      simp [hxy, hy, this]
    · simp [hxy, hy]

/-- `Tr (P_B G) = Σ_{j ∈ B} Tr (P_{{j}} G)`. -/
theorem trace_blockProjector_mul_eq_sum (B : Finset (Fin k))
    (G : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    (blockProjector B * G).trace = ∑ j ∈ B, (blockProjector {j} * G).trace := by
  simp only [blockProjector, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
    Finset.mem_singleton, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq]

/-- `Tr (E Eᴴ G) = Tr (Eᴴ G E)`. -/
theorem trace_blockProjector_singleton_mul (j : Fin k)
    (G : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    (blockProjector {j} * G).trace =
      ((blockEmbed (W := W) j)ᴴ * G * blockEmbed (W := W) j).trace := by
  rw [blockProjector_singleton, Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- A positive margin with nonpositive quadratic form forces `v = 0`. -/
theorem HasImMargin.eq_zero_of_im_le_zero {n : Type} [Fintype n] {η : ℝ} (hη : 0 < η)
    {N : Matrix n n ℂ} (h : HasImMargin η N) {v : n → ℂ}
    (hv : (star v ⬝ᵥ (N *ᵥ v)).im ≤ 0) : v = 0 := by
  have h1 := (h v).trans hv
  have h2 : (star v ⬝ᵥ v).re ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hη hc
    linarith
  funext i
  have h3 := norm_sq_le_re_star_dotProduct_self v i
  have h4 : ‖v i‖ ^ 2 = 0 := le_antisymm (h3.trans h2) (sq_nonneg _)
  simpa using h4

/-- `K = Eᴴ X₀⁻¹ E` is invertible when `X₀` has a positive margin. -/
theorem isUnit_compressedInverse {η : ℝ} (hη : 0 < η)
    {X₀ : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ} (h : HasImMargin η X₀) (j : Fin k) :
    IsUnit ((blockEmbed (W := W) j)ᴴ * X₀⁻¹ * blockEmbed (W := W) j) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  have hX := h.isUnit_det hη
  have key : ∀ w : Fin W → ℂ,
      ((blockEmbed (W := W) j)ᴴ * X₀⁻¹ * blockEmbed (W := W) j) *ᵥ w = 0 → w = 0 := by
    intro w hw
    set z := X₀⁻¹ *ᵥ (blockEmbed (W := W) j *ᵥ w) with hz
    have hEz : (blockEmbed (W := W) j)ᴴ *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec]
    have hXz : X₀ *ᵥ z = blockEmbed (W := W) j *ᵥ w := by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
    have hz0 : z = 0 := by
      apply h.eq_zero_of_im_le_zero hη
      rw [hXz, star_dotProduct_blockEmbed_mulVec, hEz, star_zero, zero_dotProduct,
        Complex.zero_im]
    have hEw : blockEmbed (W := W) j *ᵥ w = 0 := by rw [← hXz, hz0, Matrix.mulVec_zero]
    rw [← Matrix.one_mulVec w, ← conjTranspose_blockEmbed_mul_blockEmbed (W := W) j,
      ← Matrix.mulVec_mulVec, hEw, Matrix.mulVec_zero]
  intro x y hxy
  have : ((blockEmbed (W := W) j)ᴴ * X₀⁻¹ * blockEmbed (W := W) j) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ this)

/-- Schur block margin: if
`X₀` on `ℂ^{kW}` has imaginary margin `η > 0`, then `S = (Eᴴ X₀⁻¹ E)⁻¹` on `ℂ^W` has
imaginary margin `η`, for every `k`, `W`, block `j`. -/
theorem hasImMargin_schurBlock {η : ℝ} (hη : 0 < η)
    {X₀ : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ} (h : HasImMargin η X₀) (j : Fin k) :
    HasImMargin η (schurBlock X₀ j) := by
  intro u
  have hX := h.isUnit_det hη
  have hK := isUnit_compressedInverse hη h j
  have hKS : (blockEmbed (W := W) j)ᴴ * X₀⁻¹ * blockEmbed (W := W) j * schurBlock X₀ j = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hK)
  set v := X₀⁻¹ *ᵥ (blockEmbed (W := W) j *ᵥ (schurBlock X₀ j *ᵥ u)) with hv
  have hEv : (blockEmbed (W := W) j)ᴴ *ᵥ v = u := by
    simp only [hv, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hKS, Matrix.one_mulVec]
  have hXv : X₀ *ᵥ v = blockEmbed (W := W) j *ᵥ (schurBlock X₀ j *ᵥ u) := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
  have hq : star v ⬝ᵥ (X₀ *ᵥ v) = star u ⬝ᵥ (schurBlock X₀ j *ᵥ u) := by
    rw [hXv, star_dotProduct_blockEmbed_mulVec, hEv]
  have h1 := h v
  rw [hq] at h1
  have h2 := re_star_dotProduct_conjTranspose_blockEmbed_le j v
  rw [hEv] at h2
  exact (mul_le_mul_of_nonneg_left h2 hη.le).trans h1

/-- Schur-complement trace identity: if `X₀` on `ℂ^{kW}` has imaginary margin `η > 0` and `a` on
`ℂ^W` is Hermitian, then `Tr (P_{{j}} (X₀ + E a Eᴴ)⁻¹) = Tr ((a + S)⁻¹)` with `S = schurBlock X₀ j`;
all inverses are two-sided (the matrices are nonsingular). -/
theorem trace_blockProjector_inv_embed {η : ℝ} (hη : 0 < η)
    {X₀ : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ} (h : HasImMargin η X₀) (j : Fin k)
    (a : Matrix (Fin W) (Fin W) ℂ) (ha : a.IsHermitian) :
    (blockProjector {j} * (X₀ + blockEmbed (W := W) j * a * (blockEmbed (W := W) j)ᴴ)⁻¹).trace =
      ((a + schurBlock X₀ j)⁻¹).trace := by
  set E := blockEmbed (W := W) j with hE
  have hEa : (E * a * Eᴴ).IsHermitian := by
    exact isHermitian_mul_mul_conjTranspose E ha
  have hXm : HasImMargin η (X₀ + E * a * Eᴴ) := h.add_hermitian hEa
  have hXu := hXm.isUnit_det hη
  have hX := h.isUnit_det hη
  have hK := isUnit_compressedInverse hη h j
  set K := Eᴴ * X₀⁻¹ * E with hKdef
  set S := schurBlock X₀ j with hSdef
  have hKS : K * S = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det K).mp hK)
  have hSK : S * K = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det K).mp hK)
  set G := (X₀ + E * a * Eᴴ)⁻¹ with hG
  have hGX : G * (X₀ + E * a * Eᴴ) = 1 := Matrix.nonsing_inv_mul _ hXu
  -- `G = X₀⁻¹ - G E a Eᴴ X₀⁻¹`
  have h1 : G + G * E * a * Eᴴ * X₀⁻¹ = X₀⁻¹ := by
    have := congrArg (· * X₀⁻¹) hGX
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul] at this
    rw [Matrix.mul_assoc G X₀, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one] at this
    simpa only [Matrix.mul_assoc] using this
  set T := Eᴴ * G * E with hT
  have h2 : T + T * a * K = K := by
    have := congrArg (fun Z => Eᴴ * Z * E) h1
    simp only [Matrix.mul_add, Matrix.add_mul] at this
    rw [hT, hKdef]
    simpa only [Matrix.mul_assoc] using this
  have h3 : T * (a + S) = 1 := by
    have h4 : T * (a + S) * K = K := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc T S K, hSK, Matrix.mul_one,
        add_comm]
      exact h2
    calc T * (a + S) = T * (a + S) * (K * S) := by rw [hKS, Matrix.mul_one]
      _ = K * S := by rw [← Matrix.mul_assoc, h4]
      _ = 1 := hKS
  rw [trace_blockProjector_singleton_mul, Matrix.inv_eq_left_inv h3]

/-- The Schur block is a Borel-measurable function of `X₀` (nonsingular inverses). -/
theorem measurable_schurBlock (j : Fin k) :
    Measurable (fun X₀ : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ => schurBlock X₀ j) := by
  have hc : Continuous (fun Z : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ =>
      (blockEmbed (W := W) j)ᴴ * Z * blockEmbed (W := W) j) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact measurable_matrix_inv.comp (hc.measurable.comp measurable_matrix_inv)

/-- `(η i) • 1` has margin `η` for every real `η`. -/
theorem hasImMargin_I_smul_one {n : Type} [Fintype n] [DecidableEq n] (η : ℝ) :
    HasImMargin η (((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ)) := by
  intro v
  have him : (star v ⬝ᵥ v).im = 0 := by
    have := im_star_dotProduct_mulVec_hermitian (Matrix.isHermitian_one (n := n) (α := ℂ)) v
    rwa [Matrix.one_mulVec] at this
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im]
  simp [him]

/-- `i Y` has margin `0` for `Y` positive semidefinite. -/
theorem hasImMargin_I_smul_posSemidef {n : Type} [Fintype n]
    {Y : Matrix n n ℂ} (hY : Y.PosSemidef) : HasImMargin 0 (Complex.I • Y) := by
  intro v
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_im]
  simpa using hY.re_dotProduct_nonneg v

/-- Margins add. -/
theorem HasImMargin.add {n : Type} [Fintype n] {η₁ η₂ : ℝ} {N₁ N₂ : Matrix n n ℂ}
    (h₁ : HasImMargin η₁ N₁) (h₂ : HasImMargin η₂ N₂) : HasImMargin (η₁ + η₂) (N₁ + N₂) := by
  intro v
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_im, add_mul]
  exact add_le_add (h₁ v) (h₂ v)

/-- Margin of the absorbed background: for `D`
Hermitian, every `A i` Hermitian, `Y` positive semidefinite, `e` real and any real `η`, the
matrix `D + ⊕_i A_i - e + iY + iη` on `ℂ^{kW}` has imaginary margin `η`. -/
theorem hasImMargin_background {D Y : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ}
    {A : Fin k → Matrix (Fin W) (Fin W) ℂ} (hD : D.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (hY : Y.PosSemidef) (e : ℝ) {η : ℝ} :
    HasImMargin η (D + familyBlockSum A - (e : ℂ) • 1 + Complex.I • Y +
      ((η : ℂ) * Complex.I) • 1) := by
  have hH : (D + familyBlockSum A - (e : ℂ) • 1).IsHermitian :=
    (hD.add (familyBlockSum_isHermitian hA)).sub
      (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have h0 := (hasImMargin_I_smul_posSemidef hY).hermitian_add hH
  simpa using h0.add (hasImMargin_I_smul_one (n := Fin k × Fin W) η)

/-- The matrix inverted in `BlockModel.absorbedResolvent` has imaginary margin `η`, for
every outcome `w` and all real `e`, `η`. -/
theorem hasImMargin_absorbed (M : BlockModel k W) (e η : ℝ) (w : M.Ω) :
    HasImMargin η (M.H w - (e : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) +
      Complex.I • M.Y w + ((η : ℂ) * Complex.I) • 1) :=
  hasImMargin_background (M.hermitian_D w) (M.hermitian_A w) (M.posSemidef_Y w) e

end BlockBand.Wegner
