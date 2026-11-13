module

public import BlockBand.Endpoints.Response.RemoteHigherWindowContracts

/-!
# Moving the energy of the near clock: an exact pathwise identity

**Identity.** On a path sample `π` (blocks `A_i`, internal bonds, port bonds `B_0, B_1`), let
`C` be the port coupling, `z = boundaryZ b E`, `z' = boundaryZ b e`, `δ = e - E`, and real
`λ > 0`, `α` with `α = λ²/z - 1/z'` (possible exactly when `λ² = Im(1/z')/Im(1/z)`). Let `Tπ`
have blocks `A_i - δ + α D_i` (`D_i` the `i`-th diagonal block of `CC*`, i.e. `B_0B_0*` at the
near end and `B_1B_1*` at the far end), the same internal bonds and port bonds `λB_j`. Then the
full matrices with matched leads satisfy
`𝓜_{E,z}(Tπ) = diag(1, p) · 𝓜_{e,z'}(π) · [[1, 0], [αC*, λ]]`, `p = z/(z'λ)`,
hence the boundary-to-interior maps satisfy `𝒰_{e,z'}(π) = p · 𝒰_{E,z}(Tπ)` and the near clocks
`A_{e}(π) = |p|² A_{E}(Tπ)` (`rhw_clock_transform`). No invertibility hypothesis: the matrix
inverse of `Mathlib` is total and `(XY)⁻¹ = Y⁻¹X⁻¹` holds for all square matrices.

* `rhwFull`, `rhwU`, `rhwClock` — the full matrix, `𝒰` and the near clock on a path sample at
  energy `E` and lead parameter `z`; `nearClock b E W n q ω = rhwClock … (pathAt W n ω)` (`rfl`).
* `rhwT` — the transform; `rhw_full_transform`, `rhw_U_transform`, `rhw_clock_transform`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Endpoints (nearClock)

variable {W n : ℕ}

/-- The full matrix `[[H - E, C], [C*, z]]` of a path sample with two leads of parameter `z`. -/
def rhwFull (E : ℝ) (z : ℂ) (π : PathSample W n) : Matrix (FullSite W n) (FullSite W n) ℂ :=
  Matrix.fromBlocks (pathMatrix π - (E : ℂ) • 1) (pathPortCoupling π) (pathPortCoupling π)ᴴ
    (z • 1)

/-- `𝒰 = (𝓜⁻¹)₁₂`. -/
def rhwU (E : ℝ) (z : ℂ) (π : PathSample W n) : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ :=
  ((rhwFull E z π)⁻¹).toBlocks₁₂

/-- The interval source `Σ_k (q_k/W²) 𝒰* P_k 𝒰` on a path sample. -/
def rhwSource (E : ℝ) (z : ℂ) (W n : ℕ) (q : ℝ → ℝ) (π : PathSample W n) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ∑ k ∈ Finset.range n, ((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) •
    ((rhwU E z π)ᴴ * tagProjection W n k * rhwU E z π)

/-- The near clock on a path sample. -/
def rhwClock (E : ℝ) (z : ℂ) (W n : ℕ) (q : ℝ → ℝ) (π : PathSample W n) :
    Matrix (Fin W) (Fin W) ℂ :=
  portBlock (rhwSource E z W n q π) 0 0

theorem rhw_nearClock_eq (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    nearClock b E W n q ω = rhwClock E (boundaryZ b E) W n q (pathAt W n ω) := rfl

/-- The `i`-th diagonal block of `CC*`: `B_0B_0*` at position `0`, `B_1B_1*` at position
`n - 1`. -/
def rhwPortGram (π : PathSample W n) (i : Fin n) : Matrix (Fin W) (Fin W) ℂ :=
  (if i.val = 0 then π.2.2 0 * (π.2.2 0)ᴴ else 0) +
    (if i.val + 1 = n then π.2.2 1 * (π.2.2 1)ᴴ else 0)

/-- The transform `Tπ`: blocks `A_i - δ + α D_i`, internal bonds unchanged, port bonds `λB_j`. -/
def rhwT (δ α lam : ℝ) (π : PathSample W n) : PathSample W n :=
  (fun i => π.1 i - (δ : ℂ) • 1 + (α : ℂ) • rhwPortGram π i, π.2.1,
    fun j => (lam : ℂ) • π.2.2 j)

theorem rhw_coupling_transform (δ α lam : ℝ) (π : PathSample W n) :
    pathPortCoupling (rhwT δ α lam π) = (lam : ℂ) • pathPortCoupling π := by
  ext x y
  simp only [pathPortCoupling, rhwT, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem rhw_coupling_gram (π : PathSample W n) (x y : Fin n × Fin W) :
    (pathPortCoupling π * (pathPortCoupling π)ᴴ) x y =
      if x.1 = y.1 then rhwPortGram π x.1 x.2 y.2 else 0 := by
  have hC : ∀ (x : Fin n × Fin W) (j : Fin 2) (c : Fin W), pathPortCoupling π x (j, c) =
      if (j = 0 ∧ x.1.val = 0) ∨ (j = 1 ∧ x.1.val + 1 = n) then π.2.2 j x.2 c else 0 :=
    fun _ _ _ => rfl
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, hC]
  rcases x with ⟨i, a⟩
  rcases y with ⟨i', a'⟩
  simp only [rhwPortGram]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  by_cases hxy : i = i'
  · subst hxy
    simp only [true_and, h10, false_and, false_or, ite_true, Fin.isValue]
    split_ifs <;> simp_all [Matrix.mul_apply]
  · have hii : i.val ≠ i'.val := fun h => hxy (Fin.ext h)
    simp only [true_and, h10, false_and, false_or, hxy, ite_false, Fin.isValue]
    split_ifs <;> first | omega | simp

theorem rhw_pathMatrix_transform (δ α lam : ℝ) (π : PathSample W n) :
    pathMatrix (rhwT δ α lam π) = pathMatrix π - (δ : ℂ) • 1 +
      (α : ℂ) • (pathPortCoupling π * (pathPortCoupling π)ᴴ) := by
  ext x y
  rw [Matrix.add_apply, Matrix.smul_apply, rhw_coupling_gram, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply]
  simp only [pathMatrix, rhwT]
  by_cases hxy : x.1 = y.1
  · simp only [hxy, ite_true, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases h2 : x.2 = y.2
    · have : x = y := Prod.ext hxy h2
      simp [this]
    · have : x ≠ y := fun h => h2 (congrArg Prod.snd h)
      simp [this, h2]
  · have : x ≠ y := fun h => hxy (congrArg Prod.fst h)
    simp [hxy, this]

/-- **The full-matrix factorization.** If `e = E + δ`, `λ ≠ 0`, `z, z' ≠ 0` and
`α = λ²/z - 1/z'`, then `𝓜_{E,z}(Tπ) = diag(1, p) 𝓜_{e,z'}(π) [[1, 0], [αC*, λ]]`,
`p = z/(z'λ)`. -/
theorem rhw_full_transform {E e δ α lam : ℝ} {z z' : ℂ} (he : e = E + δ) (hlam : lam ≠ 0)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hα : (α : ℂ) = (lam : ℂ) ^ 2 * z⁻¹ - z'⁻¹)
    (π : PathSample W n) :
    rhwFull E z (rhwT δ α lam π) =
      Matrix.fromBlocks 1 0 0 ((z / (z' * lam)) • 1) * rhwFull e z' π *
        Matrix.fromBlocks 1 0 ((α : ℂ) • (pathPortCoupling π)ᴴ) ((lam : ℂ) • 1) := by
  have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  unfold rhwFull
  rw [rhw_pathMatrix_transform, rhw_coupling_transform, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, smul_zero]
  have h21 : z / (z' * lam) + z / (z' * lam) * z' * α = lam := by
    rw [hα]
    have : z / (z' * lam) * z' = z / lam := by field_simp
    rw [this]
    field_simp
    ring
  have h22 : z / (z' * lam) * z' * lam = z := by field_simp
  congr 1
  all_goals first
    | rfl
    | (rw [he]; push_cast; module)
    | (rw [← add_smul]; congr 1; linear_combination -h21)
    | (congr 1; linear_combination -h22)

/-- `(fromBlocks 1 0 0 (c•1))⁻¹ = fromBlocks 1 0 0 (c⁻¹•1)` for `c ≠ 0`. -/
theorem rhw_inv_diag {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    {c : ℂ} (hc : c ≠ 0) :
    (Matrix.fromBlocks (1 : Matrix m m ℂ) 0 0 (c • (1 : Matrix k k ℂ)))⁻¹ =
      Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_zero, zero_add,
    Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul,
    Matrix.fromBlocks_one]

/-- `[[1, 0], [αX, λ]]⁻¹ = [[1, 0], [-(α/λ)X, 1/λ]]` for `λ ≠ 0`. -/
theorem rhw_inv_lower {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    {a l : ℂ} (hl : l ≠ 0) (X : Matrix k m ℂ) :
    (Matrix.fromBlocks (1 : Matrix m m ℂ) 0 (a • X) (l • (1 : Matrix k k ℂ)))⁻¹ =
      Matrix.fromBlocks 1 0 ((-(l⁻¹ * a)) • X) (l⁻¹ • 1) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    mul_inv_cancel₀ hl, one_smul]
  rw [← add_smul]; ring_nf; simp

/-- **`𝒰_{e,z'}(π) = p · 𝒰_{E,z}(Tπ)`**, `p = z/(z'λ)`. -/
theorem rhw_U_transform {E e δ α lam : ℝ} {z z' : ℂ} (he : e = E + δ) (hlam : lam ≠ 0)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hα : (α : ℂ) = (lam : ℂ) ^ 2 * z⁻¹ - z'⁻¹)
    (π : PathSample W n) :
    rhwU e z' π = (z / (z' * lam)) • rhwU E z (rhwT δ α lam π) := by
  have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hp : z / (z' * lam) ≠ 0 := div_ne_zero hz (mul_ne_zero hz' hlamc)
  unfold rhwU
  rw [rhw_full_transform he hlam hz hz' hα, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    rhw_inv_diag hp, rhw_inv_lower hlamc, ← Matrix.fromBlocks_toBlocks (rhwFull e z' π)⁻¹,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_zero, zero_add,
    Matrix.mul_smul, Matrix.mul_one, smul_zero, Matrix.toBlocks_fromBlocks₁₂, smul_smul,
    mul_inv_cancel₀ hp, one_smul]

/-- **The near clock under the transform**: `A_{e,z'}(π) = |p|² A_{E,z}(Tπ)`. -/
theorem rhw_clock_transform {E e δ α lam : ℝ} {z z' : ℂ} (he : e = E + δ) (hlam : lam ≠ 0)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hα : (α : ℂ) = (lam : ℂ) ^ 2 * z⁻¹ - z'⁻¹)
    (q : ℝ → ℝ) (π : PathSample W n) :
    rhwClock e z' W n q π =
      ((Complex.normSq (z / (z' * lam)) : ℝ) : ℂ) • rhwClock E z W n q (rhwT δ α lam π) := by
  unfold rhwClock rhwSource
  rw [rhw_U_transform he hlam hz hz' hα]
  set p := z / (z' * lam)
  set U := rhwU E z (rhwT δ α lam π)
  have key : ∀ k, (p • U)ᴴ * tagProjection W n k * (p • U) =
      ((Complex.normSq p : ℝ) : ℂ) • (Uᴴ * tagProjection W n k * U) := by
    intro k
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp_rw [key, smul_comm _ ((Complex.normSq p : ℝ) : ℂ), ← Finset.smul_sum]
  ext x y
  simp [portBlock]

end BlockBand.Endpoints
