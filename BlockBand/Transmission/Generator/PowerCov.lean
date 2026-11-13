module

public import BlockBand.Transmission.Generator.PowerSand

/-!
# Contracting the passive covariance with the quadratic term

For a random matrix `U` with mean `Ū`, `Q ⪰ 0` with eigenbasis `u_i`, eigenvalues `t_i`, and
`S⁰ = sand Q (U - Ū)` (the centred Hermitian representative in the eigenbasis):
* `integral_quad_diag`: `E Tr pF2 (diag d) S⁰ (j+2) =
  Σ_{im} t_it_m wsum j d_i d_m · Cov(u_i, u_m, u_m, u_i)` (`bilinearCovariance`);
* `crossed_eigen_*`: in the eigenbasis, `I ⊗ (I-Q) = 1 - t_m`, `(I-Q) ⊗ I = 1 - t_i`,
  `f ⊗ f = f_ii f_mm`, `f* ⊗ f* = conj f_ii conj f_mm`, `fourNorm = 1`;
* **`quad_contract`**: given a covariance bound of the shape of the passive covariance lemma
  (`‖Cov - (a[I⊗(I-Q) + (I-Q)⊗I] + σ f⊗f + σ' f*⊗f*)‖ ≤ ε∏‖v_j‖`), at `d = c·t`:
  `|E Tr pF2 (diag(ct)) S⁰ (j+2) - Σ_{im} c^j w_im(a(2-t_i-t_m) + σ f_ii f_mm
  + σ' conj f_ii conj f_mm)| ≤ |c|^j ε Σ_{im} w_im`, `w_im = t_it_m wsum j t_i t_m`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

theorem wsum_mul_mul {R : Type*} [CommSemiring R] (j : ℕ) (c x y : R) :
    wsum j (c * x) (c * y) = c ^ j * wsum j x y := by
  rw [wsum, wsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [mul_pow, mul_pow, ← hp', pow_add]; ring

theorem wsum_nonneg (j : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ wsum j x y :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem wsum_le (j : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    wsum j x y ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
  have hb : ∀ p ∈ antidiagonal j, ((p.1 + 1 : ℕ) : ℝ) * x ^ p.1 * y ^ p.2 ≤ ((j + 1 : ℕ) : ℝ) := by
    intro p hp
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have h1 : x ^ p.1 * y ^ p.2 ≤ 1 := by
      have := mul_le_mul (pow_le_one₀ (n := p.1) hx hx1) (pow_le_one₀ (n := p.2) hy hy1) (by positivity)
        zero_le_one
      rwa [one_mul] at this
    have h2 : ((p.1 + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    calc ((p.1 + 1 : ℕ) : ℝ) * x ^ p.1 * y ^ p.2 = ((p.1 + 1 : ℕ) : ℝ) * (x ^ p.1 * y ^ p.2) := by
          ring
      _ ≤ ((j + 1 : ℕ) : ℝ) * 1 := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = _ := mul_one _
  refine (Finset.sum_le_sum hb).trans_eq ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]; ring

variable {W : ℕ} {Q : Matrix (Fin W) (Fin W) ℂ}

/-!
## The eigenbasis crossed tensors
-/

theorem ts_vec_self (hQ : Q.PosSemidef) (i : Fin W) : star (ts_vec hQ i) ⬝ᵥ ts_vec hQ i = 1 := by
  rw [star_self_eq, ts_vecNorm]; simp

theorem bilinear_eigen (hQ : Q.PosSemidef) (i : Fin W) :
    bilinear (ts_vec hQ i) Q (ts_vec hQ i) = (ts_lam hQ i : ℂ) := by
  have h1 := ts_vec_self hQ i
  simp only [ts_vec] at h1 ⊢
  rw [bilinear, hQ.isHermitian.mulVec_eigenvectorBasis, dotProduct_smul, h1, Complex.real_smul,
    mul_one]
  rfl

theorem bilinear_conjTranspose_self (u : Fin W → ℂ) (K : Matrix (Fin W) (Fin W) ℂ) :
    bilinear u Kᴴ u = conj (bilinear u K u) := quad_conjTranspose K u

theorem bilinear_one_eigen (hQ : Q.PosSemidef) (i : Fin W) :
    bilinear (ts_vec hQ i) 1 (ts_vec hQ i) = 1 := by
  rw [bilinear, one_mulVec, ts_vec_self]

theorem bilinear_one_sub_eigen (hQ : Q.PosSemidef) (i : Fin W) :
    bilinear (ts_vec hQ i) (1 - Q) (ts_vec hQ i) = 1 - (ts_lam hQ i : ℂ) := by
  rw [bilinear, sub_mulVec, dotProduct_sub, ← bilinear, ← bilinear, bilinear_one_eigen,
    bilinear_eigen]

theorem fourNorm_eigen (hQ : Q.PosSemidef) (i m : Fin W) :
    fourNorm (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i) = 1 := by
  simp [fourNorm, ts_vecNorm]

/-!
## The expected quadratic term
-/

section Quad

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem sand_mul_sand (hQ : Q.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) (i m : Fin W) :
    sand hQ Z i m * sand hQ Z m i =
      ((ts_lam hQ i * ts_lam hQ m : ℝ) : ℂ) * (ts_ent hQ Z i m * ts_ent hQ Z m i) := by
  rw [sand_apply, sand_apply]
  have h : (Real.sqrt (ts_lam hQ i) * Real.sqrt (ts_lam hQ m)) *
      (Real.sqrt (ts_lam hQ m) * Real.sqrt (ts_lam hQ i)) = ts_lam hQ i * ts_lam hQ m := by
    rw [show (Real.sqrt (ts_lam hQ i) * Real.sqrt (ts_lam hQ m)) *
        (Real.sqrt (ts_lam hQ m) * Real.sqrt (ts_lam hQ i)) =
        (Real.sqrt (ts_lam hQ i) * Real.sqrt (ts_lam hQ i)) *
        (Real.sqrt (ts_lam hQ m) * Real.sqrt (ts_lam hQ m)) by ring,
      Real.mul_self_sqrt (ts_lam_nonneg hQ i), Real.mul_self_sqrt (ts_lam_nonneg hQ m)]
  rw [← h]; push_cast; ring

/-- **The expected quadratic term at a diagonal representative.** -/
theorem integral_quad_diag (hQ : Q.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hQ (U ω - matrixExpect μ U) i m *
      ts_ent hQ (U ω - matrixExpect μ U) m i) μ) (d : Fin W → ℂ) (j : ℕ) :
    ∫ ω, (pF2 (diagonal d) (sand hQ (U ω - matrixExpect μ U)) (j + 2)).trace ∂μ =
      ∑ i, ∑ m, ((ts_lam hQ i * ts_lam hQ m : ℝ) : ℂ) * wsum j (d i) (d m) *
        bilinearCovariance μ U (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i) := by
  simp only [trace_pF2_diag, sand_mul_sand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ =>
    ((hp i m).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun m _ => ((hp i m).const_mul _).mul_const _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, integral_const_mul, bilinearCovariance]
  simp only [ts_ent]; ring

/-- **The covariance contracted with the quadratic term.** -/
theorem quad_contract (hQ : Q.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hQ (U ω - matrixExpect μ U) i m *
      ts_ent hQ (U ω - matrixExpect μ U) m i) μ) (f : Matrix (Fin W) (Fin W) ℂ)
    (a σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      (a * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - Q) + crossedTensor v₁ v₂ v₃ v₄ (1 - Q) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) (c : ℝ) (j : ℕ) :
    let t := ts_lam hQ
    let w : Fin W → Fin W → ℝ := fun i m => t i * t m * wsum j (t i) (t m)
    let fd : Fin W → ℂ := fun i => ts_ent hQ f i i
    ‖∫ ω, (pF2 (diagonal fun i => ((c * t i : ℝ) : ℂ)) (sand hQ (U ω - matrixExpect μ U))
        (j + 2)).trace ∂μ -
      ∑ i, ∑ m, ((c ^ j : ℝ) : ℂ) * ((w i m : ℂ) * (a * ((2 - t i - t m : ℝ) : ℂ) +
        σ * (fd i * fd m) + σ' * (conj (fd i) * conj (fd m))))‖ ≤
      |c| ^ j * ε * ∑ i, ∑ m, w i m := by
  intro t w fd
  rw [integral_quad_diag hQ U hp]
  have hcross : ∀ i m, a * (crossedTensor (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i)
      1 (1 - Q) + crossedTensor (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i) (1 - Q) 1)
      + σ * crossedTensor (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i) f f
      + σ' * crossedTensor (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i) fᴴ fᴴ =
      a * ((2 - t i - t m : ℝ) : ℂ) + σ * (fd i * fd m) + σ' * (conj (fd i) * conj (fd m)) := by
    intro i m
    simp only [crossedTensor, bilinear_one_eigen, bilinear_one_sub_eigen,
      bilinear_conjTranspose_self, fd, ts_ent]
    push_cast; ring
  have hterm : ∀ i m, ‖((t i * t m : ℝ) : ℂ) * wsum j (((c * t i : ℝ) : ℂ)) (((c * t m : ℝ) : ℂ)) *
        bilinearCovariance μ U (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i) -
      ((c ^ j : ℝ) : ℂ) * ((w i m : ℂ) * (a * ((2 - t i - t m : ℝ) : ℂ) + σ * (fd i * fd m) +
        σ' * (conj (fd i) * conj (fd m))))‖ ≤ |c| ^ j * ε * w i m := by
    intro i m
    have hw : ((t i * t m : ℝ) : ℂ) * wsum j (((c * t i : ℝ) : ℂ)) (((c * t m : ℝ) : ℂ)) =
        ((c ^ j : ℝ) : ℂ) * (w i m : ℂ) := by
      simp only [w]; push_cast; rw [wsum_mul_mul, ← wsum_ofReal]; ring
    rw [hw, ← hcross, mul_assoc, ← mul_sub, ← mul_sub, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
      abs_of_nonneg (show 0 ≤ w i m from mul_nonneg (mul_nonneg (ts_lam_nonneg hQ i)
        (ts_lam_nonneg hQ m)) (wsum_nonneg j (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ m)))]
    have h := hcov (ts_vec hQ i) (ts_vec hQ m) (ts_vec hQ m) (ts_vec hQ i)
    rw [fourNorm_eigen, mul_one] at h
    have hw0 : 0 ≤ w i m := mul_nonneg (mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ m))
      (wsum_nonneg j (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ m))
    calc |c| ^ j * (w i m * ‖_‖) ≤ |c| ^ j * (w i m * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hw0) (by positivity)
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => hterm i m)

end Quad

end BlockBand.Transmission.Generator
