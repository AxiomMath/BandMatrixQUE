module
public import BlockBand.Internal.Contracts.TransmissionFlow
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Matrix algebra of the rotation–damping coefficients

Pointwise identities for `rotationNoise r α`, `rotationDrift r κ`, for one coefficient value
`r : Fin N → Fin N → ℝ`
(symmetric, `≥ 0`) and `κ : Fin N → ℝ`:

* `rotationNoise_conjTranspose`: each noise matrix is skew-Hermitian;
* `rotationDrift_mul_apply`: `(D M)_kj = -½(∑_{m≠k} r_km + κ_k) M_kj`;
* `sum_massGenerator_mul`: `∑_l L_kl f_l` for `L = massGenerator`, split into the diagonal and
  off-diagonal parts (used for the second-moment drift).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open Matrix BlockBand.Internal.Contracts.TransmissionFlow
open scoped BigOperators ComplexOrder

variable {N : ℕ}

theorem single_mul_apply' (i j : Fin N) (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) (k l : Fin N) :
    (Matrix.single i j c * M) k l = if k = i then c * M j l else 0 := by
  by_cases h : k = i
  · subst h
    rw [ite_eq_left rfl, single_mul_apply_same]
  · rw [ite_eq_right h, single_mul_apply_of_ne _ _ _ _ _ h]

theorem rotX_mul_apply (i j : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) (k l : Fin N) :
    (rotX i j * M) k l = (if k = j then M i l else 0) - (if k = i then M j l else 0) := by
  simp only [rotX, Matrix.sub_mul, Matrix.sub_apply, single_mul_apply', one_mul]

theorem rotY_mul_apply (i j : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) (k l : Fin N) :
    (rotY i j * M) k l =
      Complex.I * ((if k = j then M i l else 0) + (if k = i then M j l else 0)) := by
  rw [rotY, Matrix.smul_mul, Matrix.smul_apply, Matrix.add_mul, Matrix.add_apply,
    single_mul_apply', single_mul_apply', one_mul, one_mul, smul_eq_mul]

/-- One pair `(p,q)`, both phases: `∑_e |(σ_{(p,q),e} M)_kj|²`. -/
theorem sum_fin2_norm_sq (r : Fin N → Fin N → ℝ) (hr : ∀ k l, 0 ≤ r k l)
    (M : Matrix (Fin N) (Fin N) ℂ) (p q k j : Fin N) :
    ∑ e : Fin 2, ‖(rotationNoise r ((p, q), e) * M) k j‖ ^ 2 =
      if p < q then r p q * ((if k = q then ‖M p j‖ ^ 2 else 0) +
        (if k = p then ‖M q j‖ ^ 2 else 0)) else 0 := by
  rw [Fin.sum_univ_two]
  by_cases hpq : p < q
  · have hne : p ≠ q := ne_of_lt hpq
    have hs : ‖((Real.sqrt (r p q / 2) : ℝ) : ℂ)‖ ^ 2 = r p q / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt (div_nonneg (hr p q) (by norm_num))]
    simp only [rotationNoise, hpq, ite_true, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Fin.isValue, ite_eq_right (by decide : ¬((1 : Fin 2) = 0)), rotX_mul_apply,
      rotY_mul_apply, norm_mul, mul_pow, hs, Complex.norm_I, one_mul]
    by_cases hkq : k = q
    · subst hkq
      simp only [ite_true, Ne.symm hne, ite_false, sub_zero, add_zero]
      ring
    · by_cases hkp : k = p
      · subst hkp
        simp only [hkq, ite_true, ite_false, zero_sub, norm_neg, zero_add]
        ring
      · simp only [hkq, hkp, ite_false, sub_zero, add_zero, norm_zero]
        ring
  · simp [rotationNoise, hpq]

/-- The pair sum behind the row structure (uses symmetry of `r`). -/
theorem pair_sum (r : Fin N → Fin N → ℝ) (hs : ∀ k l, r k l = r l k) (f : Fin N → ℝ)
    (k : Fin N) :
    ∑ p, ∑ q, (if p < q then r p q * ((if k = q then f p else 0) +
      (if k = p then f q else 0)) else 0) = ∑ m ∈ Finset.univ.erase k, r k m * f m := by
  have h1 : ∀ p q : Fin N, (if p < q then r p q * ((if k = q then f p else 0) +
      (if k = p then f q else 0)) else 0) =
      (if q = k then (if p < k then r k p * f p else 0) else 0) +
      (if p = k then (if k < q then r k q * f q else 0) else 0) := by
    intro p q
    by_cases hqk : q = k
    · subst hqk
      by_cases hpq : p < q
      · simp [hpq, ne_of_lt hpq, (ne_of_lt hpq).symm, hs p q]
      · by_cases hpk : p = q
        · subst hpk; simp
        · simp [hpq, hpk]
    · by_cases hpk : p = k
      · subst hpk
        by_cases hpq : p < q
        · simp [hpq, Ne.symm hqk]
        · simp [hpq]
      · simp [Ne.symm hqk, Ne.symm hpk, hqk, hpk]
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm (f := fun p q => if p = k then (if k < q then r k q * f q else 0) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, ← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  simp only [lt_irrefl, ite_false, add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≠ k := Finset.ne_of_mem_erase hm
  rcases lt_or_gt_of_ne hmk with h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, not_lt.2 h.le]

/-- **Row structure of the rotation noise**: `∑_α |(σ_α M)_kj|² = ∑_{m≠k} r_km |M_mj|²`. -/
theorem sum_norm_sq_rotationNoise_mul_apply (r : Fin N → Fin N → ℝ) (hs : ∀ k l, r k l = r l k)
    (hr : ∀ k l, 0 ≤ r k l) (M : Matrix (Fin N) (Fin N) ℂ) (k j : Fin N) :
    ∑ α : (Fin N × Fin N) × Fin 2, ‖(rotationNoise r α * M) k j‖ ^ 2 =
      ∑ m ∈ Finset.univ.erase k, r k m * ‖M m j‖ ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [sum_fin2_norm_sq r hr M]
  exact pair_sum r hs (fun m => ‖M m j‖ ^ 2) k

theorem rotX_conjTranspose (i j : Fin N) : (rotX i j)ᴴ = -rotX i j := by
  simp only [rotX, conjTranspose_sub, conjTranspose_single, star_one, neg_sub]

theorem rotY_conjTranspose (i j : Fin N) : (rotY i j)ᴴ = -rotY i j := by
  simp only [rotY, conjTranspose_smul, conjTranspose_add, conjTranspose_single, star_one,
    Complex.star_def, Complex.conj_I, neg_smul, add_comm]

/-- Each noise matrix is skew-Hermitian. -/
theorem rotationNoise_conjTranspose (r : Fin N → Fin N → ℝ) (α : (Fin N × Fin N) × Fin 2) :
    (rotationNoise r α)ᴴ = -rotationNoise r α := by
  unfold rotationNoise
  split_ifs
  · rw [conjTranspose_smul, rotX_conjTranspose, smul_neg, Complex.star_def, Complex.conj_ofReal]
  · rw [conjTranspose_smul, rotY_conjTranspose, smul_neg, Complex.star_def, Complex.conj_ofReal]
  · simp

/-- The diagonal drift acts row-wise. -/
theorem rotationDrift_mul_apply (r : Fin N → Fin N → ℝ) (κ : Fin N → ℝ)
    (M : Matrix (Fin N) (Fin N) ℂ) (k j : Fin N) :
    (rotationDrift r κ * M) k j =
      (((-(1 / 2 : ℝ)) * ((∑ m ∈ Finset.univ.erase k, r k m) + κ k) : ℝ) : ℂ) * M k j := by
  rw [rotationDrift, diagonal_mul]

theorem rotationDrift_conjTranspose (r : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) :
    (rotationDrift r κ)ᴴ = rotationDrift r κ := by
  rw [rotationDrift, diagonal_conjTranspose]
  congr 1
  funext k
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-- `∑_l L_kl f_l` for `L = massGenerator` at a single time. -/
theorem sum_massGenerator_mul (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (x : ℝ)
    (f : Fin N → ℝ) (k : Fin N) :
    ∑ l, massGenerator r κ x k l * f l =
      (-(∑ m ∈ Finset.univ.erase k, r x k m) - κ x k) * f k +
        ∑ m ∈ Finset.univ.erase k, r x k m * f m := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp only [massGenerator, ite_true]
  · refine Finset.sum_congr rfl fun m hm => ?_
    simp only [massGenerator, ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hm))]

end BlockBand.SourceProcess.Stochastic.RotationFlow
