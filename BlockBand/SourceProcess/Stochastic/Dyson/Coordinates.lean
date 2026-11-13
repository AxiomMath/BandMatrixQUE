module

public import BlockBand.SourceProcess.Stochastic.Dyson.Spectrum

/-!
# Dyson Brownian motion: real orthonormal coordinates on Hermitian matrices

The basis `hermBasis x`, `x = (a, b) ∈ Fin N × Fin N`, is
* `e_a e_aᵀ` for `a = b`,
* `(e_a e_bᵀ + e_b e_aᵀ)/√2` for `a < b`,
* `i (e_a e_bᵀ - e_b e_aᵀ)/√2`... more precisely `i (e_b e_aᵀ - e_a e_bᵀ)/√2` for `a > b`.

It is orthonormal for `(A, B) ↦ tr(A B)` and satisfies the completeness (contraction) identity
`∑_x (E_x)_{ab} (E_x)_{cd} = δ_{ad} δ_{bc}`, which is the deterministic half of the GUE Itô
contraction `E[G_ab G_cd] = δ_ad δ_bc / N`. Coordinates: `hermCoord H x = Re tr(E_x H)`;
inverse: `hermOfCoord y = ∑_x y_x E_x`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix
open scoped Matrix ComplexConjugate

variable {N : ℕ}

/-- `1/√2` as a complex number. -/
def isq2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem isq2_mul_isq2 : isq2 * isq2 = 1 / 2 := by
  unfold isq2
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; ring

theorem conj_isq2 : conj isq2 = isq2 := Complex.conj_ofReal _

/-- Indicator entry `[a = p ∧ b = q]`. -/
def ind (p q a b : Fin N) : ℂ := if a = p ∧ b = q then 1 else 0

/-- The orthonormal Hermitian basis, indexed by `Fin N × Fin N`. -/
def hermBasis (x : Fin N × Fin N) : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a b =>
  if x.1 = x.2 then ind x.1 x.1 a b
  else if x.1 < x.2 then isq2 * (ind x.1 x.2 a b + ind x.2 x.1 a b)
  else Complex.I * isq2 * (ind x.2 x.1 a b - ind x.1 x.2 a b)

theorem hermBasis_diag (p a b : Fin N) : hermBasis (p, p) a b = ind p p a b := by
  simp [hermBasis]

theorem hermBasis_lt {p q : Fin N} (h : p < q) (a b : Fin N) :
    hermBasis (p, q) a b = isq2 * (ind p q a b + ind q p a b) := by
  simp [hermBasis, h.ne, h]

theorem hermBasis_gt {p q : Fin N} (h : q < p) (a b : Fin N) :
    hermBasis (p, q) a b = Complex.I * isq2 * (ind q p a b - ind p q a b) := by
  simp [hermBasis, h.ne', not_lt.mpr h.le]

theorem conj_ind (p q a b : Fin N) : conj (ind p q a b) = ind p q a b := by
  unfold ind; split_ifs <;> simp

theorem ind_swap (p q a b : Fin N) : ind p q a b = ind q p b a := by
  unfold ind; congr 1; exact propext and_comm

/-- Each basis matrix is Hermitian. -/
theorem hermBasis_isHermitian (x : Fin N × Fin N) : (hermBasis x).IsHermitian := by
  ext a b
  obtain ⟨p, q⟩ := x
  simp only [conjTranspose_apply, RCLike.star_def]
  rcases lt_trichotomy p q with h | rfl | h
  · rw [hermBasis_lt h, hermBasis_lt h, map_mul, map_add, conj_isq2, conj_ind, conj_ind,
      ind_swap p q b a, ind_swap q p b a, add_comm]
  · rw [hermBasis_diag, hermBasis_diag, conj_ind]
    unfold ind; split_ifs <;> simp_all
  · rw [hermBasis_gt h, hermBasis_gt h, map_mul, map_mul, map_sub, conj_isq2, conj_ind,
      conj_ind, Complex.conj_I, ind_swap p q b a, ind_swap q p b a]
    ring

theorem ind_self (p q : Fin N) : ind p q p q = 1 := by simp [ind]

theorem ind_of_ne {p q a b : Fin N} (h : ¬ (a = p ∧ b = q)) : ind p q a b = 0 := by
  simp [ind, h]

/-- Support of a basis matrix: `(E_x)_{ab} ≠ 0` forces `x ∈ {(a,b), (b,a)}`. -/
theorem hermBasis_support {x : Fin N × Fin N} {a b : Fin N} (h : hermBasis x a b ≠ 0) :
    x = (a, b) ∨ x = (b, a) := by
  obtain ⟨p, q⟩ := x
  rcases lt_trichotomy p q with hpq | rfl | hpq
  · rw [hermBasis_lt hpq] at h
    by_cases h1 : a = p ∧ b = q
    · left; obtain ⟨rfl, rfl⟩ := h1; rfl
    by_cases h2 : a = q ∧ b = p
    · right; obtain ⟨rfl, rfl⟩ := h2; rfl
    exact absurd (by rw [ind_of_ne h1, ind_of_ne h2]; ring) h
  · rw [hermBasis_diag] at h
    by_cases h1 : a = p ∧ b = p
    · left; obtain ⟨rfl, rfl⟩ := h1; rfl
    exact absurd (ind_of_ne h1) h
  · rw [hermBasis_gt hpq] at h
    by_cases h1 : a = p ∧ b = q
    · left; obtain ⟨rfl, rfl⟩ := h1; rfl
    by_cases h2 : a = q ∧ b = p
    · right; obtain ⟨rfl, rfl⟩ := h2; rfl
    exact absurd (by rw [ind_of_ne h1, ind_of_ne h2]; ring) h

theorem hermBasis_eq_zero {x : Fin N × Fin N} {a b : Fin N} (h1 : x ≠ (a, b)) (h2 : x ≠ (b, a)) :
    hermBasis x a b = 0 := by
  by_contra h
  rcases hermBasis_support h with h' | h' <;> contradiction

theorem ind_comm_iff (a b c d : Fin N) : ind b a c d = (if a = d ∧ b = c then 1 else 0) := by
  unfold ind
  by_cases h : a = d ∧ b = c
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right h, ite_eq_right]; rintro ⟨rfl, rfl⟩; exact h ⟨rfl, rfl⟩

/-- **Completeness (GUE contraction) identity**: `∑_x (E_x)_{ab} (E_x)_{cd} = δ_{ad} δ_{bc}`. -/
theorem sum_hermBasis_mul_hermBasis (a b c d : Fin N) :
    ∑ x, hermBasis x a b * hermBasis x c d = if a = d ∧ b = c then 1 else 0 := by
  rw [← ind_comm_iff]
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [Fintype.sum_eq_add (a, b) (b, a) (by simp [hab.ne])
      (fun x hx => by rw [hermBasis_eq_zero hx.1 hx.2, zero_mul])]
    simp only [hermBasis_lt hab, hermBasis_gt hab, ind_self,
      ind_of_ne (show ¬ (a = b ∧ b = a) from fun h => hab.ne h.1)]
    linear_combination (ind a b c d + ind b a c d - (ind a b c d - ind b a c d)) *
      isq2_mul_isq2 + (ind a b c d - ind b a c d) * isq2 ^ 2 * Complex.I_sq
  · rw [Fintype.sum_eq_single (a, a) (fun x hx => by rw [hermBasis_eq_zero hx hx, zero_mul])]
    rw [hermBasis_diag, hermBasis_diag, ind_self, one_mul]
  · rw [Fintype.sum_eq_add (a, b) (b, a) (by simp [hab.ne'])
      (fun x hx => by rw [hermBasis_eq_zero hx.1 hx.2, zero_mul])]
    simp only [hermBasis_gt hab, hermBasis_lt hab, ind_self,
      ind_of_ne (show ¬ (a = b ∧ b = a) from fun h => hab.ne' h.1)]
    linear_combination (ind b a c d + ind a b c d + (ind b a c d - ind a b c d)) *
      isq2_mul_isq2 - (ind b a c d - ind a b c d) * isq2 ^ 2 * Complex.I_sq

theorem trace_hermBasis_mul (x : Fin N × Fin N) (M : Matrix (Fin N) (Fin N) ℂ) :
    trace (hermBasis x * M) = ∑ a, ∑ b, hermBasis x a b * M b a := by
  simp [trace, mul_apply]

/-- Completeness: every complex matrix is `∑_x tr(E_x M) E_x`. -/
theorem sum_trace_smul_hermBasis (M : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, trace (hermBasis x * M) • hermBasis x = M := by
  ext c d
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, trace_hermBasis_mul]
  rw [show (∑ x, (∑ a, ∑ b, hermBasis x a b * M b a) * hermBasis x c d) =
      ∑ a, ∑ b, M b a * ∑ x, hermBasis x a b * hermBasis x c d from ?_]
  · simp_rw [sum_hermBasis_mul_hermBasis, mul_ite, mul_one, mul_zero, ite_and]
    simp
  · simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => by ring

/-- Real coordinates `hermCoord H x = Re tr(E_x H)`. -/
def hermCoord (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (x : Fin N × Fin N) : ℝ :=
  (trace (hermBasis x * H)).re

/-- Inverse coordinates `hermOfCoord y = ∑_x y_x E_x` (always Hermitian). -/
def hermOfCoord (N : ℕ) (y : Fin N × Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ x, ((y x : ℝ) : ℂ) • hermBasis x

/-- For Hermitian `A, B`, `tr(A B)` is real. -/
theorem trace_mul_conj_eq {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : conj (trace (A * B)) = trace (A * B) := by
  have h := (trace_conjTranspose (A * B)).symm
  rw [conjTranspose_mul, hB.eq, hA.eq, trace_mul_comm B A] at h
  exact h

theorem trace_mul_re_eq {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (((trace (A * B)).re : ℝ) : ℂ) = trace (A * B) :=
  Complex.conj_eq_iff_re.mp (trace_mul_conj_eq hA hB)

theorem hermOfCoord_hermCoord {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    hermOfCoord N (hermCoord N H) = H := by
  unfold hermOfCoord hermCoord
  simp_rw [trace_mul_re_eq (hermBasis_isHermitian _) hH]
  exact sum_trace_smul_hermBasis H

theorem hermOfCoord_isHermitian (y : Fin N × Fin N → ℝ) : (hermOfCoord N y).IsHermitian := by
  unfold hermOfCoord IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [conjTranspose_smul, (hermBasis_isHermitian x).eq, Complex.star_def, Complex.conj_ofReal]

theorem hermOfCoord_apply (y : Fin N × Fin N → ℝ) (a b : Fin N) :
    hermOfCoord N y a b = ∑ x, ((y x : ℝ) : ℂ) * hermBasis x a b := by
  simp [hermOfCoord, Matrix.sum_apply]

/-- The basis as a square matrix `W_{x,(a,b)} = (E_x)_{ab}`. -/
def basisMat (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Matrix.of fun x z => hermBasis x z.1 z.2

/-- The swap permutation matrix on `Fin N × Fin N`. -/
def swapMat (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Matrix.of fun z z' => if z' = z.swap then 1 else 0

theorem basisMat_transpose_mul : (basisMat N)ᵀ * basisMat N = swapMat N := by
  ext z z'
  simp only [mul_apply, transpose_apply, basisMat, of_apply, swapMat]
  rw [sum_hermBasis_mul_hermBasis]
  obtain ⟨a, b⟩ := z; obtain ⟨c, d⟩ := z'
  simp only [Prod.swap_prod_mk, Prod.mk.injEq]
  by_cases h : a = d ∧ b = c
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [ite_eq_right h, ite_eq_right]; rintro ⟨rfl, rfl⟩; exact h ⟨rfl, rfl⟩

theorem swapMat_mul_self : swapMat N * swapMat N = 1 := by
  ext z z'
  simp only [mul_apply, swapMat, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single z.swap (fun w _ hw => by simp [hw])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Prod.swap_swap, ite_true, one_apply]
  by_cases h : z = z'
  · subst h; simp
  · rw [ite_eq_right (fun e => h e.symm), ite_eq_right h]

/-- **Orthonormality** `tr(E_x E_y) = δ_xy`, from completeness and `A B = 1 → B A = 1`. -/
theorem trace_hermBasis_mul_hermBasis (x y : Fin N × Fin N) :
    trace (hermBasis x * hermBasis y) = if x = y then 1 else 0 := by
  have h1 : (swapMat N * (basisMat N)ᵀ) * basisMat N = 1 := by
    rw [Matrix.mul_assoc, basisMat_transpose_mul, swapMat_mul_self]
  have h2 := congrArg (fun M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ => M x y)
    (mul_eq_one_comm.mp h1)
  rw [one_apply] at h2
  rw [← h2, trace_hermBasis_mul]
  simp only [mul_apply, transpose_apply, basisMat, swapMat, of_apply, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (b, a) (fun w _ hw => by simp [hw])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

/-- Coordinates of the coordinate matrix: `hermCoord (hermOfCoord y) = y`. -/
theorem hermCoord_hermOfCoord (y : Fin N × Fin N → ℝ) : hermCoord N (hermOfCoord N y) = y := by
  funext x
  simp only [hermCoord, hermOfCoord, Finset.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
    trace_hermBasis_mul_hermBasis, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq]

end BlockBand.SourceProcess.Stochastic.Dyson
