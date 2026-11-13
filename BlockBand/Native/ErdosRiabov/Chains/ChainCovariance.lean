module

public import BlockBand.Native.ErdosRiabov.Chains.ChainCalc

/-!
# Resolvent chains: the band covariance operator

For a symmetric variance profile `S` the covariance operator of the Hermitian coordinates is the
band self-energy `𝒮[X] = diag(S · diag X)`, and the second derivatives of resolvent chains contract
to `𝒮`-insertions.

## Coordinates and variances

* `covOp_hermBasis_bandWeight`: for symmetric `S`,
  `𝒮[X] := ∑_x S_{x} E_x X E_x = diag(S · diag X)` (`bandSelfEnergy`), i.e.
  `(𝒮[X])_aa = ∑_b S_ab X_bb` and `(𝒮[X])_ad = 0` for `a ≠ d` (`bandSelfEnergy_apply`).
* `sum_mul_fderiv_fderiv_chainTest_band`, `sum_smul_fderiv_fderiv_resChain_band`:
  along `y ↦ A₀ + hermOfCoord N y`,
  `∑_x S_x D²f(y)[e_x, e_x] = 2 ∑_{i ≤ j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)})`.
  Dividing by two gives the Itô correction `½ ∑_x v_x ∂²_x f` of the Itô equation for
  resolvent chains (the time factor of the zig flow is treated separately).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Chains
open Matrix Function
open BlockBand.Native.CEH.Flow BlockBand.SourceProcess.Stochastic.Dyson
open scoped ComplexConjugate

variable {N : ℕ}

/-- The band self-energy `𝒮[X] = diag(S · diag X)`. -/
def bandSelfEnergy (S : Matrix (Fin N) (Fin N) ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun a => ∑ b, (S a b : ℂ) * X b b

theorem bandSelfEnergy_apply (S : Matrix (Fin N) (Fin N) ℝ) (X : Matrix (Fin N) (Fin N) ℂ)
    (a d : Fin N) :
    bandSelfEnergy S X a d = if a = d then ∑ b, (S a b : ℂ) * X b b else 0 := by
  simp [bandSelfEnergy, diagonal_apply]

/-- Variance of the orthonormal coordinate `x = (p, q)`: `S_pq`. -/
def bandWeight (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin N × Fin N) : ℝ := S x.1 x.2

/-- Weighted completeness: for symmetric `S`,
`∑_x S_x (E_x)_{ab} (E_x)_{cd} = S_ab δ_{ad} δ_{bc}`. -/
theorem sum_weight_hermBasis_mul_hermBasis (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : ∀ a b, S a b = S b a) (a b c d : Fin N) :
    ∑ x : Fin N × Fin N, (S x.1 x.2 : ℂ) * (hermBasis x a b * hermBasis x c d) =
      (S a b : ℂ) * if a = d ∧ b = c then 1 else 0 := by
  rw [← sum_hermBasis_mul_hermBasis, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : hermBasis x a b = 0
  · simp [h]
  · rcases hermBasis_support h with rfl | rfl
    · rfl
    · show (S b a : ℂ) * _ = (S a b : ℂ) * _
      rw [hS b a]

/-- **Band covariance operator**: `∑_x S_x E_x X E_x = diag(S · diag X)` for symmetric `S`. -/
theorem covOp_hermBasis_bandWeight (S : Matrix (Fin N) (Fin N) ℝ) (hS : ∀ a b, S a b = S b a)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    covOp hermBasis (bandWeight S) X = bandSelfEnergy S X := by
  ext a d
  have h : ∀ x : Fin N × Fin N, (bandWeight S x • (hermBasis x * X * hermBasis x)) a d =
      ∑ b, ∑ c, X b c * ((S x.1 x.2 : ℂ) * (hermBasis x a b * hermBasis x c d)) := by
    intro x
    rw [Matrix.smul_apply, Complex.real_smul, bandWeight]
    simp only [mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  rw [covOp, Matrix.sum_apply, Finset.sum_congr rfl fun x _ => h x]
  have h2 : ∑ x : Fin N × Fin N, ∑ b, ∑ c,
        X b c * ((S x.1 x.2 : ℂ) * (hermBasis x a b * hermBasis x c d)) =
      ∑ b, ∑ c, X b c *
        ∑ x : Fin N × Fin N, (S x.1 x.2 : ℂ) * (hermBasis x a b * hermBasis x c d) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [h2]
  simp only [sum_weight_hermBasis_mul_hermBasis S hS, bandSelfEnergy_apply]
  by_cases had : a = d
  · subst had
    simp only [true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · simp [had]

/-- `hermOfCoord N` as a real-linear map `ℝ^{N×N} → Matrix`. -/
def hermOfCoordLin (N : ℕ) : (Fin N × Fin N → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun := hermOfCoord N
  map_add' y y' := by
    simp only [hermOfCoord, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  map_smul' r y := by
    simp only [hermOfCoord, RingHom.id_apply, Finset.smul_sum, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul, Complex.coe_smul]

theorem hermOfCoordLin_apply (y : Fin N × Fin N → ℝ) : hermOfCoordLin N y = hermOfCoord N y :=
  rfl

/-- The coordinate directions are the basis matrices. -/
theorem hermOfCoordLin_single (x : Fin N × Fin N) :
    hermOfCoordLin N (Pi.single x (1 : ℝ)) = hermBasis x := by
  rw [hermOfCoordLin_apply, hermOfCoord]
  rw [Finset.sum_eq_single x (fun x' _ hx' => by simp [hx'])
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

section MatrixLevel

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Band contraction (matrix level)**: along `y ↦ A₀ + hermOfCoord N y`, with variances
`v_x = S_x`, `∑_x S_x D²C(y)[e_x, e_x] = 2 ∑_{i ≤ j} G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)}`,
`𝒮 = bandSelfEnergy S`. Matrix-valued derivatives use the `Matrix.linftyOpNormedRing` norm
instance. -/
theorem sum_smul_fderiv_fderiv_resChain_band {k : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℂ)
    (z : Fin k → ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ) (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : ∀ a b, S a b = S b a) {y : Fin N × Fin N → ℝ}
    (hy : ∀ j, IsUnit (A₀ + hermOfCoordLin N y - z j • (1 : Matrix (Fin N) (Fin N) ℂ)).det) :
    ∑ x, S x.1 x.2 • fderiv ℝ (fderiv ℝ (resChain A₀ (hermOfCoordLin N) z B)) y
        (Pi.single x (1 : ℝ)) (Pi.single x (1 : ℝ)) =
      (2 : ℝ) • ∑ j, ∑ i with i ≤ j,
        pairIns B (resSlots A₀ (hermOfCoordLin N) z y) (bandSelfEnergy S) i j := by
  have h := sum_smul_fderiv_fderiv_resChain A₀ (hermOfCoordLin N) z B hy (bandWeight S)
    (fun x => Pi.single x (1 : ℝ))
  have hcov : covOp (fun x => hermOfCoordLin N (Pi.single x (1 : ℝ))) (bandWeight S) =
      bandSelfEnergy S := by
    funext X
    simp only [hermOfCoordLin_single]
    exact covOp_hermBasis_bandWeight S hS X
  rw [hcov] at h
  exact h

end MatrixLevel

/-- **Band contraction for test functions**: along `y ↦ A₀ + hermOfCoord N y`, for
`f = Re tr(K · chain)`,
`∑_x S_x ∂²_x f(y) = 2 ∑_{i ≤ j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)})`,
`𝒮[X] = diag(S · diag X)`. -/
theorem sum_mul_fderiv_fderiv_chainTest_band {k : ℕ} (A₀ : Matrix (Fin N) (Fin N) ℂ)
    (z : Fin k → ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (S : Matrix (Fin N) (Fin N) ℝ) (hS : ∀ a b, S a b = S b a) {y : Fin N × Fin N → ℝ}
    (hy : ∀ j, IsUnit (A₀ + hermOfCoordLin N y - z j • (1 : Matrix (Fin N) (Fin N) ℂ)).det) :
    ∑ x, S x.1 x.2 * fderiv ℝ (fderiv ℝ (chainTest A₀ (hermOfCoordLin N) z B K)) y
        (Pi.single x (1 : ℝ)) (Pi.single x (1 : ℝ)) =
      2 * ∑ j, ∑ i with i ≤ j,
        reTr K (pairIns B (resSlots A₀ (hermOfCoordLin N) z y) (bandSelfEnergy S) i j) := by
  have h := sum_mul_fderiv_fderiv_chainTest A₀ (hermOfCoordLin N) z B K hy (bandWeight S)
    (fun x => Pi.single x (1 : ℝ))
  have hcov : covOp (fun x => hermOfCoordLin N (Pi.single x (1 : ℝ))) (bandWeight S) =
      bandSelfEnergy S := by
    funext X
    simp only [hermOfCoordLin_single]
    exact covOp_hermBasis_bandWeight S hS X
  rw [hcov] at h
  exact h

/-!
### The coordinates in terms of matrix entries
-/

theorem hermCoord_diag (H : Matrix (Fin N) (Fin N) ℂ) (a : Fin N) :
    hermCoord N H (a, a) = (H a a).re := by
  simp [hermCoord, trace_hermBasis_mul, hermBasis_diag, ind, ite_and]

theorem trace_hermBasis_lt_mul {a b : Fin N} (h : a < b) (H : Matrix (Fin N) (Fin N) ℂ) :
    trace (hermBasis (a, b) * H) = isq2 * (H b a + H a b) := by
  simp [trace_hermBasis_mul, hermBasis_lt h, ind, ite_and, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem trace_hermBasis_gt_mul {a b : Fin N} (h : a < b) (H : Matrix (Fin N) (Fin N) ℂ) :
    trace (hermBasis (b, a) * H) = Complex.I * isq2 * (H b a - H a b) := by
  simp [trace_hermBasis_mul, hermBasis_gt h, ind, ite_and, sub_mul, mul_sub,
    Finset.sum_sub_distrib]

theorem isq2_re : isq2.re = (Real.sqrt 2)⁻¹ := by
  rw [isq2, Complex.ofReal_re]

theorem isq2_im : isq2.im = 0 := by
  rw [isq2, Complex.ofReal_im]

theorem sqrt_two_inv_mul_two : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  rw [inv_mul_eq_div, div_eq_iff h0, h]

/-- For Hermitian `H` and `a < b`: `y_(a,b) = √2 Re H_ab`. -/
theorem hermCoord_lt {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {a b : Fin N}
    (h : a < b) : hermCoord N H (a, b) = Real.sqrt 2 * (H a b).re := by
  have hba : H b a = conj (H a b) := (hH.apply b a).symm
  rw [hermCoord, trace_hermBasis_lt_mul h, hba, Complex.mul_re, isq2_re, isq2_im]
  simp only [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, zero_mul,
    sub_zero, neg_add_cancel]
  linear_combination (H a b).re * sqrt_two_inv_mul_two

/-- For Hermitian `H` and `a < b`: `y_(b,a) = √2 Im H_ab`. -/
theorem hermCoord_gt {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {a b : Fin N}
    (h : a < b) : hermCoord N H (b, a) = Real.sqrt 2 * (H a b).im := by
  have hba : H b a = conj (H a b) := (hH.apply b a).symm
  rw [hermCoord, trace_hermBasis_gt_mul h, hba]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, isq2_re, isq2_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  linear_combination (H a b).im * sqrt_two_inv_mul_two

end BlockBand.Native.ErdosRiabov.Chains
