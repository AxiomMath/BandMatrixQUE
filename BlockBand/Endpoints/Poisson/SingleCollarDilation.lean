module

public import BlockBand.Endpoints.Poisson.UnitaryLog
public import BlockBand.Endpoints.Response.FractionalTrace
public import BlockBand.Endpoints.Response.RemoteHigherPinching
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The unitary dilation of the absorbed scattering matrix

We dilate the absorbed scattering matrix to a unitary matrix and bound the fractional trace of
the difference of two dilations.

* `sc_schattenFrac_add_le`: `Tr |A + B|^p ≤ 2^{p/2} (Tr |A|^p + Tr |B|^p)` for **all** square
  matrices and `0 < p ≤ 2` (from `(A+B)*(A+B) ≤ 2(A*A + B*B)`, trace monotonicity and PSD
  subadditivity `rh_fracTrace_add_le`). This is the subadditivity used in the paper, with the
  factor `2^{p/2} ≤ 2` absorbed in `C_p`.
* `sc_charpoly_one_sub_mul_comm`: `I - AB` and `I - BA` have the same characteristic
  polynomial; hence `I - SS*` and `I - S*S` have the same spectrum, the same fractional traces and `I - SS* ⪰ 0` iff
  `I - S*S ⪰ 0`.
* `scDefect S = (I - S*S)^{1/2}`, `scDilation S = [[S, (I-SS*)^{1/2}], [(I-S*S)^{1/2}, -S*]]`
  (the matrix `𝒱(S)`); `sc_mul_defect`: `S (I-S*S)^{1/2} = (I-SS*)^{1/2} S`
  (polynomial interpolation of `√` on the joint finite spectrum); `sc_dilation_unitary`: `𝒱(S)` is
  unitary for every contraction; `sc_dilation_of_unitary`: at a unitary `S₀` the off-diagonal
  blocks vanish.
* `sc_source_unitary_dilation`: **the unitary dilation of the source** from the two bounds of
  the remote scattering source: `σ = Tr |𝒱(S_κ) - 𝒱(S₀)|^p ≤
  2^{p/2}·2·((2ηκ)^p Tr Q^p + (4ηκ)^{p/2} Tr Q^{p/2})` for `0 < p ≤ 2`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Polynomial
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace)
open BlockBand.Endpoints.PhaseFractional (schattenFrac)
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!
## 1. Subadditivity of `Tr |·|^p` for general matrices
-/

omit [DecidableEq ι] in
theorem sc_conjTranspose_add_mul_le (A B : Matrix ι ι ℂ) :
    ((2 : ℂ) • (Aᴴ * A + Bᴴ * B) - (A + B)ᴴ * (A + B)).PosSemidef := by
  have h : (2 : ℂ) • (Aᴴ * A + Bᴴ * B) - (A + B)ᴴ * (A + B) = (A - B)ᴴ * (A - B) := by
    simp only [conjTranspose_add, conjTranspose_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, two_smul]
    abel
  rw [h]; exact posSemidef_conjTranspose_mul_self _

/-- **Quasi-subadditivity of `Tr |·|^p`** for arbitrary square matrices and `0 < p ≤ 2`. -/
theorem sc_schattenFrac_add_le (A B : Matrix ι ι ℂ) {p : ℝ} (hp0 : 0 < p) (hp2 : p ≤ 2) :
    schattenFrac p (A + B) ≤ 2 ^ (p / 2) * (schattenFrac p A + schattenFrac p B) := by
  unfold schattenFrac
  have hA := posSemidef_conjTranspose_mul_self A
  have hB := posSemidef_conjTranspose_mul_self B
  have hAB := posSemidef_conjTranspose_mul_self (A + B)
  have hsum := hA.add hB
  have h2 : ((2 : ℝ) : ℂ) • (Aᴴ * A + Bᴴ * B) = (2 : ℂ) • (Aᴴ * A + Bᴴ * B) := by norm_num
  have hmono := fracTrace_mono hAB.isHermitian
    (hsum.smul (by norm_num : (0 : ℂ) ≤ 2)).isHermitian (sc_conjTranspose_add_mul_le A B)
    (by positivity : (0 : ℝ) ≤ p / 2)
  rw [← h2, fracTrace_smul hsum.isHermitian (by norm_num) (p / 2)] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact rh_fracTrace_add_le hA hB (by positivity) (by linarith)

/-!
## 2. The two defect matrices have the same spectrum
-/

theorem sc_det_add_mul_comm (A B : Matrix ι ι ℂ) (c : ℂ) :
    (c • (1 : Matrix ι ι ℂ) + A * B).det = (c • (1 : Matrix ι ι ℂ) + B * A).det := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_smul, zero_add, det_mul, mul_comm]
  have h1 : ∀ X Y : Matrix ι ι ℂ, c • (1 : Matrix ι ι ℂ) + X * Y =
      c • (1 + (c⁻¹ • X) * Y) := by
    intro X Y
    rw [smul_add, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have h2 : ∀ X Y : Matrix ι ι ℂ, c • (1 : Matrix ι ι ℂ) + Y * X =
      c • (1 + Y * (c⁻¹ • X)) := by
    intro X Y
    rw [smul_add, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [h1, h2, det_smul, det_smul, det_one_add_mul_comm]

/-- `I - AB` and `I - BA` have the same characteristic polynomial (square matrices). -/
theorem sc_charpoly_one_sub_mul_comm (A B : Matrix ι ι ℂ) :
    (1 - A * B).charpoly = (1 - B * A).charpoly := by
  refine Polynomial.funext fun t => ?_
  rw [eval_charpoly, eval_charpoly]
  have h : ∀ X Y : Matrix ι ι ℂ, Matrix.scalar ι t - (1 - X * Y) =
      (t - 1) • (1 : Matrix ι ι ℂ) + X * Y := by
    intro X Y
    rw [sub_smul, one_smul, Matrix.scalar_apply, ← smul_one_eq_diagonal]
    abel
  rw [h, h, sc_det_add_mul_comm]

theorem sc_fracTrace_one_sub_mul_comm (q : ℝ) (A B : Matrix ι ι ℂ) :
    fracTrace q (1 - A * B) = fracTrace q (1 - B * A) := by
  unfold fracTrace; rw [sc_charpoly_one_sub_mul_comm]

/-- Positive semidefiniteness of a Hermitian matrix depends only on its characteristic
polynomial. -/
theorem sc_posSemidef_of_charpoly_eq {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (h : X.charpoly = Y.charpoly) (hXp : X.PosSemidef) : Y.PosSemidef := by
  rw [hY.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have hmem : ((hY.eigenvalues i : ℝ) : ℂ) ∈ X.charpoly.roots := by
    rw [h, hY.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩
  rw [hX.roots_charpoly_eq_eigenvalues] at hmem
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hmem
  have hj' : hX.eigenvalues j = hY.eigenvalues i := Complex.ofReal_injective hj
  rw [Pi.zero_apply, ← hj']
  exact hXp.eigenvalues_nonneg j

theorem sc_isHermitian_one_sub (S : Matrix ι ι ℂ) : (1 - Sᴴ * S).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]

/-- A square contraction is a co-contraction: `I - S*S ⪰ 0 ⇒ I - SS* ⪰ 0`. -/
theorem sc_posSemidef_one_sub_mul_conjTranspose {S : Matrix ι ι ℂ}
    (h : (1 - Sᴴ * S).PosSemidef) : (1 - S * Sᴴ).PosSemidef := by
  have hY : (1 - S * Sᴴ).IsHermitian := by
    simpa only [conjTranspose_conjTranspose] using sc_isHermitian_one_sub Sᴴ
  exact sc_posSemidef_of_charpoly_eq (sc_isHermitian_one_sub S) hY
    (sc_charpoly_one_sub_mul_comm Sᴴ S) h

/-!
## 3. The defect `(I - S*S)^{1/2}` and the intertwining relation
-/

section Defect

open scoped Matrix.Norms.L2Operator MatrixOrder

/-- `(I - S*S)^{1/2}` (continuous functional calculus of the Hermitian `I - S*S`). -/
def scDefect (S : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc Real.sqrt (1 - Sᴴ * S)

theorem sc_isSelfAdjoint_one_sub (S : Matrix ι ι ℂ) : IsSelfAdjoint (1 - Sᴴ * S) :=
  sc_isHermitian_one_sub S

theorem sc_defect_isHermitian (S : Matrix ι ι ℂ) : (scDefect S)ᴴ = scDefect S :=
  (cfc_predicate Real.sqrt (1 - Sᴴ * S) : IsSelfAdjoint _).star_eq

/-- `S * P = Q * S` implies `S * q(P) = q(Q) * S` for every real polynomial `q`. -/
theorem sc_mul_aeval_of_semiconj {S P Q : Matrix ι ι ℂ} (h : S * P = Q * S) (q : ℝ[X]) :
    S * aeval P q = aeval Q q * S := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hq, hr]
  | monomial k a =>
    have hk : S * P ^ k = Q ^ k * S := (SemiconjBy.pow_right (h : SemiconjBy S P Q) k).eq
    rw [aeval_monomial, aeval_monomial, ← Matrix.mul_assoc, ← Algebra.commutes a S,
      Matrix.mul_assoc, hk, ← Matrix.mul_assoc, Algebra.commutes a (Q ^ k)]

/-- **Intertwining** `S f(I - S*S) = f(I - SS*) S` for every real function `f`. -/
theorem sc_mul_cfc_intertwine (S : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    S * cfc f (1 - Sᴴ * S) = cfc f (1 - S * Sᴴ) * S := by
  have hP := sc_isSelfAdjoint_one_sub S
  have hQ : IsSelfAdjoint (1 - S * Sᴴ) := by
    simpa only [conjTranspose_conjTranspose] using sc_isSelfAdjoint_one_sub Sᴴ
  have hfin : ∀ A : Matrix ι ι ℂ, (Complex.ofReal ⁻¹' spectrum ℂ A).Finite := fun A =>
    (Matrix.finite_spectrum A).preimage Complex.ofReal_injective.injOn
  have hmem : ∀ (A : Matrix ι ι ℂ) (x : ℝ), x ∈ spectrum ℝ A → x ∈ Complex.ofReal ⁻¹' spectrum ℂ A :=
    fun A x hx => (spectrum.algebraMap_mem_iff ℂ).2 hx
  set s : Finset ℝ := (hfin (1 - Sᴴ * S)).toFinset ∪ (hfin (1 - S * Sᴴ)).toFinset with hs
  set q : ℝ[X] := Lagrange.interpolate s id f with hq
  have hev : ∀ x ∈ s, q.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (r := f) (Set.injOn_id _) hx
  have hcP : cfc f (1 - Sᴴ * S) = aeval (1 - Sᴴ * S) q := by
    rw [← cfc_polynomial q (1 - Sᴴ * S)]
    refine cfc_congr fun x hx => (hev x ?_).symm
    rw [hs, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl (hmem _ x hx)
  have hcQ : cfc f (1 - S * Sᴴ) = aeval (1 - S * Sᴴ) q := by
    rw [← cfc_polynomial q (1 - S * Sᴴ)]
    refine cfc_congr fun x hx => (hev x ?_).symm
    rw [hs, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact Or.inr (hmem _ x hx)
  rw [hcP, hcQ]
  refine sc_mul_aeval_of_semiconj ?_ q
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

theorem sc_mul_defect (S : Matrix ι ι ℂ) : S * scDefect S = scDefect Sᴴ * S := by
  unfold scDefect
  rw [conjTranspose_conjTranspose]
  exact sc_mul_cfc_intertwine S Real.sqrt

/-- `(I - S*S)^{1/2} (I - S*S)^{1/2} = I - S*S` for a contraction. -/
theorem sc_defect_mul_self {S : Matrix ι ι ℂ} (h : (1 - Sᴴ * S).PosSemidef) :
    scDefect S * scDefect S = 1 - Sᴴ * S := by
  have hP := sc_isSelfAdjoint_one_sub S
  have hnn : (0 : Matrix ι ι ℂ) ≤ 1 - Sᴴ * S := Matrix.nonneg_iff_posSemidef.2 h
  unfold scDefect
  rw [← cfc_mul Real.sqrt Real.sqrt (1 - Sᴴ * S)]
  conv_rhs => rw [← cfc_id' ℝ (1 - Sᴴ * S)]
  refine cfc_congr fun x hx => ?_
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn hx)

theorem sc_defect_of_unitary {S : Matrix ι ι ℂ} (h : Sᴴ * S = 1) : scDefect S = 0 := by
  unfold scDefect
  rw [h, sub_self, cfc_apply_zero, Real.sqrt_zero, map_zero]

/-!
## 4. The unitary dilation
-/

/-- The unitary dilation `𝒱(S) = [[S, (I-SS*)^{1/2}], [(I-S*S)^{1/2}, -S*]]`. -/
def scDilation (S : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  fromBlocks S (scDefect Sᴴ) (scDefect S) (-Sᴴ)

theorem sc_dilation_toBlocks11 (S : Matrix ι ι ℂ) : (scDilation S).toBlocks₁₁ = S :=
  toBlocks_fromBlocks₁₁ _ _ _ _

/-- **`𝒱(S)` is unitary** for every square contraction `S` (`I - S*S ⪰ 0`). -/
theorem sc_dilation_unitary {S : Matrix ι ι ℂ} (h : (1 - Sᴴ * S).PosSemidef) :
    (scDilation S)ᴴ * scDilation S = 1 := by
  have h' : (1 - Sᴴᴴ * Sᴴ).PosSemidef := by
    rw [conjTranspose_conjTranspose]; exact sc_posSemidef_one_sub_mul_conjTranspose h
  have hD := sc_defect_isHermitian S
  have hD' := sc_defect_isHermitian Sᴴ
  have h1 := sc_defect_mul_self h
  have h2 := sc_defect_mul_self h'
  rw [conjTranspose_conjTranspose] at h2
  have i1 := sc_mul_defect S
  have i2 := sc_mul_defect Sᴴ
  rw [conjTranspose_conjTranspose] at i2
  unfold scDilation
  rw [fromBlocks_conjTranspose, hD, hD', fromBlocks_multiply, ← fromBlocks_one]
  simp only [conjTranspose_neg, conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul,
    neg_neg]
  congr 1
  · rw [h1]; abel
  · rw [i2]; abel
  · rw [i1]; abel
  · rw [h2]; abel

/-- At a unitary `S₀` the off-diagonal blocks of `𝒱(S₀)` vanish. -/
theorem sc_dilation_of_unitary {S : Matrix ι ι ℂ} (h : Sᴴ * S = 1) :
    scDilation S = fromBlocks S 0 0 (-Sᴴ) := by
  have h' : Sᴴᴴ * Sᴴ = 1 := by
    rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.1 h
  unfold scDilation
  rw [sc_defect_of_unitary h, sc_defect_of_unitary h']

end Defect

/-!
## 5. The unitary dilation of the source
-/

theorem sc_schattenFrac_fromBlocks_diag (A : Matrix ι ι ℂ) {p : ℝ} (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    schattenFrac p (fromBlocks A 0 0 (-Aᴴ)) ≤ 2 * schattenFrac p A := by
  unfold schattenFrac
  have hM := posSemidef_conjTranspose_mul_self (fromBlocks A 0 0 (-Aᴴ))
  have key := rh_fracTrace_fromBlocks_le hM (by positivity : (0 : ℝ) ≤ p / 2) (by linarith)
  have hb : (fromBlocks A 0 0 (-Aᴴ))ᴴ * fromBlocks A 0 0 (-Aᴴ) =
      fromBlocks (Aᴴ * A) 0 0 (A * Aᴴ) := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp
  rw [hb, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂, fracTrace_mul_comm (p / 2) A Aᴴ] at key
  rw [hb]; linarith

theorem sc_schattenFrac_fromBlocks_off (X Y : Matrix ι ι ℂ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp2 : p ≤ 2) :
    schattenFrac p (fromBlocks 0 X Y 0) ≤ fracTrace (p / 2) (Yᴴ * Y) + fracTrace (p / 2) (Xᴴ * X) := by
  unfold schattenFrac
  have hM := posSemidef_conjTranspose_mul_self (fromBlocks (0 : Matrix ι ι ℂ) X Y 0)
  have key := rh_fracTrace_fromBlocks_le hM (by positivity : (0 : ℝ) ≤ p / 2) (by linarith)
  have hb : (fromBlocks (0 : Matrix ι ι ℂ) X Y 0)ᴴ * fromBlocks 0 X Y 0 =
      fromBlocks (Yᴴ * Y) 0 0 (Xᴴ * X) := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp
  rw [hb, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂] at key
  rw [hb]; exact key

/-- **The unitary dilation of the source**. Let `S₀` be unitary and `S` a square
matrix with the two bounds of the remote scattering source for a PSD `Q`, `η, κ ≥ 0`:
`Tr |S - S₀|^p ≤ (2ηκ)^p Tr Q^p` and `0 ⪯ I - S*S ⪯ 4ηκ Q`. Then, for `0 < p ≤ 2`,
`σ = Tr |𝒱(S) - 𝒱(S₀)|^p ≤ 2^{p/2} · 2 ((2ηκ)^p Tr Q^p + (4ηκ)^{p/2} Tr Q^{p/2})`.
The off-diagonal blocks are controlled by `I - S*S` and `I - SS*`, which have the same spectrum
(`sc_fracTrace_one_sub_mul_comm`); no estimate on the difference of two square roots is used. -/
theorem sc_source_unitary_dilation {S₀ S Q : Matrix ι ι ℂ} (hS₀ : S₀ᴴ * S₀ = 1)
    (hQ : Q.PosSemidef) {η κ p : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hp0 : 0 < p) (hp2 : p ≤ 2)
    (hW1 : schattenFrac p (S - S₀) ≤ (2 * η * κ) ^ p * fracTrace p Q)
    (hW2 : (1 - Sᴴ * S).PosSemidef)
    (hW3 : ((((4 * η * κ : ℝ)) : ℂ) • Q - (1 - Sᴴ * S)).PosSemidef) :
    schattenFrac p (scDilation S - scDilation S₀) ≤
      2 ^ (p / 2) * (2 * ((2 * η * κ) ^ p * fracTrace p Q +
        (4 * η * κ) ^ (p / 2) * fracTrace (p / 2) Q)) := by
  have hsplit : scDilation S - scDilation S₀ =
      fromBlocks (S - S₀) 0 0 (-(S - S₀)ᴴ) + fromBlocks 0 (scDefect Sᴴ) (scDefect S) 0 := by
    rw [sc_dilation_of_unitary hS₀]
    unfold scDilation
    rw [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_add, conjTranspose_sub]
    congr 1 <;> abel
  have hDS : (scDefect S)ᴴ * scDefect S = 1 - Sᴴ * S := by
    rw [sc_defect_isHermitian]; exact sc_defect_mul_self hW2
  have hW2' : (1 - Sᴴᴴ * Sᴴ).PosSemidef := by
    rw [conjTranspose_conjTranspose]; exact sc_posSemidef_one_sub_mul_conjTranspose hW2
  have hDS' : (scDefect Sᴴ)ᴴ * scDefect Sᴴ = 1 - S * Sᴴ := by
    rw [sc_defect_isHermitian, sc_defect_mul_self hW2', conjTranspose_conjTranspose]
  have hoff := sc_schattenFrac_fromBlocks_off (scDefect Sᴴ) (scDefect S) hp0.le hp2
  rw [hDS, hDS', sc_fracTrace_one_sub_mul_comm (p / 2) S Sᴴ] at hoff
  have hdiag := sc_schattenFrac_fromBlocks_diag (S - S₀) hp0.le hp2
  have hmono := fracTrace_mono (sc_isHermitian_one_sub S)
    (hQ.smul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 4 * η * κ))).isHermitian hW3
    (by positivity : (0 : ℝ) ≤ p / 2)
  rw [fracTrace_smul hQ.isHermitian (by positivity) (p / 2)] at hmono
  rw [hsplit]
  refine (sc_schattenFrac_add_le _ _ hp0 hp2).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  nlinarith

end BlockBand.Endpoints
