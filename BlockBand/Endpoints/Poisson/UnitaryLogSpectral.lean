module

public import BlockBand.Endpoints.Poisson.PhaseFractionalMatrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Diagonalization of a unitary matrix

Mathlib has the spectral theorem for Hermitian matrices only. We reduce to it by a Cayley
transform: for a unit `λ` with `det(λ + W) ≠ 0` (it exists since the characteristic polynomial
has finitely many roots), `A = λ̄W` is unitary with `det(I + A) ≠ 0`, `H = i(I - A)(I + A)⁻¹` is
Hermitian, and `A = (H + i)⁻¹(i - H)` is diagonal in an eigenbasis of `H`.
Deterministic; no probability.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

open Matrix Polynomial
open scoped ComplexOrder ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rational parametrization of infinitely many unit complex numbers. -/
def unitPoint (n : ℕ) : ℂ := ⟨(1 - (n : ℝ) ^ 2) / (1 + (n : ℝ) ^ 2), 2 * n / (1 + (n : ℝ) ^ 2)⟩

theorem norm_unitPoint (n : ℕ) : ‖unitPoint n‖ = 1 := by
  have h : Complex.normSq (unitPoint n) = 1 := by
    rw [unitPoint, Complex.normSq_mk]
    have : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
    field_simp
    ring
  rw [Complex.normSq_eq_norm_sq] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

theorem unitPoint_injective : Function.Injective unitPoint := by
  intro m n h
  have hre := congrArg Complex.re h
  simp only [unitPoint] at hre
  have hm : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  have hn : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  rw [div_eq_div_iff hm.ne' hn.ne'] at hre
  have : ((m : ℝ)) ^ 2 = (n : ℝ) ^ 2 := by nlinarith
  have := (sq_eq_sq₀ (Nat.cast_nonneg m) (Nat.cast_nonneg n)).mp this
  exact_mod_cast this

/-- A unit `λ` avoiding the finitely many `λ` with `det(λ I + W) = 0`. -/
theorem exists_unit_det_add_ne_zero (W : Matrix ι ι ℂ) :
    ∃ l : ℂ, ‖l‖ = 1 ∧ (l • (1 : Matrix ι ι ℂ) + W).det ≠ 0 := by
  set R := ((-W).charpoly.roots.toFinset : Finset ℂ) with hR
  have hne : (-W).charpoly ≠ 0 := (charpoly_monic (-W)).ne_zero
  by_contra hcon
  push Not at hcon
  have hmem : ∀ n, unitPoint n ∈ R := by
    intro n
    rw [hR, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_charpoly]
    have := hcon (unitPoint n) (norm_unitPoint n)
    rw [← this]
    congr 1
    ext i j
    simp [scalar_apply, Matrix.smul_apply, sub_eq_add_neg, diagonal_apply, Matrix.one_apply]
  obtain ⟨x, y, hxy, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨unitPoint n, hmem n⟩ : R))
  exact hxy (unitPoint_injective (congrArg Subtype.val h))

theorem isUnit_det_of_mulVec_injective' {A : Matrix ι ι ℂ}
    (h : ∀ x, A *ᵥ x = 0 → x = 0) : IsUnit A.det := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro a b hab
  have : A *ᵥ (a - b) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hab
  exact sub_eq_zero.mp (h _ this)

theorem isUnit_det_hermitian_add_I {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    IsUnit (H + Complex.I • (1 : Matrix ι ι ℂ)).det := by
  apply isUnit_det_of_mulVec_injective'
  intro x hx
  have h1 : star x ⬝ᵥ ((H + Complex.I • 1) *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
  rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
    star_dotProduct_self_eq] at h1
  have h2 := congrArg Complex.im h1
  have hreal : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
    have h : conj (star x ⬝ᵥ (H *ᵥ x)) = star x ⬝ᵥ (H *ᵥ x) := by
      rw [conj_dotProduct, star_mulVec, ← dotProduct_mulVec, hH.eq]
    have := congrArg Complex.im h
    simp at this
    linarith
  simp only [Complex.add_im, hreal, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im] at h2
  have h3 : quadNorm x = 0 := by linarith
  by_contra hx0
  exact (quadNorm_pos hx0).ne' h3

/-- **Diagonalization of a unitary** (Step 1 of the unitary log-comparison lemma):
`W = Q diag(ζ) Q*` with `Q` unitary and `|ζ_j| = 1`. -/
theorem exists_unitary_diagonalization {W : Matrix ι ι ℂ} (hW : Wᴴ * W = 1) :
    ∃ (Q : Matrix ι ι ℂ) (ζ : ι → ℂ), Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 ∧ (∀ i, ‖ζ i‖ = 1) ∧
      W = Q * diagonal ζ * Qᴴ := by
  obtain ⟨l, hl, hdet⟩ := exists_unit_det_add_ne_zero W
  have hll : conj l * l = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hl]; simp
  have hll' : l * conj l = 1 := by rw [mul_comm]; exact hll
  set A := conj l • W with hA
  have hAA : Aᴴ * A = 1 := by
    rw [hA, conjTranspose_smul, smul_mul_smul_comm, hW, Complex.star_def, Complex.conj_conj,
      hll', one_smul]
  have hAA' : A * Aᴴ = 1 := mul_eq_one_comm.mp hAA
  have hdetA : IsUnit (1 + A).det := by
    have h1 : 1 + A = conj l • (l • (1 : Matrix ι ι ℂ) + W) := by
      rw [smul_add, smul_smul, hll, one_smul]
    rw [h1, det_smul]
    apply IsUnit.mul
    · apply IsUnit.pow
      apply isUnit_iff_ne_zero.mpr
      intro h0; rw [h0, zero_mul] at hll; exact zero_ne_one hll
    · exact isUnit_iff_ne_zero.mpr hdet
  set H := Complex.I • ((1 - A) * (1 + A)⁻¹) with hHdef
  clear_value H
  -- `H` is Hermitian
  have hdetA' : IsUnit (1 + Aᴴ).det := by
    have : (1 + Aᴴ) = (1 + A)ᴴ := by rw [conjTranspose_add, conjTranspose_one]
    rw [this, det_conjTranspose]
    exact hdetA.star
  have e1 : (1 + Aᴴ) * (1 - A) = -((1 - Aᴴ) * (1 + A)) := by
    simp only [add_mul, one_mul, mul_sub, mul_one, sub_mul, mul_add, hAA]
    abel
  have hY : (1 + Aᴴ)⁻¹ * (1 - Aᴴ) = -((1 - A) * (1 + A)⁻¹) := by
    have h2 : (1 + Aᴴ) * (-((1 - A) * (1 + A)⁻¹)) = 1 - Aᴴ := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, e1, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
        mul_nonsing_inv _ hdetA, Matrix.mul_one]
    rw [← h2, nonsing_inv_mul_cancel_left _ _ hdetA']
  have hH : H.IsHermitian := by
    rw [IsHermitian, hHdef, conjTranspose_smul, conjTranspose_mul, conjTranspose_nonsing_inv,
      conjTranspose_add, conjTranspose_sub, conjTranspose_one, hY, smul_neg, ← neg_smul]
    congr 1
    simp [Complex.conj_I]
  -- the spectral theorem for `H`
  set Q : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hQ
  have hQQ : star Q * Q = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hQQ' : Q * star Q = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  rw [star_eq_conjTranspose] at hQQ hQQ'
  set h : ι → ℝ := hH.eigenvalues with hh
  have hspec : H = Q * diagonal (fun i => (h i : ℂ)) * Qᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    rw [← star_eq_conjTranspose]
    exact this
  have hne : ∀ i, (h i : ℂ) + Complex.I ≠ 0 := by
    intro i h0
    have := congrArg Complex.im h0
    simp at this
  set E : ι → ℂ := fun i => (Complex.I - h i) / (h i + Complex.I) with hE
  have hHA : (H + Complex.I • 1) * A = Complex.I • 1 - H := by
    have h1 : H * (1 + A) = Complex.I • (1 - A) := by
      rw [hHdef, smul_mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hdetA, Matrix.mul_one]
    have h1' : H + H * A = Complex.I • 1 - Complex.I • A := by
      rw [← smul_sub, ← h1, Matrix.mul_add, Matrix.mul_one]
    rw [Matrix.add_mul, smul_mul_assoc, Matrix.one_mul]
    have h2 : H * A = Complex.I • 1 - Complex.I • A - H := by rw [← h1']; abel
    rw [h2]; abel
  have hconj : ∀ d : ι → ℂ, Q * diagonal d * Qᴴ * (Q * diagonal (E) * Qᴴ) =
      Q * diagonal (d * E) * Qᴴ := by
    intro d
    rw [show Q * diagonal d * Qᴴ * (Q * diagonal E * Qᴴ) =
      Q * diagonal d * (Qᴴ * Q) * diagonal E * Qᴴ by simp only [Matrix.mul_assoc],
      hQQ, Matrix.mul_one, Matrix.mul_assoc Q, diagonal_mul_diagonal]
    rfl
  have hone : (Complex.I • (1 : Matrix ι ι ℂ)) = Q * diagonal (fun _ => Complex.I) * Qᴴ := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc, hQQ']
  have hadd : ∀ a c : ι → ℂ, Q * diagonal a * Qᴴ + Q * diagonal c * Qᴴ =
      Q * diagonal (a + c) * Qᴴ := by
    intro a c; rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]; rfl
  have hsub : ∀ a c : ι → ℂ, Q * diagonal a * Qᴴ - Q * diagonal c * Qᴴ =
      Q * diagonal (a - c) * Qᴴ := by
    intro a c; rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]; rfl
  have hQE : (H + Complex.I • 1) * (Q * diagonal E * Qᴴ) = Complex.I • 1 - H := by
    have hfun : (fun i => (h i : ℂ)) * E + (fun _ => Complex.I) * E =
        (fun _ => Complex.I) - fun i => (h i : ℂ) := by
      funext i
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, hE]
      field_simp [hne i]
    rw [hspec, hone, Matrix.add_mul, hconj, hconj, hadd, hsub, hfun]
  have hAE : A = Q * diagonal E * Qᴴ := by
    have hu := isUnit_det_hermitian_add_I hH
    have h3 : (H + Complex.I • 1) * A = (H + Complex.I • 1) * (Q * diagonal E * Qᴴ) := by
      rw [hHA, hQE]
    rw [← nonsing_inv_mul_cancel_left _ A hu, h3, nonsing_inv_mul_cancel_left _ _ hu]
  refine ⟨Q, fun i => l * E i, hQQ, hQQ', fun i => ?_, ?_⟩
  · rw [norm_mul, hl, one_mul, hE]
    simp only
    rw [norm_div]
    have : Complex.I - (h i : ℂ) = -(conj ((h i : ℂ) + Complex.I)) := by
      simp [Complex.conj_ofReal, Complex.conj_I]; ring
    rw [this, norm_neg, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr (hne i))]
  · have hW' : W = l • A := by rw [hA, smul_smul, hll', one_smul]
    rw [hW', hAE, ← smul_mul_assoc, ← mul_smul_comm, ← diagonal_smul]
    rfl

end BlockBand.Endpoints.PhaseFractional
