module

public import BlockBand.Transmission.LawClauses.HessianSpectral
public import BlockBand.Transmission.PassiveCovariance.Step3

/-!
# Resolvent bounds along the line `A + τH`

* `posDef_add_smul`, `norm_inv_add_smul_le`: if `X` is Hermitian and `X - m ⪰ 0` (`m > 0`),
  then for `s ≥ 0` the matrix `X + s` is positive definite and `‖(X + s)⁻¹‖ ≤ (m + s)⁻¹`
  (coercivity of `i(X + s)`, `PassiveCovariance.norm_inv_le_of_im`);
* `abs_trace_re_le`: `|Re Tr M| ≤ n‖M‖`;
* `exists_coercive_line`: for `A ≻ 0` and Hermitian `H` there are `m, δ > 0` with
  `A + τH - m ⪰ 0` for `|τ| < δ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open Matrix BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem isHermitian_add_real_smul {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (s : ℝ)
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) : (X + (s : ℂ) • H).IsHermitian :=
  hX.add (hH.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]))

omit [Fintype ι] in
/-- `X - m ⪰ 0`, `m > 0`, `s ≥ 0` give `X + s ≻ 0`. -/
theorem posDef_add_smul {X : Matrix ι ι ℂ} {m s : ℝ} (hm : 0 < m) (hs : 0 ≤ s)
    (hXm : (X - (m : ℂ) • 1).PosSemidef) : (X + (s : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
  have h : X + (s : ℂ) • (1 : Matrix ι ι ℂ) = (X - (m : ℂ) • 1) + ((m + s : ℝ) : ℂ) • 1 := by
    push_cast; module
  rw [h]
  exact PosDef.posSemidef_add hXm (PosDef.one.smul (Complex.zero_lt_real.mpr (by linarith)))

/-- **`‖(X + s)⁻¹‖ ≤ (m + s)⁻¹`** for Hermitian `X` with `X - m ⪰ 0`. -/
theorem norm_inv_add_smul_le {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {m s : ℝ} (hm : 0 < m)
    (hs : 0 ≤ s) (hXm : (X - (m : ℂ) • 1).PosSemidef) :
    ‖(X + (s : ℂ) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ (m + s)⁻¹ := by
  set M := X + (s : ℂ) • (1 : Matrix ι ι ℂ) with hMdef
  set K := Complex.I • M with hKdef
  have hMH : Mᴴ = M := (isHermitian_add_real_smul hX s isHermitian_one).eq
  have hηpos : 0 < m + s := by linarith
  have him : matrixImaginaryPart K = (X - (m : ℂ) • 1) + (m + s) • (1 : Matrix ι ι ℂ) := by
    rw [matrixImaginaryPart, hKdef, conjTranspose_smul, hMH, ← sub_smul, smul_smul]
    have : -Complex.I / 2 * (Complex.I - star Complex.I) = 1 := by
      rw [Complex.star_def, Complex.conj_I]; ring_nf; rw [Complex.I_sq]; ring
    rw [this, one_smul, ← Complex.coe_smul, hMdef]; push_cast; module
  have hK := norm_inv_le_of_im K _ hηpos hXm him
  have hKu := passive_inverse_constructed K _ hηpos hXm him
  have hMK : M = (-Complex.I) • K := by
    rw [hKdef, smul_smul]
    rw [show -Complex.I * Complex.I = 1 by ring_nf; rw [Complex.I_sq]; ring, one_smul]
  have hMinv : M⁻¹ = Complex.I • K⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hMK, smul_mul_assoc, mul_smul_comm, smul_smul, hKu.2.2]
    rw [show Complex.I * -Complex.I = 1 by ring_nf; rw [Complex.I_sq]; ring, one_smul]
  rw [hMinv, norm_smul, Complex.norm_I, one_mul]
  exact hK

/-- `|Re Tr M| ≤ n‖M‖`. -/
theorem abs_trace_re_le (M : Matrix ι ι ℂ) : |M.trace.re| ≤ Fintype.card ι * ‖M‖ := by
  have h := norm_trace_mul_posSemidef_le (PosSemidef.one (n := ι) (R := ℂ)) M
  rw [Matrix.mul_one, trace_one] at h
  simp only [Complex.natCast_re] at h
  exact (Complex.abs_re_le_norm _).trans (by linarith)

/-- A positive definite `A` has `A - m ⪰ 0` for some `m > 0`. -/
theorem exists_sub_smul_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    ∃ m : ℝ, 0 < m ∧ (A - (m : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  have key : ∀ m : ℝ, (∀ i, m ≤ hA.1.eigenvalues i) →
      (A - (m : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
    intro m hm
    have h := add_smul_eq_spectral hA.1 (-m)
    have e : A - (m : ℂ) • (1 : Matrix ι ι ℂ) = A + ((-m : ℝ) : ℂ) • 1 := by push_cast; module
    rw [e, h, star_eq_conjTranspose]
    refine PosSemidef.mul_mul_conjTranspose_same ?_ _
    rw [posSemidef_diagonal_iff]
    intro i
    exact Complex.zero_le_real.mpr (by linarith [hm i])
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, key 1 fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min hA.1.eigenvalues
    exact ⟨hA.1.eigenvalues i₀, hA.eigenvalues_pos i₀, key _ hi₀⟩

/-- **Coercivity along the line**: `A + τH - m ⪰ 0` for `|τ| < δ`. -/
theorem exists_coercive_line {A H : Matrix ι ι ℂ} (hA : A.PosDef) (hH : H.IsHermitian) :
    ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ τ : ℝ, |τ| < δ →
      (A + (τ : ℂ) • H - (m : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  obtain ⟨m₀, hm₀, hA0⟩ := exists_sub_smul_posSemidef hA
  have hHn := norm_nonneg H
  refine ⟨m₀ / 2, m₀ / (2 * (‖H‖ + 1)), by positivity, by positivity, fun τ hτ => ?_⟩
  have e : A + (τ : ℂ) • H - ((m₀ / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) =
      (A - (m₀ : ℂ) • 1) + (((m₀ / 2 : ℝ) : ℂ) • 1 + (τ : ℂ) • H) := by push_cast; module
  rw [e]
  refine hA0.add (PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_add_real_smul (isHermitian_one.smul (by simp [IsSelfAdjoint,
      Complex.conj_ofReal])) τ hH) fun x => ?_)
  -- `x*(m₀/2 + τH)x = (m₀/2)|x|² + τ x*Hx ≥ (m₀/2 - |τ|‖H‖)|x|² ≥ 0`
  set q := star x ⬝ᵥ (H *ᵥ x)
  have hq : q = (q.re : ℂ) := by
    have h1 : star x ⬝ᵥ (Hᴴ *ᵥ x) = star q := quad_conjTranspose H x
    rw [hH.eq] at h1
    exact (Complex.conj_eq_iff_re.mp h1.symm).symm
  have hval : star x ⬝ᵥ ((((m₀ / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) + (τ : ℂ) • H) *ᵥ x) =
      ((m₀ / 2 * vecNorm x ^ 2 + τ * q.re : ℝ) : ℂ) := by
    rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_smul, star_self_eq, ← show q = star x ⬝ᵥ (H *ᵥ x) from rfl, hq]
    push_cast; simp only [smul_eq_mul, Complex.ofReal_re]
  rw [hval, Complex.zero_le_real]
  have hqb : |q.re| ≤ ‖H‖ * vecNorm x ^ 2 := by
    have := norm_bilinear_le x H x
    rw [bilinear] at this
    calc |q.re| ≤ ‖q‖ := Complex.abs_re_le_norm q
      _ ≤ _ := by nlinarith
  have hτH : |τ| * ‖H‖ ≤ m₀ / 2 := by
    have h2 : |τ| * (‖H‖ + 1) ≤ m₀ / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hτ; linarith
    nlinarith [abs_nonneg τ]
  have hv := sq_nonneg (vecNorm x)
  have : -(|τ| * (‖H‖ * vecNorm x ^ 2)) ≤ τ * q.re := by
    have := abs_mul τ q.re
    have h3 : |τ * q.re| ≤ |τ| * (‖H‖ * vecNorm x ^ 2) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hqb (abs_nonneg τ)
    linarith [neg_abs_le (τ * q.re)]
  nlinarith

end BlockBand.Transmission.LawClauses
