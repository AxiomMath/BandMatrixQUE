module

public import BlockBand.LocalWindow.ProofBranch
public import BlockBand.LocalWindow.ProofPoisson

/-!
# Reading Poisson sums off the averaged local law

Poisson sums of a Hermitian matrix as imaginary parts of resolvent traces, and their control by
the CEH averaged local law, for part (i) of the physical local-window lemma.

## Main results

* `spectralSum_poisson_eq`: `Σ_{λ ∈ Spec A} η²/(λ² + η²) = η Im Tr (A - iη)⁻¹` for Hermitian
  `A`, `η > 0`.
* `averagedControl_one`: the CEH averaged control at `B = 1` is `1/(N |Im z|)` whenever
  `⟨Im M⟩ ≠ 0` (`⟨Γ⟩ = 1`).
* `poisson_readout`: off the averaged bad event (`Inputs.ExternalLocalGUE`, `B = 1`, loss
  `N^δ`) at `z = e + iη` for `F + √s W`, with branch trace `⟨M(z)⟩ = m`, the Poisson sum of
  `F + √s W - e` at height `η` is within `N^δ` of `N η Im m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCertificate

open Matrix Finset
open BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofCount
open scoped ComplexConjugate

section Poisson

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `A - w = U diag(λ - w) U*` for Hermitian `A` and complex `w`. -/
theorem sub_smul_eq_conj {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (w : ℂ) :
    A - w • (1 : Matrix ι ι ℂ) =
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
        diagonal (fun j => (hA.eigenvalues j : ℂ) - w) *
          star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
  set U := hA.eigenvectorUnitary
  have hUs : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 := Unitary.coe_mul_star_self _
  have hw : w • (1 : Matrix ι ι ℂ) =
      (U : Matrix ι ι ℂ) * diagonal (fun _ => w) * star (U : Matrix ι ι ℂ) := by
    rw [show diagonal (fun _ : ι => w) = w • (1 : Matrix ι ι ℂ) by
      ext i j; by_cases h : i = j <;> simp [diagonal, h], Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hUs]
  conv_lhs => rw [show A = (U : Matrix ι ι ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      star (U : Matrix ι ι ℂ) by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]; rfl]
  rw [hw, conj_sub_conj]
  rfl

/-- `Tr (A - w)⁻¹ = Σ_j (λ_j - w)⁻¹` for Hermitian `A` and nonreal `w`. -/
theorem trace_resolvent_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) :
    ((A - w • (1 : Matrix ι ι ℂ))⁻¹).trace = ∑ j, ((hA.eigenvalues j : ℂ) - w)⁻¹ := by
  set U := hA.eigenvectorUnitary
  have hne : ∀ j, (hA.eigenvalues j : ℂ) - w ≠ 0 := fun j h => by
    have := congrArg Complex.im h
    simp at this
    exact hw this
  have hinv : (A - w • (1 : Matrix ι ι ℂ))⁻¹ =
      (U : Matrix ι ι ℂ) * diagonal (fun j => ((hA.eigenvalues j : ℂ) - w)⁻¹) *
        star (U : Matrix ι ι ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [sub_smul_eq_conj hA w, conj_mul_conj]
    have : (fun j => (hA.eigenvalues j : ℂ) - w) * (fun j => ((hA.eigenvalues j : ℂ) - w)⁻¹) =
        1 := funext fun j => mul_inv_cancel₀ (hne j)
    rw [this, show (diagonal (1 : ι → ℂ)) = 1 from diagonal_one, Matrix.mul_one]
    exact Unitary.coe_mul_star_self _
  rw [hinv, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
    Matrix.one_mul, trace_diagonal]

/-- **Poisson sum as an imaginary trace**: `Σ η²/(λ² + η²) = η Im Tr (A - iη)⁻¹`. -/
theorem spectralSum_poisson_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η) :
    spectralSum A (poissonWeight η) =
      η * ((A - (Complex.I * η) • (1 : Matrix ι ι ℂ))⁻¹).trace.im := by
  have hw : (Complex.I * η).im ≠ 0 := by simp [hη.ne']
  rw [spectralSum_eq_sum hA, trace_resolvent_eq_sum hA hw, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set l := hA.eigenvalues j
  have hden : l ^ 2 + η ^ 2 ≠ 0 := by positivity
  have : ((l : ℂ) - Complex.I * η)⁻¹ = ((l / (l ^ 2 + η ^ 2) : ℝ) : ℂ) +
      ((η / (l ^ 2 + η ^ 2) : ℝ) : ℂ) * Complex.I := by
    have hne : (l : ℂ) - Complex.I * η ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this; exact hη.ne' this
    apply inv_eq_of_mul_eq_one_right
    apply Complex.ext <;>
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.one_re, Complex.one_im]
      field_simp
      ring
  rw [this]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  unfold poissonWeight
  field_simp
  ring

end Poisson

section Control

variable {N : ℕ}

/-- **Averaged control at `B = 1`**: `averagedControl M 1 z = 1/(N |Im z|)` when `N > 0` and
`⟨Im M⟩ ≠ 0` (then `⟨Γ⟩ = 1` and `⟨1⟩ = 1`). -/
theorem averagedControl_one (hN : 0 < N) (M : CEH.SourceMatrix N) (z : ℂ)
    (hM : CEH.normalizedTrace (CEH.imaginaryPart M) ≠ 0) :
    CEH.averagedControl M 1 z = 1 / ((N : ℝ) * |z.im|) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : CEH.normalizedTrace (1 : CEH.SourceMatrix N) = 1 := by
    unfold CEH.normalizedTrace; rw [trace_one, Fintype.card_fin, inv_mul_cancel₀ hN']
  have hΓ : CEH.normalizedTrace (CEH.gammaMatrix M) = 1 := by
    unfold CEH.gammaMatrix
    unfold CEH.normalizedTrace at hM ⊢
    rw [trace_smul, smul_eq_mul, ← mul_assoc, mul_comm (N : ℂ)⁻¹, mul_assoc,
      inv_mul_cancel₀ hM]
  unfold CEH.averagedControl CEH.normalizedHilbertSchmidt
  rw [conjTranspose_one, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, h1, hΓ]
  simp

/-- **Readout**: off the averaged bad event at `B = 1`, loss `N^δ`, at `z = e + iη` (`η > 0`)
for `F + √s W`, if the branch satisfies `⟨M(z)⟩ = m` with `Im m ≠ 0`, then the Poisson sum of
`F + √s W - e` at height `η` is within `N^δ` of `N η Im m`. -/
theorem poisson_readout (hN : 0 < N) {s : ℝ} (F : CEH.SourceHermitian N)
    (M : CEH.MDEBranch (Real.sqrt s) F) (e : ℝ) {η : ℝ} (hη : 0 < η) {m : ℂ}
    (hm : CEH.normalizedTrace (M.matrix ((e : ℂ) + Complex.I * η)) = m) (hmim : m.im ≠ 0)
    (δ : ℝ) (W : CEH.SourceHermitian N)
    (hW : W ∉ CEH.averagedBadEvent M 1 ((e : ℂ) + Complex.I * η) δ) :
    |spectralSum (CEH.deformedMatrix (Real.sqrt s) F W - (e : ℂ) • 1) (poissonWeight η) -
        (N : ℝ) * η * m.im| ≤ (N : ℝ) ^ δ := by
  set z : ℂ := (e : ℂ) + Complex.I * η
  have hzim : z.im = η := by simp [z]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set A := CEH.deformedMatrix (Real.sqrt s) F W
  have hA : A.IsHermitian := CEH.deformedMatrix_isHermitian _ F W
  have hEh : ((e : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hAe : (A - (e : ℂ) • 1).IsHermitian := hA.sub hEh
  have hres : A - (e : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - (Complex.I * η) • 1 =
      A - z • 1 := by rw [sub_sub, ← add_smul]
  rw [spectralSum_poisson_eq hAe hη, hres]
  -- the imaginary part of `Im m` is `⟨Im M⟩`
  have hImM : CEH.normalizedTrace (CEH.imaginaryPart (M.matrix z)) ≠ 0 := by
    intro h0
    apply hmim
    have : CEH.normalizedTrace (CEH.imaginaryPart (M.matrix z)) = ((m.im : ℝ) : ℂ) := by
      unfold CEH.imaginaryPart CEH.normalizedTrace
      rw [trace_smul, trace_sub, trace_conjTranspose, smul_eq_mul]
      unfold CEH.normalizedTrace at hm
      have hm' : (M.matrix z).trace = (N : ℂ) * m := by
        rw [← hm, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hN.ne'), one_mul]
      rw [hm', Complex.star_def, map_mul, Complex.conj_natCast, ← mul_sub, Complex.sub_conj]
      have : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      push_cast; ring
    rw [this] at h0
    exact_mod_cast h0
  have hctrl := averagedControl_one hN (M.matrix z) z hImM
  simp only [CEH.averagedBadEvent, Set.mem_ofPred_eq, not_lt] at hW
  rw [hctrl, hzim, abs_of_pos hη] at hW
  -- `‖⟨R - M⟩‖ ≤ N^δ/(Nη)`
  have hR : CEH.sourceResolvent (Real.sqrt s) F W z = (A - z • 1)⁻¹ := rfl
  rw [Matrix.mul_one, hR] at hW
  have hdiff : CEH.normalizedTrace ((A - z • 1)⁻¹ - M.matrix z) =
      (N : ℂ)⁻¹ * ((A - z • 1)⁻¹).trace - m := by
    unfold CEH.normalizedTrace at hm ⊢
    rw [trace_sub, mul_sub, hm]
  rw [hdiff] at hW
  have him := Complex.abs_im_le_norm ((N : ℂ)⁻¹ * ((A - z • 1)⁻¹).trace - m)
  have hsplit : ((N : ℂ)⁻¹ * ((A - z • 1)⁻¹).trace - m).im =
      ((A - z • 1)⁻¹).trace.im / N - m.im := by
    rw [Complex.sub_im, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul,
      div_eq_inv_mul]
  rw [hsplit] at him
  have hb := him.trans hW
  rw [mul_one_div, abs_le] at *
  have hNη : 0 < (N : ℝ) * η := mul_pos hNr hη
  obtain ⟨hb1, hb2⟩ := hb
  have k1 : (N : ℝ) * η * (((A - z • 1)⁻¹).trace.im / N - m.im) =
      η * ((A - z • 1)⁻¹).trace.im - (N : ℝ) * η * m.im := by field_simp
  have k2 : (N : ℝ) * η * ((N : ℝ) ^ δ / ((N : ℝ) * η)) = (N : ℝ) ^ δ := by field_simp
  constructor
  · have := mul_le_mul_of_nonneg_left hb1 hNη.le
    rw [mul_neg, k2, k1] at this; linarith
  · have := mul_le_mul_of_nonneg_left hb2 hNη.le
    rw [k2, k1] at this; linarith

end Control

end BlockBand.LocalWindow.ProofCertificate
