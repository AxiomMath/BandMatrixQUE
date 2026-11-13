module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The current carrier: Loewner comparison into `nuclearNorm` (linear algebra)

Congruence preserves the Loewner order, and the inequalities hold at `j₀`. So
`-H_j ⪯ J_j ⪯ H_j`, hence `Tr|J_j| ≤ Tr H_j`. Deterministic matrices.

* `nuclearNorm_eq_sum_abs`: for Hermitian `J`, `nuclearNorm J = Σ_i |λ_i(J)|` (`nuclearNorm`
  uses `charpoly.roots`).
* `nuclearNorm_le_of_loewner`: `H - J ⪰ 0`, `H + J ⪰ 0` give `nuclearNorm J ≤ Re Tr H`.
* `absMat`: `|J| = U diag|λ| Uᴴ`, with `|J| ∓ J ⪰ 0` and `Re Tr|J| = nuclearNorm J`
  (`absMat_sub_posSemidef`, `absMat_add_posSemidef`, `trace_absMat`).
* `loewner_congr`: `H ∓ J ⪰ 0 ⇒ NᴴHN ∓ NᴴJN ⪰ 0` (the carrier transport `H₊ = NᴴHN` against
  current conservation `J₊ = NᴴJN`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem nuclearNorm_eq_sum_abs {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    nuclearNorm J = ∑ i, |hJ.eigenvalues i| := by
  rw [nuclearNorm, hJ.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp only [Function.comp_apply, Finset.sum_map_val]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- `Uᴴ J U = diag λ` for the eigenvector unitary `U`. -/
theorem eigen_conj_eq {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    (hJ.eigenvectorUnitary : Matrix n n ℂ)ᴴ * J * (hJ.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hJ.eigenvalues i : ℝ) : ℂ)) := by
  have h := hJ.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  rw [← Matrix.star_eq_conjTranspose, h]
  rfl

theorem unitary_mul_star (U : Matrix.unitaryGroup n ℂ) :
    (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self U

theorem unitary_star_mul (U : Matrix.unitaryGroup n ℂ) :
    (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self U

theorem trace_conj_unitary (U : Matrix.unitaryGroup n ℂ) (H : Matrix n n ℂ) :
    ((U : Matrix n n ℂ)ᴴ * H * (U : Matrix n n ℂ)).trace = H.trace := by
  rw [Matrix.trace_mul_cycle, unitary_mul_star, Matrix.one_mul]

theorem re_le_of_nonneg {z w : ℂ} (h : 0 ≤ z - w) : w.re ≤ z.re := by
  have := (Complex.nonneg_iff.mp h).1
  simp only [Complex.sub_re] at this; linarith

/-- **Loewner comparison**: `-H ⪯ J ⪯ H` gives `Tr|J| ≤ Re Tr H`. -/
theorem nuclearNorm_le_of_loewner {J H : Matrix n n ℂ} (hJ : J.IsHermitian)
    (h₁ : (H - J).PosSemidef) (h₂ : (H + J).PosSemidef) : nuclearNorm J ≤ H.trace.re := by
  set U : Matrix n n ℂ := ((hJ.eigenvectorUnitary : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)
  rw [nuclearNorm_eq_sum_abs hJ, ← trace_conj_unitary hJ.eigenvectorUnitary H, Matrix.trace,
    Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hl : (Uᴴ * J * U) i i = ((hJ.eigenvalues i : ℝ) : ℂ) := by
    rw [eigen_conj_eq hJ, diagonal_apply_eq]
  have d₁ := (h₁.conjTranspose_mul_mul_same U).diag_nonneg (i := i)
  have d₂ := (h₂.conjTranspose_mul_mul_same U).diag_nonneg (i := i)
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, hl] at d₁
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hl] at d₂
  have a := re_le_of_nonneg d₁
  have b := re_le_of_nonneg (z := (Uᴴ * H * U) i i) (w := -((hJ.eigenvalues i : ℝ) : ℂ))
    (by rwa [sub_neg_eq_add])
  simp only [Complex.ofReal_re, Complex.neg_re] at a b
  simp only [diag_apply]
  exact abs_le.mpr ⟨by linarith, a⟩

/-- `|J| = U diag|λ| Uᴴ`. -/
def absMat {J : Matrix n n ℂ} (hJ : J.IsHermitian) : Matrix n n ℂ :=
  (hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((|hJ.eigenvalues i| : ℝ) : ℂ)) *
    (hJ.eigenvectorUnitary : Matrix n n ℂ)ᴴ

theorem conj_eigen {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    J = (hJ.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((hJ.eigenvalues i : ℝ) : ℂ)) *
      (hJ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  rw [← eigen_conj_eq hJ]
  simp only [← Matrix.mul_assoc, unitary_mul_star, Matrix.one_mul]
  rw [Matrix.mul_assoc, unitary_mul_star, Matrix.mul_one]

theorem posSemidef_conj_diagonal (U : Matrix n n ℂ) (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (U * diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ).PosSemidef := by
  have h : (diagonal (fun i => ((d i : ℝ) : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by simpa using hd i)
  simpa using h.mul_mul_conjTranspose_same U

theorem absMat_sub_posSemidef {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    (absMat hJ - J).PosSemidef := by
  have e : absMat hJ - J = (hJ.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (((|hJ.eigenvalues i| - hJ.eigenvalues i : ℝ)) : ℂ)) *
        (hJ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    have e0 : absMat hJ - J = absMat hJ - (hJ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((hJ.eigenvalues i : ℝ) : ℂ)) *
          (hJ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by rw [← conj_eigen hJ]
    rw [e0, absMat, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 3; funext i; push_cast; ring
  rw [e]; exact posSemidef_conj_diagonal _ _ fun i => sub_nonneg.mpr (le_abs_self _)

theorem absMat_add_posSemidef {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    (absMat hJ + J).PosSemidef := by
  have e : absMat hJ + J = (hJ.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (((|hJ.eigenvalues i| + hJ.eigenvalues i : ℝ)) : ℂ)) *
        (hJ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    have e0 : absMat hJ + J = absMat hJ + (hJ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((hJ.eigenvalues i : ℝ) : ℂ)) *
          (hJ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by rw [← conj_eigen hJ]
    rw [e0, absMat, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3; funext i; push_cast; ring
  rw [e]; exact posSemidef_conj_diagonal _ _ fun i => by
    have := neg_abs_le (hJ.eigenvalues i); linarith

theorem absMat_posSemidef {J : Matrix n n ℂ} (hJ : J.IsHermitian) : (absMat hJ).PosSemidef :=
  posSemidef_conj_diagonal _ _ fun _ => abs_nonneg _

theorem trace_absMat {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    (absMat hJ).trace.re = nuclearNorm J := by
  rw [absMat, Matrix.trace_mul_cycle, unitary_star_mul, Matrix.one_mul, trace_diagonal,
    Complex.re_sum, nuclearNorm_eq_sum_abs hJ]
  simp

omit [DecidableEq n] in
/-- **Congruence preserves the Loewner sandwich.** -/
theorem loewner_congr {m : Type*} [Fintype m] {J H : Matrix n n ℂ} (N : Matrix n m ℂ)
    (h₁ : (H - J).PosSemidef) (h₂ : (H + J).PosSemidef) :
    (Nᴴ * H * N - Nᴴ * J * N).PosSemidef ∧ (Nᴴ * H * N + Nᴴ * J * N).PosSemidef := by
  constructor
  · have := h₁.conjTranspose_mul_mul_same N
    rwa [Matrix.mul_sub, Matrix.sub_mul] at this
  · have := h₂.conjTranspose_mul_mul_same N
    rwa [Matrix.mul_add, Matrix.add_mul] at this

end BlockBand.SourceProcess.FullSourceStops
