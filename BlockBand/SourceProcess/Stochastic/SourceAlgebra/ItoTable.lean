module
public import BlockBand.SourceProcess.Stochastic.FiniteSource
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Itô table of the finite source noise

For the finite source equation (with `dA dA* = D₀ Naux P dt/2`), in the real noise coordinates
`a = ((k,j),r) ∈ SourceNoise ι`, the coefficient of `dAᴴ` along
`W_a` is `w_r · P' E_jk P` with `w_r = c_r √D₀/2`, `c_0 = 1`, `c_1 = -i`, and
`E_jk = single j k 1`; the diffusion of `V` is that matrix times `V`.

This file proves the pure algebra of the Itô table: `∑_r w_r² = 0`,
`∑_r w_r conj(w_r) = D₀/2`, the matrix-unit contractions
`∑_{jk} E_kj X E_jk = Tr X · 1`, `∑_{jk} (A E_jk B)_ab (C E_kj D)_cd = (AD)_ad (CB)_cb`,
and the resulting generic bracket identity for any ℂ-algebra valued noise of the form
`w X + conj(w) Y`. No measure, stochastic integral or norm appears; `0 ≤ D₀` is used only
for `(√D₀)² = D₀`.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceAlgebra
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar weight `w_r = c_r √D₀/2` (`c_0 = 1`, `c_1 = -i`) of `sourceDiffusion`. -/
def sourceWeight (D0 : ℝ) (r : Fin 2) : ℂ :=
  (if r = 0 then (1 : ℂ) else -Complex.I) * ((Real.sqrt D0 / 2 : ℝ) : ℂ)

/-- The matrix unit `E_jk = single j k 1` attached to the noise coordinate `a = ((k,j),r)`. -/
def sourceUnit (a : SourceNoise ι) : Matrix ι ι ℂ := Matrix.single a.1.2 a.1.1 (1 : ℂ)

/-- The coefficient of `dAᴴ` along `W_a`: `w_r P' E_jk P` (: `dAᴴ = (√D₀/2) P' dZᴴ P`). -/
def sourceNoiseMatrix {c : Type*} [Fintype c] (D0 : ℝ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (a : SourceNoise ι) (V : Matrix ι c ℂ) : Matrix ι ι ℂ :=
  sourceWeight D0 a.2 • (gramProjection P V D * sourceUnit a * P)

theorem sourceDiffusion_eq {c : Type*} [Fintype c] (D0 : ℝ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    sourceDiffusion D0 P D a V = sourceNoiseMatrix D0 P D a V * V := by
  unfold sourceNoiseMatrix
  rw [Matrix.smul_mul]
  rfl

omit [Fintype ι] in
theorem sourceUnit_conjTranspose (a : SourceNoise ι) :
    (sourceUnit a)ᴴ = Matrix.single a.1.1 a.1.2 (1 : ℂ) := by
  simp [sourceUnit]

theorem sqrt_weight_sq {D0 : ℝ} (hD0 : 0 ≤ D0) :
    ((Real.sqrt D0 / 2 : ℝ) : ℂ) * ((Real.sqrt D0 / 2 : ℝ) : ℂ) = ((D0 / 4 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  have h := Real.mul_self_sqrt hD0
  nlinarith [h]

/-- Itô table, holomorphic part: `∑_r w_r² = 0` (`E dZ dZ = 0`). -/
theorem sum_weight_mul_self (D0 : ℝ) : ∑ r : Fin 2, sourceWeight D0 r * sourceWeight D0 r = 0 := by
  simp only [Fin.sum_univ_two, sourceWeight]
  simp
  ring_nf
  simp [Complex.I_sq]

/-- Itô table, antiholomorphic part: `∑_r conj(w_r)² = 0`. -/
theorem sum_star_weight_mul_self (D0 : ℝ) :
    ∑ r : Fin 2, star (sourceWeight D0 r) * star (sourceWeight D0 r) = 0 := by
  simp only [Fin.sum_univ_two, sourceWeight]
  simp [Complex.conj_ofReal]
  ring_nf
  simp [Complex.I_sq]

/-- Itô table, mixed part: `∑_r w_r conj(w_r) = D₀/2` (`E|dZ|² = 2 dt`). -/
theorem sum_weight_mul_star {D0 : ℝ} (hD0 : 0 ≤ D0) :
    ∑ r : Fin 2, sourceWeight D0 r * star (sourceWeight D0 r) = ((D0 / 2 : ℝ) : ℂ) := by
  have hs := sqrt_weight_sq hD0
  simp only [Fin.sum_univ_two, sourceWeight]
  simp only [Fin.isValue, ↓reduceIte, one_mul, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    Complex.star_def, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have : ((D0 / 2 : ℝ) : ℂ) = 2 * ((D0 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← hs]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem sum_star_weight_mul {D0 : ℝ} (hD0 : 0 ≤ D0) :
    ∑ r : Fin 2, star (sourceWeight D0 r) * sourceWeight D0 r = ((D0 / 2 : ℝ) : ℂ) := by
  simp_rw [mul_comm (star _)]
  exact sum_weight_mul_star hD0

omit [DecidableEq ι] in
/-- Generic Itô contraction: for a noise of the form `w_r X_e + conj(w_r) Y_e` with values
in any ℂ-algebra, the sum over the four real-coordinate products kills the `XX` and `YY`
parts and leaves `(D₀/2) ∑_e (X_e Y'_e + Y_e X'_e)`. -/
theorem sum_sourceNoise_mul {A : Type*} [Ring A] [Algebra ℂ A] {D0 : ℝ} (hD0 : 0 ≤ D0)
    (X Y X' Y' : ι × ι → A) :
    ∑ a : SourceNoise ι,
      (sourceWeight D0 a.2 • X a.1 + star (sourceWeight D0 a.2) • Y a.1) *
        (sourceWeight D0 a.2 • X' a.1 + star (sourceWeight D0 a.2) • Y' a.1) =
      ((D0 / 2 : ℝ) : ℂ) • ∑ e, (X e * Y' e + Y e * X' e) := by
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  set w := sourceWeight D0
  have hexp : ∀ r : Fin 2, (w r • X e + star (w r) • Y e) * (w r • X' e + star (w r) • Y' e) =
      (w r * w r) • (X e * X' e) + (w r * star (w r)) • (X e * Y' e) +
        (star (w r) * w r) • (Y e * X' e) + (star (w r) * star (w r)) • (Y e * Y' e) := by
    intro r
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    abel
  simp only [hexp, Finset.sum_add_distrib, ← Finset.sum_smul]
  rw [sum_weight_mul_self, sum_star_weight_mul_self, sum_weight_mul_star hD0,
    sum_star_weight_mul hD0]
  simp [smul_add]

omit [DecidableEq ι] in
/-- Diagonal Itô contraction `∑_r conj(w_r) w_r = D₀/2`, smeared over the units. -/
theorem sum_sourceNoise_star_mul {A : Type*} [AddCommGroup A] [Module ℂ A] {D0 : ℝ}
    (hD0 : 0 ≤ D0) (X : ι × ι → A) :
    ∑ a : SourceNoise ι, (star (sourceWeight D0 a.2) * sourceWeight D0 a.2) • X a.1 =
      ((D0 / 2 : ℝ) : ℂ) • ∑ e, X e := by
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  dsimp only
  rw [← Finset.sum_smul, sum_star_weight_mul hD0]

/-- Matrix-unit contraction: `∑_{jk} E_kj X E_jk = Tr X · 1`. -/
theorem sum_unit_conj_mul_unit (X : Matrix ι ι ℂ) :
    ∑ e : ι × ι, Matrix.single e.1 e.2 (1 : ℂ) * X * Matrix.single e.2 e.1 (1 : ℂ) =
      X.trace • (1 : Matrix ι ι ℂ) := by
  simp only [single_mul_mul_single, one_mul, mul_one]
  ext a b
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, Matrix.one_apply,
    single_apply, Matrix.trace, Matrix.diag, smul_eq_mul]
  by_cases h : a = b
  · subst h; simp [Finset.sum_ite_eq']
  · have : ∀ x : ι, ¬ (x = a ∧ x = b) := fun x hx => h (hx.1.symm.trans hx.2)
    simp [h, this]

/-- Matrix-unit contraction, other order: `∑_{jk} E_jk X E_kj = Tr X · 1`. -/
theorem sum_unit_mul_unit_conj (X : Matrix ι ι ℂ) :
    ∑ e : ι × ι, Matrix.single e.2 e.1 (1 : ℂ) * X * Matrix.single e.1 e.2 (1 : ℂ) =
      X.trace • (1 : Matrix ι ι ℂ) := by
  rw [← sum_unit_conj_mul_unit X]
  exact Fintype.sum_equiv (Equiv.prodComm ι ι) _ _ (fun _ => rfl)

theorem unit_entry {κ κ' : Type*} (A : Matrix κ ι ℂ) (B : Matrix ι κ' ℂ) (p q : ι)
    (i : κ) (j : κ') : (A * Matrix.single p q (1 : ℂ) * B) i j = A i p * B q j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · simp
  · intro b _ hb
    rw [mul_single_apply_of_ne (c := (1 : ℂ)) p q i b hb A, zero_mul]
  · simp

/-- Entry contraction of two crossed matrix units:
`∑_e (A E_{e₂e₁} B)_ij (C E_{e₁e₂} D)_kl = (A D)_il (C B)_kj`. -/
theorem sum_unit_entry_mul {κ₁ κ₂ κ₃ κ₄ : Type*} (A : Matrix κ₁ ι ℂ) (B : Matrix ι κ₂ ℂ)
    (C : Matrix κ₃ ι ℂ) (D : Matrix ι κ₄ ℂ) (i : κ₁) (j : κ₂) (k : κ₃) (l : κ₄) :
    ∑ e : ι × ι, (A * Matrix.single e.2 e.1 (1 : ℂ) * B) i j *
        (C * Matrix.single e.1 e.2 (1 : ℂ) * D) k l =
      (A * D) i l * (C * B) k j := by
  simp_rw [unit_entry]
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end BlockBand.SourceProcess.Stochastic.SourceAlgebra
