module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Renormalizing an almost-orthonormal frame

For a Hermitian `S ∈ ℂ^{r×r}` with entrywise `|(S - I)_{ij}| ≤ ε` and `r²ε ≤ 1/2`,
`exists_frameRoot` gives a Hermitian invertible `T` with `T^*T = S` and entrywise
`|(T - I)_{ij}| ≤ r³ε` (`T = S^{1/2}` through the spectral theorem: if `S = U diag(d) U^*` then
`T = U diag(√d) U^*`, `|d_k - 1| ≤ r²ε` and `|√d - 1| ≤ |d - 1|`). The frame `V₀ = V T⁻¹`
then has `V₀^*ΓV₀ = I_r` and `V = V₀T` (`frame_renormalize`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix

variable {r : ℕ}

/-- `U diag(e) U^*` for a real vector `e`. -/
def unitaryConj (U : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  U * diagonal (fun k => (e k : ℂ)) * Uᴴ

theorem unitaryConj_apply (U : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℝ) (i j : Fin r) :
    unitaryConj U e i j = ∑ k, U i k * (e k : ℂ) * star (U j k) := by
  rw [unitaryConj, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply]

theorem unitaryConj_mul (U : Matrix (Fin r) (Fin r) ℂ) (hU : Uᴴ * U = 1) (e e' : Fin r → ℝ) :
    unitaryConj U e * unitaryConj U e' = unitaryConj U (fun k => e k * e' k) := by
  unfold unitaryConj
  calc U * diagonal (fun k => (e k : ℂ)) * Uᴴ * (U * diagonal (fun k => (e' k : ℂ)) * Uᴴ)
      = U * diagonal (fun k => (e k : ℂ)) * (Uᴴ * U) * diagonal (fun k => (e' k : ℂ)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
        push_cast
        rfl

theorem unitaryConj_one (U : Matrix (Fin r) (Fin r) ℂ) (hU : U * Uᴴ = 1) :
    unitaryConj U (fun _ => 1) = 1 := by
  unfold unitaryConj
  simp only [Complex.ofReal_one, diagonal_one, Matrix.mul_one, hU]

theorem unitaryConj_sub_one (U : Matrix (Fin r) (Fin r) ℂ) (hU : U * Uᴴ = 1) (e : Fin r → ℝ) :
    unitaryConj U e - 1 = unitaryConj U (fun k => e k - 1) := by
  conv_lhs => rw [← unitaryConj_one U hU]
  unfold unitaryConj
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  push_cast
  rfl

theorem unitaryConj_conjTranspose (U : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℝ) :
    (unitaryConj U e)ᴴ = unitaryConj U e := by
  unfold unitaryConj
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]
  congr 3
  funext k
  simp

theorem norm_unitaryConj_apply_le (U : Matrix (Fin r) (Fin r) ℂ) (hU : ∀ i j, ‖U i j‖ ≤ 1)
    (e : Fin r → ℝ) {b : ℝ} (he : ∀ k, |e k| ≤ b) (i j : Fin r) :
    ‖unitaryConj U e i j‖ ≤ r * b := by
  rw [unitaryConj_apply]
  calc ‖∑ k, U i k * (e k : ℂ) * star (U j k)‖ ≤ ∑ _k : Fin r, b :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by
          rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
          have h1 := hU i k
          have h2 := hU j k
          have h3 := he k
          have h0 : 0 ≤ |e k| := abs_nonneg _
          calc ‖U i k‖ * |e k| * ‖U j k‖ ≤ 1 * |e k| * 1 := by gcongr
            _ ≤ b := by linarith)
    _ = r * b := by simp

/-- `|√d - 1| ≤ |d - 1|` for `d ≥ 0`. -/
theorem abs_sqrt_sub_one_le {d : ℝ} (hd : 0 ≤ d) : |Real.sqrt d - 1| ≤ |d - 1| := by
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd
  have hfac : d - 1 = (Real.sqrt d - 1) * (Real.sqrt d + 1) := by nlinarith
  rw [hfac, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt d + 1)]
  have := abs_nonneg (Real.sqrt d - 1)
  nlinarith

/-- **Square root of an almost-identity Hermitian matrix.** For Hermitian `S ∈ ℂ^{r×r}` with
`|(S - I)_{ij}| ≤ ε` for all `i, j` and `r²ε ≤ 1/2`, there are `T, T⁻¹` with `T^* = T`,
`T^*T = S`, `TT⁻¹ = T⁻¹T = I` and `|(T - I)_{ij}| ≤ r³ε` (spectral theorem). -/
theorem exists_frameRoot {S : Matrix (Fin r) (Fin r) ℂ} (hS : S.IsHermitian) {ε : ℝ}
    (hε : ∀ i j, ‖(S - 1) i j‖ ≤ ε) (hsmall : (r : ℝ) ^ 2 * ε ≤ 1 / 2) :
    ∃ T Tinv : Matrix (Fin r) (Fin r) ℂ, Tᴴ = T ∧ Tᴴ * T = S ∧ T * Tinv = 1 ∧ Tinv * T = 1 ∧
      ∀ i j, ‖(T - 1) i j‖ ≤ (r : ℝ) ^ 3 * ε := by
  set U : Matrix (Fin r) (Fin r) ℂ := (hS.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) with hUdef
  have hU1 : Uᴴ * U = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hU2 : U * Uᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  have hUe : ∀ i j, ‖U i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hS.eigenvectorUnitary.2 i j
  set d := hS.eigenvalues with hddef
  have hspec : S = unitaryConj U d := by
    have h := hS.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [unitaryConj, ← star_eq_conjTranspose]
    exact h
  -- `U^* (S - I) U = diag(d - 1)`.
  have hdiag : Uᴴ * (S - 1) * U = diagonal (fun k => ((d k - 1 : ℝ) : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1, hspec, unitaryConj]
    calc Uᴴ * (U * diagonal (fun k => (d k : ℂ)) * Uᴴ) * U - 1
        = (Uᴴ * U) * diagonal (fun k => (d k : ℂ)) * (Uᴴ * U) - 1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU1, Matrix.one_mul, Matrix.mul_one, ← diagonal_one, diagonal_sub]
          push_cast
          rfl
  have hd : ∀ k, |d k - 1| ≤ (r : ℝ) ^ 2 * ε := by
    intro k
    have hk := congrFun (congrFun hdiag k) k
    rw [diagonal_apply_eq] at hk
    have hn : ‖(Uᴴ * (S - 1) * U) k k‖ ≤ (r : ℝ) ^ 2 * ε := by
      rw [Matrix.mul_apply]
      calc ‖∑ j, (Uᴴ * (S - 1)) k j * U j k‖ ≤ ∑ _j : Fin r, (r : ℝ) * ε := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [norm_mul, Matrix.mul_apply]
            have hb : ‖∑ i, Uᴴ k i * (S - 1) i j‖ ≤ ∑ _i : Fin r, ε := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
              rw [norm_mul, conjTranspose_apply, norm_star]
              have h1 := hUe i k
              have h2 := hε i j
              have h0 : 0 ≤ ‖(S - 1) i j‖ := norm_nonneg _
              calc ‖U i k‖ * ‖(S - 1) i j‖ ≤ 1 * ‖(S - 1) i j‖ := by gcongr
                _ ≤ ε := by linarith
            have hb' : ‖∑ i, Uᴴ k i * (S - 1) i j‖ ≤ r * ε := by simpa using hb
            have h1 := hUe j k
            have hε0 : 0 ≤ (r : ℝ) * ε := (norm_nonneg _).trans hb'
            calc ‖∑ i, Uᴴ k i * (S - 1) i j‖ * ‖U j k‖ ≤ (r * ε) * 1 := by
                  gcongr
              _ = r * ε := mul_one _
        _ = (r : ℝ) ^ 2 * ε := by simp; ring
    rw [hk, Complex.norm_real, Real.norm_eq_abs] at hn
    exact hn
  have hdpos : ∀ k, 0 < d k := fun k => by
    have := (abs_le.1 (hd k)).1
    linarith
  set s : Fin r → ℝ := fun k => Real.sqrt (d k) with hsdef
  have hspos : ∀ k, 0 < s k := fun k => Real.sqrt_pos.2 (hdpos k)
  refine ⟨unitaryConj U s, unitaryConj U (fun k => (s k)⁻¹), unitaryConj_conjTranspose U s,
    ?_, ?_, ?_, ?_⟩
  · rw [unitaryConj_conjTranspose, unitaryConj_mul U hU1, hspec]
    congr 1
    funext k
    exact Real.mul_self_sqrt (hdpos k).le
  · rw [unitaryConj_mul U hU1, ← unitaryConj_one U hU2]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hspos k).ne'
  · rw [unitaryConj_mul U hU1, ← unitaryConj_one U hU2]
    congr 1
    funext k
    exact inv_mul_cancel₀ (hspos k).ne'
  · intro i j
    rw [unitaryConj_sub_one U hU2]
    have h := norm_unitaryConj_apply_le U hUe (fun k => s k - 1) (b := (r : ℝ) ^ 2 * ε)
      (fun k => (abs_sqrt_sub_one_le (hdpos k).le).trans (hd k)) i j
    calc _ ≤ (r : ℝ) * ((r : ℝ) ^ 2 * ε) := h
      _ = (r : ℝ) ^ 3 * ε := by ring

/-- **Frame renormalization.** If `T^*T = V^*ΓV` and `TT⁻¹ = T⁻¹T = I`, then `V₀ = VT⁻¹`
satisfies `V₀^*ΓV₀ = I_r` and `V = V₀T`. -/
theorem frame_renormalize {N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin r) ℂ)
    {T Tinv : Matrix (Fin r) (Fin r) ℂ} (hTT : Tᴴ * T = Vᴴ * Γ * V) (hT1 : T * Tinv = 1)
    (hT2 : Tinv * T = 1) :
    (V * Tinv)ᴴ * Γ * (V * Tinv) = 1 ∧ V * Tinv * T = V := by
  refine ⟨?_, by rw [Matrix.mul_assoc, hT2, Matrix.mul_one]⟩
  calc (V * Tinv)ᴴ * Γ * (V * Tinv) = Tinvᴴ * (Vᴴ * Γ * V) * Tinv := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (T * Tinv)ᴴ * (T * Tinv) := by
        rw [← hTT, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hT1, conjTranspose_one, Matrix.mul_one]

end BlockBand.Critical.RelativeVectors
