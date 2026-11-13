module

public import BlockBand.Transmission.PassiveLayer.BilSmooth
public import BlockBand.Transmission.SchurDerivative

/-!
# Derivative of the resolvent bilinear functional along a coordinate line

`psiMap a c θ P Γ G = a*(G R(G) G*)c` with `R(G) = θPGP + Γ` covers both operators of the
`bilinear` clause (`LL*`: `θ = 0`; `L(R₊ - c₀)L*`: `θ = 1`).

* `hasDerivAt_psi_line`: along `t ↦ (M + tN)⁻¹` (real `t`), with `d𝒢 = -𝒢N𝒢`.
* `psi_deriv_eq`: the derivative equals `-(x₁·Ny₁ + θ x₂·Ny₂ + x₃·N*y₃)` for explicit vectors.
* `fderiv_apply_eq_of_line`: a directional Fréchet derivative is the line derivative.
* `weightedGradientNorm_le`: with a covariance contraction `Σ_i v_i|x·N_i y|² ≤ s‖x‖²‖y‖²`,
  `|∇f|_v ≤ √(3s)(‖x₁‖‖y₁‖ + |θ|‖x₂‖‖y₂‖ + ‖x₃‖‖y₃‖)` (`Inputs.weightedGradientNorm`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator NNReal

open BlockBand.Transmission

section
variable {n : Type} [Fintype n] [DecidableEq n]

/-- `R(G) = θ P G P + Γ`. -/
def rMap (θ : ℂ) (P Γ G : Matrix n n ℂ) : Matrix n n ℂ := θ • (P * G * P) + Γ

/-- `Ψ(G) = a*(G R(G) G*)c`. -/
def psiMap (a c : n → ℂ) (θ : ℂ) (P Γ G : Matrix n n ℂ) : ℂ :=
  star a ⬝ᵥ ((G * rMap θ P Γ G * Gᴴ) *ᵥ c)

/-- The functional `H ↦ a*Hc` as a continuous ℂ-linear map. -/
def formCLM (a c : n → ℂ) : Matrix n n ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => star a ⬝ᵥ (H *ᵥ c)
      map_add' := fun H H' => by simp [add_mulVec, dotProduct_add]
      map_smul' := fun z H => by simp [smul_mulVec, dotProduct_smul] }

theorem hasDerivAt_inv_line (M N : Matrix n n ℂ) (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ => (M + (t : ℂ) • N)⁻¹) (-(M⁻¹ * N * M⁻¹)) 0 := by
  have h := affineInverse_hasDerivAt M N 0 (by simpa using hM)
  simp only [zero_smul, add_zero] at h
  have h' : HasDerivAt (fun s : ℂ => (M + s • N)⁻¹) (-(M⁻¹ * N * M⁻¹)) (Complex.ofRealCLM 0) := by
    simpa using h
  have := h'.scomp (0 : ℝ) Complex.ofRealCLM.hasDerivAt
  simpa [Function.comp_def] using this

/-- **Derivative of `Ψ` along an affine line of matrices.** -/
theorem hasDerivAt_psi_line (a c : n → ℂ) (θ : ℂ) (P Γ M N : Matrix n n ℂ) (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ => psiMap a c θ P Γ ((M + (t : ℂ) • N)⁻¹))
      (-(star a ⬝ᵥ ((M⁻¹ * N * (M⁻¹ * rMap θ P Γ M⁻¹ * M⁻¹ᴴ) +
        θ • (M⁻¹ * P * M⁻¹ * N * (M⁻¹ * P * M⁻¹ᴴ)) +
        M⁻¹ * rMap θ P Γ M⁻¹ * M⁻¹ᴴ * Nᴴ * M⁻¹ᴴ) *ᵥ c))) 0 := by
  set G := M⁻¹
  have hG := hasDerivAt_inv_line M N hM
  have hG0 : (M + ((0 : ℝ) : ℂ) • N)⁻¹ = G := by simp [G]
  have hR : HasDerivAt (fun t : ℝ => rMap θ P Γ ((M + (t : ℂ) • N)⁻¹))
      (θ • (P * -(G * N * G) * P)) 0 := by
    have := ((hG.const_mul P).mul_const P).const_smul θ
    exact this.add_const Γ
  have hH := (hG.mul hR).mul hG.star
  have hl := ((formCLM a c).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hH
  simp only [hG0] at hl
  convert hl using 1
  · funext t; rfl
  · simp only [ContinuousLinearMap.coe_restrictScalars', formCLM,
      LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, hG0]
    rw [← dotProduct_neg, ← neg_mulVec]
    congr 2
    simp only [rMap, star_neg, Matrix.star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_neg,
      Matrix.neg_mul, smul_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
    abel
end

section
variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem form_mul3 (a c : n → ℂ) (X N Y : Matrix n n ℂ) :
    star a ⬝ᵥ ((X * N * Y) *ᵥ c) = (star a ᵥ* X) ⬝ᵥ (N *ᵥ (Y *ᵥ c)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

omit [DecidableEq n] in
/-- The derivative of `Ψ` along `N`, in contracted form. -/
theorem psi_deriv_eq (a c : n → ℂ) (θ : ℂ) (P Γ G N : Matrix n n ℂ) :
    -(star a ⬝ᵥ ((G * N * (G * rMap θ P Γ G * Gᴴ) +
        θ • (G * P * G * N * (G * P * Gᴴ)) + G * rMap θ P Γ G * Gᴴ * Nᴴ * Gᴴ) *ᵥ c)) =
      -((star a ᵥ* G) ⬝ᵥ (N *ᵥ ((G * rMap θ P Γ G * Gᴴ) *ᵥ c)) +
        θ * ((star a ᵥ* (G * P * G)) ⬝ᵥ (N *ᵥ ((G * P * Gᴴ) *ᵥ c))) +
        (star a ᵥ* (G * rMap θ P Γ G * Gᴴ)) ⬝ᵥ (Nᴴ *ᵥ (Gᴴ *ᵥ c))) := by
  rw [add_mulVec, add_mulVec, dotProduct_add, dotProduct_add, smul_mulVec, dotProduct_smul,
    form_mul3, form_mul3, form_mul3, smul_eq_mul]

end

/-- The directional derivative is the derivative along the line. -/
theorem fderiv_apply_eq_of_line {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℂ} {ρ e : ι → ℝ}
    (hf : DifferentiableAt ℝ f ρ) {D : ℂ} (h : HasDerivAt (fun t : ℝ => f (ρ + t • e)) D 0) :
    fderiv ℝ f ρ e = D := by
  have hl : HasDerivAt (fun t : ℝ => ρ + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add ρ
  have h2 : HasDerivAt (fun t : ℝ => f (ρ + t • e)) (fderiv ℝ f ρ e) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h2.unique h

/-- **Abstract gradient bound**: three contracted terms and a covariance contraction with
constant `s` give `|∇f|_v ≤ √(3s) (‖x₁‖‖y₁‖ + |θ|‖x₂‖‖y₂‖ + ‖x₃‖‖y₃‖)`. -/
theorem weightedGradientNorm_le {ι n : Type} [Fintype ι] [DecidableEq ι] [Fintype n]
    (v : ι → ℝ≥0) (f : (ι → ℝ) → ℂ) (ρ : ι → ℝ) (Nd : ι → Matrix n n ℂ) (θ : ℂ)
    (x₁ y₁ x₂ y₂ x₃ y₃ : n → ℂ) {s : ℝ} (hs : 0 ≤ s)
    (hD : ∀ i, fderiv ℝ f ρ (Pi.single i 1) = -(x₁ ⬝ᵥ (Nd i *ᵥ y₁) +
      θ * (x₂ ⬝ᵥ (Nd i *ᵥ y₂)) + x₃ ⬝ᵥ (Nd i *ᵥ y₃)))
    (hcov : ∀ x y : n → ℂ, ∑ i, (v i : ℝ) * ‖x ⬝ᵥ (Nd i *ᵥ y)‖ ^ 2 ≤
      s * vecNorm x ^ 2 * vecNorm y ^ 2) :
    BlockBand.Internal.Contracts.Inputs.weightedGradientNorm v f ρ ≤
      Real.sqrt (3 * s) * (vecNorm x₁ * vecNorm y₁ + ‖θ‖ * (vecNorm x₂ * vecNorm y₂) +
        vecNorm x₃ * vecNorm y₃) := by
  unfold BlockBand.Internal.Contracts.Inputs.weightedGradientNorm
  have hpt : ∀ i, (v i : ℝ) * ‖fderiv ℝ f ρ (Pi.single i 1)‖ ^ 2 ≤
      3 * ((v i : ℝ) * ‖x₁ ⬝ᵥ (Nd i *ᵥ y₁)‖ ^ 2) +
        3 * ‖θ‖ ^ 2 * ((v i : ℝ) * ‖x₂ ⬝ᵥ (Nd i *ᵥ y₂)‖ ^ 2) +
        3 * ((v i : ℝ) * ‖x₃ ⬝ᵥ (Nd i *ᵥ y₃)‖ ^ 2) := by
    intro i
    rw [hD, norm_neg]
    have h1 := norm_add₃_le (a := x₁ ⬝ᵥ (Nd i *ᵥ y₁)) (b := θ * (x₂ ⬝ᵥ (Nd i *ᵥ y₂)))
      (c := x₃ ⬝ᵥ (Nd i *ᵥ y₃))
    rw [norm_mul] at h1
    have hv := (v i).2
    set A := ‖x₁ ⬝ᵥ (Nd i *ᵥ y₁)‖
    set B := ‖x₂ ⬝ᵥ (Nd i *ᵥ y₂)‖
    set C := ‖x₃ ⬝ᵥ (Nd i *ᵥ y₃)‖
    have hA := norm_nonneg (x₁ ⬝ᵥ (Nd i *ᵥ y₁))
    have hB := norm_nonneg (x₂ ⬝ᵥ (Nd i *ᵥ y₂))
    have hC := norm_nonneg (x₃ ⬝ᵥ (Nd i *ᵥ y₃))
    have hθ := norm_nonneg θ
    have hsq : ‖x₁ ⬝ᵥ (Nd i *ᵥ y₁) + θ * (x₂ ⬝ᵥ (Nd i *ᵥ y₂)) + x₃ ⬝ᵥ (Nd i *ᵥ y₃)‖ ^ 2 ≤
        3 * A ^ 2 + 3 * ‖θ‖ ^ 2 * B ^ 2 + 3 * C ^ 2 := by
      have h0 := norm_nonneg (x₁ ⬝ᵥ (Nd i *ᵥ y₁) + θ * (x₂ ⬝ᵥ (Nd i *ᵥ y₂)) + x₃ ⬝ᵥ (Nd i *ᵥ y₃))
      nlinarith [sq_nonneg (A - ‖θ‖ * B), sq_nonneg (A - C), sq_nonneg (‖θ‖ * B - C)]
    nlinarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have h1 := hcov x₁ y₁; have h2 := hcov x₂ y₂; have h3 := hcov x₃ y₃
  have hp1 := mul_nonneg (vecNorm_nonneg x₁) (vecNorm_nonneg y₁)
  have hp2 := mul_nonneg (vecNorm_nonneg x₂) (vecNorm_nonneg y₂)
  have hp3 := mul_nonneg (vecNorm_nonneg x₃) (vecNorm_nonneg y₃)
  have hθ := norm_nonneg θ
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ vecNorm x₁ * vecNorm y₁ + ‖θ‖ *
      (vecNorm x₂ * vecNorm y₂) + vecNorm x₃ * vecNorm y₃), ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hθ2 : 0 ≤ ‖θ‖ ^ 2 := by positivity
  calc _ ≤ 3 * (s * vecNorm x₁ ^ 2 * vecNorm y₁ ^ 2) + 3 * ‖θ‖ ^ 2 * (s * vecNorm x₂ ^ 2 *
          vecNorm y₂ ^ 2) + 3 * (s * vecNorm x₃ ^ 2 * vecNorm y₃ ^ 2) := by nlinarith
    _ ≤ _ := by nlinarith [mul_nonneg hp1 hp2, mul_nonneg hp1 hp3, mul_nonneg hp2 hp3,
          mul_nonneg hθ (mul_nonneg hp1 hp2), mul_nonneg hθ (mul_nonneg hp2 hp3)]

end BlockBand.Transmission.PassiveLayer
