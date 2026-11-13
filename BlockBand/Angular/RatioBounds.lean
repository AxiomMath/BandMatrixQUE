module

public import BlockBand.Angular.RatioBasic

/-!
# Reference-covariance bounds for the angular ratio lemma

With `R = (K₀ - ζ)⁻¹` we have `Γ = s Rᴴ R`. For an arbitrary reconstruction matrix
`𝓛 : ℂ^ι → ℂ^κ` with rows `ℓ_k = (𝓛_k)ᴴ`, put `F = Σ_k ‖R ℓ_k‖²`, so that
`T_D = Re Tr(ΓD) = s F`, `D = 𝓛ᴴ𝓛` (`trace_ΓD`). Every bound below is uniform: it involves
only `s`, a bound `Y ≥ (Im ζ)⁻¹`, a bound `Zb ≥ |ζ|`, and `F` (hence `T_D`), never a singular
value of `𝓛`. The angular first-moment hypothesis, tested against every
vector, integrates to `ν(‖𝓛Pv‖²) ≤ C_m s Σ_k ‖R Pᴴ ℓ_k‖²` (`integral_firstMoment`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_real_smul)
open scoped ComplexConjugate

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (D : AngularData ι)

/-- `R = (K₀ - ζ)⁻¹`. -/
def Rz : Matrix ι ι ℂ := Reference.resolvent D.K D.ζ

theorem Rz_conjTranspose : (Rz D)ᴴ = Reference.resolvent D.K (conj D.ζ) :=
  (resolvent_conj D.hK D.ζ).symm

theorem Γ_mulVec (x : ι → ℂ) : D.Γ *ᵥ x = (D.s : ℂ) • ((Rz D)ᴴ *ᵥ (Rz D *ᵥ x)) := by
  rw [D.Γ_eq, smul_mulVec, ← mulVec_mulVec]; rfl

theorem quadNum_Γ (x : ι → ℂ) : quadNum D.Γ x = D.s * normSqSum (Rz D *ᵥ x) := by
  rw [D.Γ_eq, quadNum_real_smul, ← reInner_self, reInner_mulVec_left, mulVec_mulVec]; rfl

theorem im_pos : 0 < D.ζ.im := D.hroot.1

theorem inv_sq_le {Y : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) : (D.ζ.im ^ 2)⁻¹ ≤ Y ^ 2 := by
  rw [← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.2 (im_pos D).le) hY 2

theorem Rz_bound {Y : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) (x : ι → ℂ) :
    normSqSum (Rz D *ᵥ x) ≤ Y ^ 2 * normSqSum x := by
  have h := resolvent_bound D.hK D.hz x
  have hy2 : 0 < D.ζ.im ^ 2 := by have := im_pos D; positivity
  calc normSqSum (Rz D *ᵥ x) ≤ (D.ζ.im ^ 2)⁻¹ * normSqSum x := by
        rw [le_inv_mul_iff₀ hy2]; exact h
    _ ≤ Y ^ 2 * normSqSum x := mul_le_mul_of_nonneg_right (inv_sq_le D hY) (normSqSum_nonneg _)

theorem Rzh_bound {Y : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) (x : ι → ℂ) :
    normSqSum ((Rz D)ᴴ *ᵥ x) ≤ Y ^ 2 * normSqSum x := by
  have h := resolvent_bound D.hK (im_conj_ne D.hz) x
  rw [← Rz_conjTranspose, Complex.conj_im, neg_sq] at h
  have hy2 : 0 < D.ζ.im ^ 2 := by have := im_pos D; positivity
  calc normSqSum ((Rz D)ᴴ *ᵥ x) ≤ (D.ζ.im ^ 2)⁻¹ * normSqSum x := by
        rw [le_inv_mul_iff₀ hy2]; exact h
    _ ≤ Y ^ 2 * normSqSum x := mul_le_mul_of_nonneg_right (inv_sq_le D hY) (normSqSum_nonneg _)

/-- `‖R K₀ x‖ ≤ (1 + |ζ| Y)‖x‖` since `R K₀ = 1 + ζ R`. -/
theorem RzK_bound {Y Zb : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) (hZb : ‖D.ζ‖ ≤ Zb) (x : ι → ℂ) :
    normSqSum (Rz D *ᵥ (D.K *ᵥ x)) ≤ (1 + Zb * Y) ^ 2 * normSqSum x := by
  have e : Rz D *ᵥ (D.K *ᵥ x) = x + D.ζ • (Rz D *ᵥ x) := by
    rw [mulVec_mulVec, Rz, resolvent_mul_K D.hK D.hz, add_mulVec, one_mulVec, smul_mulVec]
  rw [e]
  refine (normSqSum_add_le _ _).trans ?_
  have hY0 : 0 ≤ Y := (inv_nonneg.2 (im_pos D).le).trans hY
  have h1 : l2Norm (D.ζ • (Rz D *ᵥ x)) ≤ Zb * Y * l2Norm x := by
    rw [l2Norm_eq, l2Norm_eq, normSqSum_smul]
    have h2 := Rz_bound D hY x
    rw [← Real.sqrt_sq (show 0 ≤ Zb * Y by positivity [(norm_nonneg D.ζ).trans hZb]),
      ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have : ‖D.ζ‖ ^ 2 ≤ Zb ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hZb 2
    calc ‖D.ζ‖ ^ 2 * normSqSum (Rz D *ᵥ x) ≤ Zb ^ 2 * (Y ^ 2 * normSqSum x) :=
          mul_le_mul this h2 (normSqSum_nonneg _) (sq_nonneg _)
      _ = (Zb * Y) ^ 2 * normSqSum x := by ring
  have hx := l2Norm_sq x
  have hx0 := l2Norm_nonneg x
  have h3 : l2Norm x + l2Norm (D.ζ • (Rz D *ᵥ x)) ≤ (1 + Zb * Y) * l2Norm x := by linarith
  calc (l2Norm x + l2Norm (D.ζ • (Rz D *ᵥ x))) ^ 2 ≤ ((1 + Zb * Y) * l2Norm x) ^ 2 :=
        pow_le_pow_left₀ (by positivity [l2Norm_nonneg (D.ζ • (Rz D *ᵥ x))]) h3 2
    _ = (1 + Zb * Y) ^ 2 * normSqSum x := by rw [mul_pow, hx]

theorem normSqSum_real_smul (c : ℝ) (x : κ → ℂ) :
    normSqSum ((c : ℂ) • x) = c ^ 2 * normSqSum x := by
  rw [normSqSum_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem Γ_bound {Y : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) (x : ι → ℂ) :
    normSqSum (D.Γ *ᵥ x) ≤ D.s ^ 2 * Y ^ 2 * normSqSum (Rz D *ᵥ x) := by
  rw [Γ_mulVec, normSqSum_real_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (Rzh_bound D hY _) (sq_nonneg _)

/-!
## The reconstruction matrix
-/

variable (L : Matrix κ ι ℂ)

/-- `ℓ_k = (𝓛_k)ᴴ`, the adjoint of the `k`-th row. -/
def ell (k : κ) : ι → ℂ := fun j => star (L k j)

/-- `F = Σ_k ‖R ℓ_k‖²`; `T_D = s F`. -/
def Fd : ℝ := ∑ k, normSqSum (Rz D *ᵥ ell L k)

theorem Fd_nonneg : 0 ≤ Fd D L := Finset.sum_nonneg fun _ _ => normSqSum_nonneg _

theorem frob_L_Rzh : frob (L * (Rz D)ᴴ) = Fd D L := by
  unfold frob Fd normSqSum
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← norm_star ((Rz D *ᵥ ell L k) i)]
  congr 2
  simp [mul_apply, mulVec, dotProduct, conjTranspose_apply, star_sum, ell, mul_comm]

theorem frob_Rz_Lh : frob (Rz D * Lᴴ) = Fd D L := by
  unfold frob Fd normSqSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  congr 2

theorem L_Rzh_bound (u : ι → ℂ) :
    normSqSum (L *ᵥ ((Rz D)ᴴ *ᵥ u)) ≤ Fd D L * normSqSum u := by
  rw [mulVec_mulVec, ← frob_L_Rzh]; exact normSqSum_mulVec_le _ _

theorem Rz_Lh_bound (u : κ → ℂ) :
    normSqSum (Rz D *ᵥ (Lᴴ *ᵥ u)) ≤ Fd D L * normSqSum u := by
  rw [mulVec_mulVec, ← frob_Rz_Lh]; exact normSqSum_mulVec_le _ _

/-- `‖𝓛Γx‖² ≤ s² F ‖Rx‖²`. -/
theorem LΓ_bound (x : ι → ℂ) :
    normSqSum (L *ᵥ (D.Γ *ᵥ x)) ≤ D.s ^ 2 * Fd D L * normSqSum (Rz D *ᵥ x) := by
  rw [Γ_mulVec, mulVec_smul, normSqSum_real_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (L_Rzh_bound D L _) (sq_nonneg _)

theorem quadNum_eq_dot (M : Matrix ι ι ℂ) (x : ι → ℂ) : quadNum M x = (star x ⬝ᵥ (M *ᵥ x)).re :=
  rfl

/-- `T_D = Re Tr(ΓD) = s F`. -/
theorem trace_ΓD : (D.Γ * (Lᴴ * L)).trace.re = D.s * Fd D L := by
  have e : (D.Γ * (Lᴴ * L)).trace = ∑ k, star (ell L k) ⬝ᵥ (D.Γ *ᵥ ell L k) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, dotProduct, mulVec,
      Pi.star_apply, star_star, ell, Finset.mul_sum]
  rw [e, Complex.re_sum, Fd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← quadNum_eq_dot, quadNum_Γ]

theorem row_eq (P : Matrix ι ι ℂ) (k : κ) :
    (fun i => star ((L * P) k i)) = Pᴴ *ᵥ ell L k := by
  funext i
  simp [mul_apply, mulVec, dotProduct, conjTranspose_apply, star_sum, ell, mul_comm]

/-- **First-moment bound for a reconstructed quadratic form.** If
`∫ ρ |w*v|² dν_N ≤ C_m Re(w*Γw)` for every `w` (the angular first-moment bound tested against
vectors, `C_m = C₀(Z+r)/N`), then `∫ ρ ‖𝓛Pv‖² dν_N ≤ C_m s Σ_k ‖R Pᴴ ℓ_k‖²`. -/
theorem integral_firstMoment [Nonempty ι] {ρ : (ι → ℂ) → ℝ} (hρ : ContinuousOn ρ {z | z ≠ 0})
    {Cm : ℝ} (hFM : ∀ w : ι → ℂ,
      ∫ v, ρ v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι ≤ Cm * quadNum D.Γ w)
    (P : Matrix ι ι ℂ) :
    ∫ v, ρ v * normSqSum (L *ᵥ (P *ᵥ v)) ∂projectiveHaar ι ≤
      Cm * (D.s * ∑ k, normSqSum (Rz D *ᵥ (Pᴴ *ᵥ ell L k))) := by
  have e : ∀ v : ι → ℂ, ρ v * normSqSum (L *ᵥ (P *ᵥ v)) =
      ∑ k, ρ v * ‖star (fun i => star ((L * P) k i)) ⬝ᵥ v‖ ^ 2 := by
    intro v
    rw [normSqSum, Finset.mul_sum, mulVec_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 3
    simp [mulVec, dotProduct]
  simp_rw [e]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← quadNum_Γ, ← row_eq]
    exact hFM _
  · intro k _
    refine integrable_of_continuousOn (hρ.mul ?_)
    exact (Continuous.continuousOn (by fun_prop))

/-- `Σ_k ‖R (ΓM)ᴴ ℓ_k‖² ≤ c_M s² Y² F` for Hermitian `M` with `‖RMx‖² ≤ c_M ‖x‖²`. -/
theorem sum_ΓM_bound {Y : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    {cM : ℝ} (hcM0 : 0 ≤ cM) (hcM : ∀ x, normSqSum (Rz D *ᵥ (M *ᵥ x)) ≤ cM * normSqSum x) :
    ∑ k, normSqSum (Rz D *ᵥ ((D.Γ * M)ᴴ *ᵥ ell L k)) ≤ cM * D.s ^ 2 * Y ^ 2 * Fd D L := by
  rw [Fd, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [conjTranspose_mul, hM.eq, D.Γ_isHermitian.eq, ← mulVec_mulVec]
  calc normSqSum (Rz D *ᵥ (M *ᵥ (D.Γ *ᵥ ell L k)))
      ≤ cM * normSqSum (D.Γ *ᵥ ell L k) := hcM _
    _ ≤ cM * (D.s ^ 2 * Y ^ 2 * normSqSum (Rz D *ᵥ ell L k)) :=
        mul_le_mul_of_nonneg_left (Γ_bound D hY _) hcM0
    _ = _ := by ring

end BlockBand.Angular.Ratio
