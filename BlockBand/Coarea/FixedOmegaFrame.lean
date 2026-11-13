module

public import BlockBand.Coarea.FixedOmegaAlgebra
public import BlockBand.Coarea.GUELaw

/-!
# Fixed-`ω` coarea: frame independence and phase invariance of the `G_{d-1}` integral

*Measure.* `gueMeasure κ t` (`GUE_{d-1}(t)`), every `t : ℝ≥0`. *Domain.* A unit vector
`v : ι → ℂ`, frames `U : Matrix ι κ ℂ` of `v^⊥`, `|ι| = |κ| + 1`, a Hermitian `F`, a real energy
`E`, a nonnegative scalar `K`, counts `nR, α : ℕ` and an arbitrary `g ≥ 0` (no measurability is
needed). Exact identities; no limit or uniformity statement.

## Main results

* `fiberIntegrand`: the `G'`-integrand of `coareaFiber` with an arbitrary frame,
  `ofReal (K |det M|²) · 1{N_-(M) + nR = α} · g(E vvᴴ + U(UᴴFU + G')Uᴴ - F)`,
  `M = UᴴFU + G' - E`.
* `fiberIntegrand_frame_mul`: changing the frame by a unitary `W` is the conjugation
  `G' ↦ W G' Wᴴ` of the `G'` variable.
* `lintegral_fiberIntegrand_frame_eq`: the `GUE_{d-1}` integral is the same for every frame of
  `v^⊥` (unitary invariance of `GUE`).
* `lintegral_fiberIntegrand_phase`: the integral is invariant under `v ↦ c v`, `|c| = 1`, with
  the frame `U(cv)` of `(cv)^⊥ = v^⊥`.
* `regressionFactor_smul`, `quadSpeed_smul`: phase invariance of `𝓡(E,v,F)` and of
  `Re(vᴴ D v)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw
open scoped ENNReal NNReal ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `N_-` is invariant under unitary conjugation, Hermitian or not. -/
theorem negativeCount_unitary_conj' {W M : Matrix ι ι ℂ} (hW : Wᴴ * W = 1) :
    negativeCount (Wᴴ * M * W) = negativeCount M := by
  by_cases hM : M.IsHermitian
  · exact negativeCount_unitary_conj hW hM
  · have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
    have hM' : ¬ (Wᴴ * M * W).IsHermitian := by
      intro h
      apply hM
      have h2 := isHermitian_conjTranspose_mul_mul Wᴴ h
      rwa [conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hW',
        Matrix.one_mul, Matrix.mul_assoc, hW', Matrix.mul_one] at h2
    unfold negativeCount
    simp [hM, hM']

/-- The `G'`-integrand of `coareaFiber`, for an arbitrary frame `U`. -/
def fiberIntegrand (U : Matrix ι κ ℂ) (F : Matrix ι ι ℂ) (E : ℝ) (v : ι → ℂ) (nR α : ℕ)
    (K : ℝ) (g : Matrix ι ι ℂ → ℝ≥0∞) (G' : Matrix κ κ ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (K * Complex.normSq (Uᴴ * F * U + G' - (E : ℂ) • 1).det) *
    (if negativeCount (Uᴴ * F * U + G' - (E : ℂ) • 1) + nR = α then 1 else 0) *
    g ((E : ℂ) • vecMulVec v (star v) + U * (Uᴴ * F * U + G') * Uᴴ - F)

/-- A unitary change of frame `U ↦ U W` is the conjugation `G' ↦ W G' Wᴴ`. -/
theorem fiberIntegrand_frame_mul (U : Matrix ι κ ℂ) {W : Matrix κ κ ℂ} (hW : Wᴴ * W = 1)
    (F : Matrix ι ι ℂ) (E : ℝ) (v : ι → ℂ) (nR α : ℕ) (K : ℝ) (g : Matrix ι ι ℂ → ℝ≥0∞)
    (G' : Matrix κ κ ℂ) :
    fiberIntegrand (U * W) F E v nR α K g G' =
      fiberIntegrand U F E v nR α K g (W * G' * Wᴴ) := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hM : (U * W)ᴴ * F * (U * W) + G' - (E : ℂ) • 1 =
      Wᴴ * (Uᴴ * F * U + W * G' * Wᴴ - (E : ℂ) • 1) * W := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, ← Matrix.mul_assoc, hW, Matrix.one_mul]
    rw [Matrix.mul_assoc G' Wᴴ W, hW, Matrix.mul_one]
  have hR : U * W * ((U * W)ᴴ * F * (U * W) + G') * (U * W)ᴴ =
      U * (Uᴴ * F * U + W * G' * Wᴴ) * Uᴴ := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc U W Wᴴ, hW', Matrix.mul_one,
      Matrix.mul_assoc (U * Uᴴ * F * U) W Wᴴ, hW', Matrix.mul_one]
  unfold fiberIntegrand
  rw [hM, hR, det_unitary_conj hW, negativeCount_unitary_conj' hW]

/-- Conjugation by a unitary `W`, as a measurable equivalence. -/
def unitaryConjEquiv {W : Matrix κ κ ℂ} (hW : Wᴴ * W = 1) :
    Matrix κ κ ℂ ≃ᵐ Matrix κ κ ℂ where
  toFun G := W * G * Wᴴ
  invFun G := Wᴴ * G * W
  left_inv G := by
    have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
    simp only [← Matrix.mul_assoc, hW, Matrix.one_mul]
    rw [Matrix.mul_assoc, hW, Matrix.mul_one]
  right_inv G := by
    have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
    simp only [← Matrix.mul_assoc, hW', Matrix.one_mul]
    rw [Matrix.mul_assoc, hW', Matrix.mul_one]
  measurable_toFun :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  measurable_invFun :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable

theorem gueMeasure_map_unitaryConjEquiv (t : ℝ≥0) {W : Matrix κ κ ℂ} (hW : Wᴴ * W = 1) :
    (gueMeasure κ t).map (unitaryConjEquiv hW) = gueMeasure κ t := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hu : W ∈ Matrix.unitaryGroup κ ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    exact hW'
  exact gueMeasure_map_unitary_conj t hu

/-- Unitary change of the frame does not change the `GUE_{d-1}` integral. -/
theorem lintegral_fiberIntegrand_frame_mul (t : ℝ≥0) (U : Matrix ι κ ℂ) {W : Matrix κ κ ℂ}
    (hW : Wᴴ * W = 1) (F : Matrix ι ι ℂ) (E : ℝ) (v : ι → ℂ) (nR α : ℕ) (K : ℝ)
    (g : Matrix ι ι ℂ → ℝ≥0∞) :
    ∫⁻ G', fiberIntegrand (U * W) F E v nR α K g G' ∂gueMeasure κ t =
      ∫⁻ G', fiberIntegrand U F E v nR α K g G' ∂gueMeasure κ t := by
  simp_rw [fiberIntegrand_frame_mul U hW]
  conv_rhs => rw [← gueMeasure_map_unitaryConjEquiv t hW]
  rw [MeasureTheory.lintegral_map_equiv]
  rfl

/-- **Frame independence** of the `GUE_{d-1}` integral (the coarea formula is
frame independent). For two orthonormal frames `U₁, U₂` of `v^⊥`, `|ι| = |κ| + 1`. -/
theorem lintegral_fiberIntegrand_frame_eq (t : ℝ≥0)
    (hcard : Fintype.card ι = Fintype.card κ + 1) {v : ι → ℂ} (hv : star v ⬝ᵥ v = 1)
    {U₁ U₂ : Matrix ι κ ℂ} (h₁ : IsFrameOf v U₁) (h₂ : IsFrameOf v U₂)
    (F : Matrix ι ι ℂ) (E : ℝ) (nR α : ℕ) (K : ℝ) (g : Matrix ι ι ℂ → ℝ≥0∞) :
    ∫⁻ G', fiberIntegrand U₂ F E v nR α K g G' ∂gueMeasure κ t =
      ∫⁻ G', fiberIntegrand U₁ F E v nR α K g G' ∂gueMeasure κ t := by
  have hmul := frameChange_mul hcard hv h₁ h₂
  have hW := frameChange_unitary hcard hv h₁ h₂
  rw [← hmul]
  exact lintegral_fiberIntegrand_frame_mul t U₁ hW F E v nR α K g

/-!
## Phase invariance
-/

theorem vecMulVec_smul_star {c : ℂ} (hc : ‖c‖ = 1) (v : ι → ℂ) :
    vecMulVec (c • v) (star (c • v)) = vecMulVec v (star v) := by
  have hcc : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  ext a b
  simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul']
  calc c * v a * (star c * star (v b)) = (c * star c) * (v a * star (v b)) := by ring
    _ = _ := by rw [hcc, one_mul]

theorem fiberIntegrand_smul (U : Matrix ι κ ℂ) (F : Matrix ι ι ℂ) (E : ℝ) {c : ℂ}
    (hc : ‖c‖ = 1) (v : ι → ℂ) (nR α : ℕ) (K : ℝ) (g : Matrix ι ι ℂ → ℝ≥0∞)
    (G' : Matrix κ κ ℂ) :
    fiberIntegrand U F E (c • v) nR α K g G' = fiberIntegrand U F E v nR α K g G' := by
  unfold fiberIntegrand
  rw [vecMulVec_smul_star hc]

theorem isFrameOf_smul {c : ℂ} (hc : c ≠ 0) {v : ι → ℂ} {U : Matrix ι κ ℂ} :
    IsFrameOf (c • v) U ↔ IsFrameOf v U := by
  unfold IsFrameOf
  rw [Matrix.mulVec_smul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (smul_eq_zero.mp h2).resolve_left hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, smul_zero]⟩

/-- **Phase invariance** of the `GUE_{d-1}` integral with a frame map `U`: if `U(cv)` is a
frame of `(cv)^⊥` and `U v` a frame of `v^⊥`, the integrals at `cv` and `v` agree. -/
theorem lintegral_fiberIntegrand_phase (t : ℝ≥0)
    (hcard : Fintype.card ι = Fintype.card κ + 1) {v : ι → ℂ} (hv : star v ⬝ᵥ v = 1)
    {c : ℂ} (hc : ‖c‖ = 1) {U₁ U₂ : Matrix ι κ ℂ} (h₁ : IsFrameOf (c • v) U₁)
    (h₂ : IsFrameOf v U₂) (F : Matrix ι ι ℂ) (E : ℝ) (nR α : ℕ) (K : ℝ)
    (g : Matrix ι ι ℂ → ℝ≥0∞) :
    ∫⁻ G', fiberIntegrand U₁ F E (c • v) nR α K g G' ∂gueMeasure κ t =
      ∫⁻ G', fiberIntegrand U₂ F E v nR α K g G' ∂gueMeasure κ t := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  simp_rw [fiberIntegrand_smul U₁ F E hc v]
  exact lintegral_fiberIntegrand_frame_eq t hcard hv h₂ ((isFrameOf_smul hc0).1 h₁) F E nR α K g

theorem l2Norm_smul_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) (x : ι → ℂ) :
    l2Norm (c • x) = l2Norm x := by
  unfold l2Norm
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

/-- Phase invariance of the regression factor `𝓡(E, v, F)`. -/
theorem regressionFactor_smul (t E : ℝ) {c : ℂ} (hc : ‖c‖ = 1) (v : ι → ℂ)
    (F : Matrix ι ι ℂ) : regressionFactor t E (c • v) F = regressionFactor t E v F := by
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  have ha : star (c • v) ⬝ᵥ (F *ᵥ (c • v)) = star v ⬝ᵥ (F *ᵥ v) := by
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul,
      smul_eq_mul, hcc, one_mul]
  unfold regressionFactor
  simp only [ha]
  have hvec : F *ᵥ (c • v) - (star v ⬝ᵥ (F *ᵥ v)) • (c • v) =
      c • (F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v) := by
    rw [Matrix.mulVec_smul, smul_sub, smul_comm]
  rw [hvec, l2Norm_smul_of_norm_one hc]

/-- Phase invariance of the crossing speed `Re(vᴴ D v)`. -/
theorem quadSpeed_smul {c : ℂ} (hc : ‖c‖ = 1) (v : ι → ℂ) (D : Matrix ι ι ℂ) :
    (star (c • v) ⬝ᵥ (D *ᵥ (c • v))).re = (star v ⬝ᵥ (D *ᵥ v)).re := by
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul,
    smul_eq_mul, hcc, one_mul]

end BlockBand.Coarea.FixedOmega
