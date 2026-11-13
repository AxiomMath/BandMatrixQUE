module

public import BlockBand.Native.ErdosRiabov.Stochastic.OURing

set_option autoImplicit false

/-!
# Linear structure of the ring coordinates and the matrix OU flow

Setting: `p : BlockBand.Parameters`, the real coordinates `ringCoords : SiteMatrix → ℝ^d` and
`ringMatrix : ℝ^d → SiteMatrix` (`d = ringDim p`), and the ring OU flow
`ringOU`, `ringOUMatrix` on the driver space `RingSample p`.

* `ringMatrixLinear`, `ringMatrixCLM`: `ringMatrix` is a real-linear (continuous) map;
  `ringCoordsLinear`: `ringCoords` is real-linear.
* `IsRingRedundant p i`: the label of `i` is a redundant label `.inr (x, z, b)` outside the
  strict upper triangle (`¬ siteIndex x < siteIndex z`); `ringCoords` and `ringVariance` vanish
  there (`ringCoords_of_isRingRedundant`, `ringVariance_of_isRingRedundant`).
* `ringCoords_ringMatrix`: `ringCoords (ringMatrix y) = y` whenever the redundant coordinates of
  `y` vanish; together with `ringMatrix_ringCoords` (Hermitian `H`), `ringCoords`
  and `ringMatrix` are inverse real-linear bijections between Hermitian matrices and the
  subspace `{y : y_i = 0 for redundant i}`.
* `ringOU_of_isRingRedundant`: the flow stays in that subspace for **every** sample and time;
  hence `ringCoords_ringOUMatrix : ringCoords (ringOUMatrix p t x) = ringOU p t x`.
* `ringOUMatrix_eq_mehler` (matrix-level flow): for every sample with Hermitian initial state,
  `H_t = e^{-t/2} H_0 + ringMatrix(Y_t - Y_0) - ½ e^{-t/2} ringMatrix(∫_0^t e^{s/2}(Y_s - Y_0) ds)`,
  `Y = driverNoise ringVariance = diag(√v) B` (pathwise Mehler form at matrix level; the vector
  form is `ringOU_eq_mehler`).

No new probabilistic input: everything is deterministic algebra.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Stochastic
open MeasureTheory Set
open scoped NNReal Matrix

variable (p : BlockBand.Parameters)

/-!
### Linearity
-/

theorem ringMatrix_add (y z : Fin (ringDim p) → ℝ) :
    ringMatrix p (y + z) = ringMatrix p y + ringMatrix p z := by
  ext a b
  simp only [ringMatrix, BlockBand.Parameters.gaussianReconstruction, Pi.add_apply,
    Matrix.add_apply]
  split_ifs <;> push_cast <;> ring

theorem ringMatrix_smul (c : ℝ) (y : Fin (ringDim p) → ℝ) :
    ringMatrix p (c • y) = c • ringMatrix p y := by
  ext a b
  simp only [ringMatrix, BlockBand.Parameters.gaussianReconstruction, Pi.smul_apply,
    smul_eq_mul, Matrix.smul_apply, Complex.real_smul]
  split_ifs <;> push_cast <;> ring

/-- `ringMatrix` as a real-linear map `ℝ^d → SiteMatrix`. -/
def ringMatrixLinear : (Fin (ringDim p) → ℝ) →ₗ[ℝ] p.SiteMatrix where
  toFun := ringMatrix p
  map_add' := ringMatrix_add p
  map_smul' := ringMatrix_smul p

theorem ringMatrixLinear_apply (y : Fin (ringDim p) → ℝ) :
    ringMatrixLinear p y = ringMatrix p y := rfl

/-- `ringMatrix` as a continuous real-linear map `ℝ^d → SiteMatrix` (for chain rules). -/
def ringMatrixCLM : (Fin (ringDim p) → ℝ) →L[ℝ] p.SiteMatrix :=
  { ringMatrixLinear p with cont := LinearMap.continuous_of_finiteDimensional _ }

theorem ringMatrixCLM_apply (y : Fin (ringDim p) → ℝ) : ringMatrixCLM p y = ringMatrix p y :=
  rfl

theorem continuous_ringMatrix : Continuous (ringMatrix p) := (ringMatrixCLM p).continuous

theorem ringMatrix_sub (y z : Fin (ringDim p) → ℝ) :
    ringMatrix p (y - z) = ringMatrix p y - ringMatrix p z :=
  map_sub (ringMatrixLinear p) y z

theorem ringMatrix_zero : ringMatrix p 0 = 0 := map_zero (ringMatrixLinear p)

theorem ringCoords_add (H K : p.SiteMatrix) :
    ringCoords p (H + K) = ringCoords p H + ringCoords p K := by
  funext i
  simp only [ringCoords, Pi.add_apply]
  rcases (ringEquiv p).symm i with x | ⟨x, z, b⟩
  · simp [BlockBand.Parameters.gaussianExtraction]
  · cases b <;> by_cases h : p.siteIndex x < p.siteIndex z <;>
      simp [BlockBand.Parameters.gaussianExtraction, h]

theorem ringCoords_smul (c : ℝ) (H : p.SiteMatrix) :
    ringCoords p (c • H) = c • ringCoords p H := by
  funext i
  simp only [ringCoords, Pi.smul_apply, smul_eq_mul]
  rcases (ringEquiv p).symm i with x | ⟨x, z, b⟩
  · simp [BlockBand.Parameters.gaussianExtraction]
  · cases b <;> by_cases h : p.siteIndex x < p.siteIndex z <;>
      simp [BlockBand.Parameters.gaussianExtraction, h]

/-- `ringCoords` as a real-linear map `SiteMatrix → ℝ^d`. -/
def ringCoordsLinear : p.SiteMatrix →ₗ[ℝ] (Fin (ringDim p) → ℝ) where
  toFun := ringCoords p
  map_add' := ringCoords_add p
  map_smul' := ringCoords_smul p

theorem ringCoordsLinear_apply (H : p.SiteMatrix) : ringCoordsLinear p H = ringCoords p H :=
  rfl

/-!
### Redundant coordinates and the inverse identity
-/

/-- Coordinate `i` carries a redundant label `.inr (x, z, b)` with `¬ siteIndex x < siteIndex z`
(outside the strict upper triangle); `gaussianExtraction` is identically `0` there. -/
def IsRingRedundant (i : Fin (ringDim p)) : Prop :=
  ∃ x z : p.Site, ∃ b : Bool,
    (ringEquiv p).symm i = .inr (x, z, b) ∧ ¬ p.siteIndex x < p.siteIndex z

variable {p}

theorem ringCoords_of_isRingRedundant {i : Fin (ringDim p)} (hi : IsRingRedundant p i)
    (H : p.SiteMatrix) : ringCoords p H i = 0 := by
  obtain ⟨x, z, b, he, hlt⟩ := hi
  simp [ringCoords, he, BlockBand.Parameters.gaussianExtraction, hlt]

theorem ringVariance_of_isRingRedundant {i : Fin (ringDim p)} (hi : IsRingRedundant p i) :
    ringVariance p i = 0 := by
  obtain ⟨x, z, b, he, hlt⟩ := hi
  simp [ringVariance, he, BlockBand.Parameters.gaussianCoordinateVariance, hlt]

/-- **Inverse identity on the non-redundant subspace.** If the redundant coordinates of `y`
vanish, then `ringCoords (ringMatrix y) = y`. -/
theorem ringCoords_ringMatrix {y : Fin (ringDim p) → ℝ}
    (hy : ∀ i, IsRingRedundant p i → y i = 0) : ringCoords p (ringMatrix p y) = y := by
  funext i
  simp only [ringCoords, ringMatrix]
  obtain ⟨g, hg⟩ : ∃ g, (ringEquiv p).symm i = g := ⟨_, rfl⟩
  have hi : i = ringEquiv p g := by rw [← hg, Equiv.apply_symm_apply]
  rw [hg]
  rcases g with x | ⟨x, z, b⟩
  · simp [BlockBand.Parameters.gaussianExtraction, BlockBand.Parameters.gaussianReconstruction,
      hi]
  · by_cases hlt : p.siteIndex x < p.siteIndex z
    · have hxz : x ≠ z := fun h => by subst h; exact lt_irrefl _ hlt
      cases b <;> simp [BlockBand.Parameters.gaussianExtraction,
        BlockBand.Parameters.gaussianReconstruction, hlt, hxz, hi]
    · rw [hy i ⟨x, z, b, hg, hlt⟩]
      simp [BlockBand.Parameters.gaussianExtraction, hlt]

/-- The redundant coordinates of the ring OU flow vanish for every sample and time. -/
theorem ringOU_of_isRingRedundant {i : Fin (ringDim p)} (hi : IsRingRedundant p i)
    (t : ℝ≥0) (x : RingSample p) : ringOU p t x i = 0 := by
  rw [ringOU_apply, ringCoords_of_isRingRedundant hi, ringVariance_of_isRingRedundant hi]
  simp

/-- **The flow in coordinates is the coordinate vector of the matrix flow**, for every sample
and time: `ringCoords (ringOUMatrix p t x) = ringOU p t x`. -/
theorem ringCoords_ringOUMatrix (t : ℝ≥0) (x : RingSample p) :
    ringCoords p (ringOUMatrix p t x) = ringOU p t x :=
  ringCoords_ringMatrix fun _ hi => ringOU_of_isRingRedundant hi t x

/-!
### The matrix-level Mehler form
-/

variable (p)

/-- **Vector Mehler form** of the ring OU flow, with `Y = driverNoise ringVariance`:
`X_t = e^{-t/2} c(H_0) + (Y_t - Y_0) - ½ e^{-t/2} ∫_0^t e^{s/2} (Y_s - Y_0) ds`. -/
theorem ringOU_eq_mehler (t : ℝ≥0) (x : RingSample p) :
    ringOU p t x = Real.exp (-(t : ℝ) / 2) • ringCoords p x.1 +
      (driverNoise (ringVariance p) t x - driverNoise (ringVariance p) 0 x) -
      (1 / 2 * Real.exp (-(t : ℝ) / 2)) • ∫ s in (0 : ℝ)..t, Real.exp (s / 2) •
        (driverNoise (ringVariance p) s.toNNReal x - driverNoise (ringVariance p) 0 x) := by
  have hc : Continuous fun s : ℝ => Real.exp (s / 2) •
      (driverNoise (ringVariance p) s.toNNReal x - driverNoise (ringVariance p) 0 x) := by
    refine (Real.continuous_exp.comp (continuous_id.div_const 2)).smul ?_
    refine continuous_pi fun j => ?_
    simp only [driverNoise, Pi.sub_apply]
    exact (continuous_const.mul ((x.2 j).continuous.comp continuous_real_toNNReal)).sub
      continuous_const
  funext i
  have hI : (∫ s in (0 : ℝ)..t, Real.exp (s / 2) •
      (driverNoise (ringVariance p) s.toNNReal x - driverNoise (ringVariance p) 0 x)) i =
      ∫ s in (0 : ℝ)..t, (Real.exp (s / 2) •
        (driverNoise (ringVariance p) s.toNNReal x - driverNoise (ringVariance p) 0 x)) i :=
    ((ContinuousLinearMap.proj (R := ℝ) i).intervalIntegral_comp_comm
      (hc.intervalIntegrable 0 t)).symm
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hI, ringOU_apply]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, driverNoise, mul_sub]

/-- **Matrix-level Mehler form of the ring OU flow.** For every sample whose initial state
`H_0 = x.1`
is Hermitian (a.s. under the physical law), with `Y = driverNoise ringVariance = diag(√v) B`:
`H_t = e^{-t/2} H_0 + ringMatrix(Y_t - Y_0) - ½ e^{-t/2} ringMatrix(∫_0^t e^{s/2}(Y_s - Y_0) ds)`,
i.e. `H_t = e^{-t/2} (H_0 + ∫_0^t e^{s/2} dW_s)` with `W = ringMatrix(Y - Y_0)` written without
a stochastic integral. -/
theorem ringOUMatrix_eq_mehler (t : ℝ≥0) {x : RingSample p} (hx : x.1.IsHermitian) :
    ringOUMatrix p t x = Real.exp (-(t : ℝ) / 2) • x.1 +
      ringMatrix p (driverNoise (ringVariance p) t x - driverNoise (ringVariance p) 0 x) -
      (1 / 2 * Real.exp (-(t : ℝ) / 2)) • ringMatrix p (∫ s in (0 : ℝ)..t, Real.exp (s / 2) •
        (driverNoise (ringVariance p) s.toNNReal x - driverNoise (ringVariance p) 0 x)) := by
  rw [ringOUMatrix, ringOU_eq_mehler, ringMatrix_sub, ringMatrix_add, ringMatrix_smul,
    ringMatrix_smul, ringMatrix_ringCoords p hx]

end BlockBand.Native.ErdosRiabov.Stochastic
