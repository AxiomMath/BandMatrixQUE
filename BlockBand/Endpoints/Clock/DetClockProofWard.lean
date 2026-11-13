module

public import BlockBand.Endpoints.Clock.DetClockInjection
public import BlockBand.Internal.Contracts.LayersOnePort

/-!
# The deterministic-clock lemma: the sharper Ward mean

We prove the first display of the proof of the deterministic-clock lemma,
`E(U ∣ F) = -ωf(X) - ω̄f(X)* + O(δ₀² + W⁻²)`, `|ω| ≤ Cδ₀`, `U = LL* - I`.

## The weighted covariance

The weighted trace–matrix covariance is taken from `LayersOnePort.OnePortWeightedCovarianceContract`:
for Hermitian `X`, `g = W⁻¹Tr(P𝒢)`, `U = Q𝒢𝒦*`, `𝒦 = diag(z - X, 0)`, `‖Cov(g, U)‖_op ≤ CW⁻²`. We
use it at `P, Q ∈ {P_phys, P_port}` (`weightedCov_of`), for the three covariance terms
`(g_A, P_A𝒢)`, `(g_P, P_A𝒢)`, `(g_A, Q𝒢)` of the mean-equation residual
(`BlockBand.Layers.meqResid`), with the identifications `freshLayer = onePortResolvent` (`rfl`),
`meqPhysProj 0 = onePortPhysProj`, `meqPortProj 0 = onePortPortProj`,
`physBlockTrace 𝒢 0 = W⁻¹Tr(onePortPhysProj 𝒢)`, `portBlockTrace 𝒢 0 = W⁻¹Tr(onePortPortProj 𝒢)`,
and `R₁₁K* = (Res·𝒦*)₁₁` (`wardResid_mul`).

## Results (fixed `0 < b < 1/2`, `-2 < E < 2`, `z = z_∂(E)`, `η = Im z`)

* `ward_freshU`: one sample, almost surely: `LL* = (z̄ - z)⁻¹ K(𝒢₁₁ - 𝒢₁₁*)K*` (the matrix Ward
  identity `𝒢 - 𝒢* = 𝒢 diag(0, (z̄-z)I) 𝒢*`, top block).
* `wardMean_of`: from `GaussianAbsorptionContract` and `OnePortWeightedCovarianceContract`: there
  are `C, d > 0, W₀` such that for `W ≥ W₀` and every Hermitian `X` with `δ₀(X) ≤ d` there is
  `Ω ∈ ℂ` with `|Ω| ≤ C(δ₀ + W⁻²)` and `‖E(LL*) - I - Ωf - Ω̄f*‖ ≤ C(δ₀² + W⁻²)` (operator norm;
  `ω = -Ω`).
  Proof: Ward gives `E LL* = (z̄-z)⁻¹(Y - Y*)`, `Y = K E𝒢₁₁ K*`; the exact mean equation
  (`meanEquation_of_moments`) gives `(K - Ω)E𝒢₁₁ = I + R`, `Ω = c(ḡ_A - a) + b(ḡ_P - a)`
  (`c = 1-2b`); the cavity closeness (`condMeanTop_large`, `condMean_large`,
  `cavity_close_matched`) gives `|Ω| ≤ C(δ₀ + W⁻²)`; the weighted covariance bounds
  `‖RK*‖ ≤ CW⁻²`; then the exact algebra
  `Y = K* - (z-z̄)Ωf - (z-z̄)Ω²(K-Ω)⁻¹f + K(K-Ω)⁻¹RK*` (deterministic, `f = K⁻¹ - (z-z̄)⁻¹`).
  The domain `δ₀ ≤ d` makes `‖(K-Ω)⁻¹‖ ≤ 2/η`. No moment of `K` is used: off the domain the
  lemma does not use the Ward mean at all, so `OnePortOperatorMomentsContract` is not needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.LayersOnePort
open scoped Matrix.Norms.L2Operator ComplexConjugate

namespace DetClockProof

/-!
## 1. Entrywise expectations
-/

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m n : Type*}

theorem mE_apply (V : Ω → Matrix m n ℂ) (i : m) (j : n) :
    matrixExpect μ V i j = ∫ ω, V ω i j ∂μ := rfl

theorem mE_sub {V V' : Ω → Matrix m n ℂ} (hV : ∀ i j, Integrable (fun ω => V ω i j) μ)
    (hV' : ∀ i j, Integrable (fun ω => V' ω i j) μ) :
    matrixExpect μ (fun ω => V ω - V' ω) = matrixExpect μ V - matrixExpect μ V' := by
  ext i j
  simp only [mE_apply, Matrix.sub_apply]
  exact integral_sub (hV i j) (hV' i j)

theorem mE_smul (c : ℂ) (V : Ω → Matrix m n ℂ) :
    matrixExpect μ (fun ω => c • V ω) = c • matrixExpect μ V := by
  ext i j
  simp only [mE_apply, Matrix.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem mE_conjTranspose (V : Ω → Matrix m n ℂ) :
    matrixExpect μ (fun ω => (V ω)ᴴ) = (matrixExpect μ V)ᴴ := by
  ext i j
  simp only [mE_apply, conjTranspose_apply, RCLike.star_def]
  exact integral_conj

theorem mE_congr_ae {V V' : Ω → Matrix m n ℂ} (h : ∀ᵐ ω ∂μ, V ω = V' ω) :
    matrixExpect μ V = matrixExpect μ V' := by
  ext i j
  simp only [mE_apply]
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

theorem mE_const [IsProbabilityMeasure μ] (A : Matrix m n ℂ) :
    matrixExpect μ (fun _ => A) = A := by
  ext i j
  simp [mE_apply]

theorem mE_mul_mul [Fintype m] [Fintype n] {k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix k m ℂ) (B : Matrix n l ℂ)
    {V : Ω → Matrix m n ℂ} (hV : ∀ i j, Integrable (fun ω => V ω i j) μ) :
    matrixExpect μ (fun ω => A * V ω * B) = A * matrixExpect μ V * B := by
  ext x y
  simp only [mE_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun q _ => ?_]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_mul_const, integral_finsetSum _ fun p _ => (hV p q).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    exact integral_const_mul _ _
  · refine Integrable.mul_const ?_ _
    exact integrable_finsetSum _ fun p _ => (hV p q).const_mul _

end Expect

/-!
## 2. Norm of a selection of rows and columns
-/

section Select

variable {m n : Type*} [Fintype n] [DecidableEq n]

/-- The selection matrix of an injective map. -/
def selMat (f : m → n) : Matrix m n ℂ := Matrix.of fun i x => if x = f i then 1 else 0

theorem selMat_mul_conjTranspose [DecidableEq m] {f : m → n} (hf : Function.Injective f) :
    selMat f * (selMat f)ᴴ = 1 := by
  ext i j
  simp only [selMat, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (f j)]
  · by_cases h : i = j
    · subst h; simp
    · have : f j ≠ f i := fun h' => h (hf h').symm
      simp [this, h]
  · intro x _ hx; simp [hx]
  · simp

theorem norm_selMat_le [Fintype m] [DecidableEq m] {f : m → n} (hf : Function.Injective f) :
    ‖selMat f‖ ≤ 1 := by
  have h1 : ‖(selMat f)ᴴ‖ * ‖(selMat f)ᴴ‖ = ‖((selMat f)ᴴ)ᴴ * (selMat f)ᴴ‖ :=
    (l2_opNorm_conjTranspose_mul_self _).symm
  rw [conjTranspose_conjTranspose, selMat_mul_conjTranspose hf, l2_opNorm_conjTranspose] at h1
  have h2 := lct_norm_one_le (n := m)
  have h0 := norm_nonneg (selMat f)
  nlinarith

theorem submatrix_eq_sel {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]
    (M : Matrix n l ℂ) (f : m → n) (g : k → l) :
    M.submatrix f g = selMat f * M * (selMat g)ᴴ := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, selMat, conjTranspose_apply,
    Matrix.of_apply]
  simp [Finset.sum_ite_eq', ite_mul, mul_ite]

theorem norm_submatrix_le [Fintype m] [DecidableEq m] {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (M : Matrix n l ℂ) {f : m → n} (hf : Function.Injective f) {g : k → l}
    (hg : Function.Injective g) : ‖M.submatrix f g‖ ≤ ‖M‖ := by
  rw [submatrix_eq_sel]
  calc ‖selMat f * M * (selMat g)ᴴ‖ ≤ ‖selMat f * M‖ * ‖(selMat g)ᴴ‖ := l2_opNorm_mul _ _
    _ ≤ ‖selMat f‖ * ‖M‖ * ‖(selMat g)ᴴ‖ := by
        gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by
        rw [l2_opNorm_conjTranspose]
        gcongr
        · exact norm_selMat_le hf
        · exact norm_selMat_le hg
    _ = ‖M‖ := by ring

theorem norm_apply_le [Fintype m] [DecidableEq m] (M : Matrix m n ℂ) (i : m) (j : n) :
    ‖M i j‖ ≤ ‖M‖ := by
  have h := norm_submatrix_le M (f := fun _ : Unit => i) (fun _ _ _ => rfl)
    (g := fun _ : Unit => j) (fun _ _ _ => rfl)
  have h1 : ‖M.submatrix (fun _ : Unit => i) (fun _ : Unit => j)‖ = ‖M i j‖ := by
    have : M.submatrix (fun _ : Unit => i) (fun _ : Unit => j) = diagonal fun _ => M i j := by
      ext u v; simp [Subsingleton.elim u v]
    rw [this, l2_opNorm_diagonal]
    simp
  rw [h1] at h
  exact h

end Select

/-!
## 3. Shifted resolvents of a Hermitian matrix
-/

section Shift

variable {W : ℕ}

theorem isUnit_shift {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) {w : ℂ}
    (hw : 0 < w.im) : IsUnit (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X).det := by
  have h := cmp_det_ne_zero (-X) hX.neg (fun _ => -w) (fun _ => by simp; linarith)
  have he : -X - diagonal (fun _ : Fin W => -w) = w • (1 : Matrix (Fin W) (Fin W) ℂ) - X := by
    rw [← smul_one_eq_diagonal, neg_smul]; abel
  rw [he] at h
  exact isUnit_iff_ne_zero.mpr h

end Shift

/-!
## 4. The Ward identity of one sample (matrix form)
-/

section Ward

variable {W : ℕ}

/-- `𝒢₁₁` of one fresh layer, on `Fin W`. -/
def g11 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), y))

theorem entry_portWeight_mul
    (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) (c : ℂ)
    (i k : LayerSite W .oneBlockOnePort) :
    (G * DetClockInj.portWeight W c * Gᴴ) i k =
      c * ∑ y : PortSite W .oneBlockOnePort, G i (Sum.inr y) * star (G k (Sum.inr y)) := by
  simp only [DetClockInj.portWeight, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, conjTranspose_apply,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Matrix Ward identity of one sample**: `𝒢₁₂𝒢₁₂* = (z̄ - z)⁻¹(𝒢₁₁ - 𝒢₁₁*)`. -/
theorem g12_mul_conjTranspose (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (hz : boundaryZ b E ≠ conj (boundaryZ b E))
    (ω : OneEndedLayer W) (hA : ∀ j, (ω.1 j).IsHermitian)
    (hH : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    freshG12 b E X ω * (freshG12 b E X ω)ᴴ =
      (conj (boundaryZ b E) - boundaryZ b E)⁻¹ • (g11 b E X ω - (g11 b E X ω)ᴴ) := by
  set H := layerMatrix .oneBlockOnePort E (boundaryZ b E)
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω with hHdef
  have hXl : (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2).IsHermitian :=
    ClockMixingAlg.physEmbed_isHermitian hX
  have hW := DetClockInj.inv_sub_conjTranspose_inv H hH
  rw [DetClockInj.layerMatrix_conjTranspose_sub E _ hXl ω hA] at hW
  have hne : conj (boundaryZ b E) - boundaryZ b E ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  ext x y
  have he := congrFun (congrFun hW (Sum.inl ((0 : Fin 1), x))) (Sum.inl ((0 : Fin 1), y))
  rw [entry_portWeight_mul] at he
  have hG : freshLayer b E X ω = H⁻¹ := rfl
  simp only [Matrix.smul_apply, Matrix.sub_apply, conjTranspose_apply, smul_eq_mul, g11,
    Matrix.of_apply, hG]
  simp only [Matrix.sub_apply, conjTranspose_apply] at he
  rw [he, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_one]
  field_simp
  simp only [freshG12, conjTranspose_apply, Matrix.of_apply, hG]

/-- **Matrix Ward identity for `U = LL*`** (one sample, `L = K𝒢₁₂`):
`LL* = (z̄ - z)⁻¹ K(𝒢₁₁ - 𝒢₁₁*)K*`. -/
theorem ward_freshU (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (hz : boundaryZ b E ≠ conj (boundaryZ b E))
    (ω : OneEndedLayer W) (hA : ∀ j, (ω.1 j).IsHermitian)
    (hH : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    freshU b E X ω = (conj (boundaryZ b E) - boundaryZ b E)⁻¹ •
      ((boundaryZ b E • 1 - X) * (g11 b E X ω - (g11 b E X ω)ᴴ) *
        (boundaryZ b E • 1 - X)ᴴ) := by
  have hL : freshL b E X ω = (boundaryZ b E • 1 - X) * freshG12 b E X ω := rfl
  unfold freshU
  rw [hL, conjTranspose_mul, show (boundaryZ b E • 1 - X) * freshG12 b E X ω *
      ((freshG12 b E X ω)ᴴ * (boundaryZ b E • 1 - X)ᴴ) =
      (boundaryZ b E • 1 - X) * (freshG12 b E X ω * (freshG12 b E X ω)ᴴ) *
        (boundaryZ b E • 1 - X)ᴴ by simp only [Matrix.mul_assoc],
    g12_mul_conjTranspose b E hX hz ω hA hH, Matrix.mul_smul, Matrix.smul_mul]

end Ward

/-!
## 5. The deterministic algebra of the Ward mean
-/

section Algebra

variable {W : ℕ}

/-- **Exact algebra of the Ward mean**.
Let `X` be Hermitian,
`K = z - X`, `T = K - Ω` with `K, T` invertible, `ζ = z - z̄ ≠ 0`, `f = K⁻¹ - ζ⁻¹`, and
`T G = I + R`.
With `Y = K G K*` and `Err = -(ζΩ²)T⁻¹f + (I + ΩT⁻¹)RK*`:
`-ζ⁻¹(Y - Y*) - I - Ωf - Ω̄f* = -ζ⁻¹(Err - Err*)`.
(In the lemma `G = E𝒢₁₁`, so
`-ζ⁻¹(Y - Y*) = E LL*` by the Ward identity.)
-/
theorem ward_algebra {X K T f G R : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) {z Ω : ℂ}
    (hζ : z - conj z ≠ 0) (hKd : K = z • 1 - X) (hTd : T = (z - Ω) • 1 - X)
    (hfd : f = K⁻¹ - (z - conj z)⁻¹ • 1) (hK : IsUnit K.det) (hT : IsUnit T.det)
    (hG : T * G = 1 + R) :
    (-(z - conj z)⁻¹) • (K * G * Kᴴ - (K * G * Kᴴ)ᴴ) - 1 - Ω • f - conj Ω • fᴴ =
      (-(z - conj z)⁻¹) •
        ((-((z - conj z) * Ω ^ 2) • (T⁻¹ * f) + (1 + Ω • T⁻¹) * (R * Kᴴ)) -
          (-((z - conj z) * Ω ^ 2) • (T⁻¹ * f) + (1 + Ω • T⁻¹) * (R * Kᴴ))ᴴ) := by
  set ζ := z - conj z with hζdef
  have hKH : Kᴴ = K - ζ • 1 := by
    rw [hKd, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq, hζdef, sub_smul]
    simp only [RCLike.star_def]
    abel
  have hKT : K = T + Ω • 1 := by rw [hKd, hTd, sub_smul]; abel
  have hKK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hK
  have hTT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
  have hTT' : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hT
  have hGe : G = T⁻¹ * (1 + R) := by
    rw [← hG, ← Matrix.mul_assoc, hTT, Matrix.one_mul]
  have hTK : T * K⁻¹ = 1 - Ω • K⁻¹ := by
    have : T = K - Ω • 1 := by rw [hKT]; abel
    rw [this, Matrix.sub_mul, hKK, Matrix.smul_mul, Matrix.one_mul]
  have hζΩ : ζ * Ω * ζ⁻¹ = Ω := by field_simp
  have hS : Kᴴ + (ζ * Ω) • f = T * (1 - ζ • K⁻¹) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hTK, hKH, hfd, smul_sub, smul_smul,
      hζΩ, smul_sub, smul_smul]
    have : T = K - Ω • 1 := by rw [hKT]; abel
    rw [this]
    module
  have hKTS : K * T⁻¹ * (Kᴴ + (ζ * Ω) • f) = Kᴴ := by
    rw [hS, Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, hTT, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, Matrix.mul_smul, hKK, hKH]
  have hKT1 : K * T⁻¹ = 1 + Ω • T⁻¹ := by
    rw [hKT, Matrix.add_mul, hTT', Matrix.smul_mul, Matrix.one_mul]
  have h1 : K * T⁻¹ * Kᴴ = Kᴴ - (ζ * Ω) • (K * T⁻¹ * f) := by
    have := hKTS
    rw [Matrix.mul_add, Matrix.mul_smul] at this
    exact eq_sub_of_add_eq this
  set Err := -(ζ * Ω ^ 2) • (T⁻¹ * f) + (1 + Ω • T⁻¹) * (R * Kᴴ) with hErr
  have hY : K * G * Kᴴ = Kᴴ - (ζ * Ω) • f + Err := by
    have e1 : K * G * Kᴴ = K * T⁻¹ * Kᴴ + K * T⁻¹ * (R * Kᴴ) := by
      rw [hGe]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [e1, h1, hKT1, hErr, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, smul_add, smul_smul]
    rw [show ζ * Ω * Ω = ζ * Ω ^ 2 by ring]
    module
  have hstar : star (ζ * Ω) = -ζ * conj Ω := by
    rw [star_mul', hζdef]; simp only [RCLike.star_def, map_sub, Complex.conj_conj]; ring
  have hYH : (K * G * Kᴴ)ᴴ = K - (-ζ * conj Ω) • fᴴ + Errᴴ := by
    rw [hY, conjTranspose_add, conjTranspose_sub, conjTranspose_smul, conjTranspose_conjTranspose,
      hstar]
  rw [hYH, hY, hKH]
  have hz0 : ζ ≠ 0 := hζ
  match_scalars <;> field_simp <;> ring

end Algebra

/-!
## 6. The mean equation on the top block, and the weighted residual
-/

section MeanEq

variable {W : ℕ}

/-- `Fin W → Fin 1 × Fin W`, `x ↦ (0, x)`. -/
abbrev topE (W : ℕ) : Fin W ≃ Fin 1 × Fin W := (CavityMeanProb.liftEquiv W).symm

theorem cavityLift_submatrix (X : Matrix (Fin W) (Fin W) ℂ) :
    (cavityLift X).submatrix (topE W) (topE W) = X := by
  ext x y; rfl

/-- The top block of the mean equation, on `Fin W`:
`((-E - (c ḡ_A + b ḡ_P)) - X) Ḡ₁₁ = I + R₁₁`. -/
theorem meanEq_top_fin {E : ℝ} {z : ℂ} {X : Matrix (Fin W) (Fin W) ℂ} {c b : ℂ}
    {gA : Fin LayerShape.oneBlockOnePort.blocks → ℂ} {gP : Fin LayerShape.oneBlockOnePort.ports → ℂ}
    {Gbar R : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ}
    (h : (tflConst .oneBlockOnePort E z (cavityLift X) - meqShift .oneBlockOnePort c b gA gP) *
      Gbar = 1 + R) :
    ((-(E : ℂ) - (c * gA 0 + b * gP 0)) • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
        (Gbar.toBlocks₁₁.submatrix (topE W) (topE W)) =
      1 + R.toBlocks₁₁.submatrix (topE W) (topE W) := by
  have hb := (meq_blocks h).1
  rw [CavityMeanProb.meqTop_oneBlock, CavityMeanProb.meqTop_oneBlock_eq_shift] at hb
  have h2 := congrArg (fun M => M.submatrix (topE W) (topE W)) hb
  have e1 : (((-(E : ℂ) - (c * gA 0 + b * gP 0)) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) -
      cavityLift X).submatrix (topE W) (topE W)) =
      (-(E : ℂ) - (c * gA 0 + b * gP 0)) • (1 : Matrix (Fin W) (Fin W) ℂ) - X := by
    ext x y; simp [cavityLift, Matrix.one_apply]
  have e2 : (1 + R.toBlocks₁₁).submatrix (topE W) (topE W) =
      1 + R.toBlocks₁₁.submatrix (topE W) (topE W) := by
    ext x y; simp [Matrix.one_apply]
  rw [← submatrix_mul_equiv _ _ _ (topE W) _, e1, e2] at h2
  exact h2

theorem meqResid_oneBlock {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (c b : ℂ)
    (G : Ω → Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    meqResid ν c b G =
      c • meqCov ν (fun ω => physBlockTrace (G ω) 0) (fun ω => meqPhysProj 0 * G ω) +
        b • (meqCov ν (fun ω => portBlockTrace (G ω) 0) (fun ω => meqPhysProj 0 * G ω) +
          meqCov ν (fun ω => physBlockTrace (G ω) 0) (fun ω => meqPortProj 0 * G ω)) := by
  unfold meqResid
  simp [meqInc, LayerShape.incident]

theorem meqCov_mul {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (f : Ω → ℂ) {U : Ω → Matrix ι ι ℂ} (P : Matrix ι ι ℂ)
    (hU : ∀ i j, Integrable (fun ω => U ω i j) ν)
    (hfU : ∀ i j, Integrable (fun ω => f ω * U ω i j) ν) :
    meqCov ν f U * P = meqCov ν f (fun ω => U ω * P) := by
  unfold meqCov
  have h1 : matrixExpect ν (fun ω => f ω • U ω) * P = matrixExpect ν (fun ω => f ω • (U ω * P)) := by
    have := mE_mul_mul (μ := ν) (1 : Matrix ι ι ℂ) P (V := fun ω => f ω • U ω)
      (fun i j => by simpa [Matrix.smul_apply] using hfU i j)
    simp only [Matrix.one_mul] at this
    rw [← this]
    congr 1; funext ω; rw [Matrix.smul_mul]
  have h2 : matrixExpect ν U * P = matrixExpect ν (fun ω => U ω * P) := by
    have := mE_mul_mul (μ := ν) (1 : Matrix ι ι ℂ) P hU
    simp only [Matrix.one_mul] at this
    rw [this]
  rw [Matrix.sub_mul, h1, Matrix.smul_mul, h2]

end MeanEq

/-!
## 7. Identification with the one-port vocabulary (`LayersOnePort`)
-/

section Ident

variable {W : ℕ}

theorem freshLayer_eq_onePortResolvent (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : OneEndedLayer W) : freshLayer b E X ω = onePortResolvent b E X ω := rfl

theorem meqPhysProj_eq_onePort :
    (meqPhysProj 0 : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) =
      onePortPhysProj := by
  ext (p | p) (q | q) <;>
    simp [meqPhysProj, onePortPhysProj, Matrix.diagonal_apply, Matrix.one_apply,
      Subsingleton.elim p.1 0]

theorem meqPortProj_eq_onePort :
    (meqPortProj 0 : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) =
      onePortPortProj := by
  ext (p | p) (q | q) <;>
    simp [meqPortProj, onePortPortProj, Matrix.diagonal_apply, Matrix.one_apply,
      Subsingleton.elim p.1 0]

theorem physBlockTrace_eq_onePort
    (M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    physBlockTrace M 0 = (W : ℂ)⁻¹ * (onePortPhysProj * M).trace := by
  rw [meq_physBlockTrace_eq_word, ← meq_mul_eq_wordEval, meqPhysProj_eq_onePort]

theorem portBlockTrace_eq_onePort
    (M : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    portBlockTrace M 0 = (W : ℂ)⁻¹ * (onePortPortProj * M).trace := by
  rw [meq_portBlockTrace_eq_word, ← meq_mul_eq_wordEval, meqPortProj_eq_onePort]

/-- The three weighted covariance terms of the residual, from
`OnePortWeightedCovarianceContract` (at Hermitian `X`, `κ = 2 - |E|`).
-/
theorem weightedCov_of (hWC : OnePortWeightedCovarianceContract) {b E : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      X.IsHermitian →
      ‖meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
          (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤
        C / (W : ℝ) ^ 2 ∧
      ‖meqCov (freshLaw W b) (fun ω => portBlockTrace (freshLayer b E X ω) 0)
          (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤
        C / (W : ℝ) ^ 2 ∧
      ‖meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
          (fun ω => meqPortProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤
        C / (W : ℝ) ^ 2 := by
  have hκ : 0 < 2 - |E| := by
    have := abs_lt.mpr ⟨hE0, hE1⟩; linarith
  have hEb : E ∈ bulkInterval (2 - |E|) := by
    unfold bulkInterval
    constructor
    · have := neg_abs_le E; linarith
    · have := le_abs_self E; linarith
  obtain ⟨C, W₀, h⟩ := hWC b hb0 hb1 (2 - |E|) hκ
  refine ⟨C, W₀, fun W hW hWW X hX => ?_⟩
  have hPn : ‖(onePortPhysProj : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ)‖ ≤ 1 := by
    rw [← meqPhysProj_eq_onePort]; exact meq_norm_physProj_le 0
  have hQn : ‖(onePortPortProj : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ)‖ ≤ 1 := by
    rw [← meqPortProj_eq_onePort]; exact meq_norm_portProj_le 0
  have hgA : (fun ω => physBlockTrace (freshLayer b E X ω) 0) =
      fun ω => (W : ℂ)⁻¹ * (onePortPhysProj * onePortResolvent b E X ω).trace := by
    funext ω; rw [physBlockTrace_eq_onePort]; rfl
  have hgP : (fun ω => portBlockTrace (freshLayer b E X ω) 0) =
      fun ω => (W : ℂ)⁻¹ * (onePortPortProj * onePortResolvent b E X ω).trace := by
    funext ω; rw [portBlockTrace_eq_onePort]; rfl
  obtain ⟨-, -, -, h1⟩ := h W hW hWW X hX E hEb onePortPhysProj onePortPhysProj hPn hPn
  obtain ⟨-, -, -, h2⟩ := h W hW hWW X hX E hEb onePortPortProj onePortPhysProj hQn hPn
  obtain ⟨-, -, -, h3⟩ := h W hW hWW X hX E hEb onePortPhysProj onePortPortProj hPn hQn
  rw [hgA, hgP, meqPhysProj_eq_onePort, meqPortProj_eq_onePort]
  exact ⟨h1, h2, h3⟩

end Ident

/-!
## 8. The sharper Ward mean
-/

section Main

variable {W : ℕ}

/-- `x ≤ C(δ + w)`, `0 ≤ w ≤ 1` give `x² ≤ 2C²(δ² + w)`. -/
theorem sq_le_of_le_mul_add {C x δ w : ℝ} (hx : 0 ≤ x) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) (h : x ≤ C * (δ + w)) : x ^ 2 ≤ 2 * C ^ 2 * (δ ^ 2 + w) := by
  have h1 : x ^ 2 ≤ (C * (δ + w)) ^ 2 := pow_le_pow_left₀ hx h 2
  have hw2 : w ^ 2 ≤ w := by rw [sq]; exact mul_le_of_le_one_left hw0 hw1
  have h3 : (δ + w) ^ 2 ≤ 2 * δ ^ 2 + 2 * w ^ 2 := by nlinarith [sq_nonneg (δ - w)]
  have h4 : (C * (δ + w)) ^ 2 = C ^ 2 * (δ + w) ^ 2 := by ring
  have h5 : C ^ 2 * (δ + w) ^ 2 ≤ C ^ 2 * (2 * δ ^ 2 + 2 * w) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg C); linarith
  linarith

theorem integrable_g11_apply {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hGn : Integrable (fun ω => ‖freshLayer b E X ω‖) (freshLaw W b)) (x y : Fin W) :
    Integrable (fun ω => g11 b E X ω x y) (freshLaw W b) := by
  have hm : Measurable (fun ω => freshLayer b E X ω) := measurable_layerResolvent _ _ _ _
  refine Integrable.mono' hGn (ClockMixingProb.meas_entry hm _ _).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  exact norm_apply_le (freshLayer b E X ω) (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), y))

theorem integrable_g11H_apply {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hGn : Integrable (fun ω => ‖freshLayer b E X ω‖) (freshLaw W b)) (x y : Fin W) :
    Integrable (fun ω => (g11 b E X ω)ᴴ x y) (freshLaw W b) := by
  have hm : Measurable (fun ω => freshLayer b E X ω) := measurable_layerResolvent _ _ _ _
  refine Integrable.mono' hGn ((continuous_star.measurable).comp (ClockMixingProb.meas_entry hm
    (Sum.inl ((0 : Fin 1), y)) (Sum.inl ((0 : Fin 1), x)))).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  show ‖star (freshLayer b E X ω (Sum.inl ((0 : Fin 1), y)) (Sum.inl ((0 : Fin 1), x)))‖ ≤ _
  rw [norm_star]
  exact norm_apply_le (freshLayer b E X ω) (Sum.inl ((0 : Fin 1), y)) (Sum.inl ((0 : Fin 1), x))

/-- `Pw`-weighted residual entries: integrability of `(P 𝒢)_{ij}` and `g (P𝒢)_{ij}`. -/
theorem integrable_word_apply {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hGn : Integrable (fun ω => ‖freshLayer b E X ω‖) (freshLaw W b))
    (hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b))
    (P : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) (hP : ‖P‖ ≤ 1)
    (g : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ → ℂ)
    (hg : Continuous g) (hgn : ∀ M, ‖g M‖ ≤ ‖M‖) (i j : LayerSite W .oneBlockOnePort) :
    Integrable (fun ω => (P * freshLayer b E X ω) i j) (freshLaw W b) ∧
      Integrable (fun ω => g (freshLayer b E X ω) * (P * freshLayer b E X ω) i j)
        (freshLaw W b) := by
  have hm : Measurable (fun ω => freshLayer b E X ω) :=
    measurable_layerResolvent _ _ _ _
  have hent : ∀ ω, ‖(P * freshLayer b E X ω) i j‖ ≤ ‖freshLayer b E X ω‖ := by
    intro ω
    refine (norm_apply_le _ i j).trans ((l2_opNorm_mul _ _).trans ?_)
    calc ‖P‖ * ‖freshLayer b E X ω‖ ≤ 1 * ‖freshLayer b E X ω‖ := by gcongr
      _ = _ := one_mul _
  have hm1 : Measurable (fun ω => (P * freshLayer b E X ω) i j) :=
    ClockMixingProb.meas_entry (ClockMixingProb.meas_mul measurable_const hm) i j
  refine ⟨Integrable.mono' hGn hm1.aestronglyMeasurable (ae_of_all _ hent), ?_⟩
  refine Integrable.mono' hG2 ((hg.measurable.comp hm).mul hm1).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [norm_mul, sq]
  exact mul_le_mul (hgn _) (hent ω) (norm_nonneg _) (norm_nonneg _)

/-- `Ω = z + E + c ḡ_A + b ḡ_P` (`c = 1 - 2b`), the self-energy shift of the mean equation
(`T = (z - Ω) - X` is its top matrix). -/
def wardOmega (W : ℕ) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  boundaryZ b E + E + ((1 - 2 * (b : ℂ)) * meqMeanA (freshLaw W b) (freshLayer b E X) 0 +
    (b : ℂ) * meqMeanP (freshLaw W b) (freshLayer b E X) 0)

/-- `R₁₁` of the mean equation, on `Fin W`. -/
def wardResid (W : ℕ) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (meqResid (freshLaw W b) (1 - 2 * (b : ℂ)) b (freshLayer b E X)).toBlocks₁₁.submatrix
    (topE W) (topE W)

/-- `Ḡ₁₁` on `Fin W`. -/
def wardG11 (W : ℕ) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (matrixExpect (freshLaw W b) (freshLayer b E X)).toBlocks₁₁.submatrix (topE W) (topE W)

/-- The top mean equation `T Ḡ₁₁ = I + R₁₁`, `T = (z - Ω) - X`. -/
theorem ward_topEq {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) (hW : 0 < W) (hz : 0 ≤ (boundaryZ b E).im)
    (hinv : ∀ᵐ ω ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (cavityLift X) ω).det)
    (hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b)) :
    ((boundaryZ b E - wardOmega W b E X) • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
      wardG11 W b E X = 1 + wardResid W b E X := by
  have hmean := meanEquation_of_moments hW hb0 hb1 LayerShape.oneBlockOnePort
    (CavityMeanProb.cavityLift_isHermitian hX) E hz hinv hG2
  have h := meanEq_top_fin hmean
  have hs : boundaryZ b E - wardOmega W b E X =
      -(E : ℂ) - ((1 - 2 * (b : ℂ)) * meqMeanA (freshLaw W b) (freshLayer b E X) 0 +
        (b : ℂ) * meqMeanP (freshLaw W b) (freshLayer b E X) 0) := by
    unfold wardOmega; ring
  rw [hs]
  exact h

/-- The Ward identity in mean: `E(LL*) = -ζ⁻¹(Y - Y*)`, `Y = K Ḡ₁₁ K*`, `ζ = z - z̄`. -/
theorem ward_expect {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (hzc : boundaryZ b E ≠ conj (boundaryZ b E))
    (hinv : ∀ᵐ ω ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (cavityLift X) ω).det)
    (hGn : Integrable (fun ω => ‖freshLayer b E X ω‖) (freshLaw W b)) :
    matrixExpect (freshLaw W b) (freshU b E X) =
      (-(boundaryZ b E - conj (boundaryZ b E))⁻¹) •
        ((boundaryZ b E • 1 - X) * wardG11 W b E X * (boundaryZ b E • 1 - X)ᴴ -
          ((boundaryZ b E • 1 - X) * wardG11 W b E X * (boundaryZ b E • 1 - X)ᴴ)ᴴ) := by
  set z := boundaryZ b E
  set K := z • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have hint1 : ∀ x y, Integrable (fun ω => g11 b E X ω x y) (freshLaw W b) := fun x y =>
    integrable_g11_apply hGn x y
  have hint2 : ∀ x y, Integrable (fun ω => (g11 b E X ω)ᴴ x y) (freshLaw W b) := fun x y =>
    integrable_g11H_apply hGn x y
  have hg11i : ∀ x y, Integrable (fun ω => (g11 b E X ω - (g11 b E X ω)ᴴ) x y) (freshLaw W b) :=
    fun x y => (hint1 x y).sub (hint2 x y)
  have hae : ∀ᵐ ω ∂freshLaw W b, freshU b E X ω = (conj z - z)⁻¹ •
      (K * (g11 b E X ω - (g11 b E X ω)ᴴ) * Kᴴ) := by
    filter_upwards [lct_ae_blocks_isHermitian W b LayerShape.oneBlockOnePort, hinv] with ω hA hH
    exact ward_freshU b E hX hzc ω hA hH
  rw [mE_congr_ae hae, mE_smul, mE_mul_mul K Kᴴ hg11i, mE_sub hint1 hint2, mE_conjTranspose]
  have hG11 : matrixExpect (freshLaw W b) (g11 b E X) = wardG11 W b E X := by ext x y; rfl
  rw [hG11, show conj z - z = -(z - conj z) by ring, inv_neg]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_assoc K (wardG11 W b E X)ᴴ]

/-- `R₁₁K* = (Res·𝒦*)` restricted to the top block. -/
theorem wardResid_mul (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    wardResid W b E X * (boundaryZ b E • 1 - X)ᴴ =
      (meqResid (freshLaw W b) (1 - 2 * (b : ℂ)) b (freshLayer b E X) *
        (onePortWeight b E X)ᴴ).submatrix
        (Sum.inl ∘ topE W) (Sum.inl ∘ topE W) := by
  ext x y
  simp only [wardResid, Matrix.mul_apply, Matrix.submatrix_apply, Function.comp_apply, toBlocks₁₁,
    Matrix.of_apply, Fintype.sum_sum_type, onePortWeight, fromBlocks_conjTranspose,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type, Fin.sum_univ_one, onePortLift,
    conjTranspose_zero, conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  simp [Prod.ext_iff]

/-- The weighted residual bound from the three weighted covariances. -/
theorem wardResid_mul_le {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {X : Matrix (Fin W) (Fin W) ℂ}
    (hGn : Integrable (fun ω => ‖freshLayer b E X ω‖) (freshLaw W b))
    (hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b)) {B : ℝ}
    (hh1 : ‖meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
        (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤ B)
    (hh2 : ‖meqCov (freshLaw W b) (fun ω => portBlockTrace (freshLayer b E X ω) 0)
        (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤ B)
    (hh3 : ‖meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
        (fun ω => meqPortProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)‖ ≤ B) :
    ‖wardResid W b E X * (boundaryZ b E • 1 - X)ᴴ‖ ≤ 3 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hh1
  have hinj : Function.Injective (Sum.inl ∘ topE W : Fin W → LayerSite W .oneBlockOnePort) :=
    Sum.inl_injective.comp (topE W).injective
  have hwA := integrable_word_apply hGn hG2 (meqPhysProj 0) (meq_norm_physProj_le 0)
    (fun M => physBlockTrace M 0) (meq_continuous_physBlockTrace 0)
    (fun M => meq_norm_physBlockTrace_le M 0)
  have hwP := integrable_word_apply hGn hG2 (meqPhysProj 0) (meq_norm_physProj_le 0)
    (fun M => portBlockTrace M 0) (meq_continuous_portBlockTrace 0)
    (fun M => meq_norm_portBlockTrace_le M 0)
  have hwQ := integrable_word_apply hGn hG2 (meqPortProj 0) (meq_norm_portProj_le 0)
    (fun M => physBlockTrace M 0) (meq_continuous_physBlockTrace 0)
    (fun M => meq_norm_physBlockTrace_le M 0)
  rw [wardResid_mul]
  refine (norm_submatrix_le _ hinj hinj).trans ?_
  rw [meqResid_oneBlock, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.add_mul,
    meqCov_mul _ _ (fun i j => (hwA i j).1) (fun i j => (hwA i j).2),
    meqCov_mul _ _ (fun i j => (hwP i j).1) (fun i j => (hwP i j).2),
    meqCov_mul _ _ (fun i j => (hwQ i j).1) (fun i j => (hwQ i j).2)]
  have hcn : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
    rw [show (1 : ℂ) - 2 * (b : ℂ) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hbn : ‖(b : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; linarith
  refine (norm_add_le _ _).trans ?_
  have e1 := (norm_smul_le (1 - 2 * (b : ℂ)) (meqCov (freshLaw W b)
    (fun ω => physBlockTrace (freshLayer b E X ω) 0)
    (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)))
  have e2 := (norm_smul_le (b : ℂ) (meqCov (freshLaw W b)
    (fun ω => portBlockTrace (freshLayer b E X ω) 0)
    (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ) +
    meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
    (fun ω => meqPortProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ)))
  have e3 := norm_add_le (meqCov (freshLaw W b)
    (fun ω => portBlockTrace (freshLayer b E X ω) 0)
    (fun ω => meqPhysProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ))
    (meqCov (freshLaw W b) (fun ω => physBlockTrace (freshLayer b E X ω) 0)
    (fun ω => meqPortProj 0 * freshLayer b E X ω * (onePortWeight b E X)ᴴ))
  have f1 := mul_le_mul hcn hh1 (norm_nonneg _) zero_le_one
  have f2 := mul_le_mul hbn (e3.trans (add_le_add hh2 hh3)) (norm_nonneg _) zero_le_one
  linarith

/-- The scalar closeness `|Ω| ≤ C(δ₀ + W⁻²)` (cavity closeness, from `GaussianAbsorption`). -/
theorem wardOmega_le (hGA : GaussianAbsorptionContract) {b E : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 < C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      X.IsHermitian → ‖wardOmega W b E X‖ ≤ C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hc : 0 < 1 - 2 * b := by linarith
  have hη := DetClockInj.etaZ_pos (by linarith : b < 1) hE0 hE1
  obtain ⟨C₁, W₁, hC₁, htop⟩ := DetClockInj.condMeanTop_large hGA hb0 hb1
    (M := ‖boundaryZ b E‖) hη
  obtain ⟨C₃, W₃, hC₃, hport⟩ := CavityMeanProb.condMean_large hGA hb0 hb1
    (M := ‖boundaryZ b E‖) hη
  obtain ⟨C₂, hC₂, hclose⟩ := DetClockInj.cavity_close_matched hb0 hb1 hE0 hE1
  refine ⟨C₁ + C₃ + C₂, max W₁ W₃, by positivity, fun W hW0 hWW X hX => ?_⟩
  obtain ⟨vu, hsol, -⟩ := cavityMatrix_existsUnique hW0 hX hb0 hc (e := E) (z' := boundaryZ b E) hη
  have hv := htop W hW0 (le_trans (le_max_left _ _) hWW) X hX E (boundaryZ b E) vu.1 vu.2 le_rfl
    le_rfl hsol
  have hu0 := hport W hW0 (le_trans (le_max_right _ _) hWW) X hX E (boundaryZ b E) vu.1 vu.2 le_rfl
    le_rfl hsol
  have hu : ‖meqMeanP (freshLaw W b) (freshLayer b E X) 0 - vu.2‖ ≤ C₃ / (W : ℝ) ^ 2 := by
    have he : meqMeanP (freshLaw W b) (freshLayer b E X) 0 =
        ∫ ω, cavityHplus E X (boundaryZ b E) ω ∂layerLaw W b .oneBlockOnePort := by
      rw [meqMeanP]
      exact integral_congr_ae ((CavityMeanProb.ae_cavityHplus_eq_portBlockTrace hb1 E X
        (boundaryZ b E)).mono fun ω hω => hω.symm)
    rw [he]; exact hu0
  have hcl := hclose W hW0 X hX vu.1 vu.2 hsol
  set vbar := meqMeanA (freshLaw W b) (freshLayer b E X) 0
  set ubar := meqMeanP (freshLaw W b) (freshLayer b E X) 0
  have hv' : ‖vbar - vu.1‖ ≤ C₁ / (W : ℝ) ^ 2 := hv
  have hzeq : boundaryZ b E + E + ((1 - 2 * (b : ℂ)) * matchedA E + (b : ℂ) * matchedA E) = 0 := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; ring
  have hΩe : wardOmega W b E X = (1 - 2 * (b : ℂ)) * (vbar - matchedA E) +
      (b : ℂ) * (ubar - matchedA E) := by
    unfold wardOmega; linear_combination hzeq
  have hcn : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
    rw [show (1 : ℂ) - 2 * (b : ℂ) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]; linarith
  have hbn : ‖(b : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]; linarith
  have e1 : ‖vbar - matchedA E‖ ≤ C₁ / (W : ℝ) ^ 2 + ‖matchedA E - vu.1‖ := by
    calc ‖vbar - matchedA E‖ = ‖(vbar - vu.1) - (matchedA E - vu.1)‖ := by ring_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hv' le_rfl)
  have e2 : ‖ubar - matchedA E‖ ≤ C₃ / (W : ℝ) ^ 2 + ‖matchedA E - vu.2‖ := by
    calc ‖ubar - matchedA E‖ = ‖(ubar - vu.2) - (matchedA E - vu.2)‖ := by ring_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hu le_rfl)
  have f1 := mul_le_mul hcn e1 (norm_nonneg _) zero_le_one
  have f2 := mul_le_mul hbn e2 (norm_nonneg _) zero_le_one
  have hn : ‖wardOmega W b E X‖ ≤ ‖(1 - 2 * (b : ℂ))‖ * ‖vbar - matchedA E‖ +
      ‖(b : ℂ)‖ * ‖ubar - matchedA E‖ := by
    rw [hΩe]; refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
  have hWi : ((W : ℝ)⁻¹) ^ 2 = 1 / (W : ℝ) ^ 2 := by rw [inv_pow, one_div]
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hw0 : 0 ≤ 1 / (W : ℝ) ^ 2 := by positivity
  have e3 : C₁ / (W : ℝ) ^ 2 + C₃ / (W : ℝ) ^ 2 = (C₁ + C₃) * (1 / (W : ℝ) ^ 2) := by ring
  have e4 : (C₁ + C₃ + C₂) * (jetDistance0 b E X + 1 / (W : ℝ) ^ 2) =
      (C₁ + C₃) * (1 / (W : ℝ) ^ 2) + C₂ * jetDistance0 b E X +
        ((C₁ + C₃) * jetDistance0 b E X + C₂ * (1 / (W : ℝ) ^ 2)) := by ring
  have e5 : 0 ≤ (C₁ + C₃) * jetDistance0 b E X + C₂ * (1 / (W : ℝ) ^ 2) := by positivity
  rw [hWi]
  linarith

/-- **The sharper Ward mean**. Fixed `0 < b < 1/2`, `-2 < E < 2`. From
`GaussianAbsorptionContract` and `OnePortWeightedCovarianceContract`: there are `C`, `d > 0` and
`W₀` such that for every `W ≥ W₀` and every Hermitian `X` with `δ₀(X) ≤ d` there is `Ω ∈ ℂ` with `|Ω| ≤ C(δ₀ + W⁻²)` and
`‖E(LL*) - I - Ωf - Ω̄f*‖ ≤ C(δ₀² + W⁻²)` (operator norm; one fresh layer `ω ~ freshLaw W b`,
`f = passiveF b E X`, `δ₀ = jetDistance0 b E X`).
-/
theorem wardMean_of (hGA : GaussianAbsorptionContract) (hWC : OnePortWeightedCovarianceContract)
    {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ (C d : ℝ) (W₀ : ℕ), 0 < d ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      X.IsHermitian → jetDistance0 b E X ≤ d →
        ∃ Ω : ℂ, ‖Ω‖ ≤ C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) ∧
          ‖matrixExpect (freshLaw W b) (freshU b E X) - 1 - Ω • passiveF b E X -
              conj Ω • (passiveF b E X)ᴴ‖ ≤
            C * (jetDistance0 b E X ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by
  have hη := DetClockInj.etaZ_pos (by linarith : b < 1) hE0 hE1
  set z := boundaryZ b E with hzdef
  set η := etaZ b E with hηdef
  have hzim : z.im = η := rfl
  have hzc : z ≠ conj z := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hζ : z - conj z ≠ 0 := sub_ne_zero.mpr hzc
  have hζn : ‖z - conj z‖ = 2 * η := by
    have : z - conj z = ((2 * η : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hzim]; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  obtain ⟨CΩ, WΩ, hCΩ0, hΩle⟩ := wardOmega_le hGA hb0 hb1 hE0 hE1
  obtain ⟨ε₁, CA, hε₁, _hCA, habs'⟩ := hGA b hb0 hb1 η ‖z‖ hη
  obtain ⟨Ch, Wh, hhyp⟩ := weightedCov_of hWC hb0 hb1 hE0 hE1
  set Kf := η⁻¹ + ‖cZero b E‖ with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  set CR := 3 * max Ch 0 with hCR
  have hCR0 : 0 ≤ CR := by positivity
  set d := η / (4 * CΩ) with hd
  have hd0 : 0 < d := by positivity
  set Cout := (8 * Kf * CΩ ^ 2 + 2 * CR) / η + CΩ with hCout
  have hCoutΩ : CΩ ≤ Cout := by
    have : 0 ≤ (8 * Kf * CΩ ^ 2 + 2 * CR) / η := by positivity
    linarith
  set Wd : ℕ := ⌈Real.sqrt (4 * CΩ / η)⌉₊ with hWd
  refine ⟨Cout, d, max (max WΩ (max ⌈2 / ε₁⌉₊ Wh)) (max Wd 1), hd0,
    fun W hWW X hX hδ => ?_⟩
  have hWΩ : WΩ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hWW
  have hWε : ⌈2 / ε₁⌉₊ ≤ W := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWh : Wh ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hWW
  have hWdW : Wd ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hWW
  have hW0 : 0 < W := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hWW))
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  have h2W : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWε)
    rw [div_le_iff₀ hε₁] at h1; linarith
  set w := ((W : ℝ)⁻¹) ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw, inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hW1r)
  have hWinv2 : CΩ * w ≤ η / 4 := by
    have hs : Real.sqrt (4 * CΩ / η) ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWdW)
    have hsq : 4 * CΩ / η ≤ (W : ℝ) ^ 2 := by
      have e := Real.sq_sqrt (show 0 ≤ 4 * CΩ / η by positivity)
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
      linarith
    rw [div_le_iff₀ hη] at hsq
    rw [hw, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  -- the layer
  have hXl := CavityMeanProb.cavityLift_isHermitian hX
  obtain ⟨hinv, hmom⟩ := habs' W hW0 LayerShape.oneBlockOnePort (cavityLift X) hXl E z le_rfl le_rfl
  have hG2 : Integrable (fun ω => ‖freshLayer b E X ω‖ ^ 2) (freshLaw W b) :=
    meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) h2W)
  have hGm : Measurable (fun ω => freshLayer b E X ω) := measurable_layerResolvent _ _ _ _
  have hGn : Integrable (fun ω => ‖freshLayer b E X ω‖) (freshLaw W b) :=
    meq_integrable_norm_of_sq hGm.aestronglyMeasurable hG2
  set Ω := wardOmega W b E X with hΩdef
  set δ₀ := jetDistance0 b E X with hδ₀
  have hδ0 : 0 ≤ δ₀ := norm_nonneg _
  have hΩb : ‖Ω‖ ≤ CΩ * (δ₀ + w) := hΩle W hW0 hWΩ X hX
  refine ⟨Ω, hΩb.trans (mul_le_mul_of_nonneg_right hCoutΩ (by positivity)), ?_⟩
  have hΩs : ‖Ω‖ ≤ η / 2 := by
    have : CΩ * δ₀ ≤ η / 4 := by
      calc CΩ * δ₀ ≤ CΩ * d := mul_le_mul_of_nonneg_left hδ hCΩ0.le
        _ = η / 4 := by rw [hd]; field_simp
    have := mul_add CΩ δ₀ w
    linarith
  set K := z • (1 : Matrix (Fin W) (Fin W) ℂ) - X with hKdef
  set T := (z - Ω) • (1 : Matrix (Fin W) (Fin W) ℂ) - X with hTdef
  have hTim : η / 2 ≤ (z - Ω).im := by
    rw [Complex.sub_im, hzim]
    have := abs_le.mp ((Complex.abs_im_le_norm Ω).trans hΩs)
    linarith
  have hTim0 : 0 < (z - Ω).im := by linarith
  have hT : IsUnit T.det := isUnit_shift hX hTim0
  have hK : IsUnit K.det := isUnit_shift hX (by rw [hzim]; exact hη)
  have hTn : ‖T⁻¹‖ ≤ 2 / η := by
    refine (ClockMixingAlg.norm_resolvent_le hTim0 hX).trans ?_
    rw [show 2 / η = (η / 2)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) hTim
  have hfeq : passiveF b E X = K⁻¹ - (z - conj z)⁻¹ • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    rw [passiveF, passiveResolvent, ClockMixingAlg.cZero_eq]
  have hfn : ‖passiveF b E X‖ ≤ Kf :=
    ClockMixingAlg.norm_passiveF_le b E (by rw [hzim]; exact hη) hX
  have hTG : T * wardG11 W b E X = 1 + wardResid W b E X :=
    ward_topEq hb0.le hb1.le E hX hW0 (le_trans hη.le (le_of_eq hzim.symm)) hinv hG2
  have halg := ward_algebra hX (Ω := Ω) hζ hKdef hTdef hfeq hK hT hTG
  rw [ward_expect hX hzc hinv hGn, halg]
  -- the weighted residual
  obtain ⟨hh1, hh2, hh3⟩ := hhyp W hW0 hWh X hX
  have hCh0 : Ch / (W : ℝ) ^ 2 ≤ max Ch 0 * w := by
    rw [hw, inv_pow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hRn : ‖wardResid W b E X * Kᴴ‖ ≤ CR * w := by
    have := wardResid_mul_le hb0 hb1 hGn hG2 (hh1.trans hCh0) (hh2.trans hCh0) (hh3.trans hCh0)
    rw [hCR]; linarith
  set f := passiveF b E X with hfdef
  set Err := -((z - conj z) * Ω ^ 2) • (T⁻¹ * f) + (1 + Ω • T⁻¹) * (wardResid W b E X * Kᴴ)
    with hErr
  have hErrn : ‖Err‖ ≤ 4 * Kf * ‖Ω‖ ^ 2 + 2 * (CR * w) := by
    have e1 : ‖-((z - conj z) * Ω ^ 2) • (T⁻¹ * f)‖ ≤ 4 * Kf * ‖Ω‖ ^ 2 := by
      refine (norm_smul_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_pow, hζn]
      have h1 : ‖T⁻¹ * f‖ ≤ 2 / η * Kf :=
        (l2_opNorm_mul _ _).trans (mul_le_mul hTn hfn (norm_nonneg _) (by positivity))
      calc 2 * η * ‖Ω‖ ^ 2 * ‖T⁻¹ * f‖ ≤ 2 * η * ‖Ω‖ ^ 2 * (2 / η * Kf) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * Kf * ‖Ω‖ ^ 2 := by field_simp; ring
    have e2 : ‖(1 : Matrix (Fin W) (Fin W) ℂ) + Ω • T⁻¹‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      have h1 := lct_norm_one_le (n := Fin W)
      have h2 : ‖Ω • T⁻¹‖ ≤ 1 := by
        refine (norm_smul_le _ _).trans ?_
        calc ‖Ω‖ * ‖T⁻¹‖ ≤ (η / 2) * (2 / η) := mul_le_mul hΩs hTn (norm_nonneg _) (by positivity)
          _ = 1 := by field_simp
      linarith
    have e3 : ‖(1 + Ω • T⁻¹) * (wardResid W b E X * Kᴴ)‖ ≤ 2 * (CR * w) :=
      (l2_opNorm_mul _ _).trans (mul_le_mul e2 hRn (norm_nonneg _) (by norm_num))
    exact (norm_add_le _ _).trans (add_le_add e1 e3)
  have hfin : ‖(-(z - conj z)⁻¹) • (Err - Errᴴ)‖ ≤ ‖Err‖ / η := by
    refine (norm_smul_le _ _).trans ?_
    rw [norm_neg, norm_inv, hζn]
    have : ‖Err - Errᴴ‖ ≤ 2 * ‖Err‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [l2_opNorm_conjTranspose]; linarith
    calc (2 * η)⁻¹ * ‖Err - Errᴴ‖ ≤ (2 * η)⁻¹ * (2 * ‖Err‖) := by gcongr
      _ = ‖Err‖ / η := by field_simp
  refine hfin.trans ?_
  have hΩ2 : ‖Ω‖ ^ 2 ≤ 2 * CΩ ^ 2 * (δ₀ ^ 2 + w) :=
    sq_le_of_le_mul_add (norm_nonneg _) hw0 hw1 hΩb
  rw [div_le_iff₀ hη]
  have g1 : 4 * Kf * ‖Ω‖ ^ 2 ≤ 4 * Kf * (2 * CΩ ^ 2 * (δ₀ ^ 2 + w)) :=
    mul_le_mul_of_nonneg_left hΩ2 (by positivity)
  have g2 : 2 * (CR * w) ≤ 2 * (CR * (δ₀ ^ 2 + w)) := by
    have : w ≤ δ₀ ^ 2 + w := by nlinarith [sq_nonneg δ₀]
    have := mul_le_mul_of_nonneg_left this hCR0
    linarith
  have g3 : 4 * Kf * (2 * CΩ ^ 2 * (δ₀ ^ 2 + w)) + 2 * (CR * (δ₀ ^ 2 + w)) =
      (8 * Kf * CΩ ^ 2 + 2 * CR) / η * (δ₀ ^ 2 + w) * η := by
    field_simp; ring
  have g4 : (8 * Kf * CΩ ^ 2 + 2 * CR) / η * (δ₀ ^ 2 + w) * η ≤ Cout * (δ₀ ^ 2 + w) * η := by
    have h1 : (8 * Kf * CΩ ^ 2 + 2 * CR) / η ≤ Cout := by rw [hCout]; linarith
    have h2 : 0 ≤ (δ₀ ^ 2 + w) * η := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    calc (8 * Kf * CΩ ^ 2 + 2 * CR) / η * (δ₀ ^ 2 + w) * η
        = (8 * Kf * CΩ ^ 2 + 2 * CR) / η * ((δ₀ ^ 2 + w) * η) := by ring
      _ ≤ Cout * ((δ₀ ^ 2 + w) * η) := h3
      _ = Cout * (δ₀ ^ 2 + w) * η := by ring
  linarith

end Main

end DetClockProof

end BlockBand.Endpoints.Clock
