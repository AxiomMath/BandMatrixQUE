module

public import BlockBand.Transmission.Bridge.TransportStep

/-!
# Transport of the current and of the old tags: `J_{j+1} = Nᴴ J_j N`, `Y_{j+1;k} = Nᴴ Y_{j;k} N`

Proof of `pathCurrent_succ`: with `Q = 1 - P`, unitarity gives `J = Q - (Q𝕊)ᴴ(Q𝕊)`, and
`QN = Q`, `Q𝕊_{j+1} = Q𝕊_jN` (from `boundaryToInterior_succ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix ComplexOrder

variable {W : ℕ}

theorem nearProjection_conjTranspose : (nearProjection W)ᴴ = nearProjection W := by
  rw [nearProjection, Matrix.diagonal_conjTranspose]
  congr 1; funext x; by_cases h : x.1 = 0 <;> simp [h]

theorem farProjection_sq :
    (1 - nearProjection W)ᴴ * (1 - nearProjection W) = 1 - nearProjection W := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, nearProjection_conjTranspose]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, nearProjection_mul_self]
  abel

/-- `J = 𝕊ᴴP𝕊 - P = Q - (Q𝕊)ᴴ(Q𝕊)` for unitary `𝕊`, `Q = 1 - P`. -/
theorem current_eq_far (T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hT : Tᴴ * T = 1) :
    Tᴴ * nearProjection W * T - nearProjection W =
      (1 - nearProjection W) - ((1 - nearProjection W) * T)ᴴ * ((1 - nearProjection W) * T) := by
  have h1 : ((1 - nearProjection W) * T)ᴴ * ((1 - nearProjection W) * T) =
      Tᴴ * T - Tᴴ * nearProjection W * T := by
    calc ((1 - nearProjection W) * T)ᴴ * ((1 - nearProjection W) * T)
        = Tᴴ * ((1 - nearProjection W)ᴴ * (1 - nearProjection W)) * T := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Tᴴ * T - Tᴴ * nearProjection W * T := by
          rw [farProjection_sq]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [h1, hT]
  abel

theorem farProjection_mul_freshTransport (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω' : LayerSample W .oneBlockOnePort) :
    (1 - nearProjection W) * freshTransport b E XX ω' = 1 - nearProjection W := by
  ext ⟨i, x⟩ ⟨k, y⟩
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.sub_mul, nearProjection, Matrix.diagonal_mul, Matrix.diagonal_apply,
      freshTransport, Matrix.one_apply]

theorem nearProjection_mul_nearSel : nearProjection W * (nearSel W)ᴴ = (nearSel W)ᴴ := by
  ext ⟨i, x⟩ y
  fin_cases i <;> simp [nearProjection, nearSel, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

theorem nearProjection_mul_farCoupling (j : ℕ) (ω : GrowthPath W) :
    nearProjection W * (farCoupling W j ω)ᴴ = 0 := by
  ext ⟨i, x⟩ p
  fin_cases i <;> simp [nearProjection, farCoupling, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

/-- **Current conservation along the growth step**: for `j ≥ 1`, `J_{j+1} = Nᴴ J_j N` with
`N = transportN b E W j ω`. Hypotheses as in `boundaryToInterior_succ`. -/
theorem pathCurrent_succ (b E : ℝ) {j : ℕ} (hj : 1 ≤ j) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1))
    (hG : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => pathX b E W j ω u.2 v.2) (freshSample W j ω))) :
    pathCurrent b E W (j + 1) ω =
      (transportN b E W j ω)ᴴ * pathCurrent b E W j ω * transportN b E W j ω := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  obtain ⟨-, hR'⟩ := boundaryToInterior_succ b E hj ω hA hη hF hF' hG
  obtain ⟨-, hU2⟩ := full_solution b E j ω (isUnit_fullPathMatrix b E j ω hA hη hF)
  rw [coupling_split] at hU2
  set N := transportN b E W j ω
  set R := boundaryResolvent b E W j ω
  set U := boundaryToInterior b E W j ω
  set Cf := farCoupling W j ω
  have hQN : (1 - nearProjection W) * N = 1 - nearProjection W :=
    farProjection_mul_freshTransport b E _ _
  have hQι : (1 - nearProjection W) * (nearSel W)ᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, nearProjection_mul_nearSel, sub_self]
  have hQCf : (1 - nearProjection W) * Cfᴴ = Cfᴴ := by
    rw [Matrix.sub_mul, Matrix.one_mul, nearProjection_mul_farCoupling, sub_zero]
  have hQR : (1 - nearProjection W) * R =
      (boundaryZ b E)⁻¹ • ((1 - nearProjection W) - Cfᴴ * U) := by
    have h := congrArg ((1 - nearProjection W) * ·) hU2
    rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.mul_add (1 - nearProjection W), ← Matrix.mul_assoc (1 - nearProjection W) (nearSel W)ᴴ,
      hQι, Matrix.zero_mul, zero_add, hQCf, Matrix.mul_smul, Matrix.mul_one] at h
    rw [← eq_sub_of_add_eq' h, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have hQR' : (1 - nearProjection W) * boundaryResolvent b E W (j + 1) ω =
      (boundaryZ b E)⁻¹ • ((1 - nearProjection W) - Cfᴴ * (U * N)) := by
    rw [hR', Matrix.mul_smul]
    congr 1
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.conjTranspose_mul]
    have a1 : (1 - nearProjection W) * ((nearSel W)ᴴ * (ω.2 (j + 1))ᴴ * (nearSel W * R * N)) = 0 := by
      rw [Matrix.mul_assoc (nearSel W)ᴴ, ← Matrix.mul_assoc, hQι, Matrix.zero_mul]
    have a2 : (1 - nearProjection W) * (Cfᴴ * (U * N)) = Cfᴴ * (U * N) := by
      rw [← Matrix.mul_assoc, hQCf]
    rw [a1, a2, sub_zero]
  have hQS : (1 - nearProjection W) * scatteringMatrix b E W (j + 1) ω =
      (1 - nearProjection W) * scatteringMatrix b E W j ω * N := by
    have eS : ∀ n, scatteringMatrix b E W n ω =
        1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • boundaryResolvent b E W n ω := fun _ => rfl
    have hL : (1 - nearProjection W) * scatteringMatrix b E W (j + 1) ω = (1 - nearProjection W) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
          ((1 - nearProjection W) * boundaryResolvent b E W (j + 1) ω) := by
      rw [eS, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
    have hRt : (1 - nearProjection W) * scatteringMatrix b E W j ω * N = (1 - nearProjection W) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • ((1 - nearProjection W) * R * N) := by
      rw [eS, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.sub_mul, hQN, Matrix.smul_mul]
    rw [hL, hRt, hQR', hQR, Matrix.smul_mul, Matrix.sub_mul, hQN, Matrix.mul_assoc]
  have hunit : ∀ n, IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) →
      (scatteringMatrix b E W n ω)ᴴ * scatteringMatrix b E W n ω = 1 := fun n hn => by
    rw [scatteringMatrix_eq b E n ω hn]
    exact (twoPortScattering_unitary b E _ (pathSchur_isHermitian E n ω hA) hη).1
  rw [pathCurrent, pathCurrent, current_eq_far _ (hunit _ hF'), current_eq_far _ (hunit _ hF), hQS]
  have hNQN : Nᴴ * (1 - nearProjection W) * N = 1 - nearProjection W := by
    calc Nᴴ * (1 - nearProjection W) * N
        = Nᴴ * ((1 - nearProjection W)ᴴ * (1 - nearProjection W)) * N := by rw [farProjection_sq]
      _ = ((1 - nearProjection W) * N)ᴴ * ((1 - nearProjection W) * N) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 - nearProjection W := by rw [hQN, farProjection_sq]
  rw [Matrix.mul_sub Nᴴ, Matrix.sub_mul (Nᴴ * (1 - nearProjection W)), hNQN]
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **Old tags are transported by `N`**: for `j ≥ 1` and every block of birth index `k < j`,
`Y_{j+1;k} = Nᴴ Y_{j;k} N`. -/
theorem tagResponse_succ (b E : ℝ) {j : ℕ} (hj : 1 ≤ j) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1))
    (hG : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => pathX b E W j ω u.2 v.2) (freshSample W j ω)))
    {k : ℕ} (hk : k < j) :
    tagResponse b E W (j + 1) k ω =
      (transportN b E W j ω)ᴴ * tagResponse b E W j k ω * transportN b E W j ω := by
  obtain ⟨hU, -⟩ := boundaryToInterior_succ b E hj ω hA hη hF hF' hG
  set e := headEquiv j W
  have hP : (tagProjection W (j + 1) k).submatrix e e =
      Matrix.fromBlocks 0 0 0 (tagProjection W j k) := by
    ext (x | ⟨i, x⟩) (y | ⟨l, y⟩) <;>
      simp only [e, tagProjection, Matrix.submatrix_apply, headEquiv_inl, headEquiv_inr, Fin.val_succ,
        Fin.val_zero, Prod.mk.injEq, Fin.succ_inj, false_and, Fin.succ_ne_zero,
        Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] <;>
      split_ifs <;> simp_all <;> omega
  have hre : tagResponse b E W (j + 1) k ω =
      ((boundaryToInterior b E W (j + 1) ω).submatrix e id)ᴴ *
        (tagProjection W (j + 1) k).submatrix e e *
        (boundaryToInterior b E W (j + 1) ω).submatrix e id := by
    rw [tagResponse, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  rw [hre, hU, hP, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows, tagResponse]
  simp only [Matrix.mul_zero, zero_add, Matrix.zero_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

end BlockBand.Transmission.Bridge
