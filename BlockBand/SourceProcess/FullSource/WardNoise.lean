module

public import BlockBand.SourceProcess.FullSource.WardIdentity

/-!
# The full Ward identity `𝓔 = ιΔF + F*Δ*ι*`

The Ward noise `𝓔 = NN* - I` of one fresh layer is linear in `Δ = K𝒢₁₁K - K`.

`ι* = nearSel W`, `F = ι*(ℝ - c₀I) = [R - c₀, ℝ₁₂]` (`wardF`), `c₀ = (2iη)⁻¹`:
* `ward_full`: `wardNoise b E 𝕏 ω = ι(ΔF) + (ΔF)*ι*`;
* `bilinear_ward`: `u*𝓔'v = (ι*u)*Δ'(Fv) + conj((ι*v)*Δ'(Fu))` for any `Δ'` in place of `Δ`
  (used with `Δ' = Δ - EΔ`);
* `norm_wardF_le`: `‖F‖ ≤ η⁻¹ + (2η)⁻¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `F = ι*(ℝ - c₀I) = [R - c₀I, ℝ₁₂]`. -/
def wardF (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin W) (Fin 2 × Fin W) ℂ :=
  nearSel W * (twoPortResolvent b E XX - cZero b E • 1)

theorem colBlock_nearSel_mul (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (j : Fin 2) :
    colBlock (nearSel W * M) j = portBlock M 0 j := by
  ext x y; simp [colBlock, portBlock, nearSel_mul_apply]

theorem portBlock_nearSel_conj_mul (M : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock ((nearSel W)ᴴ * M) i j = if i = 0 then colBlock M j else 0 := by
  ext x y
  fin_cases i <;>
    simp [portBlock, colBlock, Matrix.mul_apply, nearSel, Matrix.conjTranspose_apply,
      Prod.ext_iff]

theorem portBlock_conj_mul_nearSel (M : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    portBlock (Mᴴ * nearSel W) i j = if j = 0 then (colBlock M i)ᴴ else 0 := by
  have h : Mᴴ * nearSel W = ((nearSel W)ᴴ * M)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [h, ← portBlock_conjTranspose, portBlock_nearSel_conj_mul]
  split_ifs <;> simp

theorem portBlock_one (i j : Fin 2) :
    portBlock (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) i j = if i = j then 1 else 0 := by
  ext x y
  by_cases h : i = j
  · subst h; simp [portBlock, Matrix.one_apply]
  · simp [portBlock, h]

theorem portBlock_freshTransport (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (i j : Fin 2) :
    portBlock (freshTransport b E XX ω) i j =
      if i = 0 ∧ j = 0 then freshL b E (nearSchur (boundaryZ b E) XX) ω
      else if i = 0 ∧ j = 1 then freshDelta b E (nearSchur (boundaryZ b E) XX) ω *
        portBlock (twoPortResolvent b E XX) 0 1
      else if i = 1 ∧ j = 1 then 1 else 0 := by
  ext x y
  fin_cases i <;> fin_cases j <;> simp [portBlock, freshTransport]

/-- **The full Ward identity** `𝓔 = ι(ΔF) + (ΔF)*ι*`. -/
theorem ward_full (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    wardNoise b E XX ω =
      (nearSel W)ᴴ * (freshDelta b E (nearSchur (boundaryZ b E) XX) ω * wardF b E XX) +
        (freshDelta b E (nearSchur (boundaryZ b E) XX) ω * wardF b E XX)ᴴ * nearSel W := by
  have hz : 0 < (boundaryZ b E).im := hη
  have hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1) :=
    BlockBand.Transmission.portPencil_isUnit _ (portBlock_isHermitian hXX 1) hz
  have h00 := portBlock_twoPortResolvent_zero_zero b E XX hD
  have hF0 : colBlock (wardF b E XX) 0 = passiveF b E (nearSchur (boundaryZ b E) XX) := by
    rw [wardF, colBlock_nearSel_mul]
    ext x y; simp [portBlock, passiveF, ← h00, Matrix.one_apply]
  have hF1 : colBlock (wardF b E XX) 1 = portBlock (twoPortResolvent b E XX) 0 1 := by
    rw [wardF, colBlock_nearSel_mul]
    ext x y; simp [portBlock]
  have hW := ward_near b E hXX hη hA hB
  apply portBlock_ext
  intro i j
  have hadd : ∀ M M' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      portBlock (M + M') i j = portBlock M i j + portBlock M' i j := fun _ _ => rfl
  have hsub : ∀ M M' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      portBlock (M - M') i j = portBlock M i j - portBlock M' i j := fun _ _ => rfl
  rw [wardNoise, hsub, portBlock_mul, ← portBlock_conjTranspose, ← portBlock_conjTranspose,
    portBlock_one, hadd, portBlock_nearSel_conj_mul, portBlock_conj_mul_nearSel, colBlock_mul,
    colBlock_mul]
  fin_cases i <;> fin_cases j <;>
    simp [portBlock_freshTransport, hF0, hF1, conjTranspose_mul] at hW ⊢
  rw [← hW]

theorem bilinear_conjTranspose {m : Type*} [Fintype m] (u v : m → ℂ) (M : Matrix m m ℂ) :
    bilinear u Mᴴ v = star (bilinear v M u) := by
  simp only [bilinear, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bilinear_sandwich' {m n : Type*} [Fintype m] [Fintype n] (u v : m → ℂ)
    (P : Matrix n m ℂ) (D : Matrix n n ℂ) (F : Matrix n m ℂ) :
    bilinear u (Pᴴ * (D * F)) v = bilinear (P *ᵥ u) D (F *ᵥ v) := by
  simp only [bilinear, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

/-- `u*(ι(Δ'F) + (Δ'F)*ι*)v = (ι*u)*Δ'(Fv) + conj((ι*v)*Δ'(Fu))`. -/
theorem bilinear_ward (u v : Fin 2 × Fin W → ℂ) (D : Matrix (Fin W) (Fin W) ℂ)
    (F : Matrix (Fin W) (Fin 2 × Fin W) ℂ) :
    bilinear u ((nearSel W)ᴴ * (D * F) + (D * F)ᴴ * nearSel W) v =
      bilinear (nearSel W *ᵥ u) D (F *ᵥ v) + star (bilinear (nearSel W *ᵥ v) D (F *ᵥ u)) := by
  have h2 : (D * F)ᴴ * nearSel W = ((nearSel W)ᴴ * (D * F))ᴴ := by
    rw [conjTranspose_mul (nearSel W)ᴴ, conjTranspose_conjTranspose]
  rw [bilinear, Matrix.add_mulVec, dotProduct_add, ← bilinear, ← bilinear, h2,
    bilinear_conjTranspose, bilinear_sandwich', bilinear_sandwich']

theorem vecNorm_nearSel_mulVec_le (u : Fin 2 × Fin W → ℂ) : vecNorm (nearSel W *ᵥ u) ≤ vecNorm u := by
  have h : nearSel W *ᵥ u = u ∘ fun x => ((0 : Fin 2), x) := by
    funext x; simp [nearSel, mulVec, dotProduct]
  rw [h]
  exact vecNorm_comp_le u fun _ _ h => by simpa using congrArg Prod.snd h

theorem norm_nearSel_mul_le (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ‖nearSel W * M‖ ≤ ‖M‖ := by
  refine opNorm_le_of_vec' _ (norm_nonneg _) fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  exact (vecNorm_nearSel_mulVec_le _).trans (vecNorm_mulVec_le' M x)

/-- `‖F‖ ≤ η⁻¹ + (2η)⁻¹`. -/
theorem norm_wardF_le (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) :
    ‖wardF b E XX‖ ≤ (etaZ b E)⁻¹ + (2 * etaZ b E)⁻¹ := by
  refine (norm_nearSel_mul_le _).trans ((norm_sub_le _ _).trans (add_le_add
    (norm_twoPortResolvent_le b E hXX hη) ?_))
  rw [norm_smul, norm_cZero b E hη]
  exact mul_le_of_le_one_right (by positivity) norm_one_matrix_le

end BlockBand.SourceProcess.FullSource
