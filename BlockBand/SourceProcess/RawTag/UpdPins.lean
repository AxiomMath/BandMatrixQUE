module

public import BlockBand.SourceProcess.RawTag.UpdForms

/-!
# The exact update `RawUpdate` and the births `RawBirth`

`rawUpdate_holds` and `rawBirth_holds`: the four raw-form identities of one growth step
(`rawForm_succ`, from `grown_G_eq` and the near frames `nearL_eq`, `nearR_eq`) hold almost
surely, which gives the exact source update on old entries and the entries with the newest block.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open scoped Matrix ComplexOrder

variable {W : ℕ}

theorem nearL_eq (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    (boundaryToInterior b E W l ω * (nearSel W)ᴴ)ᴴ *ᵥ unitTag W l β g = nearL b E W l β ω g := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose, ← mulVec_mulVec]; rfl

theorem nearR_eq (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    (nearSel W * (scatteringMatrix b E W l ω * (boundaryToInterior b E W l ω)ᴴ)) *ᵥ
      unitTag W l β g = nearR b E W l β ω g := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]; rfl

theorem kG_eq (K R G : Matrix (Fin W) (Fin W) ℂ) (hKR : K * R = 1) :
    K * G = 1 + (K * G * K - K) * R := by
  rw [Matrix.sub_mul, Matrix.mul_assoc (K * G), hKR, Matrix.mul_one]; abel

theorem Gk_eq (K R G : Matrix (Fin W) (Fin W) ℂ) (hRK : R * K = 1) :
    G * K = 1 + R * (K * G * K - K) := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc R (K * G) K, ← Matrix.mul_assoc R K G, hRK,
    Matrix.one_mul]; abel

/-- The four raw-form identities of one growth step, under the a.s. hypotheses. -/
theorem rawForm_succ (b E : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1))
    (hY : (passiveY (pathX b E W l ω)).PosSemidef) (hB : IsUnit (ω.2 (l + 1))) :
    (∀ β₁ β₂, β₁ < l → β₂ < l → ∀ g h : Fin W → ℂ,
      rawForm b E W (l + 1) β₁ β₂ ω g h = rawForm b E W l β₁ β₂ ω g h +
        bilinear (nearL b E W l β₁ ω g) (stepDelta b E W l ω) (nearR b E W l β₂ ω h)) ∧
    (∀ β, β < l → ∀ g h : Fin W → ℂ, rawForm b E W (l + 1) β l ω g h =
      bilinear (nearL b E W l β ω g) (1 + stepDelta b E W l ω * stepR b E W l ω)
        (unitVec W h)) ∧
    (∀ β, β < l → ∀ g h : Fin W → ℂ, rawForm b E W (l + 1) l β ω g h =
      bilinear (unitVec W g) (1 + stepR b E W l ω * stepDelta b E W l ω)
        (nearR b E W l β ω h)) ∧
    ∀ g h : Fin W → ℂ, rawForm b E W (l + 1) l l ω g h =
      bilinear (unitVec W g) (stepR b E W l ω + stepR b E W l ω * stepDelta b E W l ω *
        stepR b E W l ω) (unitVec W h) := by
  have hG := grown_G_eq b E hl ω hA hη hF hF' hY hB
  set X := pathX b E W l ω
  set 𝒢 := g11 E (boundaryZ b E) X (freshSample W l ω)
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set R := passiveResolvent b E X
  have hKu := (isUnit_iff_isUnit_det _).mp
    (BlockBand.SourceProcess.TagBirth.isUnit_pencil (b := b) (E := E) hη hY)
  have hRK : R * K = 1 := Matrix.nonsing_inv_mul _ hKu
  have hKR : K * R = 1 := Matrix.mul_nonsing_inv _ hKu
  have hΔ : stepDelta b E W l ω = K * 𝒢 * K - K := rfl
  have hR : stepR b E W l ω = R := rfl
  have e1 := kG_eq K R 𝒢 hKR
  have e2 := Gk_eq K R 𝒢 hRK
  have e3 : 𝒢 = R + R * (K * 𝒢 * K - K) * R :=
    BlockBand.SourceProcess.TagBirth.g11_eq_resolvent_add (b := b) (E := E) hη hY _
  have hre : ∀ β₁ β₂ g h, rawForm b E W (l + 1) β₁ β₂ ω g h =
      star (unitTag W (l + 1) β₁ g ∘ headEquiv l W) ⬝ᵥ
        ((fullInverse b E W (l + 1) ω).toBlocks₁₁.submatrix (headEquiv l W) (headEquiv l W) *ᵥ
          (unitTag W (l + 1) β₂ h ∘ headEquiv l W)) := fun _ _ _ _ => dot_reindex _ _ _ _
  refine ⟨fun β₁ β₂ h₁ h₂ g h => ?_, fun β hβ g h => ?_, fun β hβ g h => ?_, fun g h => ?_⟩
  · rw [hre, unitTag_comp_old h₁, unitTag_comp_old h₂, hG, dot_fromBlocks]
    simp only [star_zero, zero_dotProduct, mulVec_zero, zero_add, add_mulVec, dotProduct_add]
    rw [dot_sandwich, nearL_eq, nearR_eq, hΔ]; rfl
  · rw [hre, unitTag_comp_old hβ, unitTag_comp_new, hG, dot_fromBlocks]
    simp only [star_zero, zero_dotProduct, mulVec_zero, add_zero, zero_add]
    rw [← Matrix.mul_one (boundaryToInterior b E W l ω * (nearSel W)ᴴ * (K * 𝒢)), dot_sandwich,
      one_mulVec, nearL_eq, e1, hΔ, hR]; rfl
  · rw [hre, unitTag_comp_new, unitTag_comp_old hβ, hG, dot_fromBlocks]
    simp only [star_zero, zero_dotProduct, mulVec_zero, add_zero, zero_add]
    rw [← Matrix.one_mul (𝒢 * K * (nearSel W * (scatteringMatrix b E W l ω *
      (boundaryToInterior b E W l ω)ᴴ))), ← Matrix.mul_assoc, dot_sandwich, conjTranspose_one,
      one_mulVec, nearR_eq, e2, hΔ, hR]; rfl
  · rw [hre, unitTag_comp_new, unitTag_comp_new, hG, dot_fromBlocks]
    simp only [star_zero, zero_dotProduct, mulVec_zero, add_zero]
    rw [hR, hΔ, ← e3]; rfl

/-- **`RawUpdate` holds.** -/
theorem rawUpdate_holds : RawUpdate := by
  intro b E hb0 hb hE1 hE2 W hW
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E,
    ae_isUnit_growth_bond hb0 hW] with ω hA hF hB l hl β₁ β₂ h₁ h₂ g h
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hY := pathNearSchur_passive (κ := fun _ => 0) ⟨hA, fun _ => le_rfl, hη⟩ l
  exact (rawForm_succ b E hl ω hA hη (hF l) (hF (l + 1)) hY (hB (l + 1))).1 β₁ β₂ h₁ h₂ g h

/-- **`RawBirth` holds.** -/
theorem rawBirth_holds : RawBirth := by
  intro b E hb0 hb hE1 hE2 W hW
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E,
    ae_isUnit_growth_bond hb0 hW] with ω hA hF hB l hl
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hY := pathNearSchur_passive (κ := fun _ => 0) ⟨hA, fun _ => le_rfl, hη⟩ l
  exact (rawForm_succ b E hl ω hA hη (hF l) (hF (l + 1)) hY (hB (l + 1))).2

end BlockBand.SourceProcess.RawTag
