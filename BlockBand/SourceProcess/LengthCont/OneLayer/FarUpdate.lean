module

public import BlockBand.SourceProcess.RawTag.UpdPins

/-!
# The far components of the source frames under one growth step

For a unit tag `ξ` born before length `l`, with frame `V = 𝒰*ξ` (`RawTag.frame`), write
`d = (far part of V)` (`farL`) and `e = (far part of 𝕊V)` (`farR`), `a = nearL`, `c = nearR`,
`Δ = stepDelta`, `ℝ = boundaryResolvent` (all at length `l`). Then, a.s. for every `l ≥ 1`:
* `d₊(y) = d(y) + conj(a*Δ ℝ_{near,far}(·, y))` (`farL_succ`);
* `e₊(y) = e(y) + Σ_x ℝ_{far,near}(y, x) (Δc)(x)` (`farR_succ`).
Both follow from `RawTag.grown_G_eq` (the old/old block of the grown interior inverse), the
port equations `G₁₂ = -z⁻¹G₁₁C`, `G₂₁ = -z⁻¹C*G₁₁`, `G₂₁C + zℝ = 1`, `C*G₁₂ + zℝ = 1`, and
the fact that the far coupling of the grown path is that of the old path.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.RawTag
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-- The far component `d` of the frame `𝒰*ξ` of a unit tag. -/
def farL (b E : ℝ) (W l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) : Fin W → ℂ :=
  fun y => frame b E W l β ω g (1, y)

/-- The far component `e` of `𝕊𝒰*ξ`. -/
def farR (b E : ℝ) (W l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) : Fin W → ℂ :=
  fun y => (scatteringMatrix b E W l ω *ᵥ frame b E W l β ω g) (1, y)

/-- `-z⁻¹ C(·, (far, y))`. -/
def farVec (b E : ℝ) (W l : ℕ) (ω : GrowthPath W) (y : Fin W) : Fin l × Fin W → ℂ :=
  fun w => -(boundaryZ b E)⁻¹ * pathPortCoupling (pathAt W l ω) w (1, y)

/-- `conj(-z⁻¹) C(·, (far, y))`. -/
def farUVec (b E : ℝ) (W l : ℕ) (ω : GrowthPath W) (y : Fin W) : Fin l × Fin W → ℂ :=
  fun w => star (-(boundaryZ b E)⁻¹) * pathPortCoupling (pathAt W l ω) w (1, y)

theorem coupling_far_succ {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W) (y : Fin W)
    (s : Fin W ⊕ (Fin l × Fin W)) :
    pathPortCoupling (pathAt W (l + 1) ω) (headEquiv l W s) (1, y) =
      Sum.elim (0 : Fin W → ℂ) (fun w => pathPortCoupling (pathAt W l ω) w (1, y)) s := by
  have h := congrFun (congrFun (coupling_succ_submatrix hl ω) s) (1, y)
  simp only [Matrix.submatrix_apply, id] at h
  rw [h]
  rcases s with x | p
  · simp [Matrix.fromRows_apply_inl, Matrix.mul_apply, nearSel]
  · simp [Matrix.fromRows_apply_inr, farCoupling]

theorem farVec_comp {l : ℕ} (hl : 1 ≤ l) (b E : ℝ) (ω : GrowthPath W) (y : Fin W) :
    farVec b E W (l + 1) ω y ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) (farVec b E W l ω y) := by
  funext s
  simp only [Function.comp_apply, farVec, coupling_far_succ hl ω y s]
  rcases s with x | p
  · simp
  · simp only [Sum.elim_inr, farVec]

theorem farUVec_comp {l : ℕ} (hl : 1 ≤ l) (b E : ℝ) (ω : GrowthPath W) (y : Fin W) :
    farUVec b E W (l + 1) ω y ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) (farUVec b E W l ω y) := by
  funext s
  simp only [Function.comp_apply, farUVec, coupling_far_succ hl ω y s]
  rcases s with x | p
  · simp
  · simp only [Sum.elim_inr, farUVec]

/-- The left-inverse block equations `G𝓜 = 1`: `G₁₁C + zG₁₂ = 0`, `G₂₁C + zG₂₂ = 1`. -/
theorem left_eqs (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hM : IsUnit (fullPathMatrix b E W n ω)) :
    (fullInverse b E W n ω).toBlocks₁₁ * pathPortCoupling (pathAt W n ω) +
        boundaryZ b E • (fullInverse b E W n ω).toBlocks₁₂ = 0 ∧
      (fullInverse b E W n ω).toBlocks₂₁ * pathPortCoupling (pathAt W n ω) +
        boundaryZ b E • (fullInverse b E W n ω).toBlocks₂₂ = 1 := by
  have h := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  rw [← Matrix.fromBlocks_toBlocks (fullPathMatrix b E W n ω)⁻¹, fullPathMatrix,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
  refine ⟨?_, ?_⟩
  · have := h.2.1; rw [Matrix.mul_smul, Matrix.mul_one] at this; exact this
  · have := h.2.2.2; rw [Matrix.mul_smul, Matrix.mul_one] at this; exact this

/-- The right-inverse block equation `𝓜G = 1`, `(2,2)` block: `C*G₁₂ + zG₂₂ = 1`. -/
theorem right_eq22 (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hM : IsUnit (fullPathMatrix b E W n ω)) :
    (pathPortCoupling (pathAt W n ω))ᴴ * (fullInverse b E W n ω).toBlocks₁₂ +
        boundaryZ b E • (fullInverse b E W n ω).toBlocks₂₂ = 1 := by
  have h := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  rw [← Matrix.fromBlocks_toBlocks (fullPathMatrix b E W n ω)⁻¹, fullPathMatrix,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
  have := h.2.2.2; rw [Matrix.smul_mul, Matrix.one_mul] at this; exact this

theorem toBlocks₁₂_eq (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hM : IsUnit (fullPathMatrix b E W n ω))
    (hz : boundaryZ b E ≠ 0) :
    (fullInverse b E W n ω).toBlocks₁₂ =
      -((boundaryZ b E)⁻¹ •
        ((fullInverse b E W n ω).toBlocks₁₁ * pathPortCoupling (pathAt W n ω))) := by
  have h := (left_eqs b E n ω hM).1
  rw [add_eq_zero_iff_eq_neg'] at h
  rw [← smul_neg, ← h, smul_smul, inv_mul_cancel₀ hz, one_smul]

theorem toBlocks₂₁_eq (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (hM : IsUnit (fullPathMatrix b E W n ω))
    (hz : boundaryZ b E ≠ 0) :
    (fullInverse b E W n ω).toBlocks₂₁ =
      -((boundaryZ b E)⁻¹ •
        ((pathPortCoupling (pathAt W n ω))ᴴ * (fullInverse b E W n ω).toBlocks₁₁)) := by
  have h := (RawTag.interior_eqs b E n ω hM).2
  rw [add_eq_zero_iff_eq_neg'] at h
  rw [← smul_neg, ← h, smul_smul, inv_mul_cancel₀ hz, one_smul]

/-- `d(y) = conj(ξ*G₁₁ v_y)`, `v_y = -z⁻¹C(·, (far, y))`. -/
theorem farL_rep (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ)
    (hM : IsUnit (fullPathMatrix b E W l ω)) (hz : boundaryZ b E ≠ 0) (y : Fin W) :
    farL b E W l β ω g y = star (star (unitTag W l β g) ⬝ᵥ
      ((fullInverse b E W l ω).toBlocks₁₁ *ᵥ farVec b E W l ω y)) := by
  have hU : ∀ x, boundaryToInterior b E W l ω x (1, y) =
      ((fullInverse b E W l ω).toBlocks₁₁ *ᵥ farVec b E W l ω y) x := by
    intro x
    rw [boundaryToInterior, toBlocks₁₂_eq b E l ω hM hz]
    simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, mulVec, dotProduct,
      farVec, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  have e1 : farL b E W l β ω g y =
      ∑ x, star (boundaryToInterior b E W l ω x (1, y)) * unitTag W l β g x := by
    simp [farL, frame, mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [e1, dotProduct, star_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hU x, Pi.star_apply, star_mul', star_star, mul_comm]

/-- `e(y) = (conj(-z⁻¹) C(·,(far,y)))* G₁₁ ξ`. -/
theorem farR_rep (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hM : IsUnit (fullPathMatrix b E W l ω))
    (hz : boundaryZ b E ≠ 0) (y : Fin W) :
    farR b E W l β ω g y = star (farUVec b E W l ω y) ⬝ᵥ
      ((fullInverse b E W l ω).toBlocks₁₁ *ᵥ unitTag W l β g) := by
  have e1 : scatteringMatrix b E W l ω *ᵥ frame b E W l β ω g =
      (-((boundaryZ b E)⁻¹ • (pathPortCoupling (pathAt W l ω))ᴴ)) *ᵥ
        ((fullInverse b E W l ω).toBlocks₁₁ *ᵥ unitTag W l β g) := by
    rw [frame, mulVec_mulVec, mulVec_mulVec, ← RawTag.fullInverse_21_eq b E l ω hA,
      toBlocks₂₁_eq b E l ω hM hz, Matrix.neg_mul, Matrix.smul_mul]
  rw [farR, e1]
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [farUVec, Matrix.conjTranspose_apply]

/-- `ι𝕊𝒰* v_y = ℝ_{near,far}(·, y)`. -/
theorem nearCoef_farVec (b E : ℝ) (l : ℕ) (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian)
    (hM : IsUnit (fullPathMatrix b E W l ω)) (hz : boundaryZ b E ≠ 0) (y : Fin W) :
    (nearSel W * (scatteringMatrix b E W l ω * (boundaryToInterior b E W l ω)ᴴ)) *ᵥ
        farVec b E W l ω y = fun x => boundaryResolvent b E W l ω (0, x) (1, y) := by
  rw [← RawTag.fullInverse_21_eq b E l ω hA]
  have h := (left_eqs b E l ω hM).2
  have hc : ∀ c : Fin 2 × Fin W, ((fullInverse b E W l ω).toBlocks₂₁ *ᵥ farVec b E W l ω y) c =
      -(boundaryZ b E)⁻¹ * (((fullInverse b E W l ω).toBlocks₂₁ *
        pathPortCoupling (pathAt W l ω)) c (1, y)) := by
    intro c
    simp only [mulVec, dotProduct, farVec, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  funext x
  rw [← mulVec_mulVec]
  simp only [mulVec, dotProduct, nearSel]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [show (∑ j, (fullInverse b E W l ω).toBlocks₂₁ (0, x) j * farVec b E W l ω y j) =
    ((fullInverse b E W l ω).toBlocks₂₁ *ᵥ farVec b E W l ω y) (0, x) from rfl, hc]
  have h1 : ((fullInverse b E W l ω).toBlocks₂₁ * pathPortCoupling (pathAt W l ω)) (0, x) (1, y) =
      -(boundaryZ b E * boundaryResolvent b E W l ω (0, x) (1, y)) := by
    have := congrFun (congrFun h (0, x)) (1, y)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at this
    rw [boundaryResolvent]
    have hne : ((0 : Fin 2), x) ≠ (1, y) := by simp
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at this
    linear_combination this
  rw [h1]
  field_simp

/-- `conj(ι𝒰*u_y) = ℝ_{far,near}(y, ·)`. -/
theorem nearCoef_farUVec (b E : ℝ) (l : ℕ) (ω : GrowthPath W)
    (hM : IsUnit (fullPathMatrix b E W l ω)) (hz : boundaryZ b E ≠ 0) (y : Fin W) :
    (boundaryToInterior b E W l ω * (nearSel W)ᴴ)ᴴ *ᵥ farUVec b E W l ω y =
      fun x => star (boundaryResolvent b E W l ω (1, y) (0, x)) := by
  have h := right_eq22 b E l ω hM
  have h1 : ∀ x : Fin W,
      ((pathPortCoupling (pathAt W l ω))ᴴ * boundaryToInterior b E W l ω) (1, y) (0, x) =
      -(boundaryZ b E * boundaryResolvent b E W l ω (1, y) (0, x)) := by
    intro x
    have := congrFun (congrFun h (1, y)) (0, x)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at this
    rw [boundaryResolvent, boundaryToInterior]
    have hne : ((1 : Fin 2), y) ≠ (0, x) := by simp
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at this
    linear_combination this
  have e2 : ∀ x : Fin W, ((boundaryToInterior b E W l ω)ᴴ *ᵥ farUVec b E W l ω y) (0, x) =
      star (-(boundaryZ b E)⁻¹ * ((pathPortCoupling (pathAt W l ω))ᴴ *
        boundaryToInterior b E W l ω) (1, y) (0, x)) := by
    intro x
    simp only [mulVec, dotProduct, farUVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  funext x
  rw [conjTranspose_mul, conjTranspose_conjTranspose, ← mulVec_mulVec]
  simp only [mulVec, dotProduct, nearSel]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [show (∑ j, (boundaryToInterior b E W l ω)ᴴ (0, x) j * farUVec b E W l ω y j) =
    ((boundaryToInterior b E W l ω)ᴴ *ᵥ farUVec b E W l ω y) (0, x) from rfl, e2 x, h1 x]
  congr 1
  field_simp

/-- **The old/old Schur step** for arbitrary old vectors. -/
theorem form_succ_old (b E : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1))
    (hY : (passiveY (pathX b E W l ω)).PosSemidef) (hB : IsUnit (ω.2 (l + 1)))
    (u v : Fin l × Fin W → ℂ) (u' v' : Fin (l + 1) × Fin W → ℂ)
    (hu : u' ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) u)
    (hv : v' ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) v) :
    star u' ⬝ᵥ ((fullInverse b E W (l + 1) ω).toBlocks₁₁ *ᵥ v') =
      star u ⬝ᵥ ((fullInverse b E W l ω).toBlocks₁₁ *ᵥ v) +
        bilinear ((boundaryToInterior b E W l ω * (nearSel W)ᴴ)ᴴ *ᵥ u) (stepDelta b E W l ω)
          ((nearSel W * (scatteringMatrix b E W l ω * (boundaryToInterior b E W l ω)ᴴ)) *ᵥ v) := by
  rw [RawTag.dot_reindex (headEquiv l W), hu, hv, grown_G_eq b E hl ω hA hη hF hF' hY hB,
    RawTag.dot_fromBlocks]
  simp only [star_zero, zero_dotProduct, mulVec_zero, zero_add, add_mulVec, dotProduct_add]
  rw [RawTag.dot_sandwich]
  rfl

/-- **The far frame update** `d₊ = d + conj(a*Δℝ₀₁)`. -/
theorem farL_succ (b E : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1))
    (hY : (passiveY (pathX b E W l ω)).PosSemidef) (hB : IsUnit (ω.2 (l + 1)))
    {β : ℕ} (hβ : β < l) (g : Fin W → ℂ) (y : Fin W) :
    farL b E W (l + 1) β ω g y = farL b E W l β ω g y +
      star (bilinear (nearL b E W l β ω g) (stepDelta b E W l ω)
        (fun x => boundaryResolvent b E W l ω (0, x) (1, y))) := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have hM := isUnit_fullPathMatrix b E l ω hA hη hF
  have hM' := isUnit_fullPathMatrix b E (l + 1) ω hA hη hF'
  rw [farL_rep b E (l + 1) β ω g hM' hz, form_succ_old b E hl ω hA hη hF hF' hY hB _ _ _ _
    (unitTag_comp_old hβ g) (farVec_comp hl b E ω y), star_add, ← farL_rep b E l β ω g hM hz,
    nearL_eq, nearCoef_farVec b E l ω hA hM hz]

/-- **The far scattered update** `e₊ = e + ℝ₁₀Δc`. -/
theorem farR_succ (b E : ℝ) {l : ℕ} (hl : 1 ≤ l) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W l ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (l + 1) ω) - (E : ℂ) • 1))
    (hY : (passiveY (pathX b E W l ω)).PosSemidef) (hB : IsUnit (ω.2 (l + 1)))
    {β : ℕ} (hβ : β < l) (g : Fin W → ℂ) (y : Fin W) :
    farR b E W (l + 1) β ω g y = farR b E W l β ω g y +
      bilinear (fun x => star (boundaryResolvent b E W l ω (1, y) (0, x)))
        (stepDelta b E W l ω) (nearR b E W l β ω g) := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have hM := isUnit_fullPathMatrix b E l ω hA hη hF
  have hM' := isUnit_fullPathMatrix b E (l + 1) ω hA hη hF'
  rw [farR_rep b E (l + 1) β ω g hA hM' hz, form_succ_old b E hl ω hA hη hF hF' hY hB _ _ _ _
    (farUVec_comp hl b E ω y) (unitTag_comp_old hβ g), ← farR_rep b E l β ω g hA hM hz,
    nearR_eq, nearCoef_farUVec b E l ω hM hz]

/-- **The far updates hold a.s.** at every step `l ≥ 1` and old birth index. -/
theorem ae_farUpdate {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {W : ℕ} (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ l : ℕ, 1 ≤ l → ∀ β : ℕ, β < l → ∀ (g : Fin W → ℂ) (y : Fin W),
      farL b E W (l + 1) β ω g y = farL b E W l β ω g y +
        star (bilinear (nearL b E W l β ω g) (stepDelta b E W l ω)
          (fun x => boundaryResolvent b E W l ω (0, x) (1, y))) ∧
      farR b E W (l + 1) β ω g y = farR b E W l β ω g y +
        bilinear (fun x => star (boundaryResolvent b E W l ω (1, y) (0, x)))
          (stepDelta b E W l ω) (nearR b E W l β ω g) := by
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E,
    ae_isUnit_growth_bond hb0 hW] with ω hA hF hB l hl β hβ g y
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hY := pathNearSchur_passive (κ := fun _ => 0) ⟨hA, fun _ => le_rfl, hη⟩ l
  exact ⟨farL_succ b E hl ω hA hη (hF l) (hF (l + 1)) hY (hB (l + 1)) hβ g y,
    farR_succ b E hl ω hA hη (hF l) (hF (l + 1)) hY (hB (l + 1)) hβ g y⟩

end BlockBand.SourceProcess.LengthCont.OneLayer
