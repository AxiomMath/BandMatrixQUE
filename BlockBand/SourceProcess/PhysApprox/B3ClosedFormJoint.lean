module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepKFresh
public import BlockBand.SourceProcess.CompleteSourceGap.GapIdentity

/-!
# The joint one-layer covariance of `u*Δv` with the Gram increments

One fresh one-port layer at a Hermitian two-port `𝕏` with far-eliminated input `X = nearSchur z 𝕏`
(passive), `Δ = freshDelta X`, `N = freshTransport 𝕏`, `U = freshU X`, `F = wardF 𝕏`,
`F₁ = passiveF X = R - c₀`. For frame columns `c, c'` (two-port vectors) the Gram increments are
`dM = c*(NN* - 1)c'` and `dB = c*(NPN* - P)c'`.

* `bilinear_wardOf`: by the a.s. Ward identity `NN* - 1 = ι(ΔF) + (ΔF)*ι*`,
  `dM = (ιc)*Δ(Fc') + conj((ιc')*Δ(Fc))`;
* `freshTransport_P_sub`: `NPN* - P = ι*(U - 1)ι` (deterministic), so `dB = (ιc)*(U - 1)(ιc')`;
* `freshQuad X = U - 1 - (ΔF₁ + (ΔF₁)*)` is the quadratic remainder;
* **`FreshDeltaQuadCov`**: `|E[(x*Δy)(x'*freshQuad y')]| ≤ C C_f⁴(W^{-3/2} + covErr +
  (δ₀ + W⁻¹)²)` (a cubic fresh moment, not implied by the `Δ`-`Δ` or `U`-`U`
  hypotheses), stated as a hypothesis;
* **`fresh_dK_dB_le`** (proved from the contract hypotheses and `FreshDeltaQuadCov`):
  `|E[(u*Δv) dB] - {σ₋/W (u*F₁ιc')((ιc)*v) + σ₊/W (u*ιc')((F₁ιc)*v)}|
  ≤ C C_f⁴(W^{-3/2} + covErr + (δ₀ + W⁻¹)²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.ClosedForm

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceCovariance BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.PhysApprox.B3 (fresh_delta_memLp fresh_delta_same_le
  fresh_delta_opp_le)
open scoped ComplexConjugate ComplexOrder

variable {W : ℕ}

/-!
## Algebra of the two increments
-/

theorem star_dot_conjTranspose_mulVec {n m : Type*} [Fintype n] [Fintype m] (M : Matrix n m ℂ)
    (c : m → ℂ) (w : n → ℂ) : star c ⬝ᵥ (Mᴴ *ᵥ w) = star (star w ⬝ᵥ (M *ᵥ c)) := by
  rw [dotProduct_mulVec, ← star_mulVec, ← star_dotProduct_star (M *ᵥ c) (star w), star_star]

theorem star_dot_conjTranspose_mulVec' {n m : Type*} [Fintype n] [Fintype m] (M : Matrix n m ℂ)
    (c : m → ℂ) (w : n → ℂ) : star c ⬝ᵥ (Mᴴ *ᵥ w) = star (M *ᵥ c) ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← star_mulVec]

/-- `c*(ι(DF) + (DF)*ι*)c' = (ιc)*D(Fc') + conj((ιc')*D(Fc))`. -/
theorem bilinear_wardOf (D : Matrix (Fin W) (Fin W) ℂ) (F : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (c c' : Fin 2 × Fin W → ℂ) :
    bilinear c (wardOf D F) c' =
      bilinear (nearSel W *ᵥ c) D (F *ᵥ c') + star (bilinear (nearSel W *ᵥ c') D (F *ᵥ c)) := by
  unfold bilinear wardOf
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, star_dot_conjTranspose_mulVec',
    ← mulVec_mulVec c' (D * F)ᴴ (nearSel W), star_dot_conjTranspose_mulVec]
  simp only [← mulVec_mulVec]

/-- **`NPN* - P = ι*(U - 1)ι`** for the fresh transport. -/
theorem freshTransport_P_sub (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshTransport b E XX ω * nearProjection W * (freshTransport b E XX ω)ᴴ - nearProjection W =
      (nearSel W)ᴴ * (freshU b E (nearSchur (boundaryZ b E) XX) ω - 1) * nearSel W := by
  have hN := CompleteSourceGap.freshTransport_mul_nearSel_conj b E XX ω
  rw [← nearSel_conj_mul_nearSel]
  have e : freshTransport b E XX ω * ((nearSel W)ᴴ * nearSel W) * (freshTransport b E XX ω)ᴴ =
      (freshTransport b E XX ω * (nearSel W)ᴴ) * (freshTransport b E XX ω * (nearSel W)ᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
  rw [e, hN, conjTranspose_mul, conjTranspose_conjTranspose, freshU]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

/-- `c*(ι*Mι)c' = (ιc)*M(ιc')`. -/
theorem bilinear_nearSel_sandwich (M : Matrix (Fin W) (Fin W) ℂ) (c c' : Fin 2 × Fin W → ℂ) :
    bilinear c ((nearSel W)ᴴ * M * nearSel W) c' =
      bilinear (nearSel W *ᵥ c) M (nearSel W *ᵥ c') := by
  unfold bilinear
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

/-- The quadratic remainder `U - 1 - (ΔF₁ + (ΔF₁)*)` of the fresh layer at `X`. -/
def freshQuad (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  freshU b E X ω - 1 -
    (freshDelta b E X ω * passiveF b E X + (freshDelta b E X ω * passiveF b E X)ᴴ)

/-- `x*(U - 1)y = x*Δ(F₁y) + conj(y*Δ(F₁x)) + x*Quad y`. -/
theorem bilinear_freshU_sub (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (x y : Fin W → ℂ) :
    bilinear x (freshU b E X ω - 1) y =
      bilinear x (freshDelta b E X ω) (passiveF b E X *ᵥ y) +
        star (bilinear y (freshDelta b E X ω) (passiveF b E X *ᵥ x)) +
        bilinear x (freshQuad b E X ω) y := by
  have e : freshU b E X ω - 1 = freshDelta b E X ω * passiveF b E X +
      (freshDelta b E X ω * passiveF b E X)ᴴ + freshQuad b E X ω := by
    simp only [freshQuad]; abel
  rw [e]
  unfold bilinear
  rw [add_mulVec, add_mulVec, dotProduct_add, dotProduct_add, ← mulVec_mulVec,
    star_dot_conjTranspose_mulVec, ← mulVec_mulVec]

/-!
## The cubic estimate
-/

/-- **`FreshDeltaQuadCov`**: the fresh mixed moment of `x*Δy` with the quadratic
remainder of `U - 1` is `O(W^{-3/2} + covErr + (δ₀ + W⁻¹)²)` at every passive input, uniformly on
the bulk, together with the integrability of the product (the Gaussian third moment of the linear
fluctuation vanishes). -/
def FreshDeltaQuadCov : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧
    ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (x y x' y' : Fin W → ℂ) (Cf : ℝ), vecNorm x ≤ Cf → vecNorm y ≤ Cf →
        vecNorm x' ≤ Cf → vecNorm y' ≤ Cf →
        Integrable (fun F => bilinear x (freshDelta b E X F) y *
            bilinear x' (freshQuad b E X F) y') (freshLaw W b) ∧
        ‖∫ F, bilinear x (freshDelta b E X F) y * bilinear x' (freshQuad b E X F) y'
            ∂freshLaw W b‖ ≤
          C * Cf ^ 4 * ((W : ℝ)⁻¹ / Real.sqrt W + covErr b E s X +
            (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2)

/-!
## The two joint one-layer covariances
-/

theorem eta_pos_of_bulk {b E κ : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    0 < (boundaryZ b E).im :=
  boundaryZ_im_pos (b := b) (by linarith) (by linarith [hE.1]) (by linarith [hE.2])

/-- **The joint one-layer covariance of `u*Δv` with `dM = c*(NN* - 1)c'`** (the Ward
identity and the two `Δ`-covariances `fresh_delta_same_le`, `fresh_delta_opp_le`; from the input
hypotheses).
-/
theorem fresh_dK_dM_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (u v : Fin W → ℂ) (c c' : Fin 2 × Fin W → ℂ) (Cf : ℝ), vecNorm u ≤ Cf →
        vecNorm v ≤ Cf → vecNorm (nearSel W *ᵥ c) ≤ Cf → vecNorm (nearSel W *ᵥ c') ≤ Cf →
        vecNorm (wardF b E XX *ᵥ c) ≤ Cf → vecNorm (wardF b E XX *ᵥ c') ≤ Cf →
        ‖∫ F, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XX) F) v *
              bilinear c (wardNoise b E XX F) c' ∂freshLaw W b -
            (sigmaMinus b E s / W *
                crossedTensor u v (nearSel W *ᵥ c) (wardF b E XX *ᵥ c') 1 1 +
              ((sigmaPlus b : ℝ) : ℂ) / W *
                (bilinear u 1 (nearSel W *ᵥ c') * bilinear (wardF b E XX *ᵥ c) 1 v))‖ ≤
          C * Cf ^ 4 * (covErr b E s (nearSchur (boundaryZ b E) XX) +
            (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + (W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨CS, WS, hCS, hS⟩ := fresh_delta_same_le hGA hLp hb0 hb hκ
  obtain ⟨CO, WO, hCO, hO⟩ := fresh_delta_opp_le hGA hLp hP hb0 hb hκ
  obtain ⟨C₂, W₂, -, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  refine ⟨CS + CO, max (max WS WO) (max W₂ 1), add_nonneg hCS hCO, ?_⟩
  intro W hW E hE s hs XX hXX u v c c' Cf hu hv ha ha' hw hw'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWS, hWO⟩, hW2, hW1⟩ := hW
  have hη := eta_pos_of_bulk hb hκ hE
  set X := nearSchur (boundaryZ b E) XX
  have hX : (passiveY X).PosSemidef := nearSchur_passive hη hXX
  obtain ⟨-, -, hL2⟩ := hM W hW2 E hE X hX
  set a := nearSel W *ᵥ c
  set a' := nearSel W *ᵥ c'
  set w := wardF b E XX *ᵥ c
  set w' := wardF b E XX *ᵥ c'
  have hward := ward_ae hb0 hXX (show 0 < etaZ b E from hη) hW1
  have e : ∫ F, bilinear u (freshDelta b E X F) v * bilinear c (wardNoise b E XX F) c'
        ∂freshLaw W b =
      ∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshDelta b E X F) w' ∂freshLaw W b +
        ∫ F, bilinear u (freshDelta b E X F) v * star (bilinear a' (freshDelta b E X F) w)
          ∂freshLaw W b := by
    have hi1 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        bilinear a (freshDelta b E X F) w') (freshLaw W b) := (hL2 u v).integrable_mul (hL2 a w')
    have hi2 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        star (bilinear a' (freshDelta b E X F) w)) (freshLaw W b) :=
      (hL2 u v).integrable_mul (hL2 a' w).star
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (hward.mono fun F hF => ?_)
    simp only [hF, bilinear_wardOf, mul_add, X, a, a', w, w']
  rw [e]
  have h1 := hS W hWS E hE s hs X hX u v a w' Cf hu hv ha hw'
  have h2 := hO W hWO E hE s hs X hX u v a' w Cf hu hv ha' hw
  calc _ = ‖(∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshDelta b E X F) w'
          ∂freshLaw W b - sigmaMinus b E s / W * crossedTensor u v a w' 1 1) +
        (∫ F, bilinear u (freshDelta b E X F) v * star (bilinear a' (freshDelta b E X F) w)
          ∂freshLaw W b - ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 a' * bilinear w 1 v))‖ := by
        congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by
        have := add_le_add h1 h2
        nlinarith [this])

/-- **The joint one-layer covariance of `u*Δv` with `dB = c*(NPN* - P)c'`**, from the contract
hypotheses and the cubic estimate `FreshDeltaQuadCov`. -/
theorem fresh_dK_dB_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hQ : FreshDeltaQuadCov) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (u v : Fin W → ℂ) (c c' : Fin 2 × Fin W → ℂ) (Cf : ℝ), vecNorm u ≤ Cf →
        vecNorm v ≤ Cf → vecNorm (nearSel W *ᵥ c) ≤ Cf → vecNorm (nearSel W *ᵥ c') ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c)) ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c')) ≤ Cf →
        ‖∫ F, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XX) F) v *
              bilinear c (freshTransport b E XX F * nearProjection W *
                (freshTransport b E XX F)ᴴ - nearProjection W) c' ∂freshLaw W b -
            (sigmaMinus b E s / W * crossedTensor u v (nearSel W *ᵥ c)
                (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c')) 1 1 +
              ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 (nearSel W *ᵥ c') *
                bilinear (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c)) 1 v))‖
          ≤ C * Cf ^ 4 * ((W : ℝ)⁻¹ / Real.sqrt W + covErr b E s (nearSchur (boundaryZ b E) XX) +
            (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + (W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨CS, WS, hCS, hS⟩ := fresh_delta_same_le hGA hLp hb0 hb hκ
  obtain ⟨CO, WO, hCO, hO⟩ := fresh_delta_opp_le hGA hLp hP hb0 hb hκ
  obtain ⟨CQ, WQ, hCQ, hQ'⟩ := hQ b hb0 hb κ hκ
  obtain ⟨C₂, W₂, -, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  refine ⟨CS + CO + CQ, max (max WS WO) (max W₂ WQ), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX u v c c' Cf hu hv ha ha' hw hw'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWS, hWO⟩, hW2, hWQ⟩ := hW
  have hη := eta_pos_of_bulk hb hκ hE
  set X := nearSchur (boundaryZ b E) XX
  have hX : (passiveY X).PosSemidef := nearSchur_passive hη hXX
  obtain ⟨-, -, hL2⟩ := hM W hW2 E hE X hX
  set a := nearSel W *ᵥ c
  set a' := nearSel W *ᵥ c'
  set w := passiveF b E X *ᵥ a
  set w' := passiveF b E X *ᵥ a'
  obtain ⟨hQi, hQb⟩ := hQ' W hWQ E hE s hs X hX u v a a' Cf hu hv ha ha'
  have e : ∫ F, bilinear u (freshDelta b E X F) v * bilinear c (freshTransport b E XX F *
        nearProjection W * (freshTransport b E XX F)ᴴ - nearProjection W) c' ∂freshLaw W b =
      (∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshDelta b E X F) w'
          ∂freshLaw W b +
        ∫ F, bilinear u (freshDelta b E X F) v * star (bilinear a' (freshDelta b E X F) w)
          ∂freshLaw W b) +
        ∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshQuad b E X F) a'
          ∂freshLaw W b := by
    have hi1 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        bilinear a (freshDelta b E X F) w') (freshLaw W b) := (hL2 u v).integrable_mul (hL2 a w')
    have hi2 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        star (bilinear a' (freshDelta b E X F) w)) (freshLaw W b) :=
      (hL2 u v).integrable_mul (hL2 a' w).star
    have hi12 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        bilinear a (freshDelta b E X F) w' + bilinear u (freshDelta b E X F) v *
        star (bilinear a' (freshDelta b E X F) w)) (freshLaw W b) := hi1.add hi2
    rw [← integral_add hi1 hi2, ← integral_add hi12 hQi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
    simp only [freshTransport_P_sub, bilinear_nearSel_sandwich, bilinear_freshU_sub, X, a, a', w,
      w']
    ring
  rw [e]
  have h1 := hS W hWS E hE s hs X hX u v a w' Cf hu hv ha hw'
  have h2 := hO W hWO E hE s hs X hX u v a' w Cf hu hv ha' hw
  have hC4 : 0 ≤ Cf ^ 4 := by
    have := Transmission.PassiveCovariance.vecNorm_nonneg u
    have : 0 ≤ Cf := le_trans this hu
    positivity
  have hce : 0 ≤ covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 :=
    add_nonneg (B3.covErr_nonneg hb hκ hE s hX) (sq_nonneg _)
  have hw3 : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  calc _ = ‖((∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshDelta b E X F) w'
          ∂freshLaw W b - sigmaMinus b E s / W * crossedTensor u v a w' 1 1) +
        (∫ F, bilinear u (freshDelta b E X F) v * star (bilinear a' (freshDelta b E X F) w)
          ∂freshLaw W b - ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 a' * bilinear w 1 v))) +
        ∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshQuad b E X F) a'
          ∂freshLaw W b‖ := by
        congr 1; ring
    _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        have h12 := (norm_add_le _ _).trans (add_le_add h1 h2)
        nlinarith [add_le_add h12 hQb, mul_nonneg (mul_nonneg hCS hC4) hw3,
          mul_nonneg (mul_nonneg hCO hC4) hw3, mul_nonneg (mul_nonneg hCQ hC4) hce]

end BlockBand.SourceProcess.PhysApprox.ClosedForm

