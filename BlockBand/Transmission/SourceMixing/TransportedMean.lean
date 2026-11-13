module

public import BlockBand.Transmission.SourceMixing.WeightedThree
public import BlockBand.Transmission.PassiveLayer.RPlus

/-!
# The transported mean `E(Lf₊L*) = KM(θs₁M + (ρ₁ - c₀s₁))(KM)ᴴ + O(W⁻²)`

Hypothesis `PassiveBoundsStatement`. Law `freshLaw W b` (`= layerLaw W b .oneBlockOnePort`),
deterministic strictly passive `X` (`Y ≻ 0`), operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`;
constants depend on `b, E` only, uniformly in `W ≥ W₀` and `X`.

The mean of the transported source `Lf₊L*` over one fresh layer, for strictly passive `X`, in
terms of the dressed physical block `M` and the scalars `θ, s₁, ρ₁`.

* `transportedF_mean`:
  `‖E(Lf₊L*) - ((θs₁)·KM·M·(KM)ᴴ + (ρ₁ - c₀s₁)·KM(KM)ᴴ)‖ ≤ C/W²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem integrable_mul_entries {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    (R : Matrix n n ℂ) (F : Ω → Matrix n n ℂ) (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) :
    ∀ x y, Integrable (fun ω => (R * F ω) x y) μ := fun x y => by
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun k _ => (hF k y).const_mul _

theorem matrixExpect_sub_smul {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A B : Ω → Matrix n n ℂ) (c : ℂ) (hA : ∀ x y, Integrable (fun ω => A ω x y) μ)
    (hB : ∀ x y, Integrable (fun ω => B ω x y) μ) :
    matrixExpect μ (fun ω => A ω - c • B ω) = matrixExpect μ A - c • matrixExpect μ B := by
  ext x y
  simp only [matrixExpect, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  rw [integral_sub (hA x y) ((hB x y).const_mul c), integral_const_mul]

theorem matrixExpect_congr_ae {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B : Ω → Matrix n n ℂ} (h : ∀ᵐ ω ∂μ, A ω = B ω) : matrixExpect μ A = matrixExpect μ B := by
  ext x y
  exact integral_congr_ae (h.mono fun ω hω => congrFun (congrFun hω x) y)

theorem wordVal_W3 (Kh G : LayerMat W) :
    wordVal Kh G ![0, 0, 3] ![1, pTwo, pTwo, 1] = G * (pTwo * (G * (pTwo * (Kh * G)ᴴ))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]
  simp [wLetter, Matrix.mul_assoc]

/-- The transported mean `E(Lf₊L*)` at the layer level. -/
theorem transportedF_mean (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
          ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
            (rhoOf b E X - cZero b E * sOne b E X) • (kmOf b E X * (kmOf b E X)ᴴ))‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C₃, W₃, hC₃, h3⟩ := threeBlock hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, -, hw⟩ := wordMean_bound hA hb0 hb h1 h2 3 1
  obtain ⟨CD, WD, -, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  refine ⟨C₃ + ‖cZero b E‖ * Cf, max (max W₃ Wf) (max Ww WD), by positivity, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₃, hWf⟩, hWw, hWD⟩ := hW
  obtain ⟨hW1, -⟩ := hD W hWD X hX
  obtain ⟨-, -, hU⟩ := hF W hWf X hX
  have hT3 := h3 W hW₃ X hX
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set W3 : LayerSample W .oneBlockOnePort → LayerMat W := fun ω =>
    gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (Kh * gRes b E X ω)ᴴ)))
  set W2 : LayerSample W .oneBlockOnePort → LayerMat W := fun ω =>
    gRes b E X ω * (pTwo * (Kh * gRes b E X ω)ᴴ)
  have hi3 : ∀ α β, Integrable (fun ω => W3 ω α β) μ := fun α β => by
    have h := (hw W hWw X hX.posSemidef 3 le_rfl ![0, 0, 3] ![1, pTwo, pTwo, 1] norm_ins4_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 3] ![1, pTwo, pTwo, 1] α β) =
        fun ω => W3 ω α β := funext fun ω => by rw [wordVal_W3]
    rw [e] at h; exact h
  have hi2 : ∀ α β, Integrable (fun ω => W2 ω α β) μ := fun α β => by
    have h := (hw W hWw X hX.posSemidef 2 (by norm_num) ![0, 3] ![1, pTwo, 1] norm_ins_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] ![1, pTwo, 1] α β) =
        fun ω => W2 ω α β := funext fun ω => by rw [wordVal_GPKGstar]
    rw [e] at h; exact h
  -- the a.e. identity `Lf₊L* = (K̂W₃)₀₀ - c₀(K̂W₂)₀₀`
  have hz : 0 < (boundaryZ b E).im := etaZ_pos b E (by linarith) h1 h2
  have hae : ∀ᵐ ω ∂μ, freshTransportedF b E X ω =
      blkAt (Kh * W3 ω) 0 0 - cZero b E • blkAt (Kh * W2 ω) 0 0 := by
    filter_upwards [ae_g22_eq_Rplus hb0 hb hW1 E hz hX.posSemidef] with ω hω
    rw [blkAt_three, blkAt_freshU, freshTransportedF, passiveF, passiveResolvent, ← hω, freshU]
    change lAt E (boundaryZ b E) X ω * (g22 E (boundaryZ b E) X ω - cZero b E • 1) *
      (lAt E (boundaryZ b E) X ω)ᴴ = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rfl
  have hiA : ∀ x y, Integrable (fun ω => blkAt (Kh * W3 ω) 0 0 x y) μ := fun x y =>
    integrable_mul_entries Kh W3 hi3 _ _
  have hiB : ∀ x y, Integrable (fun ω => blkAt (Kh * W2 ω) 0 0 x y) μ := fun x y =>
    integrable_mul_entries Kh W2 hi2 _ _
  have hE : matrixExpect μ (freshTransportedF b E X) =
      blkAt (Kh * matrixExpect μ W3) 0 0 - cZero b E • matrixExpect μ (freshU b E X) := by
    rw [matrixExpect_congr_ae hae, matrixExpect_sub_smul _ _ _ hiA hiB, mul_matrixExpect' _ _ hi3,
      blkAt_matrixExpect]
    congr 2
    rw [← blkAt_matrixExpect (F := fun ω => Kh * W2 ω), ← mul_matrixExpect' _ _ hi2]
    rw [mul_matrixExpect' _ _ hi2, blkAt_matrixExpect]
    exact congrArg (matrixExpect μ) (funext fun ω => blkAt_freshU b E X ω)
  rw [hE]
  have e : blkAt (Kh * matrixExpect μ W3) 0 0 - cZero b E • matrixExpect μ (freshU b E X) -
      ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
        (rhoOf b E X - cZero b E * sOne b E X) • (kmOf b E X * (kmOf b E X)ᴴ)) =
      (blkAt (Kh * matrixExpect μ W3) 0 0 -
        ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
          rhoOf b E X • (kmOf b E X * (kmOf b E X)ᴴ))) -
      cZero b E • (matrixExpect μ (freshU b E X) - sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)) := by
    rw [sub_smul, smul_sub, smul_smul]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  calc _ ≤ C₃ / (W : ℝ) ^ 2 + ‖cZero b E‖ * (Cf / (W : ℝ) ^ 2) :=
        add_le_add hT3 ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _)))
    _ = _ := by ring

end BlockBand.Transmission.SourceMixing
