module

public import BlockBand.Transmission.PassiveCovariance.LayerBlocks

/-!
# The mean-field equation in operator norm and the dressed inverse

Hypothesis `PassiveBoundsStatement` (`moments`, `traceMatrix`), at `w = z_∂`. Law
`layerLaw W b .oneBlockOnePort` (`= freshLaw W b`), fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, deterministic
strictly passive `X` (`Y ≻ 0`), operator norm on `2W × 2W` layer matrices. Constants depend on
`b, E` only (uniform in `W ≥ W₀`, `X`).

`meanField_phys`/`meanField_port` are *entrywise* `C/W²` bounds. Here:

* `traceCov_op`: the full layer trace–matrix covariance `Cov(⟨ℓ_k⟩, 𝒢)` has **operator norm**
  `≤ 4C/W²` (the `traceMatrix` clause of `PassiveBoundsStatement` on the four blocks,
  `norm_layerMat_le`).
* `meanField_op`: with the mean traces `m₁ = E⟨𝒢₁₁⟩`, `m₂ = E⟨𝒢₂₂⟩`, the self-energy
  `S̄ = diag((1-2b)m₁ + bm₂, bm₁)` and the **dressed matrix** `D = H₀ - S̄`
  (`H₀ = layerMatrix … 0`, never inverted), `‖D·E𝒢 - I‖ ≤ C/W²` in operator norm.
* `dressed_inverse`: for `W ≥ W₀`, `D` is invertible, `‖D⁻¹‖ ≤ C` and
  `‖E𝒢 - D⁻¹‖ ≤ C/W²`. This is the mean-field equation `E𝒢 = (H₀ - S̄)⁻¹ + O(W⁻²)`.

The bound on `D⁻¹` does not use the stability of the scalar fixed point: it follows from
`‖E𝒢‖ ≤ E‖𝒢‖ ≤ C` (the `moments` clause) and a Neumann series. Stability is still needed to
identify `m₁, m₂` with `a`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## Trace–matrix covariance of the whole layer resolvent
-/

/-- The matrix covariance `E[f G] - (E f)(E G)`. -/
def covMat {Ω n : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℂ) (G : Ω → Matrix n n ℂ) :
    Matrix n n ℂ :=
  matrixExpect μ (fun ω => f ω • G ω) - (∫ ω, f ω ∂μ) • matrixExpect μ G

/-- The normalized trace `W⁻¹ Tr ℓ_k` of the letter `k` at `w = z_∂`. -/
def trLetter (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (k : Fin 6)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω k).trace

theorem blk_covMat (μ : Measure (LayerSample W .oneBlockOnePort)) (f : LayerSample W .oneBlockOnePort → ℂ)
    (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (m : Fin 4) :
    (![blk11, blk12, blk21, blk22] m) (covMat μ f (gRes b E X)) =
      matrixExpect μ (fun ω => f ω • passiveLetter E (boundaryZ b E) X ω m.castSucc.castSucc) -
        (∫ ω, f ω ∂μ) • matrixExpect μ (fun ω => passiveLetter E (boundaryZ b E) X ω
          m.castSucc.castSucc) := by
  fin_cases m <;> ext x y <;> rfl

/-- **The layer trace–matrix covariance in operator norm**: `‖Cov(⟨ℓ_k⟩, 𝒢)‖ ≤ C/W²` for every
letter `k`, uniformly over passive `X`, with the integrability used by `meanField_op`. -/
theorem traceCov_op (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ k : Fin 6,
        Integrable (trLetter b E X k) (layerLaw W b .oneBlockOnePort) ∧
        (∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort)) ∧
        (∀ α β, Integrable (fun ω => trLetter b E X k ω * gRes b E X ω α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖covMat (layerLaw W b .oneBlockOnePort) (trLetter b E X k) (gRes b E X)‖ ≤
          4 * C / (W : ℝ) ^ 2 := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C, W₀, h⟩ := hA.traceMatrix b hb0 hb _ hκ 1 1
  refine ⟨max C 0, W₀, le_max_right _ _, fun W hW X hX k => ?_⟩
  have hD : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ 1 :=
    fun _ => norm_one_matrix_le
  have hm := fun m : Fin 6 => h W hW E (mem_bulkInterval_min E) _
    (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX 1 1 le_rfl le_rfl
    (fun _ => (k, false)) (fun _ => 1) (fun _ => (m, false)) (fun _ => 1) hD hD
  simp only [passiveWord_single_fun] at hm
  have hent : ∀ (α β : LayerSite W .oneBlockOnePort), ∃ (m : Fin 6) (x y : Fin W),
      ∀ ω, gRes b E X ω α β = passiveLetter E (boundaryZ b E) X ω m x y := by
    have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
    rintro (⟨i0, x⟩ | ⟨i0, x⟩) (⟨j0, y⟩ | ⟨j0, y⟩) <;> rw [h0 i0, h0 j0]
    exacts [⟨0, x, y, fun _ => rfl⟩, ⟨1, x, y, fun _ => rfl⟩, ⟨2, x, y, fun _ => rfl⟩,
      ⟨3, x, y, fun _ => rfl⟩]
  refine ⟨(hm 0).1, fun α β => ?_, fun α β => ?_, ?_⟩
  · obtain ⟨m, x, y, e⟩ := hent α β
    simp only [e]; exact (hm m).2.1 x y
  · obtain ⟨m, x, y, e⟩ := hent α β
    simp only [e]; exact (hm m).2.2.1 x y
  · have hb4 : ∀ m : Fin 4, ‖(![blk11, blk12, blk21, blk22] m)
        (covMat (layerLaw W b .oneBlockOnePort) (trLetter b E X k) (gRes b E X))‖ ≤
          max C 0 / (W : ℝ) ^ 2 := fun m => by
      rw [blk_covMat]
      exact ((hm _).2.2.2).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    have := norm_layerMat_le (covMat (layerLaw W b .oneBlockOnePort) (trLetter b E X k) (gRes b E X))
    have e1 : _ := hb4 0; have e2 : _ := hb4 1; have e3 : _ := hb4 2; have e4 : _ := hb4 3
    change ‖blk11 _‖ ≤ _ at e1
    change ‖blk12 _‖ ≤ _ at e2
    change ‖blk21 _‖ ≤ _ at e3
    change ‖blk22 _‖ ≤ _ at e4
    calc _ ≤ _ := this
      _ ≤ max C 0 / (W : ℝ) ^ 2 + max C 0 / (W : ℝ) ^ 2 + max C 0 / (W : ℝ) ^ 2 +
          max C 0 / (W : ℝ) ^ 2 := by gcongr
      _ = _ := by ring

/-!
## The mean-field equation and the dressed inverse
-/

/-- The mean normalized traces `m₁ = E⟨𝒢₁₁⟩` (`k = 0`) and `m₂ = E⟨𝒢₂₂⟩` (`k = 3`). -/
def meanTr (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (k : Fin 6) : ℂ :=
  ∫ ω, trLetter b E X k ω ∂layerLaw W b .oneBlockOnePort

/-- The mean self-energy `S̄ = diag((1-2b)m₁ + bm₂ on the physical sites, bm₁ on the port)`. -/
def selfEnergy (b : ℝ) (m₁ m₂ : ℂ) : LayerMat W :=
  diagonal (Sum.elim (fun _ => ((1 - 2 * b : ℝ) : ℂ) * m₁ + (b : ℂ) * m₂) fun _ => (b : ℂ) * m₁)

/-- The **dressed matrix** `H₀ - S̄` (`H₀` the deterministic part of the layer matrix). -/
def dressed (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : LayerMat W :=
  layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) 0 -
    selfEnergy b (meanTr b E X 0) (meanTr b E X 3)

theorem trace_letter_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (hW : (W : ℂ) ≠ 0) (k : Fin 6)
    (ω : LayerSample W .oneBlockOnePort) :
    (passiveLetter E (boundaryZ b E) X ω k).trace = (W : ℂ) * trLetter b E X k ω := by
  rw [trLetter]; field_simp

/-- **The mean-field equation in operator norm**: `‖(H₀ - S̄)E𝒢 - I‖ ≤ C/W²` for strictly
passive `X`, uniformly. -/
theorem meanField_op (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖dressed b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - 1‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨W₁, hSD⟩ := meanSD_phys hA hb0 hb h1 h2
  obtain ⟨W₂, hSDp⟩ := meanSD_port hA hb0 hb h1 h2
  obtain ⟨C, W₃, hC0, hcov⟩ := traceCov_op hA hb0 hb h1 h2
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨_, W₄, hmom⟩ := hA.moments b hb0 hb _ hκ 1 le_rfl
  refine ⟨8 * C, max (max (max W₁ W₂) (max W₃ W₄)) 1, by positivity, fun W hW X hX => ?_⟩
  have hW1 : W₁ ≤ W := by omega
  have hW2 : W₂ ≤ W := by omega
  have hW3 : W₃ ≤ W := by omega
  have hW4 : W₄ ≤ W := by omega
  have hWc : (W : ℂ) ≠ 0 := by
    have : 1 ≤ W := by omega
    exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  set μ := layerLaw W b .oneBlockOnePort
  set H₀ := layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) 0
  obtain ⟨i0, iG, iG0, c0⟩ := hcov W hW3 X hX.posSemidef 0
  obtain ⟨-, -, iG3, c3⟩ := hcov W hW3 X hX.posSemidef 3
  -- (a) `E[V𝒢] = I - H₀ E𝒢`
  have hVG : matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) = 1 - H₀ * matrixExpect μ (gRes b E X) := by
    ext α β
    have hae : ∀ᵐ ω ∂μ, (layerLin ω * gRes b E X ω) α β = (1 : LayerMat W) α β -
        ∑ γ, H₀ α γ * gRes b E X ω γ β := by
      filter_upwards [(hmom W hW4 E (mem_bulkInterval_min E) _
        (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX.posSemidef).1] with ω hω
      rw [layerLin_mul_gRes b E X ω ((Matrix.isUnit_iff_isUnit_det _).mpr hω)]
      rfl
    show ∫ ω, (layerLin ω * gRes b E X ω) α β ∂μ = (1 - H₀ * matrixExpect μ (gRes b E X)) α β
    rw [integral_congr_ae hae, integral_sub (integrable_const _)
      (integrable_finsetSum _ fun γ _ => (iG γ β).const_mul _), integral_const,
      integral_finsetSum _ fun γ _ => (iG γ β).const_mul _]
    simp [Matrix.sub_apply, Matrix.mul_apply, matrixExpect, integral_const_mul]
    rfl
  -- (b) `E[V𝒢] + S̄E𝒢 = -(diag d₁ Cov₀ + diag d₂ Cov₃)`
  set d₁ : LayerSite W .oneBlockOnePort → ℂ :=
    Sum.elim (fun _ => ((1 - 2 * b : ℝ) : ℂ)) fun _ => (b : ℂ)
  set d₂ : LayerSite W .oneBlockOnePort → ℂ := Sum.elim (fun _ => (b : ℂ)) fun _ => 0
  have hXi : matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) +
      selfEnergy b (meanTr b E X 0) (meanTr b E X 3) * matrixExpect μ (gRes b E X) =
      -(diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
        diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X)) := by
    have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
    ext α β
    rcases α with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rw [h0 i0]
    · have t0 : ∀ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (phys x) β =
          (W : ℂ) * (trLetter b E X 0 ω * gRes b E X ω (phys x) β) := fun ω => by
        rw [← trace_letter0, trace_letter_eq b E X hWc]; ring
      have t3 : ∀ ω, (∑ y, gRes b E X ω (port y) (port y)) * gRes b E X ω (phys x) β =
          (W : ℂ) * (trLetter b E X 3 ω * gRes b E X ω (phys x) β) := fun ω => by
        rw [← trace_letter3, trace_letter_eq b E X hWc]; ring
      have e := hSD W hW1 X hX x β
      simp only [t0, t3, integral_const_mul, gueVar_cast hb, ginVar_cast hb0] at e
      have lhs : (matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) +
          selfEnergy b (meanTr b E X 0) (meanTr b E X 3) * matrixExpect μ (gRes b E X) :
            LayerMat W) (phys x) β =
          ∫ ω, (layerLin ω * gRes b E X ω) (phys x) β ∂μ +
            (((1 - 2 * b : ℝ) : ℂ) * meanTr b E X 0 + (b : ℂ) * meanTr b E X 3) *
              ∫ ω, gRes b E X ω (phys x) β ∂μ := by
        simp only [Matrix.add_apply, selfEnergy, diagonal_mul]; rfl
      have rhs : (-(diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
          diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X)) : LayerMat W) (phys x) β =
          -(((1 - 2 * b : ℝ) : ℂ) * ((∫ ω, trLetter b E X 0 ω * gRes b E X ω (phys x) β ∂μ) -
              meanTr b E X 0 * ∫ ω, gRes b E X ω (phys x) β ∂μ) +
            (b : ℂ) * ((∫ ω, trLetter b E X 3 ω * gRes b E X ω (phys x) β ∂μ) -
              meanTr b E X 3 * ∫ ω, gRes b E X ω (phys x) β ∂μ)) := by
        simp only [Matrix.neg_apply, Matrix.add_apply, diagonal_mul]; rfl
      rw [lhs, rhs, e]
      field_simp
      ring
    · have t0 : ∀ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (port x) β =
          (W : ℂ) * (trLetter b E X 0 ω * gRes b E X ω (port x) β) := fun ω => by
        rw [← trace_letter0, trace_letter_eq b E X hWc]; ring
      have e := hSDp W hW2 X hX x β
      simp only [t0, integral_const_mul, ginVar_cast hb0] at e
      have lhs : (matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) +
          selfEnergy b (meanTr b E X 0) (meanTr b E X 3) * matrixExpect μ (gRes b E X) :
            LayerMat W) (port x) β =
          ∫ ω, (layerLin ω * gRes b E X ω) (port x) β ∂μ +
            ((b : ℂ) * meanTr b E X 0) * ∫ ω, gRes b E X ω (port x) β ∂μ := by
        simp only [Matrix.add_apply, selfEnergy, diagonal_mul]; rfl
      have rhs : (-(diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
          diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X)) : LayerMat W) (port x) β =
          -((b : ℂ) * ((∫ ω, trLetter b E X 0 ω * gRes b E X ω (port x) β ∂μ) -
              meanTr b E X 0 * ∫ ω, gRes b E X ω (port x) β ∂μ) +
            0 * ((∫ ω, trLetter b E X 3 ω * gRes b E X ω (port x) β ∂μ) -
              meanTr b E X 3 * ∫ ω, gRes b E X ω (port x) β ∂μ)) := by
        simp only [Matrix.neg_apply, Matrix.add_apply, diagonal_mul]; rfl
      rw [lhs, rhs, e]
      field_simp
      ring
  -- (c) `D E𝒢 - I = -Ξ`
  have hD : dressed b E X * matrixExpect μ (gRes b E X) - 1 =
      diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
        diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X) := by
    rw [← neg_neg (diagonal d₁ * _ + _), ← hXi, hVG, dressed, Matrix.sub_mul]
    abel
  rw [hD]
  have hn1 : ‖diagonal d₁‖ ≤ 1 := norm_diagonal_le _ zero_le_one fun i => by
    rcases i with i | i
    · simp only [d₁, Sum.elim_inl, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b)]
      linarith
    · simp only [d₁, Sum.elim_inr, Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
  have hn2 : ‖diagonal d₂‖ ≤ 1 := norm_diagonal_le _ zero_le_one fun i => by
    rcases i with i | i
    · simp only [d₂, Sum.elim_inl, Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
    · simp [d₂]
  have hc : 0 ≤ 4 * C / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖diagonal d₁‖ * ‖covMat μ (trLetter b E X 0) (gRes b E X)‖ +
        ‖diagonal d₂‖ * ‖covMat μ (trLetter b E X 3) (gRes b E X)‖ :=
        (norm_add_le _ _).trans (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))
    _ ≤ 1 * (4 * C / (W : ℝ) ^ 2) + 1 * (4 * C / (W : ℝ) ^ 2) := by
        gcongr
    _ = 8 * C / (W : ℝ) ^ 2 := by ring

/-- **The dressed inverse.** For `W ≥ W₀` and strictly passive `X`, the dressed matrix
`H₀ - S̄` is invertible, `‖(H₀ - S̄)⁻¹‖ ≤ C`, and `‖E𝒢 - (H₀ - S̄)⁻¹‖ ≤ C/W²` (operator
norm), uniformly in `X`. -/
theorem dressed_inverse (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        IsUnit (dressed b E X) ∧ ‖(dressed b E X)⁻¹‖ ≤ C ∧
          ‖matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - (dressed b E X)⁻¹‖ ≤
            C / (W : ℝ) ^ 2 := by
  obtain ⟨Cm, Wm, hCm, hmf⟩ := meanField_op hA hb0 hb h1 h2
  obtain ⟨C₁, W₁, hm1⟩ := layer_moments hA hb0 hb h1 h2 1 le_rfl
  obtain ⟨_, W₂, _, hcov⟩ := traceCov_op hA hb0 hb h1 h2
  set C₁' := max C₁ 0
  refine ⟨max (2 * C₁') (2 * C₁' * Cm), max (max Wm W₁) (max W₂ (⌈2 * Cm⌉₊ + 1)),
    fun W hW X hX => ?_⟩
  have hWm : Wm ≤ W := by omega
  have hW1 : W₁ ≤ W := by omega
  have hW2 : W₂ ≤ W := by omega
  have hW3 : ⌈2 * Cm⌉₊ + 1 ≤ W := by omega
  set μ := layerLaw W b .oneBlockOnePort
  set A := dressed b E X
  set B := matrixExpect μ (gRes b E X)
  set T := A * B - 1
  have hWpos : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hT : ‖T‖ ≤ Cm / (W : ℝ) ^ 2 := hmf W hWm X hX
  have hT2 : Cm / (W : ℝ) ^ 2 ≤ 1 / 2 := by
    have h2C : 2 * Cm ≤ W := by
      have := Nat.le_ceil (2 * Cm)
      have : ((⌈2 * Cm⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW3
      push_cast at this; linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- `‖E𝒢‖ ≤ C₁`
  have hB : ‖B‖ ≤ C₁' := by
    obtain ⟨-, iG, -, -⟩ := hcov W hW2 X hX.posSemidef 0
    have hmem := hm1 W hW1 X hX.posSemidef
    have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
    have hgm : Measurable fun ω => ‖gRes b E X ω‖ := continuous_norm.measurable.comp hGm
    have hmemLp : MemLp (fun ω => ‖gRes b E X ω‖) 1 μ := by
      rw [MemLp, ← ENNReal.ofReal_one]; exact lt_of_le_of_lt hmem ENNReal.ofReal_lt_top
    have hint := hmemLp.integrable le_rfl
    refine (norm_matrixExpect_le _ iG hint).trans ?_
    have h := hmem
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hgm.aestronglyMeasurable] at h
    have hI : ∫ ω, ‖gRes b E X ω‖ ∂μ = (∫⁻ ω, ‖‖gRes b E X ω‖‖ₑ ∂μ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
        hgm.aestronglyMeasurable]
      congr 1
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal (norm_nonneg _)]
    rw [hI]
    exact (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  -- Neumann series for `A B = 1 + T`
  have hTn : ‖-T‖ < 1 := by rw [norm_neg]; linarith
  set u := Units.oneSub (-T) hTn
  have hu : (u : LayerMat W) = A * B := by
    simp only [u, Units.val_oneSub, sub_neg_eq_add, T]; abel
  set v : LayerMat W := ↑u⁻¹
  have hv1 : A * B * v = 1 := by rw [← hu]; exact u.mul_inv
  have hv2 : v = 1 - T * v := by
    have : (1 + T) * v = 1 := by rw [show 1 + T = A * B by simp [T]]; exact hv1
    rw [add_mul, one_mul] at this
    rw [← this]; abel
  have hvn : ‖v‖ ≤ 2 := by
    have h := norm_sub_le (1 : LayerMat W) (T * v)
    rw [← hv2] at h
    have := Matrix.l2_opNorm_mul T v
    have := norm_one_matrix_le (n := LayerSite W .oneBlockOnePort)
    nlinarith [norm_nonneg v, norm_nonneg T]
  have hAinv : A * (B * v) = 1 := by rw [← Matrix.mul_assoc]; exact hv1
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr
    (IsUnit.of_mul_eq_one _ (by rw [← det_mul, hAinv, det_one]))
  have hinv : A⁻¹ = B * v := Matrix.inv_eq_right_inv hAinv
  have hC₁' : 0 ≤ C₁' := le_max_right _ _
  refine ⟨hAu, ?_, ?_⟩
  · rw [hinv]
    calc ‖B * v‖ ≤ ‖B‖ * ‖v‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ C₁' * 2 := mul_le_mul hB hvn (norm_nonneg _) hC₁'
      _ ≤ _ := by rw [mul_comm]; exact le_max_left _ _
  · rw [hinv]
    have e : B - B * v = B * (T * v) := by
      conv_lhs => rw [hv2]
      rw [Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e]
    calc ‖B * (T * v)‖ ≤ ‖B‖ * (‖T‖ * ‖v‖) :=
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ ≤ C₁' * (Cm / (W : ℝ) ^ 2 * 2) := by gcongr
      _ = 2 * C₁' * Cm / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end BlockBand.Transmission.PassiveCovariance
