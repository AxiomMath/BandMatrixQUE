module

public import BlockBand.Transmission.PathScalar.MeanEqPort

/-!
# The physical mean equation (trace form), uniformly on `bulkInterval κ`

For strictly passive `X` with `Im ζ ≥ ι₀`, `|v - f(ζ)| ≤ C/W²` with `ζ = -E - cv - bu`, from the
exact physical Schwinger–Dyson identity and the single-letter trace covariances.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

abbrev portTr (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 3).trace

/-- The exact physical Schwinger–Dyson identity in matrix form. -/
theorem meanSD_phys_matrix {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef) {C2 C4 : ℝ}
    (hm2 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hint : ∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 0 x y)
      (layerLaw W b .oneBlockOnePort)) (hW : 0 < W) :
    let μ := layerLaw W b .oneBlockOnePort
    let M0 := matrixExpect μ fun ω => passiveLetter E (boundaryZ b E) X ω 0
    (1 : Matrix (Fin W) (Fin W) ℂ) + (E : ℂ) • M0 + X * M0 =
      -((1 - 2 * b : ℝ) : ℂ) • matrixExpect μ (fun ω => physTr b E X ω • passiveLetter E (boundaryZ b E) X ω 0) -
        (b : ℂ) • matrixExpect μ (fun ω => portTr b E X ω • passiveLetter E (boundaryZ b E) X ω 0) := by
  intro μ M0
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  ext x y
  have hSD := meanSD_phys_of hη hX hm2 hm4 x (phys y)
  have hg : ∀ x y, Integrable (fun ω => gRes b E X ω (phys x) (phys y)) μ := fun x y => hint x y
  have hl : ∫ ω, (layerLin ω * gRes b E X ω) (phys x) (phys y) ∂μ =
      (if x = y then (1 : ℂ) else 0) + (E : ℂ) * M0 x y + ∑ k, X x k * M0 k y := by
    have hi : ∀ k, Integrable (fun ω => X x k * gRes b E X ω (phys k) (phys y)) μ :=
      fun k => (hg k y).const_mul _
    have hc : Integrable (fun ω => (if x = y then (1 : ℂ) else 0) +
        (E : ℂ) * gRes b E X ω (phys x) (phys y)) μ :=
      (integrable_const _).add ((hg x y).const_mul _)
    calc ∫ ω, (layerLin ω * gRes b E X ω) (phys x) (phys y) ∂μ
        = ∫ ω, ((if x = y then (1 : ℂ) else 0) + (E : ℂ) * gRes b E X ω (phys x) (phys y)) +
            ∑ k, X x k * gRes b E X ω (phys k) (phys y) ∂μ := by
          refine integral_congr_ae ((ae_layerLin_mul hb h1 h2 hX).mono fun ω h => ?_)
          dsimp only
          rw [h, Matrix.sub_apply, H0_phys]
          simp [Matrix.one_apply]; ring
      _ = _ := by
          rw [integral_add hc (integrable_finsetSum _ fun k _ => hi k),
            integral_add (integrable_const _) ((hg x y).const_mul _), integral_const_mul,
            integral_finsetSum _ fun k _ => hi k]
          have hconst : ∫ _ω, (if x = y then (1 : ℂ) else 0) ∂μ = if x = y then 1 else 0 := by
            simp
          simp only [integral_const_mul, M0, matrixExpect, Matrix.of_apply, hconst]
          rfl
  rw [gueVar_cast hb, ginVar_cast hb0] at hSD
  have e1 : ∫ ω, (∑ y', gRes b E X ω (phys y') (phys y')) * gRes b E X ω (phys x) (phys y) ∂μ =
      (W : ℂ) * ∫ ω, physTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω
    simp only [physTr, trace_letter0]; field_simp
  have e2 : ∫ ω, (∑ y', gRes b E X ω (port y') (port y')) * gRes b E X ω (phys x) (phys y) ∂μ =
      (W : ℂ) * ∫ ω, portTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω
    simp only [portTr, trace_letter3]; field_simp
  calc ((1 : Matrix (Fin W) (Fin W) ℂ) + (E : ℂ) • M0 + X * M0) x y
      = (if x = y then (1 : ℂ) else 0) + (E : ℂ) * M0 x y + ∑ k, X x k * M0 k y := by
        simp [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply]
    _ = ∫ ω, (layerLin ω * gRes b E X ω) (phys x) (phys y) ∂μ := hl.symm
    _ = -(((1 - 2 * b : ℝ) : ℂ) * ∫ ω, physTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ) -
          (b : ℂ) * ∫ ω, portTr b E X ω * gRes b E X ω (phys x) (phys y) ∂μ := by
        rw [hSD, e1, e2]; field_simp
    _ = _ := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, matrixExpect,
          Matrix.of_apply, neg_mul]
        rfl

theorem mul_matrixExpect {μ : Measure (LayerSample W .oneBlockOnePort)}
    (R : Matrix (Fin W) (Fin W) ℂ) (F : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ)
    (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) :
    R * matrixExpect μ F = matrixExpect μ (fun ω => R * F ω) := by
  ext i j
  simp only [matrixExpect, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ fun k _ => (hF k j).const_mul _]
  simp only [integral_const_mul]

/-- **The physical mean equation, trace form**: `|v - f(ζ)| ≤ C/W²` with `ζ = -E - cv - bu`, for
strictly passive `X` with `Im ζ ≥ ι₀`, uniformly on `bulkInterval κ`. -/
theorem meanEq_phys_u (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) {ι₀ : ℝ} (hι : 0 < ι₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        ι₀ ≤ (zetaOf b E (∫ ω, physTr b E X ω ∂freshLaw W b)
          (∫ ω, freshPortTrace b E X ω ∂freshLaw W b)).im →
        ‖(∫ ω, physTr b E X ω ∂freshLaw W b) - stieltjes X (zetaOf b E
          (∫ ω, physTr b E X ω ∂freshLaw W b) (∫ ω, freshPortTrace b E X ω ∂freshLaw W b))‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C2, W2, m2⟩ := layer_moments_u hA hb0 hb hκ (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments_u hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  obtain ⟨C, W₁, hcov⟩ := wordCov_u hA hb0 hb hκ (max 1 (1 / ι₀)) (le_max_left _ _)
  refine ⟨max C 0, max (max W₁ W2) (max W4 1), le_max_right _ _, fun W hW E hE X hX hζ => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW4, hW0⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hx0 : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  set μ := layerLaw W b .oneBlockOnePort
  set v := ∫ ω, physTr b E X ω ∂freshLaw W b
  set u := ∫ ω, freshPortTrace b E X ω ∂freshLaw W b
  set ζ := zetaOf b E v u
  set g := fun ω => passiveLetter E (boundaryZ b E) X ω 0
  set M0 := matrixExpect μ g
  have hζ0 : 0 < ζ.im := lt_of_lt_of_le hι hζ
  set K := ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have hK := BlockBand.Transmission.passive_inverse_constructed K _ hζ0 hX.posSemidef (im_pencil X ζ)
  set R := K⁻¹
  have hRn : ‖R‖ ≤ max 1 (1 / ι₀) := by
    refine (norm_inv_le_of_im K _ hζ0 hX.posSemidef (im_pencil X ζ)).trans ?_
    refine le_trans ?_ (le_max_right _ _)
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hι hζ
  have hone : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ max 1 (1 / ι₀) :=
    norm_one_matrix_le.trans (le_max_left _ _)
  have c1 := hcov W hW1 E hE X hX.posSemidef 0 0 1 hone
  have c3 := hcov W hW1 E hE X hX.posSemidef 3 0 1 hone
  have cp := hcov W hW1 E hE X hX.posSemidef 0 3 1 hone
  have d1 := hcov W hW1 E hE X hX.posSemidef 0 0 R hRn
  have d3 := hcov W hW1 E hE X hX.posSemidef 3 0 R hRn
  simp only [one_mul] at c1 c3 cp
  have hint : ∀ x y, Integrable (fun ω => g ω x y) μ := c1.2.1
  have hSDm := meanSD_phys_matrix hb0 hb h1 h2 hX (m2 W hW2 E hE X hX.posSemidef)
    (m4 W hW4 E hE X hX.posSemidef) hint hW0
  -- `∫ portTr = u`
  have hport : ∀ x, Integrable (fun ω => gRes b E X ω (port x) (port x)) μ := fun x => cp.2.1 x x
  have hu : ∫ ω, portTr b E X ω ∂μ = u := by
    simp only [u]
    rw [integral_freshPortTrace hb hW0 X hport, ← integral_finsetSum _ fun x _ => hport x,
      ← integral_const_mul]
    rfl
  have hv : v = (W : ℂ)⁻¹ * M0.trace := by
    simp only [v, M0, Matrix.trace, Matrix.diag, matrixExpect, Matrix.of_apply]
    rw [← integral_finsetSum _ fun x _ => hint x x, ← integral_const_mul]
    rfl
  -- multiply the matrix identity by `R`
  have hE1 : R * matrixExpect μ (fun ω => physTr b E X ω • g ω) =
      matrixExpect μ (fun ω => physTr b E X ω • (R * g ω)) := by
    rw [mul_matrixExpect (F := fun ω => physTr b E X ω • g ω) R
      (fun x y => by simpa [Matrix.smul_apply] using c1.2.2.1 x y)]
    congr 1; funext ω; rw [Matrix.mul_smul]
  have hE3 : R * matrixExpect μ (fun ω => portTr b E X ω • g ω) =
      matrixExpect μ (fun ω => portTr b E X ω • (R * g ω)) := by
    rw [mul_matrixExpect (F := fun ω => portTr b E X ω • g ω) R
      (fun x y => by simpa [Matrix.smul_apply] using c3.2.2.1 x y)]
    congr 1; funext ω; rw [Matrix.mul_smul]
  have hRM : R * M0 = matrixExpect μ (fun ω => R * g ω) := mul_matrixExpect R _ hint
  set Δ₁ := matrixExpect μ (fun ω => physTr b E X ω • (R * g ω)) -
    (∫ ω, physTr b E X ω ∂μ) • matrixExpect μ (fun ω => R * g ω)
  set Δ₃ := matrixExpect μ (fun ω => portTr b E X ω • (R * g ω)) -
    (∫ ω, portTr b E X ω ∂μ) • matrixExpect μ (fun ω => R * g ω)
  have hD1 : ‖Δ₁‖ ≤ C / (W : ℝ) ^ 2 := d1.2.2.2
  have hD3 : ‖Δ₃‖ ≤ C / (W : ℝ) ^ 2 := d3.2.2.2
  have hζdef : ζ = -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u := rfl
  have hRX : R * X = ζ • R - 1 := by
    have h := hK.2.2
    simp only [K, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at h
    rw [← h]; abel
  have key : R - M0 = -((1 - 2 * b : ℝ) : ℂ) • Δ₁ - (b : ℂ) • Δ₃ := by
    have hSDm' : (1 : Matrix (Fin W) (Fin W) ℂ) + (E : ℂ) • M0 + X * M0 =
        -((1 - 2 * b : ℝ) : ℂ) • matrixExpect μ (fun ω => physTr b E X ω • g ω) -
          (b : ℂ) • matrixExpect μ (fun ω => portTr b E X ω • g ω) := hSDm
    have h0 := congrArg (fun M => R * M) hSDm'
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hE1, hE3,
      ← Matrix.mul_assoc R X M0, hRX, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h0
    have e1 : matrixExpect μ (fun ω => physTr b E X ω • (R * g ω)) = Δ₁ + v • (R * M0) := by
      simp only [Δ₁, hRM]; abel
    have e3 : matrixExpect μ (fun ω => portTr b E X ω • (R * g ω)) = Δ₃ + u • (R * M0) := by
      simp only [Δ₃, hRM, hu]; abel
    rw [e1, e3] at h0
    have hs : R - M0 = (R + (E : ℂ) • (R * M0) + (ζ • (R * M0) - M0)) -
        ((E : ℂ) + ζ) • (R * M0) := by module
    rw [hs, h0, hζdef]
    module
  have htr : (W : ℂ)⁻¹ * R.trace = stieltjes X ζ := rfl
  rw [hv, ← htr, ← mul_sub, ← Matrix.trace_sub]
  rw [show M0 - R = -(R - M0) by abel, key]
  refine (norm_normTrace_le _).trans ?_
  have hc : 0 ≤ 1 - 2 * b := by linarith
  calc ‖-(-((1 - 2 * b : ℝ) : ℂ) • Δ₁ - (b : ℂ) • Δ₃)‖
      ≤ (1 - 2 * b) * ‖Δ₁‖ + b * ‖Δ₃‖ := by
        rw [norm_neg]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, norm_neg, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hc, Real.norm_of_nonneg hb0.le]
    _ ≤ (1 - 2 * b) * (C / (W : ℝ) ^ 2) + b * (C / (W : ℝ) ^ 2) := by gcongr
    _ ≤ max C 0 / (W : ℝ) ^ 2 := by
        have : C / (W : ℝ) ^ 2 ≤ max C 0 / (W : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
        have h0 : 0 ≤ max C 0 / (W : ℝ) ^ 2 := by positivity
        nlinarith

end BlockBand.Transmission.PathScalar
