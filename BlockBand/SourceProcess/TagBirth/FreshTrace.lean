module

public import BlockBand.SourceProcess.FullSource.DeltaHolds
public import BlockBand.SourceProcess.TagBirth.Interface

/-!
# The fresh physical trace `⟨𝒢₁₁⟩` in `L^p`

With `Δ = K𝒢₁₁K - K` and its estimates on the scalar domain:

* `g11_eq_resolvent_add`: `𝒢₁₁ = R + RΔR` (`R = K⁻¹`, `K = z - X`, passive `X`);
* `trace_sandwich_eq`: `Tr(RNR) = Σ_x (R*e_x)*N(Re_x)`;
* `freshPhysTraceLp_holds hGA hLp : FreshPhysTraceLp`, from `deltaMean_holds`,
  `deltaFluctuation_holds` and the layer moments `BlockBand.Transmission.PassiveLayer.moments_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.TagBirth

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.FullSource
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem isUnit_pencil {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
  apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
  rw [matrixImaginaryPart_nearPencil]
  exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)

/-- `𝒢₁₁ = R + RΔR`. -/
theorem g11_eq_resolvent_add {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (ω : LayerSample W .oneBlockOnePort) :
    g11 E (boundaryZ b E) X ω = passiveResolvent b E X +
      passiveResolvent b E X * freshDelta b E X ω * passiveResolvent b E X := by
  have hK := (isUnit_iff_isUnit_det _).mp (isUnit_pencil hη hY)
  have hKR : (boundaryZ b E • 1 - X) * passiveResolvent b E X = 1 := Matrix.mul_nonsing_inv _ hK
  have hRK : passiveResolvent b E X * (boundaryZ b E • 1 - X) = 1 := Matrix.nonsing_inv_mul _ hK
  rw [freshDelta_eq]
  generalize boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X = K at hKR hRK ⊢
  have e : passiveResolvent b E X * (K * g11 E (boundaryZ b E) X ω * K - K) *
      passiveResolvent b E X = (passiveResolvent b E X * K) * g11 E (boundaryZ b E) X ω *
        (K * passiveResolvent b E X) - (passiveResolvent b E X * K) * passiveResolvent b E X := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [e, hRK, hKR, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  abel

theorem bilinear_single (A : Matrix (Fin W) (Fin W) ℂ) (x : Fin W) :
    bilinear (Pi.single x 1) A (Pi.single x 1) = A x x := by
  simp [bilinear, mulVec, dotProduct, Pi.single_apply]

/-- `Tr(RNR) = Σ_x (R*e_x)*N(Re_x)`. -/
theorem trace_sandwich_eq (R N : Matrix (Fin W) (Fin W) ℂ) :
    (R * N * R).trace = ∑ x, bilinear (Rᴴ *ᵥ Pi.single x 1) N (R *ᵥ Pi.single x 1) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← bilinear_sandwich', conjTranspose_conjTranspose, ← Matrix.mul_assoc, bilinear_single]
  rfl

theorem vecNorm_single' (x : Fin W) : vecNorm (Pi.single x (1 : ℂ)) = 1 := by
  rw [vecNorm, Finset.sum_eq_single x (fun l _ hl => by simp [hl]) (by simp)]; simp

theorem eLpNorm_const_prob {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} [IsProbabilityMeasure μ] (c : F) {p : ℝ≥0∞} (hp : p ≠ 0) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ := by
  rw [eLpNorm_const c hp (IsProbabilityMeasure.ne_zero μ)]; simp

theorem measurable_trace_comp {α n : Type*} [MeasurableSpace α] [Fintype n] {f : α → Matrix n n ℂ}
    (hf : Measurable f) : Measurable fun a => (f a).trace := by
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.measurable_sum _ fun i _ => hf.eval_matrix

theorem continuous_bilinear (u v : Fin W → ℂ) :
    Continuous fun N : Matrix (Fin W) (Fin W) ℂ => bilinear u N v := by
  simp only [bilinear, dotProduct, mulVec]
  fun_prop

/-- **`FreshPhysTraceLp`**, from the contract hypotheses only. -/
theorem freshPhysTraceLp_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    FreshPhysTraceLp := by
  intro b hb0 hb κ hκ p hp
  obtain ⟨dm, hdm, Cm, Wm, hmean⟩ := deltaMean_holds hGA hLp b hb0 hb κ hκ
  obtain ⟨df, hdf, hfl⟩ := deltaFluctuation_holds hGA hLp b hb0 hb κ hκ
  obtain ⟨Cf, Wf, hflp⟩ := hfl p hp
  obtain ⟨CG, WG, hmom⟩ := BlockBand.Transmission.PassiveLayer.moments_holds hGA b hb0 hb κ hκ p hp
  set ηi := (etaLow b κ)⁻¹
  have hηL := etaLow_pos (b := b) (by linarith) hκ
  have hηi : 0 ≤ ηi := inv_nonneg.mpr hηL.le
  set d := min dm df
  have hd : 0 < d := lt_min hdm hdf
  set Cm' := max Cm 0
  set Cf' := max Cf 0
  set CG' := max CG 0
  refine ⟨1 + ηi ^ 2 * Cm' + (CG' + 1) / d, ηi ^ 2 * (Cm' + Cf'), max (max Wm Wf) (max WG 1),
    by positivity, by positivity, fun W hW E hE X hY => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWf⟩, hWG, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using hp
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  set μ := freshLaw W b
  set a := matchedA E
  set δ := jetDistance0 b E X
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hmP : Measurable (physTr b E X) :=
    measurable_const.mul (measurable_trace_comp (measurable_g11 E _ X))
  by_cases hδd : δ ≤ d
  · -- the scalar domain: `⟨𝒢₁₁⟩ - a = c₀ + ⟨R(Δ - EΔ)R⟩`
    set R := passiveResolvent b E X
    set M := matrixExpect μ (freshDelta b E X)
    have hR : ‖R‖ ≤ ηi := (norm_passiveResolvent_le hb0 hb h1 h2 hY).trans
      (inv_anti₀ hηL (etaLow_le (by linarith) hκ hE))
    set c₀ : ℂ := ((W : ℂ)⁻¹ * R.trace - a) + (W : ℂ)⁻¹ * (R * M * R).trace
    set h : LayerSample W .oneBlockOnePort → ℂ := fun ω => (W : ℂ)⁻¹ *
      ∑ x, bilinear (Rᴴ *ᵥ Pi.single x 1) (freshDelta b E X ω - M) (R *ᵥ Pi.single x 1)
    have hdec : (fun ω => physTr b E X ω - a) = fun ω => c₀ + h ω := by
      funext ω
      have e1 : physTr b E X ω = (W : ℂ)⁻¹ * (g11 E (boundaryZ b E) X ω).trace := rfl
      rw [e1, g11_eq_resolvent_add hη hY, Matrix.trace_add,
        show R * freshDelta b E X ω * R = R * M * R + R * (freshDelta b E X ω - M) * R by
          simp only [Matrix.mul_sub, Matrix.sub_mul]; abel,
        Matrix.trace_add, trace_sandwich_eq R (freshDelta b E X ω - M)]
      simp only [c₀, h]; ring
    have hc₀ : ‖c₀‖ ≤ δ + ηi ^ 2 * (Cm * (δ + ((W : ℝ)⁻¹) ^ 2)) := by
      have hM := hmean W hWm E hE X hY (hδd.trans (min_le_left _ _))
      have e2 : ‖(W : ℂ)⁻¹ * (R * M * R).trace‖ ≤ ηi ^ 2 * (Cm * (δ + ((W : ℝ)⁻¹) ^ 2)) := by
        refine (norm_normTrace_le _).trans ?_
        calc ‖R * M * R‖ ≤ ‖R‖ * ‖M‖ * ‖R‖ :=
              (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
                (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
          _ ≤ ηi * (Cm * (δ + ((W : ℝ)⁻¹) ^ 2)) * ηi :=
            mul_le_mul (mul_le_mul hR hM (norm_nonneg _) hηi) hR (norm_nonneg _)
              (mul_nonneg hηi ((norm_nonneg _).trans hM))
          _ = _ := by ring
      exact (norm_add_le _ _).trans (add_le_add le_rfl e2)
    have hB : ∀ x, eLpNorm (fun ω => bilinear (Rᴴ *ᵥ Pi.single x 1)
        (freshDelta b E X ω - M) (R *ᵥ Pi.single x 1)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cf' / Real.sqrt W * ηi ^ 2) := by
      intro x
      refine (hflp W hWf E hE X hY (hδd.trans (min_le_right _ _)) _ _).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hu : vecNorm (Rᴴ *ᵥ Pi.single x (1 : ℂ)) ≤ ηi := by
        refine (vecNorm_mulVec_le' _ _).trans ?_
        rw [vecNorm_single', mul_one, Matrix.l2_opNorm_conjTranspose]; exact hR
      have hv : vecNorm (R *ᵥ Pi.single x (1 : ℂ)) ≤ ηi := by
        refine (vecNorm_mulVec_le' _ _).trans ?_
        rw [vecNorm_single', mul_one]; exact hR
      have hCf : Cf / Real.sqrt W ≤ Cf' / Real.sqrt W :=
        div_le_div_of_nonneg_right (le_max_left _ _) hsW.le
      have hn1 := BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg (Rᴴ *ᵥ Pi.single x (1 : ℂ))
      have hn2 := BlockBand.Transmission.PassiveCovariance.vecNorm_nonneg (R *ᵥ Pi.single x (1 : ℂ))
      calc Cf / Real.sqrt W * vecNorm (Rᴴ *ᵥ Pi.single x 1) * vecNorm (R *ᵥ Pi.single x 1)
          ≤ Cf' / Real.sqrt W * ηi * ηi := by
            have : 0 ≤ Cf' / Real.sqrt W := by positivity
            calc _ ≤ Cf' / Real.sqrt W * vecNorm (Rᴴ *ᵥ Pi.single x 1) *
                  vecNorm (R *ᵥ Pi.single x 1) := by gcongr
              _ ≤ _ := by gcongr
        _ = _ := by ring
    have hh : eLpNorm h (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cf' * ηi ^ 2 / Real.sqrt W) := by
      have e : h = (W : ℂ)⁻¹ • ∑ x, fun ω => bilinear (Rᴴ *ᵥ Pi.single x 1)
          (freshDelta b E X ω - M) (R *ᵥ Pi.single x 1) := by
        funext ω; simp [h, Finset.sum_apply]
      rw [e, eLpNorm_const_smul]
      refine (mul_le_mul_right (eLpNorm_sum_le hp1) _).trans ?_
      refine (mul_le_mul_right (Finset.sum_le_sum fun x _ => hB x) _).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ofReal_norm, norm_inv, Complex.norm_natCast, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [hdec]
    refine (eLpNorm_add_le (f := fun _ => c₀) (g := h) hp1).trans ?_
    refine (add_le_add (le_of_eq (eLpNorm_const_prob (μ := μ) c₀ hp0)) hh).trans ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hWi : ((W : ℝ)⁻¹) ^ 2 ≤ 1 / Real.sqrt W := by
      have hs1 : 1 ≤ Real.sqrt W := by rw [Real.one_le_sqrt]; exact_mod_cast hW1
      have : ((W : ℝ)⁻¹) ^ 2 ≤ (W : ℝ)⁻¹ := by
        have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
        nlinarith [inv_nonneg.mpr hW0.le]
      refine this.trans ?_
      rw [one_div]
      exact inv_anti₀ hsW (by nlinarith [Real.mul_self_sqrt hW0.le, hs1])
    have hCm : Cm ≤ Cm' := le_max_left _ _
    have hCa : ηi ^ 2 * (Cm * (δ + ((W : ℝ)⁻¹) ^ 2)) ≤
        ηi ^ 2 * Cm' * δ + ηi ^ 2 * Cm' * (1 / Real.sqrt W) := by
      have : Cm * (δ + ((W : ℝ)⁻¹) ^ 2) ≤ Cm' * (δ + 1 / Real.sqrt W) :=
        (mul_le_mul_of_nonneg_right hCm (by positivity)).trans
          (mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _))
      nlinarith [sq_nonneg ηi]
    have hd' : 0 ≤ (CG' + 1) / d * δ := by positivity
    have e3 : ηi ^ 2 * (Cm' + Cf') / Real.sqrt W =
        ηi ^ 2 * Cm' * (1 / Real.sqrt W) + Cf' * ηi ^ 2 / Real.sqrt W := by ring
    rw [add_mul, add_mul, e3]
    nlinarith [hc₀]
  · -- off the scalar domain: the crude bound `‖⟨𝒢₁₁⟩ - a‖_p ≤ C + 1 ≤ ((C+1)/d) δ₀`
    push Not at hδd
    obtain ⟨-, hG, -, -⟩ := hmom W hWG E hE (boundaryZ b E)
      (FullSource.boundaryZ_mem_paramDisk (by linarith) h1 h2) X hY
    have hpt : ∀ ω, ‖physTr b E X ω‖ ≤ ‖layerAt E (boundaryZ b E) X ω‖ := fun ω =>
      (norm_normTrace_le _).trans (by
        have : g11 E (boundaryZ b E) X ω = (layerAt E (boundaryZ b E) X ω).submatrix
            (fun x => Sum.inl ((0 : Fin 1), x)) (fun y => Sum.inl ((0 : Fin 1), y)) := by ext; rfl
        rw [show passiveLetter E (boundaryZ b E) X ω 0 = g11 E (boundaryZ b E) X ω from rfl, this]
        exact norm_submatrix_le _ (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h))
    have hP : eLpNorm (physTr b E X) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal CG' := by
      refine (eLpNorm_mono hmP.aestronglyMeasurable fun ω => (hpt ω).trans (le_of_eq (Real.norm_of_nonneg
        (norm_nonneg _)).symm)).trans (hG.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    have ha : ‖a‖ = 1 := by
      simp only [a]; exact BlockBand.Transmission.PassiveCovariance.norm_matchedA E h1 h2
    refine (eLpNorm_sub_le (f := physTr b E X) (g := fun _ => a) hp1).trans ?_
    refine (add_le_add hP (le_of_eq (eLpNorm_const_prob (μ := μ) a hp0))).trans ?_
    rw [← ofReal_norm, ha, ← ENNReal.ofReal_add (le_max_right _ _) zero_le_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : CG' + 1 ≤ (CG' + 1) / d * δ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]; nlinarith [le_max_right CG 0]
    have h0 : 0 ≤ ηi ^ 2 * Cm' * δ := by positivity
    have h0' : 0 ≤ ηi ^ 2 * (Cm' + Cf') / Real.sqrt W := by positivity
    nlinarith

end BlockBand.SourceProcess.TagBirth
