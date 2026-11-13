module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiTestMom
public import BlockBand.SourceProcess.FullSourceCovariance.TestBound
public import BlockBand.SourceProcess.FullSourceCovariance.IbpHyps23

/-!
# The centred product `E[Φ⁰F'⁰] = O(W⁻² + W⁻¹δ₀)`

Law `freshLaw W b`, strictly passive `X`, `E ∈ bulkInterval κ`, `δ₀ ≤ d₁`; constants uniform in
`W ≥ W₀`, `E`, `X` and the vectors. `Φ = phiSame x y'`, `F' = fForm x' y`.

* `eLpNorm_le_of_ae_mom`, `eLpNorm_sub_integral_le`: `L^p` bounds from a.s. bounds by a moment;
* **`phiCov_bulk hGA hLp`**: `Φ ∈ L²` and `‖E[Φ⁰F'⁰]‖ ≤ C(W⁻² + W⁻¹δ₀)‖x‖‖y‖‖x'‖‖y'‖`.
  Proof: `F'⁰ = x'*Δ⁰(Ry)` (`fForm_eq`), so `E[Φ⁰F'⁰]` is
  `test_bound` at `(x', Ry)` with the centred test `θ = Φ - EΦ` (`hasLayerDeriv_qForm`,
  integrability from `ibp_hyps23_bulk` with `X`-dependent crude constants). Its two inputs:
  `‖θ‖₄ ≤ 2CW⁻¹‖x‖‖y'‖` (`|Φ| ≤ W⁻¹‖x‖(1+B)·lamW‖y'‖` a.s.) and the crossed term
  `≤ 2CW⁻²‖x‖‖x'‖‖Ry‖‖y'‖` (`crossed_qDer_le`, `lam_mom`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem eLpNorm_le_of_ae_mom {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {g : Ω → ℝ}
    {p C K : ℝ} (hg : MomBd μ g p C) (hK : 0 ≤ K) (h : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ K * g ω) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (K * C) :=
  (eLpNorm_mono_ae_real hf h).trans (hg.const_mul hK).2

theorem eLpNorm_sub_integral_le [IsProbabilityMeasure μ] {f : Ω → ℂ}
    (hf : AEStronglyMeasurable f μ) {A : ℝ} (hA : 0 ≤ A) (h : eLpNorm f 4 μ ≤ ENNReal.ofReal A) :
    eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂μ) 4 μ ≤ ENNReal.ofReal (2 * A) := by
  have hm : ‖∫ ω', f ω' ∂μ‖ ≤ A :=
    norm_integral_le_of hf.aemeasurable hA ((eLpNorm_two_le_four f).trans h)
  have hc : eLpNorm (fun _ : Ω => ∫ ω', f ω' ∂μ) 4 μ ≤ ENNReal.ofReal A := by
    rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hm
  refine (eLpNorm_sub_le (f := f) (g := fun _ : Ω => ∫ ω', f ω' ∂μ) (by norm_num)).trans ?_
  rw [two_mul, ENNReal.ofReal_add hA hA]
  exact add_le_add h hc

end Generic

theorem continuous_qForm (b : ℝ) (u v : LayerSite W .oneBlockOnePort → ℂ) :
    Continuous (qForm (W := W) b u v) := by
  have e : qForm (W := W) b u v = fun G => star u ⬝ᵥ ((G * diagonal (physVar W b)) *ᵥ (G *ᵥ v)) :=
    funext fun G => qForm_eq b u v G
  rw [e]
  exact continuous_const.dotProduct ((continuous_id.matrix_mul continuous_const).matrix_mulVec
    (continuous_id.matrix_mulVec continuous_const))

theorem continuous_qDer (b : ℝ) (u v : LayerSite W .oneBlockOnePort → ℂ) (N : LayerMat W) :
    Continuous fun G : LayerMat W => qDer b u v G N := by
  have e : (fun G : LayerMat W => qDer b u v G N) = fun G =>
      -(star u ⬝ᵥ ((G * N * G * diagonal (physVar W b) * G) *ᵥ v)) -
        star u ⬝ᵥ ((G * diagonal (physVar W b) * G * N * G) *ᵥ v) :=
    funext fun G => qDer_apply b u v G N
  rw [e]
  refine (continuous_const.dotProduct ?_).neg.sub (continuous_const.dotProduct ?_)
  · exact ((((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id).matrix_mul
      continuous_const).matrix_mul continuous_id).matrix_mulVec continuous_const
  · exact ((((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id).matrix_mul
      continuous_const).matrix_mul continuous_id).matrix_mulVec continuous_const

theorem norm_mul5_le {A B C D F : LayerMat W} {L K : ℝ} (hA : ‖A‖ ≤ L) (hC : ‖C‖ ≤ L)
    (hF : ‖F‖ ≤ L) (hD : ‖D‖ ≤ K) (hK : 0 ≤ K) :
    ‖A * B * C * D * F‖ ≤ L ^ 3 * K * ‖B‖ := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hA
  calc ‖A * B * C * D * F‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖F‖ := by
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ L * ‖B‖ * L * K * L := by gcongr
    _ = L ^ 3 * K * ‖B‖ := by ring

/-- **The centred product of `Φ` and `F'`.** -/
theorem phiCov_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₁ C : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₁ →
      ∀ x y x' y' : Fin W → ℂ,
        MemLp (phiSame b E X x y') 2 (freshLaw W b) ∧
        ‖∫ ω, (phiSame b E X x y' ω - ∫ ω', phiSame b E X x y' ω' ∂freshLaw W b) *
            (fForm b E X x' y ω - ∫ ω', fForm b E X x' y ω' ∂freshLaw W b) ∂freshLaw W b‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) *
            (vecNorm x * vecNorm y * vecNorm x' * vecNorm y') := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨d₁, C₀, Wt, hd₁, hC₀, ht⟩ := test_bound hGA hLp hb0 hb hκ
  obtain ⟨Wi, hi⟩ := ibp_hyps23_bulk hA hb0 hb hκ
  obtain ⟨CΛ, Wl, hCΛ, hl⟩ := lam_mom hA hb0 hb hκ
  obtain ⟨Cr, Wr, -, hrf⟩ := rightForms_bulk hGA hLp hb0 hb hκ 2 one_le_two
  obtain ⟨Wp, hp4⟩ := LengthUniform.integrable_poly_bulk hA hb0 hb hκ 4
  have hηL := PathScalar.etaLow_pos (b := b) (by linarith) hκ
  set ηi := (PathScalar.etaLow b κ)⁻¹
  refine ⟨d₁, 2 * C₀ * CΛ * ηi + 2 * CΛ * ηi, max (max Wt Wi) (max (max Wl Wr) (max Wp 1)), hd₁,
    by positivity, fun W hW E hE X hY hδ x y x' y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWt, hWi⟩, ⟨hWl, hWr⟩, hWp, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hzE : ‖boundaryZ b E‖ + |E| ≤ 4 := by
    have := PathScalar.bulk_norm_z hb0 hb hκ hE
    have : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hWge : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hw0 : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hWr0.le
  have hw1 : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWge
  have hS : ‖diagonal (physVar W b)‖ ≤ (W : ℝ)⁻¹ := by
    have := norm_diag_physVar_le (W := W) hb0 hb; rwa [one_div] at this
  have hS1 : ‖diagonal (physVar W b)‖ ≤ 1 := hS.trans hw1
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have nx := vecNorm_nonneg x; have ny := vecNorm_nonneg y
  have nx' := vecNorm_nonneg x'; have ny' := vecNorm_nonneg y'
  have hRy : vecNorm (passiveResolvent b E X *ᵥ y) ≤ ηi * vecNorm y :=
    (vecNorm_mulVec_le' _ _).trans (mul_le_mul_of_nonneg_right ((norm_passiveResolvent_le hb0 hb
      h1 h2 hY.posSemidef).trans (CovarianceBulk.inv_etaZ_le_bulk hb hκ hE)) ny)
  have nRy := vecNorm_nonneg (passiveResolvent b E X *ᵥ y)
  have hB1 := fun ω => one_le_one_add_btFun b E X ω
  have hGB := fun ω => norm_gRes_le_one_add b E X ω
  have hKB := fun ω => norm_kHat_gRes_le b E X ω
  -- the test `θ = Φ - EΦ`
  have hΦq : ∀ ω, phiSame b E X x y' ω = qForm b ((kHat b E X)ᴴ *ᵥ physVec x)
      (kHat b E X *ᵥ physVec y') (gRes b E X ω) := phiSame_eq_qForm b E X x y'
  have hΦm : Measurable (phiSame b E X x y') := by
    have e : phiSame b E X x y' = fun ω => qForm b ((kHat b E X)ᴴ *ᵥ physVec x)
        (kHat b E X *ᵥ physVec y') (gRes b E X ω) := funext hΦq
    rw [e]; exact (continuous_qForm b _ _).measurable.comp hGm
  have hΦae : ∀ᵐ ω ∂freshLaw W b, ‖phiSame b E X x y' ω‖ ≤
      ((W : ℝ)⁻¹ * vecNorm x * vecNorm y') * ((1 + btFun b E X ω) * lamW b E X ω) := by
    filter_upwards [ae_norm_gK_le hη hzE hY] with ω hω
    rw [hΦq, qForm_eq_kHat]
    refine (norm_star_dotProduct_le _ _).trans ?_
    rw [vecNorm_physVec]
    have hm : ‖kHat b E X * gRes b E X ω * diagonal (physVar W b)‖ ≤
        (1 + btFun b E X ω) * (W : ℝ)⁻¹ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hKB ω) hS (norm_nonneg _) (by linarith [hB1 ω]))
    have hl0 := one_le_lamW b E X ω
    calc _ ≤ vecNorm x * (((1 + btFun b E X ω) * (W : ℝ)⁻¹) * (lamW b E X ω * vecNorm y')) := by
          refine mul_le_mul_of_nonneg_left ((vecNorm_mulVec_le' _ _).trans
            (mul_le_mul hm (hω y') (vecNorm_nonneg _) (mul_nonneg (by linarith [hB1 ω]) hw0))) nx
      _ = _ := by ring
  have hΦ4 : eLpNorm (phiSame b E X x y') 4 (freshLaw W b) ≤
      ENNReal.ofReal ((W : ℝ)⁻¹ * vecNorm x * vecNorm y' * CΛ) := by
    have := eLpNorm_le_of_ae_mom hΦm.aestronglyMeasurable (hl W hWl E hE X hY.posSemidef).1
      (by positivity) hΦae
    rwa [ENNReal.ofReal_ofNat] at this
  have hΦmem : MemLp (phiSame b E X x y') 4 (freshLaw W b) := lt_of_le_of_lt hΦ4 ENNReal.ofReal_lt_top
  have hΦ2 : MemLp (phiSame b E X x y') 2 (freshLaw W b) := hΦmem.mono_exponent (by norm_num)
  refine ⟨hΦ2, ?_⟩
  set mΦ := ∫ ω', phiSame b E X x y' ω' ∂freshLaw W b
  have hD := hasLayerDeriv_qForm (b := b) hη hY ((kHat b E X)ᴴ *ᵥ physVec x)
    (kHat b E X *ᵥ physVec y') mΦ
  have eθ : (fun ω => qForm b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω) - mΦ) = fun ω => phiSame b E X x y' ω - mΦ := funext fun ω => by rw [hΦq]
  have hθm : Measurable (fun ω => qForm b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω) - mΦ) := ((continuous_qForm b _ _).measurable.comp hGm).sub_const _
  have hθ0 : ∫ ω, (qForm b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω) - mΦ) ∂freshLaw W b = 0 := by
    rw [eθ, integral_sub (hΦ2.integrable one_le_two) (integrable_const _), integral_const]
    simp [mΦ]
  have hθ4 := eLpNorm_sub_integral_le hΦm.aestronglyMeasurable (by positivity) hΦ4
  rw [← eθ] at hθ4
  -- crude bounds for the integrability hypotheses
  set nu := vecNorm ((kHat b E X)ᴴ *ᵥ physVec x)
  set nv := vecNorm (kHat b E X *ᵥ physVec y')
  have hnu : 0 ≤ nu := vecNorm_nonneg _
  have hnv : 0 ≤ nv := vecNorm_nonneg _
  have hθB : ∀ ω, ‖qForm b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω) - mΦ‖ ≤ (nu * nv + ‖mΦ‖) * (1 + btFun b E X ω) ^ 2 := fun ω => by
    rw [qForm_eq]
    have hq : ‖star ((kHat b E X)ᴴ *ᵥ physVec x) ⬝ᵥ ((gRes b E X ω * diagonal (physVar W b)) *ᵥ
        (gRes b E X ω *ᵥ (kHat b E X *ᵥ physVec y')))‖ ≤ nu * nv * (1 + btFun b E X ω) ^ 2 := by
      refine (norm_star_dotProduct_le _ _).trans ?_
      have hGS : ‖gRes b E X ω * diagonal (physVar W b)‖ ≤ 1 + btFun b E X ω := by
        calc _ ≤ ‖gRes b E X ω‖ * ‖diagonal (physVar W b)‖ := Matrix.l2_opNorm_mul _ _
          _ ≤ (1 + btFun b E X ω) * 1 := mul_le_mul (hGB ω) hS1 (norm_nonneg _) (by linarith [hB1 ω])
          _ = _ := mul_one _
      calc _ ≤ nu * ((1 + btFun b E X ω) * ((1 + btFun b E X ω) * nv)) := by
            refine mul_le_mul_of_nonneg_left ((vecNorm_mulVec_le' _ _).trans (mul_le_mul hGS
              ((vecNorm_mulVec_le' _ _).trans (mul_le_mul_of_nonneg_right (hGB ω) hnv))
              (vecNorm_nonneg _) (by linarith [hB1 ω]))) hnu
        _ = _ := by ring
    have h1B : 1 ≤ (1 + btFun b E X ω) ^ 2 := one_le_pow₀ (hB1 ω)
    calc _ ≤ _ + ‖mΦ‖ := norm_sub_le _ _
      _ ≤ nu * nv * (1 + btFun b E X ω) ^ 2 + ‖mΦ‖ * (1 + btFun b E X ω) ^ 2 := by
          gcongr; exact le_mul_of_one_le_right (norm_nonneg _) h1B
      _ = _ := by ring
  have hDB : ∀ ω N, ‖qDer b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω) N‖ ≤ (2 * (nu * nv) * ‖N‖) * (1 + btFun b E X ω) ^ 3 := fun ω N => by
    rw [qDer_apply]
    have m1 := norm_mul5_le (B := N) (hGB ω) (hGB ω) (hGB ω) hS1 zero_le_one
    have m2 := norm_mul5_le (B := diagonal (physVar W b)) (C := gRes b E X ω) (D := N)
      (hGB ω) (hGB ω) (hGB ω) le_rfl (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    have f1 := norm_form_le ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω * N * gRes b E X ω * diagonal (physVar W b) * gRes b E X ω)
    have f2 := norm_form_le ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y')
      (gRes b E X ω * diagonal (physVar W b) * gRes b E X ω * N * gRes b E X ω)
    have hm2 : ‖gRes b E X ω * diagonal (physVar W b) * gRes b E X ω * N * gRes b E X ω‖ ≤
        (1 + btFun b E X ω) ^ 3 * ‖N‖ * 1 := by
      exact m2.trans (mul_le_mul_of_nonneg_left hS1 (mul_nonneg (pow_nonneg (by linarith [hB1 ω]) 3)
        (norm_nonneg _)))
    have hnn : 0 ≤ nu * nv := mul_nonneg hnu hnv
    calc _ ≤ nu * nv * ((1 + btFun b E X ω) ^ 3 * 1 * ‖N‖) +
          nu * nv * ((1 + btFun b E X ω) ^ 3 * ‖N‖ * 1) := add_le_add
            (f1.trans (mul_le_mul_of_nonneg_left m1 hnn)) (f2.trans (mul_le_mul_of_nonneg_left hm2 hnn))
      _ = _ := by ring
  have hDm : ∀ N, Measurable fun ω => qDer b ((kHat b E X)ᴴ *ᵥ physVec x)
      (kHat b E X *ᵥ physVec y') (gRes b E X ω) N := fun N =>
    (continuous_qDer b _ _ N).measurable.comp hGm
  obtain ⟨hL2, hI1, hI2, hI3, hFi⟩ := hi W hWi E hE X hY (physVec x')
    (physVec (passiveResolvent b E X *ᵥ y)) _ _ (by positivity) (by positivity) _ _ hθm hDm hθB hDB
  -- the crossed term
  have hXi : ∀ β γ, Integrable (fun ω => (star (physVec x') ᵥ* (kHat b E X * gRes b E X ω)) γ *
      qDer b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y') (gRes b E X ω)
        (Matrix.single β γ 1)) (freshLaw W b) := fun β γ => by
    refine hp4 W hWp E hE X hY.posSemidef _ (((continuous_letter_entry _ _ γ).mul
      (continuous_qDer b _ _ _)).measurable.comp hGm).aestronglyMeasurable
      (vecNorm (physVec x') * (2 * (nu * nv) * ‖Matrix.single β γ (1 : ℂ)‖)) fun ω => ?_
    rw [norm_mul]
    have e1 := (letter_entry_bounds b E X ω (physVec x') (physVec x') γ).1
    have e2 := hDB ω (Matrix.single β γ 1)
    calc _ ≤ (vecNorm (physVec x') * (1 + btFun b E X ω)) *
          ((2 * (nu * nv) * ‖Matrix.single β γ (1 : ℂ)‖) * (1 + btFun b E X ω) ^ 3) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (vecNorm_nonneg _) (by linarith [hB1 ω]))
      _ = _ := by ring
  have hcrEq := sum_sum_integral (μ := freshLaw W b)
    (fun β γ => physVec (passiveResolvent b E X *ᵥ y) β * siteVar W b β γ) _ hXi
  set Kc := 2 * (W : ℝ)⁻¹ ^ 2 * (vecNorm x * vecNorm x' * vecNorm (passiveResolvent b E X *ᵥ y) *
    vecNorm y')
  have hKc : 0 ≤ Kc := by positivity
  have hYae : ∀ᵐ ω ∂freshLaw W b, ‖∑ β, ∑ γ, physVec (passiveResolvent b E X *ᵥ y) β *
      siteVar W b β γ * ((star (physVec x') ᵥ* (kHat b E X * gRes b E X ω)) γ *
        qDer b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y') (gRes b E X ω)
          (Matrix.single β γ 1))‖ ≤
      Kc * ((1 + btFun b E X ω) ^ 2 * ((1 + btFun b E X ω) * lamW b E X ω)) := by
    filter_upwards [ae_norm_gK_le hη hzE hY] with ω hω
    refine (crossed_qDer_le hb0 hb (kHat b E X) (gRes b E X ω) (physVec x) (physVec x') _ _
      (physVec_port _) (hGB ω) (hKB ω)).trans ?_
    rw [vecNorm_physVec, vecNorm_physVec, vecNorm_physVec]
    have hL0 : 0 ≤ 1 + btFun b E X ω := by linarith [hB1 ω]
    have hc0 : 0 ≤ 2 * (W : ℝ)⁻¹ ^ 2 * (1 + btFun b E X ω) ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hL0 3)
    calc _ ≤ 2 * (W : ℝ)⁻¹ ^ 2 * (1 + btFun b E X ω) ^ 3 * (lamW b E X ω * vecNorm y') *
          (vecNorm x * vecNorm x' * vecNorm (passiveResolvent b E X *ᵥ y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hω y') hc0) (by positivity)
      _ = _ := by simp only [Kc]; ring
  have hYi : Integrable (fun ω => ∑ β, ∑ γ, physVec (passiveResolvent b E X *ᵥ y) β *
      siteVar W b β γ * ((star (physVec x') ᵥ* (kHat b E X * gRes b E X ω)) γ *
        qDer b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y') (gRes b E X ω)
          (Matrix.single β γ 1))) (freshLaw W b) :=
    integrable_finsetSum _ fun β _ => integrable_finsetSum _ fun γ _ => (hXi β γ).const_mul _
  have hY2 := eLpNorm_le_of_ae_mom hYi.aestronglyMeasurable (hl W hWl E hE X hY.posSemidef).2
    hKc hYae
  rw [ENNReal.ofReal_ofNat] at hY2
  have hcr : ‖∑ β, ∑ γ, physVec (passiveResolvent b E X *ᵥ y) β * siteVar W b β γ *
      ∫ ω, (star (physVec x') ᵥ* (kHat b E X * gRes b E X ω)) γ *
        qDer b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y') (gRes b E X ω)
          (Matrix.single β γ 1) ∂freshLaw W b‖ ≤ Kc * CΛ := by
    rw [hcrEq]; exact norm_integral_le_of hYi.aestronglyMeasurable.aemeasurable (by positivity) hY2
  -- the test bound at `(x', Ry)`
  have hT := ht W hWt E hE X hY hδ _ _ hD hθm x' (passiveResolvent b E X *ᵥ y) hL2 hI1 hI2 hI3
    hFi hθ0 _ (by positivity) hθ4 _ hcr
  obtain ⟨-, -, hmF, -⟩ := hrf W hWr E hE X hY.posSemidef x' y
  have hF' : ∀ ω, fForm b E X x' y ω - ∫ ω', fForm b E X x' y ω' ∂freshLaw W b =
      bilinear x' (freshDelta b E X ω - matrixExpect (freshLaw W b) (freshDelta b E X))
        (passiveResolvent b E X *ᵥ y) := fun ω => by
    rw [hmF, fForm_eq hη hY.posSemidef, PassiveCovariance.bilinear_sub]; ring
  rw [integral_congr_ae (Eventually.of_forall fun ω => by
    show _ = (qForm b ((kHat b E X)ᴴ *ᵥ physVec x) (kHat b E X *ᵥ physVec y') (gRes b E X ω) - mΦ) *
      bilinear x' (freshDelta b E X ω - matrixExpect (freshLaw W b) (freshDelta b E X))
        (passiveResolvent b E X *ᵥ y)
    rw [hF', hΦq])]
  refine hT.trans ?_
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  calc _ ≤ C₀ * (2 * ((W : ℝ)⁻¹ * vecNorm x * vecNorm y' * CΛ)) * (jetDistance0 b E X + (W : ℝ)⁻¹) *
        (vecNorm x' * (ηi * vecNorm y)) +
      2 * (W : ℝ)⁻¹ ^ 2 * (vecNorm x * vecNorm x' * (ηi * vecNorm y) * vecNorm y') * CΛ := by
        simp only [Kc]; gcongr
    _ = 2 * C₀ * CΛ * ηi * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) *
          (vecNorm x * vecNorm y * vecNorm x' * vecNorm y') +
        2 * CΛ * ηi * (W : ℝ)⁻¹ ^ 2 * (vecNorm x * vecNorm y * vecNorm x' * vecNorm y') := by ring
    _ ≤ 2 * C₀ * CΛ * ηi * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) *
          (vecNorm x * vecNorm y * vecNorm x' * vecNorm y') +
        2 * CΛ * ηi * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * jetDistance0 b E X) *
          (vecNorm x * vecNorm y * vecNorm x' * vecNorm y') := by
        gcongr; exact le_add_of_nonneg_right (mul_nonneg hw0 hδ0)
    _ = _ := by ring

end BlockBand.SourceProcess.FullSourceCovariance
