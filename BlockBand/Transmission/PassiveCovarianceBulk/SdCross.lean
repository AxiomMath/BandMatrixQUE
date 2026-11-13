module

public import BlockBand.Transmission.PassiveCovarianceBulk.SdBase
public import BlockBand.Transmission.PassiveCovariance.WordCov
public import BlockBand.Transmission.PassiveCovariance.SdCross

/-!
# Bulk-uniform word covariances and the crossed term

The general bilinear variance and covariance bounds for dressed words, the integrability of
dressed forms and the crossed term against `Q⁰`, with constants and `W₀` uniform in
`E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The general bilinear variance bound**: for strictly passive `X`, every
dressed word of length `≤ L_w` with insertions `≤ K_d` and all vectors,
`E|a*w c - E a*w c|² ≤ (C/W)‖a‖²‖c‖²`, uniformly.
Bulk-uniform copy of `wordForm_variance` (constants uniform on `bulkInterval κ`). -/
theorem wordForm_variance_bulk (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ a c : LayerSite W .oneBlockOnePort → ℂ,
        MemLp (fun ω => wordForm (kHat b E X) a c wd D (gRes b E X ω)) 2
            (layerLaw W b .oneBlockOnePort) ∧
        ∫ ω, ‖wordForm (kHat b E X) a c wd D (gRes b E X ω) -
            ∫ ω', wordForm (kHat b E X) a c wd D (gRes b E X ω') ∂layerLaw W b .oneBlockOnePort‖ ^ 2
          ∂layerLaw W b .oneBlockOnePort ≤ C / W * (vecNorm a ^ 2 * vecNorm c ^ 2) := by
  set q := Lw + 1
  set Kd' := max Kd 1
  obtain ⟨Cb, Wb, hCb, hmom⟩ := btFun_moment_bulk hA hb0 hb hκ (2 * (q : ℕ)) (by
    have : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    linarith)
  refine ⟨(Lw : ℝ) ^ 2 * 4 * (Kd' ^ q) ^ 2 * (Cb ^ q) ^ 2, max Wb 1, by positivity,
    fun W hW E hEκ X hX ℓ hℓ wd D hD a c => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hKd0 : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  have hq : ℓ + 1 ≤ q := by omega
  set μ := layerLaw W b .oneBlockOnePort
  set γ := gaussianProduct (coordVar W b)
  have hmap : μ = γ.map (coordMap W b) := freshLaw_eq_map W b
  have hmp : MeasurePreserving (coordMap W b) γ μ := ⟨measurable_coordMap W b, hmap.symm⟩
  set Kh := kHat b E X
  set F := fun ω => wordForm Kh a c wd D (gRes b E X ω)
  set f := fun ρ => wordForm Kh a c wd D (gCoord b E X ρ)
  have hfF : f = F ∘ coordMap W b := rfl
  set g := fun ω => (1 + btFun b E X ω) ^ q
  set Q := vecNorm a * vecNorm c
  have hQ : 0 ≤ Q := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by have := btFun_nonneg b E X ω; positivity
  have hgm : Measurable g := (measurable_const.add (measurable_btFun b E X)).pow_const _
  have hgL : eLpNorm g 2 μ ≤ ENNReal.ofReal (Cb ^ q) := by
    have h := eLpNorm_pow_le (μ := μ) (g := fun ω => 1 + btFun b E X ω)
      (fun ω => by have := btFun_nonneg b E X ω; positivity)
      (measurable_const.add (measurable_btFun b E X)).aestronglyMeasurable q (by omega)
      (hmom W (le_trans (le_max_left _ _) hW) E hEκ X hX.posSemidef)
    rwa [ENNReal.ofReal_pow hCb]
  have hgL2 : MemLp g 2 μ := lt_of_le_of_lt hgL ENNReal.ofReal_lt_top
  have hpt : ∀ ω, wBound Kh (gRes b E X ω) ≤ btFun b E X ω := wBound_kHat_le b E X
  have hFb : ∀ ω, ‖F ω‖ ≤ Kd' ^ q * Q * g ω := fun ω => by
    have hB := wBound_nonneg Kh (gRes b E X ω)
    have h := norm_bilinear_le a (wordVal Kh (gRes b E X ω) wd D) c
    have hw := norm_wordVal_le Kh (gRes b E X ω) hKd0 wd D hD
    have hpb := (pow_bound_le hKd0 hB hq).1
    have hpb' : Kd ^ (ℓ + 1) * wBound Kh (gRes b E X ω) ^ ℓ ≤ Kd' ^ q * g ω :=
      hpb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith [hpt ω]) _)
        (by positivity))
    calc ‖F ω‖ ≤ vecNorm a * ‖wordVal Kh (gRes b E X ω) wd D‖ * vecNorm c := h
      _ ≤ vecNorm a * (Kd' ^ q * g ω) * vecNorm c :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw.trans hpb') (vecNorm_nonneg _))
            (vecNorm_nonneg _)
      _ = Kd' ^ q * Q * g ω := by ring
  have hFm : Measurable F :=
    measurable_wordForm Kh a c wd D (measurable_layerRes (W := W) E (boundaryZ b E) X)
  have hFL2 : MemLp F 2 μ := (hgL2.const_mul (Kd' ^ q * Q)).of_le hFm.aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (by have := hg0 ω; positivity)]; exact hFb ω)
  refine ⟨hFL2, ?_⟩
  -- Poincaré in the coordinates
  have hfC := contDiff_wordForm hη hX Kh a c wd D
  have hfL2 : MemLp f 2 γ := hFL2.comp_measurePreserving hmp
  have hgc : MemLp (g ∘ coordMap W b) 2 γ := hgL2.comp_measurePreserving hmp
  have hpart : ∀ i, MemLp (fun ρ => fderiv ℝ f ρ (Pi.single i 1)) 2 γ := by
    intro i
    have hcont : Continuous fun ρ => fderiv ℝ f ρ (Pi.single i 1) :=
      (hfC.continuous_fderiv one_ne_zero).clm_apply continuous_const
    refine (hgc.const_mul (Lw * (Kd' ^ q * Q) * ‖layerDir b (Pi.single i 1)‖)).of_le
      hcont.aestronglyMeasurable (Eventually.of_forall fun ρ => ?_)
    have hB := wBound_nonneg Kh (gCoord b E X ρ)
    have h := wordForm_partial_le hη hX Kh a c hKd0 wd D hD ρ i
    have hpb := (pow_bound_le hKd0 hB hq).2
    have hpb' : Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1) ≤ Kd' ^ q * g (coordMap W b ρ) :=
      hpb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
        (by linarith [hpt (coordMap W b ρ)]) _) (by positivity))
    rw [Function.comp_apply, Real.norm_of_nonneg (by have := hg0 (coordMap W b ρ); positivity)]
    calc ‖fderiv ℝ f ρ (Pi.single i 1)‖
        ≤ ℓ * (Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1) * Q) *
          ‖layerDir b (Pi.single i 1)‖ := h
      _ ≤ Lw * (Kd' ^ q * g (coordMap W b ρ) * Q) * ‖layerDir b (Pi.single i 1)‖ := by
          gcongr
      _ = _ := by ring
  have hPo := hP (CoordW W) (coordVar W b) f (hfC.of_le le_rfl) hfL2 hpart
  -- transfer the left side
  have htrC : ∀ Φ : LayerSample W .oneBlockOnePort → ℂ, Measurable Φ →
      ∫ ω, Φ ω ∂μ = ∫ ρ, Φ (coordMap W b ρ) ∂γ := fun Φ hΦ => by
    rw [hmap, integral_map (measurable_coordMap W b).aemeasurable hΦ.aestronglyMeasurable]
  have htrR : ∀ Φ : LayerSample W .oneBlockOnePort → ℝ, Measurable Φ →
      ∫ ω, Φ ω ∂μ = ∫ ρ, Φ (coordMap W b ρ) ∂γ := fun Φ hΦ => by
    rw [hmap, integral_map (measurable_coordMap W b).aemeasurable hΦ.aestronglyMeasurable]
  have hlhs : ∫ ω, ‖F ω - ∫ ω', F ω' ∂μ‖ ^ 2 ∂μ = ∫ ρ, ‖f ρ - ∫ ρ', f ρ' ∂γ‖ ^ 2 ∂γ := by
    rw [htrC F hFm]
    exact htrR _ ((hFm.sub_const _).norm.pow_const 2)
  change ∫ ω, ‖F ω - ∫ ω', F ω' ∂μ‖ ^ 2 ∂μ ≤ _
  rw [hlhs]
  refine hPo.trans ?_
  -- bound the right side
  have hsq : ∀ i, Integrable (fun ρ => ‖fderiv ℝ f ρ (Pi.single i 1)‖ ^ 2) γ :=
    fun i => (hpart i).norm.integrable_sq
  have hgsq : Integrable (fun ρ => (g ∘ coordMap W b) ρ ^ 2) γ := hgc.integrable_sq
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (hsq i).const_mul _]
  calc ∫ ρ, ∑ i, (coordVar W b i : ℝ) * ‖fderiv ℝ f ρ (Pi.single i 1)‖ ^ 2 ∂γ
      ≤ ∫ ρ, (Lw : ℝ) ^ 2 * (4 / W) * (Kd' ^ q) ^ 2 * Q ^ 2 * (g ∘ coordMap W b) ρ ^ 2 ∂γ := by
        refine integral_mono (integrable_finsetSum _ fun i _ => (hsq i).const_mul _)
          (hgsq.const_mul _) fun ρ => ?_
        have hB := wBound_nonneg Kh (gCoord b E X ρ)
        have h := wordForm_gradSq_le hη hX hb0 hb hW1 Kh a c hKd0 wd D hD ρ
        have hpb := (pow_bound_le hKd0 hB hq).2
        have hpb' : Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1) ≤
            Kd' ^ q * g (coordMap W b ρ) :=
          hpb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
            (by linarith [hpt (coordMap W b ρ)]) _) (by positivity))
        have hsq' : (Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1)) ^ 2 ≤
            (Kd' ^ q * g (coordMap W b ρ)) ^ 2 := pow_le_pow_left₀ (by positivity) hpb' 2
        have hl : (ℓ : ℝ) ^ 2 ≤ (Lw : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast hℓ) 2
        have hW' : (0 : ℝ) ≤ 4 / W := by positivity
        refine h.trans ?_
        rw [Function.comp_apply]
        calc (ℓ : ℝ) ^ 2 * (4 / W) * (Kd ^ (ℓ + 1) * wBound Kh (gCoord b E X ρ) ^ (ℓ + 1)) ^ 2 *
              (vecNorm a ^ 2 * vecNorm c ^ 2)
            ≤ (Lw : ℝ) ^ 2 * (4 / W) * (Kd' ^ q * g (coordMap W b ρ)) ^ 2 *
              (vecNorm a ^ 2 * vecNorm c ^ 2) := by gcongr
          _ = _ := by simp only [Q]; ring
    _ = (Lw : ℝ) ^ 2 * (4 / W) * (Kd' ^ q) ^ 2 * Q ^ 2 * ∫ ω, g ω ^ 2 ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact (htrR _ (hgm.pow_const 2)).symm
    _ ≤ (Lw : ℝ) ^ 2 * (4 / W) * (Kd' ^ q) ^ 2 * Q ^ 2 * (Cb ^ q) ^ 2 := by
        gcongr
        exact integral_sq_le_of_eLpNorm hgm.aestronglyMeasurable (by positivity) hgL
    _ = _ := by simp only [Q]; field_simp

/-- **The general bilinear covariance bound**: for strictly
passive `X` and two bilinear forms `P = a₁*w₁c₁`, `Q = a₂*w₂c₂` of dressed words of length
`≤ L_w` (insertions `≤ K_d`), `|Cov(P, Q)| ≤ (C/W)‖a₁‖‖c₁‖‖a₂‖‖c₂‖`, uniformly in `X`, the
words and the vectors.
Bulk-uniform copy of `wordForm_covariance` (constants uniform on `bulkInterval κ`). -/
theorem wordForm_covariance_bulk (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
      ∀ ℓ₁ : ℕ, ℓ₁ ≤ Lw → ∀ (wd₁ : Fin ℓ₁ → Fin 4) (D₁ : Fin (ℓ₁ + 1) → LayerMat W),
      (∀ j, ‖D₁ j‖ ≤ Kd) →
      ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw → ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W),
      (∀ j, ‖D₂ j‖ ≤ Kd) → ∀ a₁ c₁ a₂ c₂ : LayerSite W .oneBlockOnePort → ℂ,
        let μ := layerLaw W b .oneBlockOnePort
        let P := fun ω => wordForm (kHat b E X) a₁ c₁ wd₁ D₁ (gRes b E X ω)
        let Q := fun ω => wordForm (kHat b E X) a₂ c₂ wd₂ D₂ (gRes b E X ω)
        Integrable (fun ω => (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ)) μ ∧
        ‖∫ ω, (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖ ≤
          C / W * (vecNorm a₁ * vecNorm c₁ * (vecNorm a₂ * vecNorm c₂)) := by
  obtain ⟨C, W₀, hC, hv⟩ := wordForm_variance_bulk hP hA hb0 hb hκ Lw Kd
  refine ⟨C, max W₀ 1, hC,
    fun W hW E hEκ X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ a₁ c₁ a₂ c₂ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ P Q
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  obtain ⟨hP2, hPv⟩ := hv W hW0 E hEκ X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ a₁ c₁
  obtain ⟨hQ2, hQv⟩ := hv W hW0 E hEκ X hX ℓ₂ hℓ₂ wd₂ D₂ hD₂ a₂ c₂
  have hu : MemLp (fun ω => P ω - ∫ ω', P ω' ∂μ) 2 μ := hP2.sub (memLp_const _)
  have hw : MemLp (fun ω => Q ω - ∫ ω', Q ω' ∂μ) 2 μ := hQ2.sub (memLp_const _)
  refine ⟨hu.integrable_mul hw, ?_⟩
  have hH := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (by simpa using hu) (by simpa using hw)
  have e2 : ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℝ) = x ^ 2 := fun x _ => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [e2 _ (norm_nonneg _)] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  set α := vecNorm a₁ * vecNorm c₁
  set β := vecNorm a₂ * vecNorm c₂
  have hα : 0 ≤ α := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  have hβ : 0 ≤ β := mul_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)
  have hs1 : Real.sqrt (∫ ω, ‖P ω - ∫ ω', P ω' ∂μ‖ ^ 2 ∂μ) ≤ Real.sqrt (C / W) * α := by
    rw [← Real.sqrt_sq hα, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by simpa [α, mul_pow] using hPv)
  have hs2 : Real.sqrt (∫ ω, ‖Q ω - ∫ ω', Q ω' ∂μ‖ ^ 2 ∂μ) ≤ Real.sqrt (C / W) * β := by
    rw [← Real.sqrt_sq hβ, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by simpa [β, mul_pow] using hQv)
  calc ‖∫ ω, (P ω - ∫ ω', P ω' ∂μ) * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ‖
      ≤ ∫ ω, ‖P ω - ∫ ω', P ω' ∂μ‖ * ‖Q ω - ∫ ω', Q ω' ∂μ‖ ∂μ := by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        congr 1; funext ω; exact norm_mul _ _
    _ ≤ Real.sqrt (C / W) * α * (Real.sqrt (C / W) * β) :=
        hH.trans (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity))
    _ = (Real.sqrt (C / W) * Real.sqrt (C / W)) * (α * β) := by ring
    _ = C / W * (α * β) := by rw [Real.mul_self_sqrt (by positivity)]

/-- Integrability of dressed forms, uniformly over passive inputs.
Bulk-uniform copy of `integrable_wordForm_unif` (constants uniform on `bulkInterval κ`). -/
theorem integrable_wordForm_unif_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ a c : LayerSite W .oneBlockOnePort → ℂ,
        Integrable (fun ω => wordForm (kHat b E X) a c wd D (gRes b E X ω))
          (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, hP⟩ := memLp_poly_bulk hA hb0 hb hκ (Lw + 1)
  refine ⟨W₀, fun W hW E hEκ X hX ℓ hℓ wd D hD a c => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  exact (hP W hW E hEκ X hX _ (measurable_wordForm _ a c wd D
    (measurable_layerRes E (boundaryZ b E) X)).aestronglyMeasurable _ (Lw + 1) le_rfl
    fun ω => (wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω).1).integrable one_le_two

/-- **The crossed term against `Q⁰`.**
Bulk-uniform copy of `crossTerm_Q` (constants uniform on `bulkInterval κ`). -/
theorem crossTerm_Q_bulk (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw →
      ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ x c u v : LayerSite W .oneBlockOnePort → ℂ,
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let M := fun ω => gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D
        let F1 := fun (k : Fin ℓ₂) (p : Fin 2) ω =>
          star x ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k) *ᵥ v)
        let F2 := fun (k : Fin ℓ₂) (p' : Fin 2) ω =>
          star u ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k * bProj p' * M ω) *ᵥ c)
        ‖(∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (x α) * (M ω *ᵥ c) γ *
            wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) ∂μ) +
          ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
            ((∫ ω, F1 k p ω ∂μ) * ∫ ω, F2 k p' ω ∂μ)‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v * (vecNorm u * vecNorm c)) := by
  set Kd' := max Kd 1 ^ 2
  obtain ⟨Cv, Wv, hCv, hcov⟩ := wordForm_covariance_bulk hP hA hb0 hb hκ (2 * Lw + 1) Kd'
  obtain ⟨Wi, hint⟩ := integrable_wordForm_unif_bulk hA hb0 hb hκ (2 * Lw + 1) Kd'
  obtain ⟨Wp, hpoly⟩ := memLp_poly_bulk hA hb0 hb hκ (2 * Lw + 3)
  refine ⟨Lw * 4 * Cv, max Wv (max Wi Wp), by positivity,
    fun W hW E hEκ X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ x c u v => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  intro μ Kh M F1 F2
  have hWv : Wv ≤ W := le_trans (le_max_left _ _) hW
  have hWi : Wi ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWp : Wp ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  have hK1 : 1 ≤ max Kd 1 := le_max_right _ _
  have hKK : max Kd 1 ≤ Kd' := by nlinarith
  have hD' : ∀ i, ‖D i‖ ≤ max Kd 1 := fun i => (hD i).trans (le_max_left _ _)
  have hD₂' : ∀ i, ‖D₂ i‖ ≤ max Kd 1 := fun i => (hD₂ i).trans (le_max_left _ _)
  -- the words of `F1`, `F2`
  have hw : ∀ k p p', Integrable (F1 k p) μ ∧ Integrable (F2 k p') μ ∧
      Integrable (fun ω => (F1 k p ω - ∫ ω', F1 k p ω' ∂μ) * (F2 k p' ω - ∫ ω', F2 k p' ω' ∂μ)) μ ∧
      ‖∫ ω, (F1 k p ω - ∫ ω', F1 k p ω' ∂μ) * (F2 k p' ω - ∫ ω', F2 k p' ω' ∂μ) ∂μ‖ ≤
        Cv / W * (vecNorm x * vecNorm v * (vecNorm u * vecNorm c)) := by
    intro k p p'
    obtain ⟨ℓA, wdA, DA, hlA, hFA, hGA⟩ := wordAlpha_word Kh ℓ₂ wd₂ D₂ k
    obtain ⟨ℓG, wdG, DG, hlG, hFG, hGG⟩ := wordGamma_word Kh ℓ₂ wd₂ D₂ k
    have hDA := hFA.norm_le hK1 hD₂'
    have hDG := hFG.norm_le hK1 hD₂'
    have hDS := norm_cons_one_le hK1 hD'
    have hcat := norm_catD_le hK1 (bProj p') (norm_bProj_le p') (Fin.cons 1 D) hDS ℓA DA hDA
    have hpre : ∀ i, ‖preD (bProj p) DG i‖ ≤ Kd' := fun i =>
      (norm_preD_le (norm_bProj_le p) hDG i).trans hKK
    have e1 : F1 k p = fun ω => wordForm Kh x v wdG (preD (bProj p) DG) (gRes b E X ω) := by
      funext ω; simp only [F1]; rw [hGG, wordForm, wordVal_preD]
    have e2 : F2 k p' = fun ω => wordForm Kh u c (catWd (Fin.cons (sideLetter adj) wd) ℓA wdA)
        (catD (bProj p') (Fin.cons 1 D) ℓA DA) (gRes b E X ω) := by
      funext ω
      simp only [F2, M]
      rw [hGA, wordForm, wordVal_cat, gSide_letter, letter_mul_wordVal]
    rw [e1, e2]
    obtain ⟨hi, hb'⟩ := hcov W hWv E hEκ X hX ℓG (by omega) wdG _ hpre (ℓ + 1 + ℓA) (by omega) _ _ hcat
      x v u c
    exact ⟨hint W hWi E hEκ X hX.posSemidef ℓG (by omega) wdG _ hpre x v,
      hint W hWi E hEκ X hX.posSemidef _ (by omega) _ _ hcat u c, hi, hb'⟩
  -- integrability of the site terms
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have cS := continuous_gSideOf (W := W) adj
  have cN := continuous_wordVal Kh wd D
  have pM : PolyBM (fun ω => 1 + btFun b E X ω) M (1 + (Lw + 1)) :=
    (polyBM_gSide b E X adj).mul (polyBM_wordVal b E X hKd hℓ wd D hD)
  have hfi : ∀ α γ, Integrable (fun ω => star (x α) * (M ω *ᵥ c) γ *
      wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) μ := by
    intro α γ
    have pD : PolyB (fun ω => 1 + btFun b E X ω)
        (fun ω => wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) (Lw + 1) :=
      ⟨Lw * max Kd 1 ^ (Lw + 1) * ‖(Matrix.single γ α 1 : LayerMat W)‖ * (vecNorm u * vecNorm v),
        by have := vecNorm_nonneg u; have := vecNorm_nonneg v; positivity,
        fun ω => (wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).2 _⟩
    obtain ⟨Cf, -, hCf⟩ := ((PolyB.const (star (x α))).mul (PolyB.vecEntry pM c γ)).mul pD
    have hm : Measurable fun ω => star (x α) * (M ω *ᵥ c) γ *
        wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) :=
      (measurable_const.mul (((continuous_apply γ).comp ((cS.matrix_mul cN).matrix_mulVec
        continuous_const)).measurable.comp hGm)).mul
        (measurable_wordFormDeriv Kh u v wd₂ D₂ hGm _)
    exact (hpoly W hWp E hEκ X hX.posSemidef _ hm.aestronglyMeasurable Cf _ (by omega) hCf).integrable
      one_le_two
  -- the pointwise block form
  have hpt : ∀ ω, ∑ α, ∑ γ, siteVar W b α γ * (star (x α) * (M ω *ᵥ c) γ *
      wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) =
      -∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' * (F1 k p ω * F2 k p' ω) := fun ω => by
    simp only [wordFormDeriv_apply]
    exact crossed_pt b x u v c (M ω) _ _
  have hsum : (∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (x α) * (M ω *ᵥ c) γ *
      wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) ∂μ) =
      -∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' * ∫ ω, F1 k p ω * F2 k p' ω ∂μ := by
    have hl : (∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (x α) * (M ω *ᵥ c) γ *
        wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) ∂μ) =
        ∫ ω, ∑ α, ∑ γ, siteVar W b α γ * (star (x α) * (M ω *ᵥ c) γ *
          wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) ∂μ := by
      rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun γ _ => (hfi α γ).const_mul _]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [integral_finsetSum _ fun γ _ => (hfi α γ).const_mul _]
      exact Finset.sum_congr rfl fun γ _ => (integral_const_mul _ _).symm
    have hFF : ∀ k p p', Integrable (fun ω => F1 k p ω * F2 k p' ω) μ := fun k p p' =>
      (integral_mul_sub_mul (hw k p p').1 (hw k p p').2.1 (hw k p p').2.2.1).1
    rw [hl]
    simp only [hpt]
    rw [integral_neg, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun p _ =>
      integrable_finsetSum _ fun p' _ => (hFF k p p').const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun p' _ => (hFF k p p').const_mul _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ fun p' _ => (hFF k p p').const_mul _]
    exact Finset.sum_congr rfl fun p' _ => integral_const_mul _ _
  rw [hsum, neg_add_eq_sub, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set P := vecNorm x * vecNorm v * (vecNorm u * vecNorm c)
  have hP0 : 0 ≤ P := by
    have := vecNorm_nonneg x; have := vecNorm_nonneg v; have := vecNorm_nonneg u
    have := vecNorm_nonneg c; positivity
  have hterm : ∀ k p p', ‖bVar W b p p' * ((∫ ω, F1 k p ω ∂μ) * ∫ ω, F2 k p' ω ∂μ) -
      bVar W b p p' * ∫ ω, F1 k p ω * F2 k p' ω ∂μ‖ ≤ Cv / (W : ℝ) ^ 2 * P := by
    intro k p p'
    rw [norm_sub_rev, ← mul_sub, norm_mul, (integral_mul_sub_mul (hw k p p').1 (hw k p p').2.1
      (hw k p p').2.2.1).2]
    calc _ ≤ 1 / W * (Cv / W * P) := mul_le_mul (norm_bVar_le b hb0.le hb p p') (hw k p p').2.2.2
          (norm_nonneg _) (by positivity)
      _ = Cv / (W : ℝ) ^ 2 * P := by
          rcases eq_or_lt_of_le hW0 with h0 | h0
          · rw [← h0]; simp
          · field_simp
  calc _ ≤ ∑ _k : Fin ℓ₂, 4 * (Cv / (W : ℝ) ^ 2 * P) := by
        refine Finset.sum_le_sum fun k _ => ?_
        try simp only [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans ?_
        calc _ ≤ ∑ _p : Fin 2, 2 * (Cv / (W : ℝ) ^ 2 * P) := by
              refine Finset.sum_le_sum fun p _ => ?_
              refine (norm_sum_le _ _).trans ?_
              calc _ ≤ ∑ _p' : Fin 2, Cv / (W : ℝ) ^ 2 * P :=
                    Finset.sum_le_sum fun p' _ => hterm k p p'
                _ = _ := by simp
          _ = _ := by simp; ring
    _ = ℓ₂ * (4 * (Cv / (W : ℝ) ^ 2 * P)) := by simp
    _ ≤ Lw * (4 * (Cv / (W : ℝ) ^ 2 * P)) := by gcongr
    _ = _ := by ring

end BlockBand.Transmission.CovarianceBulk
