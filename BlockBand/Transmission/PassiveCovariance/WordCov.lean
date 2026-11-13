module

public import BlockBand.Transmission.PassiveCovariance.WordVariance

/-!
# `Var(a*w c) ≤ (C/W)‖a‖²‖c‖²` and `|Cov(P, Q)| ≤ C/W` for dressed words

For strictly passive inputs, bilinear forms of dressed words have variance `O(1/W)` (Poincaré
inequality with the gradient bound of `WordGrad`) and hence covariances `O(1/W)`.

* `wordForm_variance (hP : GaussianPoincare) (hA : PassiveBoundsStatement)`;
* `wordForm_covariance` (Cauchy–Schwarz).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem measurable_wordForm (Kh : LayerMat W) (a c : LayerSite W .oneBlockOnePort → ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) {G : LayerSample W .oneBlockOnePort → LayerMat W}
    (hG : Measurable G) : Measurable fun ω => wordForm Kh a c wd D (G ω) := by
  have hc : Continuous fun H : LayerMat W => wordForm Kh a c wd D H :=
    (formL a c).continuous.comp (contDiff_wordVal Kh contDiff_id wd D).continuous
  exact hc.measurable.comp hG

/-- `K_d^{m+1}B^{m} ≤ K_d'^{q}(1+B)^{q}` and `K_d^{m+1}B^{m+1} ≤ K_d'^{q}(1+B)^{q}` for `m < q`. -/
theorem pow_bound_le {Kd B : ℝ} (hKd : 0 ≤ Kd) (hB : 0 ≤ B) {ℓ q : ℕ} (hℓ : ℓ + 1 ≤ q) :
    Kd ^ (ℓ + 1) * B ^ ℓ ≤ max Kd 1 ^ q * (1 + B) ^ q ∧
      Kd ^ (ℓ + 1) * B ^ (ℓ + 1) ≤ max Kd 1 ^ q * (1 + B) ^ q := by
  have hK1 : 1 ≤ max Kd 1 := le_max_right _ _
  have hk : Kd ^ (ℓ + 1) ≤ max Kd 1 ^ q :=
    (pow_le_pow_left₀ hKd (le_max_left _ _) _).trans (pow_le_pow_right₀ hK1 hℓ)
  have hb1 : B ^ (ℓ + 1) ≤ (1 + B) ^ q :=
    (pow_le_pow_left₀ hB (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hℓ)
  have hb0 : B ^ ℓ ≤ (1 + B) ^ q :=
    (pow_le_pow_left₀ hB (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  exact ⟨mul_le_mul hk hb0 (by positivity) (by positivity),
    mul_le_mul hk hb1 (by positivity) (by positivity)⟩

/-- **The general bilinear variance bound**: for strictly passive `X`, every
dressed word of length `≤ L_w` with insertions `≤ K_d` and all vectors,
`E|a*w c - E a*w c|² ≤ (C/W)‖a‖²‖c‖²`, uniformly. -/
theorem wordForm_variance (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨Cb, Wb, hCb, hmom⟩ := btFun_moment hA hb0 hb h1 h2 (2 * (q : ℕ)) (by
    have : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    linarith)
  refine ⟨(Lw : ℝ) ^ 2 * 4 * (Kd' ^ q) ^ 2 * (Cb ^ q) ^ 2, max Wb 1, by positivity,
    fun W hW X hX ℓ hℓ wd D hD a c => ?_⟩
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
      (hmom W (le_trans (le_max_left _ _) hW) X hX.posSemidef)
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
words and the vectors. -/
theorem wordForm_covariance (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₀, hC, hv⟩ := wordForm_variance hP hA hb0 hb h1 h2 Lw Kd
  refine ⟨C, max W₀ 1, hC, fun W hW X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ ℓ₂ hℓ₂ wd₂ D₂ hD₂ a₁ c₁ a₂ c₂ => ?_⟩
  intro μ P Q
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  obtain ⟨hP2, hPv⟩ := hv W hW0 X hX ℓ₁ hℓ₁ wd₁ D₁ hD₁ a₁ c₁
  obtain ⟨hQ2, hQv⟩ := hv W hW0 X hX ℓ₂ hℓ₂ wd₂ D₂ hD₂ a₂ c₂
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

end BlockBand.Transmission.PassiveCovariance
