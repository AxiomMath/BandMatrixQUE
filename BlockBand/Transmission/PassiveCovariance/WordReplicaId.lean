module

public import BlockBand.Transmission.PassiveCovariance.WordReplica

/-!
# The exact replica identity for every dressed test functional, integrability discharged

* `replica_wordForm`, physical rows:
  `E[(V𝒢)_{xβ}Ψ] = Σ_y (c/W)E[𝒢_{yβ}DΨ(E_{yx}) - Ψ𝒢_{yy}𝒢_{xβ}] + Σ_y (b/W)E[𝒢_{ȳβ}DΨ(E_{ȳx}) - Ψ𝒢_{ȳȳ}𝒢_{xβ}]`;
* port rows: `E[(V𝒢)_{x̄β}Ψ] = Σ_y (b/W)E[𝒢_{yβ}DΨ(E_{yx̄}) - Ψ𝒢_{yy}𝒢_{x̄β}]`.

`DΨ = wordFormDeriv` (`WordReplica`). These are `replica_identity_phys` and `replica_identity_port` with the
three integrability hypotheses proved from `moments` (all integrands are `≤ K(1 + B)^{L_w+3}`).
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

theorem norm_gRes_le_btFun (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖gRes b E X ω‖ ≤ 1 + btFun b E X ω := by
  unfold btFun; have := norm_nonneg (kG11 E (boundaryZ b E) X ω)
  have := norm_nonneg (lAt E (boundaryZ b E) X ω); have := norm_nonneg (gRes b E X ω); linarith

theorem one_le_one_add_btFun (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : 1 ≤ 1 + btFun b E X ω := by
  have := btFun_nonneg b E X ω; linarith

/-- Pointwise bounds of `Ψ` and `DΨ` by powers of `1 + B`. -/
theorem wordForm_poly_bounds (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd)
    {Lw ℓ : ℕ} (hℓ : ℓ ≤ Lw) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W)
    (hD : ∀ j, ‖D j‖ ≤ Kd) (a c : LayerSite W .oneBlockOnePort → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖wordForm (kHat b E X) a c wd D (gRes b E X ω)‖ ≤
        max Kd 1 ^ (Lw + 1) * (vecNorm a * vecNorm c) * (1 + btFun b E X ω) ^ (Lw + 1) ∧
      ∀ N, ‖wordFormDeriv (kHat b E X) a c wd D (gRes b E X ω) N‖ ≤
        Lw * max Kd 1 ^ (Lw + 1) * ‖N‖ * (vecNorm a * vecNorm c) *
          (1 + btFun b E X ω) ^ (Lw + 1) := by
  set G := gRes b E X ω
  set Kh := kHat b E X
  have hB := wBound_nonneg Kh G
  have hbt := wBound_kHat_le b E X ω
  have hq : ℓ + 1 ≤ Lw + 1 := by omega
  have hpb := pow_bound_le hKd hB hq
  have hmono : (1 + wBound Kh G) ^ (Lw + 1) ≤ (1 + btFun b E X ω) ^ (Lw + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hQ := mul_nonneg (vecNorm_nonneg a) (vecNorm_nonneg c)
  have hK1 : 0 ≤ max Kd 1 ^ (Lw + 1) := by positivity
  refine ⟨?_, fun N => ?_⟩
  · have h := norm_bilinear_le a (wordVal Kh G wd D) c
    have hw := norm_wordVal_le Kh G hKd wd D hD
    have h1 : ‖wordVal Kh G wd D‖ ≤ max Kd 1 ^ (Lw + 1) * (1 + btFun b E X ω) ^ (Lw + 1) :=
      hw.trans (hpb.1.trans (mul_le_mul_of_nonneg_left hmono hK1))
    calc ‖wordForm Kh a c wd D G‖ ≤ vecNorm a * ‖wordVal Kh G wd D‖ * vecNorm c := h
      _ ≤ vecNorm a * (max Kd 1 ^ (Lw + 1) * (1 + btFun b E X ω) ^ (Lw + 1)) * vecNorm c :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (vecNorm_nonneg _))
            (vecNorm_nonneg _)
      _ = _ := by ring
  · have h := norm_wordFormDeriv_le Kh a c hKd wd D hD G N
    have h1 : Kd ^ (ℓ + 1) * wBound Kh G ^ (ℓ + 1) ≤
        max Kd 1 ^ (Lw + 1) * (1 + btFun b E X ω) ^ (Lw + 1) :=
      hpb.2.trans (mul_le_mul_of_nonneg_left hmono hK1)
    have hl : (ℓ : ℝ) ≤ Lw := by exact_mod_cast hℓ
    refine h.trans ?_
    have h0 : 0 ≤ Kd ^ (ℓ + 1) * wBound Kh G ^ (ℓ + 1) := by positivity
    calc (ℓ : ℝ) * (Kd ^ (ℓ + 1) * wBound Kh G ^ (ℓ + 1)) * ‖N‖ * (vecNorm a * vecNorm c)
        ≤ Lw * (max Kd 1 ^ (Lw + 1) * (1 + btFun b E X ω) ^ (Lw + 1)) * ‖N‖ *
            (vecNorm a * vecNorm c) := by gcongr
      _ = _ := by ring

/-- **The replica identity for dressed test functionals** (both row types), with every
integrability hypothesis discharged by the `moments` clause of `PassiveBoundsStatement`. -/
theorem replica_wordForm (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (a c : LayerSite W .oneBlockOnePort → ℂ) (x : Fin W)
      (β : LayerSite W .oneBlockOnePort),
        (∫ ω, (layerLin ω * gRes b E X ω) (phys x) β *
            wordForm (kHat b E X) a c wd D (gRes b E X ω) ∂layerLaw W b .oneBlockOnePort =
          ∑ y, (gueVar W b : ℂ) * ∫ ω, (gRes b E X ω (phys y) β *
              wordFormDeriv (kHat b E X) a c wd D (gRes b E X ω) (Matrix.single (phys y) (phys x) 1) -
              wordForm (kHat b E X) a c wd D (gRes b E X ω) *
                (gRes b E X ω (phys y) (phys y) * gRes b E X ω (phys x) β))
              ∂layerLaw W b .oneBlockOnePort +
          ∑ y, (ginVar W b : ℂ) * ∫ ω, (gRes b E X ω (port y) β *
              wordFormDeriv (kHat b E X) a c wd D (gRes b E X ω) (Matrix.single (port y) (phys x) 1) -
              wordForm (kHat b E X) a c wd D (gRes b E X ω) *
                (gRes b E X ω (port y) (port y) * gRes b E X ω (phys x) β))
              ∂layerLaw W b .oneBlockOnePort) ∧
        (∫ ω, (layerLin ω * gRes b E X ω) (port x) β *
            wordForm (kHat b E X) a c wd D (gRes b E X ω) ∂layerLaw W b .oneBlockOnePort =
          ∑ y, (ginVar W b : ℂ) * ∫ ω, (gRes b E X ω (phys y) β *
              wordFormDeriv (kHat b E X) a c wd D (gRes b E X ω) (Matrix.single (phys y) (port x) 1) -
              wordForm (kHat b E X) a c wd D (gRes b E X ω) *
                (gRes b E X ω (phys y) (phys y) * gRes b E X ω (port x) β))
              ∂layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, hm⟩ := memLp_two_of_poly hA hb0 hb h1 h2 (Lw + 3) (by omega)
  refine ⟨W₀, fun W hW X hX ℓ hℓ wd D hD a c x β => ?_⟩
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set Q := vecNorm a * vecNorm c
  set K1 := max Kd 1 ^ (Lw + 1)
  have hQ : 0 ≤ Q := mul_nonneg (vecNorm_nonneg a) (vecNorm_nonneg c)
  have hK1 : 0 ≤ K1 := by positivity
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hΨm : Measurable fun ω => wordForm Kh a c wd D (gRes b E X ω) :=
    measurable_wordForm Kh a c wd D hGm
  have hDm : ∀ N, Measurable fun ω => wordFormDeriv Kh a c wd D (gRes b E X ω) N := fun N => by
    have hc : Continuous fun G : LayerMat W => wordFormDeriv Kh a c wd D G N := by
      simp only [wordFormDeriv_apply]
      refine (continuous_finsetSum _ fun j _ => ?_).neg
      exact continuous_const.dotProduct ((((continuous_wordAlpha Kh _ wd D j).mul
        continuous_const).mul (continuous_wordGamma Kh _ wd D j)).matrix_mulVec continuous_const)
    exact hc.measurable.comp hGm
  have hent : ∀ γ δ, Measurable fun ω => gRes b E X ω γ δ := fun γ δ => hGm.eval_matrix
  have hpow : ∀ ω k, k ≤ Lw + 3 → (1 + btFun b E X ω) ^ k ≤ (1 + btFun b E X ω) ^ (Lw + 3) :=
    fun ω k hk => pow_le_pow_right₀ (one_le_one_add_btFun b E X ω) hk
  have hbt0 : ∀ ω, 0 ≤ 1 + btFun b E X ω := fun ω => by have := btFun_nonneg b E X ω; linarith
  have hL2 : ∀ γ δ, MemLp (fun ω => gRes b E X ω γ δ * wordForm Kh a c wd D (gRes b E X ω)) 2 μ := by
    intro γ δ
    refine hm W hW X hX.posSemidef _ ((hent γ δ).mul hΨm).aestronglyMeasurable (K1 * Q) fun ω => ?_
    have hb1 := (wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω).1
    rw [norm_mul]
    have he := (norm_entry_le' (gRes b E X ω) γ δ).trans (norm_gRes_le_btFun b E X ω)
    have := hbt0 ω
    calc ‖gRes b E X ω γ δ‖ * ‖wordForm Kh a c wd D (gRes b E X ω)‖
        ≤ (1 + btFun b E X ω) * (K1 * Q * (1 + btFun b E X ω) ^ (Lw + 1)) :=
          mul_le_mul he hb1 (norm_nonneg _) this
      _ = K1 * Q * (1 + btFun b E X ω) ^ (Lw + 2) := by ring
      _ ≤ K1 * Q * (1 + btFun b E X ω) ^ (Lw + 3) :=
          mul_le_mul_of_nonneg_left (hpow ω _ (by omega)) (by positivity)
  have hI1 : ∀ γ N, Integrable (fun ω => gRes b E X ω γ β *
      wordFormDeriv Kh a c wd D (gRes b E X ω) N) μ := by
    intro γ N
    refine (hm W hW X hX.posSemidef _ ((hent γ β).mul (hDm N)).aestronglyMeasurable
      (Lw * K1 * ‖N‖ * Q) fun ω => ?_).integrable one_le_two
    have hb2 := (wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω).2 N
    simp only [Pi.mul_apply]
    rw [norm_mul]
    have he := (norm_entry_le' (gRes b E X ω) γ β).trans (norm_gRes_le_btFun b E X ω)
    have := hbt0 ω
    calc ‖gRes b E X ω γ β‖ * ‖wordFormDeriv Kh a c wd D (gRes b E X ω) N‖
        ≤ (1 + btFun b E X ω) * (Lw * K1 * ‖N‖ * Q * (1 + btFun b E X ω) ^ (Lw + 1)) :=
          mul_le_mul he hb2 (norm_nonneg _) this
      _ = Lw * K1 * ‖N‖ * Q * (1 + btFun b E X ω) ^ (Lw + 2) := by ring
      _ ≤ Lw * K1 * ‖N‖ * Q * (1 + btFun b E X ω) ^ (Lw + 3) :=
          mul_le_mul_of_nonneg_left (hpow ω _ (by omega)) (by positivity)
  have hI2 : ∀ γ N, Integrable (fun ω => wordForm Kh a c wd D (gRes b E X ω) *
      (gRes b E X ω * N * gRes b E X ω) γ β) μ := by
    intro γ N
    refine (hm W hW X hX.posSemidef _ (hΨm.mul ((hGm.mul_const N).mul hGm).eval_matrix).aestronglyMeasurable
      (K1 * Q * ‖N‖) fun ω => ?_).integrable one_le_two
    have hb1 := (wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω).1
    simp only [Pi.mul_apply]
    rw [norm_mul]
    have hG := norm_gRes_le_btFun b E X ω
    have he : ‖(gRes b E X ω * N * gRes b E X ω) γ β‖ ≤ ‖N‖ * (1 + btFun b E X ω) ^ 2 :=
      (norm_entry_le' _ γ β).trans ((norm_mul_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hG 2) (norm_nonneg _)))
    have := hbt0 ω
    calc ‖wordForm Kh a c wd D (gRes b E X ω)‖ * ‖(gRes b E X ω * N * gRes b E X ω) γ β‖
        ≤ (K1 * Q * (1 + btFun b E X ω) ^ (Lw + 1)) * (‖N‖ * (1 + btFun b E X ω) ^ 2) :=
          mul_le_mul hb1 he (norm_nonneg _) (by positivity)
      _ = K1 * Q * ‖N‖ * (1 + btFun b E X ω) ^ (Lw + 3) := by ring
  have hdΨ := hasLayerDeriv_wordForm hη hX Kh a c wd D
  exact ⟨replica_identity_phys b E X hη hX hdΨ hΨm x β (fun γ => hL2 γ β) hI1 hI2,
    replica_identity_port b E X hη hX hdΨ hΨm x β (fun γ => hL2 γ β) hI1 hI2⟩

end BlockBand.Transmission.PassiveCovariance
