module

public import BlockBand.Transmission.SourceMixing.ExpansionAlg

/-!
# The exact one-step expansion of `E[V𝒢·w(𝒢)]` (Gaussian integration by parts)

Hypothesis `PassiveLayer.PassiveBoundsStatement` (`moments`), at `w = z_∂`. Law
`layerLaw W b .oneBlockOnePort`, deterministic strictly passive `X` (`Y ≻ 0`), fixed `b ∈ (0, 1/2)`,
`E ∈ (-2, 2)`.

For a dressed word `w` (`wordVal`, length `≤ L_w`, insertions `≤ K_d`) with derivative
factors `α_j, γ_j` and the layer Gaussian part `V = layerLin ω`, entrywise:

`E[(V𝒢w)_{ργ}] = -E[s_ρ(𝒢)(𝒢w)_{ργ}] - Σ_j E[s_ρ(𝒢α_j)(γ_j)_{ργ}]`,

where `s_ρ(F) = (1-2b)⟨F₁₁⟩ + b⟨F₂₂⟩` on physical rows and `b⟨F₁₁⟩` on port rows
(`⟨·⟩ = blkTr`). This is `replica_wordForm` summed over the intermediate index
(`expansion_phys`, `expansion_port`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Integrability of the replica integrands, uniformly. -/
theorem expansion_integrable (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (a c : LayerSite W .oneBlockOnePort → ℂ) (σ τ ρ β : LayerSite W .oneBlockOnePort),
        Integrable (fun ω => gRes b E X ω σ β *
            wordFormDeriv (kHat b E X) a c wd D (gRes b E X ω) (Matrix.single τ ρ 1) -
          wordForm (kHat b E X) a c wd D (gRes b E X ω) * (gRes b E X ω σ σ * gRes b E X ω ρ β))
          (layerLaw W b .oneBlockOnePort) ∧
        MemLp (fun ω => gRes b E X ω σ β * wordForm (kHat b E X) a c wd D (gRes b E X ω)) 2
          (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₁, hI⟩ := integrable_poly hA hb0 hb h1 h2 (Lw + 3)
  obtain ⟨W₂, hm⟩ := memLp_two_of_poly hA hb0 hb h1 h2 (Lw + 3) (by omega)
  refine ⟨max W₁ W₂, fun W hW X hX ℓ hℓ wd D hD a c σ τ ρ β => ?_⟩
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  set Kh := kHat b E X
  set K1 := max Kd 1 ^ (Lw + 1)
  set Q := vecNorm a * vecNorm c
  have hQ : 0 ≤ Q := mul_nonneg (vecNorm_nonneg a) (vecNorm_nonneg c)
  have hK1 : 0 ≤ K1 := by positivity
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hent : ∀ γ δ, Measurable fun ω => gRes b E X ω γ δ := fun γ δ => hGm.eval_matrix
  have hΨm : Measurable fun ω => wordForm Kh a c wd D (gRes b E X ω) :=
    measurable_wordForm Kh a c wd D hGm
  have hDm : ∀ N, Measurable fun ω => wordFormDeriv Kh a c wd D (gRes b E X ω) N := fun N => by
    have hc : Continuous fun G : LayerMat W => wordFormDeriv Kh a c wd D G N := by
      simp only [wordFormDeriv_apply]
      refine (continuous_finsetSum _ fun j _ => ?_).neg
      exact continuous_const.dotProduct ((((continuous_wordAlpha Kh _ wd D j).mul
        continuous_const).mul (continuous_wordGamma Kh _ wd D j)).matrix_mulVec continuous_const)
    exact hc.measurable.comp hGm
  have hbt : ∀ ω, 1 ≤ 1 + btFun b E X ω := one_le_one_add_btFun b E X
  have he : ∀ ω γ δ, ‖gRes b E X ω γ δ‖ ≤ 1 + btFun b E X ω := fun ω γ δ =>
    (norm_entry_le' (gRes b E X ω) γ δ).trans (norm_gRes_le_btFun b E X ω)
  have hpow : ∀ ω k, k ≤ Lw + 3 → (1 + btFun b E X ω) ^ k ≤ (1 + btFun b E X ω) ^ (Lw + 3) :=
    fun ω k hk => pow_le_pow_right₀ (hbt ω) hk
  constructor
  · refine hI W (le_trans (le_max_left _ _) hW) X hX _ (((hent σ β).mul (hDm _)).sub
      (hΨm.mul ((hent σ σ).mul (hent ρ β)))).aestronglyMeasurable
      (Lw * K1 * ‖(Matrix.single τ ρ (1 : ℂ) : LayerMat W)‖ * Q + K1 * Q) fun ω => ?_
    obtain ⟨hb1, hb2⟩ := wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω
    have hb2' := hb2 (Matrix.single τ ρ 1)
    have h0 := hbt ω
    have hn : 0 ≤ ‖(Matrix.single τ ρ (1 : ℂ) : LayerMat W)‖ := norm_nonneg _
    have hp1 := hpow ω (Lw + 2) (by omega)
    have hp2 := hpow ω (Lw + 3) le_rfl
    set t := 1 + btFun b E X ω
    calc ‖gRes b E X ω σ β * wordFormDeriv Kh a c wd D (gRes b E X ω) (Matrix.single τ ρ 1) -
          wordForm Kh a c wd D (gRes b E X ω) * (gRes b E X ω σ σ * gRes b E X ω ρ β)‖
        ≤ ‖gRes b E X ω σ β‖ * ‖wordFormDeriv Kh a c wd D (gRes b E X ω) (Matrix.single τ ρ 1)‖ +
            ‖wordForm Kh a c wd D (gRes b E X ω)‖ *
              (‖gRes b E X ω σ σ‖ * ‖gRes b E X ω ρ β‖) := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ t * (Lw * K1 * ‖(Matrix.single τ ρ (1 : ℂ) : LayerMat W)‖ * Q * t ^ (Lw + 1)) +
            K1 * Q * t ^ (Lw + 1) * (t * t) := by
          gcongr
          · exact he ω σ β
          · exact he ω σ σ
          · exact he ω ρ β
      _ = Lw * K1 * ‖(Matrix.single τ ρ (1 : ℂ) : LayerMat W)‖ * Q * t ^ (Lw + 2) +
            K1 * Q * t ^ (Lw + 3) := by ring
      _ ≤ Lw * K1 * ‖(Matrix.single τ ρ (1 : ℂ) : LayerMat W)‖ * Q * t ^ (Lw + 3) +
            K1 * Q * t ^ (Lw + 3) := by gcongr
      _ = _ := by ring
  · refine hm W (le_trans (le_max_right _ _) hW) X hX _ ((hent σ β).mul hΨm).aestronglyMeasurable
      (K1 * Q) fun ω => ?_
    have hb1 := (wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω).1
    rw [norm_mul]
    have h0 := hbt ω
    calc ‖gRes b E X ω σ β‖ * ‖wordForm Kh a c wd D (gRes b E X ω)‖
        ≤ (1 + btFun b E X ω) * (K1 * Q * (1 + btFun b E X ω) ^ (Lw + 1)) :=
          mul_le_mul (he ω σ β) hb1 (norm_nonneg _) (by linarith)
      _ = K1 * Q * (1 + btFun b E X ω) ^ (Lw + 2) := by ring
      _ ≤ K1 * Q * (1 + btFun b E X ω) ^ (Lw + 3) :=
          mul_le_mul_of_nonneg_left (hpow ω _ (by omega)) (by positivity)

/-- The physical-row coefficient `s(F) = (1-2b)⟨F₁₁⟩ + b⟨F₂₂⟩`. -/
def sPhys (b : ℝ) (F : LayerMat W) : ℂ := ((1 - 2 * b : ℝ) : ℂ) * blkTr F 0 + (b : ℂ) * blkTr F 1

/-- The port-row coefficient `s(F) = b⟨F₁₁⟩`. -/
def sPort (b : ℝ) (F : LayerMat W) : ℂ := (b : ℂ) * blkTr F 0

/-- The one-step expansion on physical rows. -/
theorem expansion_phys (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (x : Fin W) (γ : LayerSite W .oneBlockOnePort),
        ∫ ω, (layerLin ω * gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) (phys x) γ
            ∂layerLaw W b .oneBlockOnePort =
          ∫ ω, (-(sPhys b (gRes b E X ω) *
              (gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) (phys x) γ) -
            ∑ j, sPhys b (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) *
              wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j (phys x) γ)
            ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨W₁, hR⟩ := replica_wordForm hA hb0 hb h1 h2 Lw Kd
  obtain ⟨W₂, hInt⟩ := expansion_integrable hA hb0 hb h1 h2 Lw Kd
  refine ⟨max (max W₁ W₂) 1, fun W hW X hX ℓ hℓ wd D hD x γ => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWc : (W : ℂ) ≠ 0 := by
    have : 1 ≤ W := le_trans (le_max_right _ _) hW
    exact_mod_cast (show 0 < W by omega).ne'
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set G := gRes b E X
  set Ψ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ := fun β ω =>
    wordForm Kh (Pi.single β 1) (Pi.single γ 1) wd D (G ω)
  have e1 : ∀ ω, (layerLin ω * G ω * wordVal Kh (G ω) wd D) (phys x) γ =
      ∑ β, (layerLin ω * G ω) (phys x) β * Ψ β ω := fun ω => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun β _ => congrArg _ (wordForm_single _ _ _ _ _ _).symm
  have hVΨ : ∀ β, Integrable (fun ω => (layerLin ω * G ω) (phys x) β * Ψ β ω) μ := by
    intro β
    have hL2 := fun σ => (hInt W hW2 X hX.posSemidef ℓ hℓ wd D hD (Pi.single β 1)
      (Pi.single γ 1) σ σ σ β).2
    have e : (fun ω => (layerLin ω * G ω) (phys x) β * Ψ β ω) = fun ω =>
        ∑ y, ω.1 0 x y * (G ω (phys y) β * Ψ β ω) + ∑ y, ω.2 0 0 x y * (G ω (port y) β * Ψ β ω) := by
      funext ω; rw [layerLin_mul_phys, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1 <;> exact Finset.sum_congr rfl fun y _ => by ring
    rw [e]
    exact (integrable_finsetSum _ fun y _ => (memLp_layer_A b x y).integrable_mul (hL2 _)).add
      (integrable_finsetSum _ fun y _ => (memLp_layer_B b x y).integrable_mul (hL2 _))
  set g : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort →
      LayerSample W .oneBlockOnePort → ℂ := fun β σ ω =>
    G ω σ β * wordFormDeriv Kh (Pi.single β 1) (Pi.single γ 1) wd D (G ω) (Matrix.single σ (phys x) 1) -
      Ψ β ω * (G ω σ σ * G ω (phys x) β)
  have hg : ∀ β σ, Integrable (g β σ) μ := fun β σ =>
    (hInt W hW2 X hX.posSemidef ℓ hℓ wd D hD (Pi.single β 1) (Pi.single γ 1) σ σ (phys x) β).1
  have hrep : ∀ β, ∫ ω, (layerLin ω * G ω) (phys x) β * Ψ β ω ∂μ =
      ∫ ω, (∑ y, (gueVar W b : ℂ) * g β (phys y) ω + ∑ y, (ginVar W b : ℂ) * g β (port y) ω) ∂μ := by
    intro β
    rw [(hR W hW1 X hX ℓ hℓ wd D hD (Pi.single β 1) (Pi.single γ 1) x β).1,
      integral_add (integrable_finsetSum _ fun y _ => (hg β _).const_mul _)
        (integrable_finsetSum _ fun y _ => (hg β _).const_mul _),
      integral_finsetSum _ fun y _ => (hg β _).const_mul _,
      integral_finsetSum _ fun y _ => (hg β _).const_mul _]
    simp only [integral_const_mul]
    rfl
  rw [integral_congr_ae (Eventually.of_forall e1), integral_finsetSum _ fun β _ => hVΨ β]
  simp only [hrep]
  have hsum : ∀ β, Integrable (fun ω => ∑ y, (gueVar W b : ℂ) * g β (phys y) ω +
      ∑ y, (ginVar W b : ℂ) * g β (port y) ω) μ := fun β =>
    (integrable_finsetSum _ fun y _ => (hg β _).const_mul _).add
      (integrable_finsetSum _ fun y _ => (hg β _).const_mul _)
  rw [← integral_finsetSum _ fun β _ => hsum β]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Finset.sum_add_distrib, g, Ψ]
  rw [pointwise_family Kh (G ω) wd D phys (phys x) γ, pointwise_family Kh (G ω) wd D port (phys x) γ]
  simp only [sum_phys_eq, sum_port_eq, gueVar_cast hb, ginVar_cast hb0, sPhys]
  have k1 : ∀ t : ℂ, ((1 - 2 * b : ℝ) : ℂ) / W * (W * t) = ((1 - 2 * b : ℝ) : ℂ) * t := fun t => by
    field_simp
  have k2 : ∀ t : ℂ, (b : ℂ) / W * (W * t) = (b : ℂ) * t := fun t => by field_simp
  simp only [k1, k2, add_mul, Finset.sum_add_distrib]
  ring

/-- The one-step expansion on port rows. -/
theorem expansion_port (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (x : Fin W) (γ : LayerSite W .oneBlockOnePort),
        ∫ ω, (layerLin ω * gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) (port x) γ
            ∂layerLaw W b .oneBlockOnePort =
          ∫ ω, (-(sPort b (gRes b E X ω) *
              (gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) (port x) γ) -
            ∑ j, sPort b (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) *
              wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j (port x) γ)
            ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨W₁, hR⟩ := replica_wordForm hA hb0 hb h1 h2 Lw Kd
  obtain ⟨W₂, hInt⟩ := expansion_integrable hA hb0 hb h1 h2 Lw Kd
  refine ⟨max (max W₁ W₂) 1, fun W hW X hX ℓ hℓ wd D hD x γ => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWc : (W : ℂ) ≠ 0 := by
    have : 1 ≤ W := le_trans (le_max_right _ _) hW
    exact_mod_cast (show 0 < W by omega).ne'
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set G := gRes b E X
  set Ψ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ := fun β ω =>
    wordForm Kh (Pi.single β 1) (Pi.single γ 1) wd D (G ω)
  have e1 : ∀ ω, (layerLin ω * G ω * wordVal Kh (G ω) wd D) (port x) γ =
      ∑ β, (layerLin ω * G ω) (port x) β * Ψ β ω := fun ω => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun β _ => congrArg _ (wordForm_single _ _ _ _ _ _).symm
  have hVΨ : ∀ β, Integrable (fun ω => (layerLin ω * G ω) (port x) β * Ψ β ω) μ := by
    intro β
    have hL2 := fun σ => (hInt W hW2 X hX.posSemidef ℓ hℓ wd D hD (Pi.single β 1)
      (Pi.single γ 1) σ σ σ β).2
    have e : (fun ω => (layerLin ω * G ω) (port x) β * Ψ β ω) = fun ω =>
        ∑ y, star (ω.2 0 0 y x) * (G ω (phys y) β * Ψ β ω) := by
      funext ω; rw [layerLin_mul_port, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun y _ => (memLp_layer_B b y x).star.integrable_mul (hL2 _)
  set g : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort →
      LayerSample W .oneBlockOnePort → ℂ := fun β σ ω =>
    G ω σ β * wordFormDeriv Kh (Pi.single β 1) (Pi.single γ 1) wd D (G ω) (Matrix.single σ (port x) 1) -
      Ψ β ω * (G ω σ σ * G ω (port x) β)
  have hg : ∀ β σ, Integrable (g β σ) μ := fun β σ =>
    (hInt W hW2 X hX.posSemidef ℓ hℓ wd D hD (Pi.single β 1) (Pi.single γ 1) σ σ (port x) β).1
  have hrep : ∀ β, ∫ ω, (layerLin ω * G ω) (port x) β * Ψ β ω ∂μ =
      ∫ ω, (∑ y, (ginVar W b : ℂ) * g β (phys y) ω) ∂μ := by
    intro β
    rw [(hR W hW1 X hX ℓ hℓ wd D hD (Pi.single β 1) (Pi.single γ 1) x β).2,
      integral_finsetSum _ fun y _ => (hg β _).const_mul _]
    simp only [integral_const_mul]
    rfl
  rw [integral_congr_ae (Eventually.of_forall e1), integral_finsetSum _ fun β _ => hVΨ β]
  simp only [hrep]
  have hsum : ∀ β, Integrable (fun ω => ∑ y, (ginVar W b : ℂ) * g β (phys y) ω) μ := fun β =>
    integrable_finsetSum _ fun y _ => (hg β _).const_mul _
  rw [← integral_finsetSum _ fun β _ => hsum β]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [g, Ψ]
  rw [pointwise_family Kh (G ω) wd D phys (port x) γ]
  simp only [sum_phys_eq, ginVar_cast hb0, sPort]
  have k2 : ∀ t : ℂ, (b : ℂ) / W * (W * t) = (b : ℂ) * t := fun t => by field_simp
  simp only [k2]
  ring

end BlockBand.Transmission.SourceMixing
