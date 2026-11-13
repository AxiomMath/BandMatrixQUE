module

public import BlockBand.Transmission.PassiveCovarianceBulk.SdBase
public import BlockBand.Transmission.PassiveCovariance.SdVector
public import BlockBand.Transmission.PassiveCovariance.SdExpand

/-!
# Bulk-uniform Schwinger–Dyson vector expansion

The vector Schwinger–Dyson identity for dressed words (`sd_vector`) and the first-letter
expansion (`sd_expand`), with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
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

/-- **The vector Schwinger–Dyson identity** for dressed words.
Bulk-uniform copy of `sd_vector` (constants uniform on `bulkInterval κ`). -/
theorem sd_vector_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw m : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (a c : LayerSite W .oneBlockOnePort → ℂ)
      (Ψ : LayerSample W .oneBlockOnePort → ℂ)
      (DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ) (K : ℝ),
      HasLayerDeriv Ψ DΨ → Measurable Ψ → (∀ N, Measurable fun ω => DΨ ω N) →
      (∀ ω, ‖Ψ ω‖ ≤ K * (1 + btFun b E X ω) ^ m) →
      (∀ ω N, ‖DΨ ω N‖ ≤ K * ‖N‖ * (1 + btFun b E X ω) ^ m) →
        ∫ ω, star a ⬝ᵥ ((layerLin ω * gSide b E X adj ω *
            wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) * Ψ ω ∂layerLaw W b .oneBlockOnePort =
          ∫ ω, (∑ α, ∑ γ, siteVar W b α γ * (star (a α) *
              ((gSide b E X adj ω * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) γ *
                DΨ ω (Matrix.single γ α 1)) -
            ((∑ j, star a ⬝ᵥ ((sdiag b (gSide b E X adj ω *
                wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) *
                wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ c)) +
              star a ⬝ᵥ ((sdiag b (gSide b E X adj ω) * gSide b E X adj ω *
                wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c)) * Ψ ω)
            ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨W₀, hP⟩ := memLp_poly_bulk hA hb0 hb hκ (Lw + m + 3)
  refine ⟨W₀, fun W hW E hEκ X hX ℓ hℓ wd D hD a c Ψ DΨ K hΨ hΨm hDm hΨb hDb => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set Bt : LayerSample W .oneBlockOnePort → ℝ := fun ω => 1 + btFun b E X ω
  have hB1 : ∀ ω, 1 ≤ Bt ω := one_le_one_add_btFun b E X
  have hB0 : ∀ ω, 0 ≤ Bt ω := fun ω => zero_le_one.trans (hB1 ω)
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hSm := measurable_gSide b E X adj
  have hent : ∀ γ δ, Measurable fun ω => gSide b E X adj ω γ δ := fun γ δ => hSm.eval_matrix
  have hGb : ∀ ω γ δ, ‖gSide b E X adj ω γ δ‖ ≤ Bt ω := fun ω γ δ =>
    (norm_entry_le' _ γ δ).trans ((norm_gSide b E X adj ω).trans_le (norm_gRes_le_btFun b E X ω))
  have hGNG : ∀ ω (N : LayerMat W) γ δ,
      ‖(gSide b E X adj ω * N * gSide b E X adj ω) γ δ‖ ≤ ‖N‖ * Bt ω ^ 2 := fun ω N γ δ => by
    refine (norm_entry_le' _ γ δ).trans ((Matrix.l2_opNorm_mul _ _).trans ?_)
    have hG := (norm_gSide b E X adj ω).trans_le (norm_gRes_le_btFun b E X ω)
    calc ‖gSide b E X adj ω * N‖ * ‖gSide b E X adj ω‖ ≤ ‖gSide b E X adj ω‖ * ‖N‖ * ‖gSide b E X adj ω‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ Bt ω * ‖N‖ * Bt ω := mul_le_mul (mul_le_mul_of_nonneg_right hG (norm_nonneg _)) hG
          (norm_nonneg _) (mul_nonneg (hB0 ω) (norm_nonneg _))
      _ = ‖N‖ * Bt ω ^ 2 := by ring
  set K1 := max Kd 1 ^ (Lw + 1)
  set Cφ := K1 * vecNorm c
  have hCφ : 0 ≤ Cφ := mul_nonneg (by positivity) (vecNorm_nonneg c)
  have hK : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hΨb 0)
    exact nonneg_of_mul_nonneg_left h (by have := hB1 0; positivity)
  set Φ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ := fun β ω =>
    wordForm Kh (Pi.single β 1) c wd D (gRes b E X ω)
  set DΦ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ :=
    fun β ω => wordFormDeriv Kh (Pi.single β 1) c wd D (gRes b E X ω)
  have hΦb : ∀ β ω, ‖Φ β ω‖ ≤ Cφ * Bt ω ^ (Lw + 1) := fun β ω => by
    have h := (wordForm_poly_bounds b E X hKd hℓ wd D hD (Pi.single β 1) c ω).1
    rw [vecNorm_single_one, one_mul] at h
    exact h.trans (le_of_eq (by ring))
  have hDΦb : ∀ β ω N, ‖DΦ β ω N‖ ≤ Lw * Cφ * ‖N‖ * Bt ω ^ (Lw + 1) := fun β ω N => by
    have h := (wordForm_poly_bounds b E X hKd hℓ wd D hD (Pi.single β 1) c ω).2 N
    rw [vecNorm_single_one, one_mul] at h
    exact h.trans (le_of_eq (by ring))
  set Ψβ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ :=
    fun β ω => Φ β ω * Ψ ω
  set DΨβ : LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ :=
    fun β ω => Φ β ω • DΨ ω + Ψ ω • DΦ β ω
  have hΨβd : ∀ β, HasLayerDeriv (Ψβ β) (DΨβ β) := fun β =>
    (hasLayerDeriv_wordForm hη hX Kh _ c wd D).mul hΨ
  have hΦm : ∀ β, Measurable (Φ β) := fun β => measurable_wordForm Kh _ c wd D hGm
  have hΨβm : ∀ β, Measurable (Ψβ β) := fun β => (hΦm β).mul hΨm
  have hDΦm : ∀ β N, Measurable fun ω => DΦ β ω N := fun β N =>
    measurable_wordFormDeriv Kh _ c wd D hGm N
  have hW' := hP W hW E hEκ X hX.posSemidef
  have hBp : ∀ ω k, 0 ≤ Bt ω ^ k := fun ω k => pow_nonneg (hB0 ω) k
  have hk : ∀ k, k ≤ Lw + m + 3 → ∀ ω, Bt ω ^ k ≤ Bt ω ^ (Lw + m + 3) := fun k hk ω =>
    pow_le_pow_right₀ (hB1 ω) hk
  have hL2 : ∀ β γ, MemLp (fun ω => gSide b E X adj ω γ β * Ψβ β ω) 2 μ := fun β γ => by
    refine hW' (fun ω => gSide b E X adj ω γ β * Ψβ β ω) ((hent γ β).mul (hΨβm β)).aestronglyMeasurable
      (Cφ * K) (Lw + m + 2) (by omega) fun ω => ?_
    simp only [Ψβ]
    rw [norm_mul, norm_mul]
    calc ‖gSide b E X adj ω γ β‖ * (‖Φ β ω‖ * ‖Ψ ω‖) ≤ Bt ω * (Cφ * Bt ω ^ (Lw + 1) * (K * Bt ω ^ m)) :=
          mul_le_mul (hGb ω γ β) (mul_le_mul (hΦb β ω) (hΨb ω) (norm_nonneg _)
            (mul_nonneg hCφ (hBp ω _))) (by positivity)
            (hB0 ω)
      _ = Cφ * K * Bt ω ^ (Lw + m + 2) := by ring
  have hI1 : ∀ β γ N, Integrable (fun ω => gSide b E X adj ω γ β * DΨβ β ω N) μ := fun β γ N => by
    refine (hW' (fun ω => gSide b E X adj ω γ β * DΨβ β ω N)
      ((hent γ β).mul (((hΦm β).mul (hDm N)).add (hΨm.mul (hDΦm β N)))).aestronglyMeasurable
      ((1 + Lw) * Cφ * K * ‖N‖) (Lw + m + 2) (by omega) fun ω => ?_).integrable one_le_two
    simp only [DΨβ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [norm_mul]
    have e1 := norm_add_le (Φ β ω * DΨ ω N) (Ψ ω * DΦ β ω N)
    rw [norm_mul, norm_mul] at e1
    have hb1 : ‖Φ β ω‖ * ‖DΨ ω N‖ ≤ Cφ * Bt ω ^ (Lw + 1) * (K * ‖N‖ * Bt ω ^ m) :=
      mul_le_mul (hΦb β ω) (hDb ω N) (norm_nonneg _) (mul_nonneg hCφ (hBp ω _))
    have hb2 : ‖Ψ ω‖ * ‖DΦ β ω N‖ ≤ K * Bt ω ^ m * (Lw * Cφ * ‖N‖ * Bt ω ^ (Lw + 1)) :=
      mul_le_mul (hΨb ω) (hDΦb β ω N) (norm_nonneg _) (mul_nonneg hK (hBp ω _))
    calc ‖gSide b E X adj ω γ β‖ * ‖Φ β ω * DΨ ω N + Ψ ω * DΦ β ω N‖
        ≤ Bt ω * (Cφ * Bt ω ^ (Lw + 1) * (K * ‖N‖ * Bt ω ^ m) +
            K * Bt ω ^ m * (Lw * Cφ * ‖N‖ * Bt ω ^ (Lw + 1))) :=
          mul_le_mul (hGb ω γ β) (e1.trans (add_le_add hb1 hb2)) (norm_nonneg _) (hB0 ω)
      _ = (1 + Lw) * Cφ * K * ‖N‖ * Bt ω ^ (Lw + m + 2) := by ring
  have hI2 : ∀ β γ N, Integrable (fun ω => Ψβ β ω * (gSide b E X adj ω * N * gSide b E X adj ω) γ β) μ :=
    fun β γ N => by
    refine (hW' (fun ω => Ψβ β ω * (gSide b E X adj ω * N * gSide b E X adj ω) γ β)
      ((hΨβm β).mul ((hSm.mul_const N).mul hSm).eval_matrix).aestronglyMeasurable
      (Cφ * K * ‖N‖) (Lw + m + 3) le_rfl fun ω => ?_).integrable one_le_two
    simp only [Ψβ]
    rw [norm_mul, norm_mul]
    calc ‖Φ β ω‖ * ‖Ψ ω‖ * ‖(gSide b E X adj ω * N * gSide b E X adj ω) γ β‖
        ≤ Cφ * Bt ω ^ (Lw + 1) * (K * Bt ω ^ m) * (‖N‖ * Bt ω ^ 2) :=
          mul_le_mul (mul_le_mul (hΦb β ω) (hΨb ω) (norm_nonneg _) (mul_nonneg hCφ (hBp ω _)))
            (hGNG ω N γ β) (norm_nonneg _)
            (mul_nonneg (mul_nonneg hCφ (hBp ω _)) (mul_nonneg hK (hBp ω _)))
      _ = Cφ * K * ‖N‖ * Bt ω ^ (Lw + m + 3) := by ring
  -- the site identities
  have hsite := fun α β => replica_site_gen b (gSide b E X adj) (hasLayerDeriv_gSide hη hX adj)
    hSm (hΨβd β) (hΨβm β) α β (hL2 β) (hI1 β) (hI2 β)
  set Y : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort →
      LayerSite W .oneBlockOnePort → LayerSample W .oneBlockOnePort → ℂ :=
    fun α β γ ω => gSide b E X adj ω γ β * DΨβ β ω (Matrix.single γ α 1) -
      Ψβ β ω * (gSide b E X adj ω γ γ * gSide b E X adj ω α β)
  have hY : ∀ α β γ, Integrable (Y α β γ) μ := fun α β γ => by
    have e : (fun ω => Ψβ β ω * (gSide b E X adj ω γ γ * gSide b E X adj ω α β)) =
        fun ω => Ψβ β ω * (gSide b E X adj ω * (Matrix.single γ α (1 : ℂ) : LayerMat W) *
          gSide b E X adj ω) γ β := by
      funext ω; rw [mul_single_mul_apply]
    have h2 := hI2 β γ (Matrix.single γ α 1)
    rw [← e] at h2
    exact (hI1 β γ _).sub h2
  -- pointwise expansion of the left side
  have hpt : ∀ ω, star a ⬝ᵥ ((layerLin ω * gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) *
      Ψ ω = ∑ α, ∑ β, star (a α) * ((layerLin ω * gSide b E X adj ω) α β * Ψβ β ω) := by
    intro ω
    rw [← mulVec_mulVec]
    simp only [Ψβ, Φ, wordForm_single, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum,
      Pi.star_apply]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun x _ => by ring
  have hint : ∀ α β, Integrable (fun ω => star (a α) *
      ((layerLin ω * gSide b E X adj ω) α β * Ψβ β ω)) μ := fun α β => (hsite α β).1.const_mul _
  have hYs : ∀ α β, Integrable (fun ω => star (a α) * ∑ γ, siteVar W b α γ * Y α β γ ω) μ :=
    fun α β => (integrable_finsetSum _ fun γ _ => (hY α β γ).const_mul _).const_mul _
  calc ∫ ω, star a ⬝ᵥ ((layerLin ω * gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D) *ᵥ c) * Ψ ω ∂μ
      = ∑ α, ∑ β, ∫ ω, star (a α) * ((layerLin ω * gSide b E X adj ω) α β * Ψβ β ω) ∂μ := by
        rw [integral_congr_ae (Eventually.of_forall hpt),
          integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint α β]
        exact Finset.sum_congr rfl fun α _ => integral_finsetSum _ fun β _ => hint α β
    _ = ∑ α, ∑ β, ∫ ω, star (a α) * ∑ γ, siteVar W b α γ * Y α β γ ω ∂μ := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [integral_const_mul, integral_const_mul, (hsite α β).2,
          integral_finsetSum _ fun γ _ => (hY α β γ).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun γ _ => (integral_const_mul _ _).symm
    _ = ∫ ω, ∑ α, ∑ β, star (a α) * ∑ γ, siteVar W b α γ * Y α β γ ω ∂μ := by
        rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hYs α β]
        exact Finset.sum_congr rfl fun α _ => (integral_finsetSum _ fun β _ => hYs α β).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Y, DΨβ, Ψβ, Φ, DΦ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          wordForm_single, wordFormDeriv_single]
        exact sd_algebra (siteVar W b) (gSide b E X adj ω) (wordVal Kh (gRes b E X ω) wd D)
          (wordAlpha Kh (gRes b E X ω) ℓ wd D) (wordGamma Kh (gRes b E X ω) ℓ wd D) a c (Ψ ω) (DΨ ω)

/-- **The first-letter expansion.**
Bulk-uniform copy of `sd_expand` (constants uniform on `bulkInterval κ`). -/
theorem sd_expand_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (Lw m : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) → ∀ (P₀ : LayerMat W) (x c : LayerSite W .oneBlockOnePort → ℂ)
      (Ψ : LayerSample W .oneBlockOnePort → ℂ)
      (DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ) (K : ℝ),
      HasLayerDeriv Ψ DΨ → Measurable Ψ → (∀ N, Measurable fun ω => DΨ ω N) →
      (∀ ω, ‖Ψ ω‖ ≤ K * (1 + btFun b E X ω) ^ m) →
      (∀ ω N, ‖DΨ ω N‖ ≤ K * ‖N‖ * (1 + btFun b E X ω) ^ m) →
        ∫ ω, star x ⬝ᵥ ((P₀ * gSide b E X adj ω * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) *
            Ψ ω ∂layerLaw W b .oneBlockOnePort =
          ∫ ω, star x ⬝ᵥ ((P₀ * mbarSide b E X adj * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) *
            Ψ ω ∂layerLaw W b .oneBlockOnePort +
          ∫ ω, star ((P₀ * mbarSide b E X adj)ᴴ *ᵥ x) ⬝ᵥ (((sdiag b (gSide b E X adj ω) -
              sbarSide b E X adj) * gSide b E X adj ω *
              wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) * Ψ ω ∂layerLaw W b .oneBlockOnePort +
          ∑ j, ∫ ω, star ((P₀ * mbarSide b E X adj)ᴴ *ᵥ x) ⬝ᵥ ((sdiag b (gSide b E X adj ω *
              wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) *
              wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) *ᵥ c) * Ψ ω
              ∂layerLaw W b .oneBlockOnePort -
          ∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (((P₀ * mbarSide b E X adj)ᴴ *ᵥ x) α) *
              ((gSide b E X adj ω * wordVal (kHat b E X) (gRes b E X ω) wd D) *ᵥ c) γ *
              DΨ ω (Matrix.single γ α 1) ∂layerLaw W b .oneBlockOnePort := by
  obtain ⟨W₁, hsd⟩ := sd_vector_bulk hA hb0 hb hκ Lw m Kd adj
  obtain ⟨W₂, hP⟩ := memLp_poly_bulk hA hb0 hb hκ (Lw + m + 3)
  obtain ⟨Cd, W₃, hdi⟩ := dressed_inverse_bulk hA hb0 hb hκ
  refine ⟨max W₁ (max W₂ W₃),
    fun W hW E hEκ X hX ℓ hℓ wd D hD P₀ x c Ψ DΨ K hΨ hΨm hDm hΨb hDb => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  have hDu := (hdi W hW3 E hEκ X hX).1
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set Bt : LayerSample W .oneBlockOnePort → ℝ := fun ω => 1 + btFun b E X ω
  have hB1 : ∀ ω, 1 ≤ Bt ω := one_le_one_add_btFun b E X
  set Mb := mbarSide b E X adj
  set Sb := sbarSide b E X adj
  set xc := (P₀ * Mb)ᴴ *ᵥ x
  set N : LayerSample W .oneBlockOnePort → LayerMat W := fun ω => wordVal Kh (gRes b E X ω) wd D
  set 𝔊 := gSide b E X adj
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hc : ∀ f : LayerMat W → ℂ, Continuous f → Measurable fun ω => f (gRes b E X ω) :=
    fun f hf => hf.measurable.comp hGm
  have hK : 0 ≤ K := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hΨb 0))
    (pow_pos (lt_of_lt_of_le zero_lt_one (hB1 0)) _)
  have hI : ∀ F : LayerSample W .oneBlockOnePort → ℂ, Measurable F → ∀ k, k ≤ Lw + m + 3 →
      PolyB Bt F k → Integrable F μ := fun F hF k hk hp => by
    obtain ⟨C, -, hb'⟩ := hp
    exact (hP W hW2 E hEκ X hX.posSemidef F hF.aestronglyMeasurable C k hk hb').integrable one_le_two
  have pG := polyBM_gSide b E X adj
  have pN : PolyBM Bt N (Lw + 1) := polyBM_wordVal b E X hKd hℓ wd D hD
  have pΨ : PolyB Bt Ψ m := ⟨K, hK, hΨb⟩
  have pD : ∀ N', PolyB Bt (fun ω => DΨ ω N') m := fun N' =>
    ⟨K * ‖N'‖, mul_nonneg hK (norm_nonneg _), fun ω => hDb ω N'⟩
  have cS := continuous_gSideOf (W := W) adj
  have cN := continuous_wordVal Kh wd D
  -- the three explicit pieces and the `V` piece
  set LHSi := fun ω => star x ⬝ᵥ ((P₀ * 𝔊 ω * N ω) *ᵥ c) * Ψ ω
  set TMi := fun ω => star x ⬝ᵥ ((P₀ * Mb * N ω) *ᵥ c) * Ψ ω
  set TSi := fun ω => star xc ⬝ᵥ ((Sb * 𝔊 ω * N ω) *ᵥ c) * Ψ ω
  set TVi := fun ω => star xc ⬝ᵥ ((layerLin ω * 𝔊 ω * N ω) *ᵥ c) * Ψ ω
  have iL : Integrable LHSi μ := hI _ ((hc _ ((continuous_bil x c).comp
    ((continuous_const.matrix_mul cS).matrix_mul cN))).mul hΨm) _ (by omega)
    (PolyB.mul (PolyB.bilin ((PolyBM.mul (PolyBM.const P₀) pG).mul pN) x c) pΨ)
  have iM : Integrable TMi μ := hI _ ((hc _ ((continuous_bil x c).comp
    (continuous_const.matrix_mul cN))).mul hΨm) _ (by omega)
    (PolyB.mul (PolyB.bilin ((PolyBM.const (P₀ * Mb)).mul pN) x c) pΨ)
  have iS : Integrable TSi μ := hI _ ((hc _ ((continuous_bil xc c).comp
    ((continuous_const.matrix_mul cS).matrix_mul cN))).mul hΨm) _ (by omega)
    (PolyB.mul (PolyB.bilin ((PolyBM.mul (PolyBM.const Sb) pG).mul pN) xc c) pΨ)
  have hae : ∀ᵐ ω ∂μ, TVi ω = TMi ω - TSi ω - LHSi ω := by
    filter_upwards [ae_layerHerm (W := W) b] with ω hω
    have hG := gSide_expand hη hX hDu adj ω hω
    have hmat : P₀ * 𝔊 ω * N ω = P₀ * Mb * N ω -
        (P₀ * Mb) * (layerLin ω * 𝔊 ω * N ω + Sb * 𝔊 ω * N ω) := by
      change P₀ * gSide b E X adj ω * N ω = _
      conv_lhs => rw [hG]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      rfl
    simp only [TVi, TMi, TSi, LHSi]
    rw [hmat, sub_mulVec, dotProduct_sub, star_dotProduct_mul_mulVec (P₀ * Mb)
      (layerLin ω * 𝔊 ω * N ω + Sb * 𝔊 ω * N ω) x c, add_mulVec,
      dotProduct_add]
    ring
  have iV : Integrable TVi μ := ((iM.sub iS).sub iL).congr (hae.mono fun ω h => h.symm)
  -- the `V` piece by `sd_vector`
  have hV := hsd W hW1 E hEκ X hX ℓ hℓ wd D hD xc c Ψ DΨ K hΨ hΨm hDm hΨb hDb
  set T1 := fun α γ ω => siteVar W b α γ * (star (xc α) * ((𝔊 ω * N ω) *ᵥ c) γ *
    DΨ ω (Matrix.single γ α 1))
  set T2 := fun (j : Fin ℓ) ω => star xc ⬝ᵥ ((sdiag b (𝔊 ω * wordAlpha Kh (gRes b E X ω) ℓ wd D j) *
    wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c) * Ψ ω
  set T3 := fun ω => star xc ⬝ᵥ ((sdiag b (𝔊 ω) * 𝔊 ω * N ω) *ᵥ c) * Ψ ω
  have i1 : ∀ α γ, Integrable (T1 α γ) μ := fun α γ => hI _ (measurable_const.mul
    ((measurable_const.mul (hc _ ((continuous_apply γ).comp ((cS.matrix_mul cN).matrix_mulVec continuous_const)))).mul
      (hDm _))) _ (by omega)
    (PolyB.const_mul _ (PolyB.mul (PolyB.mul (PolyB.const _) (PolyB.vecEntry (pG.mul pN) c γ))
      (pD _)))
  have i2 : ∀ j, Integrable (T2 j) μ := fun j => hI _ ((hc _ ((continuous_bil xc c).comp
    (((continuous_sdiag b).comp (cS.matrix_mul (continuous_wordAlpha Kh ℓ wd D j))).matrix_mul
      (continuous_wordGamma Kh ℓ wd D j)))).mul hΨm) _ (by omega)
    (PolyB.mul (PolyB.bilin (polyBM_sdiag_alpha_gamma b E hb0.le hb X adj hKd hℓ wd D hD j) xc c) pΨ)
  have i3 : Integrable T3 μ := hI _ ((hc _ ((continuous_bil xc c).comp
    ((((continuous_sdiag b).comp cS).matrix_mul cS).matrix_mul cN))).mul hΨm) _ (by omega)
    (PolyB.mul (PolyB.bilin (((PolyBM.sdiag b hb0.le hb pG).mul pG).mul pN) xc c) pΨ)
  have hsplit : ∫ ω, TVi ω ∂μ = (∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (xc α) *
      ((𝔊 ω * N ω) *ᵥ c) γ * DΨ ω (Matrix.single γ α 1) ∂μ) - ∑ j, ∫ ω, T2 j ω ∂μ -
      ∫ ω, T3 ω ∂μ := by
    have e : (fun ω => (∑ α, ∑ γ, siteVar W b α γ * (star (xc α) *
        ((𝔊 ω * N ω) *ᵥ c) γ * DΨ ω (Matrix.single γ α 1))) -
        ((∑ j, star xc ⬝ᵥ ((sdiag b (𝔊 ω * wordAlpha Kh (gRes b E X ω) ℓ wd D j) *
          wordGamma Kh (gRes b E X ω) ℓ wd D j) *ᵥ c)) +
          star xc ⬝ᵥ ((sdiag b (𝔊 ω) * 𝔊 ω * N ω) *ᵥ c)) * Ψ ω) =
        fun ω => (∑ α, ∑ γ, T1 α γ ω) - ∑ j, T2 j ω - T3 ω := by
      funext ω; simp only [T1, T2, T3, add_mul, Finset.sum_mul]; ring
    have hV' : ∫ ω, TVi ω ∂μ = ∫ ω, ((∑ α, ∑ γ, T1 α γ ω) - ∑ j, T2 j ω - T3 ω) ∂μ := by
      rw [← e]; exact hV
    have hT1 : Integrable (fun ω => ∑ α, ∑ γ, T1 α γ ω) μ :=
      integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun γ _ => i1 α γ
    have hT2 : Integrable (fun ω => ∑ j, T2 j ω) μ := integrable_finsetSum _ fun j _ => i2 j
    have hT12 : Integrable (fun ω => ∑ α, ∑ γ, T1 α γ ω - ∑ j, T2 j ω) μ := hT1.sub hT2
    rw [hV', integral_sub hT12 i3, integral_sub hT1 hT2,
      integral_finsetSum _ fun α _ => integrable_finsetSum _ fun γ _ => i1 α γ,
      integral_finsetSum _ fun j _ => i2 j]
    congr 2
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun γ _ => i1 α γ]
    exact Finset.sum_congr rfl fun γ _ => integral_const_mul _ _
  have hcent : ∫ ω, T3 ω ∂μ - ∫ ω, TSi ω ∂μ = ∫ ω, star xc ⬝ᵥ (((sdiag b (𝔊 ω) - Sb) * 𝔊 ω * N ω) *ᵥ c) *
      Ψ ω ∂μ := by
    rw [← integral_sub i3 iS]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [T3, TSi, sub_mulVec, dotProduct_sub, sub_mul]
  have hmain : ∫ ω, LHSi ω ∂μ = ∫ ω, TMi ω ∂μ - ∫ ω, TSi ω ∂μ - ∫ ω, TVi ω ∂μ := by
    have iMS : Integrable (fun ω => TMi ω - TSi ω) μ := iM.sub iS
    rw [← integral_sub iM iS, ← integral_sub iMS iV]
    refine integral_congr_ae (hae.mono fun ω h => ?_)
    simp only [h]; ring
  change ∫ ω, LHSi ω ∂μ = ∫ ω, TMi ω ∂μ + _ + ∑ j, ∫ ω, T2 j ω ∂μ - _
  rw [hmain, hsplit, ← hcent]
  ring

end BlockBand.Transmission.CovarianceBulk
