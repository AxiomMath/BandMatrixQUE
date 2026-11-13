module

public import BlockBand.Transmission.PassiveCovariance.SdBasic

/-!
# The first-letter expansion of a dressed form against a test functional

**Hypothesis:** `PassiveBoundsStatement` (through `sd_vector`, `memLp_poly`, `dressed_inverse`).
Law `layerLaw W b .oneBlockOnePort`, `z = z_∂(E)`; fixed `b, E, L_w, K_d, m` and a side
`𝔊 = gSide adj ∈ {𝒢, 𝒢ᴴ}`; then `W₀`; for `W ≥ W₀` and strictly passive `X`.

**`sd_expand`.** For every deterministic `P₀`, vectors `x, c`, dressed word `N = w(𝒢)`
(length `≤ L_w`, insertions `≤ K_d`, derivative factors `α_j, γ_j`) and test `Ψ` with the
polynomial bounds of `sd_vector`, with `M̄ = mbarSide adj`, `S̄ = sbarSide adj`,
`x̌ = (P₀M̄)ᴴx`:
`E[(x*P₀𝔊Nc)Ψ] = E[(x*P₀M̄Nc)Ψ] + E[(x̌*(S[𝔊] - S̄)𝔊Nc)Ψ] + Σ_j E[(x̌*S[𝔊α_j]γ_jc)Ψ]
   - Σ_{α,γ} σ(α,γ) E[x̌̄_α (𝔊Nc)_γ DΨ(E_{γα})]`.
The second term is the centred self-energy, the third the letter traces (the ladder), the last the
crossed contraction. Every integrand is polynomially bounded (`SdPoly`), hence integrable.
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

theorem ae_layerHerm (b : ℝ) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, (ω.1 0).IsHermitian := by
  have h := ae_isHermitian_pi W (Real.toNNReal ((1 - 2 * b) / W))
  unfold layerLaw
  exact (measurePreserving_fst).quasiMeasurePreserving.ae h

theorem continuous_bil {n : Type*} [Fintype n] (x c : n → ℂ) :
    Continuous fun A : Matrix n n ℂ => star x ⬝ᵥ (A *ᵥ c) :=
  continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

/-- **The first-letter expansion** (see the module docstring). -/
theorem sd_expand (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw m : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
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
  obtain ⟨W₁, hsd⟩ := sd_vector hA hb0 hb h1 h2 Lw m Kd adj
  obtain ⟨W₂, hP⟩ := memLp_poly hA hb0 hb h1 h2 (Lw + m + 3)
  obtain ⟨Cd, W₃, hdi⟩ := dressed_inverse hA hb0 hb h1 h2
  refine ⟨max W₁ (max W₂ W₃), fun W hW X hX ℓ hℓ wd D hD P₀ x c Ψ DΨ K hΨ hΨm hDm hΨb hDb => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  have hDu := (hdi W hW3 X hX).1
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
    exact (hP W hW2 X hX.posSemidef F hF.aestronglyMeasurable C k hk hb').integrable one_le_two
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
  have hV := hsd W hW1 X hX ℓ hℓ wd D hD xc c Ψ DΨ K hΨ hΨm hDm hΨb hDb
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

end BlockBand.Transmission.PassiveCovariance
