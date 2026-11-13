module

public import BlockBand.Transmission.PassiveCovariance.Q2All

/-!
# Site variances, the variance-weighted diagonal, and the replica identity at every site

Law `layerLaw W b .oneBlockOnePort`, `z = z_∂(E)`, strictly passive `X`.

* `siteVar W b α γ = E|V_{αγ}|²`: `c/W` on physical–physical pairs, `b/W` on physical–port and
  port–physical pairs, `0` on port–port pairs (`V = layerLin ω`).
* `sdiag b M = diag(Σ_γ σ(α,γ) M_{γγ})`, the self-energy operator `S[M]` of `M`; for `M = E𝒢`
  it is `selfEnergy b m₁ m₂` (`sdiag_eq_selfEnergy`).
* `gSide b E X adj` is `𝒢` (`adj = false`) or `𝒢ᴴ` (`adj = true`); both have entry derivatives
  `N ↦ -(𝔊N𝔊)_{γβ}` (`hasLayerDeriv_gSide`).
* `replica_site_gen`: `replica_identity_phys/port` (re-proved from the same Stein lemmas) as
  one statement for every row `α` and every such side `𝔊`:
  `E[(V𝔊)_{αβ}Ψ] = Σ_γ σ(α,γ) E[𝔊_{γβ} DΨ(E_{γα}) - Ψ 𝔊_{γγ}𝔊_{αβ}]`, with the integrability of
  the left side.
* `memLp_poly`: `memLp_two_of_poly` for every exponent `k ≤ R` at once.
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

/-- The site variances `σ(α,γ) = E|V_{αγ}|²` of the Gaussian part of the layer matrix. -/
def siteVar (W : ℕ) (b : ℝ) : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort → ℂ
  | Sum.inl _, Sum.inl _ => (gueVar W b : ℂ)
  | Sum.inl _, Sum.inr _ => (ginVar W b : ℂ)
  | Sum.inr _, Sum.inl _ => (ginVar W b : ℂ)
  | Sum.inr _, Sum.inr _ => 0

/-- The self-energy operator `S[M] = diag(Σ_γ σ(α,γ) M_{γγ})`. -/
def sdiag (b : ℝ) (M : LayerMat W) : LayerMat W :=
  diagonal fun α => ∑ γ, siteVar W b α γ * M γ γ

theorem siteVar_phys_phys (b : ℝ) (x y : Fin W) :
    siteVar W b (phys x) (phys y) = (gueVar W b : ℂ) := rfl

theorem siteVar_phys_port (b : ℝ) (x y : Fin W) :
    siteVar W b (phys x) (port y) = (ginVar W b : ℂ) := rfl

theorem siteVar_port_phys (b : ℝ) (x y : Fin W) :
    siteVar W b (port x) (phys y) = (ginVar W b : ℂ) := rfl

theorem siteVar_port_port (b : ℝ) (x y : Fin W) : siteVar W b (port x) (port y) = 0 := rfl

theorem norm_siteVar_le (b : ℝ) (hb0 : 0 ≤ b) (hb : b < 1 / 2) (α γ : LayerSite W .oneBlockOnePort) :
    ‖siteVar W b α γ‖ ≤ 1 / W := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hg : ‖((gueVar W b : ℝ≥0) : ℂ)‖ ≤ 1 / W := by
    rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    simp only [gueVar, Real.coe_toNNReal']
    exact max_le (div_le_div_of_nonneg_right (by linarith) hW) (by positivity)
  have hn : ‖((ginVar W b : ℝ≥0) : ℂ)‖ ≤ 1 / W := by
    rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    simp only [ginVar, Real.coe_toNNReal']
    exact max_le (div_le_div_of_nonneg_right (by linarith) hW) (by positivity)
  rcases α with α | α <;> rcases γ with γ | γ
  · exact hg
  · exact hn
  · exact hn
  · simp [siteVar]

/-- Sum over the two site types. -/
theorem sum_siteVar_phys (b : ℝ) (x : Fin W) (f : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ γ, siteVar W b (phys x) γ * f γ =
      ∑ y, (gueVar W b : ℂ) * f (phys y) + ∑ y, (ginVar W b : ℂ) * f (port y) := by
  rw [sum_layerSite]; rfl

theorem sum_siteVar_port (b : ℝ) (x : Fin W) (f : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ γ, siteVar W b (port x) γ * f γ = ∑ y, (ginVar W b : ℂ) * f (phys y) := by
  rw [sum_layerSite]; simp [siteVar]

/-- The resolvent side used in the expansion: `𝒢` (`adj = false`) or `𝒢ᴴ` (`adj = true`);
`𝒢ᴴ = (H₀ᴴ + V)⁻¹` at Hermitian samples, with the same Gaussian part `V`. -/
def gSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) (ω : LayerSample W .oneBlockOnePort) :
    LayerMat W :=
  if adj then (gRes b E X ω)ᴴ else gRes b E X ω

theorem measurable_gSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) :
    Measurable (gSide b E X adj) := by
  cases adj
  · exact measurable_layerRes E (boundaryZ b E) X
  · exact continuous_id.matrix_conjTranspose.measurable.comp (measurable_layerRes E (boundaryZ b E) X)

theorem norm_gSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool)
    (ω : LayerSample W .oneBlockOnePort) : ‖gSide b E X adj ω‖ = ‖gRes b E X ω‖ := by
  cases adj
  · rfl
  · exact Matrix.l2_opNorm_conjTranspose _

theorem hasLayerDeriv_gSide {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosDef) (adj : Bool) (γ β : LayerSite W .oneBlockOnePort) :
    HasLayerDeriv (fun ω => gSide b E X adj ω γ β) (fun ω => resDeriv (gSide b E X adj ω) γ β) := by
  have hinv := fun ω hω => isUnit_layerMatrix_strict (E := E) hη hY ω hω
  cases adj
  · exact hasLayerDeriv_resolvent_entry E (boundaryZ b E) _ hinv γ β
  · exact hasLayerDeriv_resolvent_adj_entry E (boundaryZ b E) _ hinv γ β

/-- **The replica identity at every row, for a general resolvent side** `𝔊` (entries with
derivative `N ↦ -(𝔊N𝔊)_{γβ}`): `E[(V𝔊)_{αβ}Ψ] = Σ_γ σ(α,γ) E[𝔊_{γβ} DΨ(E_{γα}) - Ψ 𝔊_{γγ}𝔊_{αβ}]`,
with the integrability of the left side. The proof is that of `replica_identity_phys`, for every
`𝔊`. -/
theorem replica_site_gen (b : ℝ) (𝔊 : LayerSample W .oneBlockOnePort → LayerMat W)
    (h𝔊 : ∀ γ β, HasLayerDeriv (fun ω => 𝔊 ω γ β) (fun ω => resDeriv (𝔊 ω) γ β))
    (h𝔊m : Measurable 𝔊) {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hΨ : HasLayerDeriv Ψ DΨ) (hΨm : Measurable Ψ) (α β : LayerSite W .oneBlockOnePort)
    (hL2 : ∀ γ, MemLp (fun ω => 𝔊 ω γ β * Ψ ω) 2 (layerLaw W b .oneBlockOnePort))
    (hI1 : ∀ γ N, Integrable (fun ω => 𝔊 ω γ β * DΨ ω N) (layerLaw W b .oneBlockOnePort))
    (hI2 : ∀ γ N, Integrable (fun ω => Ψ ω * (𝔊 ω * N * 𝔊 ω) γ β)
      (layerLaw W b .oneBlockOnePort)) :
    Integrable (fun ω => (layerLin ω * 𝔊 ω) α β * Ψ ω) (layerLaw W b .oneBlockOnePort) ∧
    ∫ ω, (layerLin ω * 𝔊 ω) α β * Ψ ω ∂layerLaw W b .oneBlockOnePort =
      ∑ γ, siteVar W b α γ * ∫ ω, (𝔊 ω γ β * DΨ ω (Matrix.single γ α 1) -
          Ψ ω * (𝔊 ω γ γ * 𝔊 ω α β)) ∂layerLaw W b .oneBlockOnePort := by
  set μ := layerLaw W b .oneBlockOnePort
  have hd : ∀ γ, HasLayerDeriv (fun ω => 𝔊 ω γ β * Ψ ω)
      (fun ω => 𝔊 ω γ β • DΨ ω + Ψ ω • resDeriv (𝔊 ω) γ β) := fun γ => (h𝔊 γ β).mul hΨ
  have hm : ∀ γ, Measurable fun ω => 𝔊 ω γ β * Ψ ω := fun γ => h𝔊m.eval_matrix.mul hΨm
  have happ : ∀ γ N ω, (𝔊 ω γ β • DΨ ω + Ψ ω • resDeriv (𝔊 ω) γ β) N =
      𝔊 ω γ β * DΨ ω N - Ψ ω * (𝔊 ω * N * 𝔊 ω) γ β := fun γ N ω => by
    simp [resDeriv, sub_eq_add_neg]
  have hi : ∀ γ N, Integrable (fun ω => (𝔊 ω γ β • DΨ ω + Ψ ω • resDeriv (𝔊 ω) γ β) N) μ :=
    fun γ N => by simp only [happ]; exact (hI1 γ N).sub (hI2 γ N)
  have hval : ∀ γ α', ∫ ω, (𝔊 ω γ β • DΨ ω + Ψ ω • resDeriv (𝔊 ω) γ β)
      (Matrix.single γ α' 1) ∂μ = ∫ ω, (𝔊 ω γ β * DΨ ω (Matrix.single γ α' 1) -
        Ψ ω * (𝔊 ω γ γ * 𝔊 ω α' β)) ∂μ := fun γ α' => by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [happ, mul_single_mul_apply]
  rcases α with ⟨i, x⟩ | ⟨i, x⟩ <;> obtain rfl : i = 0 := Subsingleton.elim i 0
  · have e : (fun ω => (layerLin ω * 𝔊 ω) (phys x) β * Ψ ω) = fun ω =>
        ∑ y, ω.1 0 x y * (𝔊 ω (phys y) β * Ψ ω) + ∑ y, ω.2 0 0 x y * (𝔊 ω (port y) β * Ψ ω) := by
      funext ω; rw [layerLin_mul_phys, add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1 <;> refine Finset.sum_congr rfl fun y _ => by ring
    have hA : ∀ y, Integrable (fun ω => ω.1 0 x y * (𝔊 ω (phys y) β * Ψ ω)) μ :=
      fun y => (memLp_layer_A b x y).integrable_mul (hL2 _)
    have hB : ∀ y, Integrable (fun ω => ω.2 0 0 x y * (𝔊 ω (port y) β * Ψ ω)) μ :=
      fun y => (memLp_layer_B b x y).integrable_mul (hL2 _)
    change Integrable (fun ω => (layerLin ω * 𝔊 ω) (phys x) β * Ψ ω) μ ∧
      ∫ ω, (layerLin ω * 𝔊 ω) (phys x) β * Ψ ω ∂μ = _
    rw [e]
    refine ⟨(integrable_finsetSum _ fun y _ => hA y).add (integrable_finsetSum _ fun y _ => hB y), ?_⟩
    rw [integral_add (integrable_finsetSum _ fun y _ => hA y) (integrable_finsetSum _ fun y _ => hB y),
      integral_finsetSum _ (fun y _ => hA y), integral_finsetSum _ (fun y _ => hB y)]
    refine Eq.trans ?_ (sum_siteVar_phys b x (fun γ => ∫ ω, (𝔊 ω γ β * DΨ ω (Matrix.single γ (phys x) 1) -
        Ψ ω * (𝔊 ω γ γ * 𝔊 ω (phys x) β)) ∂μ)).symm
    congr 1
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [stein_layerA_lin b _ _ (hd _) (hm _) (hL2 _) (hi _) x y, layerA_single, hval]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [stein_layerB_lin b _ _ (hd _) (hm _) (hL2 _) (hi _) x y, lowerB_single, hval]
  · have e : (fun ω => (layerLin ω * 𝔊 ω) (port x) β * Ψ ω) = fun ω =>
        ∑ y, star (ω.2 0 0 y x) * (𝔊 ω (phys y) β * Ψ ω) := by
      funext ω; rw [layerLin_mul_port, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => by ring
    have hB : ∀ y, Integrable (fun ω => star (ω.2 0 0 y x) * (𝔊 ω (phys y) β * Ψ ω)) μ :=
      fun y => (memLp_layer_B b y x).star.integrable_mul (hL2 _)
    change Integrable (fun ω => (layerLin ω * 𝔊 ω) (port x) β * Ψ ω) μ ∧
      ∫ ω, (layerLin ω * 𝔊 ω) (port x) β * Ψ ω ∂μ = _
    rw [e]
    refine ⟨integrable_finsetSum _ fun y _ => hB y, ?_⟩
    rw [integral_finsetSum _ (fun y _ => hB y)]
    refine Eq.trans ?_ (sum_siteVar_port b x (fun γ => ∫ ω, (𝔊 ω γ β * DΨ ω (Matrix.single γ (port x) 1) -
        Ψ ω * (𝔊 ω γ γ * 𝔊 ω (port x) β)) ∂μ)).symm
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [stein_layerBconj_lin b _ _ (hd _) (hm _) (hL2 _) (hi _) y x, upperB_single, hval]

/-- `memLp_two_of_poly` for every exponent `k ≤ R` and every sign of the constant. -/
theorem memLp_poly (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (R : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (F : LayerSample W .oneBlockOnePort → ℂ), AEStronglyMeasurable F (layerLaw W b .oneBlockOnePort) →
      ∀ (K : ℝ) (k : ℕ), k ≤ R → (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ k) →
        MemLp F 2 (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, hm⟩ := memLp_two_of_poly hA hb0 hb h1 h2 (R + 1) (by omega)
  refine ⟨W₀, fun W hW X hX F hF K k hk hK => hm W hW X hX F hF (max K 0) fun ω => ?_⟩
  have h1' : 1 ≤ 1 + btFun b E X ω := one_le_one_add_btFun b E X ω
  have hp : (1 + btFun b E X ω) ^ k ≤ (1 + btFun b E X ω) ^ (R + 1) :=
    pow_le_pow_right₀ h1' (by omega)
  have h0 : 0 ≤ (1 + btFun b E X ω) ^ k := by positivity
  calc ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ k := hK ω
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ (R + 1) :=
        mul_le_mul_of_nonneg_left hp (le_max_right _ _)

end BlockBand.Transmission.PassiveCovariance
