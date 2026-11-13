module

public import BlockBand.Transmission.SourceMixing.ExpansionAlg

/-!
# Bulk-uniform moments, replica identity and integrability

Moments of `1 + B`, `L²` and integrability from polynomial bounds in `1 + B`, and the replica
identity for dressed test functionals, uniformly in `E ∈ bulkInterval κ`: the constants and `W₀`
depend only on `b` and the bulk margin `κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Moments of `1 + B`** (`btFun_moment`), with `C, W₀` uniform over `E ∈ bulkInterval κ`. -/
theorem btFun_moment_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => 1 + btFun b E X ω) (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
          ENNReal.ofReal C := by
  obtain ⟨C, W₀, h⟩ := hA.moments b hb0 hb κ hκ p hp
  refine ⟨1 + (3 * max C 0 + max C 0 + max C 0), W₀, by positivity, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  obtain ⟨-, hg, hk, hl⟩ := h W hW E hE _
    (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX
  set μ := layerLaw W b .oneBlockOnePort
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have mg : MomBd μ (fun ω => ‖gRes b E X ω‖) p (max C 0) :=
    MomBd.nonneg ⟨(continuous_norm.measurable.comp hGm).aestronglyMeasurable, hg⟩
  have mk : MomBd μ (fun ω => ‖kG11 E (boundaryZ b E) X ω‖) p (max C 0) :=
    MomBd.nonneg ⟨(continuous_norm.measurable.comp
      (measurable_kG11 (W := W) E (boundaryZ b E) X)).aestronglyMeasurable, hk⟩
  have ml : MomBd μ (fun ω => ‖lAt E (boundaryZ b E) X ω‖) p (max C 0) :=
    MomBd.nonneg ⟨(continuous_norm.measurable.comp
      (measurable_lAt (W := W) E (boundaryZ b E) X)).aestronglyMeasurable, hl⟩
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have m1 : MomBd μ (fun _ => (1 : ℝ)) p 1 := by
    simpa using MomBd.const (μ := μ) (1 : ℝ) p (by linarith)
  have m3 := mg.const_mul (show (0 : ℝ) ≤ 3 by norm_num)
  have ms := ((m3.add hp mk (by positivity) hC0).add hp ml (by positivity) hC0)
  exact (m1.add hp ms zero_le_one (by positivity)).2

/-- **`L²` from a polynomial bound in `1 + B`** (`memLp_two_of_poly`), with `W₀` uniform over
`E ∈ bulkInterval κ`. -/
theorem memLp_two_of_poly_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (r : ℕ) (hr : 1 ≤ r) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      ∀ (F : LayerSample W .oneBlockOnePort → ℂ), AEStronglyMeasurable F (layerLaw W b .oneBlockOnePort) →
      ∀ K : ℝ, (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ r) →
        MemLp F 2 (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨C, W₀, hC, hm⟩ := btFun_moment_bulk hA hb0 hb hκ (2 * (r : ℕ)) (by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith)
  refine ⟨W₀, fun W hW E hE X hX F hF K hK => ?_⟩
  have hg := eLpNorm_pow_le (μ := layerLaw W b .oneBlockOnePort) (g := fun ω => 1 + btFun b E X ω)
    (fun ω => by have := btFun_nonneg b E X ω; positivity)
    (measurable_const.add (measurable_btFun b E X)).aestronglyMeasurable r hr (hm W hW E hE X hX)
  have hgL : MemLp (fun ω => (1 + btFun b E X ω) ^ r) 2 (layerLaw W b .oneBlockOnePort) :=
    lt_of_le_of_lt hg (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  refine (hgL.const_mul K).of_le hF (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ (1 + btFun b E X ω) ^ r := by have := btFun_nonneg b E X ω; positivity
  have hK0 : 0 ≤ K := by
    by_contra hneg
    have := hK ω
    have : K * (1 + btFun b E X ω) ^ r < 0 := by
      have h1' : 0 < (1 + btFun b E X ω) ^ r := by have := btFun_nonneg b E X ω; positivity
      nlinarith
    linarith [norm_nonneg (F ω)]
  rw [Real.norm_of_nonneg (mul_nonneg hK0 h0)]
  exact hK ω

/-- **Integrability from a polynomial bound in `1 + B`** (`integrable_poly`), with `W₀` uniform
over `E ∈ bulkInterval κ`. -/
theorem integrable_poly_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (r : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      ∀ (F : LayerSample W .oneBlockOnePort → ℂ), AEStronglyMeasurable F (layerLaw W b .oneBlockOnePort) →
      ∀ K : ℝ, (∀ ω, ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ r) →
        Integrable F (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, h⟩ := memLp_two_of_poly_bulk hA hb0 hb hκ (r + 1) (by omega)
  refine ⟨W₀, fun W hW E hE X hX F hF K hK =>
    (h W hW E hE X hX F hF (max K 0) fun ω => ?_).integrable one_le_two⟩
  have h1' := one_le_one_add_btFun b E X ω
  have h0 : 0 ≤ (1 + btFun b E X ω) ^ r := by positivity
  calc ‖F ω‖ ≤ K * (1 + btFun b E X ω) ^ r := hK ω
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ r := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max K 0 * (1 + btFun b E X ω) ^ (r + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1' (by omega)) (le_max_right _ _)

/-- **The replica identity for dressed test functionals** (both row types), with every
integrability hypothesis discharged by the `moments` clause of `PassiveBoundsStatement`
(`replica_wordForm`), with `W₀` uniform
over `E ∈ bulkInterval κ`. -/
theorem replica_wordForm_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
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
  obtain ⟨W₀, hm⟩ := memLp_two_of_poly_bulk hA hb0 hb hκ (Lw + 3) (by omega)
  refine ⟨W₀, fun W hW E hE X hX ℓ hℓ wd D hD a c x β => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
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
    refine hm W hW E hE X hX.posSemidef _ ((hent γ δ).mul hΨm).aestronglyMeasurable (K1 * Q) fun ω => ?_
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
    refine (hm W hW E hE X hX.posSemidef _ ((hent γ β).mul (hDm N)).aestronglyMeasurable
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
    refine (hm W hW E hE X hX.posSemidef _ (hΨm.mul ((hGm.mul_const N).mul hGm).eval_matrix).aestronglyMeasurable
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

end BlockBand.Transmission.LengthUniform
