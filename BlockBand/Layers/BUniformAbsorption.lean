module

public import BlockBand.Layers.GaussianAbsorption
public import BlockBand.Internal.Contracts.LayersBUniform

/-!
# Gaussian absorption, uniformly in `b` on compact subsets of `(0,1/2)`

The Gaussian absorption lemma (the absorber moments), all four layer shapes, with the uniformity
in `b` used later in the paper. Proves
`BlockBand.Internal.Contracts.LayersBUniform.GaussianAbsorptionUniformContract`
(`gaussianAbsorptionUniform_holds`) from `Inputs.ConditionalBlockGUECount` only.

* **Law**: `layerLaw W b σ` (blocks `A_a ~ GUE_W((1-2b)/W)`, bonds `Gin(b/W)`).
* **Domain**: `W ≥ 1`, every shape `σ`, deterministic Hermitian `X`, real `E`, `z` with
  `Im z ≥ η₀`, `‖z‖ ≤ M`; moments `1 ≤ p ≤ W/48`.
* **Norms**: `ℓ²` operator norm of the layer resolvent `𝒢`; `L^p(layerLaw)` norm of `‖𝒢‖`.
* **Quantifier order**: `β ∈ (0,1/4)`, `η₀ > 0`, `M`; then `ε₁ = 1/48`, `C > 0`; then uniformly
  in `b ∈ [β, 1/2-β]` and everything else.
* **Uniformity / constant**: `C = L Cδ(β)² (C_K¹² + C_d(β)⁴)` with
  `L = layerResolventConstant η₀ M` (`b`-free),
  `Cδ(β) = max_{k∈{1,2}} gapMomentConstant C_PSSS k (2β)` (`bu_gapUnifConst`),
  `C_K = bondMomentConst (1/2) = 6(1+10/√2)` (`bu_bondUnifConst`),
  `C_d(β) = 4^(⌈27e/β + 2·12⁸⌉₊+2)` (`bu_singUnifConst`).
* **Inputs**: `Inputs.ConditionalBlockGUECount` (hypothesis), and Mathlib.

Proof. `bu_gaussianAbsorption_explicit` is the proof of `gaussianAbsorption_holds`, adapted so
that the three `b`-dependent constants `Cδ(b) = max_k gapMomentConstant C_PSSS k (1-2b)`,
`C_K(b) = bondMomentConst b`, `C_d(b) = singMomentConst b` are replaced by **arbitrary upper
bounds** `Cδ, CK, Cd` (the moment inequalities are monotone in the constant). Apart from these
three constants, `b` enters that proof only through `0 < b` (`singFloor_pos_ae`,
`singFloor_inv_moment`, `bond_lintegral_rpow_le`) and `0 < 1 - 2b` (`absn_gap_pos_ae`, the
gap moments). The uniform bounds: `gapTailConstant C k c = 16 e C k / √c` is antitone in
`c > 0` and `1 - 2b ≥ 2β` (`bu_gapMomentConstant_le`); `bondMomentConst` is monotone and
`b ≤ 1/2` (`bu_bondMomentConst_le`); `singTailConst b = 27e/b + 4b·12⁸ ≤ 27e/β + 2·12⁸`
for `β ≤ b ≤ 1/2` (`bu_singMomentConst_le`). Also `bu_gaussianAbsorption_of_uniform`: the
uniform clause implies `GaussianAbsorptionContract` (`β = min b (1/2-b) / 2`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Module Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.LayersBUniform
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## 1. The parameter interval
-/

/-- The standard `β` for a fixed `b ∈ (0,1/2)`: `β = min b (1/2-b) / 2` satisfies
`0 < β < 1/4` and `b ∈ [β, 1/2-β]`. -/
theorem bu_beta_of_mem {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) :
    0 < min b (1 / 2 - b) / 2 ∧ min b (1 / 2 - b) / 2 < 1 / 4 ∧
      b ∈ Set.Icc (min b (1 / 2 - b) / 2) (1 / 2 - min b (1 / 2 - b) / 2) := by
  have hm0 : 0 < min b (1 / 2 - b) := lt_min hb0 (by linarith)
  have hm1 := min_le_left b (1 / 2 - b)
  have hm2 := min_le_right b (1 / 2 - b)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `b ∈ [β, 1/2-β]` with `β > 0` gives `0 < b < 1/2`. -/
theorem bu_mem_bounds {β b : ℝ} (hβ : 0 < β) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    0 < b ∧ b < 1 / 2 := by
  obtain ⟨h1, h2⟩ := hb
  exact ⟨by linarith, by linarith⟩

/-!
## 2. Uniform constants
-/

/-- `gapMomentConstant` is monotone in the tail constant. -/
theorem bu_gapMomentConstant_mono {C c c' : ℝ} {k : ℕ}
    (h : gapTailConstant C k c ≤ gapTailConstant C k c') :
    gapMomentConstant C k c ≤ gapMomentConstant C k c' := by
  unfold gapMomentConstant
  exact pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right (Nat.ceil_mono h) 2)

/-- `gapTailConstant C k c = 16 e C k / √c` is antitone in `c > 0` (for `C ≥ 0`). -/
theorem bu_gapTailConstant_anti {C c c' : ℝ} (hC : 0 ≤ C) (k : ℕ) (hc' : 0 < c')
    (hcc : c' ≤ c) : gapTailConstant C k c ≤ gapTailConstant C k c' := by
  unfold gapTailConstant
  exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hc')
    (Real.sqrt_le_sqrt hcc)

/-- Uniform gap-moment constant `Cδ(β) = max_{k∈{1,2}} gapMomentConstant C k (2β)`. -/
def bu_gapUnifConst (C β : ℝ) : ℝ :=
  max (gapMomentConstant C 1 (2 * β)) (gapMomentConstant C 2 (2 * β))

/-- For `b ∈ [β, 1/2-β]`: `gapMomentConstant C k (1-2b) ≤ gapMomentConstant C k (2β)`. -/
theorem bu_gapMomentConstant_le {C β b : ℝ} (hC : 0 ≤ C) (hβ : 0 < β)
    (hb : b ∈ Set.Icc β (1 / 2 - β)) (k : ℕ) :
    gapMomentConstant C k (1 - 2 * b) ≤ gapMomentConstant C k (2 * β) :=
  bu_gapMomentConstant_mono (bu_gapTailConstant_anti hC k (by linarith) (by linarith [hb.2]))

/-- Uniform bond-moment constant `C_K = bondMomentConst (1/2)`. -/
def bu_bondUnifConst : ℝ := bondMomentConst (1 / 2)

/-- `bondMomentConst b ≤ bondMomentConst (1/2)` for `b ≤ 1/2`. -/
theorem bu_bondMomentConst_le {b : ℝ} (hb : b ≤ 1 / 2) :
    bondMomentConst b ≤ bu_bondUnifConst := by
  unfold bu_bondUnifConst bondMomentConst
  have := Real.sqrt_le_sqrt hb
  linarith

/-- Uniform singular-floor tail constant `27 e / β + 4 (1/2) 12⁸`. -/
def bu_singTailUnif (β : ℝ) : ℝ := 27 * Real.exp 1 / β + 4 * (1 / 2) * 12 ^ 8

/-- Uniform singular-floor moment constant `C_d(β) = 4^(⌈27e/β + 2·12⁸⌉₊ + 2)`. -/
def bu_singUnifConst (β : ℝ) : ℝ := (4 : ℝ) ^ (⌈bu_singTailUnif β⌉₊ + 2)

/-- For `β ≤ b ≤ 1/2`, `β > 0`: `singTailConst b ≤ 27e/β + 2·12⁸`. -/
theorem bu_singTailConst_le {β b : ℝ} (hβ : 0 < β) (hβb : β ≤ b) (hb : b ≤ 1 / 2) :
    singTailConst b ≤ bu_singTailUnif β := by
  unfold singTailConst bu_singTailUnif
  have h1 : 27 * Real.exp 1 / b ≤ 27 * Real.exp 1 / β :=
    div_le_div_of_nonneg_left (by positivity) hβ hβb
  have h2 : 4 * b * 12 ^ 8 ≤ 4 * (1 / 2) * 12 ^ 8 := by nlinarith
  linarith

/-- For `β ≤ b ≤ 1/2`, `β > 0`: `singMomentConst b ≤ C_d(β)`. -/
theorem bu_singMomentConst_le {β b : ℝ} (hβ : 0 < β) (hβb : β ≤ b) (hb : b ≤ 1 / 2) :
    singMomentConst b ≤ bu_singUnifConst β := by
  unfold singMomentConst bu_singUnifConst
  exact pow_le_pow_right₀ (by norm_num)
    (Nat.add_le_add_right (Nat.ceil_mono (bu_singTailConst_le hβ hβb hb)) 2)

/-!
## 3. Explicit-constant absorption
-/

/-- **The Gaussian absorption lemma with explicit constants** (the proof of
`gaussianAbsorption_holds`, adapted). From `ConditionalBlockGUECount` there is `C_PSSS > 0` such
that for every `0 < b < 1/2`, `η₀ > 0`, `M`, and all reals
`Cδ ≥ max_{k∈{1,2}} gapMomentConstant C_PSSS k (1-2b)`, `CK ≥ bondMomentConst b`,
`Cd ≥ singMomentConst b`: uniformly in `W ≥ 1`, the shape, Hermitian `X`, real `E` and
`Im z ≥ η₀`, `‖z‖ ≤ M`, the layer matrix is a.s. invertible and
`‖‖𝒢‖‖_{L^p(layerLaw W b σ)} ≤ L Cδ² (CK¹² + Cd⁴)`, `L = layerResolventConstant η₀ M`, for
`1 ≤ p ≤ W/48`. -/
theorem bu_gaussianAbsorption_explicit (hcount : ConditionalBlockGUECount) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ →
      ∀ Cδ CK Cd : ℝ, gapMomentConstant Cg 1 (1 - 2 * b) ≤ Cδ →
        gapMomentConstant Cg 2 (1 - 2 * b) ≤ Cδ → bondMomentConst b ≤ CK →
        singMomentConst b ≤ Cd →
      ∀ (W : ℕ), 0 < W → ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ),
        X.IsHermitian → ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
          (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
          ∀ p : ℝ, 1 ≤ p → p ≤ 1 / 48 * W →
            eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal p) (layerLaw W b σ) ≤
              ENNReal.ofReal (layerResolventConstant η₀ M * Cδ ^ 2 * (CK ^ 12 + Cd ^ 4)) := by
  obtain ⟨Cg, hCg, hgap⟩ := absorbedGap_inv_moment hcount
  refine ⟨Cg, hCg, ?_⟩
  intro b hb hb2 η₀ M hη Cδ CK Cd hδ1 hδ2 hCKb hCdb
  have hc : 0 < 1 - 2 * b := by linarith
  set L := layerResolventConstant η₀ M with hLdef
  have hL : 0 < L := absn_layerResolventConstant_pos hη M
  have hCδ0 : 0 < Cδ := (gapMomentConstant_pos _ _ _).trans_le hδ1
  have hCK : 0 < CK := (bondMomentConst_pos b).trans_le hCKb
  have hCd : 0 < Cd := (singMomentConst_pos b).trans_le hCdb
  set Cfin := L * Cδ ^ 2 * (CK ^ 12 + Cd ^ 4) with hCfin
  have hC0 : 0 < Cfin := by positivity
  intro W hW σ X hX E z hz hM
  have hgood : ∀ᵐ A ∂blockLaw σ.blocks W (1 - 2 * b),
      (∀ j, (A j).IsHermitian) ∧ 0 < absnGap E X hX A := by
    filter_upwards [ae_blocks_isHermitian σ.blocks W (Real.toNNReal ((1 - 2 * b) / W)),
      absn_gap_pos_ae hcount hW hc E ⟨X, hX⟩] with A h1 h2
    exact ⟨h1, h2⟩
  have hbond : ∀ A, ∀ᵐ B ∂absnBondLaw W b σ, 0 < singFloor (absnSub E X hX A) B := fun A =>
    absn_ae_bond W b σ (singFloor_pos_ae σ hW hb _ (absn_finrank_sub_le E X hX A))
  refine ⟨?_, ?_⟩
  · -- almost-sure invertibility
    have hmeas : MeasurableSet {ω : LayerSample W σ | (layerMatrix σ E z X ω).det ≠ 0} :=
      (measurableSet_singleton 0).compl.preimage
        ((continuous_id.matrix_det).measurable.comp (measurable_layerMatrix σ E z X))
    have h : ∀ᵐ ω ∂layerLaw W b σ, (layerMatrix σ E z X ω).det ≠ 0 := by
      rw [absn_layerLaw_eq, Measure.ae_prod_iff_ae_ae hmeas]
      filter_upwards [hgood] with A hA
      filter_upwards [hbond A] with B hB
      exact (absn_pointwise σ E z X hX (A, B) hA.1 hη hz hM hA.2 hB).1.ne_zero
    filter_upwards [h] with ω hω
    exact isUnit_iff_ne_zero.mpr hω
  · intro p hp1 hpW
    have hp0 : 0 < p := by linarith
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have h2p1 : 1 ≤ 2 * p := by linarith
    have h2pW : 2 * p ≤ (W : ℝ) / 16 := by linarith
    have h4p1 : 1 ≤ 4 * p := by linarith
    have h4pW : 4 * p ≤ (W : ℝ) / 2 := by linarith
    have h12p1 : 1 ≤ 12 * p := by linarith
    have h12pW : 12 * p ≤ (W : ℝ) := by linarith
    have hLp : 0 ≤ L ^ p / 2 := div_nonneg (Real.rpow_nonneg hL.le _) zero_le_two
    set Q := ENNReal.ofReal (CK ^ (12 * p)) + ENNReal.ofReal (Cd ^ (4 * p)) with hQ
    have hQtop : Q ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    -- the inner (bond) integral, for a good block sample
    have hinner : ∀ A, (∀ j, (A j).IsHermitian) ∧ 0 < absnGap E X hX A →
        ∫⁻ B, ENNReal.ofReal (‖layerResolvent σ E z X (A, B)‖ ^ p) ∂absnBondLaw W b σ ≤
          ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) * Q := by
      intro A hA
      calc ∫⁻ B, ENNReal.ofReal (‖layerResolvent σ E z X (A, B)‖ ^ p) ∂absnBondLaw W b σ
          ≤ ∫⁻ B, ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) *
              (ENNReal.ofReal ((1 + ‖bondMatrix σ B‖) ^ (12 * p)) +
                ENNReal.ofReal ((singFloor (absnSub E X hX A) B)⁻¹ ^ (4 * p)))
                ∂absnBondLaw W b σ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hbond A] with B hB
            exact absn_ofReal_bound (norm_nonneg _) hL.le (norm_nonneg _) hB hA.2 hp0.le
              (absn_pointwise σ E z X hX (A, B) hA.1 hη hz hM hA.2 hB).2
        _ = ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) *
              (∫⁻ B, ENNReal.ofReal ((1 + ‖bondMatrix σ B‖) ^ (12 * p)) ∂absnBondLaw W b σ +
                ∫⁻ B, ENNReal.ofReal ((singFloor (absnSub E X hX A) B)⁻¹ ^ (4 * p))
                  ∂absnBondLaw W b σ) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left]
            exact ENNReal.measurable_ofReal.comp
              (((continuous_norm.measurable.comp (absn_measurable_bondMatrix σ)).const_add
                1).pow_const _)
        _ ≤ ENNReal.ofReal (L ^ p / 2 * (absnGap E X hX A)⁻¹ ^ (2 * p)) * Q := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) zero_le
            · exact ((absn_lintegral_bond_le W b σ
                (fun B => ENNReal.ofReal ((1 + ‖bondMatrix σ B‖) ^ (12 * p)))).trans
                (bond_lintegral_rpow_le σ hb h12p1 h12pW)).trans
                (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (bondMomentConst_pos b).le hCKb
                  (by linarith)))
            · exact ((absn_lintegral_bond_le W b σ
                (fun B => ENNReal.ofReal ((singFloor (absnSub E X hX A) B)⁻¹ ^ (4 * p)))).trans
                (singFloor_inv_moment σ hW hb _ (absn_finrank_sub_le E X hX A) h4p1
                  h4pW)).trans
                (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (singMomentConst_pos b).le hCdb
                  (by linarith)))
    -- the outer (block) integral: gap moments
    have hgapm : ∫⁻ A, ENNReal.ofReal ((absnGap E X hX A)⁻¹ ^ (2 * p))
        ∂blockLaw σ.blocks W (1 - 2 * b) ≤ ENNReal.ofReal (Cδ ^ (2 * p)) := by
      refine (hgap σ.blocks W hW (1 - 2 * b) hc E ⟨X, hX⟩ (2 * p) h2p1 h2pW).trans ?_
      refine ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (gapMomentConstant_pos _ _ _).le ?_ (by linarith))
      cases σ
      · exact hδ2
      · exact hδ2
      · exact hδ1
      · exact hδ1
    have hF : Measurable (fun ω : LayerSample W σ =>
        ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p)) :=
      ENNReal.measurable_ofReal.comp ((measurable_norm_layerResolvent σ E z X).pow_const p)
    have hmom : ∫⁻ ω, ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p) ∂layerLaw W b σ ≤
        ENNReal.ofReal (Cfin ^ p) := by
      rw [absn_layerLaw_eq, lintegral_prod _ hF.aemeasurable]
      calc ∫⁻ A, ∫⁻ B, ENNReal.ofReal (‖layerResolvent σ E z X (A, B)‖ ^ p)
            ∂absnBondLaw W b σ ∂blockLaw σ.blocks W (1 - 2 * b)
          ≤ ∫⁻ A, ENNReal.ofReal (L ^ p / 2) *
              ENNReal.ofReal ((absnGap E X hX A)⁻¹ ^ (2 * p)) * Q
              ∂blockLaw σ.blocks W (1 - 2 * b) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hgood] with A hA
            refine (hinner A hA).trans (le_of_eq ?_)
            rw [ENNReal.ofReal_mul hLp]
        _ = ENNReal.ofReal (L ^ p / 2) * (∫⁻ A, ENNReal.ofReal ((absnGap E X hX A)⁻¹ ^ (2 * p))
              ∂blockLaw σ.blocks W (1 - 2 * b)) * Q := by
            rw [lintegral_mul_const' _ _ hQtop, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (L ^ p / 2) * ENNReal.ofReal (Cδ ^ (2 * p)) * Q := by gcongr
        _ = ENNReal.ofReal (L ^ p / 2 * Cδ ^ (2 * p) * (CK ^ (12 * p) + Cd ^ (4 * p))) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hLp (Real.rpow_nonneg hCδ0.le _)),
              ENNReal.ofReal_mul hLp, ENNReal.ofReal_add (Real.rpow_nonneg hCK.le _)
                (Real.rpow_nonneg hCd.le _)]
        _ ≤ ENNReal.ofReal (Cfin ^ p) :=
            ENNReal.ofReal_le_ofReal (absn_const_le hL.le hCδ0.le hCK.le hCd.le hp0.le)
    -- the `L^p` norm
    have hmeasG : AEStronglyMeasurable (fun ω => ‖layerResolvent σ E z X ω‖) (layerLaw W b σ) :=
      (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top hmeasG,
      ENNReal.toReal_ofReal hp0.le]
    have hint : ∫⁻ ω, ‖‖layerResolvent σ E z X ω‖‖ₑ ^ p ∂layerLaw W b σ =
        ∫⁻ ω, ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p) ∂layerLaw W b σ := by
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal (norm_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    rw [hint]
    calc (∫⁻ ω, ENNReal.ofReal (‖layerResolvent σ E z X ω‖ ^ p) ∂layerLaw W b σ) ^ (1 / p)
        ≤ (ENNReal.ofReal (Cfin ^ p)) ^ (1 / p) := ENNReal.rpow_le_rpow hmom (by positivity)
      _ = ENNReal.ofReal Cfin := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC0.le _) (by positivity), one_div,
            Real.rpow_rpow_inv hC0.le hp0.ne']

/-!
## 4. The uniform clause
-/

/-- **The Gaussian absorption lemma, `b`-uniform**, from `ConditionalBlockGUECount` only.
For `β ∈ (0,1/4)`, `η₀ > 0`, `M`: `ε₁ = 1/48` and
`C = layerResolventConstant η₀ M · Cδ(β)² · (C_K¹² + C_d(β)⁴)` with
`Cδ(β) = bu_gapUnifConst C_PSSS β`, `C_K = bu_bondUnifConst`, `C_d(β) = bu_singUnifConst β`;
uniformly in `b ∈ [β, 1/2-β]`, `W ≥ 1`, the shape, Hermitian `X`, real `E`, `Im z ≥ η₀`,
`‖z‖ ≤ M`, `1 ≤ p ≤ W/48`. -/
theorem gaussianAbsorptionUniform_holds (hcount : ConditionalBlockGUECount) :
    GaussianAbsorptionUniformContract := by
  intro β hβ _ η₀ M hη
  obtain ⟨Cg, hCg, hexp⟩ := bu_gaussianAbsorption_explicit hcount
  have hδU : 0 < bu_gapUnifConst Cg β := lt_max_of_lt_left (gapMomentConstant_pos _ _ _)
  have hKU : 0 < bu_bondUnifConst := bondMomentConst_pos _
  have hdU : 0 < bu_singUnifConst β := by unfold bu_singUnifConst; positivity
  have hL : 0 < layerResolventConstant η₀ M := absn_layerResolventConstant_pos hη M
  refine ⟨1 / 48, layerResolventConstant η₀ M * bu_gapUnifConst Cg β ^ 2 *
      (bu_bondUnifConst ^ 12 + bu_singUnifConst β ^ 4), by norm_num, by positivity, ?_⟩
  intro b hb
  obtain ⟨hb0, hb1⟩ := bu_mem_bounds hβ hb
  exact hexp b hb0 hb1 η₀ M hη _ _ _
    ((bu_gapMomentConstant_le hCg.le hβ hb 1).trans (le_max_left _ _))
    ((bu_gapMomentConstant_le hCg.le hβ hb 2).trans (le_max_right _ _))
    (bu_bondMomentConst_le hb1.le) (bu_singMomentConst_le hβ hb.1 hb1.le)

/-- The uniform clause implies `GaussianAbsorptionContract` (`β = min b (1/2-b) / 2`). -/
theorem bu_gaussianAbsorption_of_uniform (hU : GaussianAbsorptionUniformContract) :
    GaussianAbsorptionContract := by
  intro b hb0 hb1 η₀ M hη
  obtain ⟨hβ0, hβ1, hbI⟩ := bu_beta_of_mem hb0 hb1
  obtain ⟨ε₁, C, hε₁, hC, h⟩ := hU _ hβ0 hβ1 η₀ M hη
  exact ⟨ε₁, C, hε₁, hC, h b hbI⟩

end BlockBand.Layers
