module

public import BlockBand.Critical.MatrixClosing.Poles.GoodEventRegular

/-!
# The good event of the conditional collar: the exceptional events

*Law.* `layerLaw W b .common` (end diagonals `A_j ~ GUE_W(c/W)`, bonds `Gin(b/W)`), `b < 1/2`,
`c = 1 - 2b`, conditional on deterministic Hermitian `X`; energies `e ∈ bulkInterval κ`.

* `collarRegEvent W b e τ X`: `A` Hermitian, `D` invertible, `‖D⁻¹‖ ≤ W³`, `Σ|B_xy|² ≤ W³`,
  `|W⁻¹Tr 𝒢_port - a| ≤ τ`.
* `layerLaw_compl_collarRegEvent_le`: `P(regᶜ) ≤ (4C_w/√c + 2b + C_T)/W²` given the trace bound
  `P(|W⁻¹Tr 𝒢_port - a| > τ) ≤ C_T/W²` (Wegner: `layerLaw_collarTopBlock_inv_bad_le`, native
  PSSS; Frobenius: `layerLaw_frobenius_bad_le`).
* `layerLaw_entry_bad_le`: `P(|u^*(LL^* - E LL^*)v| > θ) ≤ C²/(θ²W)` for unit `u, v`
  (`CommonPortMeanContract.fluctuation` at `p = 2`, Chebyshev).
* `layerLaw_commonPortL_sq_bad_le`: `P(‖L‖² > R) ≤ C₄⁴/R²` (`CommonPortMeanContract.moments`
  at `p = 4`, Markov).
* `tendsto_zero_of_slack`: a sequence in `[0, ∞]` eventually below `g_N + η` for every `η > 0`,
  with `g_N → 0` (depending on `η`), tends to `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The regular event of the conditional collar. -/
def collarRegEvent (W : ℕ) (b e τ : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Set (LayerSample W .common) :=
  {ω | (∀ j, (ω.1 j).IsHermitian) ∧ IsUnit (Collar.Density.collarTopBlock e X ω).det ∧
    (∀ v, ∑ a, ‖((Collar.Density.collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤
      ((((W : ℝ) ^ 3)⁻¹) ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2) ∧
    ∑ x, ∑ y, ‖bondMatrix .common ω.2 x y‖ ^ 2 ≤ (W : ℝ) ^ 3 ∧
    ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖ ≤ τ}

/-- **The exceptional set of the regular event.** -/
theorem layerLaw_compl_collarRegEvent_le (source : BlockBand.External.PSSS.SourceContract.{0}) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ (W : ℕ), 0 < W → ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ (e : ℝ)
      (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), X.IsHermitian → ∀ τ CT : ℝ, 0 ≤ CT →
      layerLaw W b .common
          {ω | τ < ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖} ≤
        ENNReal.ofReal (CT / (W : ℝ) ^ 2) →
      layerLaw W b .common (collarRegEvent W b e τ X)ᶜ ≤
        ENNReal.ofReal ((4 * Cw / Real.sqrt (1 - 2 * b) + 2 * b + CT) / (W : ℝ) ^ 2) := by
  obtain ⟨Cw, hCw, hweg⟩ := Collar.Density.layerLaw_collarTopBlock_inv_bad_le source
  refine ⟨Cw, hCw, fun W hW b hb0 hb e X hX τ CT hCT htr => ?_⟩
  set μ := layerLaw W b .common
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set t : ℝ := ((W : ℝ) ^ 3)⁻¹
  have ht : 0 < t := by positivity
  set β : ℝ := (W : ℝ) ^ 3
  have hβ : 0 < β := by positivity
  set B1 : Set (LayerSample W .common) := {ω | ¬ ∀ j, (ω.1 j).IsHermitian}
  set B2 : Set (LayerSample W .common) := {ω | ¬ ∀ v, ∑ a,
    ‖((Collar.Density.collarTopBlock e X ω)⁻¹ *ᵥ v) a‖ ^ 2 ≤ (t ^ 2)⁻¹ * ∑ a, ‖v a‖ ^ 2}
  set B3 : Set (LayerSample W .common) :=
    {ω | β < ∑ x, ∑ y, ‖bondMatrix .common ω.2 x y‖ ^ 2}
  set B4 : Set (LayerSample W .common) :=
    {ω | τ < ‖portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 - matchedA e‖}
  set B5 : Set (LayerSample W .common) :=
    {ω | ¬ IsUnit (Collar.Density.collarTopBlock e X ω).det}
  have hsub : (collarRegEvent W b e τ X)ᶜ ⊆ B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 := by
    intro ω hω
    simp only [collarRegEvent, Set.mem_compl_iff, Set.mem_ofPred_eq] at hω
    simp only [B1, B2, B3, B4, B5, Set.mem_union, Set.mem_ofPred_eq, t, β]
    by_contra hc
    simp only [not_or, not_not, not_lt] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    exact hω ⟨h1, h5, h2, h3, h4⟩
  have hB1 : μ B1 = 0 := by
    have := BlockBand.Layers.lct_ae_blocks_isHermitian W b .common
    rwa [ae_iff] at this
  have hB5 : μ B5 = 0 := by
    have := Collar.Density.ae_isUnit_det_collarTopBlock (b := b) hb hW e X
    rwa [ae_iff] at this
  have hB2 : μ B2 ≤ ENNReal.ofReal (4 * Cw / Real.sqrt (1 - 2 * b) / (W : ℝ) ^ 2) := by
    refine (hweg W hW b hb e X hX t ht).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [t]; field_simp; ring
  have hB3 : μ B3 ≤ ENNReal.ofReal (2 * b / (W : ℝ) ^ 2) := by
    refine (Collar.Density.layerLaw_frobenius_bad_le W b hβ).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [β]; field_simp
  have h0 := measure_union_le (μ := μ) (B1 ∪ B2 ∪ B3 ∪ B4) B5
  have h1 := measure_union_le (μ := μ) (B1 ∪ B2 ∪ B3) B4
  have h2 := measure_union_le (μ := μ) (B1 ∪ B2) B3
  have h3 := measure_union_le (μ := μ) B1 B2
  rw [hB1, zero_add] at h3
  rw [hB5, add_zero] at h0
  refine (measure_mono hsub).trans (h0.trans (h1.trans ((add_le_add (h2.trans
    (add_le_add (h3.trans hB2) hB3)) htr).trans (le_of_eq ?_))))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp

theorem rpow_neg_half_sq {x : ℝ} (hx : 0 < x) : (x ^ (-(1 : ℝ) / 2)) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num
  exact Real.rpow_neg_one x

/-- **Chebyshev for the projected fluctuation** (`CommonPortMeanContract.fluctuation`, `p = 2`). -/
theorem layerLaw_entry_bad_le (hCM : CommonPortMeanContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (Cf : ℝ) (Wf : ℕ), 0 ≤ Cf ∧ ∀ (W : ℕ), 0 < W → Wf ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, ∀ u v : Fin 2 × Fin W → ℂ, l2Norm u = 1 → l2Norm v = 1 →
      ∀ θ : ℝ, 0 < θ →
        layerLaw W b .common {ω | θ < ‖star u ⬝ᵥ ((commonPortLL b e X ω -
          matrixExpect (layerLaw W b .common) (commonPortLL b e X)) *ᵥ v)‖} ≤
        ENNReal.ofReal (Cf ^ 2 / (θ ^ 2 * W)) := by
  obtain ⟨C, Wf, hfl⟩ := hCM.fluctuation b hb0 hb κ hκ 2 le_rfl
  refine ⟨max C 0, Wf, le_max_right _ _, fun W hW hWf X hX e he u v hu hv θ hθ => ?_⟩
  set μ := layerLaw W b .common
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set g : LayerSample W .common → ℂ := fun ω => star u ⬝ᵥ ((commonPortLL b e X ω -
    matrixExpect μ (commonPortLL b e X)) *ᵥ v)
  have hflW := hfl W hW hWf X hX e he u v
  rw [hu, hv, mul_one, mul_one] at hflW
  have hsub : {ω | θ < ‖g ω‖} ⊆ {ω | ENNReal.ofReal θ ≤ ‖g ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hω.le
  refine (measure_mono hsub).trans ?_
  have hp : (ENNReal.ofReal 2).toReal = 2 := by simp
  have hcheb := mul_meas_ge_le_pow_eLpNorm' μ
    (p := ENNReal.ofReal 2) (by simp) ENNReal.ofReal_ne_top (f := g) (ENNReal.ofReal θ)
  rw [hp, ENNReal.rpow_two, ENNReal.rpow_two] at hcheb
  rw [← ENNReal.ofReal_pow hθ.le] at hcheb
  have hpos : ENNReal.ofReal (θ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)] at hcheb
  refine hcheb.trans ?_
  have hflW' : eLpNorm g (ENNReal.ofReal 2) μ ≤
      ENNReal.ofReal (max C 0 * (W : ℝ) ^ (-(1 : ℝ) / 2)) :=
    hflW.trans (ENNReal.ofReal_le_ofReal (by
      have : C ≤ max C 0 := le_max_left _ _
      have := Real.rpow_nonneg hWr.le (-(1 : ℝ) / 2)
      gcongr))
  have hL := pow_le_pow_left' hflW' 2
  refine (ENNReal.div_le_div_right hL _).trans (le_of_eq ?_)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  rw [mul_pow, rpow_neg_half_sq hWr]
  field_simp

/-- **Markov for `‖L‖²`** (`CommonPortMeanContract.moments`, `p = 4`). -/
theorem layerLaw_commonPortL_sq_bad_le (hCM : CommonPortMeanContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C4 : ℝ) (W4 : ℕ), 0 ≤ C4 ∧ ∀ (W : ℕ), 0 < W → W4 ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, ∀ R : ℝ, 0 < R →
        layerLaw W b .common {ω | R < ‖commonPortL b e X ω‖ ^ 2} ≤
          ENNReal.ofReal (C4 ^ 4 / R ^ 2) := by
  obtain ⟨C, W4, hmom⟩ := hCM.moments b hb0 hb κ hκ 4 (by norm_num)
  refine ⟨max C 0, W4, le_max_right _ _, fun W hW hW4 X hX e he R hR => ?_⟩
  set μ := layerLaw W b .common
  have hLm := BlockBand.Critical.CommonPort.measurable_commonPortL b e X
  have hnLm : Measurable fun ω => ‖commonPortL b e X ω‖ := continuous_norm.measurable.comp hLm
  have hmom4 := Collar.Density.lintegral_ofReal_pow_four_le hnLm (fun ω => norm_nonneg _)
    (le_max_right C 0)
    (((hmom W hW hW4 X hX e he).1).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hfm : Measurable fun ω => ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4) :=
    ENNReal.measurable_ofReal.comp (hnLm.pow_const 4)
  have hsub : {ω | R < ‖commonPortL b e X ω‖ ^ 2} ⊆
      {ω | ENNReal.ofReal (R ^ 2) ≤ ENNReal.ofReal (‖commonPortL b e X ω‖ ^ 4)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine ENNReal.ofReal_le_ofReal ?_
    have : ‖commonPortL b e X ω‖ ^ 4 = (‖commonPortL b e X ω‖ ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ hR.le hω.le 2
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hfm.aemeasurable (ENNReal.ofReal_pos.2 (by positivity)).ne'
    ENNReal.ofReal_ne_top).trans ?_
  refine (ENNReal.div_le_div_right hmom4 _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]

/-- A `[0, ∞]`-valued sequence that is eventually below `g_N + η` for every `η > 0` (with
`g_N → 0` depending on `η`) tends to `0`. -/
theorem tendsto_zero_of_slack {f : ℕ → ℝ≥0∞}
    (h : ∀ η : ℝ, 0 < η → ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ N in atTop, f N ≤ ENNReal.ofReal (g N + η)) :
    Tendsto f atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ⊤
  · exact Eventually.of_forall fun N => hδt ▸ le_top
  have hd : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  obtain ⟨g, hg, hf⟩ := h (δ.toReal / 2) (by positivity)
  have hg' : ∀ᶠ N in atTop, g N < δ.toReal / 2 := hg.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hf, hg'] with N h1 h2
  refine h1.trans ?_
  rw [ENNReal.ofReal_le_iff_le_toReal hδt]
  linarith

end BlockBand.Critical.MatrixClosing.Poles
