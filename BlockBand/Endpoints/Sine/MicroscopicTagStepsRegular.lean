module

public import BlockBand.Endpoints.Sine.MicroscopicTagInputs
public import BlockBand.Endpoints.Response.PassDerivative

/-!
# Step 2 of the microscopic tag comparison: the regular event under the window measures

The irregular event `{¬ IsBlockRegular}` need not be measurable (it involves the choice-defined
Dyson root); the statements below are therefore phrased for every **measurable** observable `G`
with `|G| ≤ 1` that vanishes on the regular event, which is exactly the form in which the
proof uses the event (the difference of the Palm and Gaussian tests is such a `G` after
truncation). Outer measures are used for the sections, through measurable hulls.

* `mts_isProbabilityMeasure_of_blockSplitting`, `mts_ae_blockState_isHermitian`: a one-block
  exterior law is a probability law, and `H_R` is a.s. Hermitian under it.
* `mts_prior_irregular_le`: `∫ |G| d𝔭_W ≤ W^{-D}` (prior window measure, `e = e(u)`).
* `mts_window_irregular_le`: `∫ |G| d𝔪⁰_W ≤ (C/ρ(E)) W^{-D}` (exact window measure), with `C`
  the constant of `OneBlockPalmContract.upper` (depending on `b` only).
In both, `b`, `E`, `T` and the window `w` are fixed first; the regularity constants come from
`BlockRegularEventContract` at the bulk margin `κ = (2 - |E|)/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal

section Splitting

variable {p : Parameters} {k : ZMod p.n} {model : p.GaussianRingModel}
  {Pω : Measure (BlockState p k)}

theorem mts_measurable_assembleBlock (p : Parameters) (k : ZMod p.n) :
    Measurable (fun x : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      assembleBlock p k x.1 x.2) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  by_cases hx : x.1 = k <;> by_cases hy : y.1 = k
  · simp only [assembleBlock, hx, hy, dite_true]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
  · simp only [assembleBlock, hx, hy, dite_true, dite_false]
    exact continuous_star.measurable.comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_snd.comp
        measurable_fst)))
  · simp only [assembleBlock, hx, hy, dite_true, dite_false]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_snd.comp
        measurable_fst))
  · simp only [assembleBlock, hx, hy, dite_false]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_fst.comp
        measurable_fst))

/-- A one-block exterior law is a probability measure (its product with `GUE_W(c/W)` maps to
the probability law `model.law`). -/
theorem mts_isProbabilityMeasure_of_blockSplitting (h : IsBlockSplitting p k model Pω) :
    IsProbabilityMeasure Pω := by
  have := passDeriv_isProbabilityMeasure_gue (BlockSite p k) (blockTime p)
  have h1 : ((Pω.prod (gueMeasure (BlockSite p k) (blockTime p))).map
      (fun x => assembleBlock p k x.1 x.2)) Set.univ = 1 := by
    rw [h]; exact measure_univ
  rw [Measure.map_apply (mts_measurable_assembleBlock p k) MeasurableSet.univ,
    Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod,
    measure_univ (μ := gueMeasure (BlockSite p k) (blockTime p)), mul_one] at h1
  exact ⟨h1⟩

/-- Under a one-block exterior law, `H_R` is almost surely Hermitian. -/
theorem mts_ae_blockState_isHermitian (h : IsBlockSplitting p k model Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian := by
  have := mts_isProbabilityMeasure_of_blockSplitting h
  have := passDeriv_isProbabilityMeasure_gue (BlockSite p k) (blockTime p)
  have hlaw := model.isPhysical.1
  rw [← h] at hlaw
  have hS : MeasurableSet {A : p.SiteMatrix | A.IsHermitian} := measurableSet_isHermitian
  have hprod := (ae_map_iff (mts_measurable_assembleBlock p k).aemeasurable hS).1 hlaw
  have hS1 : MeasurableSet {ω : BlockState p k | ω.1.IsHermitian} :=
    measurableSet_isHermitian.preimage measurable_fst
  rw [ae_iff] at hprod ⊢
  refine le_antisymm ?_ bot_le
  have hsub : {ω : BlockState p k | ¬ ω.1.IsHermitian} ×ˢ
      (Set.univ : Set (Matrix (BlockSite p k) (BlockSite p k) ℂ)) ⊆
      {x | ¬ (assembleBlock p k x.1 x.2).IsHermitian} := by
    rintro ⟨ω, G⟩ ⟨hω, -⟩ hA
    apply hω
    ext x y
    have := congrFun (congrFun hA x.1) y.1
    simp only [conjTranspose_apply] at this ⊢
    simpa [assembleBlock, x.2, y.2] using this
  have := measure_mono (μ := Pω.prod (gueMeasure (BlockSite p k) (blockTime p))) hsub
  rw [hprod, Measure.prod_prod, measure_univ, mul_one] at this
  exact this

end Splitting

section Window

variable (p : Parameters)

/-- `∫ w(Nρ(E)(e - E)) de = (Nρ(E))⁻¹ ∫ w` (the microscopic change of variables). -/
theorem mts_integral_window_microCoord {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    (w : ℝ → ℝ) :
    ∫ e, w (microCoord p E e) = ((p.N : ℝ) * Parameters.semicircleDensity E)⁻¹ * ∫ u, w u := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have ha : 0 < (p.N : ℝ) * Parameters.semicircleDensity E := mul_pos hN hρ
  unfold microCoord
  rw [integral_sub_right_eq_self (fun x => w ((p.N : ℝ) * Parameters.semicircleDensity E * x)) E,
    Measure.integral_comp_mul_left (fun x => w x), abs_of_pos (inv_pos.2 ha), smul_eq_mul]

/-- The window support: for `W` large, `w(u(e)) ≠ 0` forces `e ∈ bulkInterval κ`. -/
theorem mts_mem_bulk_of_window {E κ R : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    (hκE : E ∈ Set.Icc (-2 + 2 * κ) (2 - 2 * κ)) (hκ : 0 < κ)
    (hW : R / (κ * Parameters.semicircleDensity E) ≤ p.W) {e : ℝ}
    (he : |microCoord p E e| ≤ R) : e ∈ bulkInterval κ := by
  have hN : (p.W : ℝ) ≤ p.N := by
    unfold Parameters.N; push_cast
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast (le_trans (by norm_num) p.n_ge_four)
    nlinarith [(Nat.cast_nonneg p.W : (0 : ℝ) ≤ p.W)]
  have hR0 : 0 ≤ R := (abs_nonneg _).trans he
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hNpos : (0 : ℝ) < p.N := lt_of_lt_of_le hWpos hN
  have hR' : R ≤ κ * Parameters.semicircleDensity E * p.W := by
    rw [div_le_iff₀ (mul_pos hκ hρ)] at hW; linarith
  have hdist : |e - E| ≤ κ := by
    unfold microCoord at he
    rw [abs_mul, abs_of_pos (mul_pos hNpos hρ)] at he
    have h1 : (p.N : ℝ) * Parameters.semicircleDensity E * |e - E| ≤
        κ * Parameters.semicircleDensity E * p.N := by
      refine he.trans (hR'.trans ?_)
      exact mul_le_mul_of_nonneg_left hN (mul_pos hκ hρ).le
    have h2 : Parameters.semicircleDensity E * p.N * |e - E| ≤
        Parameters.semicircleDensity E * p.N * κ := by linarith
    exact le_of_mul_le_mul_left h2 (mul_pos hρ hNpos)
  obtain ⟨h1, h2⟩ := abs_le.1 hdist
  exact ⟨by linarith [hκE.1], by linarith [hκE.2]⟩

end Window

/-- The section bound: if `G` is measurable, `|G| ≤ 1`, and `G = 0` off a set `B` with
(outer) `Pω(B) ≤ β`, then `∫ |G| dPω ≤ β`. -/
theorem mts_lintegral_abs_le_of_vanish {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {g : Ω → ℝ} (hg1 : ∀ x, |g x| ≤ 1) {B : Set Ω} (hB : ∀ x, x ∉ B → g x = 0) {β : ℝ≥0∞}
    (hβ : μ B ≤ β) : ∫⁻ x, ENNReal.ofReal |g x| ∂μ ≤ β := by
  have hle : ∀ x, ENNReal.ofReal |g x| ≤ (toMeasurable μ B).indicator 1 x := by
    intro x
    by_cases hx : x ∈ toMeasurable μ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hg1 x)
    · have : x ∉ B := fun h => hx (subset_toMeasurable μ B h)
      rw [hB x this]; simp
  calc ∫⁻ x, ENNReal.ofReal |g x| ∂μ ≤ ∫⁻ x, (toMeasurable μ B).indicator 1 x ∂μ :=
        lintegral_mono hle
    _ = μ B := by rw [lintegral_indicator_one (measurableSet_toMeasurable μ B),
        measure_toMeasurable]
    _ ≤ β := hβ

/-- Support radius of a compactly supported `w`. -/
theorem mts_exists_support_radius {w : ℝ → ℝ} (hw : HasCompactSupport w) :
    ∃ R : ℝ, ∀ u, w u ≠ 0 → |u| ≤ R := by
  obtain ⟨R, hR⟩ := hw.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => ?_⟩
  have : u ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport w hu)
  simpa [Real.dist_eq] using this

theorem mts_semicircleDensity_pos {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  have : 0 < 4 - E ^ 2 := by nlinarith
  exact div_pos (Real.sqrt_pos.2 this) (by positivity)

theorem mts_bulk_margin {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < (2 - |E|) / 2 ∧ E ∈ Set.Icc (-2 + 2 * ((2 - |E|) / 2)) (2 - 2 * ((2 - |E|) / 2)) := by
  refine ⟨by cases abs_cases E <;> linarith, ?_, ?_⟩ <;> cases abs_cases E <;> linarith

/-- **(f), prior form.** Fixed first `b`, bulk `E`, `T` and a window `w`; the regularity
constants `r₀, s₀, v₀` (at the bulk margin `κ = (2-|E|)/2`), then for every `D > 0` a norm
exponent `A`, then for every `η > 0` a width `W₀`: for every admissible `p` with `W ≥ W₀`,
`n ≤ TW`, every model, block, one-block exterior law, reindexing `σ` and measurable `G(u, ω)`
with `|G| ≤ 1` vanishing on the regular event at `e = e(u)`,
`∫ |G| d𝔭_W ≤ W^{-D}` (`𝔭_W = w(u) du dPω`). Input: `BlockRegularEventContract`. -/
theorem mts_prior_irregular_le (hReg : BlockRegularEventContract)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (T : ℝ)
    {w : ℝ → ℝ} (hw : IsWindow w) :
    ∃ r₀ s₀ v₀ : ℝ, FreshConstants (1 - 2 * b) r₀ s₀ v₀ ∧
    ∀ D : ℝ, 0 < D → ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ W₀ : ℕ,
    ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (G : ℝ × BlockState p k → ℝ),
      Measurable G → (∀ x, |G x| ≤ 1) →
      (∀ u ω, IsBlockRegular p k σ A r₀ s₀ v₀ η (microEnergy p E u) ω → G (u, ω) = 0) →
      ∫⁻ x, ENNReal.ofReal |G x| ∂priorWindowMeasure Pω w ≤
        ENNReal.ofReal ((p.W : ℝ) ^ (-D)) := by
  obtain ⟨hκ, hκE⟩ := mts_bulk_margin hE1 hE2
  set κ := (2 - |E|) / 2
  have hρ : 0 < Parameters.semicircleDensity E := mts_semicircleDensity_pos hE1 hE2
  obtain ⟨R, hR⟩ := mts_exists_support_radius hw.2.1
  obtain ⟨r₀, s₀, v₀, hFC, hDc⟩ := hReg b hb hb' κ T hκ
  refine ⟨r₀, s₀, v₀, hFC, fun D hD => ?_⟩
  obtain ⟨A, hA⟩ := hDc D hD
  refine ⟨A, fun η hη => ?_⟩
  obtain ⟨W₁, hW₁⟩ := hA η hη
  refine ⟨max W₁ (⌈R / (κ * Parameters.semicircleDensity E)⌉₊), ?_⟩
  intro p hpb hW hn model k Pω hsplit σ G hGm hG1 hGreg
  have := mts_isProbabilityMeasure_of_blockSplitting hsplit
  have hWR : R / (κ * Parameters.semicircleDensity E) ≤ p.W :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hW)
  have hwm : Measurable fun u => ENNReal.ofReal (w u) :=
    ENNReal.measurable_ofReal.comp hw.1.measurable
  -- sections
  have hsec : ∀ u, w u ≠ 0 →
      ∫⁻ ω, ENNReal.ofReal |G (u, ω)| ∂Pω ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-D)) := by
    intro u hu
    have hmem : microEnergy p E u ∈ bulkInterval κ := by
      refine mts_mem_bulk_of_window p hρ hκE hκ hWR ?_
      have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
      have : microCoord p E (microEnergy p E u) = u := by
        unfold microCoord microEnergy; field_simp; ring
      rw [this]; exact hR u hu
    refine mts_lintegral_abs_le_of_vanish Pω (fun ω => hG1 _)
      (B := {ω | ¬ IsBlockRegular p k σ A r₀ s₀ v₀ η (microEnergy p E u) ω}) ?_
      (hW₁ p hpb ((le_max_left _ _).trans hW) hn model k Pω hsplit σ _ hmem)
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_not] at hω
    exact hGreg u ω hω
  calc ∫⁻ x, ENNReal.ofReal |G x| ∂priorWindowMeasure Pω w
      ≤ ∫⁻ u, ∫⁻ ω, ENNReal.ofReal |G (u, ω)| ∂Pω
          ∂(volume.withDensity fun u => ENNReal.ofReal (w u)) := lintegral_prod_le _
    _ = ∫⁻ u, ENNReal.ofReal (w u) * ∫⁻ ω, ENNReal.ofReal |G (u, ω)| ∂Pω := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hwm]
        · rfl
        · exact (Measurable.lintegral_prod_right'
            (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hGm)))
    _ ≤ ∫⁻ u, ENNReal.ofReal (w u) * ENNReal.ofReal ((p.W : ℝ) ^ (-D)) := by
        refine lintegral_mono fun u => ?_
        by_cases hu : w u = 0
        · simp [hu]
        · exact mul_le_mul' le_rfl (hsec u hu)
    _ = ENNReal.ofReal ((p.W : ℝ) ^ (-D)) := by
        rw [lintegral_mul_const _ hwm, ← ofReal_integral_eq_lintegral_ofReal
          (hw.1.integrable_of_hasCompactSupport hw.2.1) (ae_of_all _ hw.2.2.1), hw.2.2.2,
          ENNReal.ofReal_one, one_mul]

/-- **(f), window form** (the regular event transferred from the prior to the exact window
measure). Fixed first `b`, bulk `E`, `T`, a window `w`; the constant `C` of
`OneBlockPalmContract.upper` (depending on `b` only), the regularity constants, then `D ↦ A`,
`η ↦ W₀`: for every admissible `p` with `W ≥ W₀`, `n ≤ TW`, every model, block, one-block
exterior law, measurable frame, reindexing `σ` and measurable `G(e, ω)` with `|G| ≤ 1`
vanishing on the regular event at `e`,
`∫ |G| d𝔪⁰_W ≤ (C/ρ(E)) W^{-D}` (`𝔪⁰_W = n w(u(e)) Z₀(e) de dPω`). Inputs:
`BlockRegularEventContract` and `OneBlockPalmContract.upper`; the energy Jacobian
`n/(Nρ(E)) = 1/(Wρ(E))` cancels the factor `W` of `Z₀ ≤ CW`. -/
theorem mts_window_irregular_le (hReg : BlockRegularEventContract)
    (hPalm : OneBlockPalmContract)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (T : ℝ)
    {w : ℝ → ℝ} (hw : IsWindow w) :
    ∃ C : ℝ, ∃ r₀ s₀ v₀ : ℝ, FreshConstants (1 - 2 * b) r₀ s₀ v₀ ∧
    ∀ D : ℝ, 0 < D → ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ W₀ : ℕ,
    ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω → ∀ U, IsBlockFrame p k U →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (G : ℝ × BlockState p k → ℝ),
      Measurable G → (∀ x, |G x| ≤ 1) →
      (∀ e ω, IsBlockRegular p k σ A r₀ s₀ v₀ η e ω → G (e, ω) = 0) →
      ∫⁻ x, ENNReal.ofReal |G x| ∂blockWindowMeasure p k U Pω E w ≤
        ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) := by
  obtain ⟨hκ, hκE⟩ := mts_bulk_margin hE1 hE2
  set κ := (2 - |E|) / 2
  have hρ : 0 < Parameters.semicircleDensity E := mts_semicircleDensity_pos hE1 hE2
  obtain ⟨R, hR⟩ := mts_exists_support_radius hw.2.1
  obtain ⟨C₀, hC₀⟩ := hPalm.upper b hb hb'
  set C₁ := max C₀ 0
  refine ⟨C₁ / Parameters.semicircleDensity E, ?_⟩
  obtain ⟨r₀, s₀, v₀, hFC, hDc⟩ := hReg b hb hb' κ T hκ
  refine ⟨r₀, s₀, v₀, hFC, fun D hD => ?_⟩
  obtain ⟨A, hA⟩ := hDc D hD
  refine ⟨A, fun η hη => ?_⟩
  obtain ⟨W₁, hW₁⟩ := hA η hη
  refine ⟨max W₁ (⌈R / (κ * Parameters.semicircleDensity E)⌉₊), ?_⟩
  intro p hpb hW hn model k Pω hsplit U hU σ G hGm hG1 hGreg
  have := mts_isProbabilityMeasure_of_blockSplitting hsplit
  have hWR : R / (κ * Parameters.semicircleDensity E) ≤ p.W :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hW)
  have hWpos : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  -- the window weight in the energy coordinate
  set a : ℝ → ℝ≥0∞ := fun e => ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E e)) with ha_def
  have hmc : Measurable (microCoord p E) := by unfold microCoord; fun_prop
  have ham : Measurable a :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hw.1.measurable.comp hmc))
  set g : ℝ × BlockState p k → ℝ≥0∞ := fun x => a x.1 * ENNReal.ofReal (C₁ * p.W)
  have hgm : Measurable g := (ham.comp measurable_fst).mul_const _
  -- density domination
  have hdom : (fun x : ℝ × BlockState p k => ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E x.1)) *
      blockNormalizer p k U x.2 x.1) ≤ᵐ[volume.prod Pω] g := by
    have h1 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := Pω)).ae
      (mts_ae_blockState_isHermitian hsplit)
    filter_upwards [h1] with x hx
    refine mul_le_mul' le_rfl ((hC₀ p hpb k U hU x.2 hx x.1).trans ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hWpos.le)
  -- sections
  have hsec : ∀ e, a e ≠ 0 →
      ∫⁻ ω, ENNReal.ofReal |G (e, ω)| ∂Pω ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-D)) := by
    intro e he
    have hwe : w (microCoord p E e) ≠ 0 := by
      intro h0; apply he; simp [ha_def, h0]
    have hmem : e ∈ bulkInterval κ := mts_mem_bulk_of_window p hρ hκE hκ hWR (hR _ hwe)
    refine mts_lintegral_abs_le_of_vanish Pω (fun ω => hG1 _)
      (B := {ω | ¬ IsBlockRegular p k σ A r₀ s₀ v₀ η e ω}) ?_
      (hW₁ p hpb ((le_max_left _ _).trans hW) hn model k Pω hsplit σ e hmem)
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_not] at hω
    exact hGreg e ω hω
  have hGa : Measurable fun x : ℝ × BlockState p k => ENNReal.ofReal |G x| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hGm)
  -- the integral of the window weight
  have hint : ∫⁻ e, a e = ENNReal.ofReal ((p.W : ℝ)⁻¹ * (Parameters.semicircleDensity E)⁻¹) := by
    have hi : Integrable (fun e => (p.n : ℝ) * w (microCoord p E e)) := by
      have h0 : Integrable (fun e => w (microCoord p E e)) := by
        refine Integrable.of_integral_ne_zero ?_
        rw [mts_integral_window_microCoord p hρ w, hw.2.2.2, mul_one]
        have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
        exact (inv_pos.2 (mul_pos hN hρ)).ne'
      exact h0.const_mul _
    rw [ha_def, ← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun e => mul_nonneg hnpos.le (hw.2.2.1 _)), integral_const_mul,
      mts_integral_window_microCoord p hρ w, hw.2.2.2]
    congr 1
    unfold Parameters.N; push_cast
    field_simp
  calc ∫⁻ x, ENNReal.ofReal |G x| ∂blockWindowMeasure p k U Pω E w
      ≤ ∫⁻ x, ENNReal.ofReal |G x| ∂((volume.prod Pω).withDensity g) :=
        lintegral_mono' (withDensity_mono hdom) le_rfl
    _ = ∫⁻ x, g x * ENNReal.ofReal |G x| ∂(volume.prod Pω) :=
        lintegral_withDensity_eq_lintegral_mul _ hgm hGa
    _ ≤ ∫⁻ e, ∫⁻ ω, g (e, ω) * ENNReal.ofReal |G (e, ω)| ∂Pω := lintegral_prod_le _
    _ = ∫⁻ e, a e * ENNReal.ofReal (C₁ * p.W) * ∫⁻ ω, ENNReal.ofReal |G (e, ω)| ∂Pω := by
        refine lintegral_congr fun e => ?_
        show ∫⁻ ω, a e * ENNReal.ofReal (C₁ * p.W) * ENNReal.ofReal |G (e, ω)| ∂Pω = _
        exact lintegral_const_mul _ (f := fun ω => ENNReal.ofReal |G (e, ω)|)
          (hGa.comp (measurable_const.prodMk measurable_id) :
            Measurable fun ω => ENNReal.ofReal |G (e, ω)|)
    _ ≤ ∫⁻ e, a e * ENNReal.ofReal (C₁ * p.W) * ENNReal.ofReal ((p.W : ℝ) ^ (-D)) := by
        refine lintegral_mono fun e => ?_
        by_cases he : a e = 0
        · simp [he]
        · exact mul_le_mul' le_rfl (hsec e he)
    _ = (∫⁻ e, a e) * (ENNReal.ofReal (C₁ * p.W) * ENNReal.ofReal ((p.W : ℝ) ^ (-D))) := by
        rw [← lintegral_mul_const _ ham]
        refine lintegral_congr fun e => ?_
        ring
    _ = ENNReal.ofReal (C₁ / Parameters.semicircleDensity E * (p.W : ℝ) ^ (-D)) := by
        rw [hint, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end BlockBand.Endpoints
