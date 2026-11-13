module

public import BlockBand.Layers.RingDecomposition

/-!
# The ring clauses of the matched-traces theorem: the common port

Step 5 of the proof of the matched-traces theorem: "The common port has the parameter
`z₀ = a⁻¹ + 2ba` ... Lemma layer-contraction gives the mean bound for this layer, and the
Poincaré inequality the fluctuation bound." `commonPort_of_path` proves the exact type of the
`commonPort` field of `MatchedTracesContract` (the common-port trace), from `hcount`, `hgrad` and
the `path` clause `hpath` (proved as `matchedTracesPath_of_core hcount hgrad hcore` in
`BlockBand.Layers.PathTraces`).

Law: `model.law` (any realization of the exact physical law); by
`rng_eLpNorm_commonPort` the `L^q` norm equals the one under
`layerLaw W b .common ⊗ pathLaw W (n-3) b` of `‖W⁻¹Tr 𝒢_port - a‖`, `𝒢` the common-port layer
resolvent at `z₀ = commonZ b E` and `X = pathSchur E π` (the separate-port Schur matrix of the
middle `n-3 ≥ 1` blocks). Pointwise, with `g = W⁻¹Tr 𝒢_port`, `m(X) = E_ℓ g`:
`|g - a| ≤ |g - m(X)| + (C d(X) + C W⁻²) + M₀ 1{d(X) > d_*}`, `M₀ = (Im z₀)⁻¹ + 1`
(the layer-contraction lemma, common port, on `d ≤ d_*`; crude bound `|g| ≤ (Im z₀)⁻¹` off it).
Minkowski; Fubini with the fluctuation clause of the trace–matrix lemma (`D = Q_0`, `‖D‖ ≤ 1`) for
the first term; the path clause for `‖d(X)‖_q ≤ C√q/W`; Markov with the `q`-th moment for the
exit event. Result `‖·‖_q ≤ C√q/W` for `2 ≤ q ≤ ε₀W`, uniformly in `4 ≤ n ≤ TW`, every block
`k`, `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- The common-port layer Schur matrix is Hermitian for Hermitian `X` and Hermitian blocks. -/
theorem rng_layerSchur_common_isHermitian {W : ℕ} (E : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (ω : LayerSample W .common) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (layerSchur .common E X ω).IsHermitian := by
  have hD : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian := blockDiag_isHermitian hA
  have hM := layerDiag_isHermitian (σ := .common) E X hX ω hD
  exact isHermitian_conjTranspose_mul_mul (bondMatrix .common ω.2) hM.inv

/-- **Crude bound** on the common port trace: `|W⁻¹Tr 𝒢_port| ≤ (Im z)⁻¹`. -/
theorem rng_norm_portTrace_le {W : ℕ} (E : ℝ) {z : ℂ} (hz : 0 < z.im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (ω : LayerSample W .common) (hA : ∀ j, (ω.1 j).IsHermitian)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - X).det) :
    ‖portBlockTrace (layerResolvent .common E z X ω) 0‖ ≤ z.im⁻¹ := by
  have hSch := rng_layerSchur_common_isHermitian E hX ω hA
  have hblk : (layerResolvent .common E z X ω).toBlocks₂₂ =
      (z • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - layerSchur .common E X ω)⁻¹ := by
    rw [layerResolvent, layerMatrix, pg_toBlocks22_inv _ _ _ _ hS]
    rfl
  have hpt : portBlockTrace (layerResolvent .common E z X ω) 0 =
      blockTrace (layerResolvent .common E z X ω).toBlocks₂₂ 0 := rfl
  have heq : z • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - layerSchur .common E X ω =
      -layerSchur .common E X ω - diagonal (fun _ => -z) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp; ring
  rw [hpt, hblk]
  refine (lct_norm_blockTrace_le _ 0).trans ?_
  rw [heq]
  exact lct_norm_shifted_inv_le _ hSch.neg _ hz fun _ => by simp

/-- A uniform lower bound `η ≤ Im z₀(E)` and `|E| ≤ 2` on `bulkInterval κ` (`b < 1/2`). -/
theorem rng_commonZ_im_lower {b κ : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ ∀ E ∈ bulkInterval κ, η ≤ (commonZ b E).im ∧ |E| ≤ 2 := by
  by_cases h : (bulkInterval κ).Nonempty
  · obtain ⟨E₀, hE₀⟩ := h
    exact ⟨_, (commonZ_im_pos_of_mem_bulkInterval hb hκ hE₀).1, fun E hE =>
      ⟨(commonZ_im_pos_of_mem_bulkInterval hb hκ hE).2,
        (abs_lt_two_of_mem_bulkInterval hκ hE).le⟩⟩
  · exact ⟨1, one_pos, fun E hE => absurd ⟨E, hE⟩ h⟩

/-- The common port trace `g(ℓ, X)`. -/
def rngG (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .common) : ℂ :=
  portBlockTrace (layerResolvent .common E (commonZ b E) X ℓ) 0

theorem rng_measurable_G {Ω : Type*} [MeasurableSpace Ω] (b E : ℝ) {W : ℕ}
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .common}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) : Measurable (fun t => rngG b E (Xf t) (ℓf t)) := by
  have hG := rng_measurable_layerResolvent .common E (commonZ b E) hX hℓ
  unfold rngG portBlockTrace
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ => pg_entry hG _ _)

/-- **The common-port clause** (the common-port trace) of the matched-traces theorem: the exact
type of the `commonPort` field of `MatchedTracesContract`, from `ConditionalBlockGUECount`,
`GaussianLpGradient` and the `path` clause. -/
theorem commonPort_of_path
    (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient)
    (hpath : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
      ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
          eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
              ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
            (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W)) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ), E ∈ bulkInterval κ →
      ∀ q : ℝ, 2 ≤ q → q ≤ ε₀ * p.W →
        eLpNorm (fun H => ‖oneBlockTrace p k ((commonZ b E • 1 - oneBlockComplement p k H E)⁻¹) -
            matchedA E‖) (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
          ENNReal.ofReal (C * Real.sqrt q / p.W) := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨dstar, Cl, qstar, hds, -, -, hcon⟩ := layerContraction_holds hcount b hb0 hb1 κ hκ
  obtain ⟨η, hη, hηE⟩ := rng_commonZ_im_lower hb1 hκ
  obtain ⟨ε₃, Cf, hε₃, hfl⟩ := (traceMatrix_holds hcount hgrad).fluctuation b hb0 hb1 η 3 hη 1
  obtain ⟨εp, Cp, hεp, hpb⟩ := hpath b hb0 hb1 κ T hκ
  set Cl' := max Cl 0 with hCl'
  set Cf' := max Cf 0 with hCf'
  set Cp' := max Cp 0 with hCp'
  set M0 := η⁻¹ + 1 with hM0def
  have hCl0 : 0 ≤ Cl' := le_max_right _ _
  have hCf0 : 0 ≤ Cf' := le_max_right _ _
  have hCp0 : 0 ≤ Cp' := le_max_right _ _
  have hM0 : 0 ≤ M0 := by positivity
  refine ⟨min ε₃ εp, Cf' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar), lt_min hε₃ hεp, ?_⟩
  intro p hpb' hnT model k E hE q hq2 hqε
  subst hpb'
  set b := p.b
  set W := p.W
  set r := p.n - 3 with hr
  have hW : 0 < W := p.W_pos
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hn4 := p.n_ge_four
  have hr1 : 1 ≤ r := by omega
  have hrT : (r : ℝ) ≤ T * W := le_trans (by exact_mod_cast (by omega : r ≤ p.n)) hnT
  have hq0 : 0 < q := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr (by linarith)
  have hq0' : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hqε₃ : q ≤ ε₃ * W := hqε.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le)
  have hqεp : q ≤ εp * W := hqε.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
  obtain ⟨hzη, hEabs⟩ := hηE E hE
  have hz0 : 0 < (commonZ b E).im := hη.trans_le hzη
  have hz3 : ‖commonZ b E‖ ≤ 3 := norm_commonZ_le hb0.le (by linarith) hEabs
  have hsq : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  set x := Real.sqrt q / W with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxW2 : 1 / (W : ℝ) ^ 2 ≤ x := by
    refine le_trans ?_ (div_le_div_of_nonneg_right hsq hWr.le)
    exact one_div_le_one_div_of_le hWr (by nlinarith)
  rw [rng_eLpNorm_commonPort model k E (ENNReal.ofReal q)]
  -- notation
  set μ := (layerLaw W b .common).prod (pathLaw W r b) with hμ
  set d : PathSample W r → ℝ := fun π => matchedDistance b E (pathSchur E π) with hd
  set m : PathSample W r → ℂ := fun π =>
    ∫ ℓ, rngG b E (pathSchur E π) ℓ ∂layerLaw W b .common with hm
  have hdm : Measurable d := (srec_measurable_matchedDistance b E W).comp (measurable_pathSchur W r E)
  have hgm : Measurable (fun x : LayerSample W .common × PathSample W r =>
      rngG b E (pathSchur E x.2) x.1) :=
    rng_measurable_G b E ((measurable_pathSchur W r E).comp measurable_snd) measurable_fst
  have hmm : Measurable m := by
    have h := StronglyMeasurable.integral_prod_left (μ := layerLaw W b .common)
      (f := fun (ℓ : LayerSample W .common) (π : PathSample W r) => rngG b E (pathSchur E π) ℓ)
      hgm.stronglyMeasurable
    exact h.measurable
  -- the pieces
  set S := {π : PathSample W r | dstar < d π} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hdm
  set f1 : LayerSample W .common × PathSample W r → ℝ :=
    fun x => ‖rngG b E (pathSchur E x.2) x.1 - m x.2‖ with hf1
  set f2 : LayerSample W .common × PathSample W r → ℝ :=
    fun x => Cl' * d x.2 + Cl' / (W : ℝ) ^ 2 with hf2
  set f4 : LayerSample W .common × PathSample W r → ℝ :=
    (Prod.snd ⁻¹' S).indicator (fun _ => M0) with hf4
  have hd0 : ∀ π, 0 ≤ d π := fun π => (norm_nonneg _).trans (le_max_left _ _)
  -- a.e. facts on the product
  have hA : ∀ᵐ x ∂μ, ∀ j, (x.1.1 j).IsHermitian := by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    have h := ae_blocks_isHermitian 2 W (Real.toNNReal ((1 - 2 * b) / W))
    have h' : ∀ᵐ ℓ ∂layerLaw W b .common, ∀ j, (ℓ.1 j).IsHermitian := by
      unfold layerLaw
      exact (Measure.quasiMeasurePreserving_fst).ae h
    exact (Measure.quasiMeasurePreserving_fst).ae h'
  have hX : ∀ᵐ x ∂μ, (pathSchur E x.2).IsHermitian :=
    (Measure.quasiMeasurePreserving_snd).ae (srec_ae_pathSchur_isHermitian W r b E)
  have hbound : ∀ᵐ x ∂μ, ‖rngPortObs b E x‖ ≤ f1 x + f2 x + f4 x := by
    filter_upwards [hA, hX, rng_ae_invertible (W := W) (r := r) hb1 E] with x hxA hxX hxI
    have hobs0 : 0 ≤ rngPortObs b E x := norm_nonneg _
    rw [Real.norm_of_nonneg hobs0]
    have hf1nn : 0 ≤ f1 x := norm_nonneg _
    have hf2nn : 0 ≤ f2 x := by
      simp only [hf2]; have := hd0 x.2; positivity
    by_cases hdx : d x.2 ≤ dstar
    · have hnot : x ∉ Prod.snd ⁻¹' S := by
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq, not_lt]; exact hdx
      simp only [hf4]
      rw [Set.indicator_of_notMem hnot, add_zero]
      have hmean := (hcon W hW (pathSchur E x.2) hxX E hE hdx).2
      have hm2 : ‖m x.2 - matchedA E‖ ≤ f2 x := by
        refine hmean.trans ?_
        simp only [hf2]
        have h1 : Cl * d x.2 ≤ Cl' * d x.2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (hd0 x.2)
        have h2 : Cl / (W : ℝ) ^ 2 ≤ Cl' / (W : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
        exact add_le_add h1 h2
      calc rngPortObs b E x = ‖rngG b E (pathSchur E x.2) x.1 - matchedA E‖ := rfl
        _ ≤ ‖rngG b E (pathSchur E x.2) x.1 - m x.2‖ + ‖m x.2 - matchedA E‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ f1 x + f2 x := add_le_add le_rfl hm2
    · have hmem : x ∈ Prod.snd ⁻¹' S := by
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq]; exact not_le.mp hdx
      simp only [hf4]
      rw [Set.indicator_of_mem hmem]
      have hcr := rng_norm_portTrace_le E hz0 hxX x.1 hxA hxI.2
      have ha := norm_matchedA hEabs
      have hcr' : rngPortObs b E x ≤ M0 := by
        calc rngPortObs b E x ≤ ‖portBlockTrace (layerResolvent .common E (commonZ b E)
              (pathSchur E x.2) x.1) 0‖ + ‖matchedA E‖ := norm_sub_le _ _
          _ ≤ (commonZ b E).im⁻¹ + 1 := add_le_add hcr ha.le
          _ ≤ M0 := by
              have := inv_anti₀ hη hzη
              linarith
      linarith
  -- the three norms
  have hf1e : eLpNorm f1 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (Cf' * Real.sqrt q / W) := by
    refine srec_eLpNorm_prod_le ((hgm.sub (hmm.comp measurable_snd)).norm) hq0 ?_
    filter_upwards [srec_ae_pathSchur_isHermitian W r b E] with π hπ
    have h := hfl W hW .common (pathSchur E π) hπ E (commonZ b E) hzη hz3
      (meqPortProj (W := W) (σ := .common) 0) (meq_norm_portProj_le (W := W) (σ := .common) 0)
      q hq2 hqε₃
    have hpt : ∀ ℓ, rngG b E (pathSchur E π) ℓ = (W : ℂ)⁻¹ *
        (meqPortProj (W := W) (σ := .common) 0 *
          layerResolvent .common E (commonZ b E) (pathSchur E π) ℓ).trace := fun ℓ =>
      lct_port_eq_trace (W := W) (σ := .common) _ 0
    have hmeas : Measurable (fun ℓ => rngG b E (pathSchur E π) ℓ - m π) :=
      (rng_measurable_G b E measurable_const measurable_id).sub measurable_const
    show eLpNorm (fun ℓ => ‖rngG b E (pathSchur E π) ℓ - m π‖) (ENNReal.ofReal q)
      (layerLaw W b .common) ≤ _
    rw [eLpNorm_norm _ hmeas.aestronglyMeasurable]
    have hmπ : m π = ∫ ℓ, (W : ℂ)⁻¹ * (meqPortProj (W := W) (σ := .common) 0 *
        layerResolvent .common E (commonZ b E) (pathSchur E π) ℓ).trace ∂layerLaw W b .common := by
      simp only [hm, hpt]
    simp only [hmπ, hpt]
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _)) hWr.le
  have hdq : eLpNorm d (ENNReal.ofReal q) (pathLaw W r b) ≤
      ENNReal.ofReal (Cp' * Real.sqrt q / W) := by
    refine (hpb W hW q hq2 hqεp r hr1 hrT E hE).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _)) hWr.le
  have hf2e : eLpNorm f2 (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Cl' * (Cp' * Real.sqrt q / W)) + ENNReal.ofReal (Cl' / (W : ℝ) ^ 2) := by
    refine (eLpNorm_add_le (f := fun x : LayerSample W .common × PathSample W r => Cl' * d x.2)
      (g := fun _ => Cl' / (W : ℝ) ^ 2) hq1).trans (add_le_add ?_ ?_)
    · have : (fun x : LayerSample W .common × PathSample W r => Cl' * d x.2) =
          Cl' • (d ∘ Prod.snd) := rfl
      rw [this, eLpNorm_const_smul, Real.enorm_of_nonneg hCl0,
        eLpNorm_comp_measurePreserving hdm.aestronglyMeasurable measurePreserving_snd,
        ENNReal.ofReal_mul hCl0]
      gcongr
    · rw [eLpNorm_const _ hq0' (IsProbabilityMeasure.ne_zero μ), measure_univ,
        ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg (by positivity)]
  have hf4e : eLpNorm f4 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (M0 * (Cp' * Real.sqrt q / W / dstar)) := by
    rw [hf4, eLpNorm_indicator_const (hSm.preimage measurable_snd).nullMeasurableSet hq0'
      ENNReal.ofReal_ne_top, measurePreserving_snd.measure_preimage hSm.nullMeasurableSet,
      ENNReal.toReal_ofReal hq0.le, Real.enorm_of_nonneg hM0]
    have hB0 : 0 ≤ Cp' * Real.sqrt q / W := by positivity
    have hmk := srec_markov hq0 hB0 hds hdq
    have hP : pathLaw W r b S ≤ ENNReal.ofReal ((Cp' * Real.sqrt q / W / dstar) ^ q) :=
      (measure_mono (s := S) (t := {π | dstar ≤ d π}) fun π hπ => by
        simp only [hSdef, Set.mem_ofPred_eq] at hπ ⊢; exact hπ.le).trans hmk
    calc ENNReal.ofReal M0 * pathLaw W r b S ^ (1 / q)
        ≤ ENNReal.ofReal M0 * ENNReal.ofReal ((Cp' * Real.sqrt q / W / dstar) ^ q) ^ (1 / q) := by
          gcongr
      _ = ENNReal.ofReal (M0 * (Cp' * Real.sqrt q / W / dstar)) := by
          have hy0 : 0 ≤ Cp' * Real.sqrt q / W / dstar := by positivity
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
            Real.rpow_rpow_inv hy0 hq0.ne', ← ENNReal.ofReal_mul hM0]
  -- assemble
  have hobsm : AEStronglyMeasurable (rngPortObs b E) μ :=
    (rng_measurable_portObs b E W r).aestronglyMeasurable
  calc eLpNorm (rngPortObs b E) (ENNReal.ofReal q) μ
      ≤ eLpNorm (fun x => f1 x + f2 x + f4 x) (ENNReal.ofReal q) μ :=
        eLpNorm_mono_ae_real hobsm hbound
    _ ≤ eLpNorm f1 (ENNReal.ofReal q) μ + eLpNorm f2 (ENNReal.ofReal q) μ +
          eLpNorm f4 (ENNReal.ofReal q) μ := by
        refine (eLpNorm_add_le (f := fun x => f1 x + f2 x) (g := f4) hq1).trans ?_
        exact add_le_add (eLpNorm_add_le (f := f1) (g := f2) hq1) le_rfl
    _ ≤ ENNReal.ofReal (Cf' * Real.sqrt q / W) +
          (ENNReal.ofReal (Cl' * (Cp' * Real.sqrt q / W)) + ENNReal.ofReal (Cl' / (W : ℝ) ^ 2)) +
          ENNReal.ofReal (M0 * (Cp' * Real.sqrt q / W / dstar)) :=
        add_le_add (add_le_add hf1e hf2e) hf4e
    _ ≤ ENNReal.ofReal ((Cf' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar)) * Real.sqrt q / W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hClW : Cl' / (W : ℝ) ^ 2 ≤ Cl' * x := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hxW2 hCl0
        have e1 : Cf' * Real.sqrt q / W = Cf' * x := by rw [hxdef]; ring
        have e2 : Cl' * (Cp' * Real.sqrt q / W) = Cl' * Cp' * x := by rw [hxdef]; ring
        have e3 : M0 * (Cp' * Real.sqrt q / W / dstar) = M0 * (Cp' / dstar) * x := by
          rw [hxdef]; ring
        have e4 : (Cf' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar)) * Real.sqrt q / W =
            (Cf' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar)) * x := by rw [hxdef]; ring
        rw [e1, e2, e3, e4]
        nlinarith

end BlockBand.Layers
