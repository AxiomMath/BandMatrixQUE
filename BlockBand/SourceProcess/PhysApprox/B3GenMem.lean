module

public import BlockBand.SourceProcess.PhysApprox.B3GenDoob
public import BlockBand.SourceProcess.PhysApprox.B3MomTight
public import BlockBand.SourceProcess.PhysApprox.B3Bridge
public import BlockBand.SourceProcess.ClosedSumProof.ClosedStep

/-!
# The integrability and mean estimates of the Doob split

Targets: the two estimates `GenStepMemL2` and `GenStepMeanL2` (stated in a sibling module) of the
Doob split of the `𝒦` brackets. Law `closedLaw b W np`, filtration `b3Sigma W j np`, alive set
`A_j = b3Alive … R W j`, increment `dX_c = b3dX … j … c`, steps `j ∈ genNoBirthSteps s T τ W`,
eventually in `W`, for every `R`.

**`GenStepMemL2`** (`MemLp (1_{A_j} dX_c) 2`). Proved:
* measurability through `b3Alive_ae_eq` and `measurable_b3ClosedGramAt`/`measurable_b3ClosedKAt`;
* **`genKStepMemL2_of_stopped`**: the `𝒦` half from the per-length stopped fourth moment
  `ComplexKStoppedMoment` (hence from its maximal form). `1_{A_j}𝒦_{j+1}` has a finite fourth
  moment; `1_{A_j}𝒦_j` is `0` at `j = n_s` (`b3ClosedKAt_start`) and is dominated by
  `1_{A_{j-1}}𝒦_j` otherwise;
* **`genGramStepMemL2_of_next`**: the Gram half from `GenGramNextL2`, square integrability of
  `1_{A_j} G_{j+1}`. The alive set bounds `G_j` (`norm_gramEntry_b3ClosedGramAt_le`) but **not**
  `G_{j+1}`: `A_j` stops the trace only up to length `j`, so the trace bound alone does not give
  the Gram half;
* **`genGramStepMemL2_of_lindeberg`**, `genKStepMemL2_of_lindeberg`, `genStepMemL2_of_lindeberg`:
  the halves from the Lindeberg clauses (eventually finite fourth moments);
* **`genStepMemL2_of`**: `ComplexGramLindeberg + ComplexKStoppedMomentMax ⇒ GenStepMemL2`.
* `genStepMemL2_of_next`: `GenGramNextL2 + ComplexKStoppedMomentMax ⇒ GenStepMemL2`.

**`GenStepMeanL2`** (`∫‖E_j[1_{A_j} dX_c]‖² ≤ C/W²`), reduced to two hypotheses:
* `genStepMeanL2_of_parts`: Gram half `GenGramMeanL2` and `𝒦` half `GenKMeanL2`;
* **`genGramMeanL2_of_driftL2`**: the Gram half from the per-step `L²` drift error
  `GenGramDriftL2` (`∫‖E_j[1_{A_j} dG_e] − 1_{A_j}W⁻¹ drift_e(G_j)‖² ≤ C/W²`); the drift itself is
  bounded on `A_j` by the trace (`ClosedSumProof.norm_gramDriftEntry_le_rho`);
* **`genKMeanL2_of_form`**: the `𝒦` half from the mean size `GenKMeanForm`
  (`|E_j[1_{A_j} d𝒦]| ≤ C(δ₀ + W⁻²)`, `‖δ₀‖_{L²}² ≤ C/W²`, the factor `Tr M_pr < R` absorbed in
  `C`).
* `complexClosedSummed_of_mem`: `ComplexClosedSummed` from these estimates and those of
  `complexClosedSummed_of_cov`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## Generic facts
-/

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem genMem_sq_le_one_add_pow_four (x : ℝ≥0∞) : x ^ 2 ≤ 1 + x ^ 4 := by
  rcases le_total x 1 with hx | hx
  · exact (pow_le_one₀ zero_le hx).trans le_self_add
  · exact (pow_le_pow_right₀ hx (by norm_num)).trans le_add_self

theorem genMem_add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2) := by
  have h := gen_mul_le_sq_add_sq x y
  calc (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by ring
    _ ≤ x ^ 2 + y ^ 2 + 2 * (x ^ 2 + y ^ 2) := by gcongr
    _ = 3 * (x ^ 2 + y ^ 2) := by ring

omit [MeasurableSpace α] in
theorem genMem_enorm_indicator_pow (A : Set α) (f : α → ℂ) {n : ℕ} (hn : n ≠ 0) (y : α) :
    ‖A.indicator f y‖ₑ ^ n = A.indicator (fun y => ‖f y‖ₑ ^ n) y := by
  by_cases hy : y ∈ A
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy, hn]

/-- A finite fourth moment gives `L²` on a finite measure. -/
theorem genMem_memLp_two_of_four [IsFiniteMeasure μ] {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (h4 : ∫⁻ y, ‖f y‖ₑ ^ 4 ∂μ ≠ ∞) : MemLp f 2 μ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hf]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2, ENNReal.rpow_two]
  calc ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≤ ∫⁻ y, (1 + ‖f y‖ₑ ^ 4) ∂μ :=
        lintegral_mono fun y => genMem_sq_le_one_add_pow_four _
    _ = μ Set.univ + ∫⁻ y, ‖f y‖ₑ ^ 4 ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, h4.lt_top⟩

/-- `∫‖a‖² ≤ 3∫‖a - g‖² + 3k²` when `‖g‖ ≤ k` (probability measure). -/
theorem genMem_lintegral_sq_le_of_sub [IsProbabilityMeasure μ] (a g : α → ℂ) {k : ℝ≥0∞}
    (hg : ∀ y, ‖g y‖ₑ ≤ k) :
    ∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ ≤ 3 * ∫⁻ y, ‖a y - g y‖ₑ ^ 2 ∂μ + 3 * k ^ 2 := by
  calc ∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ ≤ ∫⁻ y, (3 * ‖a y - g y‖ₑ ^ 2 + 3 * k ^ 2) ∂μ := by
        refine lintegral_mono fun y => ?_
        have h1 : ‖a y‖ₑ ≤ ‖a y - g y‖ₑ + k := by
          calc ‖a y‖ₑ = ‖(a y - g y) + g y‖ₑ := by rw [sub_add_cancel]
            _ ≤ ‖a y - g y‖ₑ + ‖g y‖ₑ := enorm_add_le _ _
            _ ≤ ‖a y - g y‖ₑ + k := by gcongr; exact hg y
        calc ‖a y‖ₑ ^ 2 ≤ (‖a y - g y‖ₑ + k) ^ 2 := pow_le_pow_left₀ zero_le h1 2
          _ ≤ 3 * (‖a y - g y‖ₑ ^ 2 + k ^ 2) := genMem_add_sq_le _ _
          _ = 3 * ‖a y - g y‖ₑ ^ 2 + 3 * k ^ 2 := by ring
    _ = 3 * ∫⁻ y, ‖a y - g y‖ₑ ^ 2 ∂μ + 3 * k ^ 2 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const, measure_univ, mul_one]

/-- `∫‖a‖² ≤ 3c²(∫δ² + w²)` when `‖a‖ ≤ c(δ + w)` a.e. (probability measure). -/
theorem genMem_lintegral_sq_le_of_dom [IsProbabilityMeasure μ] (a : α → ℂ) (δ : α → ℝ≥0∞)
    {c w : ℝ≥0∞} (hc : c ≠ ∞) (h : ∀ᵐ y ∂μ, ‖a y‖ₑ ≤ c * (δ y + w)) :
    ∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ ≤ 3 * c ^ 2 * (∫⁻ y, δ y ^ 2 ∂μ + w ^ 2) := by
  have hc2 : 3 * c ^ 2 ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hc)
  calc ∫⁻ y, ‖a y‖ₑ ^ 2 ∂μ ≤ ∫⁻ y, (3 * c ^ 2 * δ y ^ 2 + 3 * c ^ 2 * w ^ 2) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [h] with y hy
        calc ‖a y‖ₑ ^ 2 ≤ (c * (δ y + w)) ^ 2 := pow_le_pow_left₀ zero_le hy 2
          _ = c ^ 2 * (δ y + w) ^ 2 := mul_pow _ _ _
          _ ≤ c ^ 2 * (3 * (δ y ^ 2 + w ^ 2)) := by gcongr; exact genMem_add_sq_le _ _
          _ = 3 * c ^ 2 * δ y ^ 2 + 3 * c ^ 2 * w ^ 2 := by ring
    _ = 3 * c ^ 2 * (∫⁻ y, δ y ^ 2 ∂μ + w ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ hc2,
          lintegral_const, measure_univ, mul_one, mul_add]

end Generic

/-!
## Measurability and the alive sets
-/

theorem genMem_measurable_b3X (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (c : CIdx K np) : Measurable (b3X b E s h τ m W j Vs c) := by
  rcases c with e | ij
  · exact (ClosedSumProof.measurable_gramEntry e).comp
      (measurable_b3ClosedGramAt b E s h τ m W j hV)
  · exact (measurable_b3ClosedKAt b E s h τ m W j).eval_matrix

theorem genMem_measurable_b3dX (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (c : CIdx K np) : Measurable (b3dX b E s h τ m W j Vs c) :=
  (genMem_measurable_b3X b E s h τ m W (j + 1) hV c).sub
    (genMem_measurable_b3X b E s h τ m W j hV c)

/-- `1_{A_j} f` is a.e. strongly measurable for measurable `f` (`b3Alive_ae_eq`). -/
theorem genMem_aesm_indicator {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    {f : ProbedPath W np × ℝ → ℂ} (hf : Measurable f) :
    AEStronglyMeasurable ((b3Alive b E s h τ m R W j Vs).indicator f) (closedLaw b W np) :=
  (hf.indicator (measurableSet_b3AliveM b E s h τ m R W j hV)).aestronglyMeasurable.congr
    (indicator_ae_eq_of_ae_eq_set (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs)).symm

/-- `1_{A_j} f ∈ L²` from a finite stopped fourth moment. -/
theorem genMem_memLp_indicator_of_four {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    {f : ProbedPath W np × ℝ → ℂ} (hf : Measurable f)
    (h4 : ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator (fun y => ‖f y‖ₑ ^ 4) y
      ∂closedLaw b W np ≠ ∞) :
    MemLp ((b3Alive b E s h τ m R W j Vs).indicator f) 2 (closedLaw b W np) := by
  refine genMem_memLp_two_of_four (genMem_aesm_indicator hb hE1 hE2 s h τ m R W j hV hf) ?_
  rwa [lintegral_congr fun y => genMem_enorm_indicator_pow _ f (by norm_num : 4 ≠ 0) y]

theorem genMem_b3Alive_succ_subset (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ)
    (W i : ℕ) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    b3Alive b E s h τ m R W (i + 1) Vs ⊆ b3Alive b E s h τ m R W i Vs :=
  fun _ hy => ⟨hy.1, fun l h1 h2 => hy.2 l h1 (by omega)⟩

theorem genMem_indicator_dX_eq {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W j : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (A : Set (ProbedPath W np × ℝ))
    (c : CIdx K np) :
    A.indicator (b3dX b E s h τ m W j Vs c) =
      A.indicator (b3X b E s h τ m W (j + 1) Vs c) - A.indicator (b3X b E s h τ m W j Vs c) :=
  Set.indicator_sub _ _ _

/-!
## `GenStepMemL2`: the two halves
-/

/-- Gram half of `GenStepMemL2`. -/
def GenGramStepMemL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
        MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3dX b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np))) 2 (closedLaw b W np)

/-- `𝒦` half of `GenStepMemL2`. -/
def GenKStepMemL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator
        (b3dX b E s h τ m W j (Vs W) (Sum.inr ij : CIdx K np))) 2 (closedLaw b W np)

theorem genStepMemL2_of_parts (hG : GenGramStepMemL2) (hK : GenKStepMemL2) : GenStepMemL2 := by
  intro b E np τ m T s h K Vs hF R
  filter_upwards [hG b E np τ m T s h K Vs hF R, hK b E np τ m T s h K Vs hF R]
    with W hGW hKW j hj c
  rcases c with e | ij
  · exact hGW j hj e
  · exact hKW j hj ij

/-- **The `𝒦` half from the per-length stopped fourth moment** (`ComplexKStoppedMoment`). -/
theorem genKStepMemL2_of_stopped (hK : ComplexKStoppedMoment) : GenKStepMemL2 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hD, -, hτ, -, -, hVs⟩ := id hF
  obtain ⟨C, hC⟩ := hK b E np τ m T s h K Vs hF R
  have hb1 : b < 1 := by linarith [hD.2.1]
  filter_upwards [hC, hVs] with W hCW hVW j hj ij
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1
  have hX : ∀ i, Measurable (b3X b E s h τ m W i (Vs W) (Sum.inr ij : CIdx K np)) :=
    fun i => genMem_measurable_b3X b E s h τ m W i hmV _
  have hnext : MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator
      (b3X b E s h τ m W (j + 1) (Vs W) (Sum.inr ij : CIdx K np))) 2 (closedLaw b W np) :=
    genMem_memLp_indicator_of_four hb1 hD.2.2.1 hD.2.2.2.1 s h τ m R W j hmV (hX _)
      ((hCW j hj1 hj2 ij).trans_lt ENNReal.ofReal_lt_top).ne
  have hcur : MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator
      (b3X b E s h τ m W j (Vs W) (Sum.inr ij : CIdx K np))) 2 (closedLaw b W np) := by
    rcases Nat.eq_or_lt_of_le hj1 with heq | hlt
    · subst heq
      have h0 : b3X b E s h τ m W (closeLen s W) (Vs W) (Sum.inr ij : CIdx K np) = 0 := by
        funext y
        simp [b3X, cEntry, b3ClosedKAt_start hτ]
      rw [h0, Set.indicator_zero']
      exact MemLp.zero
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi1 : closeLen s W ≤ i := by omega
      have hi2 : i < ⌊(W : ℝ) * T⌋₊ := by omega
      refine genMem_memLp_indicator_of_four hb1 hD.2.2.1 hD.2.2.2.1 s h τ m R W (i + 1) hmV
        (hX _) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          ((lintegral_mono fun y => ?_).trans (hCW i hi1 hi2 ij)))
      exact Set.indicator_le_indicator_of_subset
        (genMem_b3Alive_succ_subset b E s h τ m R W i (Vs W)) (fun _ => zero_le) y
  rw [genMem_indicator_dX_eq]
  exact hnext.sub hcur

/-- **`GenGramNextL2`**: one-step square integrability of the closed Gram coordinates on
the alive set, `1_{A_j} G_{e,j+1} ∈ L²`. The alive set `A_j` stops the trace only up to `j`. -/
def GenGramNextL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
        MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3X b E s h τ m W (j + 1) (Vs W) (Sum.inl e : CIdx K np))) 2 (closedLaw b W np)

/-- **The Gram half from `GenGramNextL2`**: `1_{A_j} G_{e,j}` is bounded by `R` (the trace). -/
theorem genGramStepMemL2_of_next (hN : GenGramNextL2) : GenGramStepMemL2 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hD, -, -, -, -, hVs⟩ := id hF
  have hb1 : b < 1 := by linarith [hD.2.1]
  filter_upwards [hN b E np τ m T s h K Vs hF R, hVs] with W hNW hVW j hj e
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hj1 := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hcur : MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator
      (b3X b E s h τ m W j (Vs W) (Sum.inl e : CIdx K np))) 2 (closedLaw b W np) := by
    refine MemLp.of_bound (genMem_aesm_indicator hb1 hD.2.2.1 hD.2.2.2.1 s h τ m R W j hmV
      (genMem_measurable_b3X b E s h τ m W j hmV _)) (max R 0) (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ b3Alive b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy]
      exact ((norm_gramEntry_b3ClosedGramAt_le b E s h τ m W j (Vs W) y e).trans
        (hy.2 j hj1 le_rfl).le).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hy, norm_zero]
      exact le_max_right _ _
  rw [genMem_indicator_dX_eq]
  exact (hNW j hj e).sub hcur

/-- From the Lindeberg limit of one coordinate: eventually `1_{A_j} dX_c ∈ L²` at every step. -/
theorem genMem_eventually_memLp_of_lindeberg {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ}
    {K : ℕ} {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ) (c : CIdx K np)
    (hT : Tendsto (fun W => b3LindebergErr b E s T h τ m R W (Vs W) c) atTop (𝓝 0)) :
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      MemLp ((b3Alive b E s h τ m R W j (Vs W)).indicator (b3dX b E s h τ m W j (Vs W) c)) 2
        (closedLaw b W np) := by
  obtain ⟨hD, -, -, -, -, hVs⟩ := id hF
  have hb1 : b < 1 := by linarith [hD.2.1]
  filter_upwards [hT.eventually (gt_mem_nhds zero_lt_one), hVs] with W hTW hVW j hj
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  refine genMem_memLp_indicator_of_four hb1 hD.2.2.1 hD.2.2.2.1 s h τ m R W j hmV
    (genMem_measurable_b3dX b E s h τ m W j hmV c)
    (ne_top_of_lt (lt_of_le_of_lt ?_ (hTW.trans ENNReal.one_lt_top)))
  exact Finset.single_le_sum (f := fun j => ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3dX b E s h τ m W j (Vs W) c y‖ₑ ^ 4) y ∂closedLaw b W np)
    (fun _ _ => zero_le) hj

theorem genGramStepMemL2_of_lindeberg (hL : ComplexGramLindeberg) : GenGramStepMemL2 := by
  intro b E np τ m T s h K Vs hF R
  filter_upwards [Filter.eventually_all.2 fun e => genMem_eventually_memLp_of_lindeberg hF R
    (Sum.inl e) (hL b E np τ m T s h K Vs hF R e)] with W hW j hj e
  exact hW e j hj

theorem genKStepMemL2_of_lindeberg (hL : ComplexKLindeberg) : GenKStepMemL2 := by
  intro b E np τ m T s h K Vs hF R
  filter_upwards [Filter.eventually_all.2 fun ij => genMem_eventually_memLp_of_lindeberg hF R
    (Sum.inr ij) (hL b E np τ m T s h K Vs hF R ij)] with W hW j hj ij
  exact hW ij j hj

/-- **`GenStepMemL2` from the Lindeberg clause** (both halves). -/
theorem genStepMemL2_of_lindeberg (hL : ComplexClosedLindeberg) : GenStepMemL2 := by
  intro b E np τ m T s h K Vs hF R
  filter_upwards [Filter.eventually_all.2 fun c => genMem_eventually_memLp_of_lindeberg hF R
    c (hL b E np τ m T s h K Vs hF R c)] with W hW j hj c
  exact hW c j hj

/-- **`GenStepMemL2` from the Gram Lindeberg estimate and the maximal stopped fourth moment.** -/
theorem genStepMemL2_of (hG : ComplexGramLindeberg) (hK : ComplexKStoppedMomentMax) :
    GenStepMemL2 :=
  genStepMemL2_of_parts (genGramStepMemL2_of_lindeberg hG)
    (genKStepMemL2_of_stopped (complexKStoppedMoment_of_max hK))

/-- **`GenStepMemL2` from `GenGramNextL2` and the maximal stopped fourth moment.** -/
theorem genStepMemL2_of_next (hN : GenGramNextL2) (hK : ComplexKStoppedMomentMax) :
    GenStepMemL2 :=
  genStepMemL2_of_parts (genGramStepMemL2_of_next hN)
    (genKStepMemL2_of_stopped (complexKStoppedMoment_of_max hK))

/-!
## `GenStepMeanL2`: the two halves
-/

/-- Gram half of `GenStepMeanL2`. -/
def GenGramMeanL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
        genMeanSq b E s h τ m R W j (Vs W) (Sum.inl e : CIdx K np) ≤
          ENNReal.ofReal (C / (W : ℝ) ^ 2)

/-- `𝒦` half of `GenStepMeanL2`. -/
def GenKMeanL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      genMeanSq b E s h τ m R W j (Vs W) (Sum.inr ij : CIdx K np) ≤
        ENNReal.ofReal (C / (W : ℝ) ^ 2)

theorem genStepMeanL2_of_parts (hG : GenGramMeanL2) (hK : GenKMeanL2) : GenStepMeanL2 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, hC₁, hev₁⟩ := hG b E np τ m T s h K Vs hF R
  obtain ⟨C₂, hC₂, hev₂⟩ := hK b E np τ m T s h K Vs hF R
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, ?_⟩
  filter_upwards [hev₁, hev₂] with W h₁ h₂ j hj c
  have hmono : ∀ C : ℝ, C ≤ max C₁ C₂ →
      ENNReal.ofReal (C / (W : ℝ) ^ 2) ≤ ENNReal.ofReal (max C₁ C₂ / (W : ℝ) ^ 2) :=
    fun C hC => ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC (sq_nonneg _))
  rcases c with e | ij
  · exact (h₁ j hj e).trans (hmono _ (le_max_left _ _))
  · exact (h₂ j hj ij).trans (hmono _ (le_max_right _ _))

/-- The per-step `L²` drift error of `c` at step `j`:
`∫‖E_j[1_{A_j} dX_c] − 1_{A_j} W⁻¹ cDrift(G_j)‖²`. -/
def genDriftSqStep (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∫⁻ y, ‖(closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator
      (b3dX b E s h τ m W j Vs c) | b3Sigma W j np] y -
    (b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      (W : ℂ)⁻¹ * cDrift b E c (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ^ 2
    ∂closedLaw b W np

/-- **`GenGramDriftL2`: the Gram one-step drift error in `L²`**:
`∫‖E_j[1_{A_j} dG_e] − 1_{A_j} W⁻¹ drift_e(G_j)‖² ≤ C/W²`. -/
def GenGramDriftL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
        genDriftSqStep b E s h τ m R W j (Vs W) (Sum.inl e : CIdx K np) ≤
          ENNReal.ofReal (C / (W : ℝ) ^ 2)

/-- The Gram drift on the alive set: `‖drift_e(G_j)‖ ≤ |D₀|(l1 𝖣 ρ)²ρ`, `ρ = |c|² max R 0`. -/
theorem genMem_norm_cDrift_le (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (hj : closeLen s W ≤ j)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) {y : ProbedPath W np × ℝ}
    (hy : y ∈ b3Alive b E s h τ m R W j Vs) :
    ‖cDrift b E (Sum.inl e : CIdx K np) (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤
      |transportD0 b E| * (ClosedSumProof.l1 (srcSignature K (Fin np)) *
        ((Fintype.card (SrcCol K (Fin np)) : ℝ) ^ 2 * max R 0)) ^ 2 *
        ((Fintype.card (SrcCol K (Fin np)) : ℝ) ^ 2 * max R 0) := by
  set G := b3ClosedGramAt b E s h τ m W j Vs y
  have htr : (G.1.trace).re ≤ max R 0 := (hy.2 j hj le_rfl).le.trans (le_max_left _ _)
  have h1 : ∀ a c, ‖G.1 a c‖ ≤ max R 0 := fun a c => by
    have := norm_gramEntry_b3ClosedGramAt_le b E s h τ m W j Vs y (0, a, c)
    simp only [gramEntry, ite_true] at this
    exact this.trans htr
  have h2 : ∀ a c, ‖G.2 a c‖ ≤ max R 0 := fun a c => by
    have := norm_gramEntry_b3ClosedGramAt_le b E s h τ m W j Vs y (1, a, c)
    simp only [gramEntry, one_ne_zero, ite_false] at this
    exact this.trans htr
  exact ClosedSumProof.norm_gramDriftEntry_le_rho _ _ e G (ClosedSumProof.l1_le_of_entry h1)
    (ClosedSumProof.l1_le_of_entry h2)

/-- **The Gram mean from the `L²` drift error** and the trace bound on the drift. -/
theorem genGramMeanL2_of_driftL2 (hL : GenGramDriftL2) : GenGramMeanL2 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, hC, hev⟩ := hL b E np τ m T s h K Vs hF R
  set ρ : ℝ := (Fintype.card (SrcCol K (Fin np)) : ℝ) ^ 2 * max R 0 with hρ
  set D : ℝ := |transportD0 b E| * (ClosedSumProof.l1 (srcSignature K (Fin np)) * ρ) ^ 2 * ρ
    with hDdef
  have hρ0 : 0 ≤ ρ := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) hρ0
  refine ⟨3 * C + 3 * D ^ 2, by positivity, ?_⟩
  filter_upwards [hev] with W hW j hj e
  have hj1 := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hg : ∀ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
      (W : ℂ)⁻¹ * cDrift b E (Sum.inl e : CIdx K np)
        (b3ClosedGramAt b E s h τ m W j (Vs W) y)) y‖ₑ ≤ ENNReal.ofReal (D / W) := by
    intro y
    by_cases hy : y ∈ b3Alive b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (genMem_norm_cDrift_le b E s h τ m R W j (Vs W) hj1 e hy)
        (inv_nonneg.2 (Nat.cast_nonneg W))
    · rw [Set.indicator_of_notMem hy, enorm_zero]
      exact zero_le
  refine (genMem_lintegral_sq_le_of_sub _ _ hg).trans ?_
  calc 3 * genDriftSqStep b E s h τ m R W j (Vs W) (Sum.inl e : CIdx K np) +
        3 * ENNReal.ofReal (D / W) ^ 2 ≤
        3 * ENNReal.ofReal (C / (W : ℝ) ^ 2) + 3 * ENNReal.ofReal (D / W) ^ 2 := by
        gcongr
        exact hW j hj e
    _ = ENNReal.ofReal ((3 * C + 3 * D ^ 2) / (W : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_pow (div_nonneg hD (Nat.cast_nonneg W)),
          ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [div_pow]
        ring

/-- **`GenKMeanForm`: the mean size of the closed `𝒦` step**: on the alive set the conditional
mean is at most `C(δ₀ + W⁻²) Tr M_pr`, with `‖δ₀‖²_{L²} ≤ C/W²`; `Tr M_pr < R` is absorbed in `C`.
Stated a.e. on the whole space: off the alive set the conditional mean of `1_{A_j} d𝒦` vanishes
once `A_j` is a `b3Sigma W j`-event. -/
def GenKMeanForm : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W, ∀ ij : Fin np × Fin np,
      ∃ δ : ProbedPath W np × ℝ → ℝ≥0∞,
        ∫⁻ y, δ y ^ 2 ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ 2) ∧
        ∀ᵐ y ∂closedLaw b W np,
          ‖(closedLaw b W np)[(b3Alive b E s h τ m R W j (Vs W)).indicator
              (b3dX b E s h τ m W j (Vs W) (Sum.inr ij : CIdx K np)) | b3Sigma W j np] y‖ₑ ≤
            ENNReal.ofReal C * (δ y + ENNReal.ofReal (1 / (W : ℝ) ^ 2))

/-- **The `𝒦` mean in `L²` from its paper shape.** -/
theorem genKMeanL2_of_form (hT : GenKMeanForm) : GenKMeanL2 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C, hC, hev⟩ := hT b E np τ m T s h K Vs hF R
  refine ⟨3 * C ^ 2 * (C + 1), by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1 j hj ij
  obtain ⟨δ, hδ, hdom⟩ := hW j hj ij
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hw0 : (0 : ℝ) ≤ 1 / (W : ℝ) ^ 2 := by positivity
  have hw1 : 1 / (W : ℝ) ^ 2 ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ hW1')
  refine (genMem_lintegral_sq_le_of_dom _ δ ENNReal.ofReal_ne_top hdom).trans ?_
  calc 3 * ENNReal.ofReal C ^ 2 *
        (∫⁻ y, δ y ^ 2 ∂closedLaw b W np + ENNReal.ofReal (1 / (W : ℝ) ^ 2) ^ 2) ≤
        3 * ENNReal.ofReal C ^ 2 *
          (ENNReal.ofReal (C / (W : ℝ) ^ 2) + ENNReal.ofReal (1 / (W : ℝ) ^ 2)) := by
        have hw : ENNReal.ofReal (1 / (W : ℝ) ^ 2) ^ 2 ≤ ENNReal.ofReal (1 / (W : ℝ) ^ 2) := by
          rw [← ENNReal.ofReal_pow hw0]
          exact ENNReal.ofReal_le_ofReal (pow_le_of_le_one hw0 hw1 two_ne_zero)
        gcongr
    _ = ENNReal.ofReal (3 * C ^ 2 * (C / (W : ℝ) ^ 2 + 1 / (W : ℝ) ^ 2)) := by
        rw [ENNReal.ofReal_mul (p := 3 * C ^ 2) (by positivity),
          ENNReal.ofReal_mul (p := 3) (by norm_num), ENNReal.ofReal_pow hC,
          ENNReal.ofReal_add (div_nonneg hC (sq_nonneg (W : ℝ))) hw0, ENNReal.ofReal_ofNat]
    _ = ENNReal.ofReal (3 * C ^ 2 * (C + 1) / (W : ℝ) ^ 2) := by
        congr 1
        ring

/-- **`GenStepMeanL2` from the Gram `L²` drift error and the paper's `𝒦` mean.** -/
theorem genStepMeanL2_of (hG : GenGramDriftL2) (hK : GenKMeanForm) : GenStepMeanL2 :=
  genStepMeanL2_of_parts (genGramMeanL2_of_driftL2 hG) (genKMeanL2_of_form hK)

/-- **`ComplexClosedSummed` from the finest estimates**: `complexClosedSummed_of_cov` with
`GenStepMemL2` from the Gram Lindeberg estimate and the maximal stopped fourth moment, and
`GenStepMeanL2` from `GenGramDriftL2` and `GenKMeanForm`. -/
theorem complexClosedSummed_of_mem (hGD : GenReqGramDrift) (hGB : GenReqGramBracket)
    (hB : GenReqBirth) (hKD : KStepDrift) (hGL : ComplexGramLindeberg)
    (hKM : ComplexKStoppedMomentMax) (hDL : GenGramDriftL2) (hKT : GenKMeanForm)
    (hKB : KStepCov) (hKC : KStepConjCov) : ComplexClosedSummed :=
  complexClosedSummed_of_cov hGD hGB hB hKD (genStepMemL2_of hGL hKM) (genStepMeanL2_of hDL hKT)
    hKB hKC

end BlockBand.SourceProcess.PhysApprox.B3
