module

public import BlockBand.Critical.RelativeVectors.StochasticStatements
public import BlockBand.Palm.RelativeLocalizationAdapter
public import BlockBand.Palm.RelativeLocalizationLabels
public import BlockBand.Palm.MomentFlow.BridgeBrownian
public import BlockBand.Critical.WeightedDensity.Spectral

/-!
# Path events of the matrix flow: countable reduction and almost sure simplicity

*Measure:* `flowLaw N a = GUE_N(a/N) ⊗ commonWienerLaw`.
*Domain:* every `N` (`N > 0` for the a.s. statements), Hermitian `F`, `0 < a ≤ c`.

* `pathDense a c`: the countable set `(ℚ ∩ [a, c]) ∪ {a, c}`, dense in `[a, c]`.
* `continuous_flowEigenvalue_herm`: `σ ↦ λ_k(H_σ)` is continuous (Weyl + continuity of the
  Brownian path) whenever `ω.1` is Hermitian.
* `simplePathSet`, `longGapPathSet`: path events written over `pathDense` only, hence
  `pathSigma F a a c`-measurable (`measurableSet_simplePathSet`,
  `measurableSet_longGapPathSet`), and equal to their `[a, c]`-versions on Hermitian samples
  (`mem_simplePathSet_iff`, `mem_longGapPathSet_iff`).
* `ae_hasSimpleSpectrum_flowInit`: `flowInit F = F + G_a` has a.s. simple spectrum for
  `a > 0` (`ae_simpleSpectrum_add_gue` and `map_flowMatrix_sub`).
* `ae_simple_path`, `flowLaw_compl_simplePathSet`: under `DysonBrownianMotion` (a hypothesis),
  a.s. the spectrum is simple along the whole closed window `[a, c]`.
* `comap_hermProj_pathSigma_le_eigen`, `measurable_comp_hermProj_eigen`,
  `measurableSet_preimage_hermProj`: `pathSigma F a a c` pulled back by `hermProj` lies in the
  whole-path σ-algebra `eigenPathSigma (flowInit F) (flowBM N) 0` of the angular martingale.
* `flowMatrix_hermProj`, `flowEigenvalue_hermProj`: `H_{a+x}(hermProj ω) = F' + G_x`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
  BlockBand.Palm.MomentFlow
open scoped NNReal

variable {N : ℕ}

/-!
## 1. A countable dense set of times
-/

/-- `(ℚ ∩ [a, c]) ∪ {a, c}`. -/
def pathDense (a c : ℝ) : Set ℝ :=
  {σ | σ ∈ Icc a c ∧ (σ ∈ Set.range ((↑) : ℚ → ℝ) ∨ σ = a ∨ σ = c)}

theorem pathDense_countable (a c : ℝ) : (pathDense a c).Countable := by
  refine ((Set.countable_range ((↑) : ℚ → ℝ)).union ((Set.countable_singleton a).union
    (Set.countable_singleton c))).mono ?_
  rintro _ ⟨_, h | h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem pathDense_subset (a c : ℝ) : pathDense a c ⊆ Icc a c := fun _ h => h.1

theorem left_mem_pathDense {a c : ℝ} (hac : a ≤ c) : a ∈ pathDense a c :=
  ⟨⟨le_rfl, hac⟩, Or.inr (Or.inl rfl)⟩

theorem Icc_subset_closure_pathDense {a c : ℝ} (hac : a ≤ c) :
    Icc a c ⊆ closure (pathDense a c) := by
  rcases hac.eq_or_lt with h | h
  · subst h
    intro σ hσ
    have : σ = a := le_antisymm hσ.2 hσ.1
    subst this
    exact subset_closure (left_mem_pathDense le_rfl)
  · rw [← closure_Ioo h.ne]
    refine closure_minimal ?_ isClosed_closure
    refine (Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo).trans
      (closure_mono ?_)
    rintro σ ⟨hσ, hq⟩
    exact ⟨Ioo_subset_Icc_self hσ, Or.inl hq⟩

/-- A closed lower bound on `pathDense` extends to `[a, c]`. -/
theorem forall_Icc_of_pathDense {a c : ℝ} (hac : a ≤ c) {g : ℝ → ℝ} (hg : Continuous g) {b : ℝ}
    (h : ∀ σ ∈ pathDense a c, b ≤ g σ) : ∀ σ ∈ Icc a c, b ≤ g σ := fun _ hσ =>
  closure_minimal h (isClosed_le continuous_const hg) (Icc_subset_closure_pathDense hac hσ)

/-!
## 2. Continuity of the eigenvalue paths
-/

/-- Euclidean operator norm (local copy, to keep imports minimal). -/
def psOpNorm (M : Matrix (Fin N) (Fin N) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖

theorem ps_l2Norm_eq_norm (x : Fin N → ℂ) :
    l2Norm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem ps_l2Norm_mulVec_le (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    l2Norm (M *ᵥ x) ≤ psOpNorm M * l2Norm x := by
  rw [ps_l2Norm_eq_norm, ps_l2Norm_eq_norm, ← Matrix.toEuclideanCLM_toLp]
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ) M).le_opNorm _

theorem continuous_psOpNorm : Continuous (psOpNorm (N := N)) := by
  unfold psOpNorm
  have : Continuous (fun M : Matrix (Fin N) (Fin N) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) M) :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun M => Matrix.toEuclideanCLM (𝕜 := ℂ) M
         map_add' := fun A B => map_add _ A B
         map_smul' := fun c A => map_smul _ c A } :
        Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)))
  exact continuous_norm.comp this

/-- Eigenvalues of a continuous Hermitian matrix path are continuous (Weyl). -/
theorem continuous_freshEigenvalue_comp {M : ℝ → Matrix (Fin N) (Fin N) ℂ} (hM : Continuous M)
    (hH : ∀ σ, (M σ).IsHermitian) (k : Fin N) :
    Continuous fun σ => freshEigenvalue (M σ) k := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hg : Tendsto (fun σ => psOpNorm (M σ - M σ₀)) (𝓝 σ₀) (𝓝 0) := by
    have h := (continuous_psOpNorm.comp (hM.sub (continuous_const (y := M σ₀)))).tendsto σ₀
    simpa [Function.comp_def, psOpNorm] using h
  refine squeeze_zero (fun _ => dist_nonneg) (fun σ => ?_) hg
  rw [Real.dist_eq]
  exact BlockBand.Palm.RelativeLocalization.abs_freshEigenvalue_sub_le (hH σ) (hH σ₀)
    (fun x => ps_l2Norm_mulVec_le _ x) k

theorem ps_flowMatrix_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) : (flowMatrix F a ω σ).IsHermitian :=
  (hF.add hω).add (hermitianBrownian_isHermitian _ _)

theorem continuous_flowEigenvalue_herm {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (k : Fin N) :
    Continuous fun σ => flowEigenvalue F a ω σ k :=
  continuous_freshEigenvalue_comp (continuous_flowMatrix F a ω) (ps_flowMatrix_isHermitian hF a hω) k

theorem monotone_flowEigenvalue {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) : Monotone (flowEigenvalue F a ω σ) :=
  BlockBand.Palm.RelativeLocalization.freshEigenvalue_monotone (ps_flowMatrix_isHermitian hF a hω σ)

/-!
## 3–4. Path events over the countable set
-/

theorem measurableSet_gap_le (F : Matrix (Fin N) (Fin N) ℂ) {a c σ : ℝ} (hσ : σ ∈ Icc a c)
    (i j : Fin N) (b : ℝ) :
    MeasurableSet[pathSigma F a a c]
      {ω : FlowSample N | b ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|} := by
  have hf : Measurable[pathSigma F a a c]
      (fun ω : FlowSample N => flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j) :=
    (measurable_flowEigenvalue_pathSigma F a a c hσ i).sub
      (measurable_flowEigenvalue_pathSigma F a a c hσ j)
  have hs : MeasurableSet {x : ℝ | b ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  exact hf hs

/-- Uniformly separated spectrum along the countable set `pathDense a c`. -/
def simplePathSet (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) : Set (FlowSample N) :=
  {ω | ∃ n : ℕ, ∀ σ ∈ pathDense a c, ∀ i j : Fin N, i ≠ j →
    1 / ((n : ℝ) + 1) ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|}

theorem measurableSet_simplePathSet (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) :
    MeasurableSet[pathSigma F a a c] (simplePathSet F a c) := by
  have he : simplePathSet F a c = ⋃ n : ℕ, ⋂ σ ∈ pathDense a c, ⋂ i : Fin N, ⋂ j : Fin N,
      ⋂ (_ : i ≠ j), {ω : FlowSample N |
        1 / ((n : ℝ) + 1) ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|} := by
    ext ω
    simp only [simplePathSet, mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [he]
  exact MeasurableSet.iUnion fun n => MeasurableSet.biInter (pathDense_countable a c)
    fun σ hσ => MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_gap_le F (pathDense_subset a c hσ) i j _

theorem mem_simplePathSet_iff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a ≤ c) {ω : FlowSample N} (hω : ω.1.IsHermitian) :
    ω ∈ simplePathSet F a c ↔ ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ) := by
  have hcont : ∀ i j : Fin N,
      Continuous fun σ => |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| :=
    fun i j => ((continuous_flowEigenvalue_herm hF a hω i).sub
      (continuous_flowEigenvalue_herm hF a hω j)).abs
  constructor
  · rintro ⟨n, hn⟩ σ hσ
    refine (monotone_flowEigenvalue hF a hω σ).strictMono_of_injective fun i j hij => ?_
    by_contra hne
    have h := forall_Icc_of_pathDense hac (hcont i j) (fun σ' hσ' => hn σ' hσ' i j hne) σ hσ
    rw [hij, sub_self, abs_zero] at h
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h
    have hpair : ∀ p : Fin N × Fin N, ∀ᶠ n : ℕ in atTop, p.1 ≠ p.2 → ∀ σ ∈ Icc a c,
        1 / ((n : ℝ) + 1) ≤ |flowEigenvalue F a ω σ p.1 - flowEigenvalue F a ω σ p.2| := by
      rintro ⟨i, j⟩
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h' => absurd hij h'
      obtain ⟨σ₀, hσ₀, hmin⟩ :=
        isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hac) (hcont i j).continuousOn
      have hpos : 0 < |flowEigenvalue F a ω σ₀ i - flowEigenvalue F a ω σ₀ j| :=
        abs_pos.2 (sub_ne_zero.2 ((h σ₀ hσ₀).injective.ne hij))
      obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hpos
      filter_upwards [eventually_ge_atTop n₀] with n hn _ σ hσ
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      have h2 := isMinOn_iff.mp hmin σ hσ
      linarith
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 hpair).exists
    exact ⟨n, fun σ hσ i j hij => hn (i, j) hij σ (pathDense_subset a c hσ)⟩

/-- Long-range gaps `|λ_i - λ_j| ≥ c₁ |i - j| / N` for `|i - j| ≥ ℓ`, along `pathDense a c`. -/
def longGapPathSet (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (ℓ : ℕ) (c₁ : ℝ) :
    Set (FlowSample N) :=
  {ω | ∀ σ ∈ pathDense a c, ∀ i j : Fin N, ℓ ≤ labelDist i j →
    c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|}

theorem measurableSet_longGapPathSet (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (ℓ : ℕ)
    (c₁ : ℝ) : MeasurableSet[pathSigma F a a c] (longGapPathSet F a c ℓ c₁) := by
  have he : longGapPathSet F a c ℓ c₁ = ⋂ σ ∈ pathDense a c, ⋂ i : Fin N, ⋂ j : Fin N,
      ⋂ (_ : ℓ ≤ labelDist i j), {ω : FlowSample N |
        c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|} := by
    ext ω
    simp only [longGapPathSet, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact MeasurableSet.biInter (pathDense_countable a c)
    fun σ hσ => MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_gap_le F (pathDense_subset a c hσ) i j _

theorem mem_longGapPathSet_iff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a ≤ c) {ℓ : ℕ} {c₁ : ℝ} {ω : FlowSample N} (hω : ω.1.IsHermitian) :
    ω ∈ longGapPathSet F a c ℓ c₁ ↔ ∀ σ ∈ Icc a c, ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| := by
  constructor
  · intro h σ hσ i j hij
    exact forall_Icc_of_pathDense hac (((continuous_flowEigenvalue_herm hF a hω i).sub
      (continuous_flowEigenvalue_herm hF a hω j)).abs) (fun σ' hσ' => h σ' hσ' i j hij) σ hσ
  · intro h σ hσ i j hij
    exact h σ (pathDense_subset a c hσ) i j hij

/-!
## 5–6. Almost sure simple spectrum
-/

theorem ae_simpleSpectrum_flowMatrix_start {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a : ℝ} (ha : 0 < a) (hN : 0 < N) :
    ∀ᵐ ω ∂flowLaw N a, BlockBand.Critical.WeightedDensity.SimpleSpectrum (flowMatrix F a ω a) := by
  have ht : 0 < Real.toNNReal (a / N) := Real.toNNReal_pos.2 (div_pos ha (Nat.cast_pos.2 hN))
  have h := BlockBand.Critical.WeightedDensity.ae_simpleSpectrum_add_gue hF ht
  rw [← map_flowMatrix_sub F ha.le le_rfl] at h
  have hm : Measurable (fun ω : FlowSample N => flowMatrix F a ω a - F) :=
    measurable_matrix_sub.comp ((measurable_flowMatrix F a a).prodMk measurable_const)
  have h' := ae_of_ae_map hm.aemeasurable h
  filter_upwards [h'] with ω hω
  simpa using hω

theorem flowInit_eq_flowMatrix_start (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) {ω : FlowSample N}
    (hp : hermProj ω = ω) : BlockBand.Palm.MomentFlow.flowInit F ω = flowMatrix F a ω a := by
  have := flowInit_add_flowBM F a ω 0
  rw [hp] at this
  simpa [flowBM] using this

theorem ae_hasSimpleSpectrum_flowInit (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    {a : ℝ} (ha : 0 < a) (hN : 0 < N) :
    ∀ᵐ ω ∂flowLaw N a, HasSimpleSpectrum N (BlockBand.Palm.MomentFlow.flowInit F ω) := by
  filter_upwards [ae_simpleSpectrum_flowMatrix_start hF ha hN, hermProj_ae_eq (N := N) a]
    with ω hω hp
  rw [flowInit_eq_flowMatrix_start F a hp, hasSimpleSpectrum_iff_strictMono hω.1]
  exact (BlockBand.Palm.RelativeLocalization.freshEigenvalue_monotone hω.1).strictMono_of_injective
    hω.2

theorem ae_simple_path (hDBM : DysonBrownianMotion N) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) (hN : 0 < N) (c : ℝ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ) := by
  filter_upwards [ae_simpleSpectrum_flowMatrix_start hF ha hN,
    BlockBand.Palm.RelativeLocalization.flow_simpleSpectrum hDBM hF a,
    BlockBand.Palm.RelativeLocalization.ae_fst_isHermitian (N := N) a] with ω h0 hpos hω σ hσ
  rcases hσ.1.eq_or_lt with h | h
  · subst h
    exact (BlockBand.Palm.RelativeLocalization.freshEigenvalue_monotone h0.1).strictMono_of_injective
      h0.2
  · exact (hasSimpleSpectrum_iff_strictMono (ps_flowMatrix_isHermitian hF a hω σ)).1 (hpos σ h)

theorem flowLaw_compl_simplePathSet (hDBM : DysonBrownianMotion N)
    (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hN : 0 < N)
    (hac : a ≤ c) : flowLaw N a (simplePathSet F a c)ᶜ = 0 := by
  have h : ∀ᵐ ω ∂flowLaw N a, ω ∈ simplePathSet F a c := by
    filter_upwards [ae_simple_path hDBM F hF ha hN c,
      BlockBand.Palm.RelativeLocalization.ae_fst_isHermitian (N := N) a] with ω h hω
    exact (mem_simplePathSet_iff hF hac hω).2 h
  exact ae_iff.1 h

/-!
## 7–8. `hermProj` and the whole-path σ-algebra
-/

theorem flowMatrix_hermProj (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (x : ℝ≥0) :
    flowMatrix F a (hermProj ω) (a + x) =
      BlockBand.Palm.MomentFlow.flowInit F ω + BlockBand.Palm.MomentFlow.flowBM N x ω :=
  (flowInit_add_flowBM F a ω x).symm

theorem flowEigenvalue_hermProj (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (x : ℝ≥0) :
    flowEigenvalue F a (hermProj ω) (a + x) = fun i =>
      freshEigenvalue (BlockBand.Palm.MomentFlow.flowInit F ω +
        BlockBand.Palm.MomentFlow.flowBM N x ω) i := by
  funext i
  rw [flowEigenvalue, flowMatrix_hermProj]

theorem comap_hermProj_pathSigma_le_eigen (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) :
    MeasurableSpace.comap BlockBand.Palm.MomentFlow.hermProj (pathSigma F a a c) ≤
      eigenPathSigma (BlockBand.Palm.MomentFlow.flowInit F)
        (BlockBand.Palm.MomentFlow.flowBM N) 0 := by
  rw [MeasurableSpace.comap_le_iff_le_map]
  refine iSup₂_le fun σ hσ => iSup_le fun k => ?_
  rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
  set x : ℝ≥0 := Real.toNNReal (σ - a) with hxdef
  have hx : a + (x : ℝ) = σ := by
    rw [hxdef, Real.coe_toNNReal _ (sub_nonneg.2 hσ.1)]; ring
  set V : FlowSample N → Fin N → ℝ := fun ω => fun i =>
    freshEigenvalue (BlockBand.Palm.MomentFlow.flowInit F ω +
      BlockBand.Palm.MomentFlow.flowBM N (0 + x) ω) i with hV
  have hfun : (fun ω => flowEigenvalue F a ω σ k) ∘ hermProj = (fun v : Fin N → ℝ => v k) ∘ V := by
    funext ω
    simp only [Function.comp_apply, hV, zero_add]
    rw [← hx, flowEigenvalue_hermProj]
  rw [hfun, ← MeasurableSpace.comap_comp]
  refine le_trans (MeasurableSpace.comap_mono (measurable_pi_apply k).comap_le) ?_
  exact le_iSup (fun v : ℝ≥0 => MeasurableSpace.comap (fun ω : FlowSample N => fun i =>
    freshEigenvalue (BlockBand.Palm.MomentFlow.flowInit F ω +
      BlockBand.Palm.MomentFlow.flowBM N (0 + v) ω) i) inferInstance) x

theorem measurable_hermProj_eigenPathSigma (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) :
    @Measurable _ _ (eigenPathSigma (BlockBand.Palm.MomentFlow.flowInit F)
      (BlockBand.Palm.MomentFlow.flowBM N) 0) (pathSigma F a a c)
      BlockBand.Palm.MomentFlow.hermProj :=
  measurable_iff_comap_le.2 (comap_hermProj_pathSigma_le_eigen F a c)

theorem measurable_comp_hermProj_eigen {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ} {β : Type*}
    [MeasurableSpace β] {f : FlowSample N → β} (hf : Measurable[pathSigma F a a c] f) :
    Measurable[eigenPathSigma (BlockBand.Palm.MomentFlow.flowInit F)
      (BlockBand.Palm.MomentFlow.flowBM N) 0] (f ∘ BlockBand.Palm.MomentFlow.hermProj) :=
  hf.comp (measurable_hermProj_eigenPathSigma F a c)

theorem measurableSet_preimage_hermProj {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ}
    {s : Set (FlowSample N)} (hs : MeasurableSet[pathSigma F a a c] s) :
    MeasurableSet[eigenPathSigma (BlockBand.Palm.MomentFlow.flowInit F)
      (BlockBand.Palm.MomentFlow.flowBM N) 0] (BlockBand.Palm.MomentFlow.hermProj ⁻¹' s) :=
  measurable_hermProj_eigenPathSigma F a c hs

end BlockBand.Critical.RelativeVectors
