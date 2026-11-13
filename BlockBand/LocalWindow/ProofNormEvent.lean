module

public import BlockBand.LocalWindow.Statements
public import BlockBand.Angular.AssemblyRowTail
public import BlockBand.DeterminantScore.GUENormTailProof
public import BlockBand.DeterminantScore.PairRowMoment
public import BlockBand.Angular.FiberAngular

/-!
# The Gaussian norm event

With overwhelming probability all entries of the physical matrix are bounded by one and the fresh
`GUE` block is bounded in operator norm; this gives the norm bounds used in the physical
local-window lemma.

## Main results

* `coord_tail_le`: `P{u ≤ c z_j} ≤ exp(v_j c²/2 - u)` (exponential Markov) for a coordinate of
  the physical Gaussian coordinate law.
* `law_entry_tail_le`: under the physical law, `P{|H_xy| > 1} ≤ 4 e^{-W/8}` (all coordinate
  variances are `≤ 1/W`).
* `splitLaw_entryEvent_le`: on the split space, `P{∃ x y, |H_xy| > 1} ≤ 4 (nW)² e^{-W/8}`,
  `H = assemble ω G`, for every splitting law.
* `splitLaw_gueEvent_le`: constants `C_G, c_G > 0` with `P{‖G‖ > C_G} ≤ e^{-c_G 2W}`
  (`DeterminantScore.gueNormTail_holds`, `t · 2W = s < 1`).
* `normEvent_le`: both together, `P(entryEvent ∪ {‖G‖ > C_G}) ≤ 4 (nW)² e^{-W/8} + e^{-c_G 2W}`;
  `normBound_le_rpow`: this is `≤ C W^{-D}` uniformly in `n ≤ T_n W`, for every `D`.
* Deterministic consequences off the event: `toE_norm_le_of_entries` (`‖Av‖ ≤ √(|m||n|)‖v‖`
  for entries bounded by one) and `norm_bounds_of_not_mem`: `‖C‖, ‖C*‖ ≤ nW` and
  `‖V‖ ≤ nW + C_G` as Euclidean maps, the hypotheses `hC`, `hC'`, `hV` of
  the truncation bounds (`norm_truncF_le`) (`ω = (H_R, C, V)`, `V = H_SS - G`). Polynomial (not `≤ W`) bounds
  suffice there: the grid spacing `W^{-M}` absorbs any fixed power.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofNormEvent

open MeasureTheory ProbabilityTheory Matrix Finset
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-!
## Exponential Markov for one Gaussian coordinate
-/

/-- `P{u ≤ c z_j} ≤ exp(v_j c²/2 - u)` under the physical Gaussian coordinate law. -/
theorem coord_tail_le (p : Parameters) (j : p.GaussianCoordinate) (c u : ℝ) :
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) {z | u ≤ c * z j} ≤
      ENNReal.ofReal (Real.exp ((p.gaussianCoordinateVariance j : ℝ) * c ^ 2 / 2 - u)) := by
  set μ := (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))
  have hmp := measurePreserving_eval (fun i : p.GaussianCoordinate =>
    gaussianReal 0 (p.gaussianCoordinateVariance i)) j
  have hint : ∫⁻ z, ENNReal.ofReal (Real.exp (c * z j)) ∂μ =
      ENNReal.ofReal (Real.exp ((p.gaussianCoordinateVariance j : ℝ) * c ^ 2 / 2)) := by
    have h := hmp.lintegral_comp (f := fun t : ℝ => ENNReal.ofReal (Real.exp (c * t)))
      (by fun_prop)
    change ∫⁻ z, ENNReal.ofReal (Real.exp (c * z j))
      ∂Measure.pi (fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) = _
    rw [h]
    exact BlockBand.Angular.Assembly.RowTail.lintegral_exp_mul_gaussianReal _ c
  have hsub : {z : p.GaussianCoordinate → ℝ | u ≤ c * z j} ⊆
      {z | ENNReal.ofReal (Real.exp u) ≤ ENNReal.ofReal (Real.exp (c * z j))} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hz)
  have hM := mul_meas_ge_le_lintegral₀ (μ := μ)
    (f := fun z => ENNReal.ofReal (Real.exp (c * z j)))
    (measurable_const.mul (measurable_pi_apply j)).exp.ennreal_ofReal.aemeasurable
    (ENNReal.ofReal (Real.exp u))
  rw [hint] at hM
  have h1 : ENNReal.ofReal (Real.exp (-u)) * ENNReal.ofReal (Real.exp u) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc μ {z | u ≤ c * z j}
      ≤ μ {z | ENNReal.ofReal (Real.exp u) ≤ ENNReal.ofReal (Real.exp (c * z j))} :=
        measure_mono hsub
    _ = ENNReal.ofReal (Real.exp (-u)) * (ENNReal.ofReal (Real.exp u) *
          μ {z | ENNReal.ofReal (Real.exp u) ≤ ENNReal.ofReal (Real.exp (c * z j))}) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-u)) *
          ENNReal.ofReal (Real.exp ((p.gaussianCoordinateVariance j : ℝ) * c ^ 2 / 2)) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; ring

/-- Every physical coordinate variance is at most `1/W`. -/
theorem coordVariance_le (p : Parameters) (j : p.GaussianCoordinate) :
    (p.gaussianCoordinateVariance j : ℝ) ≤ 1 / p.W := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hev : ∀ x y : p.Site, p.entryVariance x y ≤ 1 / p.W := by
    intro x y
    have hb := p.b_pos; have hb' := p.b_lt_half
    unfold Parameters.entryVariance Parameters.c
    split_ifs
    · exact div_le_div_of_nonneg_right (by linarith) hW.le
    · exact div_le_div_of_nonneg_right (by linarith) hW.le
    · positivity
  rcases j with x | ⟨x, y, e⟩
  · exact hev x x
  · by_cases h : p.siteIndex x < p.siteIndex y
    · have e1 : (p.gaussianCoordinateVariance (.inr (x, y, e)) : ℝ) = p.entryVariance x y / 2 := by
        simp [Parameters.gaussianCoordinateVariance, h]; rfl
      rw [e1]
      have := hev x y
      have h0 := p.entryVariance_nonneg x y
      linarith
    · have e1 : (p.gaussianCoordinateVariance (.inr (x, y, e)) : ℝ) = 0 := by
        simp [Parameters.gaussianCoordinateVariance, h]
      rw [e1]
      positivity

/-- `P{1/2 ≤ ± z_j} ≤ e^{-W/8}`. -/
theorem coord_half_tail_le (p : Parameters) (j : p.GaussianCoordinate) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) {z | 1 / 2 ≤ σ * z j} ≤
      ENNReal.ofReal (Real.exp (-(p.W : ℝ) / 8)) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hsub : {z : p.GaussianCoordinate → ℝ | 1 / 2 ≤ σ * z j} ⊆
      {z | (p.W : ℝ) / 4 ≤ (σ * p.W / 2) * z j} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    have : (σ * p.W / 2) * z j = (p.W / 2) * (σ * z j) := by ring
    rw [this]; nlinarith
  refine (measure_mono hsub).trans ((coord_tail_le p j _ _).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hv := coordVariance_le p j
  have hv0 : (0 : ℝ) ≤ p.gaussianCoordinateVariance j := NNReal.coe_nonneg _
  have e : (σ * p.W / 2) ^ 2 = (p.W : ℝ) ^ 2 / 4 := by
    rw [div_pow, mul_pow, hσ]; ring
  rw [e]
  have : (p.gaussianCoordinateVariance j : ℝ) * p.W ≤ 1 := by
    rw [le_div_iff₀ hW] at hv; linarith
  nlinarith

/-- Two coordinates control a function: `P{1 < g} ≤ 4 e^{-W/8}` if `g z ≤ |z_a| + |z_b|`. -/
theorem coord_pair_tail_le (p : Parameters) (ja jb : p.GaussianCoordinate)
    (g : (p.GaussianCoordinate → ℝ) → ℝ) (hg : ∀ z, g z ≤ |z ja| + |z jb|) :
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) {z | 1 < g z} ≤
      ENNReal.ofReal (4 * Real.exp (-(p.W : ℝ) / 8)) := by
  set μ := (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ))
  have hsub : {z | 1 < g z} ⊆
      (({z | 1 / 2 ≤ (1 : ℝ) * z ja} ∪ {z | 1 / 2 ≤ (-1 : ℝ) * z ja}) ∪
        {z | 1 / 2 ≤ (1 : ℝ) * z jb}) ∪ {z | 1 / 2 ≤ (-1 : ℝ) * z jb} := by
    intro z hz
    have h := hz.trans_le (hg z)
    simp only [Set.mem_union, Set.mem_ofPred_eq, one_mul, neg_one_mul]
    rcases le_or_gt (1 / 2) |z ja| with ha | ha
    · rcases le_abs'.mp ha with h1 | h1
      · left; left; right; linarith
      · left; left; left; exact h1
    · have hb : 1 / 2 ≤ |z jb| := by linarith
      rcases le_abs'.mp hb with h1 | h1
      · right; linarith
      · left; right; exact h1
  have e := fun j σ hσ => coord_half_tail_le p j σ hσ
  calc μ {z | 1 < g z}
      ≤ μ {z | 1 / 2 ≤ (1 : ℝ) * z ja} + μ {z | 1 / 2 ≤ (-1 : ℝ) * z ja} +
          μ {z | 1 / 2 ≤ (1 : ℝ) * z jb} + μ {z | 1 / 2 ≤ (-1 : ℝ) * z jb} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add_left
          ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)) _))
    _ ≤ ENNReal.ofReal (Real.exp (-(p.W : ℝ) / 8)) + ENNReal.ofReal (Real.exp (-(p.W : ℝ) / 8)) +
          ENNReal.ofReal (Real.exp (-(p.W : ℝ) / 8)) +
          ENNReal.ofReal (Real.exp (-(p.W : ℝ) / 8)) := by
        gcongr
        · exact e ja 1 (by norm_num)
        · exact e ja (-1) (by norm_num)
        · exact e jb 1 (by norm_num)
        · exact e jb (-1) (by norm_num)
    _ = ENNReal.ofReal (4 * Real.exp (-(p.W : ℝ) / 8)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **Entry tail of the physical law**: `P{|H_xy| > 1} ≤ 4 e^{-W/8}`. -/
theorem law_entry_tail_le {p : Parameters} (model : p.GaussianRingModel) (x y : p.Site) :
    (model.law : Measure p.SiteMatrix) {H | 1 < ‖H x y‖} ≤
      ENNReal.ofReal (4 * Real.exp (-(p.W : ℝ) / 8)) := by
  have hS : MeasurableSet {H : p.SiteMatrix | 1 < ‖H x y‖} :=
    measurableSet_lt measurable_const
      ((measurable_pi_apply y).comp (measurable_pi_apply x)).norm
  rw [model.law_eq_gaussianMatrixLaw]
  change Measure.map p.gaussianReconstruction
    (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) _ ≤ _
  rw [Measure.map_apply p.measurable_gaussianReconstruction hS]
  obtain ⟨ja, jb, hg⟩ : ∃ ja jb : p.GaussianCoordinate, ∀ z : p.GaussianCoordinate → ℝ,
      ‖p.gaussianReconstruction z x y‖ ≤ |z ja| + |z jb| := by
    by_cases hxy : x = y
    · subst hxy
      refine ⟨.inl x, .inl x, fun z => ?_⟩
      simp only [Parameters.gaussianReconstruction, ite_true, Complex.norm_real,
        Real.norm_eq_abs]
      linarith [abs_nonneg (z (.inl x))]
    by_cases hlt : p.siteIndex x < p.siteIndex y
    · refine ⟨.inr (x, y, false), .inr (x, y, true), fun z => ?_⟩
      simp only [Parameters.gaussianReconstruction, hxy, hlt, ite_false, ite_true]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    · refine ⟨.inr (y, x, false), .inr (y, x, true), fun z => ?_⟩
      simp only [Parameters.gaussianReconstruction, hxy, hlt, ite_false]
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
  exact coord_pair_tail_le p ja jb _ hg

/-!
## The norm event on the split space
-/

section Split

variable {p : Parameters} {i : ZMod p.n}

/-- The entry event `{∃ x y, |H_xy| > 1}`, `H = assemble ω G`. -/
def entryEvent (p : Parameters) (i : ZMod p.n) : Set (SplitState p i × PairMatrix p i) :=
  {x | ∃ a b : p.Site, 1 < ‖assemble p i x.1 x.2 a b‖}

/-- `P(entryEvent) ≤ 4 (nW)² e^{-W/8}` for every splitting law. -/
theorem splitLaw_entryEvent_le {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (hsplit : IsPairSplitting p i model (splitS p) Pω) :
    splitLaw p i Pω (entryEvent p i) ≤
      ENNReal.ofReal (4 * ((p.n : ℝ) * p.W) ^ 2 * Real.exp (-(p.W : ℝ) / 8)) := by
  have hf := BlockBand.Angular.PairCoareaBridge.measurable_assemble p i
  have hmap : (splitLaw p i Pω).map (fun x => assemble p i x.1 x.2) =
      (model.law : Measure p.SiteMatrix) := hsplit
  have hsub : entryEvent p i ⊆ ⋃ ab ∈ (univ : Finset (p.Site × p.Site)),
      (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹'
        {H | 1 < ‖H ab.1 ab.2‖} := by
    rintro x ⟨a, b, h⟩
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq, mem_univ, exists_true_left]
    exact ⟨(a, b), h⟩
  calc splitLaw p i Pω (entryEvent p i)
      ≤ ∑ ab ∈ (univ : Finset (p.Site × p.Site)), splitLaw p i Pω
          ((fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹'
            {H | 1 < ‖H ab.1 ab.2‖}) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _ab ∈ (univ : Finset (p.Site × p.Site)),
          ENNReal.ofReal (4 * Real.exp (-(p.W : ℝ) / 8)) := by
        gcongr with ab
        refine (Measure.le_map_apply hf.aemeasurable _).trans ?_
        rw [hmap]
        exact law_entry_tail_le model ab.1 ab.2
    _ = ENNReal.ofReal (4 * ((p.n : ℝ) * p.W) ^ 2 * Real.exp (-(p.W : ℝ) / 8)) := by
        rw [sum_const, card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Fintype.card_prod, physicalSite_card]
        simp only [Parameters.N]
        push_cast; ring

/-- The fresh-noise event `{‖G‖ > C_G}` (operator norm). -/
def gueEvent (p : Parameters) (i : ZMod p.n) (CG : ℝ) : Set (SplitState p i × PairMatrix p i) :=
  {x | CG < ‖x.2‖}

/-- **`GUE` norm tail on the split space** (`DeterminantScore.gueNormTail_holds`): constants
`C_G, c_G > 0` first; for every splitting law, `P{‖G‖ > C_G} ≤ e^{-c_G · 2W}`
(`t · 2W = s < 1`). -/
theorem splitLaw_gueEvent_le :
    ∃ CG cG : ℝ, 0 < CG ∧ 0 < cG ∧ ∀ (p : Parameters) (model : p.GaussianRingModel)
      (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model (splitS p) Pω →
        splitLaw p i Pω (gueEvent p i CG) ≤
          ENNReal.ofReal (Real.exp (-(cG * (2 * (p.W : ℝ))))) := by
  obtain ⟨C, c, hC, hc, h⟩ := BlockBand.DeterminantScore.GUENormTail.gueNormTail_holds
  refine ⟨C, c, hC, hc, fun p model i Pω hsplit => ?_⟩
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    exact_mod_cast BlockBand.Angular.FiberAngular.card_pairSite p i
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hs1 : splitS p ≤ 1 := by
    have := min_le_right p.c p.b
    unfold splitS; linarith [p.b_lt_half]
  have ht : ((pairTime p (splitS p) : ℝ≥0) : ℝ) * (Fintype.card (PairSite p i) : ℝ) ≤ 1 := by
    rw [hcard, pairTime, Real.coe_toNNReal _ (by positivity)]
    rw [div_mul_cancel₀ _ (by positivity)]
    exact hs1
  have hsub : gueEvent p i C ⊆ Set.univ ×ˢ
      {G : PairMatrix p i | C * Real.sqrt ((pairTime p (splitS p) : ℝ) *
        (Fintype.card (PairSite p i) : ℝ)) < ‖G‖} := by
    intro x hx
    refine ⟨Set.mem_univ _, ?_⟩
    have : Real.sqrt ((pairTime p (splitS p) : ℝ) * (Fintype.card (PairSite p i) : ℝ)) ≤ 1 :=
      Real.sqrt_le_one.mpr ht
    show _ < ‖x.2‖
    have hx' : C < ‖x.2‖ := hx
    nlinarith
  have hprob := BlockBand.DeterminantScore.ScoreMoments.PairRow.splitLaw_univ hsplit
  have : IsProbabilityMeasure (gueMeasure (PairSite p i) (pairTime p (splitS p))) := by
    unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
    infer_instance
  refine (measure_mono hsub).trans ?_
  unfold splitLaw
  rw [Measure.prod_prod, hprob, one_mul]
  refine (h (PairSite p i) (pairTime p (splitS p))).trans (le_of_eq ?_)
  rw [hcard]

/-!
## Deterministic norm bounds
-/

/-- `‖Av‖ ≤ ‖A‖ ‖v‖` (Euclidean map against the `L²` operator norm). -/
theorem toE_le_opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (v : EuclideanSpace ℂ n) : ‖T A v‖ ≤ ‖A‖ * ‖v‖ := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap (T A)) v

/-- Entries bounded by one: `‖Av‖ ≤ √(|m| |n|) ‖v‖`. -/
theorem toE_norm_le_of_entries {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hA : ∀ r c, ‖A r c‖ ≤ 1) (v : EuclideanSpace ℂ n) :
    ‖T A v‖ ≤ Real.sqrt ((Fintype.card m : ℝ) * Fintype.card n) * ‖v‖ := by
  refine (toE_le_opNorm A v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (BlockBand.Angular.Assembly.RowTail.l2_opNorm_le_frob A).trans (Real.sqrt_le_sqrt ?_)
  calc ∑ r, ∑ c, ‖A r c‖ ^ 2 ≤ ∑ _r : m, ∑ _c : n, (1 : ℝ) := by
        gcongr with r _ c _
        exact pow_le_one₀ (norm_nonneg _) (hA r c)
    _ = _ := by simp

/-- `√(|m| |n|) ≤ nW` for index types of physical sites. -/
theorem sqrt_card_le {p : Parameters} {m n : Type} [Fintype m] [Fintype n]
    (hm : Fintype.card m ≤ Fintype.card p.Site) (hn : Fintype.card n ≤ Fintype.card p.Site) :
    Real.sqrt ((Fintype.card m : ℝ) * Fintype.card n) ≤ (p.n : ℝ) * p.W := by
  have hS : (Fintype.card p.Site : ℝ) = (p.n : ℝ) * p.W := by
    rw [physicalSite_card]; simp [Parameters.N]
  rw [Real.sqrt_le_left (by positivity)]
  rw [← hS]
  have hm' : (Fintype.card m : ℝ) ≤ Fintype.card p.Site := by exact_mod_cast hm
  have hn' : (Fintype.card n : ℝ) ≤ Fintype.card p.Site := by exact_mod_cast hn
  calc (Fintype.card m : ℝ) * Fintype.card n ≤ Fintype.card p.Site * Fintype.card p.Site :=
        mul_le_mul hm' hn' (by positivity) (by positivity)
    _ = _ := by ring

/-- **Off the norm event**: `‖C‖, ‖C*‖ ≤ nW` and `‖V‖ ≤ nW + C_G` as Euclidean maps, where
`ω = (H_R, C, V)` (the hypotheses of the truncation bounds). -/
theorem norm_bounds_of_not_mem {p : Parameters} {i : ZMod p.n} {CG : ℝ}
    {x : SplitState p i × PairMatrix p i} (hx : x ∉ entryEvent p i)
    (hG : x ∉ gueEvent p i CG) :
    (∀ v, ‖T x.1.2.1 v‖ ≤ ((p.n : ℝ) * p.W) * ‖v‖) ∧
      (∀ w, ‖T x.1.2.1ᴴ w‖ ≤ ((p.n : ℝ) * p.W) * ‖w‖) ∧
      (∀ v, ‖T x.1.2.2 v‖ ≤ ((p.n : ℝ) * p.W + CG) * ‖v‖) := by
  have hent : ∀ a b : p.Site, ‖assemble p i x.1 x.2 a b‖ ≤ 1 := by
    intro a b; by_contra h; exact hx ⟨a, b, lt_of_not_ge h⟩
  have hext : Fintype.card (ExteriorSite p i) ≤ Fintype.card p.Site := Fintype.card_subtype_le _
  have hpair : Fintype.card (PairSite p i) ≤ Fintype.card p.Site := Fintype.card_subtype_le _
  have hC : ∀ r c, ‖x.1.2.1 r c‖ ≤ 1 := by
    intro r c
    have := hent r.1 c.1
    simpa [assemble, r.2, c.2] using this
  refine ⟨fun v => ?_, fun w => ?_, fun v => ?_⟩
  · exact (toE_norm_le_of_entries _ hC v).trans
      (mul_le_mul_of_nonneg_right (sqrt_card_le hext hpair) (norm_nonneg _))
  · refine (toE_norm_le_of_entries _ (fun r c => ?_) w).trans
      (mul_le_mul_of_nonneg_right (sqrt_card_le hpair hext) (norm_nonneg _))
    rw [conjTranspose_apply, norm_star]; exact hC c r
  · have hVG : ∀ r c, ‖(x.1.2.2 + x.2) r c‖ ≤ 1 := by
      intro r c
      have := hent r.1 c.1
      simpa [assemble, r.2, c.2] using this
    have hGn : ‖x.2‖ ≤ CG := by by_contra h; exact hG (lt_of_not_ge h)
    have e : x.1.2.2 = (x.1.2.2 + x.2) - x.2 := by abel
    rw [e, map_sub, LinearMap.sub_apply]
    calc ‖T (x.1.2.2 + x.2) v - T x.2 v‖ ≤ ‖T (x.1.2.2 + x.2) v‖ + ‖T x.2 v‖ := norm_sub_le _ _
      _ ≤ ((p.n : ℝ) * p.W) * ‖v‖ + CG * ‖v‖ := by
          refine add_le_add ((toE_norm_le_of_entries _ hVG v).trans
            (mul_le_mul_of_nonneg_right (sqrt_card_le hpair hpair) (norm_nonneg _))) ?_
          exact (toE_le_opNorm _ v).trans (mul_le_mul_of_nonneg_right hGn (norm_nonneg _))
      _ = _ := by ring

/-- **The Gaussian norm event**: constants `C_G, c_G > 0` first; for every splitting law,
`P(entryEvent ∪ {‖G‖ > C_G}) ≤ 4 (nW)² e^{-W/8} + e^{-c_G · 2W}`, and off this event
`‖C‖, ‖C*‖ ≤ nW`, `‖V‖ ≤ nW + C_G` (`norm_bounds_of_not_mem`). -/
theorem normEvent_le :
    ∃ CG cG : ℝ, 0 < CG ∧ 0 < cG ∧ ∀ (p : Parameters) (model : p.GaussianRingModel)
      (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model (splitS p) Pω →
        splitLaw p i Pω (entryEvent p i ∪ gueEvent p i CG) ≤
          ENNReal.ofReal (4 * ((p.n : ℝ) * p.W) ^ 2 * Real.exp (-(p.W : ℝ) / 8) +
            Real.exp (-(cG * (2 * (p.W : ℝ))))) := by
  obtain ⟨CG, cG, hCG, hcG, h⟩ := splitLaw_gueEvent_le
  refine ⟨CG, cG, hCG, hcG, fun p model i Pω hsplit => ?_⟩
  refine (measure_union_le _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (splitLaw_entryEvent_le hsplit) (h p model i Pω hsplit)

end Split

/-!
## Superpolynomial smallness
-/

/-- `x^k e^{-ax} ≤ k!/a^k` for `x ≥ 0`, `a > 0`. -/
theorem pow_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(a * x)) ≤ k.factorial / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (x := a * x) (mul_nonneg ha.le hx) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hak : 0 < a ^ k := pow_pos ha k
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ hak]
  have e : x ^ k * Real.exp (-(a * x)) * a ^ k = (a ^ k * x ^ k) * Real.exp (-(a * x)) := by ring
  rw [e]
  calc (a ^ k * x ^ k) * Real.exp (-(a * x)) ≤ (Real.exp (a * x) * k.factorial) *
        Real.exp (-(a * x)) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = k.factorial := by
        rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
          mul_one]

/-- The norm-event bound is `O(W^{-D})` uniformly in `n ≤ T_n W`, for every `D`. -/
theorem normBound_le_rpow (Tn D cG : ℝ) (hcG : 0 < cG) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Parameters, (p.n : ℝ) ≤ Tn * p.W →
      4 * ((p.n : ℝ) * p.W) ^ 2 * Real.exp (-(p.W : ℝ) / 8) +
          Real.exp (-(cG * (2 * (p.W : ℝ)))) ≤ C * (p.W : ℝ) ^ (-D) := by
  set m := ⌈D⌉₊
  refine ⟨4 * Tn ^ 2 * ((m + 4).factorial / (1 / 8 : ℝ) ^ (m + 4)) +
    m.factorial / (2 * cG) ^ m, by positivity, fun p hn => ?_⟩
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < p.W := by linarith
  have hWD : (p.W : ℝ) ^ D ≤ (p.W : ℝ) ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hW1 (Nat.le_ceil D)
  have hWDpos : 0 < (p.W : ℝ) ^ D := Real.rpow_pos_of_pos hW0 D
  rw [Real.rpow_neg hW0.le, ← div_eq_mul_inv, le_div_iff₀ hWDpos]
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hnW : ((p.n : ℝ) * p.W) ^ 2 ≤ Tn ^ 2 * (p.W : ℝ) ^ 4 := by
    have : (p.n : ℝ) * p.W ≤ Tn * p.W * p.W := mul_le_mul_of_nonneg_right hn hW0.le
    calc ((p.n : ℝ) * p.W) ^ 2 ≤ (Tn * p.W * p.W) ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
      _ = Tn ^ 2 * (p.W : ℝ) ^ 4 := by ring
  have h1 := pow_mul_exp_neg_le (a := 1 / 8) (by norm_num) (m + 4) hW0.le
  have h2 := pow_mul_exp_neg_le (a := 2 * cG) (by positivity) m hW0.le
  have e1 : -(p.W : ℝ) / 8 = -(1 / 8 * (p.W : ℝ)) := by ring
  have e2 : -(cG * (2 * (p.W : ℝ))) = -(2 * cG * (p.W : ℝ)) := by ring
  rw [e1, e2]
  have hE1 := (Real.exp_pos (-(1 / 8 * (p.W : ℝ)))).le
  have hE2 := (Real.exp_pos (-(2 * cG * (p.W : ℝ)))).le
  calc (4 * ((p.n : ℝ) * p.W) ^ 2 * Real.exp (-(1 / 8 * (p.W : ℝ))) +
        Real.exp (-(2 * cG * (p.W : ℝ)))) * (p.W : ℝ) ^ D
      ≤ (4 * (Tn ^ 2 * (p.W : ℝ) ^ 4) * Real.exp (-(1 / 8 * (p.W : ℝ))) +
          Real.exp (-(2 * cG * (p.W : ℝ)))) * (p.W : ℝ) ^ m := by
        apply mul_le_mul _ hWD hWDpos.le (by positivity)
        gcongr
    _ = 4 * Tn ^ 2 * ((p.W : ℝ) ^ (m + 4) * Real.exp (-(1 / 8 * (p.W : ℝ)))) +
          (p.W : ℝ) ^ m * Real.exp (-(2 * cG * (p.W : ℝ))) := by ring
    _ ≤ _ := by
        gcongr

end BlockBand.LocalWindow.ProofNormEvent
