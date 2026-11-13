module

public import BlockBand.Layers.RingTraces

/-!
# The residual-pair clause of the matched-traces theorem: reduction to two named statements

Step 5 of the proof of the matched-traces theorem: "For a removed adjacent pair, we subtract an
independent `GUE_{2W}(s/(2W))` from the pair. The last residual Gaussian layer then has diagonal
variance `(c−s/2)/W` and internal-bond variance `(b−s/2)/W`. Its test matrix is `(V−E−X−sa)⁻¹`
... the stability gap ... is at least `s/(1−b)`."

Geometry. For the pair `S = {i, i+1}`, the exterior `R` is the path of the `n-2` blocks
`i+2, …, i+n-1 = i-1`; its two port bonds couple path block `0` (`i+2`) to the pair block
`i+1` and path block `n-3` (`i-1`) to the pair block `i`. Pair index `0 ↔ i+1`, `1 ↔ i`.

* `rpLaw W b s`: the residual pair layer (`A_j ~ GUE_W((c-s/2)/W)`, bond `Gin((b-s/2)/W)`),
  `rpMatrix`, `rpResolvent = (V - E - X - sa)⁻¹`, `rpObs = max_j |W⁻¹Tr P_j(·) - a|`.
* `rpSplitAssemble`: the split state `(H_R, C, V)` built from a residual pair sample and an
  exterior path sample (pure reindexing).
* `rp_pairResidual_assemble` (deterministic): for that split state,
  `K(E) = V - C*(H_R - E)⁻¹C - E` is `rpMatrix - pathSchur E π - E`, reindexed; hence the pair
  observable is `rpObs` at `X = pathSchur E π` (`rp_pairObs_assemble`).
* Two statements are isolated as named propositions (they are proved in `ResidualSplitLaw` and
  `ResidualLayer`):
  - `ResidualSplitLaw` (law identification by deconvolution): every splitting law `Pω` of the pair
    splitting is the image of `rpLaw ⊗ pathLaw (n-2)` under `rpSplitAssemble`. (True because the
    characteristic function of the embedded `GUE_{2W}(s/(2W))` never vanishes, so `Pω` is
    determined by the exact law; and the variances add up: `(c-s/2)/W + s/(2W) = c/W`,
    `(b-s/2)/W + s/(2W) = b/W`.)
  - `ResidualPairLayerBound` (the residual-pair analogue of the layer-contraction lemma and of the
    fluctuation clause of the trace–matrix lemma, for the residual pair layer): `MeanEquations`,
    `ComparisonStability` and `LayerContraction` are stated for `layerLaw` with the variances
    `(1-2b)/W, b/W` and the four `LayerShape`s only; the residual layer (two blocks with an
    internal bond, no port, modified variances, shift `sa`) is not covered by them.
* `residualPair_of_path`: the exact type of the `residualPair` field of `MatchedTracesContract`,
  from the `path` clause and the two statements above; the assembly is that of
  `commonPort_of_path` (crude bound `‖(V-E-X-sa)⁻¹‖ ≤ (s|Im a|)⁻¹`, deterministic).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure PairSite ExteriorSite PairMatrix
  SplitState IsPairSplitting)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## 1. The residual pair layer
-/

/-- Residual pair sample: the two diagonal blocks and the internal bond. -/
abbrev RpSample (W : ℕ) := (Fin 2 → Matrix (Fin W) (Fin W) ℂ) × Matrix (Fin W) (Fin W) ℂ

/-- Law of the residual pair layer: `A_j ~ GUE_W((c - s/2)/W)`, bond `Gin((b - s/2)/W)`. -/
def rpLaw (W : ℕ) (b s : ℝ) : Measure (RpSample W) :=
  (Measure.pi fun _ : Fin 2 => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b - s / 2) / W))).prod
    (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal ((b - s / 2) / W)))

instance rp_isProbabilityMeasure_rpLaw (W : ℕ) (b s : ℝ) : IsProbabilityMeasure (rpLaw W b s) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold rpLaw
  infer_instance

/-- The residual pair matrix `V` (index `0 ↔ i+1`, `1 ↔ i`; the bond `B` sits at
`(1, 0)`, i.e. at `(i, i+1)`). -/
def rpMatrix {W : ℕ} (ω : RpSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  fun x y =>
    if x.1 = y.1 then ω.1 x.1 x.2 y.2
    else if x.1 = 1 then ω.2 x.2 y.2
    else star (ω.2 y.2 x.2)

/-- The residual test matrix `(V - E - X - sa)⁻¹`. -/
def rpResolvent (E s : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : RpSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (rpMatrix ω - (E : ℂ) • 1 - X - ((s : ℂ) * matchedA E) • 1)⁻¹

/-- The residual observable `max_j |W⁻¹Tr P_j (V - E - X - sa)⁻¹ - a|`. -/
def rpObs (E s : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : RpSample W) : ℝ :=
  max ‖blockTrace (rpResolvent E s X ω) 0 - matchedA E‖ ‖blockTrace (rpResolvent E s X ω) 1 - matchedA E‖

/-- **The residual pair layer bound** (residual-pair analogue of the layer-contraction lemma, common to its
mean and fluctuation halves). `b, I = bulkInterval κ` and the fixed admissible
`0 < s < 2 min(c, b)` first; then `d_*, C, ε > 0`; uniformly in `W ≥ 1`, every deterministic
Hermitian two-port `X` and `E ∈ I`, under `rpLaw W b s`:
* mean: on `d(X) ≤ d_*`, `|E W⁻¹Tr P_j(V - E - X - sa)⁻¹ - a| ≤ C d(X) + C W⁻²` for `j = 0, 1`;
* fluctuation: `‖W⁻¹Tr P_j(·) - E W⁻¹Tr P_j(·)‖_q ≤ C√q/W` for `2 ≤ q ≤ εW`.
(`d(X) = matchedDistance b E X` at `z_∂`; at the matched value the mean-field inverse is
`(z_∂ - X)⁻¹` since `(c - s/2) + (b - s/2) + s = 1 - b`.) -/
def ResidualPairLayerBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ s : ℝ, 0 < κ → 0 < s → s < 2 * min (1 - 2 * b) b →
    ∃ dstar C ε : ℝ, 0 < dstar ∧ 0 < ε ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ,
        (matchedDistance b E X ≤ dstar → ∀ j : Fin 2,
          ‖(∫ ω, blockTrace (rpResolvent E s X ω) j ∂rpLaw W b s) - matchedA E‖ ≤
            C * matchedDistance b E X + C / (W : ℝ) ^ 2) ∧
        ∀ q : ℝ, 2 ≤ q → q ≤ ε * W → ∀ j : Fin 2,
          eLpNorm (fun ω => blockTrace (rpResolvent E s X ω) j -
              ∫ ω', blockTrace (rpResolvent E s X ω') j ∂rpLaw W b s)
            (ENNReal.ofReal q) (rpLaw W b s) ≤ ENNReal.ofReal (C * Real.sqrt q / W)

/-!
## 2. The split state from a residual pair sample and an exterior path
-/

section Geometry

variable {p : Parameters}

/-- Pair offsets: index `0` at `i + 1`, index `1` at `i`. -/
def rpPairOff (a : Fin 2) : ℕ := if a = 0 then 1 else 0

theorem rpPairOff_lt (a : Fin 2) : rpPairOff a < p.n := by
  have := p.n_ge_four
  unfold rpPairOff; split_ifs <;> omega

theorem rpBlk_pair_mem (i : ZMod p.n) (a : Fin 2) : rngBlk i (rpPairOff a) = i ∨
    rngBlk i (rpPairOff a) = i + 1 := by
  unfold rpPairOff
  split_ifs
  · right; simp [rngBlk]
  · left; exact rngBlk_zero i

theorem rpBlk_ext_not_mem (i : ZMod p.n) (j : Fin (p.n - 2)) :
    ¬ (rngBlk i (j.val + 2) = i ∨ rngBlk i (j.val + 2) = i + 1) := by
  have h4 := p.n_ge_four
  have hj := j.isLt
  rintro (h | h)
  · have h' : rngBlk i (j.val + 2) = rngBlk i 0 := h.trans (rngBlk_zero i).symm
    rw [rngBlk_eq_iff i (by omega) (by omega)] at h'
    omega
  · have h' : rngBlk i (j.val + 2) = rngBlk i 1 := h.trans (by simp [rngBlk])
    rw [rngBlk_eq_iff i (by omega) (by omega)] at h'
    omega

theorem rp_card_pairBlocks (i : ZMod p.n) :
    Fintype.card {j : ZMod p.n // j = i ∨ j = i + 1} = 2 := by
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun j : ZMod p.n => j = i ∨ j = i + 1) = {i, i + 1} := by
    ext j; simp
  rw [hfilter, Finset.card_pair (rng_add_one_ne p i).symm]

/-- The pair blocks. -/
def rpPairBlk (i : ZMod p.n) (a : Fin 2) : {j : ZMod p.n // j = i ∨ j = i + 1} :=
  ⟨rngBlk i (rpPairOff a), rpBlk_pair_mem i a⟩

theorem rpPairBlk_bijective (i : ZMod p.n) : Function.Bijective (rpPairBlk i) := by
  rw [Fintype.bijective_iff_injective_and_card, rp_card_pairBlocks, Fintype.card_fin]
  refine ⟨fun a a' h => ?_, rfl⟩
  have h' : rngBlk i (rpPairOff a) = rngBlk i (rpPairOff a') := congrArg Subtype.val h
  rw [rngBlk_eq_iff i (rpPairOff_lt a) (rpPairOff_lt a')] at h'
  unfold rpPairOff at h'
  by_cases ha : a = 0 <;> by_cases ha' : a' = 0
  · rw [ha, ha']
  · rw [ite_eq_left ha, ite_eq_right ha'] at h'; omega
  · rw [ite_eq_right ha, ite_eq_left ha'] at h'; omega
  · exact rng_fin2_eq ha ha'

/-- The exterior blocks `i + 2 + j`. -/
def rpExtBlk (i : ZMod p.n) (j : Fin (p.n - 2)) : {k : ZMod p.n // ¬ (k = i ∨ k = i + 1)} :=
  ⟨rngBlk i (j.val + 2), rpBlk_ext_not_mem i j⟩

theorem rpExtBlk_bijective (i : ZMod p.n) : Function.Bijective (rpExtBlk i) := by
  have h4 := p.n_ge_four
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro j j' h
    have h' : rngBlk i (j.val + 2) = rngBlk i (j'.val + 2) := congrArg Subtype.val h
    rw [rngBlk_eq_iff i (by omega) (by omega)] at h'
    exact Fin.ext (by omega)
  · rw [Fintype.card_fin, Fintype.card_subtype_compl, rp_card_pairBlocks, ZMod.card]

/-- Pair sites: `(a, x) ↦ (i + rpPairOff a, x)`. -/
def rpPairEquiv (i : ZMod p.n) : Fin 2 × Fin p.W ≃ PairSite p i :=
  ((Equiv.ofBijective _ (rpPairBlk_bijective i)).prodCongr (Equiv.refl _)).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun j : ZMod p.n => j = i ∨ j = i + 1)).symm

/-- Exterior sites: `(j, x) ↦ (i + 2 + j, x)`. -/
def rpExtEquiv (i : ZMod p.n) : Fin (p.n - 2) × Fin p.W ≃ ExteriorSite p i :=
  ((Equiv.ofBijective _ (rpExtBlk_bijective i)).prodCongr (Equiv.refl _)).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun j : ZMod p.n => ¬ (j = i ∨ j = i + 1))).symm

theorem rpPairEquiv_val (i : ZMod p.n) (a : Fin 2) (x : Fin p.W) :
    (rpPairEquiv i (a, x)).1 = (rngBlk i (rpPairOff a), x) := rfl

/-- **The split state** `(H_R, C, V)` of a residual pair sample `ω` and an exterior path
sample `π` (`n - 2` blocks): `H_R` is the path matrix, `C` its port coupling, `V` the residual
pair matrix, all reindexed. -/
def rpSplitAssemble (i : ZMod p.n) (x : RpSample p.W × PathSample p.W (p.n - 2)) :
    SplitState p i :=
  ((pathMatrix x.2).submatrix (rpExtEquiv i).symm (rpExtEquiv i).symm,
    (pathPortCoupling x.2).submatrix (rpExtEquiv i).symm (rpPairEquiv i).symm,
    (rpMatrix x.1).submatrix (rpPairEquiv i).symm (rpPairEquiv i).symm)

theorem rp_measurable_rpMatrix (W : ℕ) : Measurable (fun ω : RpSample W => rpMatrix ω) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold rpMatrix
  split_ifs
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp measurable_fst))
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)
  · exact continuous_star.measurable.comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp measurable_snd))

theorem rp_measurable_splitAssemble (i : ZMod p.n) : Measurable (rpSplitAssemble (p := p) i) := by
  have hP := measurable_pathMatrix p.W (p.n - 2)
  have hC := measurable_pathPortCoupling p.W (p.n - 2)
  have hV := rp_measurable_rpMatrix p.W
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      pg_entry (hP.comp measurable_snd) _ _
  · exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      pg_entry (hC.comp measurable_snd) _ _
  · exact measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y =>
      pg_entry (hV.comp measurable_fst) _ _

/-- **Deterministic reduction** (unconditional): `K(E) = V - C*(H_R - E)⁻¹C - E` of the
assembled split state is `rpMatrix ω - pathSchur E π - E`, reindexed. -/
theorem rp_pairResidual_assemble (i : ZMod p.n) (x : RpSample p.W × PathSample p.W (p.n - 2))
    (E : ℝ) :
    pairResidual p i (rpSplitAssemble i x) E =
      (rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1).submatrix (rpPairEquiv i).symm
        (rpPairEquiv i).symm := by
  unfold pairResidual BlockBand.Coarea.physicalCoareaF BlockBand.Coarea.physicalCoareaResolvent
    rpSplitAssemble pathSchur
  dsimp only
  have h1 : (pathMatrix x.2).submatrix (rpExtEquiv i).symm (rpExtEquiv i).symm - (E : ℂ) • 1 =
      (pathMatrix x.2 - (E : ℂ) • 1).submatrix (rpExtEquiv i).symm (rpExtEquiv i).symm := by
    rw [show (pathMatrix x.2 - (E : ℂ) • 1).submatrix (rpExtEquiv i).symm (rpExtEquiv i).symm =
        (pathMatrix x.2).submatrix (rpExtEquiv i).symm (rpExtEquiv i).symm -
          (E : ℂ) • (1 : Matrix (Fin (p.n - 2) × Fin p.W) (Fin (p.n - 2) × Fin p.W) ℂ).submatrix
            (rpExtEquiv i).symm (rpExtEquiv i).symm from rfl, submatrix_one_equiv]
  have h2 : (E : ℂ) • (1 : PairMatrix p i) = ((E : ℂ) • (1 : Matrix (Fin 2 × Fin p.W)
      (Fin 2 × Fin p.W) ℂ)).submatrix (rpPairEquiv i).symm (rpPairEquiv i).symm := by
    rw [show ((E : ℂ) • (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ)).submatrix
        (rpPairEquiv i).symm (rpPairEquiv i).symm = (E : ℂ) • (1 : Matrix (Fin 2 × Fin p.W)
          (Fin 2 × Fin p.W) ℂ).submatrix (rpPairEquiv i).symm (rpPairEquiv i).symm from rfl,
      submatrix_one_equiv]
  rw [h1, inv_submatrix_equiv, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, h2]
  rfl

theorem rp_pairBlockTrace_submatrix (i : ZMod p.n) (N : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ)
    (a : Fin 2) :
    pairBlockTrace p i (N.submatrix (rpPairEquiv i).symm (rpPairEquiv i).symm)
        (rngBlk i (rpPairOff a)) = blockTrace N a := by
  unfold pairBlockTrace blockTrace
  congr 1
  rw [← Fintype.sum_equiv (rpPairEquiv i) (fun y => if (rpPairEquiv i y).1.1 = rngBlk i (rpPairOff a)
      then N.submatrix (rpPairEquiv i).symm (rpPairEquiv i).symm (rpPairEquiv i y)
        (rpPairEquiv i y) else 0) _ (fun _ => rfl), Fintype.sum_prod_type]
  simp only [submatrix_apply, Equiv.symm_apply_apply, rpPairEquiv_val]
  rw [Fin.sum_univ_two]
  have hne : rngBlk i (rpPairOff 0) ≠ rngBlk i (rpPairOff 1) := by
    rw [Ne, rngBlk_eq_iff i (rpPairOff_lt 0) (rpPairOff_lt 1)]
    simp [rpPairOff]
  rcases rng_fin2_cases a with rfl | rfl
  · simp [hne.symm]
  · simp [hne]

/-- **The pair observable** of the assembled split state is `rpObs` at `X = pathSchur E π`. -/
theorem rp_pairObs_assemble (i : ZMod p.n) (x : RpSample p.W × PathSample p.W (p.n - 2))
    (E s : ℝ) :
    max ‖pairBlockTrace p i ((pairResidual p i (rpSplitAssemble i x) E -
        ((s : ℂ) * matchedA E) • 1)⁻¹) i - matchedA E‖
      ‖pairBlockTrace p i ((pairResidual p i (rpSplitAssemble i x) E -
        ((s : ℂ) * matchedA E) • 1)⁻¹) (i + 1) - matchedA E‖ =
      rpObs E s (pathSchur E x.2) x.1 := by
  have hM : (pairResidual p i (rpSplitAssemble i x) E - ((s : ℂ) * matchedA E) • 1)⁻¹ =
      (rpResolvent E s (pathSchur E x.2) x.1).submatrix (rpPairEquiv i).symm (rpPairEquiv i).symm := by
    rw [rp_pairResidual_assemble, rpResolvent, ← inv_submatrix_equiv]
    congr 1
    rw [show rpMatrix x.1 - (E : ℂ) • 1 - pathSchur E x.2 - ((s : ℂ) * matchedA E) • 1 =
        (rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1) - ((s : ℂ) * matchedA E) • 1 by abel]
    rw [show ((rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1) - ((s : ℂ) * matchedA E) •
        (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ)).submatrix (rpPairEquiv i).symm
          (rpPairEquiv i).symm = (rpMatrix x.1 - pathSchur E x.2 - (E : ℂ) • 1).submatrix
          (rpPairEquiv i).symm (rpPairEquiv i).symm - ((s : ℂ) * matchedA E) •
          (1 : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ).submatrix (rpPairEquiv i).symm
            (rpPairEquiv i).symm from rfl, submatrix_one_equiv]
  have e1 := rp_pairBlockTrace_submatrix i (rpResolvent E s (pathSchur E x.2) x.1) 1
  have e0 := rp_pairBlockTrace_submatrix i (rpResolvent E s (pathSchur E x.2) x.1) 0
  rw [show rngBlk i (rpPairOff 1) = i by simp [rpPairOff, rngBlk_zero]] at e1
  rw [show rngBlk i (rpPairOff 0) = i + 1 by simp [rpPairOff, rngBlk]] at e0
  rw [hM, e0, e1, rpObs, max_comm]

end Geometry

/-- **The residual splitting law** (law identification of the splitting, by deconvolution): every
splitting law `Pω` of the pair splitting at an admissible `0 < s < 2 min(c, b)` is the image of
`rpLaw W b s ⊗ pathLaw W (n-2) b` under `rpSplitAssemble`. -/
def ResidualSplitLaw : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n) (s : ℝ), 0 < s →
    s < 2 * min (1 - 2 * p.b) p.b → ∀ Pω : Measure (SplitState p i),
      IsPairSplitting p i model s Pω →
        Pω = ((rpLaw p.W p.b s).prod (pathLaw p.W (p.n - 2) p.b)).map (rpSplitAssemble i)

/-!
## 3. Transfer and the assembly of the residual-pair clause
-/

section Assembly

variable {p : Parameters}

/-- The residual-pair observable on split states. -/
def rpSplitObs (i : ZMod p.n) (E s : ℝ) (ω : SplitState p i) : ℝ :=
  max ‖pairBlockTrace p i ((pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) i - matchedA E‖
    ‖pairBlockTrace p i ((pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) (i + 1) -
      matchedA E‖

theorem rp_measurable_splitObs (i : ZMod p.n) (E s : ℝ) :
    Measurable (rpSplitObs (p := p) i E s) := by
  have h1 : Measurable (fun ω : SplitState p i => ω.1) := measurable_fst
  have h2 : Measurable (fun ω : SplitState p i => ω.2.1) := measurable_fst.comp measurable_snd
  have h3 : Measurable (fun ω : SplitState p i => ω.2.2) := measurable_snd.comp measurable_snd
  have hK : Measurable (fun ω : SplitState p i => pairResidual p i ω E) := by
    unfold pairResidual BlockBand.Coarea.physicalCoareaF BlockBand.Coarea.physicalCoareaResolvent
    exact (h3.sub (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose h2)
      (measurable_matrix_inv.comp (h1.sub measurable_const))) h2)).sub measurable_const
  have hR : Measurable (fun ω : SplitState p i =>
      (pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) :=
    measurable_matrix_inv.comp (hK.sub measurable_const)
  have hT : ∀ k : ZMod p.n, Measurable (fun ω : SplitState p i => pairBlockTrace p i
      ((pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) k) := by
    intro k
    unfold pairBlockTrace
    refine measurable_const.mul (Finset.measurable_sum _ fun x _ => ?_)
    split_ifs
    · exact pg_entry hR x x
    · exact measurable_const
  exact (((hT i).sub measurable_const).norm).max (((hT (i + 1)).sub measurable_const).norm)

/-- **Transfer** under the law identification `ResidualSplitLaw`. -/
theorem rp_eLpNorm_residual (hlaw : ResidualSplitLaw) (model : p.GaussianRingModel)
    (i : ZMod p.n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 2 * min (1 - 2 * p.b) p.b)
    {Pω : Measure (SplitState p i)} (hsplit : IsPairSplitting p i model s Pω) (E : ℝ)
    (q : ℝ≥0∞) :
    eLpNorm (rpSplitObs i E s) q Pω =
      eLpNorm (fun x : RpSample p.W × PathSample p.W (p.n - 2) => rpObs E s (pathSchur E x.2) x.1) q
        ((rpLaw p.W p.b s).prod (pathLaw p.W (p.n - 2) p.b)) := by
  rw [hlaw p model i s hs0 hs1 Pω hsplit, eLpNorm_map_measure
    (rp_measurable_splitObs i E s).aestronglyMeasurable
    (rp_measurable_splitAssemble i).aemeasurable]
  congr 1
  funext x
  exact rp_pairObs_assemble i x E s

theorem rp_rpMatrix_isHermitian {W : ℕ} (ω : RpSample W) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (rpMatrix ω).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, rpMatrix]
  by_cases h : x.1 = y.1
  · rw [ite_eq_left h.symm, ite_eq_left h, h]
    exact (hA y.1).apply x.2 y.2
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
    rcases rng_fin2_cases x.1 with hx | hx <;> rcases rng_fin2_cases y.1 with hy | hy
    · exact absurd (hx.trans hy.symm) h
    · rw [ite_eq_left hy, ite_eq_right (by rw [hx]; exact zero_ne_one)]
    · rw [ite_eq_right (by rw [hy]; exact zero_ne_one), ite_eq_left hx, star_star]
    · exact absurd (hx.trans hy.symm) h

theorem rp_measurable_resolvent {Ω : Type*} [MeasurableSpace Ω] (E s : ℝ) {W : ℕ}
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ωf : Ω → RpSample W}
    (hX : Measurable Xf) (hω : Measurable ωf) :
    Measurable (fun t => rpResolvent E s (Xf t) (ωf t)) := by
  unfold rpResolvent
  exact measurable_matrix_inv.comp ((((rp_measurable_rpMatrix W).comp hω).sub
    measurable_const).sub hX |>.sub measurable_const)

/-- **Deterministic crude bound** `‖(V - E - X - sa)⁻¹‖ ≤ y⁻¹` for `0 < y ≤ -s Im a`. -/
theorem rp_norm_resolvent_le {W : ℕ} (E s : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (ω : RpSample W) (hA : ∀ j, (ω.1 j).IsHermitian) {y : ℝ} (hy : 0 < y)
    (hya : y ≤ -(s * (matchedA E).im)) :
    ‖rpResolvent E s X ω‖ ≤ y⁻¹ := by
  have hH : (rpMatrix ω - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X).IsHermitian := by
    refine ((rp_rpMatrix_isHermitian ω hA).sub ?_).sub hX
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have heq : rpMatrix ω - (E : ℂ) • 1 - X - ((s : ℂ) * matchedA E) • 1 =
      (rpMatrix ω - (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) -
        diagonal (fun _ => (s : ℂ) * matchedA E) := by
    rw [← smul_one_eq_diagonal]
  unfold rpResolvent
  rw [heq]
  refine lct_norm_shifted_inv_le _ hH _ hy fun _ => ?_
  rw [Complex.im_ofReal_mul]
  exact hya

/-- A uniform lower bound `η ≤ -Im a(E)` and `|E| ≤ 2` on `bulkInterval κ`. -/
theorem rp_im_a_lower {κ : ℝ} (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ ∀ E ∈ bulkInterval κ, η ≤ -(matchedA E).im ∧ |E| ≤ 2 := by
  by_cases h : (bulkInterval κ).Nonempty
  · obtain ⟨E₀, hE₀⟩ := h
    have hκ2 : κ ≤ 2 := by linarith [hE₀.1, hE₀.2]
    refine ⟨Real.sqrt (4 - (2 - κ) ^ 2) / 2, ?_, fun E hE => ⟨?_,
      (abs_lt_two_of_mem_bulkInterval hκ hE).le⟩⟩
    · have := Real.sqrt_pos.mpr (four_sub_sq_pos hκ (by linarith))
      positivity
    · have := matchedA_im_le_of_mem_bulkInterval hE
      linarith
  · exact ⟨1, one_pos, fun E hE => absurd ⟨E, hE⟩ h⟩

set_option maxHeartbeats 400000 in
/-- **The residual-pair clause** of the matched-traces theorem: the exact type of the
`residualPair` field of `MatchedTracesContract`, from the `path` clause and the two statements
`ResidualSplitLaw` (law identification) and `ResidualPairLayerBound` (residual layer). -/
theorem residualPair_of_path
    (hpath : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
      ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
          eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
              ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
            (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W))
    (hlaw : ResidualSplitLaw) (hlay : ResidualPairLayerBound) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T s : ℝ, 0 < κ → 0 < s →
    s < 2 * min (1 - 2 * b) b →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model s Pω → ∀ E ∈ bulkInterval κ,
      ∀ q : ℝ, 2 ≤ q → q ≤ ε₀ * p.W →
        eLpNorm (fun ω =>
            max ‖pairBlockTrace p i ((pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) i -
                matchedA E‖
              ‖pairBlockTrace p i ((pairResidual p i ω E - ((s : ℂ) * matchedA E) • 1)⁻¹) (i + 1) -
                matchedA E‖)
          (ENNReal.ofReal q) Pω ≤ ENNReal.ofReal (C * Real.sqrt q / p.W) := by
  intro b hb0 hb1 κ T s hκ hs0 hs1
  obtain ⟨dstar, Cl, ε, hds, hε, hlb⟩ := hlay b hb0 hb1 κ s hκ hs0 hs1
  obtain ⟨ηa, hηa, hηaE⟩ := rp_im_a_lower hκ
  obtain ⟨εp, Cp, hεp, hpb⟩ := hpath b hb0 hb1 κ T hκ
  set Cl' := max Cl 0 with hCl'
  set Cp' := max Cp 0 with hCp'
  set M0 := (s * ηa)⁻¹ + 1 with hM0def
  have hCl0 : 0 ≤ Cl' := le_max_right _ _
  have hCp0 : 0 ≤ Cp' := le_max_right _ _
  have hsη : 0 < s * ηa := mul_pos hs0 hηa
  have hM0 : 0 ≤ M0 := by positivity
  refine ⟨min ε εp, 2 * Cl' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar), lt_min hε hεp, ?_⟩
  intro p hpb' hnT model i Pω hsplit E hE q hq2 hqε
  subst hpb'
  set b := p.b
  set W := p.W
  set r := p.n - 2 with hr
  have hW : 0 < W := p.W_pos
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hn4 := p.n_ge_four
  have hr1 : 1 ≤ r := by omega
  have hrT : (r : ℝ) ≤ T * W := le_trans (by exact_mod_cast (by omega : r ≤ p.n)) hnT
  have hq0 : 0 < q := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr (by linarith)
  have hq0' : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hqε' : q ≤ ε * W := hqε.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le)
  have hqεp : q ≤ εp * W := hqε.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
  obtain ⟨hηE, hEabs⟩ := hηaE E hE
  have hsq : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  set x := Real.sqrt q / W with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxW2 : 1 / (W : ℝ) ^ 2 ≤ x := by
    refine le_trans ?_ (div_le_div_of_nonneg_right hsq hWr.le)
    exact one_div_le_one_div_of_le hWr (by nlinarith)
  change eLpNorm (rpSplitObs i E s) (ENNReal.ofReal q) Pω ≤ _
  rw [rp_eLpNorm_residual hlaw model i hs0 hs1 hsplit E (ENNReal.ofReal q)]
  set μ := (rpLaw W b s).prod (pathLaw W r b) with hμ
  set d : PathSample W r → ℝ := fun π => matchedDistance b E (pathSchur E π) with hd
  set g : Fin 2 → RpSample W × PathSample W r → ℂ :=
    fun j y => blockTrace (rpResolvent E s (pathSchur E y.2) y.1) j with hg
  set m : Fin 2 → PathSample W r → ℂ := fun j π =>
    ∫ ω, blockTrace (rpResolvent E s (pathSchur E π) ω) j ∂rpLaw W b s with hm
  have hdm : Measurable d := (srec_measurable_matchedDistance b E W).comp (measurable_pathSchur W r E)
  have hgm : ∀ j, Measurable (g j) := fun j =>
    srec_measurable_blockTrace (rp_measurable_resolvent E s
      ((measurable_pathSchur W r E).comp measurable_snd) measurable_fst) j
  have hmm : ∀ j, Measurable (m j) := fun j =>
    (StronglyMeasurable.integral_prod_left (μ := rpLaw W b s)
      (f := fun (ω : RpSample W) (π : PathSample W r) =>
        blockTrace (rpResolvent E s (pathSchur E π) ω) j) (hgm j).stronglyMeasurable).measurable
  set S := {π : PathSample W r | dstar < d π} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hdm
  set f1 : RpSample W × PathSample W r → ℝ :=
    fun y => ‖g 0 y - m 0 y.2‖ + ‖g 1 y - m 1 y.2‖ with hf1
  set f2 : RpSample W × PathSample W r → ℝ :=
    fun y => Cl' * d y.2 + Cl' / (W : ℝ) ^ 2 with hf2
  set f4 : RpSample W × PathSample W r → ℝ :=
    (Prod.snd ⁻¹' S).indicator (fun _ => M0) with hf4
  have hd0 : ∀ π, 0 ≤ d π := fun π => (norm_nonneg _).trans (le_max_left _ _)
  have hf1m : Measurable f1 :=
    (((hgm 0).sub ((hmm 0).comp measurable_snd)).norm).add
      (((hgm 1).sub ((hmm 1).comp measurable_snd)).norm)
  have hA : ∀ᵐ y ∂μ, ∀ j, (y.1.1 j).IsHermitian := by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    have h := ae_blocks_isHermitian 2 W (Real.toNNReal ((1 - 2 * b - s / 2) / W))
    have h' : ∀ᵐ ω ∂rpLaw W b s, ∀ j, (ω.1 j).IsHermitian := by
      unfold rpLaw
      exact (Measure.quasiMeasurePreserving_fst).ae h
    exact (Measure.quasiMeasurePreserving_fst).ae h'
  have hX : ∀ᵐ y ∂μ, (pathSchur E y.2).IsHermitian :=
    (Measure.quasiMeasurePreserving_snd).ae (srec_ae_pathSchur_isHermitian W r b E)
  have hya : s * ηa ≤ -(s * (matchedA E).im) := by nlinarith
  have hbound : ∀ᵐ y ∂μ, ‖rpObs E s (pathSchur E y.2) y.1‖ ≤ f1 y + f2 y + f4 y := by
    filter_upwards [hA, hX] with y hyA hyX
    have hobs0 : 0 ≤ rpObs E s (pathSchur E y.2) y.1 := (norm_nonneg _).trans (le_max_left _ _)
    rw [Real.norm_of_nonneg hobs0]
    have hf1nn : 0 ≤ f1 y := by simp only [hf1]; positivity
    have hf2nn : 0 ≤ f2 y := by simp only [hf2]; have := hd0 y.2; positivity
    by_cases hdy : d y.2 ≤ dstar
    · have hnot : y ∉ Prod.snd ⁻¹' S := by
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq, not_lt]; exact hdy
      simp only [hf4]
      rw [Set.indicator_of_notMem hnot, add_zero]
      have hmean := (hlb W hW (pathSchur E y.2) hyX E hE).1 hdy
      have hmj : ∀ j : Fin 2, ‖m j y.2 - matchedA E‖ ≤ f2 y := by
        intro j
        refine (hmean j).trans ?_
        simp only [hf2]
        exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (hd0 y.2))
          (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
      have hj : ∀ j : Fin 2, ‖g j y - matchedA E‖ ≤ f1 y + f2 y := by
        intro j
        have hfj : ‖g j y - m j y.2‖ ≤ f1 y := by
          simp only [hf1]
          rcases rng_fin2_cases j with rfl | rfl
          · exact le_add_of_nonneg_right (norm_nonneg _)
          · exact le_add_of_nonneg_left (norm_nonneg _)
        calc ‖g j y - matchedA E‖ ≤ ‖g j y - m j y.2‖ + ‖m j y.2 - matchedA E‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ f1 y + f2 y := add_le_add hfj (hmj j)
      exact max_le (hj 0) (hj 1)
    · have hmem : y ∈ Prod.snd ⁻¹' S := by
        simp only [hSdef, Set.mem_preimage, Set.mem_ofPred_eq]; exact not_le.mp hdy
      simp only [hf4]
      rw [Set.indicator_of_mem hmem]
      have hcr := rp_norm_resolvent_le E s hyX y.1 hyA hsη hya
      have ha := norm_matchedA hEabs
      have hj : ∀ j : Fin 2, ‖blockTrace (rpResolvent E s (pathSchur E y.2) y.1) j - matchedA E‖
          ≤ M0 := fun j =>
        (norm_sub_le _ _).trans (by rw [ha]; linarith [(lct_norm_blockTrace_le _ j).trans hcr])
      have := max_le (hj 0) (hj 1)
      simp only [rpObs]
      linarith
  have hf1e : eLpNorm f1 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (2 * Cl' * Real.sqrt q / W) := by
    refine srec_eLpNorm_prod_le hf1m hq0 ?_
    filter_upwards [srec_ae_pathSchur_isHermitian W r b E] with π hπ
    have hfl := (hlb W hW (pathSchur E π) hπ E hE).2 q hq2 hqε'
    have hmeas : ∀ j, Measurable (fun ω => blockTrace (rpResolvent E s (pathSchur E π) ω) j -
        m j π) := fun j =>
      (srec_measurable_blockTrace (rp_measurable_resolvent E s measurable_const measurable_id) j).sub
        measurable_const
    have hj : ∀ j, eLpNorm (fun ω => ‖blockTrace (rpResolvent E s (pathSchur E π) ω) j - m j π‖)
        (ENNReal.ofReal q) (rpLaw W b s) ≤ ENNReal.ofReal (Cl' * Real.sqrt q / W) := by
      intro j
      rw [eLpNorm_norm _ (hmeas j).aestronglyMeasurable]
      refine (hfl j).trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.sqrt_nonneg _)) hWr.le
    show eLpNorm (fun ω => ‖blockTrace (rpResolvent E s (pathSchur E π) ω) 0 - m 0 π‖ +
        ‖blockTrace (rpResolvent E s (pathSchur E π) ω) 1 - m 1 π‖) (ENNReal.ofReal q)
        (rpLaw W b s) ≤ _
    refine (eLpNorm_add_le hq1).trans ?_
    refine (add_le_add (hj 0) (hj 1)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have hdq : eLpNorm d (ENNReal.ofReal q) (pathLaw W r b) ≤
      ENNReal.ofReal (Cp' * Real.sqrt q / W) := by
    refine (hpb W hW q hq2 hqεp r hr1 hrT E hE).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _)) hWr.le
  have hf2e : eLpNorm f2 (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Cl' * (Cp' * Real.sqrt q / W)) + ENNReal.ofReal (Cl' / (W : ℝ) ^ 2) := by
    refine (eLpNorm_add_le (f := fun y : RpSample W × PathSample W r => Cl' * d y.2)
      (g := fun _ => Cl' / (W : ℝ) ^ 2) hq1).trans (add_le_add ?_ ?_)
    · have : (fun y : RpSample W × PathSample W r => Cl' * d y.2) = Cl' • (d ∘ Prod.snd) := rfl
      rw [this, eLpNorm_const_smul, Real.enorm_of_nonneg hCl0,
        eLpNorm_comp_measurePreserving hdm.aestronglyMeasurable measurePreserving_snd,
        ENNReal.ofReal_mul hCl0]
      gcongr
    · rw [eLpNorm_const _ hq0' (IsProbabilityMeasure.ne_zero μ), measure_univ,
        ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg (by positivity)]
  have hf4e : eLpNorm f4 (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (M0 * (Cp' * Real.sqrt q / W / dstar)) := by
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
  have hobsm : AEStronglyMeasurable
      (fun y : RpSample W × PathSample W r => rpObs E s (pathSchur E y.2) y.1) μ := by
    have h := rp_measurable_resolvent (Ω := RpSample W × PathSample W r) E s
      ((measurable_pathSchur W r E).comp measurable_snd) measurable_fst
    unfold rpObs
    exact ((((srec_measurable_blockTrace h 0).sub measurable_const).norm).max
      (((srec_measurable_blockTrace h 1).sub measurable_const).norm)).aestronglyMeasurable
  calc eLpNorm (fun y : RpSample W × PathSample W r => rpObs E s (pathSchur E y.2) y.1)
        (ENNReal.ofReal q) μ
      ≤ eLpNorm (fun y => f1 y + f2 y + f4 y) (ENNReal.ofReal q) μ :=
        eLpNorm_mono_ae_real hobsm hbound
    _ ≤ eLpNorm f1 (ENNReal.ofReal q) μ + eLpNorm f2 (ENNReal.ofReal q) μ +
          eLpNorm f4 (ENNReal.ofReal q) μ := by
        refine (eLpNorm_add_le (f := fun y => f1 y + f2 y) (g := f4) hq1).trans ?_
        exact add_le_add (eLpNorm_add_le (f := f1) (g := f2) hq1) le_rfl
    _ ≤ ENNReal.ofReal (2 * Cl' * Real.sqrt q / W) +
          (ENNReal.ofReal (Cl' * (Cp' * Real.sqrt q / W)) + ENNReal.ofReal (Cl' / (W : ℝ) ^ 2)) +
          ENNReal.ofReal (M0 * (Cp' * Real.sqrt q / W / dstar)) :=
        add_le_add (add_le_add hf1e hf2e) hf4e
    _ ≤ ENNReal.ofReal ((2 * Cl' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar)) * Real.sqrt q / W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hClW : Cl' / (W : ℝ) ^ 2 ≤ Cl' * x := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hxW2 hCl0
        have e1 : 2 * Cl' * Real.sqrt q / W = 2 * Cl' * x := by rw [hxdef]; ring
        have e2 : Cl' * (Cp' * Real.sqrt q / W) = Cl' * Cp' * x := by rw [hxdef]; ring
        have e3 : M0 * (Cp' * Real.sqrt q / W / dstar) = M0 * (Cp' / dstar) * x := by
          rw [hxdef]; ring
        have e4 : (2 * Cl' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar)) * Real.sqrt q / W =
            (2 * Cl' + Cl' * Cp' + Cl' + M0 * (Cp' / dstar)) * x := by rw [hxdef]; ring
        rw [e1, e2, e3, e4]
        nlinarith

end Assembly

end BlockBand.Layers
