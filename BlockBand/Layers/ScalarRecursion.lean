module

public import BlockBand.Layers.PathGrowthLaw
public import BlockBand.Layers.LayerContraction
public import BlockBand.Layers.TraceMatrix

/-!
# The stopped scalar recursion: the one-step matched-trace recursion and the scalar exit bound

Steps 3–4 of the proof of the matched-traces theorem: the constructor `scalarRecursion_holds` of
`ScalarRecursionContract`, field by field.

Law: `layerLaw W b .separate` (fresh separate-port layer, conditional on a deterministic
Hermitian two-port `X`) for the one-step field; `growthLaw W r₀ L b` (core `r₀ ∈ {1,2}` and `L` fresh
layers) for the exit field. `z = z_∂(E) = boundaryZ b E`, `E ∈ bulkInterval κ`, `d = matchedDistance`;
norms: `ℓ²` operator norm on matrices.

* The one-step field (the one-step matched-trace recursion): a.s. `(z - X₊)⁻¹ = 𝒢_ports`
  (`srec_portResolvent`; the top block
  `diag(A) - E - X` is a.s. invertible, `srec_ae_isUnit_top`: its determinant is a nonzero
  polynomial in the Gaussian block coordinates), so `d(X₊) = max_j |g_j - a|` with
  `g_j = W⁻¹ Tr(𝒢_ports)_{jj}`; the mean bound is `layerContraction_holds`, the fluctuation
  `‖ξ‖_p ≤ C√p/W` is the fluctuation clause of `traceMatrix_holds` with `D = Q_j`, `‖Q_j‖ ≤ 1`.
* The exit field (the scalar exit bound): with `δ = (1-q)d'/2` and `C W⁻² ≤ δ`, the exit event is
  contained in
  `{d(X_{r₀}) > d'} ∪ ⋃_{j<L} {d(X_j) ≤ d₀, d(X_{j+1}) > q d(X_j) + C W⁻² + δ}`. Each step event
  has probability `≤ (C√p/(Wδ))^p` (Markov for the excess, conditional on the old path through
  `(ω_j, pgPath ω j) ~ layerLaw ⊗ pathLaw (r₀+2j)`, `srec_mp_layerPath`); the core event is
  bounded by Markov and `CoreTraceBound`. With `p = εW` and the union bound over `L ≤ TW` steps,
  `≤ (TW + 1)(K√ε/√W)^{εW} ≤ exp(-(ε/8) W log W)` for `W ≥ W₀`.

`CoreTraceBound` is the `r ∈ {1,2}` clause (Steps 1–2) of `MatchedTracesContract.path`, an
explicit hypothesis here (it is proved by `coreTraces_holds`). The other inputs are
`ConditionalBlockGUECount` and `GaussianLpGradient` (through `layerContraction_holds`,
`traceMatrix_holds`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- **Core trace bound** (Steps 1–2 of the proof of the matched-traces theorem):
the clause `MatchedTracesContract.path` restricted to the one- and two-block cores `r ∈ {1,2}`. -/
def CoreTraceBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
      ∀ r : ℕ, (r = 1 ∨ r = 2) → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
            ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖)
          (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W)

/-!
## 1. Almost-sure invertibility of the layer top block
-/

/-- `blockDiag A + N` as a matrix of polynomials in the flat block coordinates. -/
def srecTopPoly (W k : ℕ) (t : ℝ≥0) (N : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) (MvPolynomial (Fin k × GaussCoord W) ℂ) :=
  fun p q => (if p.1 = q.1 then pgGuePoly W k t p.1 p.2 q.2 else 0) + MvPolynomial.C (N p q)

theorem srec_eval_det_topPoly (W k : ℕ) (t : ℝ≥0) (N : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)
    (x : Fin k × GaussCoord W → ℝ) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (srecTopPoly W k t N).det =
      (Internal.Contracts.Layers.blockDiag (pgBlocksOfCoords W k t x) + N).det := by
  rw [RingHom.map_det]
  congr 1
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [srecTopPoly, map_add, MvPolynomial.eval_C, Matrix.add_apply,
    Internal.Contracts.Layers.blockDiag]
  split_ifs with h
  · rw [eval_pgGuePoly]
  · simp

/-- For `t > 0` some block configuration makes `blockDiag A + N` invertible. -/
theorem srec_exists_det_ne_zero (W k : ℕ) {t : ℝ≥0} (ht : t ≠ 0)
    (N : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    ∃ x : Fin k × GaussCoord W → ℝ,
      (Internal.Contracts.Layers.blockDiag (pgBlocksOfCoords W k t x) + N).det ≠ 0 := by
  set c : ℂ := (Real.sqrt ((t : ℝ) / 2) : ℂ) * (2 / (Real.sqrt 2 : ℂ))
  have hc : c ≠ 0 := by
    have h1 : Real.sqrt ((t : ℝ) / 2) ≠ 0 := by
      have : (0 : ℝ) < (t : ℝ) / 2 := by
        have := (pos_iff_ne_zero.mpr ht : 0 < t); positivity
      exact (Real.sqrt_pos.mpr this).ne'
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    simp only [c]
    exact mul_ne_zero (by exact_mod_cast h1) (div_ne_zero two_ne_zero h2)
  have key : ∀ s : ℝ, (Internal.Contracts.Layers.blockDiag
      (pgBlocksOfCoords W k t (pgWitness W k s)) + N).det = (-N).charpoly.eval (c * s) := by
    intro s
    rw [eval_charpoly]
    congr 1
    ext p q
    simp only [Matrix.add_apply, Internal.Contracts.Layers.blockDiag, pgBlocksOfCoords_witness,
      Matrix.sub_apply, Matrix.neg_apply, sub_neg_eq_add, Matrix.scalar_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    by_cases h : p = q
    · subst h; simp [c]
    · have h2 : ¬ (p.1 = q.1 ∧ p.2 = q.2) := fun e => h (Prod.ext e.1 e.2)
      by_cases h1 : p.1 = q.1
      · have h3 : ¬ p.2 = q.2 := fun e => h2 ⟨h1, e⟩
        simp [h, h1, h3]
      · simp [h, h1]
  have hp : (-N).charpoly ≠ 0 := (charpoly_monic _).ne_zero
  have hfin : {s : ℝ | (-N).charpoly.IsRoot (c * s)}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hp).preimage fun a _ b _ hab => by
      have := mul_left_cancel₀ hc hab
      exact_mod_cast this
  obtain ⟨s, hs⟩ := hfin.exists_notMem
  exact ⟨pgWitness W k s, by rw [key]; exact hs⟩

theorem srec_continuous_blockDiag (k W : ℕ) :
    Continuous (fun A : Fin k → Matrix (Fin W) (Fin W) ℂ =>
      Internal.Contracts.Layers.blockDiag A) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  unfold Internal.Contracts.Layers.blockDiag
  split_ifs
  · fun_prop
  · fun_prop

/-- For `t > 0`, independent `GUE_W(t)` blocks make `blockDiag A + N` singular with probability
zero, for every fixed `N`. -/
theorem srec_pi_gue_det_null (W k : ℕ) {t : ℝ≥0} (ht : t ≠ 0)
    (N : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) :
    (Measure.pi fun _ : Fin k => gueMeasure (Fin W) t)
      {A | (Internal.Contracts.Layers.blockDiag A + N).det = 0} = 0 := by
  set Q := BlockBand.Parameters.mvPolynomialNormSq (srecTopPoly W k t N).det
  have hQx : ∀ x, MvPolynomial.eval x Q = Complex.normSq
      (Internal.Contracts.Layers.blockDiag (pgBlocksOfCoords W k t x) + N).det := by
    intro x
    rw [BlockBand.Parameters.eval_mvPolynomialNormSq, srec_eval_det_topPoly]
  have hQ : Q ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := srec_exists_det_ne_zero W k ht N
    have h := hQx x
    rw [h0, map_zero] at h
    exact hx (Complex.normSq_eq_zero.mp h.symm)
  have hnull := BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype Q hQ
  have hac := BlockBand.Parameters.pi_absolutelyContinuous_volume
    (fun _ : Fin k × GaussCoord W => gaussianReal 0 1)
    (fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero)
  have hmeasS : MeasurableSet {A : Fin k → Matrix (Fin W) (Fin W) ℂ |
      (Internal.Contracts.Layers.blockDiag A + N).det = 0} :=
    measurableSet_eq_fun ((continuous_id.matrix_det).measurable.comp
      ((srec_continuous_blockDiag k W).add continuous_const).measurable) measurable_const
  rw [pi_gueMeasure_eq_map, Measure.map_apply (measurable_pgBlocksOfCoords W k t) hmeasS]
  apply hac
  convert hnull using 2
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hQx, Complex.normSq_eq_zero]

/-- **A.s. invertibility of the top block** (`b < 1/2`): for every real `E` and every fixed `X`,
`diag(A) - E - X` is `layerLaw W b σ`-a.s. invertible. -/
theorem srec_ae_isUnit_top {W : ℕ} {b : ℝ} (hb : b < 1 / 2) (σ : LayerShape) (E : ℝ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) :
    ∀ᵐ ω ∂layerLaw W b σ,
      IsUnit (Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - X).det := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · exact Filter.Eventually.of_forall fun ω => by rw [Matrix.det_isEmpty]; exact isUnit_one
  have := fun t => isProbabilityMeasure_gueMeasure W t
  set t := Real.toNNReal ((1 - 2 * b) / W) with ht_def
  have ht : t ≠ 0 := by
    have hpos : (0 : ℝ) < (1 - 2 * b) / W := div_pos (by linarith) (by exact_mod_cast hW)
    exact (Real.toNNReal_pos.mpr hpos).ne'
  have hnull := srec_pi_gue_det_null W σ.blocks ht (-((E : ℂ) • 1) - X)
  rw [ae_iff]
  simp only [isUnit_iff_ne_zero, not_not]
  have hset : {ω : LayerSample W σ |
      (Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - X).det = 0} =
      {A : Fin σ.blocks → Matrix (Fin W) (Fin W) ℂ |
        (Internal.Contracts.Layers.blockDiag A + (-((E : ℂ) • 1) - X)).det = 0} ×ˢ Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
    rw [show Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - X =
      Internal.Contracts.Layers.blockDiag ω.1 + (-((E : ℂ) • 1) - X) by abel]
  rw [hset]
  unfold layerLaw
  rw [Measure.prod_prod, hnull, zero_mul]

/-!
## 2. The port identity `(z - X₊)⁻¹ = 𝒢_ports` and the distance of the new Schur matrix
-/

/-- **Port identity** (the `r`-independent layer version of `portResolvent_pgGrow`): if the top
block is invertible, `(z - X₊)⁻¹` is the port block of `𝒢`. -/
theorem srec_portResolvent {W : ℕ} (E : ℝ) (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .separate)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - X).det) :
    (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - layerSchur .separate E X ω)⁻¹ =
      (layerResolvent .separate E z X ω).toBlocks₂₂ := by
  rw [layerResolvent, layerMatrix, pg_toBlocks22_inv _ _ _ _ hS]
  rfl

/-- The port trace `g_j = W⁻¹ Tr(𝒢_ports)_{jj}` at `z = z_∂(E)`. -/
def srecPortTrace (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .separate) (j : Fin 2) : ℂ :=
  portBlockTrace (layerResolvent .separate E (boundaryZ b E) X ω) j

/-- The fresh fluctuation `ξ = max_j |g_j - E g_j|` of the one-step matched-trace recursion. -/
def srecXi (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .separate) : ℝ :=
  max ‖srecPortTrace b E X ω 0 - ∫ ω', srecPortTrace b E X ω' 0 ∂layerLaw W b .separate‖
    ‖srecPortTrace b E X ω 1 - ∫ ω', srecPortTrace b E X ω' 1 ∂layerLaw W b .separate‖

/-- `d(X₊) = max_j |g_j - a|` when the top block is invertible. -/
theorem srec_matchedDistance_layerSchur {W : ℕ} (b E : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : LayerSample W .separate)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - X).det) :
    matchedDistance b E (layerSchur .separate E X ω) =
      max ‖srecPortTrace b E X ω 0 - matchedA E‖ ‖srecPortTrace b E X ω 1 - matchedA E‖ := by
  unfold matchedDistance
  rw [srec_portResolvent E (boundaryZ b E) X ω hS]
  rfl

/-!
## 3. Measurability, Hermitian Schur matrices and the crude bound
-/

theorem srec_measurable_mul {Ω l m n : Type*} [MeasurableSpace Ω] [Fintype m]
    {f : Ω → Matrix l m ℂ} {g : Ω → Matrix m n ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun t => f t * g t) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => (pg_entry hf i k).mul (pg_entry hg k j)

theorem srec_measurable_conjTranspose {Ω m n : Type*} [MeasurableSpace Ω]
    {f : Ω → Matrix m n ℂ} (hf : Measurable f) : Measurable (fun t => (f t)ᴴ) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [conjTranspose_apply]
  exact continuous_star.measurable.comp (pg_entry hf j i)

theorem srec_measurable_blockTrace {Ω : Type*} [MeasurableSpace Ω] {k W : ℕ}
    {f : Ω → Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ} (hf : Measurable f) (j : Fin k) :
    Measurable (fun t => blockTrace (f t) j) := by
  unfold blockTrace
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ => pg_entry hf _ _)

/-- `X ↦ d(X)` is measurable. -/
theorem srec_measurable_matchedDistance (b E : ℝ) (W : ℕ) :
    Measurable (fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => matchedDistance b E X) := by
  have hR : Measurable (fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) :=
    measurable_matrix_inv.comp (continuous_const.sub continuous_id).measurable
  unfold matchedDistance
  exact (((srec_measurable_blockTrace hR 0).sub measurable_const).norm).max
    (((srec_measurable_blockTrace hR 1).sub measurable_const).norm)

/-- The layer Schur matrix is jointly measurable in `(X, ω)`. -/
theorem srec_measurable_layerSchur {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (E : ℝ)
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .separate}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => layerSchur .separate E (Xf t) (ℓf t)) := by
  have hB : Measurable (fun t => bondMatrix .separate (ℓf t).2) := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    unfold bondMatrix
    split_ifs
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp (measurable_snd.comp hℓ))))
    · exact measurable_const
  have hD : Measurable (fun t => Internal.Contracts.Layers.blockDiag (ℓf t).1) :=
    (srec_continuous_blockDiag 2 W).measurable.comp (measurable_fst.comp hℓ)
  have hM : Measurable (fun t => (Internal.Contracts.Layers.blockDiag (ℓf t).1 -
      (E : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Xf t)⁻¹) :=
    measurable_matrix_inv.comp ((hD.sub measurable_const).sub hX)
  exact srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hB) hM) hB

theorem srec_measurable_portTrace (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (j : Fin 2) : Measurable (fun ω => srecPortTrace b E X ω j) := by
  unfold srecPortTrace portBlockTrace
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ =>
    pg_entry (measurable_layerResolvent .separate E (boundaryZ b E) X) _ _)

theorem srec_measurable_xi (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (srecXi b E X) := by
  unfold srecXi
  exact (((srec_measurable_portTrace b E X 0).sub measurable_const).norm).max
    (((srec_measurable_portTrace b E X 1).sub measurable_const).norm)

/-- The path matrix is Hermitian when its blocks are. -/
theorem srec_pathMatrix_isHermitian {W r : ℕ} (ω : PathSample W r)
    (hA : ∀ j, (ω.1 j).IsHermitian) : (pathMatrix ω).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, pathMatrix]
  by_cases h : y.1 = x.1
  · have hx := (hA y.1).apply x.2 y.2
    simp only [h, ↓reduceIte] at hx ⊢
    exact hx
  have h' : ¬ x.1 = y.1 := Ne.symm h
  simp only [h, h', ↓reduceIte]
  by_cases h1 : y.1.val + 1 = x.1.val
  · have h1' : ¬ x.1.val + 1 = y.1.val := by omega
    simp only [h1, h1', ↓reduceDIte]
  by_cases h2 : x.1.val + 1 = y.1.val
  · simp only [h1, h2, ↓reduceDIte, star_star]
  simp only [h1, h2, ↓reduceDIte, star_zero]

/-- The path Schur matrix is Hermitian when the blocks are. -/
theorem srec_pathSchur_isHermitian {W r : ℕ} (E : ℝ) (ω : PathSample W r)
    (hA : ∀ j, (ω.1 j).IsHermitian) : (pathSchur E ω).IsHermitian := by
  have hH : (pathMatrix ω - (E : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)).IsHermitian := by
    refine (srec_pathMatrix_isHermitian ω hA).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  exact isHermitian_conjTranspose_mul_mul _ hH.inv

/-- `pathLaw`-a.s. the path Schur matrix is Hermitian. -/
theorem srec_ae_pathSchur_isHermitian (W r : ℕ) (b E : ℝ) :
    ∀ᵐ ω ∂pathLaw W r b, (pathSchur E ω).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have h := ae_blocks_isHermitian r W (Real.toNNReal ((1 - 2 * b) / W))
  unfold pathLaw
  filter_upwards [(Measure.quasiMeasurePreserving_fst).ae h] with ω hω
  exact srec_pathSchur_isHermitian E ω hω

/-- The layer Schur matrix is Hermitian for Hermitian blocks and Hermitian `X`. -/
theorem srec_layerSchur_isHermitian {W : ℕ} (E : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (ω : LayerSample W .separate) (hA : ∀ j, (ω.1 j).IsHermitian) :
    (layerSchur .separate E X ω).IsHermitian := by
  have hD : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian := blockDiag_isHermitian hA
  have hM := layerDiag_isHermitian (σ := .separate) E X hX ω hD
  exact isHermitian_conjTranspose_mul_mul (bondMatrix .separate ω.2) hM.inv

/-- **Crude bound**: for Hermitian `X` and `Im z > 0`,
`d(X) ≤ (Im z)⁻¹ + 1`. -/
theorem srec_matchedDistance_le {W : ℕ} {b E : ℝ} (hE : |E| ≤ 2) (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    matchedDistance b E X ≤ ((boundaryZ b E).im)⁻¹ + 1 := by
  have heq : boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X =
      -X - diagonal (fun _ => -boundaryZ b E) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.neg_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp; ring
  have hinv : ‖(boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹‖ ≤
      ((boundaryZ b E).im)⁻¹ := by
    rw [heq]
    exact lct_norm_shifted_inv_le (-X) hX.neg _ hz fun _ => by simp
  have ha := norm_matchedA (E := E) hE
  have hi : ∀ i : Fin 2, ‖blockTrace ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      - X)⁻¹) i - matchedA E‖ ≤ ((boundaryZ b E).im)⁻¹ + 1 := fun i =>
    (norm_sub_le _ _).trans (by rw [ha]; linarith [(lct_norm_blockTrace_le _ i).trans hinv])
  exact max_le (hi 0) (hi 1)

/-!
## 4. One step of the recursion (the one-step matched-trace recursion)
-/

/-- A uniform lower bound `η ≤ Im z_∂(E)` on `bulkInterval κ` (`b < 1`). -/
theorem srec_boundaryZ_im_lower {b κ : ℝ} (hb : b < 1) (hκ : 0 < κ) :
    ∃ η : ℝ, 0 < η ∧ ∀ E ∈ bulkInterval κ, η ≤ (boundaryZ b E).im ∧ |E| ≤ 2 := by
  by_cases h : (bulkInterval κ).Nonempty
  · obtain ⟨E₀, hE₀⟩ := h
    exact ⟨_, (boundaryZ_im_pos_of_mem_bulkInterval hb hκ hE₀).1, fun E hE =>
      ⟨(boundaryZ_im_pos_of_mem_bulkInterval hb hκ hE).2, (abs_lt_two_of_mem_bulkInterval hκ hE).le⟩⟩
  · exact ⟨1, one_pos, fun E hE => absurd ⟨E, hE⟩ h⟩

/-- **One step, internal form** (the one-step matched-trace recursion, with `q ≥ 0` and `C ≥ 0` recorded). -/
theorem srec_oneStep_core (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ d₀ q C ε : ℝ, 0 < d₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ 0 < ε ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ,
        (matchedDistance b E X ≤ d₀ → ∀ᵐ ω ∂layerLaw W b .separate,
          matchedDistance b E (layerSchur .separate E X ω) ≤
            q * matchedDistance b E X + C / (W : ℝ) ^ 2 + srecXi b E X ω) ∧
        ∀ p : ℝ, 2 ≤ p → p ≤ ε * W →
          eLpNorm (srecXi b E X) (ENNReal.ofReal p) (layerLaw W b .separate) ≤
            ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨dstar, Cl, qstar, hds, hq0, hq1, hcon⟩ := layerContraction_holds hcount b hb0 hb1 κ hκ
  obtain ⟨η, hη, hηE⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  obtain ⟨ε₃, Cf, hε₃, hfl⟩ := (traceMatrix_holds hcount hgrad).fluctuation b hb0 hb1 η 3 hη 1
  set C := max (max Cl 0) (2 * max Cf 0) with hCdef
  have hC0 : 0 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨dstar, qstar, C, ε₃, hds, hq0, hq1, hC0, hε₃, ?_⟩
  intro W hW X hX E hE
  obtain ⟨hzη, hEabs⟩ := hηE E hE
  have hz3 : ‖boundaryZ b E‖ ≤ 3 := norm_boundaryZ_le hb0.le (by linarith) hEabs
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  constructor
  · intro hd
    have hmean := (hcon W hW X hX E hE hd).1
    filter_upwards [srec_ae_isUnit_top hb1 .separate E X] with ω hS
    rw [srec_matchedDistance_layerSchur b E X ω hS]
    have hCl : Cl / (W : ℝ) ^ 2 ≤ C / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)
    have key : ∀ j : Fin 2, ‖srecPortTrace b E X ω j -
        ∫ ω', srecPortTrace b E X ω' j ∂layerLaw W b .separate‖ ≤ srecXi b E X ω →
        ‖srecPortTrace b E X ω j - matchedA E‖ ≤
          qstar * matchedDistance b E X + C / (W : ℝ) ^ 2 + srecXi b E X ω := by
      intro j hj
      have h2 := hmean j
      calc ‖srecPortTrace b E X ω j - matchedA E‖
          ≤ ‖srecPortTrace b E X ω j - ∫ ω', srecPortTrace b E X ω' j ∂layerLaw W b .separate‖ +
            ‖(∫ ω', srecPortTrace b E X ω' j ∂layerLaw W b .separate) - matchedA E‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ srecXi b E X ω + (qstar * matchedDistance b E X + Cl / (W : ℝ) ^ 2) :=
            add_le_add hj h2
        _ ≤ qstar * matchedDistance b E X + C / (W : ℝ) ^ 2 + srecXi b E X ω := by linarith
    exact max_le (key 0 (le_max_left _ _)) (key 1 (le_max_right _ _))
  · intro p hp2 hpε
    have hfj : ∀ j : Fin 2, eLpNorm (fun ω => srecPortTrace b E X ω j -
        ∫ ω', srecPortTrace b E X ω' j ∂layerLaw W b .separate) (ENNReal.ofReal p)
        (layerLaw W b .separate) ≤ ENNReal.ofReal (max Cf 0 * Real.sqrt p / W) := by
      intro j
      have h := hfl W hW .separate X hX E (boundaryZ b E) hzη hz3 (meqPortProj (W := W) (σ := .separate) j)
        (meq_norm_portProj_le (W := W) (σ := .separate) j) p hp2 hpε
      have hpt : ∀ ω, srecPortTrace b E X ω j = (W : ℂ)⁻¹ *
          (meqPortProj (W := W) (σ := .separate) j *
            layerResolvent .separate E (boundaryZ b E) X ω).trace := fun ω =>
        lct_port_eq_trace (W := W) (σ := .separate) _ j
      simp only [hpt]
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.sqrt_nonneg _)) hW0.le
    have hu : ∀ j : Fin 2, Measurable (fun ω => srecPortTrace b E X ω j -
        ∫ ω', srecPortTrace b E X ω' j ∂layerLaw W b .separate) := fun j =>
      (srec_measurable_portTrace b E X j).sub measurable_const
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
    have hB0 : 0 ≤ max Cf 0 * Real.sqrt p / W := by positivity
    calc eLpNorm (srecXi b E X) (ENNReal.ofReal p) (layerLaw W b .separate)
        ≤ eLpNorm (fun ω => ‖srecPortTrace b E X ω 0 -
              ∫ ω', srecPortTrace b E X ω' 0 ∂layerLaw W b .separate‖ +
            ‖srecPortTrace b E X ω 1 - ∫ ω', srecPortTrace b E X ω' 1 ∂layerLaw W b .separate‖)
            (ENNReal.ofReal p) (layerLaw W b .separate) := by
          refine eLpNorm_mono_real (srec_measurable_xi b E X).aestronglyMeasurable fun ω => ?_
          have h0 : 0 ≤ srecXi b E X ω := (norm_nonneg _).trans (le_max_left _ _)
          rw [Real.norm_of_nonneg h0]
          exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ eLpNorm (fun ω => ‖srecPortTrace b E X ω 0 -
              ∫ ω', srecPortTrace b E X ω' 0 ∂layerLaw W b .separate‖) (ENNReal.ofReal p)
              (layerLaw W b .separate) +
            eLpNorm (fun ω => ‖srecPortTrace b E X ω 1 -
              ∫ ω', srecPortTrace b E X ω' 1 ∂layerLaw W b .separate‖) (ENNReal.ofReal p)
              (layerLaw W b .separate) := eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (max Cf 0 * Real.sqrt p / W) +
            ENNReal.ofReal (max Cf 0 * Real.sqrt p / W) := by
          rw [eLpNorm_norm _ (hu 0).aestronglyMeasurable,
            eLpNorm_norm _ (hu 1).aestronglyMeasurable]
          exact add_le_add (hfj 0) (hfj 1)
      _ ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
          rw [← ENNReal.ofReal_add hB0 hB0]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : 2 * max Cf 0 ≤ C := le_max_right _ _
          have : max Cf 0 * Real.sqrt p / W + max Cf 0 * Real.sqrt p / W =
              (2 * max Cf 0) * Real.sqrt p / W := by ring
          rw [this]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))
            hW0.le

/-- The excess `(d(Y) - q d(X) - C W⁻²)₊` of one step on `{d(X) ≤ d₀}` (zero off it). -/
def srecExcess (b E q C d₀ : ℝ) (W : ℕ) (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  if matchedDistance b E X ≤ d₀ then
    max (matchedDistance b E Y - q * matchedDistance b E X - C / (W : ℝ) ^ 2) 0
  else 0

theorem srec_excess_nonneg (b E q C d₀ : ℝ) (W : ℕ)
    (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : 0 ≤ srecExcess b E q C d₀ W X Y := by
  unfold srecExcess
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem srec_measurable_excess (b E q C d₀ : ℝ) (W : ℕ) :
    Measurable (fun P : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => srecExcess b E q C d₀ W P.1 P.2) := by
  have hd := srec_measurable_matchedDistance b E W
  unfold srecExcess
  refine Measurable.ite (measurableSet_le (hd.comp measurable_fst) measurable_const) ?_
    measurable_const
  exact ((((hd.comp measurable_snd).sub (measurable_const.mul (hd.comp measurable_fst))).sub
    measurable_const).max measurable_const)

/-- **Excess moments**: for every deterministic Hermitian `X` (any `d(X)`), the one-step excess
has `‖·‖_p ≤ C √p / W` under the fresh layer. -/
theorem srec_excess_core (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ d₀ q C ε : ℝ, 0 < d₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ 0 < ε ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, ∀ p : ℝ, 2 ≤ p → p ≤ ε * W →
        eLpNorm (fun ω => srecExcess b E q C d₀ W X (layerSchur .separate E X ω))
          (ENNReal.ofReal p) (layerLaw W b .separate) ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨d₀, q, C, ε, hd₀, hq0, hq1, hC0, hε, hstep⟩ := srec_oneStep_core hcount hgrad b hb0 hb1 κ hκ
  refine ⟨d₀, q, C, ε, hd₀, hq0, hq1, hC0, hε, ?_⟩
  intro W hW X hX E hE p hp2 hpε
  obtain ⟨has, hxi⟩ := hstep W hW X hX E hE
  by_cases hd : matchedDistance b E X ≤ d₀
  · have hS : Measurable (fun ω : LayerSample W .separate => layerSchur .separate E X ω) :=
      srec_measurable_layerSchur (Xf := fun _ : LayerSample W .separate => X) (ℓf := id) E
        measurable_const measurable_id
    have hmeas : Measurable (fun ω => srecExcess b E q C d₀ W X (layerSchur .separate E X ω)) := by
      simp only [srecExcess, hd, ↓reduceIte]
      exact ((((srec_measurable_matchedDistance b E W).comp hS).sub measurable_const).sub
        measurable_const).max measurable_const
    refine (eLpNorm_mono_ae_real hmeas.aestronglyMeasurable ?_).trans (hxi p hp2 hpε)
    filter_upwards [has hd] with ω hω
    rw [Real.norm_of_nonneg (srec_excess_nonneg _ _ _ _ _ _ _ _)]
    simp only [srecExcess, hd, ↓reduceIte]
    have h0 : 0 ≤ srecXi b E X ω := (norm_nonneg _).trans (le_max_left _ _)
    exact max_le (by linarith) h0
  · have h0 : (fun ω => srecExcess b E q C d₀ W X (layerSchur .separate E X ω)) = fun _ => 0 := by
      funext ω; simp only [srecExcess, hd, ↓reduceIte]
    rw [h0]
    simp

/-!
## 5. Markov's inequality and conditional moments on a product
-/

/-- Markov's inequality with the `p`-th moment: `μ(f ≥ δ) ≤ (B/δ)^p` when `‖f‖_p ≤ B`. -/
theorem srec_markov {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ} {p B δ : ℝ}
    (hp : 0 < p) (hB : 0 ≤ B) (hδ : 0 < δ)
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B) :
    μ {ω | δ ≤ f ω} ≤ ENNReal.ofReal ((B / δ) ^ p) := by
  have hsub : {ω | δ ≤ f ω} ⊆ {ω | ENNReal.ofReal δ ≤ ‖f ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hω.trans (le_abs_self _))
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hδ0 : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
  have hM := meas_ge_le_mul_pow_eLpNorm_enorm μ hp0 ENNReal.ofReal_ne_top (f := f) hδ0
    (fun h => absurd h ENNReal.ofReal_ne_top)
  rw [ENNReal.toReal_ofReal hp.le] at hM
  refine (measure_mono hsub).trans (hM.trans ?_)
  calc (ENNReal.ofReal δ)⁻¹ ^ p * eLpNorm f (ENNReal.ofReal p) μ ^ p
      ≤ (ENNReal.ofReal δ)⁻¹ ^ p * (ENNReal.ofReal B) ^ p :=
        by gcongr
    _ = ENNReal.ofReal ((B / δ) ^ p) := by
        rw [← ENNReal.ofReal_inv_of_pos hδ,
          ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hδ.le) hp.le,
          ENNReal.ofReal_rpow_of_nonneg hB hp.le, ← ENNReal.ofReal_mul (by positivity),
          div_eq_mul_inv, Real.mul_rpow hB (inv_nonneg.mpr hδ.le), mul_comm]

/-- **Conditional moments on a product** (Fubini): if every section `x ↦ F(x, y)` has
`‖·‖_p ≤ B` for a.e. `y`, then `‖F‖_p ≤ B` under `μ ⊗ ν`, `ν` a probability measure. -/
theorem srec_eLpNorm_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν] {F : α × β → ℝ}
    (hF : Measurable F) {p B : ℝ} (hp : 0 < p)
    (h : ∀ᵐ y ∂ν, eLpNorm (fun x => F (x, y)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B) :
    eLpNorm F (ENNReal.ofReal p) (μ.prod ν) ≤ ENNReal.ofReal B := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  have hint : ∀ᵐ y ∂ν, ∫⁻ x, ‖F (x, y)‖ₑ ^ p ∂μ ≤ ENNReal.ofReal B ^ p := by
    filter_upwards [h] with y hy
    have hFy : Measurable (fun x => F (x, y)) := hF.comp (measurable_id.prodMk measurable_const)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hFy.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp.le] at hy
    have := ENNReal.rpow_le_rpow hy hp.le
    rwa [one_div, ENNReal.rpow_inv_rpow hp.ne'] at this
  rw [lintegral_prod_symm _ ((hF.enorm.pow_const p).aemeasurable)]
  calc (∫⁻ y, ∫⁻ x, ‖F (x, y)‖ₑ ^ p ∂μ ∂ν) ^ (1 / p)
      ≤ (∫⁻ _y, ENNReal.ofReal B ^ p ∂ν) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hint) (by positivity)
    _ = ENNReal.ofReal B := by
        rw [lintegral_const, measure_univ, mul_one, one_div, ENNReal.rpow_rpow_inv hp.ne']

/-!
## 6. The layer and the old path along the growth are independent
-/

/-- For `j < L`, `(ω_j, pgPath ω j)` is distributed as `layerLaw ⊗ pathLaw (r₀ + 2j)` under
`growthLaw W r₀ L b`: the fresh layer `j` is independent of the old path. -/
theorem srec_mp_layerPath {W r₀ : ℕ} (b : ℝ) (hr₀ : 1 ≤ r₀) :
    ∀ L j (hj : j < L), MeasurePreserving
      (fun ω : GrowthSample W r₀ L => (ω.2 ⟨j, hj⟩, pgPath ω j))
      (growthLaw W r₀ L b) ((layerLaw W b .separate).prod (pathLaw W (r₀ + 2 * j) b))
  | 0, j, hj => absurd hj (Nat.not_lt_zero _)
  | L + 1, j, hj => by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    have hT := pg_mp_splitLast W r₀ L b
    rcases Nat.lt_or_ge j L with hjL | hjL
    · have hP := srec_mp_layerPath (W := W) b hr₀ L j hjL
      have h := (hP.comp (measurePreserving_fst (μ := growthLaw W r₀ L b)
        (ν := layerLaw W b .separate))).comp hT
      convert h using 1
      funext ω
      simp only [Function.comp_apply]
      rw [pgPath_pgTrunc ω j hjL.le]
      rfl
    · obtain rfl : j = L := by omega
      have hP := measurePreserving_pgPath (W := W) b hr₀ j j le_rfl
      have h := (Measure.measurePreserving_swap.comp
        (hP.prod (MeasurePreserving.id (layerLaw W b .separate)))).comp hT
      convert h using 1
      funext ω
      simp only [Function.comp_apply, Prod.map, Prod.swap, id]
      rw [pgPath_pgTrunc ω j le_rfl]
      rfl

/-!
## 7. The bad-step probability
-/

theorem srec_measurable_excess_comp {W r : ℕ} (b E q C d₀ : ℝ) :
    Measurable (fun x : LayerSample W .separate × PathSample W r =>
      srecExcess b E q C d₀ W (pathSchur E x.2) (layerSchur .separate E (pathSchur E x.2) x.1)) := by
  have hX : Measurable (fun x : LayerSample W .separate × PathSample W r => pathSchur E x.2) :=
    (measurable_pathSchur W r E).comp measurable_snd
  have hY : Measurable (fun x : LayerSample W .separate × PathSample W r =>
      layerSchur .separate E (pathSchur E x.2) x.1) := srec_measurable_layerSchur E hX measurable_fst
  have hd := srec_measurable_matchedDistance b E W
  unfold srecExcess
  refine Measurable.ite (measurableSet_le (hd.comp hX) measurable_const) ?_ measurable_const
  exact ((((hd.comp hY).sub (measurable_const.mul (hd.comp hX))).sub
    measurable_const).max measurable_const)

/-- **Bad step, conditional on the old path**: under `layerLaw ⊗ pathLaw r`, the excess of the
step from the path `X_r` exceeds `δ` with probability `≤ (C√p/(Wδ))^p`. -/
theorem srec_badStep_le (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ d₀ q C ε : ℝ, 0 < d₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ 0 < ε ∧
      ∀ (W : ℕ), 0 < W → ∀ (r : ℕ), ∀ E ∈ bulkInterval κ, ∀ δ : ℝ, 0 < δ →
      ∀ p : ℝ, 2 ≤ p → p ≤ ε * W →
        ((layerLaw W b .separate).prod (pathLaw W r b))
          {x | δ ≤ srecExcess b E q C d₀ W (pathSchur E x.2)
            (layerSchur .separate E (pathSchur E x.2) x.1)} ≤
          ENNReal.ofReal ((C * Real.sqrt p / W / δ) ^ p) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨d₀, q, C, ε, hd₀, hq0, hq1, hC0, hε, hex⟩ := srec_excess_core hcount hgrad b hb0 hb1 κ hκ
  refine ⟨d₀, q, C, ε, hd₀, hq0, hq1, hC0, hε, ?_⟩
  intro W hW r E hE δ hδ p hp2 hpε
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have hS : MeasurableSet {x : LayerSample W .separate × PathSample W r | δ ≤ srecExcess b E q C d₀ W
      (pathSchur E x.2) (layerSchur .separate E (pathSchur E x.2) x.1)} :=
    measurableSet_le measurable_const (srec_measurable_excess_comp b E q C d₀)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Measure.prod_apply_symm hS]
  have hpw : IsProbabilityMeasure (pathLaw W r b) := by unfold pathLaw; infer_instance
  calc ∫⁻ y, layerLaw W b .separate ((fun x => (x, y)) ⁻¹' {x : LayerSample W .separate ×
        PathSample W r | δ ≤ srecExcess b E q C d₀ W (pathSchur E x.2)
          (layerSchur .separate E (pathSchur E x.2) x.1)}) ∂pathLaw W r b
      ≤ ∫⁻ _y, ENNReal.ofReal ((C * Real.sqrt p / W / δ) ^ p) ∂pathLaw W r b := by
        refine lintegral_mono_ae ?_
        filter_upwards [srec_ae_pathSchur_isHermitian W r b E] with y hy
        exact srec_markov (by linarith) (by positivity) hδ
          (hex W hW (pathSchur E y) hy E hE p hp2 hpε)
    _ = ENNReal.ofReal ((C * Real.sqrt p / W / δ) ^ p) := by
        rw [lintegral_const, measure_univ, mul_one]

/-!
## 8. The exit bound (the scalar exit bound)
-/

/-- **Exit arithmetic**: with `p = εW`, the union bound over `L ≤ TW` steps
is `(L + 1)(K√p/W)^p ≤ exp(-(ε/8) W log W)` for `W ≥ W₀(K, ε, T)`; also `p ≥ 2`. -/
theorem srec_exit_arith {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (T : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → 0 < W → 2 ≤ ε * W ∧ ∀ L : ℕ, (L : ℝ) ≤ T * W →
      ((L : ℝ) + 1) * (K * Real.sqrt (ε * W) / W) ^ (ε * W) ≤
        Real.exp (-(ε / 8 * W * Real.log W)) := by
  set A := K * Real.sqrt ε with hA
  have hA0 : 0 < A := mul_pos hK (Real.sqrt_pos.mpr hε)
  set M := 8 / (3 * ε) * (|T| + ε * |Real.log A|) with hM
  refine ⟨⌈Real.exp M⌉₊ + ⌈2 / ε⌉₊ + 1, fun W hW hW0 => ?_⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hWge : (⌈Real.exp M⌉₊ : ℝ) + ⌈2 / ε⌉₊ + 1 ≤ W := by exact_mod_cast hW
  have h1 : Real.exp M ≤ W := (Nat.le_ceil _).trans (by linarith [Nat.cast_nonneg (α := ℝ) ⌈2 / ε⌉₊])
  have h2 : 2 / ε ≤ W := (Nat.le_ceil _).trans (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Real.exp M⌉₊])
  refine ⟨?_, fun L hL => ?_⟩
  · have := mul_le_mul_of_nonneg_left h2 hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have hlogW : M ≤ Real.log W := (Real.le_log_iff_exp_le hWr).mpr h1
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWr
  have hbase : K * Real.sqrt (ε * W) / W = A / Real.sqrt W := by
    rw [Real.sqrt_mul hε.le, hA, div_eq_div_iff hWr.ne' hsW.ne']
    linear_combination (K * Real.sqrt ε) * Real.mul_self_sqrt hWr.le
  have hlog : Real.log (A / Real.sqrt W) = Real.log A - Real.log W / 2 := by
    rw [Real.log_div hA0.ne' hsW.ne', Real.log_sqrt hWr.le]
  rw [hbase, Real.rpow_def_of_pos (div_pos hA0 hsW), hlog]
  have hL1 : (L : ℝ) + 1 ≤ Real.exp (T * W) :=
    (Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr hL)
  calc ((L : ℝ) + 1) * Real.exp ((Real.log A - Real.log W / 2) * (ε * W))
      ≤ Real.exp (T * W) * Real.exp ((Real.log A - Real.log W / 2) * (ε * W)) :=
        mul_le_mul_of_nonneg_right hL1 (Real.exp_pos _).le
    _ = Real.exp (T * W + (Real.log A - Real.log W / 2) * (ε * W)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(ε / 8 * W * Real.log W)) := by
        refine Real.exp_le_exp.mpr ?_
        have hT : T ≤ |T| := le_abs_self T
        have hLA : Real.log A ≤ |Real.log A| := le_abs_self _
        have hkey : T + ε * Real.log A ≤ 3 * ε / 8 * Real.log W := by
          have h3 : 3 * ε / 8 * M = |T| + ε * |Real.log A| := by
            rw [hM]; field_simp
          have h4 : 3 * ε / 8 * M ≤ 3 * ε / 8 * Real.log W :=
            mul_le_mul_of_nonneg_left hlogW (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hLA hε.le]
        have : T * W + (Real.log A - Real.log W / 2) * (ε * W) + ε / 8 * W * Real.log W =
            W * (T + ε * Real.log A - 3 * ε / 8 * Real.log W) := by ring
        nlinarith [mul_nonneg hWr.le (by linarith : (0 : ℝ) ≤ 3 * ε / 8 * Real.log W -
          (T + ε * Real.log A))]

/-- **The scalar exit bound**, internal form (the `exit` field of `ScalarRecursionContract`). -/
theorem srec_exit_core (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) (hcore : CoreTraceBound) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d' : ℝ, 0 < d' → d' ≤ d₀ →
      ∃ (c : ℝ) (W₀ : ℕ), 0 < c ∧ ∀ (W : ℕ), W₀ ≤ W → 0 < W →
      ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ L : ℕ, ((r₀ + 2 * L : ℕ) : ℝ) ≤ T * W →
      ∀ E ∈ bulkInterval κ,
        growthLaw W r₀ L b {ω | ∃ k ≤ L, d' < matchedDistance b E (grownSchur E ω k)} ≤
          ENNReal.ofReal (Real.exp (-(c * W * Real.log W))) := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨d₀, q, C, ε, hd₀, hq0, hq1, hC0, hε, hbad⟩ := srec_badStep_le hcount hgrad b hb0 hb1 κ hκ
  obtain ⟨εc, Cc, hεc, hcb⟩ := hcore b hb0 hb1 κ hκ
  refine ⟨d₀, hd₀, fun d' hd' hd'd₀ => ?_⟩
  set δ := (1 - q) * d' / 2 with hδdef
  have hδ : 0 < δ := by
    have h1q : 0 < 1 - q := by linarith
    positivity
  set ε' := min ε εc with hε'def
  have hε' : 0 < ε' := lt_min hε hεc
  set Cc' := max Cc 0 with hCc'
  set K := max (max (C / δ) (Cc' / d')) 1 with hKdef
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨W₁, hW₁⟩ := srec_exit_arith hK hε' T
  refine ⟨ε' / 8, max W₁ (⌈C / δ⌉₊ + 1), by positivity, ?_⟩
  intro W hW hW0 r₀ hr₀ L hL E hE
  have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  obtain ⟨hp2, harith⟩ := hW₁ W (le_of_max_le_left hW) hW0
  set p := ε' * W with hpdef
  have hp0 : 0 < p := by linarith
  have hpc : p ≤ εc * W := mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le
  have hpe : p ≤ ε * W := mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le
  have hLT : (L : ℝ) ≤ T * W := by
    refine le_trans ?_ hL
    exact_mod_cast (by omega : L ≤ r₀ + 2 * L)
  -- `C W⁻² ≤ δ`
  have hCW : C / (W : ℝ) ^ 2 ≤ δ := by
    have hW2 : ((⌈C / δ⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
    have h3 : C / δ ≤ W := (Nat.le_ceil _).trans (by push_cast at hW2; linarith)
    have h4 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hδ).mp h3
    nlinarith
  -- the deterministic inclusion
  set Bad : ℕ → Set (GrowthSample W r₀ L) := fun j =>
    {ω | δ ≤ srecExcess b E q C d₀ W (grownSchur E ω j) (grownSchur E ω (j + 1))} with hBad
  have hincl : {ω : GrowthSample W r₀ L | ∃ k ≤ L, d' < matchedDistance b E (grownSchur E ω k)} ⊆
      {ω | d' < matchedDistance b E (grownSchur E ω 0)} ∪ ⋃ j ∈ Finset.range L, Bad j := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, not_or, not_exists,
      Set.mem_ofPred_eq, not_lt] at hno
    obtain ⟨h0, hj⟩ := hno
    have hall : ∀ k, k ≤ L → matchedDistance b E (grownSchur E ω k) ≤ d' := by
      intro k
      induction k with
      | zero => exact fun _ => h0
      | succ k ih =>
        intro hk
        have hdk := ih (by omega)
        have hbk := hj k (by omega)
        simp only [hBad, Set.mem_ofPred_eq, srecExcess, hdk.trans hd'd₀, ↓reduceIte, not_le,
          max_lt_iff] at hbk
        have := hbk.1
        have hqd : q * matchedDistance b E (grownSchur E ω k) ≤ q * d' :=
          mul_le_mul_of_nonneg_left hdk hq0
        nlinarith
    obtain ⟨k, hk, hlt⟩ := hω
    exact absurd (hall k hk) (not_le.mpr hlt)
  -- the core event
  have hcoreE : growthLaw W r₀ L b {ω | d' < matchedDistance b E (grownSchur E ω 0)} ≤
      ENNReal.ofReal ((K * Real.sqrt p / W) ^ p) := by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    have hset : {ω : GrowthSample W r₀ L | d' < matchedDistance b E (grownSchur E ω 0)} =
        Prod.fst ⁻¹' {y : PathSample W r₀ | d' < matchedDistance b E (pathSchur E y)} := rfl
    have hmeas : MeasurableSet {y : PathSample W r₀ | d' < matchedDistance b E (pathSchur E y)} :=
      measurableSet_lt measurable_const
        ((srec_measurable_matchedDistance b E W).comp (measurable_pathSchur W r₀ E))
    rw [hset]
    unfold growthLaw
    rw [(measurePreserving_fst).measure_preimage hmeas.nullMeasurableSet]
    have hcb' := hcb W hW0 p hp2 hpc r₀ hr₀ E hE
    have hcb'' : eLpNorm (fun y : PathSample W r₀ => matchedDistance b E (pathSchur E y))
        (ENNReal.ofReal p) (pathLaw W r₀ b) ≤ ENNReal.ofReal (Cc' * Real.sqrt p / W) :=
      hcb'.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)) hWr.le))
    have hsub : {y : PathSample W r₀ | d' < matchedDistance b E (pathSchur E y)} ⊆
        {y | d' ≤ matchedDistance b E (pathSchur E y)} := fun y hy => by
      simp only [Set.mem_ofPred_eq] at hy ⊢; exact le_of_lt hy
    refine (measure_mono hsub).trans
      ((srec_markov hp0 (by positivity) hd' hcb'').trans (ENNReal.ofReal_le_ofReal ?_))
    refine Real.rpow_le_rpow (by positivity) ?_ hp0.le
    rw [show Cc' * Real.sqrt p / W / d' = Cc' / d' * (Real.sqrt p / W) by ring,
      show K * Real.sqrt p / W = K * (Real.sqrt p / W) by ring]
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)
  -- the step events
  have hstepE : ∀ j ∈ Finset.range L, growthLaw W r₀ L b (Bad j) ≤
      ENNReal.ofReal ((K * Real.sqrt p / W) ^ p) := by
    intro j hj
    have hjL : j < L := Finset.mem_range.mp hj
    have hMP := srec_mp_layerPath (W := W) b hr₀1 L j hjL
    set S := {x : LayerSample W .separate × PathSample W (r₀ + 2 * j) | δ ≤ srecExcess b E q C d₀ W
      (pathSchur E x.2) (layerSchur .separate E (pathSchur E x.2) x.1)} with hSdef
    have hSm : MeasurableSet S := measurableSet_le measurable_const (srec_measurable_excess_comp b E q C d₀)
    have hae : Bad j ≤ᵐ[growthLaw W r₀ L b]
        (fun ω : GrowthSample W r₀ L => (ω.2 ⟨j, hjL⟩, pgPath ω j)) ⁻¹' S := by
      filter_upwards [ae_grownSchur_eq_pathSchur_of_lt hb1 E hr₀1 hjL.le] with ω hω
      intro hb
      have hsucc : grownSchur E ω (j + 1) = layerSchur .separate E (grownSchur E ω j) (ω.2 ⟨j, hjL⟩) := by
        simp only [grownSchur, hjL, ↓reduceDIte]
      simp only [hBad, Set.mem_ofPred_eq, hsucc, hω] at hb
      exact hb
    refine (measure_mono_ae hae).trans ?_
    rw [hMP.measure_preimage hSm.nullMeasurableSet]
    refine (hbad W hW0 (r₀ + 2 * j) E hE δ hδ p hp2 hpe).trans (ENNReal.ofReal_le_ofReal ?_)
    refine Real.rpow_le_rpow (by positivity) ?_ hp0.le
    rw [show C * Real.sqrt p / W / δ = C / δ * (Real.sqrt p / W) by ring,
      show K * Real.sqrt p / W = K * (Real.sqrt p / W) by ring]
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)
  -- union bound
  have ht0 : 0 ≤ (K * Real.sqrt p / W) ^ p := by positivity
  calc growthLaw W r₀ L b {ω | ∃ k ≤ L, d' < matchedDistance b E (grownSchur E ω k)}
      ≤ growthLaw W r₀ L b ({ω | d' < matchedDistance b E (grownSchur E ω 0)} ∪
          ⋃ j ∈ Finset.range L, Bad j) := measure_mono hincl
    _ ≤ growthLaw W r₀ L b {ω | d' < matchedDistance b E (grownSchur E ω 0)} +
          ∑ j ∈ Finset.range L, growthLaw W r₀ L b (Bad j) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal ((K * Real.sqrt p / W) ^ p) +
          ∑ _j ∈ Finset.range L, ENNReal.ofReal ((K * Real.sqrt p / W) ^ p) :=
        add_le_add hcoreE (Finset.sum_le_sum hstepE)
    _ = ENNReal.ofReal (((L : ℝ) + 1) * (K * Real.sqrt p / W) ^ p) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add ht0 (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (Real.exp (-(ε' / 8 * W * Real.log W))) :=
        ENNReal.ofReal_le_ofReal (harith L hLT)

/-!
## 9. The contract
-/

/-- **The one-step matched-trace recursion and the scalar exit bound**: constructor of
`ScalarRecursionContract`, from `ConditionalBlockGUECount`, `GaussianLpGradient` and the core
trace bound (`CoreTraceBound`, the `r ∈ {1,2}` clause of the matched-traces theorem). -/
theorem scalarRecursion_holds (hcount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) (hcore : CoreTraceBound) :
    ScalarRecursionContract where
  oneStep := by
    intro b hb0 hb1 κ hκ
    obtain ⟨d₀, q, C, ε, hd₀, -, hq1, -, hε, h⟩ := srec_oneStep_core hcount hgrad b hb0 hb1 κ hκ
    refine ⟨d₀, q, C, ε, hd₀, hq1, hε, ?_⟩
    intro W hW X hX E hE hd
    exact ⟨(h W hW X hX E hE).1 hd, (h W hW X hX E hE).2⟩
  exit := srec_exit_core hcount hgrad hcore

end BlockBand.Layers
