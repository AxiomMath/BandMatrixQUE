module

public import BlockBand.SourceProcess.ModelExist.TransFinal

/-!
# Measurability, continuity and integrals of the born congruence

* `stronglyMeasurable_bornG`: `G_t` is `𝓖_t`-measurable (the columns `1{θ_y ≤ t} λ_y`);
* `continuous_of_entries`: a Gram path is continuous if all its coordinates are;
* `integrableOn_ite_le`, `integrableOn_ite_lt`: if `g` is integrable on `(0, t]`, so are
  `s ↦ 1{r ≤ s} g s` and `s ↦ 1{r < s} g s` for every `r ∈ [0, ∞]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

variable {c c' : Type*} [Fintype c] [Fintype c']

/-- The matrix with the single column `v` at `y`. -/
def colMat [DecidableEq c] (y : c) (v : c' → ℂ) : Matrix c' c ℂ := fun x y' => if y' = y then v x else 0

omit [Fintype c] [Fintype c'] in
theorem continuous_colMat [DecidableEq c] (y : c) : Continuous (colMat (c' := c') y) :=
  continuous_pi fun x => continuous_pi fun y' => by
    unfold colMat
    split_ifs
    · exact continuous_apply x
    · exact continuous_const

omit [Fintype c'] in
theorem bornL_eq_sum [DecidableEq c] {Ω : Type*} (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ)
    (t : ℝ≥0) (ω : Ω) :
    bornL θ lam t ω = ∑ y, if ((θ y ω : ℝ≥0) : WithTop ℝ≥0) ≤ t then colMat y (lam y ω) else 0 := by
  ext x y'
  simp only [bornL, Matrix.sum_apply]
  rw [Finset.sum_eq_single y' ?_ (by simp)]
  · split_ifs with h1 h2 h2
    · simp [colMat]
    · exact absurd (WithTop.coe_le_coe.2 h1) h2
    · exact absurd (WithTop.coe_le_coe.1 h2) h1
    · simp
  · intro b _ hb
    split_ifs
    · simp [colMat, Ne.symm hb]
    · simp

omit [Fintype c] in
theorem continuous_congrGram :
    Continuous fun p : Matrix c' c ℂ × (Matrix c' c' ℂ × Matrix c' c' ℂ) => congrGram p.1 p.2 :=
  ((continuous_fst.matrix_conjTranspose.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
    continuous_fst).prodMk
  ((continuous_fst.matrix_conjTranspose.matrix_mul (continuous_snd.comp continuous_snd)).matrix_mul
    continuous_fst)

omit [Fintype c] [Fintype c'] in
theorem continuous_of_entries {α : Type*} [TopologicalSpace α] {H : α → Matrix c c ℂ × Matrix c c ℂ}
    (h : ∀ e : Fin 2 × c × c, Continuous fun t => gramEntry e (H t)) : Continuous H :=
  (continuous_pi fun i => continuous_pi fun j => by simpa [gramEntry] using h (0, i, j)).prodMk
    (continuous_pi fun i => continuous_pi fun j => by simpa [gramEntry] using h (1, i, j))

omit [Fintype c] [Fintype c'] in
theorem integrableOn_ite_le {g : ℝ → ℂ} {t : ℝ≥0} (hg : IntegrableOn g (Ioc 0 t))
    (r : WithTop ℝ≥0) :
    IntegrableOn (fun s : ℝ => if r ≤ (s.toNNReal : WithTop ℝ≥0) then g s else 0) (Ioc 0 t) := by
  have hm : MeasurableSet {v : ℝ | r ≤ (v.toNNReal : WithTop ℝ≥0)} :=
    measurableSet_le measurable_const (WithTop.measurable_coe.comp measurable_real_toNNReal)
  refine (hg.indicator hm).congr_fun (fun v _ => ?_) measurableSet_Ioc
  by_cases h : r ≤ (v.toNNReal : WithTop ℝ≥0)
  · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | r ≤ (v.toNNReal : WithTop ℝ≥0)} from h)]
    split_ifs; rfl
  · rw [Set.indicator_of_notMem (show v ∉ {v : ℝ | r ≤ (v.toNNReal : WithTop ℝ≥0)} from h)]
    split_ifs; rfl

omit [Fintype c] [Fintype c'] in
theorem integrableOn_ite_lt {g : ℝ → ℂ} {t : ℝ≥0} (hg : IntegrableOn g (Ioc 0 t))
    (r : WithTop ℝ≥0) :
    IntegrableOn (fun s : ℝ => if r < (s.toNNReal : WithTop ℝ≥0) then g s else 0) (Ioc 0 t) := by
  have hm : MeasurableSet {v : ℝ | r < (v.toNNReal : WithTop ℝ≥0)} :=
    measurableSet_lt measurable_const (WithTop.measurable_coe.comp measurable_real_toNNReal)
  refine (hg.indicator hm).congr_fun (fun v _ => ?_) measurableSet_Ioc
  by_cases h : r < (v.toNNReal : WithTop ℝ≥0)
  · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | r < (v.toNNReal : WithTop ℝ≥0)} from h)]
    split_ifs; rfl
  · rw [Set.indicator_of_notMem (show v ∉ {v : ℝ | r < (v.toNNReal : WithTop ℝ≥0)} from h)]
    split_ifs; rfl

variable {Ω : Type*} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

omit [Fintype c'] in
theorem stronglyMeasurable_bornL [DecidableEq c] {θ : c → Ω → ℝ≥0}
    (hθ : ∀ y, Measurable[𝓖 0] (θ y)) {lam : c → Ω → c' → ℂ}
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    (t : ℝ≥0) : StronglyMeasurable[𝓖 t] (fun ω => bornL θ lam t ω) := by
  simp only [bornL_eq_sum]
  exact Finset.stronglyMeasurable_fun_sum _ fun y _ => stronglyMeasurable_ite_le
    (isStoppingTime_of_meas0 (hθ y)) ((continuous_colMat y).comp_stronglyMeasurable (hlam y)) t

theorem stronglyMeasurable_bornG [DecidableEq c] {𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ}
    (h𝒢 : ∀ t, StronglyMeasurable[𝓖 t] (𝒢 t)) {θ : c → Ω → ℝ≥0}
    (hθ : ∀ y, Measurable[𝓖 0] (θ y)) {lam : c → Ω → c' → ℂ}
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    (t : ℝ≥0) : StronglyMeasurable[𝓖 t] (bornG 𝒢 θ lam t) := by
  have h1 : StronglyMeasurable[𝓖 t] (fun ω => (bornL θ lam t ω, 𝒢 t ω)) :=
    (stronglyMeasurable_bornL hθ hlam t).prodMk (h𝒢 t)
  have h2 := (continuous_congrGram (c := c) (c' := c')).comp_stronglyMeasurable h1
  exact h2

end BlockBand.SourceProcess.ModelExist
