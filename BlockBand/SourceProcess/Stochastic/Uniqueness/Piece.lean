module
public import BlockBand.SourceProcess.Stochastic.Representation.PosDef
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Elementary integrands against a filtration Brownian motion

Setting: `(Ω, 𝓕, P)` with a raw filtration; `h : IsL2IntegratorVec P 𝓕 Z a` a vector integrator
(general vector integral of `GeneralIntegral/`); for the piece lemmas `B` is a `𝓕`-Brownian
motion (`IsFiltrationBrownian`) with its integrator `hB.isL2IntegratorVec` (identity density).

* `vecIntegral_add`, `vecIntegral_smul`, `vecCont_add_ae`, `vecCont_sub_ae`: linearity (a.s. at
  each time) of the vector integral.
* `pieceFn s u G k`: the vector integrand `1_{(s,u]}(r) G(ω) e_k`; `isBddPred_pieceFn` for
  bounded `𝓕_s`-strongly measurable `G`.

These are used in sibling modules to prove:
* **`vecIntegral_pieceFn`**: `∫_0^T 1_{(s,u]} G e_k dB = G (B^k_u - B^k_s)` a.s. (`s ≤ u ≤ T`);
  first for indicators (rectangle identity), then simple functions (induction), then bounded
  `G` (`approxBounded` and `L²` limits: dominated convergence on both sides).
* **`vecCont_pieceFn`**: at every time `t ≤ T`, `∫_0^t 1_{(s,u]} G e_k dB =
  G (B^k_{u∧t} - B^k_{s∧t})` a.s.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}

section Linear

variable {P : Measure Ω} [IsFiniteMeasure P] {ι : Type*} [Fintype ι] {Z : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ}

theorem vecIntegral_add (h : IsL2IntegratorVec P 𝓕 Z a) (T : ℝ≥0)
    (H H' : ι → PredL2 𝓕 (barMeasure P a T)) :
    h.vecIntegral T (H + H') = h.vecIntegral T H + h.vecIntegral T H' := by
  rw [← vecIntegralL_apply, map_add, vecIntegralL_apply, vecIntegralL_apply]

theorem vecIntegral_smul (h : IsL2IntegratorVec P 𝓕 Z a) (T : ℝ≥0) (c : ℝ)
    (H : ι → PredL2 𝓕 (barMeasure P a T)) :
    h.vecIntegral T (c • H) = c • h.vecIntegral T H := by
  rw [← vecIntegralL_apply, map_smul, vecIntegralL_apply]

theorem vecIntegral_sub (h : IsL2IntegratorVec P 𝓕 Z a) (T : ℝ≥0)
    (H H' : ι → PredL2 𝓕 (barMeasure P a T)) :
    h.vecIntegral T (H - H') = h.vecIntegral T H - h.vecIntegral T H' := by
  rw [← vecIntegralL_apply, map_sub, vecIntegralL_apply, vecIntegralL_apply]

theorem vecCont_add_ae (h : IsL2IntegratorVec P 𝓕 Z a) (T : ℝ≥0)
    (H H' : ι → PredL2 𝓕 (barMeasure P a T)) (t : ℝ≥0) :
    h.vecCont T (H + H') t =ᵐ[P] fun ω => h.vecCont T H t ω + h.vecCont T H' t ω := by
  have hR := measurableSet_Iic_prod_univ 𝓕 t
  have e : (fun i => predInd 𝓕 _ hR ((H + H') i)) =
      (fun i => predInd 𝓕 _ hR (H i)) + fun i => predInd 𝓕 _ hR (H' i) := by
    funext i; simp only [Pi.add_apply, map_add]
  filter_upwards [vecIntegral_Iic h T (H + H') t, vecIntegral_Iic h T H t,
    vecIntegral_Iic h T H' t, Lp.coeFn_add (h.vecIntegral T fun i => predInd 𝓕 _ hR (H i))
      (h.vecIntegral T fun i => predInd 𝓕 _ hR (H' i))] with ω h1 h2 h3 h4
  rw [← h1, ← h2, ← h3, e, vecIntegral_add, h4, Pi.add_apply]

theorem vecCont_sub_ae (h : IsL2IntegratorVec P 𝓕 Z a) (T : ℝ≥0)
    (H H' : ι → PredL2 𝓕 (barMeasure P a T)) (t : ℝ≥0) :
    h.vecCont T (H - H') t =ᵐ[P] fun ω => h.vecCont T H t ω - h.vecCont T H' t ω := by
  have hR := measurableSet_Iic_prod_univ 𝓕 t
  have e : (fun i => predInd 𝓕 _ hR ((H - H') i)) =
      (fun i => predInd 𝓕 _ hR (H i)) - fun i => predInd 𝓕 _ hR (H' i) := by
    funext i; simp only [Pi.sub_apply, map_sub]
  filter_upwards [vecIntegral_Iic h T (H - H') t, vecIntegral_Iic h T H t,
    vecIntegral_Iic h T H' t, Lp.coeFn_sub (h.vecIntegral T fun i => predInd 𝓕 _ hR (H i))
      (h.vecIntegral T fun i => predInd 𝓕 _ hR (H' i))] with ω h1 h2 h3 h4
  rw [← h1, ← h2, ← h3, e, vecIntegral_sub, h4, Pi.sub_apply]

theorem vecCont_zero_ae (h : IsL2IntegratorVec P 𝓕 Z a) (T : ℝ≥0) (t : ℝ≥0) :
    h.vecCont T 0 t =ᵐ[P] 0 := by
  have := vecCont_sub_ae h T 0 0 t
  filter_upwards [this] with ω hω
  rw [sub_zero] at hω
  simpa using hω

theorem vecCont_finsetSum_ae (h : IsL2IntegratorVec P 𝓕 Z a) (T : ℝ≥0) {κ : Type*}
    (s : Finset κ) (H : κ → ι → PredL2 𝓕 (barMeasure P a T)) (t : ℝ≥0) :
    h.vecCont T (∑ j ∈ s, H j) t =ᵐ[P] fun ω => ∑ j ∈ s, h.vecCont T (H j) t ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact vecCont_zero_ae h T t
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [vecCont_add_ae h T (H j) (∑ j ∈ s, H j) t, ih] with ω h1 h2
    rw [h1, h2, Finset.sum_insert hj]

end Linear

section Piece

variable {d : ℕ}

/-- The vector integrand `1_{(s,u]}(r) G(ω) e_k`. -/
def pieceFn (s u : ℝ≥0) (G : Ω → ℝ) (k : Fin d) : Fin d → ℝ × Ω → ℝ := fun l p =>
  if l = k then (Ioc (s : ℝ) u ×ˢ (univ : Set Ω)).indicator (fun q => G q.2) p else 0

theorem measurableSet_pred_pieceFn {s u : ℝ≥0} {G : Ω → ℝ} (hG : Measurable[𝓕 s] G)
    {C : Set ℝ} (hC : MeasurableSet C) :
    MeasurableSet[predictableSpace (toCF 𝓕)]
      ((Ioc (s : ℝ) u ×ˢ (univ : Set Ω)).indicator (fun q => G q.2) ⁻¹' C) := by
  classical
  have e : (Ioc (s : ℝ) u ×ˢ (univ : Set Ω)).indicator (fun q => G q.2) ⁻¹' C =
      (Ioc (s : ℝ) u ×ˢ (G ⁻¹' C)) ∪
        (if (0 : ℝ) ∈ C then (Ioc (s : ℝ) u ×ˢ (univ : Set Ω))ᶜ else ∅) := by
    ext p
    by_cases hp : p ∈ Ioc (s : ℝ) u ×ˢ (univ : Set Ω)
    · have hp1 : p.1 ∈ Ioc (s : ℝ) u := hp.1
      by_cases h0 : (0 : ℝ) ∈ C <;> simp [hp1, h0]
    · have hp1 : p.1 ∉ Ioc (s : ℝ) u := fun h => hp ⟨h, mem_univ _⟩
      by_cases h0 : (0 : ℝ) ∈ C <;> simp [hp1, h0]
  rw [e]
  refine (measurableSet_rect_pred 𝓕 (hG hC)).union ?_
  split_ifs
  · exact (measurableSet_rect_pred 𝓕 (q₂ := u)
      (MeasurableSet.univ : MeasurableSet[𝓕 s] (univ : Set Ω))).compl
  · exact @MeasurableSet.empty _ (predictableSpace (toCF 𝓕))

theorem isBddPred_pieceFn {s u : ℝ≥0} {G : Ω → ℝ} (hG : StronglyMeasurable[𝓕 s] G) {C : ℝ}
    (hC : ∀ ω, |G ω| ≤ C) (k l : Fin d) : IsBddPred 𝓕 (pieceFn s u G k l) := by
  refine ⟨?_, max C 0, le_max_right _ _, fun p => ?_⟩
  · have hm : Measurable[predictableSpace (toCF 𝓕)] fun p : ℝ × Ω =>
        (Ioc (s : ℝ) u ×ˢ (univ : Set Ω)).indicator (fun q => G q.2) p :=
      fun C hC => measurableSet_pred_pieceFn hG.measurable hC
    by_cases hl : l = k
    · have e : pieceFn s u G k l = fun p : ℝ × Ω =>
          (Ioc (s : ℝ) u ×ˢ (univ : Set Ω)).indicator (fun q => G q.2) p :=
        funext fun p => ite_eq_left hl
      rw [e]
      exact hm.stronglyMeasurable
    · have e : pieceFn s u G k l = fun _ => (0 : ℝ) := funext fun p => ite_eq_right hl
      rw [e]
      exact stronglyMeasurable_const
  · simp only [pieceFn]
    split_ifs
    · rw [indicator_apply]
      split_ifs
      · exact (hC _).trans (le_max_left _ _)
      · simp
    · simp

theorem bpL2_add' {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {f g : ℝ × Ω → ℝ}
    (hf : IsBddPred 𝓕 f) (hg : IsBddPred 𝓕 g) (hfg : IsBddPred 𝓕 fun p => f p + g p) :
    bpL2 μ hfg = bpL2 μ hf + bpL2 μ hg := by
  refine predL2_ext 𝓕 ?_
  rw [Submodule.coe_add]
  filter_upwards [bpL2_coeFn (μ := μ) hfg, bpL2_coeFn (μ := μ) hf, bpL2_coeFn (μ := μ) hg,
    Lp.coeFn_add ((bpL2 μ hf : PredL2 𝓕 μ) : Lp ℝ 2 μ) ((bpL2 μ hg : PredL2 𝓕 μ) : Lp ℝ 2 μ)]
    with p h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]

theorem bpL2_smul' {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ} (c : ℝ)
    (hf : IsBddPred 𝓕 f) (hcf : IsBddPred 𝓕 fun p => c * f p) :
    bpL2 μ hcf = c • bpL2 μ hf := by
  refine predL2_ext 𝓕 ?_
  rw [Submodule.coe_smul]
  filter_upwards [bpL2_coeFn (μ := μ) hcf, bpL2_coeFn (μ := μ) hf,
    Lp.coeFn_smul c ((bpL2 μ hf : PredL2 𝓕 μ) : Lp ℝ 2 μ)] with p h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]

end Piece

/-- **Dominated `L²` convergence.** -/
theorem tendsto_eLpNorm_two_of_dominated {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g C : X → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ) (hC : MemLp C 2 μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, |f n x - g x| ≤ C x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
  have e : ∀ n, eLpNorm (f n - g) 2 μ =
      (∫⁻ x, ‖(f n - g) x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := fun n => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top ((hf n).sub hg),
      ENNReal.toReal_ofNat]
  simp_rw [e]
  have hfin : ∫⁻ x, ‖C x‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      hC.eLpNorm_lt_top
    rw [ENNReal.toReal_ofNat] at this
    exact this.ne
  have hl : Tendsto (fun n => ∫⁻ x, ‖(f n - g) x‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have h0 : ∫⁻ _x : X, (0 : ℝ≥0∞) ∂μ = 0 := lintegral_zero
    rw [← h0]
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖C x‖ₑ ^ (2 : ℝ))
      (fun n => AEMeasurable.pow_const ((hf n).sub hg).enorm _) (fun n => ?_) hfin ?_
    · filter_upwards [hb n] with x hx
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => f n x - g x) atTop (𝓝 0) := by
        simpa using hx.sub_const (g x)
      have h1' : Tendsto (fun n => ‖f n x - g x‖ₑ) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : ℝ)).comp h1
      have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h1'
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using h2
  have h3 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hl
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using h3

end BlockBand.SourceProcess.Stochastic.Uniqueness
