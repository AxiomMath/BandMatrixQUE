module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Piece
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The elementary integral `∫ 1_{(s,u]} G e_k dB = G (B^k_u - B^k_s)`

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion
(`IsFiltrationBrownian`), its vector integrator `hB.isL2IntegratorVec` (identity density
`idDens`), horizon `T`, integrand measure `barMeasure P (idDens d Ω) T`.

* `vecCont_unitTop`: `∫_0^t e_k dB = B^k_t - B^k_0` a.s. for all `t ≤ T`.
* `vecIntegral_pieceFn_indicator`, `vecIntegral_pieceFn_simple`: the identity for `G = 1_A` and
  for `𝓕_s`-simple `G`.
* **`vecIntegral_pieceFn`**: for bounded `𝓕_s`-strongly measurable `G` and `s ≤ u ≤ T`,
  `∫_0^T 1_{(s,u]} G e_k dB = G (B^k_u - B^k_s)` a.s.

The time-`t` form `∫_0^t 1_{(s,u]} G e_k dB = G (B^k_{u∧t} - B^k_{s∧t})`, `t ≤ T`, is derived
from it in a sibling module (`vecCont_pieceFn`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ}

theorem isStoppingTime_top'' : IsStoppingTime 𝓕 (fun _ : Ω => (⊤ : WithTop ℝ≥0)) :=
  fun t => by simp

/-- `∫_0^t e_k dB = B^k_t - B^k_0` a.s. for all `t ≤ T`. -/
theorem vecCont_unitTop (hB : IsFiltrationBrownian P 𝓕 B) (T : ℝ≥0) (k : Fin d) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
    ∀ᵐ ω ∂P, ∀ t ≤ T, hB.isL2IntegratorVec.vecCont T
      (fun l => bpL2 _ (isBddPred_unitStop isStoppingTime_top'' k l)) t ω = B t ω k - B 0 ω k := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  filter_upwards [vecCont_unitStop hB.isL2IntegratorVec T isStoppingTime_top'' k] with ω hω t ht
  rw [hω t ht, stopTime_of_le le_top]

theorem pieceFn_indicator_eq (s u : ℝ≥0) {T : ℝ≥0} (hsu : s ≤ u) (huT : u ≤ T) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) (k l : Fin d) (p : ℝ × Ω) :
    pieceFn s u (A.indicator 1) k l p =
      (Rect.set (⟨s, u, A, hsu, huT, hA⟩ : Rect 𝓕 T)).indicator
        (fun p => if l = k then (stopSet (fun _ : Ω => (⊤ : WithTop ℝ≥0))).indicator
          (fun _ => (1 : ℝ)) p else 0) p := by
  have htop : p ∈ stopSet (fun _ : Ω => (⊤ : WithTop ℝ≥0)) :=
    mem_stopSet.2 (le_top : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ⊤)
  simp only [pieceFn, Rect.set]
  by_cases hl : l = k <;> by_cases h1 : p.1 ∈ Ioc (s : ℝ) u <;> by_cases h2 : p.2 ∈ A <;>
    simp [hl, h1, h2, indicator_of_mem htop]

omit mΩ in
theorem pieceFn_mul_left (s u : ℝ≥0) (c : ℝ) (G : Ω → ℝ) (k l : Fin d) (p : ℝ × Ω) :
    pieceFn s u (fun ω => c * G ω) k l p = c * pieceFn s u G k l p := by
  simp only [pieceFn, indicator_apply]
  split_ifs <;> simp

omit mΩ in
theorem pieceFn_add (s u : ℝ≥0) (G G' : Ω → ℝ) (k l : Fin d) (p : ℝ × Ω) :
    pieceFn s u (fun ω => G ω + G' ω) k l p = pieceFn s u G k l p + pieceFn s u G' k l p := by
  simp only [pieceFn, indicator_apply]
  split_ifs <;> simp

omit mΩ in
theorem coe_piecewise_const {m : MeasurableSpace Ω} {A : Set Ω} (hA : MeasurableSet A) (c : ℝ) :
    ⇑(SimpleFunc.piecewise A hA (SimpleFunc.const Ω c) (SimpleFunc.const Ω 0)) =
      fun ω => c * A.indicator 1 ω := by
  classical
  funext ω
  simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, Set.piecewise, indicator_apply,
    Pi.one_apply, Function.const_apply]
  split_ifs <;> simp

/-- The identity for `G = 1_A`, `A ∈ 𝓕_s`. -/
theorem vecIntegral_pieceFn_indicator (hB : IsFiltrationBrownian P 𝓕 B) {s u T : ℝ≥0}
    (hsu : s ≤ u) (huT : u ≤ T) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) (k : Fin d)
    (h : ∀ l, IsBddPred 𝓕 (pieceFn s u (A.indicator 1) k l)) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
    (hB.isL2IntegratorVec.vecIntegral T (fun l => bpL2 _ (h l)) : Ω → ℝ) =ᵐ[P]
      fun ω => A.indicator 1 ω * (B u ω k - B s ω k) := by
  classical
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  set r : Rect 𝓕 T := ⟨s, u, A, hsu, huT, hA⟩
  set G := fun l => bpL2 (barMeasure P (idDens d Ω) T)
    (isBddPred_unitStop isStoppingTime_top'' k l)
  have e : (fun l => bpL2 (barMeasure P (idDens d Ω) T) (h l)) =
      fun l => predInd 𝓕 r.set r.measurableSet_pred (G l) := funext fun l => by
    rw [← bpL2_indicator]
    exact bpL2_congr _ _ (Eventually.of_forall fun p => pieceFn_indicator_eq s u hsu huT hA k l p)
  rw [e]
  filter_upwards [vecIntegral_predInd_rect hB.isL2IntegratorVec T G r,
    vecCont_unitTop hB T k] with ω h1 h2
  have h2' : ∀ t ≤ T, hB.isL2IntegratorVec.vecCont T G t ω = B t ω k - B 0 ω k := h2
  rw [h1]
  change A.indicator (fun ω => hB.isL2IntegratorVec.vecCont T G u ω -
    hB.isL2IntegratorVec.vecCont T G s ω) ω = _
  rw [indicator_apply, h2' u huT, h2' s (hsu.trans huT)]
  by_cases hω : ω ∈ A <;> simp [hω]

/-- The identity for `𝓕_s`-simple `G`. -/
theorem vecIntegral_pieceFn_simple (hB : IsFiltrationBrownian P 𝓕 B) {s u T : ℝ≥0}
    (hsu : s ≤ u) (huT : u ≤ T) (k : Fin d) (f : @SimpleFunc Ω (𝓕 s) ℝ)
    (h : ∀ l, IsBddPred 𝓕 (pieceFn s u f k l)) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
    (hB.isL2IntegratorVec.vecIntegral T (fun l => bpL2 _ (h l)) : Ω → ℝ) =ᵐ[P]
      fun ω => f ω * (B u ω k - B s ω k) := by
  classical
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  induction f using @SimpleFunc.induction _ _ (𝓕 s) with
  | @const c A hA =>
    have h1 : ∀ l, IsBddPred 𝓕 (pieceFn s u (A.indicator 1) k l) := fun l =>
      isBddPred_pieceFn ((stronglyMeasurable_const : StronglyMeasurable[𝓕 s]
        fun _ : Ω => (1 : ℝ)).indicator hA)
        (C := 1) (fun ω => by rw [indicator_apply]; split_ifs <;> simp) k l
    have e : (fun l => bpL2 (barMeasure P (idDens d Ω) T) (h l)) =
        c • fun l => bpL2 (barMeasure P (idDens d Ω) T) (h1 l) := funext fun l => by
      rw [Pi.smul_apply, ← bpL2_smul' c (h1 l) ((IsBddPred.const c).mul (h1 l))]
      refine bpL2_congr _ _ (Eventually.of_forall fun p => ?_)
      rw [coe_piecewise_const hA c]
      exact pieceFn_mul_left s u c _ k l p
    rw [e, vecIntegral_smul]
    filter_upwards [vecIntegral_pieceFn_indicator hB hsu huT hA k h1,
      Lp.coeFn_smul c (hB.isL2IntegratorVec.vecIntegral T fun l => bpL2 _ (h1 l))] with ω h2 h3
    rw [h3, Pi.smul_apply, h2, smul_eq_mul, coe_piecewise_const hA c]
    ring
  | @add f g _ hf hg =>
    obtain ⟨Cf, hCf⟩ := @SimpleFunc.exists_forall_norm_le Ω ℝ (𝓕 s) _ f
    obtain ⟨Cg, hCg⟩ := @SimpleFunc.exists_forall_norm_le Ω ℝ (𝓕 s) _ g
    have h1 : ∀ l, IsBddPred 𝓕 (pieceFn s u f k l) := fun l =>
      isBddPred_pieceFn f.stronglyMeasurable (C := Cf)
        (fun ω => (Real.norm_eq_abs _).symm.le.trans (hCf ω)) k l
    have h2 : ∀ l, IsBddPred 𝓕 (pieceFn s u g k l) := fun l =>
      isBddPred_pieceFn g.stronglyMeasurable (C := Cg)
        (fun ω => (Real.norm_eq_abs _).symm.le.trans (hCg ω)) k l
    have e : (fun l => bpL2 (barMeasure P (idDens d Ω) T) (h l)) =
        (fun l => bpL2 (barMeasure P (idDens d Ω) T) (h1 l)) +
          fun l => bpL2 (barMeasure P (idDens d Ω) T) (h2 l) := funext fun l => by
      rw [Pi.add_apply, ← bpL2_add' (h1 l) (h2 l) ((h1 l).add (h2 l))]
      refine bpL2_congr _ _ (Eventually.of_forall fun p => ?_)
      exact pieceFn_add s u f g k l p
    rw [e, vecIntegral_add]
    filter_upwards [hf h1, hg h2, Lp.coeFn_add (hB.isL2IntegratorVec.vecIntegral T
      fun l => bpL2 _ (h1 l)) (hB.isL2IntegratorVec.vecIntegral T fun l => bpL2 _ (h2 l))]
      with ω e1 e2 e3
    rw [e3, Pi.add_apply, e1, e2]
    change _ = (f ω + g ω) * _
    ring

omit mΩ in
theorem pieceFn_sub_abs_le (s u : ℝ≥0) {G G' : Ω → ℝ} {C : ℝ} (hG : ∀ ω, |G ω| ≤ C)
    (hG' : ∀ ω, |G' ω| ≤ C) (k l : Fin d) (p : ℝ × Ω) :
    |pieceFn s u G k l p - pieceFn s u G' k l p| ≤ 2 * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hG p.2)
  simp only [pieceFn, indicator_apply]
  split_ifs
  · exact (abs_sub _ _).trans (by linarith [hG p.2, hG' p.2])
  · simp; linarith
  · simp; linarith

omit mΩ in
theorem tendsto_pieceFn (s u : ℝ≥0) {G : ℕ → Ω → ℝ} {G' : Ω → ℝ}
    (hG : ∀ ω, Tendsto (fun n => G n ω) atTop (𝓝 (G' ω))) (k l : Fin d) (p : ℝ × Ω) :
    Tendsto (fun n => pieceFn s u (G n) k l p) atTop (𝓝 (pieceFn s u G' k l p)) := by
  simp only [pieceFn, indicator_apply]
  split_ifs
  · exact hG p.2
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

/-- **The elementary integral** `∫_0^T 1_{(s,u]} G e_k dB = G (B^k_u - B^k_s)` for bounded
`𝓕_s`-strongly measurable `G`. -/
theorem vecIntegral_pieceFn (hB : IsFiltrationBrownian P 𝓕 B) {s u T : ℝ≥0}
    (hsu : s ≤ u) (huT : u ≤ T) {G : Ω → ℝ} (hG : StronglyMeasurable[𝓕 s] G) {C : ℝ}
    (hC : ∀ ω, |G ω| ≤ C) (k : Fin d) (h : ∀ l, IsBddPred 𝓕 (pieceFn s u G k l)) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
    (hB.isL2IntegratorVec.vecIntegral T (fun l => bpL2 _ (h l)) : Ω → ℝ) =ᵐ[P]
      fun ω => G ω * (B u ω k - B s ω k) := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  set hI := hB.isL2IntegratorVec
  set μ := barMeasure P (idDens d Ω) T
  set C' := max C 0
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hC' : ∀ ω, |G ω| ≤ C' := fun ω => (hC ω).trans (le_max_left _ _)
  set Gn : ℕ → @SimpleFunc Ω (𝓕 s) ℝ := hG.approxBounded C'
  have hGb : ∀ n ω, |Gn n ω| ≤ C' := fun n ω => by
    rw [← Real.norm_eq_abs]; exact hG.norm_approxBounded_le hC0 n ω
  have hGl : ∀ ω, Tendsto (fun n => Gn n ω) atTop (𝓝 (G ω)) := fun ω =>
    hG.tendsto_approxBounded_of_norm_le (by rw [Real.norm_eq_abs]; exact hC' ω)
  have hn : ∀ n l, IsBddPred 𝓕 (pieceFn s u (Gn n) k l) := fun n l =>
    isBddPred_pieceFn (Gn n).stronglyMeasurable (hGb n) k l
  set Δ : Ω → ℝ := fun ω => B u ω k - B s ω k
  have hΔ : MemLp Δ 2 P := hB.memLp_incr hsu k
  -- the integrands converge in `L²(μ)`
  have hconv : Tendsto (fun n => fun l => bpL2 μ (hn n l)) atTop (𝓝 fun l => bpL2 μ (h l)) := by
    rw [tendsto_pi_nhds]
    intro l
    rw [tendsto_subtype_rng, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have e : ∀ n, eLpNorm (⇑((bpL2 μ (hn n l) : PredL2 𝓕 μ) : Lp ℝ 2 μ) -
        ⇑((bpL2 μ (h l) : PredL2 𝓕 μ) : Lp ℝ 2 μ)) 2 μ =
        eLpNorm (pieceFn s u (Gn n) k l - pieceFn s u G k l) 2 μ := fun n =>
      eLpNorm_congr_ae ((bpL2_coeFn (hn n l)).sub (bpL2_coeFn (h l)))
    simp_rw [e]
    refine tendsto_eLpNorm_two_of_dominated (C := fun _ => 2 * C')
      (fun n => ((hn n l).sm.mono (predictableSpace_le _)).aestronglyMeasurable)
      (((h l).sm.mono (predictableSpace_le _)).aestronglyMeasurable) (memLp_const _)
      (fun n => Eventually.of_forall fun p => pieceFn_sub_abs_le s u (hGb n) hC' k l p)
      (Eventually.of_forall fun p => tendsto_pieceFn s u hGl k l p)
  have hV : Tendsto (fun n => hI.vecIntegral T fun l => bpL2 μ (hn n l)) atTop
      (𝓝 (hI.vecIntegral T fun l => bpL2 μ (h l))) := by
    have := ((vecIntegralL hI T).continuous.tendsto _).comp hconv
    simpa only [Function.comp_def, vecIntegralL_apply] using this
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hV
  -- the elementary side converges in `L²(P)`
  have hR : Tendsto (fun n => eLpNorm ((fun ω => Gn n ω * Δ ω) - fun ω => G ω * Δ ω) 2 P)
      atTop (𝓝 0) := by
    refine tendsto_eLpNorm_two_of_dominated (C := fun ω => 2 * C' * |Δ ω|)
      (fun n => ((Gn n).stronglyMeasurable.mono (𝓕.le s)).aestronglyMeasurable.mul
        hΔ.aestronglyMeasurable)
      ((hG.mono (𝓕.le s)).aestronglyMeasurable.mul hΔ.aestronglyMeasurable)
      (hΔ.abs.const_mul _) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => (hGl ω).mul_const _)
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by linarith [hGb n ω, hC' ω]))
      (abs_nonneg _)
  -- conclusion
  have hsum := (hV.add hR)
  rw [zero_add] at hsum
  have key : eLpNorm (⇑(hI.vecIntegral T fun l => bpL2 μ (h l)) - fun ω => G ω * Δ ω) 2 P = 0 := by
    refine le_antisymm (ge_of_tendsto' hsum fun n => ?_) zero_le
    have hz : eLpNorm (⇑(hI.vecIntegral T fun l => bpL2 μ (hn n l)) - fun ω => Gn n ω * Δ ω)
        2 P = 0 := by
      rw [eLpNorm_eq_zero_iff two_ne_zero]
      filter_upwards [vecIntegral_pieceFn_simple hB hsu huT k (Gn n) (hn n)] with ω hω
      change _ - _ = (0 : ℝ)
      rw [hω, sub_self]
    calc eLpNorm (⇑(hI.vecIntegral T fun l => bpL2 μ (h l)) - fun ω => G ω * Δ ω) 2 P
        = eLpNorm ((⇑(hI.vecIntegral T fun l => bpL2 μ (h l)) -
              ⇑(hI.vecIntegral T fun l => bpL2 μ (hn n l))) +
            ((⇑(hI.vecIntegral T fun l => bpL2 μ (hn n l)) - fun ω => Gn n ω * Δ ω) +
              ((fun ω => Gn n ω * Δ ω) - fun ω => G ω * Δ ω))) 2 P := by
          congr 1; abel
      _ ≤ eLpNorm (⇑(hI.vecIntegral T fun l => bpL2 μ (h l)) -
              ⇑(hI.vecIntegral T fun l => bpL2 μ (hn n l))) 2 P +
            (eLpNorm (⇑(hI.vecIntegral T fun l => bpL2 μ (hn n l)) - fun ω => Gn n ω * Δ ω)
              2 P + eLpNorm ((fun ω => Gn n ω * Δ ω) - fun ω => G ω * Δ ω) 2 P) :=
          (eLpNorm_add_le one_le_two).trans (add_le_add le_rfl (eLpNorm_add_le one_le_two))
      _ = eLpNorm (⇑(hI.vecIntegral T fun l => bpL2 μ (hn n l)) -
              ⇑(hI.vecIntegral T fun l => bpL2 μ (h l))) 2 P +
            eLpNorm ((fun ω => Gn n ω * Δ ω) - fun ω => G ω * Δ ω) 2 P := by
          rw [hz, zero_add, eLpNorm_sub_comm]
  rw [eLpNorm_eq_zero_iff two_ne_zero] at key
  filter_upwards [key] with ω hω
  simpa [sub_eq_zero] using hω

end BlockBand.SourceProcess.Stochastic.Uniqueness
