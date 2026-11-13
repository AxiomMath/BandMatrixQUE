module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VecAdapt
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Cross-bracket martingales of general integrals

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, finite `ι`,
`h : IsL2IntegratorVec Q 𝓖 N a` with symmetric `a` (`hs`), horizon `T`,
`ν̄ = barMeasure Q a T`, `H, K ∈ PredL2 𝓖 ν̄` (representatives `H̃, K̃`),
`Z^i_t(H) = ∫_0^t H dN^i := (h.coord i).contIntegral T (restr H)`, and the pathwise cross
bracket `C_t = crossTerm a i j H̃ K̃ (t ∧ T) = ∫_{(0, t∧T]} H̃ K̃ a^{ij} dr`.

* `integrable_crossTerm`: `C_t ∈ L¹(Q)`; `setIntegral_rect_indicator` (the pathwise integral of
  a predictable rectangle indicator, for Fubini).
* `setIntegral_cross_eq`: `∫_B (Z^i_v Z^j_v - C_v) = ∫_B (Z^i_u Z^j_u - C_u)` for
  `u ≤ v ≤ T`, `B ∈ 𝓖_u`. Proof: martingale orthogonality reduces the left side to
  `E[1_B ΔZ^i ΔZ^j]`; the stopping-rectangle identity `stochIntegral_predInd_rect_of_le`
  writes `1_B ΔZ^i = ∫_0^T 1_{(u,v] × B} H dN^i`; the cross isometry `inner_coordInt` and
  Fubini give `E[1_B (C_v - C_u)]`.

These give, in the sibling module:
* **`IsL2IntegratorVec.cross_martingale`**: `Z^i(H) Z^j(K) - ∫_0^{·∧T} H̃ K̃ a^{ij}` has a
  `𝓖`-martingale modification (adaptedness: `aesm_crossTerm`).
* **`IsL2IntegratorVec.vecBracket_martingale`**: `(∑_i ∫_0^t H_i dN^i)² - ∫_0^{t∧T} Hᵀ a H` has a
  martingale modification (`vecCont`, `quadDensity`).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] {N : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ}

omit mΩ [IsFiniteMeasure Q] [Fintype ι] in
/-- Pathwise integral of a rectangle indicator. -/
theorem setIntegral_rect_indicator {T u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) {B : Set Ω}
    {F : ℝ × Ω → ℝ} {ω : Ω} (hω : IntegrableOn (fun r => F (r, ω)) (Ioc 0 T)) :
    ∫ r in Ioc (0 : ℝ) T, (Ioc (u : ℝ) v ×ˢ B).indicator F (r, ω) =
      B.indicator (fun ω => (∫ r in Ioc (0 : ℝ) v, F (r, ω)) - ∫ r in Ioc (0 : ℝ) u, F (r, ω)) ω := by
  by_cases hB : ω ∈ B
  · have hpt : (fun r => (Ioc (u : ℝ) v ×ˢ B).indicator F (r, ω)) =
        (Ioc (u : ℝ) v).indicator fun r => F (r, ω) := by
      funext r; by_cases hr : r ∈ Ioc (u : ℝ) v <;> simp [indicator, hr, hB]
    have hI : Ioc (0 : ℝ) T ∩ Ioc (u : ℝ) v = Ioc (u : ℝ) v :=
      inter_eq_right.2 (Ioc_subset_Ioc u.coe_nonneg (NNReal.coe_le_coe.2 hvT))
    have hU : Ioc (0 : ℝ) u ∪ Ioc (u : ℝ) v = Ioc (0 : ℝ) v :=
      Ioc_union_Ioc_eq_Ioc u.coe_nonneg (NNReal.coe_le_coe.2 huv)
    have hsplit : ∫ r in Ioc (0 : ℝ) v, F (r, ω) =
        (∫ r in Ioc (0 : ℝ) u, F (r, ω)) + ∫ r in Ioc (u : ℝ) v, F (r, ω) := by
      rw [← hU]
      exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hω.mono_set (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (huv.trans hvT))))
        (hω.mono_set (Ioc_subset_Ioc u.coe_nonneg (NNReal.coe_le_coe.2 hvT)))
    have hfin : ∫ x in Ioc (u : ℝ) v, F (x, ω) =
        (∫ r in Ioc (0 : ℝ) v, F (r, ω)) - ∫ r in Ioc (0 : ℝ) u, F (r, ω) := by
      rw [hsplit]; ring
    rw [hpt, setIntegral_indicator measurableSet_Ioc, hI, indicator_of_mem hB]
    exact hfin
  · have hpt : (fun r => (Ioc (u : ℝ) v ×ˢ B).indicator F (r, ω)) = fun _ => 0 := by
      funext r; simp [indicator, hB]
    rw [hpt, indicator_of_notMem hB, integral_zero]

namespace IsL2IntegratorVec

variable (h : IsL2IntegratorVec Q 𝓖 N a) (T : ℝ≥0) (hs : ∀ i j t ω, a i j t ω = a j i t ω)

/-- The cross density `H̃ K̃ a^{ij}` on `ℝ × Ω`. -/
def crossDens (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) (p : ℝ × Ω) : ℝ :=
  (H : Lp ℝ 2 (barMeasure Q a T)) p * (K : Lp ℝ 2 (barMeasure Q a T)) p * a i j p.1.toNNReal p.2

include h hs

theorem integrable_crossDens (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) :
    Integrable (crossDens T i j H K) (timeProbMeasure T Q) :=
  (h.integral_coordInt_mul T hs i j H K).1

/-- **Integrability of the pathwise cross bracket.** -/
theorem integrable_crossTerm (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) {q : ℝ≥0}
    (hq : q ≤ T) :
    Integrable (crossTerm a i j ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
      ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) q) Q := by
  have hF := h.integrable_crossDens T hs i j H K
  have hR : MeasurableSet (Ioc ((0 : ℝ≥0) : ℝ) q ×ˢ (univ : Set Ω)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hI := (hF.indicator hR).integral_prod_right
  refine hI.congr ?_
  filter_upwards [hF.prod_left_ae] with ω hω
  rw [setIntegral_rect_indicator zero_le hq hω, indicator_of_mem (mem_univ ω)]
  simp [crossTerm, crossDens]

/-- **The bracket identity on `(u, v] × B`**, `u ≤ v ≤ T`, `B ∈ 𝓖_u`. -/
theorem setIntegral_cross_eq (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) {u v : ℝ≥0}
    (huv : u ≤ v) (hvT : v ≤ T) {B : Set Ω} (hB : MeasurableSet[𝓖 u] B) :
    ∫ ω in B, ((h.coord i).contIntegral T (h.restr T i H) v ω *
        (h.coord j).contIntegral T (h.restr T j K) v ω -
        crossTerm a i j ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
          ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) v ω) ∂Q =
      ∫ ω in B, ((h.coord i).contIntegral T (h.restr T i H) u ω *
        (h.coord j).contIntegral T (h.restr T j K) u ω -
        crossTerm a i j ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
          ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) u ω) ∂Q := by
  have hBm : MeasurableSet B := 𝓖.le _ _ hB
  set Hi := h.restr T i H
  set Kj := h.restr T j K
  set Zi := (h.coord i).contIntegral T Hi
  set Zj := (h.coord j).contIntegral T Kj
  set C := crossTerm a i j ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
    ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
  have sZi := (h.coord i).contIntegral_spec T Hi
  have sZj := (h.coord j).contIntegral_spec T Kj
  obtain ⟨Yi, hYi, hYie⟩ := sZi.2.2.1
  obtain ⟨Yj, hYj, hYje⟩ := sZj.2.2.1
  have hL (X Y : Ω → ℝ) (hX : MemLp X 2 Q) (hY : MemLp Y 2 Q) :
      Integrable (fun ω => X ω * Y ω) Q := hX.integrable_mul hY
  -- orthogonality
  have o1 : ∫ ω in B, Zi u ω * (Zj v ω - Zj u ω) ∂Q = 0 := by
    rw [← setIntegral_mul_sub_eq_zero hYj huv ((sZj.2.1 v).ae_eq (hYje v).symm) hB (sZi.2.1 u)
      ((h.coord i).aestronglyMeasurable_contIntegral T Hi u)]
    refine setIntegral_congr_ae hBm ?_
    filter_upwards [hYje u, hYje v] with ω h1 h2 _
    rw [h1, h2]
  have o2 : ∫ ω in B, Zj u ω * (Zi v ω - Zi u ω) ∂Q = 0 := by
    rw [← setIntegral_mul_sub_eq_zero hYi huv ((sZi.2.1 v).ae_eq (hYie v).symm) hB (sZj.2.1 u)
      ((h.coord j).aestronglyMeasurable_contIntegral T Kj u)]
    refine setIntegral_congr_ae hBm ?_
    filter_upwards [hYie u, hYie v] with ω h1 h2 _
    rw [h1, h2]
  -- the rectangle integrands
  have hR := measurableSet_rect_pred 𝓖 (q₂ := v) hB
  set H' := predInd 𝓖 _ hR H
  set K' := predInd 𝓖 _ hR K
  have eI : (h.coordInt T i H' : Ω → ℝ) =ᵐ[Q] B.indicator fun ω => Zi v ω - Zi u ω := by
    have : h.coordInt T i H' = (h.coord i).stochIntegral T (predInd 𝓖 _ hR Hi) := by
      simp only [coordInt, ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap, H', Hi, restr, predRestrict_predInd]
    rw [this]
    exact (h.coord i).stochIntegral_predInd_rect_of_le T Hi huv hvT hB
  have eJ : (h.coordInt T j K' : Ω → ℝ) =ᵐ[Q] B.indicator fun ω => Zj v ω - Zj u ω := by
    have : h.coordInt T j K' = (h.coord j).stochIntegral T (predInd 𝓖 _ hR Kj) := by
      simp only [coordInt, ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap, K', Kj, restr, predRestrict_predInd]
    rw [this]
    exact (h.coord j).stochIntegral_predInd_rect_of_le T Kj huv hvT hB
  -- the right side through the cross isometry
  have hF := h.integrable_crossDens T hs i j H K
  have hRm : MeasurableSet (Ioc (u : ℝ) v ×ˢ B) := measurableSet_Ioc.prod hBm
  have hHK : Integrable (fun p => (H : Lp ℝ 2 (barMeasure Q a T)) p *
      (K : Lp ℝ 2 (barMeasure Q a T)) p) (barMeasure Q a T) :=
    (Lp.memLp _).integrable_mul (Lp.memLp _)
  obtain ⟨-, hbar⟩ := h.integral_bar_crossRatio hs T i j (hHK.indicator hRm)
  have key : ∫ ω in B, (Zi v ω - Zi u ω) * (Zj v ω - Zj u ω) ∂Q =
      ∫ ω in B, (C v ω - C u ω) ∂Q := by
    calc _ = ∫ ω, h.coordInt T i H' ω * h.coordInt T j K' ω ∂Q := by
          rw [← integral_indicator hBm]
          refine integral_congr_ae ?_
          filter_upwards [eI, eJ] with ω h1 h2
          rw [h1, h2]
          by_cases hω : ω ∈ B <;> simp [hω]
      _ = crossInt Q a T i j H' K' := by
          rw [← real_inner_Lp_eq]; exact h.inner_coordInt T hs i j H' K'
      _ = ∫ p, crossRatio a i j p.1.toNNReal p.2 * (Ioc (u : ℝ) v ×ˢ B).indicator
            (fun p => (H : Lp ℝ 2 (barMeasure Q a T)) p *
              (K : Lp ℝ 2 (barMeasure Q a T)) p) p ∂barMeasure Q a T := by
          rw [crossInt]
          refine integral_congr_ae ?_
          filter_upwards [predInd_coeFn 𝓖 _ hR H, predInd_coeFn 𝓖 _ hR K] with p h1 h2
          rw [h1, h2]
          by_cases hp : p ∈ Ioc (u : ℝ) v ×ˢ B <;> simp [hp]
      _ = ∫ p, (Ioc (u : ℝ) v ×ˢ B).indicator (crossDens T i j H K) p ∂timeProbMeasure T Q := by
          rw [hbar]
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          by_cases hp : p ∈ Ioc (u : ℝ) v ×ˢ B <;> simp [hp, crossDens]
      _ = ∫ ω, (∫ r in Ioc (0 : ℝ) T, (Ioc (u : ℝ) v ×ˢ B).indicator (crossDens T i j H K)
            (r, ω)) ∂Q := by
          rw [timeProbMeasure, integral_prod_symm _ (hF.indicator hRm)]
      _ = ∫ ω, B.indicator (fun ω => C v ω - C u ω) ω ∂Q := by
          refine integral_congr_ae ?_
          filter_upwards [hF.prod_left_ae] with ω hω
          rw [setIntegral_rect_indicator huv hvT hω]
          simp only [C, crossTerm, crossDens]
      _ = _ := integral_indicator hBm
  -- assembly
  have iZZ (q : ℝ≥0) : Integrable (fun ω => Zi q ω * Zj q ω) Q :=
    hL _ _ (sZi.2.1 q) (sZj.2.1 q)
  have iC (q : ℝ≥0) (hq : q ≤ T) : Integrable (C q) Q := h.integrable_crossTerm T hs i j H K hq
  have iA : Integrable (fun ω => Zi u ω * (Zj v ω - Zj u ω)) Q :=
    hL _ _ (sZi.2.1 u) ((sZj.2.1 v).sub (sZj.2.1 u))
  have iB : Integrable (fun ω => Zj u ω * (Zi v ω - Zi u ω)) Q :=
    hL _ _ (sZj.2.1 u) ((sZi.2.1 v).sub (sZi.2.1 u))
  have iD : Integrable (fun ω => (Zi v ω - Zi u ω) * (Zj v ω - Zj u ω)) Q :=
    hL _ _ ((sZi.2.1 v).sub (sZi.2.1 u)) ((sZj.2.1 v).sub (sZj.2.1 u))
  have hexp : ∫ ω in B, (Zi v ω * Zj v ω - Zi u ω * Zj u ω) ∂Q =
      ∫ ω in B, (Zi v ω - Zi u ω) * (Zj v ω - Zj u ω) ∂Q := by
    have he : (fun ω => Zi v ω * Zj v ω - Zi u ω * Zj u ω) = fun ω =>
        (Zi v ω - Zi u ω) * (Zj v ω - Zj u ω) + Zi u ω * (Zj v ω - Zj u ω) +
          Zj u ω * (Zi v ω - Zi u ω) := by funext ω; ring
    have e1 := integral_add (μ := Q.restrict B) (iD.integrableOn.add iA.integrableOn)
      iB.integrableOn
    have e2 := integral_add (μ := Q.restrict B) iD.integrableOn iA.integrableOn
    simp only [Pi.add_apply] at e1
    rw [he, e1, e2, o1, o2, add_zero, add_zero]
  have h1 := integral_sub (iZZ v).integrableOn (iC v hvT).integrableOn (μ := Q.restrict B)
  have h2 := integral_sub (iZZ u).integrableOn (iC u (huv.trans hvT)).integrableOn
    (μ := Q.restrict B)
  have h3 := integral_sub (iZZ v).integrableOn (iZZ u).integrableOn (μ := Q.restrict B)
  have h4 := integral_sub (iC v hvT).integrableOn (iC u (huv.trans hvT)).integrableOn
    (μ := Q.restrict B)
  rw [hexp, key] at h3
  rw [h1, h2]
  linarith

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
