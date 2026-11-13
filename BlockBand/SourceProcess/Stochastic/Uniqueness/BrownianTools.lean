module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.PieceIntegral
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Elementary integrals at intermediate times and the Brownian isometry

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion, its
vector integrator `hB.isL2IntegratorVec` (identity density), horizon `T`.

* **`vecCont_pieceFn`**: for `s ≤ u ≤ T`, bounded `𝓕_s`-strongly measurable `G` and `t ≤ T`,
  `∫_0^t 1_{(s,u]} G e_k dB = G (B^k_{u∧t} - B^k_{s∧t})` a.s.
* **`integral_sq_vecCont`** (isometry at time `t ≤ T`, bounded predictable `f`):
  `E (∫_0^t f dB)² = E ∫_{(0,t]} ∑_k f_k(r)² dr`.
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

omit mΩ in
theorem indicator_Iic_pieceFn {s u t : ℝ≥0} (G : Ω → ℝ) (k l : Fin d)
    (p : ℝ × Ω) : (Iic (t : ℝ) ×ˢ (univ : Set Ω)).indicator (pieceFn s u G k l) p =
      pieceFn s (min u t) G k l p := by
  simp only [pieceFn, indicator_apply, mem_prod, mem_Iic, mem_univ, and_true, mem_Ioc,
    NNReal.coe_min, le_min_iff]
  split_ifs <;> simp_all

omit mΩ in
theorem indicator_Iic_pieceFn_of_lt {s u t : ℝ≥0} (hts : t < s) (G : Ω → ℝ) (k l : Fin d)
    (p : ℝ × Ω) : (Iic (t : ℝ) ×ˢ (univ : Set Ω)).indicator (pieceFn s u G k l) p =
      pieceFn s s G k l p := by
  have hts' : (t : ℝ) < s := hts
  simp only [pieceFn, indicator_apply, mem_prod, mem_Iic, mem_univ, and_true, mem_Ioc]
  split_ifs <;> simp_all
  all_goals linarith

/-- **The elementary integral at intermediate times.** -/
theorem vecCont_pieceFn (hB : IsFiltrationBrownian P 𝓕 B) {s u T : ℝ≥0}
    (hsu : s ≤ u) (huT : u ≤ T) {G : Ω → ℝ} (hG : StronglyMeasurable[𝓕 s] G) {C : ℝ}
    (hC : ∀ ω, |G ω| ≤ C) (k : Fin d) (h : ∀ l, IsBddPred 𝓕 (pieceFn s u G k l)) (t : ℝ≥0) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
    hB.isL2IntegratorVec.vecCont T (fun l => bpL2 _ (h l)) t =ᵐ[P]
      fun ω => G ω * (B (min u t) ω k - B (min s t) ω k) := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  set μ := barMeasure P (idDens d Ω) T
  have hR := measurableSet_Iic_prod_univ 𝓕 t
  have e1 : (fun l => predInd 𝓕 _ hR (bpL2 μ (h l))) =
      fun l => bpL2 μ ((h l).indicator hR) := funext fun l => (bpL2_indicator (h l) hR).symm
  have h0 := vecIntegral_Iic hB.isL2IntegratorVec T (fun l => bpL2 μ (h l)) t
  rw [e1] at h0
  rcases le_or_gt s t with hst | hts
  · have h2 : ∀ l, IsBddPred 𝓕 (pieceFn s (min u t) G k l) :=
      fun l => isBddPred_pieceFn hG hC k l
    have e2 : (fun l => bpL2 μ ((h l).indicator hR)) = fun l => bpL2 μ (h2 l) :=
      funext fun l => bpL2_congr _ _ (Eventually.of_forall fun p =>
        indicator_Iic_pieceFn G k l p)
    rw [e2] at h0
    filter_upwards [h0, vecIntegral_pieceFn hB (le_min hsu hst) ((min_le_left _ _).trans huT)
      hG hC k h2] with ω h3 h4
    rw [← h3, h4, min_eq_left hst]
  · have h2 : ∀ l, IsBddPred 𝓕 (pieceFn s s G k l) := fun l => isBddPred_pieceFn hG hC k l
    have e2 : (fun l => bpL2 μ ((h l).indicator hR)) = fun l => bpL2 μ (h2 l) :=
      funext fun l => bpL2_congr _ _ (Eventually.of_forall fun p =>
        indicator_Iic_pieceFn_of_lt hts G k l p)
    rw [e2] at h0
    filter_upwards [h0, vecIntegral_pieceFn hB le_rfl (hsu.trans huT) hG hC k h2] with ω h3 h4
    rw [← h3, h4, min_eq_right (hts.le.trans hsu), min_eq_right hts.le]
    ring

/-- **Brownian isometry at time `t ≤ T`** for bounded predictable vector integrands. -/
theorem integral_sq_vecCont (hB : IsFiltrationBrownian P 𝓕 B) {T : ℝ≥0}
    {f : Fin d → ℝ × Ω → ℝ} (hf : ∀ k, IsBddPred 𝓕 (f k)) {t : ℝ≥0} (htT : t ≤ T) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
    ∫ ω, (hB.isL2IntegratorVec.vecCont T (fun k => bpL2 _ (hf k)) t ω) ^ 2 ∂P =
      ∫ ω, (∫ r in Ioc (0 : ℝ) t, ∑ k, f k (r, ω) ^ 2) ∂P := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  set hI := hB.isL2IntegratorVec
  set μ := barMeasure P (idDens d Ω) T
  have hR := measurableSet_Iic_prod_univ 𝓕 t
  set g : Fin d → ℝ × Ω → ℝ := fun k => (Iic (t : ℝ) ×ˢ (univ : Set Ω)).indicator (f k)
  have hg : ∀ k, IsBddPred 𝓕 (g k) := fun k => (hf k).indicator hR
  have e1 : (fun k => predInd 𝓕 _ hR (bpL2 μ (hf k))) = fun k => bpL2 μ (hg k) :=
    funext fun k => (bpL2_indicator (hf k) hR).symm
  have h0 := vecIntegral_Iic hI T (fun k => bpL2 μ (hf k)) t
  rw [e1] at h0
  have hs : ∀ i j (t : ℝ≥0) (ω : Ω), idDens d Ω i j t ω = idDens d Ω j i t ω := fun i j _ _ => by
    simp only [idDens, eq_comm]
  have h1 : (fun ω => (hI.vecCont T (fun k => bpL2 μ (hf k)) t ω) ^ 2) =ᵐ[P]
      fun ω => (hI.vecIntegral T (fun k => bpL2 μ (hg k)) ω) ^ 2 := by
    filter_upwards [h0] with ω hω; rw [hω]
  rw [integral_congr_ae h1, hI.integral_sq_vecIntegral T hs]
  -- identify the quadratic density `dt ⊗ P`-a.e.
  have hq : IsL2IntegratorVec.quadDensity T (idDens d Ω) (fun k => bpL2 μ (hg k)) =ᵐ[timeProbMeasure T P]
      fun p => ∑ k, g k p ^ 2 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      exact Eventually.of_forall fun p => by simp [IsL2IntegratorVec.quadDensity]
    · have hac : timeProbMeasure T P ≪ μ := by
        have e : (fun p : ℝ × Ω => ENNReal.ofReal (traceA (idDens d Ω) p.1.toNNReal p.2)) =
            fun _ => ENNReal.ofReal d := by
          funext p; simp [traceA, idDens]
        change timeProbMeasure T P ≪ (timeProbMeasure T P).withDensity
          (fun p : ℝ × Ω => ENNReal.ofReal (traceA (idDens d Ω) p.1.toNNReal p.2))
        rw [e]
        exact withDensity_absolutelyContinuous' aemeasurable_const
          (Eventually.of_forall fun _ => (ENNReal.ofReal_pos.2 (Nat.cast_pos.2 hd)).ne')
      filter_upwards [hac.ae_le (ae_all_iff.2 fun k => bpL2_coeFn (μ := μ) (hg k))] with p hp
      simp only [IsL2IntegratorVec.quadDensity, idDens, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, hp, sq]
  rw [integral_congr_ae hq, timeProbMeasure, integral_prod_symm]
  · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have e : ∀ r : ℝ, (∑ k, g k (r, ω) ^ 2) = (Iic (t : ℝ)).indicator
        (fun r => ∑ k, f k (r, ω) ^ 2) r := fun r => by
      by_cases hr : r ∈ Iic (t : ℝ)
      · simp [g, hr]
      · simp [g, hr]
    simp_rw [e]
    rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right
      (NNReal.coe_le_coe.2 htT)]
  · refine Integrable.of_bound (C := ∑ k, (hg k).bdd.choose ^ 2) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        (((hg k).sm.mono (predictableSpace_le _)).aestronglyMeasurable).pow 2)
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((hg k).bdd.choose_spec.2 p) 2

end BlockBand.SourceProcess.Stochastic.Uniqueness
