module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.GronwallAbs
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The vector isometry at intermediate times for a general integrator

Setting: `(Ω, 𝓕, P)` with a raw filtration, a vector integrator
`h : IsL2IntegratorVec P 𝓕 Z a` with symmetric PSD density `a` (general vector integral of
`GeneralIntegral/`), horizon `T`, bounded predictable integrands `f`.

* `psd_entry_eq_zero`: a PSD density with nonpositive trace vanishes.
* **`lintegral_sq_vecCont_gen`**: for `t ≤ T`,
  `E ‖∫_0^t f dZ‖² = E ∫_{(0,t]} fᵀ a f dr` (in `ℝ≥0∞`; the canonical representatives are
  identified with `f` where `tr a > 0`, and both quadratic forms vanish where `tr a = 0`).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A PSD symmetric matrix with nonpositive trace vanishes. -/
theorem psd_entry_eq_zero {A : ι → ι → ℝ} (hA : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * A i j)
    (hs : ∀ i j, A i j = A j i) (htr : ∑ i, A i i ≤ 0) (i j : ι) : A i j = 0 := by
  have hdiag : ∀ k, 0 ≤ A k k := fun k => by
    have := hA (Pi.single k 1)
    simpa [Pi.single_apply, ite_mul] using this
  have hzero : ∀ k, A k k = 0 := fun k => by
    have h1 := Finset.single_le_sum (f := fun k => A k k) (fun k _ => hdiag k)
      (Finset.mem_univ k)
    linarith [hdiag k]
  rcases eq_or_ne i j with h | h
  · subst h; exact hzero i
  · have key : ∀ s : ℝ, 0 ≤ 2 * s * A i j := fun s => by
      have := hA (Pi.single i 1 + Pi.single j s)
      have e : ∑ k, ∑ l, (Pi.single i 1 + Pi.single j s : ι → ℝ) k *
          (Pi.single i 1 + Pi.single j s : ι → ℝ) l * A k l =
          A i i + s * A i j + s * A j i + s ^ 2 * A j j := by
        simp [Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib]
        ring
      rw [e, hzero i, hzero j, hs j i] at this
      linarith
    have h1 := key 1
    have h2 := key (-1)
    linarith

variable {P : Measure Ω} [IsFiniteMeasure P] {Z : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ}

/-- **The vector isometry at time `t ≤ T`**, general integrator, `ℝ≥0∞` form. -/
theorem lintegral_sq_vecCont_gen (h : IsL2IntegratorVec P 𝓕 Z a)
    (hs : ∀ i j t ω, a i j t ω = a j i t ω) {T : ℝ≥0} [IsFiniteMeasure (barMeasure P a T)]
    {f : ι → ℝ × Ω → ℝ} (hf : ∀ k, IsBddPred 𝓕 (f k)) {t : ℝ≥0} (htT : t ≤ T) :
    ∫⁻ ω, ‖h.vecCont T (fun k => bpL2 _ (hf k)) t ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ENNReal.ofReal
        (∑ i, ∑ j, f i (r, ω) * f j (r, ω) * a i j r.toNNReal ω)) ∂P := by
  set μ := barMeasure P a T
  have hR := measurableSet_Iic_prod_univ 𝓕 t
  set g : ι → ℝ × Ω → ℝ := fun k => (Iic (t : ℝ) ×ˢ (univ : Set Ω)).indicator (f k)
  have hg : ∀ k, IsBddPred 𝓕 (g k) := fun k => (hf k).indicator hR
  have e1 : (fun k => predInd 𝓕 _ hR (bpL2 μ (hf k))) = fun k => bpL2 μ (hg k) :=
    funext fun k => (bpL2_indicator (hf k) hR).symm
  have h0 := vecIntegral_Iic h T (fun k => bpL2 μ (hf k)) t
  rw [e1] at h0
  set F : (ι → ℝ × Ω → ℝ) → ℝ × Ω → ℝ := fun u p =>
    ∑ i, ∑ j, u i p * u j p * a i j p.1.toNNReal p.2
  have hFnn : ∀ u p, 0 ≤ F u p := fun u p => h.psd _ _ fun i => u i p
  have hfm : ∀ k, Measurable (f k) := fun k => ((hf k).sm.mono (predictableSpace_le _)).measurable
  have hgm : ∀ k, Measurable (g k) := fun k => ((hg k).sm.mono (predictableSpace_le _)).measurable
  have hFm : ∀ u : ι → ℝ × Ω → ℝ, (∀ k, Measurable (u k)) → Measurable (F u) := fun u hu =>
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((hu i).mul (hu j)).mul (h.measurable i j)
  -- identification of the quadratic density
  have hden : Measurable fun p : ℝ × Ω => ENNReal.ofReal (traceA a p.1.toNNReal p.2) :=
    (Finset.measurable_sum _ fun i _ => h.measurable i i).ennreal_ofReal
  have hrep : ∀ᵐ p ∂timeProbMeasure T P, ENNReal.ofReal (traceA a p.1.toNNReal p.2) ≠ 0 →
      ∀ k, ((bpL2 μ (hg k) : PredL2 𝓕 μ) : Lp ℝ 2 μ) p = g k p :=
    (ae_withDensity_iff hden).1 (ae_all_iff.2 fun k => bpL2_coeFn (μ := μ) (hg k))
  have hq : IsL2IntegratorVec.quadDensity T a (fun k => bpL2 μ (hg k)) =ᵐ[timeProbMeasure T P]
      F g := by
    filter_upwards [hrep] with p hp
    by_cases htr : ENNReal.ofReal (traceA a p.1.toNNReal p.2) = 0
    · rw [ENNReal.ofReal_eq_zero] at htr
      have hz := psd_entry_eq_zero (h.psd p.1.toNNReal p.2) (fun i j => hs i j _ _) htr
      simp [IsL2IntegratorVec.quadDensity, F, hz]
    · simp only [IsL2IntegratorVec.quadDensity, F, hp htr]
  have hint : Integrable (F g) (timeProbMeasure T P) :=
    (h.integrable_quadDensity T hs _).congr hq
  have hM : MemLp (h.vecIntegral T fun k => bpL2 μ (hg k)) 2 P := Lp.memLp _
  calc ∫⁻ ω, ‖h.vecCont T (fun k => bpL2 _ (hf k)) t ω‖ₑ ^ 2 ∂P
      = ∫⁻ ω, ‖(h.vecIntegral T fun k => bpL2 μ (hg k)) ω‖ₑ ^ 2 ∂P :=
        lintegral_congr_ae (by filter_upwards [h0] with ω hω; rw [hω])
    _ = ENNReal.ofReal (∫ ω, ((h.vecIntegral T fun k => bpL2 μ (hg k)) ω) ^ 2 ∂P) := by
        simp_rw [enorm_sq_eq_ofReal]
        rw [ofReal_integral_eq_lintegral_ofReal hM.integrable_sq
          (Eventually.of_forall fun _ => sq_nonneg _)]
    _ = ENNReal.ofReal (∫ p, F g p ∂timeProbMeasure T P) := by
        rw [h.integral_sq_vecIntegral T hs, integral_congr_ae hq]
    _ = ∫⁻ p, ENNReal.ofReal (F g p) ∂timeProbMeasure T P :=
        ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (hFnn g))
    _ = ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) T, ENNReal.ofReal (F g (r, ω))) ∂P := by
        rw [timeProbMeasure, lintegral_prod_symm _
          ((hFm g hgm).ennreal_ofReal).aemeasurable]
    _ = _ := by
        refine lintegral_congr fun ω => ?_
        have e : ∀ r : ℝ, ENNReal.ofReal (F g (r, ω)) = (Iic (t : ℝ)).indicator
            (fun r => ENNReal.ofReal (F f (r, ω))) r := fun r => by
          by_cases hr : r ∈ Iic (t : ℝ)
          · simp [F, g, hr]
          · simp [F, g, hr]
        simp_rw [e]
        rw [setLIntegral_indicator measurableSet_Iic, inter_comm, Ioc_inter_Iic,
          min_eq_right (NNReal.coe_le_coe.2 htT)]

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
