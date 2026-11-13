module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.LocalLawMain
public import BlockBand.SourceProcess.Stochastic.Representation.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A martingale-problem solution gives an Euler setup on the Wiener extension

Setting: `(Ω, 𝓖, Q)` with `Ω : Type`, a raw filtration; `Y` solves the `(b, σσᵀ)` martingale
problem in `V` (`IsMPSolutionOn`); `W` a relatively compact subdomain of `V` with
`closure W ⊆ U`, `b, σ` continuous on the open `U`, `σ` invertible on `closure W`; bounded
globally Lipschitz `c` with `c.b = b`, `c.σ = σ` on `closure W`.

**`exists_eulerSetup`**: on the Wiener extension `(Ω × C(ℝ≥0,ℝ)^d, Q ⊗ Wiener)` there is an
`EulerSetup c W` whose process is `Y ∘ fst`, initial value `Y_0 ∘ fst`, and stopping time equal
to `exitTimeFrom W Y ∘ fst` on continuous paths. The stopping time is the raw hitting time of
`Wᶜ` (`exists_stoppingTime_ae_eq_hitTime`); the diffusion integrand is
`1_{[[0,τ]]} c.σ(predVersion Y)` (identified a.e. with the classes `K` of the representation
theorem); the drift
`∫_0^{t∧τ} b(Y)` is rewritten as `∫_0^t 1_{[[0,τ]]} c.b(Y)`.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {d : ℕ}

/-- **An Euler setup from a martingale-problem solution.** -/
theorem exists_eulerSetup {b : (Fin d → ℝ) → Fin d → ℝ}
    {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {U V W : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hb : ContinuousOn b U) (hσ : ContinuousOn σ U) (hWV : IsInteriorDomain W V)
    (hWU : closure W ⊆ U) (hdet : ∀ y ∈ closure W, IsUnit (σ y).det) {c : LipCoef d}
    (hcb : EqOn b c.b (closure W)) (hcσ : EqOn σ c.σ (closure W))
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : IsMPSolutionOn Q 𝓖 b (fun y => σ y * (σ y).transpose) V Y) :
    ∃ S : EulerSetup c W (extMeasure Q d), S.Y = (fun t x => Y t x.1) ∧
      S.ξ = (fun x => Y 0 x.1) ∧
      ∀ x : Ω × WienerSpace d, (Continuous fun t => Y t x.1) →
        S.τ x = exitTimeFrom W Y x.1 := by
  classical
  obtain ⟨B, hBM, hB, hrepK⟩ := exists_weak_solution_posDef hU hb hσ hWV hWU hdet hY
  obtain ⟨τ, hτ, hτc, -⟩ := exists_stoppingTime_ae_eq_hitTime (Q := Q) (F := Wᶜ)
    (fun t => (hY.adapted t).measurable) hY.continuous hWV.1.isClosed_compl
  have hτe : ∀ ω, (Continuous fun t => Y t ω) → τ ω = exitTimeFrom W Y ω := fun ω h => hτc ω h
  set P := extMeasure Q d
  set 𝓕 := extFiltration 𝓖 d
  set Y' : ℝ≥0 → Ω × WienerSpace d → Fin d → ℝ := fun t x => Y t x.1
  have hY' : ∀ t, StronglyMeasurable[𝓕 t] (Y' t) := fun t =>
    (hY.adapted t).comp_measurable (measurable_fst_prodFiltration t)
  set τ' : Ω × WienerSpace d → WithTop ℝ≥0 := fun x => τ x.1
  have hτ' : IsStoppingTime 𝓕 τ' := fun t => measurable_fst_prodFiltration t (hτ t)
  have hcont' : ∀ᵐ x ∂P, Continuous fun t => Y t x.1 :=
    (measurePreserving_fst (μ := Q) (ν := commonWienerLaw (Fin d))).quasiMeasurePreserving.ae
      hY.continuous
  have hS := measurableSet_stopSet 𝓕 hτ'
  have hσm : ∀ i l, Measurable fun y => c.σ y i l := fun i l =>
    ((continuous_apply l).comp ((continuous_apply i).comp c.continuous_σ)).measurable
  set γY : Fin d → Fin d → ℝ × (Ω × WienerSpace d) → ℝ := fun i l =>
    (stopSet τ').indicator fun p => c.σ (predVersion Y' p) i l
  have hγY : ∀ i l, IsBddPred 𝓕 (γY i l) := fun i l =>
    (⟨stronglyMeasurable_comp_predVersion 𝓕 hY' (hσm i l), c.M, c.M_nonneg,
      fun p => c.bd_σ _ i l⟩ : IsBddPred 𝓕 fun p => c.σ (predVersion Y' p) i l).indicator hS
  have hcl : ∀ x : Ω × WienerSpace d, (Continuous fun t => Y t x.1) → ∀ r : ℝ, 0 < r →
      (r, x) ∈ stopSet τ' → Y r.toNNReal x.1 ∈ closure W := by
    intro x hx r hr hS'
    have hS'' : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y x.1 := by
      rw [← hτe x.1 hx]; exact hS'
    refine (stopped_path_mem_closure hWV.1 hx r.toNNReal).1 r ⟨hr, ?_⟩
    rw [stopTime_of_le hS'', Real.coe_toNNReal _ hr.le]
  have hτe' : ∀ᵐ x ∂P, τ' x = exitTimeFrom W Y' x := by
    filter_upwards [hcont'] with x hx using hτe x.1 hx
  refine ⟨EulerSetup.mk 𝓕 B (fun x => Y 0 x.1) τ' Y' γY hBM
    ((hY.adapted 0).measurable.comp (measurable_fst_prodFiltration 0)) hτ' hτe'
    (fun t => ((hY.adapted t).mono (𝓖.le t)).measurable.comp measurable_fst) hcont' hγY
    ?_ ?_, rfl, rfl, fun x hx => hτe x.1 hx⟩
  · filter_upwards [hcont'] with x hx r hr i l
    simp only [γY, indicator_apply]
    split_ifs
    · rw [predVersion_eq (p := (r, x)) hx hr]
    · rfl
  · intro n
    have := hBM.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
    obtain ⟨K, hKrep, hKid⟩ := hrepK n
    have hK : ∀ i, (fun l => bpL2 (barMeasure P (idDens d (Ω × WienerSpace d)) n)
        (hγY i l)) = K i := fun i => funext fun l => by
      refine predL2_ext 𝓕 ?_
      have hac := bracketMeasure_absolutelyContinuous P (traceA (idDens d (Ω × WienerSpace d)))
        (n : ℝ≥0)
      filter_upwards [bpL2_coeFn (μ := barMeasure P (idDens d (Ω × WienerSpace d)) n)
          (hγY i l), hKrep i l, hac.ae_le (ae_timeProb_snd (T := (n : ℝ≥0)) hcont'),
          hac.ae_le (ae_timeProb_mem P (n : ℝ≥0))] with p h1 h2 h3 h4
      rw [h1, h2]
      have hr : 0 < p.1 := h4.1
      have hiff : p ∈ stopSet τ' ↔
          ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y p.2.1 := by
        rw [mem_stopSet, ← hτe p.2.1 h3]
      by_cases hp : p ∈ stopSet τ'
      · have hy := hcl p.2 h3 p.1 hr hp
        rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.1 hp))]
        simp only [γY, indicator_of_mem hp]
        rw [predVersion_eq (p := p) h3 hr, ← hcσ hy]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hp (hiff.2 h))]
        simp only [γY, indicator_of_notMem hp]
    filter_upwards [ae_all_iff.2 hKid, hcont'] with x hx hc t ht i
    rw [hK i, ← hx i t ht, stopped_mpCompensated_congr hWV.1 hcb hc i t]
    simp only [stoppedProcess_eq_stopTime, mpCompensated]
    rw [← hτe x.1 hc]
    have hs : stopTime (τ x.1) t ≤ t := stopTime_le _ _
    have e2 : ∫ r in Ioc (0 : ℝ) t, (stopSet τ').indicator
        (fun p => c.b (Y' p.1.toNNReal p.2) i) (r, x) =
        ∫ r in Ioc (0 : ℝ) (stopTime (τ x.1) t), c.b (Y r.toNNReal x.1) i := by
      have e3 : ∫ r in Ioc (0 : ℝ) t, (stopSet τ').indicator
          (fun p => c.b (Y' p.1.toNNReal p.2) i) (r, x) =
          ∫ r in Ioc (0 : ℝ) t, (Iic (stopTime (τ x.1) t : ℝ)).indicator
            (fun r => c.b (Y r.toNNReal x.1) i) r := by
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        by_cases h : r ≤ stopTime (τ x.1) t
        · rw [indicator_of_mem ((mem_stopSet_iff_le_stopTime (τ := τ') hr).2 h),
            indicator_of_mem (show r ∈ Iic (stopTime (τ x.1) t : ℝ) from h)]
        · rw [indicator_of_notMem (fun h' => h ((mem_stopSet_iff_le_stopTime (τ := τ') hr).1 h')),
            indicator_of_notMem (show r ∉ Iic (stopTime (τ x.1) t : ℝ) from h)]
      rw [e3, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
        min_eq_right (NNReal.coe_le_coe.2 hs)]
    rw [e2]
    ring

end BlockBand.SourceProcess.Stochastic.Uniqueness
