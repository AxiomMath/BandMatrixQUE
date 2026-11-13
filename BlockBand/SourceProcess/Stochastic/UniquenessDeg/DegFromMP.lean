module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegSetup
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegDriver
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegMeas
public import BlockBand.SourceProcess.Stochastic.Representation.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A degenerate martingale-problem solution gives a degenerate setup

Setting: `(Ω, 𝓖, Q)` with `Ω : Type u` (any universe), a raw filtration; `Y` solves the
`(b, σσᵀ)` martingale problem in `V`; `W` a relatively compact subdomain of `V`; bounded globally
Lipschitz `c` with `c.b = b`, `c.σ = σ` on `closure W`.

**`exists_degSetup`**: on the Wiener extension `(Ω × C(ℝ≥0,ℝ)^{2d}, Q ⊗ Wiener)` there is a
`DegSetup c W` with process `Y ∘ fst`, initial value `Y_0 ∘ fst` and stopping time
`exitTimeFrom W Y ∘ fst` on continuous paths. Construction: the joint integrator
`Z = (M, B')` (`exists_mp_integrator` with `c.b, c.σ`, `jointExtension`), density
`jointA = zDens(1_{[[0,τ]]} c.σ(Y))` (`psdVersion_eq`); for every `n` the integrand
`H n = hval(c.σ(Y)) ε_n` on `[[0,τ]]` and `offval` after (bounded on `closure W`, predictable
through `predVersion`), with identity bracket (`bil_hval`, `bil_offval`), so
`Bd n = ∫ H n dZ` is a filtration Brownian motion (`exists_brownian_of_driver`, Lévy). No
pseudoinverse integrand is needed.
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {d : ℕ}

/-- **A degenerate setup from a martingale-problem solution.** -/
theorem exists_degSetup {b : (Fin d → ℝ) → Fin d → ℝ}
    {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {V W : Set (Fin d → ℝ)}
    (hWV : IsInteriorDomain W V) {c : LipCoef d}
    (hcb : EqOn b c.b (closure W)) (hcσ : EqOn σ c.σ (closure W))
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : IsMPSolutionOn Q 𝓖 b (fun y => σ y * (σ y).transpose) V Y) :
    ∃ S : DegSetup c W (extMeasure Q (d + d)), S.Y = (fun t x => Y t x.1) ∧
      S.ξ = (fun x => Y 0 x.1) ∧
      ∀ x : Ω × WienerSpace (d + d), (Continuous fun t => Y t x.1) →
        S.τ x = exitTimeFrom W Y x.1 := by
  classical
  obtain ⟨τ, hτ, hτe, hM⟩ := exists_mp_integrator hWV c.continuous_b c.continuous_σ hcb hcσ hY
  set a := psdVersion τ (covEntry c.σ) Y with hadef
  have hs : ∀ i j t ω, a i j t ω = a j i t ω := psdVersion_symm (covEntry_symm c.σ)
  set M : Fin d → ℝ≥0 → Ω → ℝ := fun i => stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y)
    with hMdef
  have hZ := hM.jointExtension (d + d)
  have hZs := jointA_symm hs (d + d)
  set P := extMeasure Q (d + d)
  set 𝓕 := extFiltration 𝓖 (d + d)
  set Y' : ℝ≥0 → Ω × WienerSpace (d + d) → Fin d → ℝ := fun t x => Y t x.1 with hY'def
  have hY' : ∀ t, StronglyMeasurable[𝓕 t] (Y' t) := fun t =>
    (hY.adapted t).comp_measurable (measurable_fst_prodFiltration t)
  set τ' : Ω × WienerSpace (d + d) → WithTop ℝ≥0 := fun x => τ x.1 with hτ'def
  have hτ' : IsStoppingTime 𝓕 τ' := fun t => measurable_fst_prodFiltration t (hτ t)
  have hmp := measurePreserving_fst (μ := Q) (ν := commonWienerLaw (Fin (d + d)))
  have hcont' : ∀ᵐ x ∂P, Continuous fun t => Y t x.1 :=
    hmp.quasiMeasurePreserving.ae hY.continuous
  have hcl : ∀ x : Ω × WienerSpace (d + d), (Continuous fun t => Y t x.1) → ∀ r : ℝ, 0 < r →
      (r, x) ∈ stopSet τ' → Y r.toNNReal x.1 ∈ closure W := by
    intro x hx r hr hS
    have hS' : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y x.1 := by
      rw [← hτe x.1 hx]; exact hS
    refine (stopped_path_mem_closure hWV.1 hx r.toNNReal).1 r ⟨hr, ?_⟩
    rw [stopTime_of_le hS', Real.coe_toNNReal _ hr.le]
  have hpv : ∀ x : Ω × WienerSpace (d + d), (Continuous fun t => Y t x.1) → ∀ r : ℝ, 0 < r →
      predVersion Y' (r, x) = Y r.toNNReal x.1 := fun x hx r hr =>
    predVersion_eq (p := (r, x)) hx hr
  have hS := measurableSet_stopSet 𝓕 hτ'
  have hbddpv {g : (Fin d → ℝ) → ℝ} (hg : Measurable g ∧ ∃ C, 0 ≤ C ∧ ∀ y, |g y| ≤ C) :
      IsBddPred 𝓕 ((stopSet τ').indicator fun p => g (predVersion Y' p)) := by
    obtain ⟨C, hC0, hC⟩ := hg.2
    exact (⟨stronglyMeasurable_comp_predVersion 𝓕 hY' hg.1, C, hC0, fun p => hC _⟩ :
      IsBddPred 𝓕 fun p => g (predVersion Y' p)).indicator hS
  have hg (n : ℕ) (k : Fin d) (c' : Fin d ⊕ Fin (d + d)) :=
    measurable_bdd_indicator hWV.2.1 (f := fun y => hval (c.σ y) (regSeq n) k c')
      ((continuous_hval (regSeq_pos n) k c').comp c.continuous_σ).continuousOn
      ((continuous_hval (regSeq_pos n) k c').comp c.continuous_σ).measurable
  -- the driver integrands
  set H : ℕ → Fin d → Fin d ⊕ Fin (d + d) → ℝ × (Ω × WienerSpace (d + d)) → ℝ :=
    fun n k c' p => (stopSet τ').indicator (fun p => (closure W).indicator
      (fun y => hval (c.σ y) (regSeq n) k c') (predVersion Y' p)) p +
        (stopSet τ')ᶜ.indicator (fun _ => offval k c') p with hHdef
  have hH : ∀ n k c', IsBddPred 𝓕 (H n k c') := fun n k c' =>
    (hbddpv (hg n k c')).add ((IsBddPred.const _).indicator hS.compl)
  have hHval : ∀ x : Ω × WienerSpace (d + d), (Continuous fun t => Y t x.1) → ∀ r : ℝ, 0 < r →
      ∀ n k c', H n k c' (r, x) = if (r, x) ∈ stopSet τ' then
        hval (c.σ (Y r.toNNReal x.1)) (regSeq n) k c' else offval k c' := by
    intro x hx r hr n k c'
    by_cases hSr : (r, x) ∈ stopSet τ'
    · have hc : (r, x) ∉ (stopSet τ')ᶜ := fun h => h hSr
      simp only [hHdef, indicator_of_mem hSr, hpv x hx r hr, indicator_of_mem (hcl x hx r hr hSr),
        indicator_of_notMem hc, add_zero, hSr, ite_true]
    · simp only [hHdef, indicator_of_notMem hSr, indicator_of_mem (mem_compl hSr), zero_add, hSr,
        ite_false]
  have haZv : ∀ x : Ω × WienerSpace (d + d), (Continuous fun t => Y t x.1) → ∀ r : ℝ, 0 < r →
      ∀ c₁ c₂, jointA a (d + d) c₁ c₂ r.toNNReal x = zDens (if (r, x) ∈ stopSet τ' then
        c.σ (Y r.toNNReal x.1) else 0) c₁ c₂ := by
    intro x hx r hr c₁ c₂
    rcases c₁ with i | k <;> rcases c₂ with j | l
    · simp only [jointA]
      rw [hadef, psdVersion_eq (continuous_covEntry c.continuous_σ) hx (Real.toNNReal_pos.2 hr) i j,
        covEntry_eq]
      by_cases hSr : (r, x) ∈ stopSet τ'
      · have hτr : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x.1 := hSr
        simp only [hτr, hSr, ite_true, zDens, Sum.elim_inl]
      · have hτr : ¬ ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x.1 := hSr
        rw [ite_eq_right hτr]
        simp [hSr, zDens]
    · simp [jointA, zDens]
    · simp [jointA, zDens]
    · simp [jointA, zDens]
  have hHaH : ∀ n, ∀ᵐ x ∂P, ∀ r : ℝ, 0 < r → ∀ k l,
      ∑ i, ∑ j, H n k i (r, x) * H n l j (r, x) * jointA a (d + d) i j r.toNNReal x =
        if k = l then 1 else 0 := by
    intro n
    filter_upwards [hcont'] with x hx r hr k l
    simp only [hHval x hx r hr, haZv x hx r hr]
    by_cases hSr : (r, x) ∈ stopSet τ'
    · simp only [hSr, ite_true]
      exact bil_hval _ (regSeq_pos n) k l
    · simp only [hSr, ite_false]
      exact bil_offval k l
  -- the Brownian drivers
  choose Bd hBd hBX using fun n => exists_brownian_of_driver hZ (hH n) hZs (hHaH n)
  have hξ : Measurable[𝓕 0] (fun x : Ω × WienerSpace (d + d) => Y 0 x.1) :=
    (hY.adapted 0).measurable.comp (measurable_fst_prodFiltration 0)
  have hτe' : ∀ᵐ x ∂P, τ' x = exitTimeFrom W Y' x := by
    filter_upwards [hcont'] with x hx using hτe x.1 hx
  refine ⟨DegSetup.mk 𝓕 (fun x => Y 0 x.1) τ' Y' (jointN M (d + d)) (jointA a (d + d)) Bd H
    hZ hZs hH hBd (fun n T k t ht => hBX n T k t ht) hξ hτ' hτe'
    (fun t => ((hY.adapted t).mono (𝓖.le t)).measurable.comp measurable_fst) hcont'
    ?_ ?_ ?_, rfl, rfl, fun x hx => hτe x.1 hx⟩
  · -- the representation of the stopped solution
    intro n
    have := hZ.isFiniteMeasure_bar (n : ℝ≥0)
    filter_upwards [ae_all_iff.2 fun i => vecCont_unitStop hZ (n : ℝ≥0) hτ' (Sum.inl i),
      hcont'] with x hx hc t ht i
    rw [hx i t ht]
    simp only [jointN]
    have h0 : M i 0 x.1 = 0 := by
      simp [hMdef, stoppedProcess_eq_stopTime, mpCompensated,
        le_antisymm (stopTime_le _ 0) zero_le]
    rw [h0, sub_zero]
    simp only [hMdef]
    rw [stopped_mpCompensated_congr hWV.1 hcb hc i]
    simp only [stoppedProcess_eq_stopTime, mpCompensated, hτ'def, hY'def]
    rw [← hτe x.1 hc, stopTime_stopTime]
    have e2 : ∫ r in Ioc (0 : ℝ) t, (stopSet τ').indicator
        (fun p => c.b (Y p.1.toNNReal p.2.1) i) (r, x) =
        ∫ r in Ioc (0 : ℝ) (stopTime (τ x.1) t), c.b (Y r.toNNReal x.1) i := by
      have e3 : ∫ r in Ioc (0 : ℝ) t, (stopSet τ').indicator
          (fun p => c.b (Y p.1.toNNReal p.2.1) i) (r, x) =
          ∫ r in Ioc (0 : ℝ) t, (Iic (stopTime (τ x.1) t : ℝ)).indicator
            (fun r => c.b (Y r.toNNReal x.1) i) r := by
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        by_cases h : r ≤ stopTime (τ x.1) t
        · rw [indicator_of_mem ((mem_stopSet_iff_le_stopTime (τ := τ') hr).2 h),
            indicator_of_mem (show r ∈ Iic (stopTime (τ x.1) t : ℝ) from h)]
        · rw [indicator_of_notMem (fun h' => h ((mem_stopSet_iff_le_stopTime (τ := τ') hr).1 h')),
            indicator_of_notMem (show r ∉ Iic (stopTime (τ x.1) t : ℝ) from h)]
      rw [e3, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic,
        min_eq_right (NNReal.coe_le_coe.2 (stopTime_le _ _))]
    rw [e2]
    ring
  · filter_upwards [hcont'] with x hx r hr c₁ c₂ using haZv x hx r hr c₁ c₂
  · filter_upwards [hcont'] with x hx r hr n k c' using hHval x hx r hr n k c'

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
