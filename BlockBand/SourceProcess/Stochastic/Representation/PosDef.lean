module
public import BlockBand.SourceProcess.Stochastic.Representation.Coord
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Weak-solution representation of martingale-problem solutions, invertible `σ`

Setting: `(Ω, 𝓖, Q)` a probability space with a raw filtration (no usual conditions);
`b : ℝ^d → ℝ^d`, `σ : ℝ^d → ℝ^{d×d}` continuous on an open `U`; `Y` solves the
`(b, σσᵀ)` martingale problem in the domain `V` (`IsMPSolutionOn`); `W` is a relatively
compact subdomain of `V` with `closure W ⊆ U`, and `σ(y)` is invertible for `y ∈ closure W`
(the situation of `StoppedMartingaleProblemUniquenessPosDef`: `a` positive definite, `σ` a square
root of `a`). `τ_W = exitTimeFrom W Y`.
The extension is the Wiener extension `(Ω × C(ℝ≥0,ℝ)^d, 𝓖 ⊗ σ(B'), Q ⊗ Wiener)` of `Levy/`.

**`exists_weak_solution_posDef`**: on the extension there is a filtration Brownian motion `B`
(all times, `IsFiltrationBrownian`), and for every horizon `T` the `L²` integrands
`K_{ik} = 1{s ≤ τ_W} σ_{ik}(Y_s)` (classes in `PredL2` of the extension, with the stated
representatives) satisfy, a.s. simultaneously for all `t ≤ T`,
`Y^i_{t∧τ_W} - Y^i_0 - ∫_0^{t∧τ_W} b_i(Y_s) ds = ∑_k ∫_0^t K_{ik} dB^k`
(the general vector stochastic integral against `B`).

Construction: `M = ` stopped compensated process (`exists_mp_integrator`), joint integrator
`(M, B')` (`jointExtension`), `W = ∫ 1{s≤τ} σ⁻¹(Y) dM + ∫ 1{s>τ} dB'` (bounded integrands since
`σ⁻¹` is bounded on the compact `closure W`), Brownian by `exists_brownian_of_driver`; the
representation follows from associativity (`vecCont_assoc`) and `vecCont_unitStop`.
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

theorem jointA_symm {Ω : Type*} {ι : Type*} {a : ι → ι → ℝ≥0 → Ω → ℝ}
    (hs : ∀ i j t ω, a i j t ω = a j i t ω) (m : ℕ) (i j : ι ⊕ Fin m) (t : ℝ≥0)
    (x : Ω × WienerSpace m) : jointA a m i j t x = jointA a m j i t x := by
  rcases i with i | i <;> rcases j with j | j
  · exact hs i j t x.1
  · rfl
  · rfl
  · simp only [jointA]
    rcases eq_or_ne i j with h | h
    · subst h; rfl
    · simp [h, h.symm]

theorem stopTime_of_le {e : WithTop ℝ≥0} {t : ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ e) :
    stopTime e t = t := by
  apply WithTop.coe_injective
  rw [show ((stopTime e t : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) e from
    coe_untopA_min t e, min_eq_left h]

theorem inv_entry {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (k i : Fin d) :
    A⁻¹ k i = (A.det)⁻¹ * A.adjugate k i := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]

variable {d : ℕ}

/-- The identity bracket density `δ_{kl}`. -/
abbrev idDens (d : ℕ) (X : Type*) : Fin d → Fin d → ℝ≥0 → X → ℝ :=
  fun k l _ _ => if k = l then 1 else 0

/-- A function continuous on the compact `closure W` and measurable, cut off outside
`closure W`, is measurable and bounded. -/
theorem measurable_bdd_indicator {W : Set (Fin d → ℝ)} (hW : IsCompact (closure W))
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (closure W)) (hfm : Measurable f) :
    Measurable ((closure W).indicator f) ∧ ∃ C, 0 ≤ C ∧ ∀ y, |(closure W).indicator f y| ≤ C := by
  refine ⟨hfm.indicator isClosed_closure.measurableSet, ?_⟩
  obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn hf
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ closure W
  · rw [indicator_of_mem hy, ← Real.norm_eq_abs]; exact (hC y hy).trans (le_max_left _ _)
  · rw [indicator_of_notMem hy, abs_zero]; exact le_max_right _ _

/-- **Weak-solution representation of a martingale-problem solution with invertible `σ`.** -/
theorem exists_weak_solution_posDef {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {b : (Fin d → ℝ) → Fin d → ℝ} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {U V W : Set (Fin d → ℝ)} (hU : IsOpen U) (hb : ContinuousOn b U) (hσ : ContinuousOn σ U)
    (hWV : IsInteriorDomain W V) (hWU : closure W ⊆ U)
    (hdet : ∀ y ∈ closure W, IsUnit (σ y).det) {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : IsMPSolutionOn Q 𝓖 b (fun y => σ y * (σ y).transpose) V Y) :
    ∃ B : ℝ≥0 → Ω × WienerSpace d → Fin d → ℝ,
      IsFiltrationBrownian (extMeasure Q d) (extFiltration 𝓖 d) B ∧
      ∃ hB : IsL2IntegratorVec (extMeasure Q d) (extFiltration 𝓖 d) (fun k t x => B t x k)
        (idDens d (Ω × WienerSpace d)),
      ∀ T : ℝ≥0, ∃ K : Fin d → Fin d → PredL2 (extFiltration 𝓖 d)
          (barMeasure (extMeasure Q d) (idDens d (Ω × WienerSpace d)) T),
        (∀ i k, (((K i k : PredL2 (extFiltration 𝓖 d) (barMeasure (extMeasure Q d)
            (idDens d (Ω × WienerSpace d)) T)) : Lp ℝ 2 (barMeasure (extMeasure Q d)
              (idDens d (Ω × WienerSpace d)) T)) : ℝ × (Ω × WienerSpace d) → ℝ) =ᵐ[barMeasure
                (extMeasure Q d) (idDens d (Ω × WienerSpace d)) T]
            fun p => if ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y p.2.1 then
              σ (Y p.1.toNNReal p.2.1) i k else 0) ∧
        ∀ i, ∀ᵐ x ∂extMeasure Q d, ∀ t ≤ T,
          stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y) t x.1 =
            hB.vecCont T (K i) t x := by
  classical
  -- everywhere continuous coefficients agreeing on `closure W`
  obtain ⟨χ, -, -, hχ1, -, hχf⟩ := exists_cutoff hU isClosed_closure hWU
  set b' : (Fin d → ℝ) → Fin d → ℝ := fun y i => χ y * b y i with hb'def
  set σ' : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ := fun y => Matrix.of fun i k => χ y * σ y i k
    with hσ'def
  have hb' : Continuous b' :=
    continuous_pi fun i => hχf _ ((continuous_apply i).comp_continuousOn hb)
  have hσ' : Continuous σ' := continuous_matrix fun i k =>
    hχf _ ((continuous_id.matrix_elem i k).comp_continuousOn hσ)
  have hbb : EqOn b b' (closure W) := fun y hy => funext fun i => by
    simp [hb'def, hχ1 hy]
  have hσσ : EqOn σ σ' (closure W) := fun y hy => Matrix.ext fun i k => by
    simp [hσ'def, hχ1 hy]
  have hdet' : ∀ y ∈ closure W, IsUnit (σ' y).det := fun y hy => by rw [← hσσ hy]; exact hdet y hy
  -- the integrator `M`
  obtain ⟨τ, hτ, hτe, hM⟩ := exists_mp_integrator hWV hb' hσ' hbb hσσ hY
  set a := psdVersion τ (covEntry σ') Y with hadef
  have hs : ∀ i j t ω, a i j t ω = a j i t ω := psdVersion_symm (covEntry_symm σ')
  set M : Fin d → ℝ≥0 → Ω → ℝ := fun i => stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y)
    with hMdef
  have hZ := hM.jointExtension d
  have hZs := jointA_symm hs d
  -- objects on the extension
  set P := extMeasure Q d
  set 𝓕 := extFiltration 𝓖 d
  set Y' : ℝ≥0 → Ω × WienerSpace d → Fin d → ℝ := fun t x => Y t x.1 with hY'def
  have hY' : ∀ t, StronglyMeasurable[𝓕 t] (Y' t) := fun t =>
    (hY.adapted t).comp_measurable (measurable_fst_prodFiltration t)
  set τ' : Ω × WienerSpace d → WithTop ℝ≥0 := fun x => τ x.1 with hτ'def
  have hτ' : IsStoppingTime 𝓕 τ' := fun t => measurable_fst_prodFiltration t (hτ t)
  have hmp := measurePreserving_fst (μ := Q) (ν := commonWienerLaw (Fin d))
  have hcont' : ∀ᵐ x ∂P, Continuous fun t => Y t x.1 :=
    hmp.quasiMeasurePreserving.ae hY.continuous
  have hcl : ∀ x : Ω × WienerSpace d, (Continuous fun t => Y t x.1) → ∀ r : ℝ, 0 < r →
      (r, x) ∈ stopSet τ' → Y r.toNNReal x.1 ∈ closure W := by
    intro x hx r hr hS
    have hS' : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y x.1 := by
      rw [← hτe x.1 hx]; exact hS
    refine (stopped_path_mem_closure hWV.1 hx r.toNNReal).1 r ⟨hr, ?_⟩
    rw [stopTime_of_le hS', Real.coe_toNNReal _ hr.le]
  have hpv : ∀ x : Ω × WienerSpace d, (Continuous fun t => Y t x.1) → ∀ r : ℝ, 0 < r →
      predVersion Y' (r, x) = Y r.toNNReal x.1 := fun x hx r hr =>
    predVersion_eq (p := (r, x)) hx hr
  -- truncated coefficients
  have hψ (k i : Fin d) := measurable_bdd_indicator hWV.2.1
    (f := fun y => (σ' y)⁻¹ k i)
    (by
      have he : (fun y => (σ' y)⁻¹ k i) = fun y => ((σ' y).det)⁻¹ * (σ' y).adjugate k i :=
        funext fun y => inv_entry _ k i
      rw [he]
      exact (hσ'.matrix_det.continuousOn.inv₀ fun y hy => (hdet' y hy).ne_zero).mul
        (hσ'.matrix_adjugate.matrix_elem k i).continuousOn)
    (by
      have he : (fun y => (σ' y)⁻¹ k i) = fun y => ((σ' y).det)⁻¹ * (σ' y).adjugate k i :=
        funext fun y => inv_entry _ k i
      rw [he]
      exact (hσ'.matrix_det.measurable.inv).mul
        (hσ'.matrix_adjugate.matrix_elem k i).measurable)
  have hσh (i k : Fin d) := measurable_bdd_indicator hWV.2.1 (f := fun y => σ' y i k)
    (hσ'.matrix_elem i k).continuousOn (hσ'.matrix_elem i k).measurable
  set ψ : Fin d → Fin d → (Fin d → ℝ) → ℝ := fun k i => (closure W).indicator fun y => (σ' y)⁻¹ k i
  set σh : Fin d → Fin d → (Fin d → ℝ) → ℝ := fun i k => (closure W).indicator fun y => σ' y i k
  have hS := measurableSet_stopSet 𝓕 hτ'
  have hbddpv {g : (Fin d → ℝ) → ℝ} (hg : Measurable g ∧ ∃ C, 0 ≤ C ∧ ∀ y, |g y| ≤ C) :
      IsBddPred 𝓕 ((stopSet τ').indicator fun p => g (predVersion Y' p)) := by
    obtain ⟨C, hC0, hC⟩ := hg.2
    exact (⟨stronglyMeasurable_comp_predVersion 𝓕 hY' hg.1, C, hC0, fun p => hC _⟩ :
      IsBddPred 𝓕 fun p => g (predVersion Y' p)).indicator hS
  -- the driver integrand `H`
  set H : Fin d → Fin d ⊕ Fin d → ℝ × (Ω × WienerSpace d) → ℝ := fun k j => Sum.elim
    (fun i => (stopSet τ').indicator fun p => ψ k i (predVersion Y' p))
    (fun l => (stopSet τ')ᶜ.indicator fun _ => if k = l then 1 else 0) j with hHdef
  have hH : ∀ k j, IsBddPred 𝓕 (H k j) := by
    intro k j
    rcases j with i | l
    · exact hbddpv (hψ k i)
    · exact (IsBddPred.const _).indicator hS.compl
  have hinl : ∀ k i p, H k (Sum.inl i) p =
      if p ∈ stopSet τ' then ψ k i (predVersion Y' p) else 0 := fun k i p => by
    simp only [hHdef, Sum.elim_inl, Set.indicator_apply]
  have hinr : ∀ k l p, H k (Sum.inr l) p =
      if p ∈ stopSet τ' then 0 else (if k = l then 1 else 0) := fun k l p => by
    simp only [hHdef, Sum.elim_inr, Set.indicator_apply, mem_compl_iff]
    by_cases hp : p ∈ stopSet τ' <;> simp [hp]
  -- identity bracket density
  have hHaH : ∀ᵐ x ∂P, ∀ r : ℝ, 0 < r → ∀ k l,
      ∑ i, ∑ j, H k i (r, x) * H l j (r, x) * jointA a d i j r.toNNReal x =
        if k = l then 1 else 0 := by
    filter_upwards [hcont'] with x hx r hr k l
    simp only [Fintype.sum_sum_type, hinl, hinr, jointA]
    by_cases hSr : (r, x) ∈ stopSet τ'
    · have hy := hcl x hx r hr hSr
      have hτr : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x.1 := hSr
      simp only [hSr, ite_true, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
      have ha (i j : Fin d) : a i j r.toNNReal x.1 = (σ' (Y r.toNNReal x.1) *
          (σ' (Y r.toNNReal x.1)).transpose) i j := by
        rw [hadef, psdVersion_eq (continuous_covEntry hσ') hx (Real.toNNReal_pos.2 hr) i j,
          ite_eq_left_of_eq_true _ _ (eq_true hτr), covEntry_eq]
      simp only [ha, hpv x hx r hr, ψ, indicator_of_mem hy]
      exact inv_cov_inv (hdet' _ hy) k l
    · simp only [hSr, ite_false, zero_mul, mul_zero, Finset.sum_const_zero, zero_add]
      by_cases hkl : k = l
      · subst hkl; simp
      · simp [hkl]
  -- the Brownian motion
  obtain ⟨B, hBM, hBX⟩ := exists_brownian_of_driver hZ hH hZs hHaH
  have hB := hBM.isL2IntegratorVec
  refine ⟨B, hBM, hB, fun T => ?_⟩
  have := hZ.isFiniteMeasure_bar T
  have := hB.isFiniteMeasure_bar T
  have hK : ∀ i k, IsBddPred 𝓕 ((stopSet τ').indicator fun p => σh i k (predVersion Y' p)) :=
    fun i k => hbddpv (hσh i k)
  refine ⟨fun i k => bpL2 _ (hK i k), fun i k => ?_, fun i => ?_⟩
  · -- the representative of `K`
    have hac := bracketMeasure_absolutelyContinuous P (traceA (idDens d (Ω × WienerSpace d))) T
    filter_upwards [bpL2_coeFn (μ := barMeasure P (idDens d (Ω × WienerSpace d)) T) (hK i k), hac.ae_le (ae_timeProb_snd (T := T) hcont'), hac.ae_le (ae_timeProb_mem P T)]
      with p h1 h2 h3
    rw [h1]
    have hr : 0 < p.1 := h3.1
    have hiff : p ∈ stopSet τ' ↔
        ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y p.2.1 := by
      rw [mem_stopSet, ← hτe p.2.1 h2]
    by_cases hSp : p ∈ stopSet τ'
    · have hy := hcl p.2 h2 p.1 hr hSp
      rw [indicator_of_mem hSp, ite_eq_left_of_eq_true _ _ (eq_true (hiff.1 hSp)), hpv p.2 h2 p.1 hr]
      simp only [σh, indicator_of_mem hy, ← hσσ hy]
    · rw [indicator_of_notMem hSp, ite_eq_right_of_eq_false _ _ (eq_false (fun h => hSp (hiff.2 h)))]
  · -- the representation
    have hassoc := vecCont_assoc hZ hB T hH (fun k t ht => hBX T k t ht) (hK i)
    have hunit := vecCont_unitStop hZ T hτ' (Sum.inl i)
    have hG : (fun j => bpL2 (barMeasure P (jointA a d) T)
        (IsBddPred.sum Finset.univ fun k => (hH k j).mul (hK i k))) =
        fun j => bpL2 (barMeasure P (jointA a d) T) (isBddPred_unitStop hτ' (Sum.inl i) j) := by
      funext j
      refine bpL2_congr _ _ ?_
      have hac := bracketMeasure_absolutelyContinuous P (traceA (jointA a d)) T
      filter_upwards [hac.ae_le (ae_timeProb_snd (T := T) hcont'),
        hac.ae_le (ae_timeProb_mem P T)] with p h2 h3
      have hr : 0 < p.1 := h3.1
      rcases j with j | l
      · simp only [hinl, Set.indicator_apply]
        by_cases hSp : p ∈ stopSet τ'
        · have hy := hcl p.2 h2 p.1 hr hSp
          simp only [hSp, ite_true, hpv p.2 h2 p.1 hr, ψ, σh, indicator_of_mem hy,
            Sum.inl.injEq]
          rw [show (∑ k, (σ' (Y p.1.toNNReal p.2.1))⁻¹ k j * σ' (Y p.1.toNNReal p.2.1) i k) =
              ∑ k, σ' (Y p.1.toNNReal p.2.1) i k * (σ' (Y p.1.toNNReal p.2.1))⁻¹ k j from
            Finset.sum_congr rfl fun k _ => mul_comm _ _, mul_inv_entry (hdet' _ hy) i j]
          by_cases hij : i = j
          · simp [hij]
          · simp [hij, Ne.symm hij]
        · simp [hSp]
      · simp only [hinr, Set.indicator_apply]
        by_cases hSp : p ∈ stopSet τ' <;> simp [hSp]
    filter_upwards [hassoc, hunit, hcont'] with x h1 h2 hx t ht
    rw [h1 t, hG, h2 t ht]
    simp only [jointN]
    have h0 : M i 0 x.1 = 0 := by
      simp [hMdef, stoppedProcess_eq_stopTime, mpCompensated,
        le_antisymm (stopTime_le _ 0) zero_le]
    rw [h0, sub_zero]
    simp only [hMdef, hτ'def, stoppedProcess_eq_stopTime, hτe x.1 hx, stopTime_stopTime]

end BlockBand.SourceProcess.Stochastic.Representation
