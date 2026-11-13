module

public import BlockBand.SourceProcess.ModelExist.TransRep

/-!
# The born congruence of a Gram martingale-problem solution is a born Gram solution

`isBornGramSolution_bornG`: for a progressive Gram martingale-problem solution `𝒢` and born
congruence matrices `L_t` with `L_t D L_t* = D'`, the transform `bornG 𝒢 θ lam` is a born Gram
solution, provided it almost surely represents the births.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.BornUnique
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {c c' F : Type*} [Fintype c] [DecidableEq c] [Fintype c'] [Fintype F]
  {D0 : ℝ} {D : Matrix c c ℂ} {D' : Matrix c' c' ℂ}
  {𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ} {θ : c → Ω → ℝ≥0} {lam : c → Ω → c' → ℂ}
  {j : F → Matrix c c ℂ × Matrix c c ℂ} {β : F → Ω → ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] [DecidableEq c] [Fintype c'] in
theorem norm_entry_bJ_le (t : ℝ≥0) (ω : Ω) (e : Fin 2 × c × c) :
    ‖gramEntry e (bJ j β t ω)‖ ≤ ∑ f, ∑ e', ‖gramEntry e' (j f)‖ := by
  have h : gramEntry e (bJ j β t ω) = ∑ f, if β f ω ≤ t then gramEntry e (j f) else 0 := by
    simp only [bJ, birthSum, gramEntry, Prod.fst_sum, Prod.snd_sum, Matrix.sum_apply]
    split_ifs <;> refine Finset.sum_congr rfl fun f _ => ?_ <;> split_ifs <;> simp
  rw [h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  split_ifs
  · exact Finset.single_le_sum (f := fun e' => ‖gramEntry e' (j f)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ e)
  · simpa using Finset.sum_nonneg fun e' _ => norm_nonneg (gramEntry e' (j f))

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] [Fintype c] [DecidableEq c] [Fintype c']
  [Fintype F] in
theorem bornRep_zero [Fintype c'] (N : Fin 2 × c' × c' → ℝ≥0 → Ω → ℂ) (e : Fin 2 × c × c)
    (ω : Ω) : bornRep θ lam N e 0 ω = 0 := by
  have h0 : ∀ r : WithTop ℝ≥0, stopTime r 0 = 0 := fun r => le_antisymm (stopTime_le _ 0) zero_le
  simp [bornRep, stoppedProcess_eq_stopTime, h0]

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
/-- The covariance integrals of `G` and of the transform agree (they differ at one time). -/
theorem integral_cov_bornG (hsig : ∀ t ω, bornL θ lam t ω * D * (bornL θ lam t ω)ᴴ = D')
    (e e' : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) :
    ∫ s in Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (bornG 𝒢 θ lam s.toNNReal ω) =
      ∫ s in Ioc (0 : ℝ) t, ∑ x, ∑ x', ∑ z, ∑ z',
        (if max (bTime θ e ω) (bTime θ e' ω) < ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) then
          bCoef lam e ω x x' * bCoef lam e' ω z z' *
            gramCovEntry D0 D' (e.1, x, x') (e'.1, z, z') (𝒢 s.toNNReal ω) else 0) := by
  set m : ℝ≥0 := max (max (θ e.2.1 ω) (θ e.2.2 ω)) (max (θ e'.2.1 ω) (θ e'.2.2 ω))
  have hm : max (bTime θ e ω) (bTime θ e' ω) = (m : WithTop ℝ≥0) := by
    simp only [bTime, m, WithTop.coe_max]
  refine integral_congr_ae ?_
  have hne : ∀ᵐ v ∂(volume.restrict (Ioc (0 : ℝ) t)), v ≠ (m : ℝ) := Measure.ae_ne _ _
  filter_upwards [hne, ae_restrict_mem measurableSet_Ioc] with v hv hvI
  have hv' : v.toNNReal ≠ m := fun h => hv (by rw [← h, Real.coe_toNNReal _ hvI.1.le])
  rw [gramCovEntry_bornG D0 𝒢 hsig, hm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (WithTop.coe_lt_coe.2 (lt_of_le_of_ne (WithTop.coe_le_coe.1 h1)
      (Ne.symm hv'))) h2
  · exact absurd h2.le h1
  · simp

theorem isBornGramSolution_bornG (h𝒢 : IsGramMartingaleSolution Q 𝓖 D0 D' 𝒢)
    (hp : IsStronglyProgressive 𝓖 𝒢) (hθ : ∀ y, Measurable[𝓖 0] (θ y))
    (hlam : ∀ y, StronglyMeasurable[(isStoppingTime_of_meas0 (hθ y)).measurableSpace] (lam y))
    (hsig : ∀ t ω, bornL θ lam t ω * D * (bornL θ lam t ω)ᴴ = D')
    (hj : ∀ f, 0 ≤ ((j f).1.trace).re) (hβ : ∀ f, Measurable[𝓖 0] (β f))
    (hrep : ∀ᵐ ω ∂Q, BornRepresents 𝒢 θ lam j β ω) :
    IsBornGramSolution Q 𝓖 D0 D (bJ j β) (bornG 𝒢 θ lam) := by
  have hGa : ∀ t, StronglyMeasurable[𝓖 t] (bornG 𝒢 θ lam t) :=
    stronglyMeasurable_bornG h𝒢.adapted hθ hlam
  have hcont : ∀ᵐ ω ∂Q, Continuous fun t => bornG 𝒢 θ lam t ω - bJ j β t ω := by
    filter_upwards [hrep, h𝒢.continuous] with ω hr hc
    refine continuous_of_entries fun e => ?_
    have e1 : (fun t => gramEntry e (bornG 𝒢 θ lam t ω - bJ j β t ω)) = fun t =>
        gramEntry e (bornG 𝒢 θ lam 0 ω - bJ j β 0 ω) + ∑ x, ∑ x', bCoef lam e ω x x' *
          (gramEntry (e.1, x, x') (𝒢 t ω) -
            gramEntry (e.1, x, x') (𝒢 (stopTime (bTime θ e ω) t) ω)) := by
      funext t; rw [← hr t e]; ring
    rw [e1]
    refine continuous_const.add (continuous_finsetSum _ fun x _ =>
      continuous_finsetSum _ fun x' _ => continuous_const.mul ?_)
    exact ((continuous_gramEntry _).comp hc).sub
      (((continuous_gramEntry _).comp hc).comp (continuous_stopTime _))
  have hfeas : ∀ᵐ ω ∂Q, ∀ t, GramFeasible D (bornG 𝒢 θ lam t ω) := by
    filter_upwards [h𝒢.feasible] with ω h t
    exact gramFeasible_congr (hsig t ω) (h t)
  have hgood : ∀ᵐ ω ∂Q, BornRepresents 𝒢 θ lam j β ω ∧ (Continuous fun t => 𝒢 t ω) ∧
      (Continuous fun t => bornG 𝒢 θ lam t ω - bJ j β t ω) ∧
      ∀ t, GramFeasible D (bornG 𝒢 θ lam t ω) := by
    filter_upwards [hrep, h𝒢.continuous, hcont, hfeas] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  set CJ : ℝ := ∑ f, ∑ e', ‖gramEntry e' (j f)‖
  refine ⟨hGa, fun t => stronglyMeasurable_birthSum hβ t, hcont, hfeas, fun K e => ?_,
    fun K e e' => ?_⟩
  · obtain ⟨ρ, hρ, hρσ⟩ := exists_stop_ae_eq_traceStop hGa hj hβ hcont K
    refine exists_martingale_of_cLocMart (cLocMart_bornRep h𝒢 hp hθ hlam e)
      (fun ω => bornRep_zero _ e ω) (ae_of_all _ fun ω t =>
        integrableOn_zero) ?_ hρ hρσ fun t => ?_
    · filter_upwards [hgood] with ω h u
      rw [integral_zero, sub_zero]
      exact bornCompensated_eq_bornRep hsig h.1 h.2.1 e u
    · obtain ⟨Cd, hCd⟩ := exists_bound_box (continuous_gramDriftEntry D0 D e) (2 * |K|)
      refine ⟨2 * (2 * |K| + CJ) + |Cd| * t, ?_⟩
      filter_upwards [hgood] with ω h s hs
      exact norm_comp_stopped_le (G := fun t => bornG 𝒢 θ lam t ω) h.2.2.2 h.2.2.1
        (fun u e => norm_entry_bJ_le u ω e) hCd hs e
  · obtain ⟨ρ, hρ, hρσ⟩ := exists_stop_ae_eq_traceStop hGa hj hβ hcont K
    refine exists_martingale_of_cLocMart (cLocMart_bornRep_mul h𝒢 hp hθ hlam e e')
      (fun ω => by simp only [bornRep_zero, zero_mul]) ?_ ?_ hρ hρσ fun t => ?_
    · filter_upwards [h𝒢.continuous] with ω hc t
      exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun x' _ =>
        integrable_finsetSum _ fun z _ => integrable_finsetSum _ fun z' _ =>
          integrableOn_ite_lt ((integrableOn_comp_path hc
            (continuous_gramCovEntry D0 D' (e.1, x, x') (e'.1, z, z')) t).const_mul _) _
    · filter_upwards [hgood] with ω h u
      rw [bornCompensated_eq_bornRep hsig h.1 h.2.1 e u,
        bornCompensated_eq_bornRep hsig h.1 h.2.1 e' u, integral_cov_bornG hsig]
    · obtain ⟨Cd, hCd⟩ := exists_bound_box (continuous_gramDriftEntry D0 D e) (2 * |K|)
      obtain ⟨Cd', hCd'⟩ := exists_bound_box (continuous_gramDriftEntry D0 D e') (2 * |K|)
      obtain ⟨Cc, hCc⟩ := exists_bound_box (continuous_gramCovEntry D0 D e e') (2 * |K|)
      refine ⟨(2 * (2 * |K| + CJ) + |Cd| * t) * (2 * (2 * |K| + CJ) + |Cd'| * t) + |Cc| * t, ?_⟩
      filter_upwards [hgood] with ω h s hs
      have hA := norm_comp_stopped_le (G := fun t => bornG 𝒢 θ lam t ω) h.2.2.2 h.2.2.1
        (fun u e => norm_entry_bJ_le u ω e) hCd hs e
      have hB := norm_comp_stopped_le (G := fun t => bornG 𝒢 θ lam t ω) h.2.2.2 h.2.2.1
        (fun u e => norm_entry_bJ_le u ω e) hCd' hs e'
      have hu : ((stopTime (gramTraceStop (bornG 𝒢 θ lam) K ω) s : ℝ≥0) : WithTop ℝ≥0) ≤
          gramTraceStop (bornG 𝒢 θ lam) K ω := stopTime_le_self' _ s
      have hut : ((stopTime (gramTraceStop (bornG 𝒢 θ lam) K ω) s : ℝ≥0) : ℝ) ≤ t :=
        NNReal.coe_le_coe.2 ((stopTime_le _ s).trans hs)
      have hC := (norm_integral_le_stop (G := fun t => bornG 𝒢 θ lam t ω) h.2.2.2
        (fun H hH => (hCc H hH).trans (le_abs_self Cc)) hu).trans
        (mul_le_mul_of_nonneg_left hut (abs_nonneg Cc))
      simp only [stoppedProcess_eq_stopTime]
      refine (norm_sub_le _ _).trans (add_le_add ?_ hC)
      rw [norm_mul]
      exact mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA)

end BlockBand.SourceProcess.ModelExist
