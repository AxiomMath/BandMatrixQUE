module

public import BlockBand.SourceProcess.ComplexUnique.SegDom

/-!
# Exhaustion of the horizon by the chart domains

**`tendsto_stop_segW`**: along a continuous real path with time coordinate `u ∧ h` and Gram part
of exact ranks `(r, r')` before `h` (`e_r(B) > 0`, `e_{r'}(M - B) > 0`), the exit times from
`segW r r' h n` tend to `h`, so the paths stopped there have value at `h` tending to the value
at `h`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {Ω : Type*}

/-- Before `a' < h` the path is eventually inside every chart domain. -/
theorem eventually_le_exit_segW {Y : ℝ≥0 → Ω → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ} {ω : Ω}
    (hc : Continuous fun t => Y t ω) {r r' : ℕ} {h : ℝ≥0}
    (htime : ∀ u, tOf (Y u ω) = ((min u h : ℝ≥0) : ℝ))
    (hpos : ∀ u < h, 0 < principalMinorSum r (gOf (Y u ω)).2 ∧
      0 < principalMinorSum r' ((gOf (Y u ω)).1 - (gOf (Y u ω)).2)) {a' : ℝ≥0} (ha' : a' < h) :
    ∀ᶠ n : ℕ in atTop, (a' : WithTop ℝ≥0) ≤ exitTimeFrom (segW K π r r' h n) Y ω := by
  have hI : IsCompact (Icc (0 : ℝ≥0) a') := isCompact_Icc
  have hne : (Icc (0 : ℝ≥0) a').Nonempty := ⟨0, zero_le, zero_le⟩
  have hg : Continuous fun u => gOf (K := K) (π := π) (Y u ω) := continuous_gOf.comp hc
  have hfB : Continuous fun u => principalMinorSum r (gOf (Y u ω)).2 :=
    (contDiff_ek_snd r).continuous.comp hg
  have hfC : Continuous fun u => principalMinorSum r' ((gOf (Y u ω)).1 - (gOf (Y u ω)).2) :=
    (contDiff_ek_fst_sub_snd r').continuous.comp hg
  have hfT : Continuous fun u => ((gOf (Y u ω)).1.trace).re :=
    Complex.continuous_re.comp ((continuous_fst.comp hg).matrix_trace)
  obtain ⟨sB, hsB0, hsB⟩ := hI.exists_isMinOn hne hfB.continuousOn
  obtain ⟨sC, hsC0, hsC⟩ := hI.exists_isMinOn hne hfC.continuousOn
  obtain ⟨R, hR⟩ := hI.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨R2, hR2⟩ := hI.exists_bound_of_continuousOn hfT.continuousOn
  have hmB := (hpos sB (lt_of_le_of_lt hsB0.2 ha')).1
  have hmC := (hpos sC (lt_of_le_of_lt hsC0.2 ha')).2
  set m := min (min (principalMinorSum r (gOf (Y sB ω)).2)
    (principalMinorSum r' ((gOf (Y sC ω)).1 - (gOf (Y sC ω)).2))) ((h : ℝ) - a')
  have hm : 0 < m := lt_min (lt_min hmB hmC) (by have : (a' : ℝ) < h := ha'; linarith)
  have h1 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < m :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds hm)
  have h2 : ∀ᶠ n : ℕ in atTop, max R R2 < (n : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_gt_atTop _
  filter_upwards [h1, h2] with n hn1 hn2
  refine le_iInf₂ fun s hs => WithTop.coe_le_coe.2 (not_lt.1 fun hst => hs ?_)
  have hsI : s ∈ Icc (0 : ℝ≥0) a' := ⟨zero_le, hst.le⟩
  have hsh : s ≤ h := hst.le.trans ha'.le
  have hmB' : m ≤ principalMinorSum r (gOf (Y s ω)).2 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (hsB hsI))
  have hmC' : m ≤ principalMinorSum r' ((gOf (Y s ω)).1 - (gOf (Y s ω)).2) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (hsC hsI))
  have hmt : m ≤ (h : ℝ) - a' := min_le_right _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_ofPred_eq]
    linarith [hR s hsI, le_max_left R R2]
  · simp only [mem_ofPred_eq]
    rw [htime, min_eq_left hsh]
    have : (s : ℝ) ≤ a' := hst.le
    linarith
  · simp only [mem_ofPred_eq]; linarith
  · simp only [mem_ofPred_eq]; linarith
  · simp only [mem_ofPred_eq]
    have := hR2 s hsI
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self ((gOf (Y s ω)).1.trace.re), le_max_right R R2]

/-- **The stopped values at `h` tend to the value at `h`.** -/
theorem tendsto_stop_segW {Y : ℝ≥0 → Ω → Fin (rDim (JIdx (SrcCol K π) π)) → ℝ} {ω : Ω}
    (hc : Continuous fun t => Y t ω) {r r' : ℕ} {h : ℝ≥0}
    (htime : ∀ u, tOf (Y u ω) = ((min u h : ℝ≥0) : ℝ))
    (hpos : ∀ u < h, 0 < principalMinorSum r (gOf (Y u ω)).2 ∧
      0 < principalMinorSum r' ((gOf (Y u ω)).1 - (gOf (Y u ω)).2)) :
    Tendsto (fun n : ℕ => stoppedProcess Y (exitTimeFrom (segW K π r r' h n) Y) h ω) atTop
      (𝓝 (Y h ω)) := by
  have hv : Tendsto (fun n : ℕ => stopTime (exitTimeFrom (segW K π r r' h n) Y ω) h) atTop
      (𝓝 h) := by
    refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => Eventually.of_forall fun n =>
      lt_of_le_of_lt (stopTime_le _ h) ha'⟩
    obtain ⟨b', hab, hbh⟩ := exists_between ha'
    filter_upwards [eventually_le_exit_segW hc htime hpos hbh] with n hn
    refine lt_of_lt_of_le hab ?_
    induction h' : exitTimeFrom (segW K π r r' h n) Y ω with
    | top => rw [stopTime_top]; exact hbh.le
    | coe x =>
      rw [h'] at hn
      rw [stopTime_coe]
      exact le_min hbh.le (WithTop.coe_le_coe.1 hn)
  exact (hc.tendsto h).comp hv

end BlockBand.SourceProcess.ComplexUnique
