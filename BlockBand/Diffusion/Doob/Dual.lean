module

public import BlockBand.Diffusion.Doob.Test

/-!
# Conditional duality for the one-pair boundary dual

For every realization of the one-pair boundary dual
`IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y` from a dual start `(x, y)` (`D₀ > 0`), every
test pair `(g, k)` and the duality function `u = dkU D0 g k t`, with the named
hypothesis `DkLbkCornerHeatIdentity D0` (used only for the bound `0 ≤ u ≤ C`):

**Main result (`dk_dual_duality`).** For `s < t` and `A ∈ 𝓖_s`,
`∫_A u(t, Z_t) dP = ∫_A u(s, Z_s) dP`, `Z = dkZf N X Y` (the killed point, progressive version).
Here `u(t, Z_t) = ℓ(Z_t) g(Z_t,₀) k(Z_t,₁)` on `{t < σ₀}` and `0` after (`Z = 0`, the corner).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission (shiftFiltration)
open scoped ENNReal NNReal

/-!
### Time translation of `C^{0,2}` data
-/

theorem IsC02On.comp_add_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u ut : ℝ × E → ℝ} {u1 : ℝ × E → E →L[ℝ] ℝ} {u2 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {S : Set (ℝ × E)} (h : IsC02On u ut u1 u2 S) (q : ℝ) :
    IsC02On (fun p => u (p.1 + q, p.2)) (fun p => ut (p.1 + q, p.2))
      (fun p => u1 (p.1 + q, p.2)) (fun p => u2 (p.1 + q, p.2))
      {p | (p.1 + q, p.2) ∈ S} where
  hasDerivAt_time p hp := (h.hasDerivAt_time _ hp).comp_add_const p.1 q
  hasFDerivAt_space p hp := h.hasFDerivAt_space _ hp
  hasFDerivAt_space2 p hp := h.hasFDerivAt_space2 _ hp
  continuousOn := h.continuousOn.comp (by fun_prop) fun _ hp => hp
  continuousOn_time := h.continuousOn_time.comp (by fun_prop) fun _ hp => hp
  continuousOn_space := h.continuousOn_space.comp (by fun_prop) fun _ hp => hp
  continuousOn_space2 := h.continuousOn_space2.comp (by fun_prop) fun _ hp => hp

theorem finProd_symm_mem_openStripFin {p : ℝ × ℝ} (hp : p ∈ exOpenStrip) :
    finProd.symm p ∈ openStripFin := ⟨hp.1, hp.2.1, hp.2.2⟩

theorem finProd_symm_zero : finProd.symm ((0 : ℝ), (0 : ℝ)) = 0 := by
  ext i; fin_cases i <;> rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {D0 x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- **The killed path of the progressive version**, a.s.: in the open strip at positive times
before `σ₀`, at the corner from `σ₀` on, at the start at time `0`, continuous, and `σ₀ > 0`. -/
theorem IsDkBoundaryDualProcess.ae_killed
    (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, (∀ r : ℝ≥0, 0 < r → (r : ℝ≥0∞) < dkDualExtinction N ω →
        dkZf N X Y r ω ∈ openStripFin) ∧
      (∀ r : ℝ≥0, dkDualExtinction N ω ≤ r → dkZf N X Y r ω = 0) ∧
      dkZf N X Y 0 ω = finProd.symm (x, y) ∧ Continuous (fun t => dkZf N X Y t ω) ∧
      0 < dkDualExtinction N ω := by
  filter_upwards [hP.ae_good, hP.ae_dkZf_eq, hP.isTestMPSolution_flat.continuous]
    with ω hg he hc
  obtain ⟨⟨h0, hx0, hy0⟩, hpath⟩ := hg
  refine ⟨fun r hr hrσ => ?_, fun r hr => ?_, ?_, hc, dk_extinction_pos hpath h0⟩
  · rw [he, dkZ, dkPt_eq_of_lt hpath h0 hrσ]
    exact finProd_symm_mem_openStripFin (dk_mem_openStrip hpath h0 hr hrσ)
  · rw [he, dkZ, dkPt_eq_of_le hpath h0 hr, finProd_symm_zero]
  · rw [he, dkZ, dkPt_eq_of_lt hpath h0 (dk_extinction_pos hpath h0), hx0, hy0]

variable (hD0 : 0 < D0) (hCH : DkLbkCornerHeatIdentity D0)
  (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hz : IsDkDualStart ![x] ![y])
  {g k : ℝ → ℝ} (hgk : IsDkTestPair g k)
include hD0 hCH hP hz hgk

omit hD0 hCH hP hgk in
theorem dk_start_mem_strip : (x, y) ∈ exBaseStrip := by
  obtain ⟨-, -, hx, hy, -⟩ := hz
  exact ⟨by simpa using hx 0, by simpa using (hy 0).1, by simpa using (hy 0).2⟩

omit hP hz in
/-- The uniform bound of the duality function. -/
theorem dk_dual_bounds {t : ℝ≥0} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × (Fin 2 → ℝ), p.1 ≤ t → p.2 ∈ openStripFin →
      |dkU D0 g k t p| ≤ C := by
  obtain ⟨R, hR⟩ := hgk.supp
  refine ⟨max R 0 + 1, by positivity, fun p hpt hp => ?_⟩
  obtain ⟨h1, h2⟩ := dkU_le hD0 hCH hgk hR hpt hp
  rw [abs_of_nonneg h1]; exact h2

/-- **Conditional duality from a positive time.** -/
theorem dk_dual_duality_pos {s t : ℝ≥0} (hs0 : 0 < s) (hst : s < t) :
    Integrable (fun ω => dkU D0 g k t ((t : ℝ), dkZf N X Y t ω)) P ∧
      Integrable (fun ω => dkU D0 g k t ((s : ℝ), dkZf N X Y s ω)) P ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, dkU D0 g k t ((t : ℝ), dkZf N X Y t ω) ∂P =
          ∫ ω in A, dkU D0 g k t ((s : ℝ), dkZf N X Y s ω) ∂P := by
  have := hP.prob
  set q : ℝ≥0 := s / 2 with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hqs : q < s := by rw [hq]; exact NNReal.half_lt_self hs0.ne'
  have hqt : q ≤ t := (hqs.trans hst).le
  have hZ' := hP.isTestMPSolution_shift q
  obtain ⟨ut, u1, u2, hd, hpde, hcont, -⟩ := dkU_isC02On_spGen hD0 hgk t (dk_start_mem_strip hz)
  obtain ⟨C, -, hC⟩ := dk_dual_bounds hD0 hCH hgk (t := t)
  set t' : ℝ≥0 := t - q with ht'
  set s' : ℝ≥0 := s - q with hs'
  have ht'R : (t' : ℝ) + q = t := by rw [ht', NNReal.coe_sub hqt]; ring
  have hs'R : (s' : ℝ) + q = s := by rw [hs', NNReal.coe_sub hqs.le]; ring
  have hs'0 : 0 < s' := by rw [hs']; exact tsub_pos_of_lt hqs
  have hst' : s' < t' := by rw [hs', ht']; exact tsub_lt_tsub_right_of_le hqs.le hst
  set u' : ℝ × (Fin 2 → ℝ) → ℝ := fun p => dkU D0 g k t (p.1 + q, p.2) with hu'
  have hmaps : ∀ p ∈ Ioo 0 (t' : ℝ) ×ˢ openStripFin,
      ((p.1 + q, p.2) : ℝ × (Fin 2 → ℝ)) ∈ Ioo 0 (t : ℝ) ×ˢ openStripFin := fun p hp =>
    ⟨⟨by linarith [hp.1.1, (NNReal.coe_nonneg q)], by linarith [hp.1.2]⟩, hp.2⟩
  have hmaps' : ∀ p ∈ Ioc 0 (t' : ℝ) ×ˢ openStripFin,
      ((p.1 + q, p.2) : ℝ × (Fin 2 → ℝ)) ∈ Ioc 0 (t : ℝ) ×ˢ openStripFin := fun p hp =>
    ⟨⟨by linarith [hp.1.1, (NNReal.coe_nonneg q)], by linarith [hp.1.2]⟩, hp.2⟩
  have hd' := (hd.comp_add_time (q : ℝ)).mono (fun p hp => hmaps p hp)
  have hpde' : ∀ p ∈ Ioo 0 (t' : ℝ) ×ˢ openStripFin, spGen (dkHDrift D0) (baseCov D0)
      (fun p => ut (p.1 + q, p.2)) (fun p => u1 (p.1 + q, p.2)) (fun p => u2 (p.1 + q, p.2))
      p = 0 := fun p hp => hpde _ (hmaps p hp)
  have hcont' : ContinuousOn u' (Ioc 0 (t' : ℝ) ×ˢ openStripFin) :=
    hcont.comp (by fun_prop) fun p hp => hmaps' p hp
  have hC' : ∀ p ∈ Ioc 0 (t' : ℝ) ×ˢ openStripFin, |u' p| ≤ C := fun p hp =>
    hC _ (by simp only; linarith [hp.1.2]) hp.2
  have hu0' : ∀ r, u' (r, 0) = 0 := fun r => dkU_zero D0 g k t _
  have hlin' : ∀ p ∈ Ioc 0 (t' : ℝ) ×ˢ openStripFin, |u' p| ≤ 2 * ‖p.2 - 0‖ := fun p hp =>
    dkU_lin hD0 hgk t (p := (p.1 + q, p.2)) hp.2
  have hpath : ∀ᵐ ω ∂P, (∀ r : ℝ≥0, (r : ℝ≥0∞) < dkDualExtinction N ω - q →
      shiftProc (dkZf N X Y) q r ω ∈ openStripFin) ∧
      ∀ r : ℝ≥0, dkDualExtinction N ω - q ≤ r → shiftProc (dkZf N X Y) q r ω = 0 := by
    filter_upwards [hP.ae_killed] with ω h
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [shiftProc_apply]
      refine h.1 (q + r) (add_pos_of_pos_of_nonneg hq0 zero_le) ?_
      have := lt_tsub_iff_left.1 hr
      exact_mod_cast this
    · rw [shiftProc_apply]
      refine h.2.1 (q + r) ?_
      have := tsub_le_iff_left.1 hr
      exact_mod_cast this
  have H := dk_duality_C02_killed hZ' isOpen_openStripFin (continuousOn_dkHDrift D0)
    (continuous_baseCov D0).continuousOn (fun y _ i j => baseCov_symm D0 y i j) hd' hpde'
    hcont' hC' zero_notMem_openStripFin hu0' hlin' hpath hs'0 hst'
  have eT : ∀ ω, u' ((t' : ℝ), shiftProc (dkZf N X Y) q t' ω) =
      dkU D0 g k t ((t : ℝ), dkZf N X Y t ω) := fun ω => by
    show dkU D0 g k t ((t' : ℝ) + q, dkZf N X Y (q + t') ω) = _
    rw [ht'R, ht', add_tsub_cancel_of_le hqt]
  have eS : ∀ ω, u' ((s' : ℝ), shiftProc (dkZf N X Y) q s' ω) =
      dkU D0 g k t ((s : ℝ), dkZf N X Y s ω) := fun ω => by
    show dkU D0 g k t ((s' : ℝ) + q, dkZf N X Y (q + s') ω) = _
    rw [hs'R, hs', add_tsub_cancel_of_le hqs.le]
  refine ⟨(H.1).congr (ae_of_all _ fun ω => eT ω), (H.2.1).congr (ae_of_all _ fun ω => eS ω),
    fun A hA => ?_⟩
  have hA' : MeasurableSet[shiftFiltration 𝓖 q s'] A := by
    rw [shiftFiltration_apply, hs', add_tsub_cancel_of_le hqs.le]; exact hA
  calc ∫ ω in A, dkU D0 g k t ((t : ℝ), dkZf N X Y t ω) ∂P
      = ∫ ω in A, u' ((t' : ℝ), shiftProc (dkZf N X Y) q t' ω) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => (eT ω).symm)
    _ = ∫ ω in A, u' ((s' : ℝ), shiftProc (dkZf N X Y) q s' ω) ∂P := H.2.2 A hA'
    _ = _ := integral_congr_ae (ae_of_all _ eS)

/-- **Conditional duality for the one-pair dual.** For `s < t` and `A ∈ 𝓖_s`,
`∫_A u(t, Z_t) = ∫_A u(s, Z_s)`. -/
theorem dk_dual_duality {s t : ℝ≥0} (hst : s < t) :
    Integrable (fun ω => dkU D0 g k t ((t : ℝ), dkZf N X Y t ω)) P ∧
      Integrable (fun ω => dkU D0 g k t ((s : ℝ), dkZf N X Y s ω)) P ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, dkU D0 g k t ((t : ℝ), dkZf N X Y t ω) ∂P =
          ∫ ω in A, dkU D0 g k t ((s : ℝ), dkZf N X Y s ω) ∂P := by
  have := hP.prob
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
  swap
  · exact dk_dual_duality_pos hD0 hCH hP hz hgk h0 hst
  subst h0
  have htR : (0 : ℝ) < t := by exact_mod_cast hst
  have hn2 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  set sn : ℕ → ℝ≥0 := fun n => ⟨(t : ℝ) / ((n : ℝ) + 2), (div_pos htR (hn2 n)).le⟩ with hsn
  have hsn0 : ∀ n, 0 < sn n := fun n => by
    rw [← NNReal.coe_pos]; exact div_pos htR (hn2 n)
  have hsnt : ∀ n, sn n < t := fun n => by
    rw [← NNReal.coe_lt_coe]
    change (t : ℝ) / ((n : ℝ) + 2) < t
    rw [div_lt_iff₀ (hn2 n)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hsnR : Tendsto (fun n => (sn n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsnl : Tendsto sn atTop (𝓝 0) := NNReal.tendsto_coe.1 (by simpa using hsnR)
  have PP := fun n => dk_dual_duality_pos hD0 hCH hP hz hgk (hsn0 n) (hsnt n)
  obtain ⟨C, hC0, hC⟩ := dk_dual_bounds hD0 hCH hgk (t := t)
  obtain ⟨-, -, -, -, -, -, hu0c⟩ := dkU_isC02On_spGen hD0 hgk t (dk_start_mem_strip hz)
  have hi0 : Integrable (fun ω => dkU D0 g k t (((0 : ℝ≥0) : ℝ), dkZf N X Y 0 ω)) P :=
    (integrable_const (dkU D0 g k t (0, finProd.symm (x, y)))).congr
      (hP.ae_killed.mono fun ω h => by simp only [NNReal.coe_zero, h.2.2.1])
  refine ⟨(PP 0).1, hi0, fun A hA => ?_⟩
  have hbd : ∀ n, ∀ᵐ ω ∂P, |dkU D0 g k t ((sn n : ℝ), dkZf N X Y (sn n) ω)| ≤ C := fun n => by
    filter_upwards [hP.ae_killed] with ω h
    by_cases hr : ((sn n : ℝ≥0) : ℝ≥0∞) < dkDualExtinction N ω
    · exact hC _ (by exact_mod_cast (hsnt n).le) (h.1 _ (hsn0 n) hr)
    · push Not at hr
      rw [h.2.1 _ hr, dkU_zero, abs_zero]; exact hC0
  have hl : ∀ᵐ ω ∂P, Tendsto (fun n => dkU D0 g k t ((sn n : ℝ), dkZf N X Y (sn n) ω)) atTop
      (𝓝 (dkU D0 g k t (((0 : ℝ≥0) : ℝ), dkZf N X Y 0 ω))) := by
    filter_upwards [hP.ae_killed] with ω h
    obtain ⟨hO, -, h0, hc, hσ⟩ := h
    rw [h0, NNReal.coe_zero]
    have hev : ∀ᶠ n in atTop, ((sn n : ℝ≥0) : ℝ≥0∞) < dkDualExtinction N ω :=
      ((ENNReal.continuous_coe.tendsto 0).comp hsnl).eventually
        (gt_mem_nhds (by simpa using hσ))
    have hp : Tendsto (fun n => ((sn n : ℝ), dkZf N X Y (sn n) ω)) atTop
        (𝓝[Ioc 0 (t : ℝ) ×ˢ openStripFin] (0, finProd.symm (x, y))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h2 : Tendsto (fun n => dkZf N X Y (sn n) ω) atTop (𝓝 (finProd.symm (x, y))) := by
          rw [← h0]; exact (hc.tendsto 0).comp hsnl
        exact hsnR.prodMk_nhds h2
      · filter_upwards [hev] with n hn
        exact ⟨⟨by exact_mod_cast hsn0 n, by exact_mod_cast (hsnt n).le⟩, hO _ (hsn0 n) hn⟩
    exact hu0c.tendsto.comp hp
  have hT := tendsto_setIntegral_of_abs_le (fun n => (PP n).2.1.aestronglyMeasurable) hbd hl A
  have heq : ∀ n, ∫ ω in A, dkU D0 g k t ((sn n : ℝ), dkZf N X Y (sn n) ω) ∂P =
      ∫ ω in A, dkU D0 g k t ((t : ℝ), dkZf N X Y t ω) ∂P :=
    fun n => ((PP n).2.2 A (𝓖.mono zero_le A hA)).symm
  exact tendsto_nhds_unique (hT.congr heq) tendsto_const_nhds |>.symm

end BlockBand.Diffusion
