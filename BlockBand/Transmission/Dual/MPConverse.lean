module

public import BlockBand.Transmission.Dual.MPConverseStop

/-!
# The martingale-problem converse: `C_c^∞` tests ⇒ `IsMPSolutionOn`

`isMPSolutionOn_of_test`: on a probability space with a raw filtration, let `U ⊆ ℝ^d` be open,
let `b, a` be continuous on `U` with `a(y)` symmetric, and let `Y` be adapted with a.s. continuous
paths such that, for every smooth `φ` with compact support in `U`,
`φ(Y_t) − φ(Y_0) − ∫_0^t 𝓛φ(Y_s) ds` has a martingale modification (`IsTestMPSolution`). Then `Y`
solves the `(b, a)` martingale problem in `U` in the sense of `Stochastic.IsMPSolutionOn`
(stopped compensated coordinates and stopped brackets at the exits of relatively compact
subdomains have martingale modifications).

Proof, for `W ⊂⊂ U` with a cutoff `χ = 1` near `closure W`:
* drift: the test `χ·y_i`, stopped at the exit (`hasMM_stop`, `stopped_testMart_eq`);
* bracket: `M_iM_j − ∫a_ij = F_ij − y_i(0)F_j − y_j(0)F_i − G_ij − G_ji` pathwise
  (`bracket_alg`), where `F` are the stopped tests `χ·y_i`, `χ·y_iy_j`, and
  `G_ij = A_iM_j − ∫ b_iM_j` has a modification by integration by parts
  (`hasMartingaleModification_ibp`, drift switched off after the exit).

Symmetry of `a` is needed: the tests only see `(a + aᵀ)/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime
  setIntegral_switch measurableSet_toNNReal_le continuous_stopTime stopTime_le
  aesm_stoppedProcess_exit exitTimeFrom_eq_zero stopTime_of_eq_zero)
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem continuous_mul_cutoff {χ f : (Fin d → ℝ) → ℝ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hχ : Continuous χ) (hχs : tsupport χ ⊆ U) (hf : ContinuousOn f U) :
    Continuous fun y => χ y * f y := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y ∈ U
  · exact hχ.continuousAt.mul (hf.continuousAt (hU.mem_nhds hy))
  · have hev := notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hχs h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hev] with z hz
    simp only [Pi.zero_apply] at hz
    simp [hz]

theorem coe_toNNReal_eq {u : ℝ} (hu : 0 ≤ u) : ((u.toNNReal : ℝ≥0) : ℝ) = u :=
  Real.coe_toNNReal _ hu

/-- **The martingale-problem converse.** -/
theorem isMPSolutionOn_of_test {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hb : ContinuousOn b U) (ha : ContinuousOn a U) (hsym : ∀ y ∈ U, ∀ i j, a y i j = a y j i)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} (H : IsTestMPSolution Q 𝓖 b a U Y) :
    IsMPSolutionOn Q 𝓖 b a U Y := by
  have hmeas : ∀ t, Measurable[𝓖 t] (Y t) := fun t => (H.adapted t).measurable
  have key : ∀ W, IsInteriorDomain W U →
      (∀ i, HasMartingaleModification Q 𝓖
        (stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y))) ∧
      ∀ i j, HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
        mpCompensated b Y i t ω * mpCompensated b Y j t ω -
          ∫ s in Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j) (exitTimeFrom W Y)) := by
    intro W hW
    obtain ⟨χ, V, hVo, hWV, hχs, hχc, hχU, hχ1, -⟩ := exists_cutoff hU hW.2.1 hW.2.2
    have hVU : V ⊆ U := fun y hy => hχU (subset_tsupport _ (by
      rw [Function.mem_support, hχ1 y hy]; exact one_ne_zero))
    set ψ : Fin d → (Fin d → ℝ) → ℝ := fun i z => χ z * z i with hψdef
    set ψ2 : Fin d → Fin d → (Fin d → ℝ) → ℝ := fun i j z => χ z * (z i * z j) with hψ2def
    have hψV : ∀ i, ∀ y ∈ V, ψ i y = y i := fun i y hy => by simp [ψ, hχ1 y hy]
    have hψ2V : ∀ i j, ∀ y ∈ V, ψ2 i j y = y i * y j := fun i j y hy => by simp [ψ2, hχ1 y hy]
    have genV : ∀ i, ∀ y ∈ V, mpGenerator b a (ψ i) y = b y i := fun i y hy => by
      have h : ψ i =ᶠ[𝓝 y] fun z => z i := Filter.eventually_of_mem (hVo.mem_nhds hy) fun z hz => hψV i z hz
      rw [mpGenerator_congr h, mpGenerator_coord]
    have genV2 : ∀ i j, ∀ y ∈ V, mpGenerator b a (ψ2 i j) y =
        b y i * y j + b y j * y i + a y i j := fun i j y hy => by
      have h : ψ2 i j =ᶠ[𝓝 y] fun z => z i * z j :=
        Filter.eventually_of_mem (hVo.mem_nhds hy) fun z hz => hψ2V i j z hz
      rw [mpGenerator_congr h, mpGenerator_coord_mul i j y (hsym y (hVU hy) i j)]
    have hF : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ U → HasMartingaleModification Q 𝓖
          (stoppedProcess (testMart b a φ Y) (exitTimeFrom W Y)) := fun φ h1 h2 h3 =>
      hasMM_stop (H.mart φ h1 h2 h3) (H.continuous.mono fun ω hω =>
        continuous_testMart hU hb ha (h1.of_le (by norm_cast)) h3 hω) hmeas H.continuous hW.1
    have hψ : ∀ i, HasMartingaleModification Q 𝓖
        (stoppedProcess (testMart b a (ψ i) Y) (exitTimeFrom W Y)) := fun i =>
      hF _ (hχs.mul (contDiff_apply ℝ ℝ i)) hχc.mul_right (tsupport_mul_subset_left.trans hχU)
    have hψ2 : ∀ i j, HasMartingaleModification Q 𝓖
        (stoppedProcess (testMart b a (ψ2 i j) Y) (exitTimeFrom W Y)) := fun i j =>
      hF _ (hχs.mul ((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ j))) hχc.mul_right
        (tsupport_mul_subset_left.trans hχU)
    have hFi : ∀ i, ∀ᵐ ω ∂Q, ∀ t, stoppedProcess (testMart b a (ψ i) Y) (exitTimeFrom W Y) t ω =
        stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y) t ω := fun i => by
      filter_upwards [H.continuous] with ω hω t
      rw [stopped_testMart_eq hW.1 hWV (hψV i) (genV i) hω, stoppedProcess_eq_stopTime]
      rfl
    have hdrift : ∀ i, HasMartingaleModification Q 𝓖
        (stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y)) := fun i =>
      hasMM_congr (hψ i) fun t => by
        filter_upwards [hFi i] with ω hω; exact hω t
    refine ⟨hdrift, fun i j => ?_⟩
    -- globally continuous versions of the coefficients
    set bc : Fin d → (Fin d → ℝ) → ℝ := fun k y => χ y * b y k with hbcdef
    have hbc : ∀ k, Continuous (bc k) := fun k =>
      continuous_mul_cutoff hU hχs.continuous hχU ((continuous_apply k).comp_continuousOn hb)
    have hbc_eq : ∀ k, ∀ y ∈ closure W, bc k y = b y k := fun k y hy => by
      simp [bc, hχ1 y (hWV hy)]
    set b' : (Fin d → ℝ) → Fin d → ℝ := fun y k => bc k y
    have hb' : Continuous b' := continuous_pi fun k => hbc k
    have hbb' : EqOn b b' (closure W) := fun y hy => funext fun k => (hbc_eq k y hy).symm
    have hbcB : ∀ k, ∃ C, ∀ y, ‖bc k y‖ ≤ C := fun k =>
      (hbc k).bounded_above_of_compact_support hχc.mul_right
    -- bounds on `closure W`
    obtain ⟨R₁, hR₁⟩ := hW.2.1.exists_bound_of_continuousOn (continuousOn_id (s := closure W))
    obtain ⟨B₁, hB₁⟩ := hW.2.1.exists_bound_of_continuousOn (hb.mono hW.2.2)
    set R := max R₁ 0
    set B := max B₁ 0
    have hR : ∀ y ∈ closure W, ∀ k, |y k| ≤ R := fun y hy k => by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm y k).trans ((hR₁ y hy).trans (le_max_left _ _))
    have hB : ∀ y ∈ closure W, ∀ k, |b y k| ≤ B := fun y hy k => by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (b y) k).trans ((hB₁ y hy).trans (le_max_left _ _))
    -- the stopped compensated coordinates
    set X : Fin d → ℝ≥0 → Ω → ℝ := fun k => stoppedProcess (mpCompensated b Y k)
      (exitTimeFrom W Y) with hXdef
    have hXc : ∀ k, ∀ᵐ ω ∂Q, Continuous fun t => X k t ω := fun k => by
      filter_upwards [H.continuous] with ω hω
      have e : (fun t => X k t ω) = fun t =>
          mpCompensated b' Y k (stopTime (exitTimeFrom W Y ω) t) ω := funext fun t => by
        simp only [hXdef]
        rw [Representation.stopped_mpCompensated_congr hW.1 hbb' hω k t,
          stoppedProcess_eq_stopTime]
      rw [e]
      exact (Representation.continuous_mpCompensated hb' hω k).comp (continuous_stopTime _)
    have hXb : ∀ k (T : ℝ≥0), ∃ C, ∀ᵐ ω ∂Q, ∀ t ≤ T, |X k t ω| ≤ C := fun k T =>
      ⟨2 * R + B * T, by
        filter_upwards [H.continuous] with ω hω t ht
        refine (Representation.abs_stopped_mpCompensated_le hW.1 (le_max_right _ _)
          (le_max_right _ _) hR hB hω k t).trans ?_
        have : (t : ℝ) ≤ T := ht
        nlinarith [le_max_right B₁ 0]⟩
    -- the drifts switched off after the exit
    set β : Fin d → ℝ≥0 → Ω → ℝ := fun k u ω =>
      if (u : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω then bc k (Y u ω) else 0 with hβdef
    set A : Fin d → ℝ≥0 → Ω → ℝ := fun k t ω => ∫ u in Ioc (0 : ℝ) t, β k u.toNNReal ω
      with hAdef
    have hβb : ∀ k, ∃ C, ∀ t ω, |β k t ω| ≤ C := fun k => by
      obtain ⟨C, hC⟩ := hbcB k
      refine ⟨C, fun t ω => ?_⟩
      simp only [hβdef]
      split_ifs
      · rw [← Real.norm_eq_abs]; exact hC _
      · rw [abs_zero]; exact (norm_nonneg _).trans (hC 0)
    have hβm : ∀ k, ∀ᵐ ω ∂Q, Measurable fun u : ℝ => β k u.toNNReal ω := fun k => by
      filter_upwards [H.continuous] with ω hω
      exact Measurable.ite (measurableSet_toNNReal_le _)
        ((hbc k).comp (hω.comp continuous_real_toNNReal)).measurable measurable_const
    have hAeq : ∀ k, ∀ᵐ ω ∂Q, ∀ t, A k t ω = Y (stopTime (exitTimeFrom W Y ω) t) ω k -
        Y 0 ω k - X k t ω := fun k => by
      filter_upwards [H.continuous] with ω hω t
      have hcl := (Bridges.stopped_path_mem_closure hW.1 hω t).1
      simp only [hAdef, hβdef, hXdef, stoppedProcess_eq_stopTime, mpCompensated]
      rw [setIntegral_switch (fun v => bc k (Y v.toNNReal ω))]
      rw [setIntegral_congr_fun measurableSet_Ioc fun s hs => hbc_eq k _ (hcl s hs)]
      ring
    have hAm : ∀ k t, AEStronglyMeasurable[𝓖 t] (A k t) Q := fun k t => by
      obtain ⟨N, hN, hNe⟩ := hdrift k
      have hYs := aesm_stoppedProcess_exit H.adapted H.continuous hW.1 t
      have h1 : AEStronglyMeasurable[𝓖 t] (fun ω => stoppedProcess Y (exitTimeFrom W Y) t ω k -
          Y 0 ω k - N t ω) Q :=
        (((continuous_apply k).comp_aestronglyMeasurable hYs).sub
          ((((continuous_apply k).comp_stronglyMeasurable (H.adapted 0)).mono
            (𝓖.mono zero_le)).aestronglyMeasurable)).sub (hN.1 t).aestronglyMeasurable
      refine h1.congr ?_
      filter_upwards [hAeq k, hNe t] with ω hω hN'
      rw [hω t, hN']
      rfl
    -- integration by parts
    have hG : ∀ k l, HasMartingaleModification Q 𝓖 (fun t ω => A k t ω * X l t ω -
        ∫ u in Ioc (0 : ℝ) t, β k u.toNNReal ω * X l u.toNNReal ω) := fun k l => by
      obtain ⟨C, hC⟩ := hβb k
      exact hasMartingaleModification_ibp (hdrift l) (hXc l) (hXb l) hC (hβm k)
        (fun t ω => rfl) (hAm k)
    -- the initial coordinates, cut off outside `W`
    set ξ : Fin d → Ω → ℝ := fun k ω => W.indicator (fun y => y k) (Y 0 ω) with hξdef
    have hξm : ∀ k, StronglyMeasurable[𝓖 0] (ξ k) := fun k =>
      (((measurable_pi_apply k).indicator hW.1.measurableSet).comp (hmeas 0)).stronglyMeasurable
    have hξb : ∀ k ω, |ξ k ω| ≤ R := fun k ω => by
      simp only [hξdef]
      by_cases h : Y 0 ω ∈ W
      · rw [Set.indicator_of_mem h]; exact hR _ (subset_closure h) k
      · rw [Set.indicator_of_notMem h, abs_zero]; exact le_max_right _ _
    have hRHS := hasMM_sub (hasMM_sub (hasMM_sub (hasMM_sub (hψ2 i j)
      (hasMM_const_mul (hψ j) (hξm i) (hξb i))) (hasMM_const_mul (hψ i) (hξm j) (hξb j)))
      (hG i j)) (hG j i)
    refine hasMM_congr hRHS fun t => ?_
    filter_upwards [H.continuous, hFi i, hFi j] with ω hω hFiω hFjω
    have hcl : ∀ t' : ℝ≥0, ∀ s ∈ Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t'),
        Y s.toNNReal ω ∈ closure W := fun t' => (Bridges.stopped_path_mem_closure hW.1 hω t').1
    set r := stopTime (exitTimeFrom W Y ω) t with hr
    set yy : Fin d → ℝ → ℝ := fun k s => Y s.toNNReal ω k with hyydef
    set bb : Fin d → ℝ → ℝ := fun k s => bc k (Y s.toNNReal ω) with hbbdef
    set aa : ℝ → ℝ := fun s => χ (Y s.toNNReal ω) * a (Y s.toNNReal ω) i j with haadef
    set AA : Fin d → ℝ → ℝ := fun k s => ∫ u in (0 : ℝ)..s, bb k u with hAAdef
    set MM : Fin d → ℝ → ℝ := fun k s => yy k s - yy k 0 - AA k s with hMMdef
    have hyy : ∀ k, Continuous (yy k) := fun k =>
      (continuous_apply k).comp (hω.comp continuous_real_toNNReal)
    have hbb : ∀ k, Continuous (bb k) := fun k => (hbc k).comp (hω.comp continuous_real_toNNReal)
    have haa : Continuous aa := by
      have h1 : Continuous fun y => χ y * a y i j := continuous_mul_cutoff hU hχs.continuous
        hχU ((continuous_id.matrix_elem i j).comp_continuousOn ha)
      exact h1.comp (hω.comp continuous_real_toNNReal)
    have hyy0 : ∀ k, yy k 0 = Y 0 ω k := fun k => by simp [yy]
    have fM : ∀ k (t' : ℝ≥0), X k t' ω = MM k (stopTime (exitTimeFrom W Y ω) t') := by
      intro k t'
      simp only [hXdef, stoppedProcess_eq_stopTime, mpCompensated, hMMdef, hyy0, hAAdef]
      rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
      simp only [yy, Real.toNNReal_coe]
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioc fun s hs => (hbc_eq k _ (hcl t' s hs)).symm
    have fFi : stoppedProcess (testMart b a (ψ i) Y) (exitTimeFrom W Y) t ω = MM i r := by
      rw [hFiω t]; exact fM i t
    have fFj : stoppedProcess (testMart b a (ψ j) Y) (exitTimeFrom W Y) t ω = MM j r := by
      rw [hFjω t]; exact fM j t
    have fFij : stoppedProcess (testMart b a (ψ2 i j) Y) (exitTimeFrom W Y) t ω =
        yy i r * yy j r - yy i 0 * yy j 0 -
          ∫ u in (0 : ℝ)..r, (bb i u * yy j u + bb j u * yy i u + aa u) := by
      rw [stopped_testMart_eq hW.1 hWV (hψ2V i j) (genV2 i j) hω t, hyy0, hyy0,
        intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
      simp only [yy, Real.toNNReal_coe]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have h := hcl t s hs
      simp only [bb, aa, hbc_eq i _ h, hbc_eq j _ h, hχ1 _ (hWV h), one_mul]
    have fξ : ∀ k l, stoppedProcess (testMart b a (ψ l) Y) (exitTimeFrom W Y) t ω = MM l r →
        ξ k ω * stoppedProcess (testMart b a (ψ l) Y) (exitTimeFrom W Y) t ω =
          yy k 0 * MM l r := by
      intro k l hl
      rw [hl, hyy0]
      by_cases h : Y 0 ω ∈ W
      · simp only [hξdef, Set.indicator_of_mem h]
      · have hr0 : r = 0 := by
          rw [hr, exitTimeFrom_eq_zero h, stopTime_of_eq_zero]
        have : MM l r = 0 := by simp [hMMdef, hAAdef, hr0]
        simp [this]
    have fG : ∀ k l, A k t ω * X l t ω -
        ∫ u in Ioc (0 : ℝ) t, β k u.toNNReal ω * X l u.toNNReal ω =
          AA k r * MM l r - ∫ u in (0 : ℝ)..r, bb k u * MM l u := by
      intro k l
      have hA' : A k t ω = AA k r := by
        simp only [hAdef, hβdef]
        rw [setIntegral_switch (fun v => bc k (Y v.toNNReal ω)),
          ← intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
      have hfun : (fun u : ℝ => β k u.toNNReal ω * X l u.toNNReal ω) = fun u =>
          if (u.toNNReal : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω then bb k u * X l u.toNNReal ω
          else 0 := funext fun u => by
        simp only [hβdef]; split_ifs <;> simp [bb]
      rw [hA', fM l t, hfun, setIntegral_switch (fun u => bb k u * X l u.toNNReal ω),
        intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      have hur : u.toNNReal ≤ stopTime (exitTimeFrom W Y ω) t :=
        Real.toNNReal_le_iff_le_coe.2 hu.2
      rw [fM l, Bridges.stopTime_eq_of_le_stopTime hur, coe_toNNReal_eq hu.1.le]
    have fZ : stoppedProcess (fun t ω => mpCompensated b Y i t ω * mpCompensated b Y j t ω -
        ∫ s in Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j) (exitTimeFrom W Y) t ω =
          MM i r * MM j r - ∫ u in (0 : ℝ)..r, aa u := by
      have hi := fM i t
      have hj := fM j t
      simp only [hXdef, stoppedProcess_eq_stopTime] at hi hj
      rw [stoppedProcess_eq_stopTime]
      show mpCompensated b Y i r ω * mpCompensated b Y j r ω -
        ∫ s in Ioc (0 : ℝ) r, a (Y s.toNNReal ω) i j = _
      rw [hi, hj, intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      show a (Y s.toNNReal ω) i j = χ (Y s.toNNReal ω) * a (Y s.toNNReal ω) i j
      rw [hχ1 _ (hWV (hcl t s hs)), one_mul]
    rw [fZ, fFij, fξ i j fFj, fξ j i fFi, fG i j, fG j i]
    exact (bracket_alg (hyy i) (hyy j) (hbb i) (hbb j) haa (fun s => rfl) (fun s => rfl)
      (fun s => rfl) (fun s => rfl) r).symm
  refine ⟨H.adapted, H.continuous, fun W hW i => (key W hW).1 i, fun W hW i j => (key W hW).2 i j⟩

end BlockBand.Transmission.Dual
