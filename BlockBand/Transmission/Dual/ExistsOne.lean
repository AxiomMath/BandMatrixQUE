module

public import BlockBand.Transmission.Dual.ExistsPath

/-!
# `exists_` at `p = 1`: the martingale clause and `hasDualDeletionProcess_one`

For a test `f ∈ C_c^∞(𝒞₁)` and `F = f ∘ ofFlat`, the compensated processes
`Mraw n = F(Yf n) − F(z) − ∫ 1{s ≤ e_n} 𝒟₁f(Yf n s) ds` have martingale modifications
(`hasMart_G`). On `good` they are eventually equal (in `n`) to the `dualMartingale` of
the glued realization (`eventually_Mraw`): before `ζ` because the paths agree; after `ζ`
because `f` and `𝒟₁f` vanish near the corner, which the path approaches. They
are bounded uniformly in `n`, so `dualMartingale` is a `𝓖₁`-martingale
(`martingale_dualMartingale`; it is `𝓖₁ t`-measurable at every `ω` as an everywhere limit).

**Main result.** `hasDualDeletionProcess_one`: for `D₀ > 0` and every ordered interior start
`(x, y)` with one pair, `HasDualDeletionProcess D₀ x y` holds (the `p = 1` case of
`DualBoundaryLawStatement.exists_`), on the driver space `Ω₁ : Type`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {D0 : ℝ} {z : Fin 2 → ℝ}

namespace SolFamily

variable (F : SolFamily D0 z) (f : DualCoord 1 → ℝ)

/-- The flat test function. -/
def Fc : (Fin 2 → ℝ) → ℝ := fun w => f (ofFlat 1 w)

/-- The flat generator of the test. -/
def Lc (D0 : ℝ) : (Fin 2 → ℝ) → ℝ := fun w => dualGenerator D0 f (ofFlat 1 w)

theorem L₁_Fc (hf : ContDiff ℝ 2 f) : L₁ D0 (Fc f) = Lc f D0 :=
  funext fun w => mpGenerator_flat D0 hf w

/-- The compensated `n`-th process of the test. -/
def Mraw (n : ℕ) (t : ℝ≥0) (ω : Ω₁) : ℝ :=
  Fc f (F.Yf n t ω) - Fc f (F.Yf n 0 ω) -
    ∫ s in Ioc (0 : ℝ) t, switchOff (F.e n) (fun t ω => Lc f D0 (F.Yf n t ω)) s.toNNReal ω

theorem dualMartingale_eq (hz : z ∈ flatChamber 1) (t : ℝ≥0) (ω : Ω₁) :
    dualMartingale D0 1 f F.Nd F.Xd F.Yd t ω =
      (if F.Nd t ω = 1 then Fc f (F.Zd t ω) else 0) - Fc f z -
        ∫ u in Ioc (0 : ℝ) t, (if F.Nd u.toNNReal ω = 1 then Lc f D0 (F.Zd u.toNNReal ω) else 0) := by
  have hex : ∃ u ≤ t, F.Nd u ω ≤ 1 := ⟨0, zero_le, F.Nd_le_one 0 ω⟩
  have hent : dualEntrance F.Nd 1 ω = 0 := by
    have : {s | F.Nd s ω ≤ 1} = univ := eq_univ_of_forall fun s => F.Nd_le_one s ω
    simp only [dualEntrance, this, csInf_univ]; rfl
  simp only [dualMartingale, dualEntranceValue, hex, ite_true, hent, dualLift, F.dualCoordOf_d,
    F.Nd_zero, F.Zd_zero hz, Fc, Lc]

variable {f}

theorem vanish_near_corner (hfs : tsupport f ⊆ dualChamber 1) :
    IsOpen {w : Fin 2 → ℝ | ofFlat 1 w ∉ tsupport f} ∧ (0 : Fin 2 → ℝ) ∈
      {w : Fin 2 → ℝ | ofFlat 1 w ∉ tsupport f} ∧
      ∀ w ∈ {w : Fin 2 → ℝ | ofFlat 1 w ∉ tsupport f}, Fc f w = 0 ∧ Lc f D0 w = 0 := by
  refine ⟨(isClosed_tsupport f).preimage (ofFlat 1).continuous |>.isOpen_compl, fun h => ?_,
    fun w hw => ⟨show f (ofFlat 1 w) = 0 from image_eq_zero_of_notMem_tsupport hw,
      dualGenerator_eq_zero_of_notMem_tsupport hw⟩⟩
  have := (hfs h).2.2.1 0
  simp at this

/-- **On `good`, the `n`-th compensated process is eventually the `dualMartingale`.** -/
theorem eventually_Mraw (hz : z ∈ flatChamber 1) (hfs : tsupport f ⊆ dualChamber 1) {ω : Ω₁}
    (hω : ω ∈ F.good) (t : ℝ≥0) :
    ∀ᶠ n in atTop, F.Mraw f n t ω = dualMartingale D0 1 f F.Nd F.Xd F.Yd t ω := by
  have hc := (F.good_spec hω).1
  rw [F.dualMartingale_eq f hz]
  by_cases ht : (t : WithTop ℝ≥0) < F.zeta ω
  · obtain ⟨n₀, hn₀⟩ := lt_iSup_iff.1 ht
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have htn : (t : WithTop ℝ≥0) < F.e n ω := hn₀.trans_le (hc n₀ n hn).1
    simp only [Mraw, F.Nd_of_lt hω ht, ite_true, F.Zd_eq hω htn.le, F.Yf_zero hz]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs' : (s.toNNReal : WithTop ℝ≥0) ≤ t :=
      WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    simp only [switchOff, hs'.trans htn.le, ite_true, F.Nd_of_lt hω (hs'.trans_lt ht),
      F.Zd_eq hω (hs'.trans htn.le)]
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top
      (not_lt.1 ht))
    have hζ : F.zeta ω = m := hm.symm
    obtain ⟨hO, h0, hvan⟩ := vanish_near_corner (D0 := D0) hfs
    have hlim : Tendsto (fun u => F.Zd u ω) (𝓝[<] m) (𝓝 0) :=
      tendsto_pi_nhds.2 fun i => F.tendsto_Zd hω hζ i
    have hm0 : 0 < m := by have := F.zeta_pos ω; rw [hζ] at this; exact WithTop.coe_lt_coe.1 this
    obtain ⟨s₀, hs₀, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hm0).1
      (hlim (hO.mem_nhds h0))
    obtain ⟨n₀, hn₀⟩ := lt_iSup_iff.1 (show (s₀ : WithTop ℝ≥0) < F.zeta ω by
      rw [hζ]; exact WithTop.coe_lt_coe.2 hs₀)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hlt := F.e_lt_zeta hc (by rw [hζ]; exact WithTop.coe_lt_top m) n
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hs₀r : s₀ < r := WithTop.coe_lt_coe.1 (hr ▸ hn₀.trans_le (hc n₀ n hn).1)
    have hrm : r < m := WithTop.coe_lt_coe.1 (by rw [hr, ← hζ]; exact hlt)
    have hrt : r ≤ t := (hrm.trans_le (WithTop.coe_le_coe.1 (hζ ▸ not_lt.1 ht))).le
    have hNt : F.Nd t ω = 0 := F.Nd_of_le hω (not_lt.1 ht)
    have hY : F.Yf n t ω = F.Zd r ω := by
      rw [F.Zd_eq hω (hr ▸ le_rfl : (r : WithTop ℝ≥0) ≤ F.e n ω)]
      simp only [Yf, F.X_eq_of_e_le n hr.symm hrt]
    simp only [Mraw, hNt, zero_ne_one, ite_false, hY, (hvan _ (hsub ⟨hs₀r, hrm⟩)).1,
      F.Yf_zero hz]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    by_cases h1 : (s.toNNReal : WithTop ℝ≥0) ≤ F.e n ω
    · simp only [switchOff, h1, ite_true, F.Nd_of_lt hω (h1.trans_lt hlt), F.Zd_eq hω h1]
    · simp only [switchOff, h1, ite_false]
      have hrs : r < s.toNNReal := WithTop.coe_lt_coe.1 (hr ▸ not_le.1 h1)
      by_cases h2 : (s.toNNReal : WithTop ℝ≥0) < F.zeta ω
      · have hsm : s.toNNReal < m := WithTop.coe_lt_coe.1 (hζ ▸ h2)
        rw [F.Nd_of_lt hω h2]
        simp only [↓reduceIte, (hvan _ (hsub ⟨hs₀r.trans hrs, hsm⟩)).2]
      · rw [F.Nd_of_le hω (not_lt.1 h2)]; simp

theorem abs_Mraw_le {C CL : ℝ} (hC : ∀ w, |Fc f w| ≤ C) (hCL0 : 0 ≤ CL)
    (hCL : ∀ w, |Lc f D0 w| ≤ CL) (n : ℕ) (t : ℝ≥0) (ω : Ω₁) :
    |F.Mraw f n t ω| ≤ 2 * C + CL * t := by
  have hint : |∫ s in Ioc (0 : ℝ) t,
      switchOff (F.e n) (fun t ω => Lc f D0 (F.Yf n t ω)) s.toNNReal ω| ≤ CL * t := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := CL)
      (s := Ioc (0 : ℝ) (t : ℝ))
      (f := fun u : ℝ => switchOff (F.e n) (fun t ω => Lc f D0 (F.Yf n t ω)) u.toNNReal ω)
      measure_Ioc_lt_top fun u _ => by
        unfold switchOff; split_ifs
        · exact hCL _
        · simpa using hCL0
    rwa [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp),
      sub_zero] at h
  have h1 := hC (F.Yf n t ω)
  have h2 := hC (F.Yf n 0 ω)
  unfold Mraw
  calc _ ≤ |Fc f (F.Yf n t ω)| + |Fc f (F.Yf n 0 ω)| + |∫ s in Ioc (0 : ℝ) t,
        switchOff (F.e n) (fun t ω => Lc f D0 (F.Yf n t ω)) s.toNNReal ω| :=
          (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans (by linarith)
    _ ≤ _ := by linarith

/-- **The `dualMartingale` of the glued realization is a `𝓖₁`-martingale.** -/
theorem martingale_dualMartingale (hD0 : 0 < D0) (hz : z ∈ flatChamber 1)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ dualChamber 1) :
    Martingale (dualMartingale D0 1 f F.Nd F.Xd F.Yd) 𝓖₁ P₁ := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
  have hFc : ContDiff ℝ 2 (Fc f) := hf2.comp (ofFlat 1).contDiff
  have hLc : Continuous (Lc f D0) :=
    (continuous_dualGenerator D0 hf2 hfs).comp (ofFlat 1).continuous
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨CL', hCL'⟩ := (hasCompactSupport_dualGenerator D0 hfc).exists_bound_of_continuous
    (continuous_dualGenerator D0 hf2 hfs)
  set CL := max CL' 0
  have hCL0 : 0 ≤ CL := le_max_right _ _
  have hCw : ∀ w, |Fc f w| ≤ C := fun w => by rw [← Real.norm_eq_abs]; exact hC _
  have hCLw : ∀ w, |Lc f D0 w| ≤ CL := fun w => by
    rw [← Real.norm_eq_abs]; exact (hCL' _).trans (le_max_left _ _)
  set D := dualMartingale D0 1 f F.Nd F.Xd F.Yd with hDdef
  have hmart : ∀ n, HasMartingaleModification P₁ 𝓖₁ (F.Mraw f n) := fun n => by
    have h := F.hasMart_G hD0 n hFc.continuous.measurable hFc.contDiffOn
      (by rw [L₁_Fc f hf2]; exact hLc.continuousOn)
    rw [L₁_Fc f hf2] at h
    exact h
  choose M hM hMe using hmart
  have hgood : ∀ᵐ ω ∂P₁, ω ∈ F.good :=
    measure_eq_zero_iff_ae_notMem.1 (F.measure_good_compl hD0 hz) |>.mono fun _ h => not_not.1 h
  have hlim : ∀ t, ∀ᵐ ω ∂P₁, Tendsto (fun n => M n t ω) atTop (𝓝 (D t ω)) := fun t => by
    filter_upwards [hgood, ae_all_iff.2 fun n => hMe n t] with ω hω hn
    exact tendsto_const_nhds.congr' ((F.eventually_Mraw hz hfs hω t).mono fun n h =>
      ((hn n).trans h).symm)
  have hbd : ∀ t n, ∀ᵐ ω ∂P₁, ‖M n t ω‖ ≤ 2 * C + CL * t := fun t n => by
    filter_upwards [hMe n t] with ω h
    rw [h, Real.norm_eq_abs]; exact F.abs_Mraw_le hCw hCL0 hCLw n t ω
  have hoff : ∀ t ω, ω ∉ F.good → D t ω = -∫ u in Ioc (0 : ℝ) t, Lc f D0 z := fun t ω hω => by
    have hN : ∀ s, F.Nd s ω = 1 := fun s => by simp [Nd, hω]
    have hZ : ∀ s, F.Zd s ω = z := fun s => by simp [Zd, hω]
    rw [hDdef, F.dualMartingale_eq f hz]
    simp only [hN, hZ, ite_true, sub_self, zero_sub]
  have hadp : ∀ t, StronglyMeasurable[𝓖₁ t] (D t) := fun t => by
    classical
    have hprog : ∀ n, IsStronglyProgressive 𝓖₁
        (fun s ω => switchOff (F.e n) (fun t ω => Lc f D0 (F.Yf n t ω)) s ω) := fun n r => by
      have h := (F.isCSM_G hD0 n hFc.continuous.measurable hFc.contDiffOn).drift_progressive r
      rw [L₁_Fc f hf2] at h
      simpa [Function.comp_def] using (continuous_apply (0 : Fin 1)).comp_stronglyMeasurable h
    have hYm : ∀ n (s : ℝ≥0), s ≤ t → Measurable[𝓖₁ t] fun ω => Fc f (F.Yf n s ω) :=
      fun n s hs => hFc.continuous.measurable.comp
        ((F.measurable_Yf n s).mono (𝓖₁.mono hs) le_rfl)
    have hg : ∀ n, StronglyMeasurable[𝓖₁ t] (fun ω => if ω ∈ F.good then F.Mraw f n t ω
        else -∫ u in Ioc (0 : ℝ) t, Lc f D0 z) := fun n =>
      StronglyMeasurable.ite (F.measurableSet_good_aug hD0 hz t)
        ((((hYm n t le_rfl).sub (hYm n 0 zero_le)).stronglyMeasurable).sub
          (SemimartingaleIto.stronglyMeasurable_integral_of_progressive (hprog n) t))
        stronglyMeasurable_const
    refine stronglyMeasurable_of_tendsto atTop hg (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ F.good
    · exact tendsto_const_nhds.congr' ((F.eventually_Mraw hz hfs hω t).mono fun n h => by
        simp only [hω, ite_true, h, hDdef])
    · simp only [hω, ite_false, hoff t ω hω]; exact tendsto_const_nhds
  have hDbd : ∀ t, ∀ᵐ ω ∂P₁, ‖D t ω‖ ≤ 2 * C + CL * t := fun t => by
    filter_upwards [hlim t, ae_all_iff.2 (hbd t)] with ω h1 h2
    exact le_of_tendsto' (continuous_norm.tendsto _ |>.comp h1) h2
  have hint : ∀ t, Integrable (D t) P₁ := fun t =>
    Integrable.mono' (integrable_const _) ((hadp t).mono (𝓖₁.le t)).aestronglyMeasurable (hDbd t)
  have hset : ∀ u v : ℝ≥0, u ≤ v → ∀ B, MeasurableSet[𝓖₁ u] B →
      ∫ ω in B, D v ω ∂P₁ = ∫ ω in B, D u ω ∂P₁ := fun u v huv B hB => by
    have hDCT : ∀ t, Tendsto (fun n => ∫ ω in B, M n t ω ∂P₁) atTop
        (𝓝 (∫ ω in B, D t ω ∂P₁)) :=
      fun t => tendsto_integral_of_dominated_convergence (fun _ => 2 * C + CL * t)
        (fun n => ((hM n).integrable t).1.restrict) (integrable_const _)
        (fun n => ae_restrict_of_ae (hbd t n)) (ae_restrict_of_ae (hlim t))
    exact tendsto_nhds_unique ((hDCT v).congr fun n => ((hM n).setIntegral_eq huv hB).symm)
      (hDCT u)
  exact ⟨hadp, fun i j hij => (ae_eq_condExp_of_forall_setIntegral_eq (𝓖₁.le i) (hint j)
    (fun _ _ _ => (hint i).integrableOn) (fun s hs _ => (hset i j hij s hs).symm)
    (hadp i).aestronglyMeasurable).symm⟩

end SolFamily

/-- The flat start of a one-pair ordered interior start. -/
theorem flat_mem_of_ratio {x y : Fin 1 → ℝ} (hxy : IsRatioParameter x y) :
    (![x 0, y 0] : Fin 2 → ℝ) ∈ flatChamber 1 := by
  show ofFlat 1 ![x 0, y 0] ∈ dualChamber 1
  refine ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun i => ?_, fun i => ?_⟩
  · have := Fin.fin_one_eq_zero i; subst this; exact hxy.2.2.1 0
  · have := Fin.fin_one_eq_zero i; subst this; exact hxy.2.2.2 0

/-- **`exists_` for `p = 1`**: the conservative deletion law started at a one-pair ordered
interior point exists, on the driver space `Ω₁ : Type` with the augmented filtration. -/
theorem hasDualDeletionProcess_one {D0 : ℝ} (hD0 : 0 < D0) (x y : Fin 1 → ℝ)
    (hxy : IsRatioParameter x y) : HasDualDeletionProcess D0 x y := by
  set z : Fin 2 → ℝ := ![x 0, y 0] with hzdef
  have hz : z ∈ flatChamber 1 := flat_mem_of_ratio hxy
  obtain ⟨F⟩ := nonempty_solFamily hD0 z
  refine ⟨Ω₁, inferInstance, 𝓖₁, P₁, F.Nd, F.Xd, F.Yd,
    { prob := inferInstance
      adapted := fun t => ⟨F.measurable_Nd hD0 hz t,
        (continuous_pi fun _ => continuous_apply 0).measurable.comp (F.measurable_Zd hD0 hz t),
        (continuous_pi fun _ => continuous_apply 1).measurable.comp (F.measurable_Zd hD0 hz t)⟩
      start := Eventually.of_forall fun ω => ⟨F.Nd_zero ω, fun i => ?_⟩
      paths := ?_
      martingale := fun q hq hq1 f hf hfc hfs => ?_ }⟩
  · have := Fin.fin_one_eq_zero i; subst this
    simp [SolFamily.Xd, SolFamily.Yd, F.Zd_zero hz, hzdef]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (F.measure_good_compl hD0 hz)] with ω hω
    exact F.isDeletionPath_of_good hz (not_not.1 hω)
  · obtain rfl : q = 1 := le_antisymm hq1 hq
    exact F.martingale_dualMartingale hD0 hz hf hfc hfs

end BlockBand.Transmission.Dual.Exists
