module

public import BlockBand.Transmission.Dual.GStageIto

/-!
# The first-stage martingale at the top level

For `F : B1R D₀ (q+1) μ ξ` and a test `f ∈ C_c^∞(𝒞_{q+1})`, with `ρ₁ = ζ` on `good` and `⊤` off
it (`rho1`, a stopping time):
* `M1 f t = 1{t < ρ₁} f(Zs t) − f(ξ) − ∫_(0,t] 1{u < ρ₁} 𝒟f(Zs u) du` (flat coordinates);
* `eventually_Mraw`: on `good` the compensated `n`-th processes `Mraw n` are eventually `M1`
  (before `ζ` the paths agree; after `ζ`, `f` and `𝒟f` vanish near the corner `corner_spec`);
* **`martingale_M1`**: `M1 f` is a `𝓖R`-martingale under `PR μ (q+1)` (dominated
  convergence; global bounds of `f` and `𝒟f`, compact support). This is the random-start
  analogue of `martingale_dualMartingale`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ}
variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin ((q + 1) + (q + 1)) → ℝ}

/-- A test in flat coordinates. -/
def flatT {p : ℕ} (f : DualCoord p → ℝ) : (Fin (p + p) → ℝ) → ℝ := fun w => f (ofFlat p w)

/-- Its generator in flat coordinates. -/
def flatGen {p : ℕ} (D0 : ℝ) (f : DualCoord p → ℝ) : (Fin (p + p) → ℝ) → ℝ :=
  fun w => dualGenerator D0 f (ofFlat p w)

theorem Lq_flatT {p : ℕ} {f : DualCoord p → ℝ} (hf : ContDiff ℝ 2 f) :
    Lq D0 p (flatT f) = flatGen D0 f :=
  funext fun w => mpGenerator_flat D0 hf w

namespace B1R

variable (F : B1R D0 (q + 1) μ ξ)

open scoped Classical in
/-- The first deletion time of the first stage: `ζ` on `good`, `⊤` off it. -/
def rho1 (x : ΩR S (q + 1)) : WithTop ℝ≥0 := if x ∈ F.good then F.zeta x else ⊤

theorem rho1_le_iff {x : ΩR S (q + 1)} {t : ℝ≥0} :
    F.rho1 x ≤ t ↔ x ∈ F.good ∧ F.zeta x ≤ t := by
  unfold rho1; split_ifs with h
  · simp [h]
  · simp only [h, false_and, iff_false, not_le]; exact WithTop.coe_lt_top t

theorem isStoppingTime_rho1 (hD0 : 0 < D0) (hξ : Measurable ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) : IsStoppingTime (𝓖R μ (q + 1)) F.rho1 := by
  intro t
  have e : {x | F.rho1 x ≤ t} = F.good ∩ {x | F.zeta x ≤ t} := by
    ext x; exact F.rho1_le_iff
  rw [e]; exact (F.measurableSet_good_aug hD0 hξ hξc t).inter (F.measurableSet_zeta_le t)

theorem measurable_rho1 (hD0 : 0 < D0) (hξ : Measurable ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) : Measurable F.rho1 :=
  (F.isStoppingTime_rho1 hD0 hξ hξc).measurable'

theorem rho1_pos (x : ΩR S (q + 1)) : (0 : WithTop ℝ≥0) < F.rho1 x := by
  unfold rho1; split_ifs
  · exact F.zeta_pos x
  · exact WithTop.coe_lt_top 0

variable (f : DualCoord (q + 1) → ℝ)

/-- **The first-stage martingale** of a level-`(q+1)` test. -/
def M1 (t : ℝ≥0) (x : ΩR S (q + 1)) : ℝ :=
  (if (t : WithTop ℝ≥0) < F.rho1 x then flatT f (F.Zs t x) else 0) - flatT f (ξ x.1) -
    ∫ u in Ioc (0 : ℝ) t,
      if (u.toNNReal : WithTop ℝ≥0) < F.rho1 x then flatGen D0 f (F.Zs u.toNNReal x) else 0

/-- The compensated `n`-th process of the test. -/
def Mraw (n : ℕ) (t : ℝ≥0) (x : ΩR S (q + 1)) : ℝ :=
  flatT f (F.Yf n t x) - flatT f (F.Yf n 0 x) -
    ∫ s in Ioc (0 : ℝ) t, switchOff (F.e n) (fun t x => flatGen D0 f (F.Yf n t x)) s.toNNReal x

variable {f}

theorem vanish_corner (hfs : tsupport f ⊆ dualChamber (q + 1)) {c : Fin ((q + 1) + (q + 1)) → ℝ}
    (hc : IsCorner q c) :
    IsOpen {w | ofFlat (q + 1) w ∉ tsupport f} ∧ c ∈ {w | ofFlat (q + 1) w ∉ tsupport f} ∧
      ∀ w ∈ {w | ofFlat (q + 1) w ∉ tsupport f}, flatT f w = 0 ∧ flatGen D0 f w = 0 := by
  refine ⟨(isClosed_tsupport f).preimage (ofFlat (q + 1)).continuous |>.isOpen_compl,
    fun h => ?_, fun w hw =>
      ⟨show f (ofFlat (q + 1) w) = 0 from image_eq_zero_of_notMem_tsupport hw,
      dualGenerator_eq_zero_of_notMem_tsupport hw⟩⟩
  have := (hfs h).2.2.1 0
  rw [hc.1] at this
  exact lt_irrefl _ this

theorem M1_of_notMem_good {x : ΩR S (q + 1)} (hx : x ∉ F.good) (t : ℝ≥0) :
    F.M1 f t x = -∫ _ in Ioc (0 : ℝ) t, flatGen D0 f (ξ x.1) := by
  simp only [M1, rho1, hx, ↓reduceIte, WithTop.coe_lt_top, Zs, sub_self, zero_sub]

/-- **On `good`, the `n`-th compensated process is eventually `M1`.** -/
theorem eventually_Mraw (hξc : ∀ s, ξ s ∈ flatChamber (q + 1))
    (hfs : tsupport f ⊆ dualChamber (q + 1)) {x : ΩR S (q + 1)} (hx : x ∈ F.good) (t : ℝ≥0) :
    ∀ᶠ n in atTop, F.Mraw f n t x = F.M1 f t x := by
  have hc := (F.good_spec hx).1
  have hρ : F.rho1 x = F.zeta x := by simp only [rho1, hx, ↓reduceIte]
  have hZs : ∀ u, F.Zs u x = F.Z u x := fun u => by simp only [Zs, hx, ↓reduceIte]
  simp only [M1, Mraw, hρ, hZs, F.Yf_zero hξc]
  by_cases ht : (t : WithTop ℝ≥0) < F.zeta x
  · obtain ⟨n₀, hn₀⟩ := lt_iSup_iff.1 ht
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have htn : (t : WithTop ℝ≥0) < F.e n x := hn₀.trans_le (hc n₀ n hn).1
    simp only [ht, ↓reduceIte, F.Z_eq hc htn.le]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs' : (s.toNNReal : WithTop ℝ≥0) ≤ t :=
      WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    simp only [switchOff, hs'.trans htn.le, ↓reduceIte, hs'.trans_lt ht,
      F.Z_eq hc (hs'.trans htn.le)]
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top
      (not_lt.1 ht))
    have hζ : F.zeta x = m := hm.symm
    have hfin : x ∈ F.finE := ⟨hx, show F.zeta x < ⊤ by rw [hζ]; exact WithTop.coe_lt_top m⟩
    obtain ⟨hcor, hlim⟩ := F.corner_spec hfin
    rw [hζ] at hlim
    obtain ⟨hO, h0, hvan⟩ := vanish_corner (D0 := D0) hfs hcor
    have hm0 : 0 < m := by
      have := F.zeta_pos x; rw [hζ] at this; exact WithTop.coe_lt_coe.1 this
    obtain ⟨s₀, hs₀, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hm0).1
      (hlim (hO.mem_nhds h0))
    obtain ⟨n₀, hn₀⟩ := lt_iSup_iff.1 (show (s₀ : WithTop ℝ≥0) < F.zeta x by
      rw [hζ]; exact WithTop.coe_lt_coe.2 hs₀)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hlt := F.e_lt_zeta hc (by rw [hζ]; exact WithTop.coe_lt_top m) n
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hs₀r : s₀ < r := WithTop.coe_lt_coe.1 (hr ▸ hn₀.trans_le (hc n₀ n hn).1)
    have hrm : r < m := WithTop.coe_lt_coe.1 (by rw [hr, ← hζ]; exact hlt)
    have hrt : r ≤ t := (hrm.trans_le (WithTop.coe_le_coe.1 (hζ ▸ not_lt.1 ht))).le
    have hY : F.Yf n t x = F.Z r x := by
      rw [F.Z_eq hc (hr ▸ le_rfl : (r : WithTop ℝ≥0) ≤ F.e n x)]
      simp only [Yf, F.X_eq_of_e_le n hr.symm hrt]
    simp only [ht, ↓reduceIte, hY, (hvan _ (hsub ⟨hs₀r, hrm⟩)).1]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    by_cases h1 : (s.toNNReal : WithTop ℝ≥0) ≤ F.e n x
    · simp only [switchOff, h1, ↓reduceIte, h1.trans_lt hlt, F.Z_eq hc h1]
    · simp only [switchOff, h1, ↓reduceIte]
      have hrs : r < s.toNNReal := WithTop.coe_lt_coe.1 (hr ▸ not_le.1 h1)
      by_cases h2 : (s.toNNReal : WithTop ℝ≥0) < F.zeta x
      · have hsm : s.toNNReal < m := WithTop.coe_lt_coe.1 (hζ ▸ h2)
        simp only [h2, ↓reduceIte, (hvan _ (hsub ⟨hs₀r.trans hrs, hsm⟩)).2]
      · simp only [h2, ↓reduceIte]

theorem abs_integral_le {g : ℝ → ℝ} {CL : ℝ} (hg : ∀ u, |g u| ≤ CL)
    (t : ℝ≥0) : |∫ s in Ioc (0 : ℝ) t, g s| ≤ CL * t := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := CL)
    (s := Ioc (0 : ℝ) (t : ℝ)) (f := g) measure_Ioc_lt_top fun u _ => hg u
  rwa [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp),
    sub_zero] at h

theorem abs_Mraw_le {C CL : ℝ} (hC : ∀ w, |flatT f w| ≤ C) (hCL0 : 0 ≤ CL)
    (hCL : ∀ w, |flatGen D0 f w| ≤ CL) (n : ℕ) (t : ℝ≥0) (x : ΩR S (q + 1)) :
    |F.Mraw f n t x| ≤ 2 * C + CL * t := by
  have hint := abs_integral_le (g := fun s : ℝ =>
    switchOff (F.e n) (fun t x => flatGen D0 f (F.Yf n t x)) s.toNNReal x) (fun u => by
      unfold switchOff; split_ifs
      · exact hCL _
      · simpa using hCL0) t
  have h1 := hC (F.Yf n t x)
  have h2 := hC (F.Yf n 0 x)
  unfold Mraw
  calc _ ≤ |flatT f (F.Yf n t x)| + |flatT f (F.Yf n 0 x)| + |∫ s in Ioc (0 : ℝ) t,
        switchOff (F.e n) (fun t x => flatGen D0 f (F.Yf n t x)) s.toNNReal x| :=
          (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans (by linarith)
    _ ≤ _ := by linarith

/-- **The first-stage martingale is a `𝓖R`-martingale.** -/
theorem martingale_M1 (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (q + 1))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ dualChamber (q + 1)) :
    Martingale (F.M1 f) (𝓖R μ (q + 1)) (PR μ (q + 1)) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_cast)
  have hFc : ContDiff ℝ 2 (flatT f) := hf2.comp (ofFlat (q + 1)).contDiff
  have hLc : Continuous (flatGen D0 f) :=
    (continuous_dualGenerator D0 hf2 hfs).comp (ofFlat (q + 1)).continuous
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨CL', hCL'⟩ := (hasCompactSupport_dualGenerator D0 hfc).exists_bound_of_continuous
    (continuous_dualGenerator D0 hf2 hfs)
  set CL := max CL' 0
  have hCL0 : 0 ≤ CL := le_max_right _ _
  have hCw : ∀ w, |flatT f w| ≤ C := fun w => by rw [← Real.norm_eq_abs]; exact hC _
  have hCLw : ∀ w, |flatGen D0 f w| ≤ CL := fun w => by
    rw [← Real.norm_eq_abs]; exact (hCL' _).trans (le_max_left _ _)
  set D := F.M1 f with hDdef
  have hmart : ∀ n, HasMartingaleModification (PR μ (q + 1)) (𝓖R μ (q + 1)) (F.Mraw f n) :=
    fun n => by
      have h := F.hasMart_G hD0 n hFc.continuous.measurable hFc.contDiffOn hCw hCL0
        (fun w _ => by rw [Lq_flatT hf2]; exact hCLw w)
      rw [Lq_flatT hf2] at h
      exact h
  choose M hM hMe using hmart
  have hgood : ∀ᵐ x ∂PR μ (q + 1), x ∈ F.good :=
    measure_eq_zero_iff_ae_notMem.1 (F.measure_good_compl hD0 hξ hξc) |>.mono fun _ h =>
      not_not.1 h
  have hlim : ∀ t, ∀ᵐ x ∂PR μ (q + 1), Tendsto (fun n => M n t x) atTop (𝓝 (D t x)) :=
    fun t => by
      filter_upwards [hgood, ae_all_iff.2 fun n => hMe n t] with x hx hn
      exact tendsto_const_nhds.congr' ((F.eventually_Mraw hξc hfs hx t).mono fun n h =>
        ((hn n).trans h).symm)
  have hbd : ∀ t n, ∀ᵐ x ∂PR μ (q + 1), ‖M n t x‖ ≤ 2 * C + CL * t := fun t n => by
    filter_upwards [hMe n t] with x h
    rw [h, Real.norm_eq_abs]; exact F.abs_Mraw_le hCw hCL0 hCLw n t x
  have hadp : ∀ t, StronglyMeasurable[𝓖R μ (q + 1) t] (D t) := fun t => by
    classical
    have hprog : ∀ n, IsStronglyProgressive (𝓖R μ (q + 1))
        (fun s x => switchOff (F.e n) (fun t x => flatGen D0 f (F.Yf n t x)) s x) := fun n r => by
      have h := (F.isCSM_G hD0 n hFc.continuous.measurable hFc.contDiffOn).drift_progressive r
      rw [Lq_flatT hf2] at h
      simpa [Function.comp_def] using (continuous_apply (0 : Fin 1)).comp_stronglyMeasurable h
    have hYm : ∀ n (s : ℝ≥0), s ≤ t →
        Measurable[𝓖R μ (q + 1) t] fun x => flatT f (F.Yf n s x) :=
      fun n s hs => hFc.continuous.measurable.comp
        ((F.measurable_Yf_t n s).mono ((𝓖R μ (q + 1)).mono hs) le_rfl)
    have hoffm : StronglyMeasurable[𝓖R μ (q + 1) t]
        fun x : ΩR S (q + 1) => -∫ _ in Ioc (0 : ℝ) t, flatGen D0 f (ξ x.1) := by
      simp only [setIntegral_const]
      have hm : Measurable[𝓖R μ (q + 1) t] fun x : ΩR S (q + 1) => flatGen D0 f (ξ x.1) :=
        (measurable_fst_zero μ (hLc.measurable.comp hξ)).mono ((𝓖R μ (q + 1)).mono zero_le) le_rfl
      exact ((hm.const_smul (volume.real (Ioc (0 : ℝ) t))).neg).stronglyMeasurable
    have hg : ∀ n, StronglyMeasurable[𝓖R μ (q + 1) t] (fun x => if x ∈ F.good then
        F.Mraw f n t x else -∫ _ in Ioc (0 : ℝ) t, flatGen D0 f (ξ x.1)) := fun n =>
      StronglyMeasurable.ite (F.measurableSet_good_aug hD0 hξ hξc t)
        ((((hYm n t le_rfl).sub (hYm n 0 zero_le)).stronglyMeasurable).sub
          (SemimartingaleIto.stronglyMeasurable_integral_of_progressive (hprog n) t))
        hoffm
    refine stronglyMeasurable_of_tendsto atTop hg (tendsto_pi_nhds.2 fun x => ?_)
    by_cases hx : x ∈ F.good
    · exact tendsto_const_nhds.congr' ((F.eventually_Mraw hξc hfs hx t).mono fun n h => by
        simp only [hx, ↓reduceIte, h, hDdef])
    · simp only [hx, ↓reduceIte, hDdef, F.M1_of_notMem_good hx t]; exact tendsto_const_nhds
  have hDbd : ∀ t, ∀ᵐ x ∂PR μ (q + 1), ‖D t x‖ ≤ 2 * C + CL * t := fun t => by
    filter_upwards [hlim t, ae_all_iff.2 (hbd t)] with x h1 h2
    exact le_of_tendsto' (continuous_norm.tendsto _ |>.comp h1) h2
  have hint : ∀ t, Integrable (D t) (PR μ (q + 1)) := fun t =>
    Integrable.mono' (integrable_const _)
      ((hadp t).mono ((𝓖R μ (q + 1)).le t)).aestronglyMeasurable (hDbd t)
  have hset : ∀ u v : ℝ≥0, u ≤ v → ∀ B, MeasurableSet[𝓖R μ (q + 1) u] B →
      ∫ x in B, D v x ∂PR μ (q + 1) = ∫ x in B, D u x ∂PR μ (q + 1) := fun u v huv B hB => by
    have hDCT : ∀ t, Tendsto (fun n => ∫ x in B, M n t x ∂PR μ (q + 1)) atTop
        (𝓝 (∫ x in B, D t x ∂PR μ (q + 1))) :=
      fun t => tendsto_integral_of_dominated_convergence (fun _ => 2 * C + CL * t)
        (fun n => ((hM n).integrable t).1.restrict) (integrable_const _)
        (fun n => ae_restrict_of_ae (hbd t n)) (ae_restrict_of_ae (hlim t))
    exact tendsto_nhds_unique ((hDCT v).congr fun n => ((hM n).setIntegral_eq huv hB).symm)
      (hDCT u)
  exact ⟨hadp, fun i j hij => (ae_eq_condExp_of_forall_setIntegral_eq ((𝓖R μ (q + 1)).le i)
    (hint j) (fun _ _ _ => (hint i).integrableOn) (fun s hs _ => (hset i j hij s hs).symm)
    (hadp i).aestronglyMeasurable).symm⟩

end B1R

end BlockBand.Transmission.Dual.G
