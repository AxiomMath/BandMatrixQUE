module

public import BlockBand.Transmission.DualLift.LReal
public import BlockBand.Transmission.Dual.ExistsOne

/-!
# The martingale clause of the lifted realization

Boundary and random starts. For a test `f ∈ C_c^∞(𝒞₁)`, the compensated processes
`Mraw n = F(Yf n) − F(π ξ) − ∫ 1{s ≤ e_n} 𝒟₁f(Yf n s) ds` (`F = f ∘ ofFlat 1`) have martingale
modifications (`hasMart_G` on `flatU`; `L₁ F = 𝒟₁ f ∘ ofFlat 1` by `mpGenerator_flat`). On
`good₂` they are eventually equal to `dualMartingale` of `(N₂, X₂, Y₂)` (`eventually_Mraw₂`):
before `ζ` the paths agree; after `ζ` because `f`, `𝒟₁f` vanish near the corner, which the path
approaches (the corner limit). The entrance value is `F(π ξ)`; at a boundary start it is `0`.
Uniform bounds (`abs_Mraw_le`) and dominated convergence give, in the sibling module,
**`LiftFamily.martingale_dualMartingale₂`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Transmission
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ) (f : DualCoord 1 → ℝ)

/-- The compensated `n`-th process of the test. -/
def Mraw (n : ℕ) (t : ℝ≥0) (ω : LΩ S) : ℝ :=
  liftFc f (F.Yf n t ω) - liftFc f (F.Yf n 0 ω) -
    ∫ s in Ioc (0 : ℝ) t, switchOff (F.e n) (fun t ω => liftLc f D0 (F.Yf n t ω)) s.toNNReal ω

theorem L₁_liftFc (hf : ContDiff ℝ 2 f) : L₁ D0 (liftFc f) = liftLc f D0 :=
  funext fun w => mpGenerator_flat D0 hf w

variable {f}

theorem eventually_Mraw₂ (hξ : IsLiftStart μ ξ) (hfs : tsupport f ⊆ dualChamber 1) {ω : LΩ S}
    (hω₂ : ω ∈ F.good₂) (t : ℝ≥0) :
    ∀ᶠ n in atTop, F.Mraw f n t ω = dualMartingale D0 1 f F.N₂ F.X₂ F.Y₂ t ω := by
  obtain ⟨hω, hcv⟩ := F.good₂_spec hω₂
  have hc := (F.good_spec hω).2
  have hN : ∀ s, F.N₂ s ω = F.Nd s ω := fun s => by simp only [N₂, hω₂, ite_true]
  have hZ : ∀ s, F.Z₂ s ω = F.Zd s ω := fun s => by simp only [Z₂, hω₂, ite_true]
  rw [F.dualMartingale_eq₂ f]
  simp only [hN, hZ]
  by_cases ht : (t : WithTop ℝ≥0) < F.zeta ω
  · obtain ⟨n₀, hn₀⟩ := lt_iSup_iff.1 ht
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have htn : (t : WithTop ℝ≥0) < F.e n ω := hn₀.trans_le (hc n₀ n hn).1
    simp only [Mraw, F.Nd_of_lt hω ht, ite_true, F.Zd_eq hω htn.le, F.Yf_zero]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs' : (s.toNNReal : WithTop ℝ≥0) ≤ t :=
      WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    simp only [switchOff, hs'.trans htn.le, ite_true, F.Nd_of_lt hω (hs'.trans_lt ht),
      F.Zd_eq hω (hs'.trans htn.le)]
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top
      (not_lt.1 ht))
    have hζ : F.zeta ω = m := hm.symm
    obtain ⟨hO, h0, hvan⟩ := SolFamily.vanish_near_corner (D0 := D0) hfs
    have hvan' : ∀ w ∈ {w : Fin 2 → ℝ | ofFlat 1 w ∉ tsupport f},
        liftFc f w = 0 ∧ liftLc f D0 w = 0 := hvan
    have hlim : Tendsto (fun u => F.Zd u ω) (𝓝[<] m) (𝓝 0) :=
      tendsto_pi_nhds.2 fun i => F.tendsto_Zd hξ hω hcv hζ i
    have hm0 : 0 < m := by have := F.zeta_pos ω; rw [hζ] at this; exact WithTop.coe_lt_coe.1 this
    obtain ⟨s₀, hs₀, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hm0).1
      (hlim (hO.mem_nhds h0))
    obtain ⟨n₀, hn₀⟩ := lt_iSup_iff.1 (show (s₀ : WithTop ℝ≥0) < F.zeta ω by
      rw [hζ]; exact WithTop.coe_lt_coe.2 hs₀)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hlt := F.e_lt_zeta hω (by rw [hζ]; exact WithTop.coe_lt_top m) n
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hs₀r : s₀ < r := WithTop.coe_lt_coe.1 (hr ▸ hn₀.trans_le (hc n₀ n hn).1)
    have hrm : r < m := WithTop.coe_lt_coe.1 (by rw [hr, ← hζ]; exact hlt)
    have hrt : r ≤ t := (hrm.trans_le (WithTop.coe_le_coe.1 (hζ ▸ not_lt.1 ht))).le
    have hNt : F.Nd t ω = 0 := F.Nd_of_le hω (not_lt.1 ht)
    have hY : F.Yf n t ω = F.Zd r ω := by
      rw [F.Zd_eq hω (hr ▸ le_rfl : (r : WithTop ℝ≥0) ≤ F.e n ω), F.Yf_of_good hω,
        F.Yf_of_good hω, Zp, Zp, F.X_eq_of_e_le n hr.symm hrt]
    simp only [Mraw, hNt, zero_ne_one, ite_false, hY, (hvan' _ (hsub ⟨hs₀r, hrm⟩)).1, F.Yf_zero]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    by_cases h1 : (s.toNNReal : WithTop ℝ≥0) ≤ F.e n ω
    · simp only [switchOff, h1, ite_true, F.Nd_of_lt hω (h1.trans_lt hlt), F.Zd_eq hω h1]
    · simp only [switchOff, h1, ite_false]
      have hrs : r < s.toNNReal := WithTop.coe_lt_coe.1 (hr ▸ not_le.1 h1)
      by_cases h2 : (s.toNNReal : WithTop ℝ≥0) < F.zeta ω
      · have hsm : s.toNNReal < m := WithTop.coe_lt_coe.1 (hζ ▸ h2)
        rw [F.Nd_of_lt hω h2]
        simp only [↓reduceIte, (hvan' _ (hsub ⟨hs₀r.trans hrs, hsm⟩)).2]
      · rw [F.Nd_of_le hω (not_lt.1 h2)]; simp

theorem abs_Mraw_le {C CL : ℝ} (hC : ∀ w, |liftFc f w| ≤ C) (hCL0 : 0 ≤ CL)
    (hCL : ∀ w, |liftLc f D0 w| ≤ CL) (n : ℕ) (t : ℝ≥0) (ω : LΩ S) :
    |F.Mraw f n t ω| ≤ 2 * C + CL * t := by
  have hint : |∫ s in Ioc (0 : ℝ) t,
      switchOff (F.e n) (fun t ω => liftLc f D0 (F.Yf n t ω)) s.toNNReal ω| ≤ CL * t := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := CL)
      (s := Ioc (0 : ℝ) (t : ℝ))
      (f := fun u : ℝ => switchOff (F.e n) (fun t ω => liftLc f D0 (F.Yf n t ω)) u.toNNReal ω)
      measure_Ioc_lt_top fun u _ => by
        unfold switchOff; split_ifs
        · exact hCL _
        · simpa using hCL0
    rwa [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp),
      sub_zero] at h
  have h1 := hC (F.Yf n t ω)
  have h2 := hC (F.Yf n 0 ω)
  unfold Mraw
  calc _ ≤ |liftFc f (F.Yf n t ω)| + |liftFc f (F.Yf n 0 ω)| + |∫ s in Ioc (0 : ℝ) t,
        switchOff (F.e n) (fun t ω => liftLc f D0 (F.Yf n t ω)) s.toNNReal ω| :=
          (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans (by linarith)
    _ ≤ _ := by linarith

end LiftFamily

end BlockBand.Transmission.DualLift
