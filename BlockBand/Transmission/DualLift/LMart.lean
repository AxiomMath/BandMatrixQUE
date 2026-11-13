module

public import BlockBand.Transmission.DualLift.Flat
public import BlockBand.Transmission.Dual.ExistsMart

/-!
# Martingales and supermartingales along the flat paths of the lift

Setting: `(LΩ S, L𝓖 μ, LP μ)`, `D₀ > 0`, `IsLiftStart μ ξ`, a `LiftFamily μ D₀ ξ`, and
`L₁ = mpGenerator (flatDrift D₀ 1) (flatDiff D₀ 1)`. The open set `flatU` replaces the open
chamber, so boundary starts are allowed. For `G` measurable and `C²` on `flatU`:
* `isCSM_G`: `G(Yf n)` is a continuous semimartingale with drift `1{t ≤ e_n} L₁G(Yf n)`
  (Itô's formula on `U = flatU`);
* `hasMart_G`: if `L₁G` is continuous on `flatU`, the compensated process of `G(Yf n)` has a
  martingale modification. Starts may be random and unbounded: on `{‖ξ‖ ≥ n}` the exit time is
  `0` and the compensated process vanishes; on `{‖ξ‖ < n}` the path stays in `flatK (max n 1)`.

The discounted bound is proved from these in the sibling module,
`LiftFamily.lintegral_discount_le`: if `0 ≤ G` and `L₁G ≤ cG` on the closed strip minus the
corner (`flatStrip`), then for every stopping time `θ`, `T` and `A ∈ 𝓖₀`, with `G(π ξ) ≤ B` on `A`,
`∫_A e^{−c(T∧θ)} G(Yf n (T∧θ)) ≤ ∫_A G(π ξ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

/-- The closed strip minus the corner, `{x ≥ 0, 0 ≤ y ≤ 1, x + y > 0}`. -/
def flatStrip : Set (Fin 2 → ℝ) := {z | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1 ∧ 0 < z 0 + z 1}

theorem flatK_subset_strip {R : ℝ} (hR : 0 < R) : flatK R ⊆ flatStrip := fun _ hz =>
  ⟨hz.2.1, hz.2.2.2.1, hz.2.2.2.2, lt_of_lt_of_le (by positivity) hz.1⟩

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

theorem Yf_mem_strip (hξ : IsLiftStart μ ξ) (n : ℕ) (t : ℝ≥0) (ω : LΩ S) :
    F.Yf n t ω ∈ flatStrip :=
  flatK_subset_strip (lt_of_lt_of_le one_pos (le_max_right _ _)) (F.Yf_mem_flatK hξ n t ω)

theorem mpGenerator_switchOff (n : ℕ) {G : (Fin 2 → ℝ) → ℝ} (t : ℝ≥0) (ω : LΩ S) :
    mpGenerator (fun _ => switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω)
      (fun _ => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω) G (F.Yf n t ω) =
      switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω := by
  unfold switchOff
  split_ifs
  · rfl
  · simp [mpGenerator]

/-- **`G(Yf n)` is a continuous semimartingale** with drift `1{t ≤ e_n} L₁G(Yf n)`. -/
theorem isCSM_G (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) {G : (Fin 2 → ℝ) → ℝ}
    (hGm : Measurable G) (hG : ContDiffOn ℝ 2 G flatU) :
    IsContinuousSemimartingale (d := 1) (LP μ) (L𝓖 μ) (fun t ω (_ : Fin 1) => G (F.Yf n t ω))
      (fun t ω (_ : Fin 1) => switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω)
      (fun t ω => Matrix.of fun (_ _ : Fin 1) => itoBracket (fun q : ℝ × (Fin 2 → ℝ) => G q.2)
        (F.Yf n t ω) t (switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω)) := by
  have hφ : ContDiffOn ℝ 2 (fun q : ℝ × (Fin 2 → ℝ) => G q.2) (univ ×ˢ flatU) :=
    hG.comp contDiffOn_snd fun q hq => hq.2
  have H := SemimartingaleIto.semimartingaleItoFormula_holds 2 (LΩ S) (LP μ) (L𝓖 μ) (F.Yf n) _ _
    (F.isCSM_Yf hD0 hξ n) flatU isOpen_flatU
    (Eventually.of_forall fun ω t => F.Yf_mem_flatU hξ n t ω) (fun q : ℝ × (Fin 2 → ℝ) => G q.2)
    (hGm.comp measurable_snd) hφ
  have e : (fun (t : ℝ≥0) (ω : LΩ S) (_ : Fin 1) =>
      itoDrift (fun q : ℝ × (Fin 2 → ℝ) => G q.2)
      (F.Yf n t ω) t (switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω)
      (switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω)) =
      fun t ω _ => switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω := by
    funext t ω _
    rw [itoDrift_comp_snd ((hG.contDiffAt (isOpen_flatU.mem_nhds (F.Yf_mem_flatU hξ n t ω))))]
    exact F.mpGenerator_switchOff n t ω
  rw [e] at H
  exact H

/-- At a start outside the ball of radius `n`, the exit time is `0`. -/
theorem e_eq_zero {n : ℕ} {ω : LΩ S} (h : (n : ℝ) ≤ ‖ξ ω‖) : F.e n ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine (iInf₂_le (0 : ℝ≥0) ?_).trans (le_of_eq rfl)
  rw [F.X_zero]; exact h

theorem X_eq_start {n : ℕ} {ω : LΩ S} (h : (n : ℝ) ≤ ‖ξ ω‖) (t : ℝ≥0) : F.X n t ω = ξ ω := by
  rw [F.X_eq_of_e_le n (F.e_eq_zero h) (zero_le : (0 : ℝ≥0) ≤ t), F.X_zero]

/-- **The compensated process of `G(Yf n)` has a martingale modification.** -/
theorem hasMart_G (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) {G : (Fin 2 → ℝ) → ℝ}
    (hGm : Measurable G) (hG : ContDiffOn ℝ 2 G flatU) (hL : ContinuousOn (L₁ D0 G) flatU) :
    HasMartingaleModification (LP μ) (L𝓖 μ) (fun t ω => G (F.Yf n t ω) - G (F.Yf n 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) s.toNNReal ω) := by
  obtain ⟨τ, -, hτlim, hm⟩ := (F.isCSM_G hD0 hξ n hGm hG).localizing
  have hK : flatK (max (n : ℝ) 1) ⊆ flatU := flatK_subset (lt_of_lt_of_le one_pos (le_max_right _ _))
  obtain ⟨CG, hCG⟩ := (isCompact_flatK (max (n : ℝ) 1)).exists_bound_of_continuousOn
    (hG.continuousOn.mono hK)
  obtain ⟨CL, hCL⟩ := (isCompact_flatK (max (n : ℝ) 1)).exists_bound_of_continuousOn
    (hL.mono hK)
  have hCL0 : 0 ≤ max CL 0 := le_max_right _ _
  have hG' : ∀ᵐ ω ∂LP μ, ω ∈ F.good := by rw [ae_iff]; exact F.measure_good_compl hD0 hξ
  refine Bridges.hasMartingaleModification_of_localized hτlim (fun k => (hm k).1 0)
    fun t => ⟨2 * max CG 0 + max CL 0 * t, ?_⟩
  filter_upwards [hG'] with ω hω s hs
  show |G (F.Yf n s ω) - G (F.Yf n 0 ω) - _| ≤ _
  by_cases hξn : (n : ℝ) ≤ ‖ξ ω‖
  · have hY : ∀ u, F.Yf n u ω = F.Yf n 0 ω := fun u => by
      rw [F.Yf_of_good hω, F.Yf_of_good hω, Zp, Zp, F.X_eq_start hξn, F.X_eq_start hξn]
    have hI : ∫ u in Ioc (0 : ℝ) s,
        switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) u.toNNReal ω = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      have hpos : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
      unfold switchOff
      rw [F.e_eq_zero hξn]
      split_ifs with h0
      · exact absurd (WithTop.coe_le_coe.1 h0) (not_le.2 hpos)
      · rfl
    rw [hY s, hI]; simp only [sub_self, abs_zero]
    positivity
  · have hR : max (max (n : ℝ) ‖ξ ω‖) 1 = max (n : ℝ) 1 := by
      rw [max_eq_left (le_of_lt (not_le.1 hξn))]
    have hmem : ∀ u, F.Yf n u ω ∈ flatK (max (n : ℝ) 1) := fun u => hR ▸ F.Yf_mem_flatK hξ n u ω
    have hb : ∀ u, |G (F.Yf n u ω)| ≤ max CG 0 := fun u =>
      (Real.norm_eq_abs _ ▸ hCG _ (hmem u)).trans (le_max_left _ _)
    have hint : |∫ u in Ioc (0 : ℝ) s,
        switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) u.toNNReal ω| ≤ max CL 0 * t := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := max CL 0)
        (s := Ioc (0 : ℝ) (s : ℝ))
        (f := fun u : ℝ => switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) u.toNNReal ω)
        measure_Ioc_lt_top fun u _ => by
          unfold switchOff; split_ifs
          · exact (hCL _ (hmem _)).trans (le_max_left _ _)
          · simp
      rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp)] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hCL0)
      simpa using (NNReal.coe_le_coe.2 hs)
    have h1 := hb s
    have h2 := hb 0
    calc _ ≤ |G (F.Yf n s ω)| + |G (F.Yf n 0 ω)| + |∫ u in Ioc (0 : ℝ) s,
          switchOff (F.e n) (fun t ω => L₁ D0 G (F.Yf n t ω)) u.toNNReal ω| := by
            refine (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans ?_
            linarith
      _ ≤ _ := by linarith

end LiftFamily

end BlockBand.Transmission.DualLift
