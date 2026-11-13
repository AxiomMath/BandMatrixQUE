module

public import BlockBand.Transmission.Dual.GB1RSurv
public import BlockBand.Transmission.Dual.ExistsMart

/-!
# Itô's formula along a random-start family

The analogue of `isCSM_G` / `hasMart_G` from the level-one family on `Ω₁` for the random-start
family `F : B1R D₀ q μ ξ` on `ΩR S q`, with `L_q = mpGenerator (flatDrift D₀ q) (flatDiff D₀ q)`:
* `isCSM_G`: `G(Yf n)` is a continuous semimartingale with drift `1{t ≤ e_n} L_q G(Yf n)`;
* `hasMart_G`: for `G` bounded and `L_q G` bounded on the chamber (global bounds: the start is
  random, so `Yf n` need not stay in a deterministic compact), the compensated process
  `G(Yf n t) − G(Yf n 0) − ∫_(0,t] 1{s ≤ e_n} L_q G(Yf n s) ds` has a martingale modification.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ}
variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin (q + q) → ℝ}

namespace B1R

variable (F : B1R D0 q μ ξ)

theorem mpGenerator_switchOff (n : ℕ) {G : (Fin (q + q) → ℝ) → ℝ} (t : ℝ≥0) (ω : ΩR S q) :
    mpGenerator (fun _ => switchOff (F.e n) (fun t ω => flatDrift D0 q (F.Yf n t ω)) t ω)
      (fun _ => switchOff (F.e n) (fun t ω => flatDiff D0 q (F.Yf n t ω)) t ω) G (F.Yf n t ω) =
      switchOff (F.e n) (fun t ω => Lq D0 q G (F.Yf n t ω)) t ω := by
  unfold switchOff
  split_ifs
  · rfl
  · simp [mpGenerator]

/-- **`G(Yf n)` is a continuous semimartingale** with drift `1{t ≤ e_n} L_q G(Yf n)`. -/
theorem isCSM_G (hD0 : 0 < D0) (n : ℕ) {G : (Fin (q + q) → ℝ) → ℝ} (hGm : Measurable G)
    (hG : ContDiffOn ℝ 2 G (flatChamber q)) :
    IsContinuousSemimartingale (d := 1) (PR μ q) (𝓖R μ q) (fun t ω (_ : Fin 1) => G (F.Yf n t ω))
      (fun t ω (_ : Fin 1) => switchOff (F.e n) (fun t ω => Lq D0 q G (F.Yf n t ω)) t ω)
      (fun t ω => Matrix.of fun (_ _ : Fin 1) => itoBracket
        (fun p : ℝ × (Fin (q + q) → ℝ) => G p.2)
        (F.Yf n t ω) t (switchOff (F.e n) (fun t ω => flatDiff D0 q (F.Yf n t ω)) t ω)) := by
  have hφ : ContDiffOn ℝ 2 (fun p : ℝ × (Fin (q + q) → ℝ) => G p.2) (univ ×ˢ flatChamber q) :=
    hG.comp contDiffOn_snd fun p hp => hp.2
  have H := SemimartingaleIto.semimartingaleItoFormula_holds (q + q) (ΩR S q) (PR μ q)
    (𝓖R μ q) (F.Yf n) _ _ (F.isCSM_Yf hD0 n) (flatChamber q) (isOpen_flatChamber q)
    (Eventually.of_forall fun ω t => F.Yf_mem n t ω) (fun p : ℝ × (Fin (q + q) → ℝ) => G p.2)
    (hGm.comp measurable_snd) hφ
  have e : (fun (t : ℝ≥0) (ω : ΩR S q) (_ : Fin 1) => itoDrift
      (fun p : ℝ × (Fin (q + q) → ℝ) => G p.2)
      (F.Yf n t ω) t (switchOff (F.e n) (fun t ω => flatDrift D0 q (F.Yf n t ω)) t ω)
      (switchOff (F.e n) (fun t ω => flatDiff D0 q (F.Yf n t ω)) t ω)) =
      fun t ω _ => switchOff (F.e n) (fun t ω => Lq D0 q G (F.Yf n t ω)) t ω := by
    funext t ω _
    rw [itoDrift_comp_snd ((hG.contDiffAt ((isOpen_flatChamber q).mem_nhds (F.Yf_mem n t ω))))]
    exact F.mpGenerator_switchOff n t ω
  rw [e] at H
  exact H

/-- **The compensated process of a bounded `G(Yf n)` has a martingale modification.** -/
theorem hasMart_G (hD0 : 0 < D0) (n : ℕ) {G : (Fin (q + q) → ℝ) → ℝ} (hGm : Measurable G)
    (hG : ContDiffOn ℝ 2 G (flatChamber q)) {CG CL : ℝ} (hCG : ∀ w, |G w| ≤ CG)
    (hCL0 : 0 ≤ CL) (hCL : ∀ w ∈ flatChamber q, |Lq D0 q G w| ≤ CL) :
    HasMartingaleModification (PR μ q) (𝓖R μ q) (fun t ω => G (F.Yf n t ω) - G (F.Yf n 0 ω) -
      ∫ s in Ioc (0 : ℝ) t,
        switchOff (F.e n) (fun t ω => Lq D0 q G (F.Yf n t ω)) s.toNNReal ω) := by
  obtain ⟨τ, -, hτlim, hm⟩ := (F.isCSM_G hD0 n hGm hG).localizing
  refine Bridges.hasMartingaleModification_of_localized hτlim (fun k => (hm k).1 0)
    fun t => ⟨2 * CG + CL * t, Eventually.of_forall fun ω s hs => ?_⟩
  have hint : |∫ u in Ioc (0 : ℝ) s,
      switchOff (F.e n) (fun t ω => Lq D0 q G (F.Yf n t ω)) u.toNNReal ω| ≤ CL * t := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := CL)
      (s := Ioc (0 : ℝ) (s : ℝ))
      (f := fun u : ℝ => switchOff (F.e n) (fun t ω => Lq D0 q G (F.Yf n t ω)) u.toNNReal ω)
      measure_Ioc_lt_top fun u _ => by
        unfold switchOff; split_ifs
        · exact hCL _ (F.Yf_mem n _ ω)
        · simpa using hCL0
    rw [Real.norm_eq_abs, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp)] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCL0)
    simpa using (NNReal.coe_le_coe.2 hs)
  have h1 := hCG (F.Yf n s ω)
  have h2 := hCG (F.Yf n 0 ω)
  show |G (F.Yf n s ω) - G (F.Yf n 0 ω) - _| ≤ _
  calc _ ≤ |G (F.Yf n s ω)| + |G (F.Yf n 0 ω)| + |∫ u in Ioc (0 : ℝ) s,
        switchOff (F.e n) (fun t ω => Lq D0 q G (F.Yf n t ω)) u.toNNReal ω| := by
          refine (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans ?_
          linarith
    _ ≤ _ := by linarith

end B1R

end BlockBand.Transmission.Dual.G
