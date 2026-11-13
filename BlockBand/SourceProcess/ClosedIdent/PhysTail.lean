module

public import BlockBand.SourceProcess.ClosedIdent.Defs
public import BlockBand.SourceProcess.SourcePins.AtomLimit

/-!
# The physical cap tail from the fractional trace bound

The number of retained modes is tight, at the physical level, by the homogeneous fractional trace
bound. If more than `K` eigenvalues of `T = T_{⌊Ws⌋}` exceed `h²`, then `Tr T^{1/2} ≥ (K+1)h`.
Markov's inequality and the fractional trace bound of `TransmissionLawContract` at `p = 1/2` give
`P_W(μ_W(s) ∉ capSet K h) ≤ B/((K+1)h)` for all large `W`.

* `ofReal_sqrt_mul_countWeight_le`: `√r · 1{y ≥ r}/y ≤ y^{-1/2}` (`countWeight`, `psiP`).
* `mul_le_psi_of_notMem_capSet`: `ν ∉ capSet K h` (`h > 0`) forces `h(K+1) ≤ ∫⁻ ψ_{1/2} dν`, for
  every measure `ν` on `[0,1]` (through `seqExtract`).
* `physCapEvent_compl_le`: the finite-`W` Markov bound.
* `eventually_physCapEvent_compl_le`: `∀ η > 0, ∀ᶠ K, ∀ᶠ W, P_W(cap event)ᶜ ≤ η`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedIdent

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.SourcePins
open BlockBand.SourceProcess.CapLimit
open scoped ENNReal NNReal

/-- `√r · 1{y ≥ r} y⁻¹ ≤ ψ_{1/2}(y)` for `r > 0`. -/
theorem ofReal_sqrt_mul_countWeight_le {r : ℝ} (hr : 0 < r) (y : unitInterval) :
    ENNReal.ofReal (Real.sqrt r) * countWeight r y ≤ psiP (1 / 2) y := by
  by_cases hy : r ≤ (y : ℝ)
  · have hy0 : 0 < (y : ℝ) := hr.trans_le hy
    simp only [countWeight, Set.indicator, Set.mem_ofPred_eq, hy, ite_true, psiP, hy0]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg r)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_sub hy0, Real.rpow_one, ← Real.sqrt_eq_rpow, mul_one_div]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hy) hy0.le
  · simp [countWeight, Set.indicator, hy]

/-- **More than `K` modes above `h²` force `Tr T^{1/2} ≥ h(K+1)`** (measure form). -/
theorem mul_le_psi_of_notMem_capSet {h : ℝ} (hh : 0 < h) {K : ℕ} {ν : Measure unitInterval}
    (hν : ν ∉ capSet K h) :
    ENNReal.ofReal h * ((K + 1 : ℕ) : ℝ≥0∞) ≤ ∫⁻ y, psiP (1 / 2) y ∂ν := by
  have h1 : ¬ seqExtract ν K ≤ h ^ 2 := hν
  rw [not_le, seqExtract] at h1
  set S := ⨆ r : {r : ℚ // 0 < r}, Set.indicator {ν : Measure unitInterval |
    ((K + 1 : ℕ) : ℝ≥0∞) ≤ atomCount (r : ℝ) ν} (fun _ => ENNReal.ofReal (r : ℝ)) ν with hS
  have hh2 : 0 < h ^ 2 := pow_pos hh 2
  have hStop : S ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h1
    linarith
  have hlt : ENNReal.ofReal (h ^ 2) < S := (ENNReal.ofReal_lt_iff_lt_toReal hh2.le hStop).2 h1
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 hlt
  by_cases hmem : ν ∈ {ν : Measure unitInterval | ((K + 1 : ℕ) : ℝ≥0∞) ≤ atomCount (r : ℝ) ν}
  · rw [Set.indicator_of_mem hmem] at hr
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast r.2
    have hhr : h ^ 2 < (r : ℝ) := (ENNReal.ofReal_lt_ofReal_iff hr0).1 hr
    have hsq : h ≤ Real.sqrt r := by
      rw [← Real.sqrt_sq hh.le]
      exact Real.sqrt_le_sqrt hhr.le
    calc ENNReal.ofReal h * ((K + 1 : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal (Real.sqrt r) * atomCount (r : ℝ) ν :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hsq) hmem
      _ = ∫⁻ y, ENNReal.ofReal (Real.sqrt r) * countWeight r y ∂ν := by
          rw [atomCount, lintegral_const_mul _ (measurable_countWeight _)]
      _ ≤ ∫⁻ y, psiP (1 / 2) y ∂ν :=
          lintegral_mono fun y => ofReal_sqrt_mul_countWeight_le hr0 y
  · rw [Set.indicator_of_notMem hmem] at hr
    exact absurd hr (not_lt.2 zero_le)

/-- **Finite-`W` Markov bound** for the physical cap event. -/
theorem physCapEvent_compl_le {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ}
    {h : ℝ} (hh : 0 < h) (s : ℝ) (K : ℕ) :
    growthPathLaw W b (physCapEvent b E s h K W)ᶜ ≤
      (∫⁻ ω, ENNReal.ofReal
          (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω))
        ∂growthPathLaw W b) / (ENNReal.ofReal h * ((K + 1 : ℕ) : ℝ≥0∞)) := by
  have hae := Transmission.LawDuality.aemeasurable_transmissionProcess (W := W)
    (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2 s
  have hpas := Transmission.Bridge.ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2
  have hT : ∀ᵐ ω ∂growthPathLaw W b,
      psiInt (1 / 2) (transmissionProcess b E (fun _ => 0) W s ω) =
        ENNReal.ofReal (fracTrace (1 / 2)
          (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω)) := by
    filter_upwards [hpas] with ω hω
    exact lintegral_psiP_traceMeasure (by norm_num)
      (Transmission.Bridge.pathTransmission_posSemidef hω _)
      (Transmission.Bridge.one_sub_pathTransmission_posSemidef b E _ W _ ω)
  have hne : ENNReal.ofReal h * ((K + 1 : ℕ) : ℝ≥0∞) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 hh).ne' (by exact_mod_cast Nat.succ_ne_zero K)
  have hnt : ENNReal.ofReal h * ((K + 1 : ℕ) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  refine (measure_mono fun ω hω => ?_).trans ((meas_ge_le_lintegral_div
    ((measurable_psiInt (1 / 2)).comp_aemeasurable hae) hne hnt).trans
    (le_of_eq (by
      rw [lintegral_congr_ae (hT.mono fun ω hω => by simp only [Function.comp_apply]; exact hω)])))
  exact mul_le_psi_of_notMem_capSet hh hω

/-- **The physical cap tail**: for `h > 0` and `η > 0`, for all large caps
`K`, for all large `W`, `P_W(more than K modes t_i > h² at time s) ≤ η`. -/
theorem eventually_physCapEvent_compl_le (hTL : TransmissionLawContract) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {s : ℝ} (hs : 0 < s) {h : ℝ} (hh : 0 < h)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ W : ℕ in atTop,
      (growthPathLaw W b (physCapEvent b E s h K W)ᶜ).toReal ≤ η := by
  obtain ⟨C, hC⟩ := hTL.fractional b hb0 hb E hE1 hE2 (1 / 2) (by norm_num) (by norm_num)
  set B := max (C * (1 + s⁻¹)) 0 + 1 with hB
  have hB0 : 0 < B := by positivity
  have hlt : limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
      (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω))
      ∂growthPathLaw W b) atTop < ENNReal.ofReal B :=
    (hC s hs).trans_lt ((ENNReal.ofReal_le_ofReal (le_max_left _ _)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (lt_add_one _)))
  have hevW := eventually_lt_of_limsup_lt hlt
  obtain ⟨N, hN⟩ := exists_nat_gt (B / (h * η))
  refine eventually_atTop.2 ⟨N, fun K hK => ?_⟩
  have hb1 : b < 1 := by linarith
  filter_upwards [hevW] with W hW
  have hK1 : (0 : ℝ) < h * ((K + 1 : ℕ) : ℝ) := by positivity
  have hle := physCapEvent_compl_le hb1 hE1 hE2 (W := W) hh s K
  have e1 : ENNReal.ofReal h * ((K + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (h * ((K + 1 : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_mul hh.le, ENNReal.ofReal_natCast]
  rw [e1] at hle
  have hle2 : growthPathLaw W b (physCapEvent b E s h K W)ᶜ ≤
      ENNReal.ofReal (B / (h * ((K + 1 : ℕ) : ℝ))) := by
    rw [ENNReal.ofReal_div_of_pos hK1]
    exact hle.trans (ENNReal.div_le_div_right hW.le _)
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hle2).trans ?_
  rw [div_le_iff₀ hK1]
  rw [div_lt_iff₀ (by positivity)] at hN
  have hKN : (N : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast hK.trans (Nat.le_succ K)
  have := mul_le_mul_of_nonneg_right hKN (mul_pos hh hη).le
  nlinarith

end BlockBand.SourceProcess.ClosedIdent
