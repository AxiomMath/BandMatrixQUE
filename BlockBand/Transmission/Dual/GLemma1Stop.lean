module

public import BlockBand.Transmission.Dual.GBaseQ
public import BlockBand.Transmission.Dual.GDensity
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Adapted
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Localize

/-!
# The local Doob identity: the stopped base path and the density martingale

Let `Z` be a base solution (`IsBaseSol`, continuous and started at `z` at every `ω`) on
`(Ω, 𝓖, P)`, `W` an interior domain of the flat chamber with `z ∈ W`, `τ` the exit time from
`W`, and `Z^τ = stopZ W Z`.
* `stopZ` is progressive and adapted (`τ` is the hitting time of `Wᶜ`, a stopping time), stays
  in `closure W`, and `∫_0^t G(Z^τ_s) ds = ∫_0^{t∧τ} G(Z_s) ds` when `G = 0` off `W`
  (`integral_stopZ`).
* `exists_tilt`: the density `M_t = H_q(Z^τ_t)/H_q(z)` (bounded by `max_{closure W} H_q / H_q(z)`)
  has an adapted martingale version `M̃` with terminal density `g` (`IsDensity`), and
  `P̃ = tilt P g` is a probability measure.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime rawHit
  isStoppingTime_rawHit exitTimeFrom_attained)
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}
  {z : Fin (q + q) → ℝ} {W : Set (Fin (q + q) → ℝ)}

/-- The base path stopped at its exit from `W`. -/
def stopZ (W : Set (Fin (q + q) → ℝ)) (Z : ℝ≥0 → Ω → Fin (q + q) → ℝ) :
    ℝ≥0 → Ω → Fin (q + q) → ℝ :=
  stoppedProcess Z (exitTimeFrom W Z)

theorem isStoppingTime_exit (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W) :
    IsStoppingTime 𝓖 (exitTimeFrom W Z) := by
  have e : exitTimeFrom W Z = rawHit Wᶜ Z :=
    funext fun ω => (SemimartingaleIto.rawHit_compl_eq_exitTimeFrom hW (hZ.cont ω)).symm
  rw [e]
  exact isStoppingTime_rawHit fun t => (hZ.sol.adapted t).measurable

theorem isStronglyProgressive_stopZ (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W) :
    IsStronglyProgressive 𝓖 (stopZ W Z) :=
  (StronglyAdapted.isStronglyProgressive_of_continuous hZ.sol.adapted hZ.cont).stoppedProcess
    (isStoppingTime_exit hZ hW)

theorem stronglyMeasurable_stopZ (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W) (t : ℝ≥0) :
    StronglyMeasurable[𝓖 t] (stopZ W Z t) :=
  (isStronglyProgressive_stopZ hZ hW).stronglyAdapted t

theorem continuous_stopZ (hZ : IsBaseSol D0 q P 𝓖 Z z) (ω : Ω) :
    Continuous fun t => stopZ W Z t ω :=
  NativeSDE.continuous_stoppedProcess (hZ.cont ω) _

theorem stopZ_mem_closure (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W) (hzW : z ∈ W)
    (t : ℝ≥0) (ω : Ω) : stopZ W Z t ω ∈ closure W := by
  rcases (Bridges.stopped_path_mem_closure hW (hZ.cont ω) t).2 with h | h
  · rw [stopZ, stoppedProcess_eq_stopTime, h, hZ.start]; exact subset_closure hzW
  · exact h.1

/-- Time integrals of functions vanishing off `W` along the stopped path. -/
theorem integral_stopZ (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W)
    {G : (Fin (q + q) → ℝ) → ℝ} (hG : ∀ w ∉ W, G w = 0) (t : ℝ≥0) (ω : Ω) :
    ∫ s in Ioc (0 : ℝ) t, G (stopZ W Z s.toNNReal ω) =
      ∫ s in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Z ω) t), G (Z s.toNNReal ω) := by
  set u := stopTime (exitTimeFrom W Z ω) t
  have hut : u ≤ t := Semimartingale.stopTime_le _ _
  have hpt : ∀ s ∈ Ioc (0 : ℝ) t, G (stopZ W Z s.toNNReal ω) =
      (Iic (u : ℝ)).indicator (fun s => G (Z s.toNNReal ω)) s := by
    intro s hs
    by_cases hsu : s ≤ u
    · rw [indicator_of_mem (mem_Iic.2 hsu), stopZ, stoppedProcess_eq_stopTime]
      congr 2
      refine stopTime_eq_self_of_le_stopTime (t := t) ?_
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le]; exact hsu
    · rw [indicator_of_notMem (by simpa using hsu)]
      push Not at hsu
      rcases exitTimeFrom_attained hW (hZ.cont ω) with he | ⟨s₀, he, hs₀⟩
      · exfalso
        have : u = t := by simp only [u, he, Semimartingale.stopTime_top]
        rw [this] at hsu; exact absurd hs.2 (not_le.2 hsu)
      · have hu : u = min t s₀ := by simp only [u, he, Semimartingale.stopTime_coe]
        have hs₀t : s₀ < t := by
          by_contra h; push Not at h
          rw [min_eq_left h] at hu; rw [hu] at hsu; exact absurd hs.2 (not_le.2 hsu)
        rw [min_eq_right hs₀t.le] at hu
        have hss : s₀ ≤ s.toNNReal := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le, ← hu]; exact hsu.le
        rw [stopZ, stoppedProcess_eq_stopTime, he, Semimartingale.stopTime_coe, min_eq_right hss]
        exact hG _ hs₀
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, setIntegral_indicator measurableSet_Iic,
    Ioc_inter_Iic, min_eq_right (by exact_mod_cast hut)]

/-!
## The density martingale
-/

/-- `H_q` in flat coordinates. -/
def flatH (q : ℕ) (w : Fin (q + q) → ℝ) : ℝ := cauchyH q (ofFlat q w)

theorem exists_bound_flatH (hW : IsInteriorDomain W (flatChamber q)) :
    ∃ C, ∀ w ∈ closure W, 0 < flatH q w ∧ flatH q w ≤ C := by
  obtain ⟨C, hC⟩ := hW.2.1.exists_bound_of_continuousOn
    (contDiffOn_cauchyH_flat.continuousOn.mono hW.2.2)
  exact ⟨C, fun w hw => ⟨cauchyH_pos (hW.2.2 hw), (le_abs_self _).trans
    (Real.norm_eq_abs _ ▸ hC w hw)⟩⟩

/-- The density `H_q(Z^τ_t)/H_q(z)`. -/
def densM (W : Set (Fin (q + q) → ℝ)) (Z : ℝ≥0 → Ω → Fin (q + q) → ℝ) (z : Fin (q + q) → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  flatH q (stopZ W Z t ω) / flatH q z

variable [IsProbabilityMeasure P]

/-- **The tilted measure of the local Doob identity.** -/
theorem exists_tilt (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsInteriorDomain W (flatChamber q))
    (hzW : z ∈ W) : ∃ (M : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0), IsDensity P 𝓖 M g ∧
      (∀ t, M t =ᵐ[P] densM W Z z t) ∧ IsProbabilityMeasure (tilt P g) := by
  obtain ⟨C, hC⟩ := exists_bound_flatH hW
  have hz0 : 0 < flatH q z := (hC z (subset_closure hzW)).1
  obtain ⟨N, hN, hNe⟩ := hasMM_cauchyH_stop hZ.chamber hW
  set M : ℝ≥0 → Ω → ℝ := fun t => (flatH q z)⁻¹ • (N t + fun _ => flatH q z)
  have hM : Martingale M 𝓖 P := (hN.add (martingale_const 𝓖 P (flatH q z))).smul _
  have hMe : ∀ t, M t =ᵐ[P] densM W Z z t := fun t => by
    filter_upwards [hNe t] with ω hω
    simp only [M, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hω, densM, stoppedProcess_eq_stopTime,
      hZ.start, stopZ, flatH]
    field_simp
    ring
  have hbd : ∀ t, ∀ᵐ ω ∂P, 0 ≤ M t ω ∧ M t ω ≤ C / flatH q z := fun t => by
    filter_upwards [hMe t] with ω hω
    rw [hω, densM]
    have h := hC _ (stopZ_mem_closure hZ hW.1 hzW t ω)
    exact ⟨div_nonneg h.1.le hz0.le, div_le_div_of_nonneg_right h.2 hz0.le⟩
  obtain ⟨g, hg⟩ := exists_isDensity hM hbd
  refine ⟨M, g, hg, hMe, hg.isProbabilityMeasure_tilt ?_⟩
  filter_upwards [hMe 0] with ω hω
  rw [hω, densM, stopZ, stoppedProcess_eq_stopTime, Semimartingale.stopTime_zero, hZ.start,
    div_self hz0.ne']

end BlockBand.Transmission.Dual.G
