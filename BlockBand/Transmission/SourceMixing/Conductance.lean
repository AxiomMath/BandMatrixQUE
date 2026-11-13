module

public import BlockBand.Transmission.SourceMixing.MassMoment

/-!
# Finite-width conductance moments

Proves `ConductanceMomentBound`, the `finiteConductance` field of the passive source-mixing lemma:
`E[g_r^p] ≤ C(1 + W^p/(r+1)^p)` for `r ≤ TW`. The conductance is `g_r = 4η q_r` pointwise
(`pathConductance_eq_mass`), so:
* for `W ≥ W₀(T)` and `r ≥ 1`: `‖g_r‖_p ≤ 4ηK(1 + W/r)` (`massMomentBound_holds`), and
  `(1 + W/r)^p ≤ 4^p(1 + W^p/(r+1)^p)` (`cm_real`);
* otherwise: `0 ≤ g_r ≤ W` almost surely.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- `g_r = 4η q_r` pointwise. -/
theorem pathConductance_eq_mass (b E : ℝ) (r : ℕ) (ω : GrowthPath W) :
    pathConductance b E W r ω = 4 * etaZ b E * passiveMass b E (pathX b E W r ω) := by
  rw [pathConductance, conductanceOf, pathTransmission, passiveTransmission, trace_smul,
    passiveMass, smul_eq_mul, Complex.re_ofReal_mul]

theorem measurable_pathConductance (b E : ℝ) (r : ℕ) :
    Measurable (pathConductance b E W r) := by
  have h : pathConductance b E W r = fun ω => 4 * etaZ b E * passiveMass b E (pathX b E W r ω) :=
    funext (pathConductance_eq_mass b E r)
  rw [h]
  exact ((measurable_passiveMass b E).comp (PathJet.measurable_pathX b E r)).const_mul _

/-- From an `L^p` bound to the `lintegral` of the `p`-th power. -/
theorem cm_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {p X : ℝ} (hp : 0 < p) (hX : 0 ≤ X)
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal X) :
    ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (X ^ p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le] at h
  have h' := ENNReal.rpow_le_rpow h hp.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hX hp.le] at h'
  exact h'

/-- `(1 + W/r)^p ≤ 4^p (1 + W^p/(r+1)^p)` for `r ≥ 1`, `p ≥ 0`. -/
theorem cm_real {w r p : ℝ} (hw : 0 ≤ w) (hr : 1 ≤ r) (hp : 0 ≤ p) :
    (1 + w / r) ^ p ≤ 4 ^ p * (1 + w ^ p / (r + 1) ^ p) := by
  have hr0 : 0 < r := by linarith
  set x := w / (r + 1)
  have hx : 0 ≤ x := by positivity
  have h1 : 1 + w / r ≤ 1 + 2 * x := by
    have : w / r ≤ 2 * (w / (r + 1)) := by
      rw [mul_div_assoc', div_le_div_iff₀ hr0 (by linarith)]; nlinarith
    linarith
  have hxp : x ^ p = w ^ p / (r + 1) ^ p := Real.div_rpow hw (by linarith) p
  rw [← hxp]
  refine (Real.rpow_le_rpow (by positivity) h1 hp).trans ?_
  have hxp0 : 0 ≤ x ^ p := by positivity
  rcases le_or_gt x 1 with h | h
  · calc (1 + 2 * x) ^ p ≤ 4 ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ ≤ 4 ^ p * (1 + x ^ p) := le_mul_of_one_le_right (by positivity) (by linarith)
  · calc (1 + 2 * x) ^ p ≤ (4 * x) ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = 4 ^ p * x ^ p := Real.mul_rpow (by norm_num) hx
      _ ≤ 4 ^ p * (1 + x ^ p) := by
          have : (0 : ℝ) ≤ 4 ^ p := by positivity
          nlinarith

/-- **`PassiveSourceMixingContract.finiteConductance`**: the `ConductanceMomentBound`. -/
theorem conductanceMomentBound_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : ConductanceMomentBound := by
  intro b hb0 hb E h1 h2 T p hp
  obtain ⟨K, hK, hKT⟩ := massMomentBound_holds hMT hGA hLp hb0 hb h1 h2 p hp
  obtain ⟨W₀, hW₀⟩ := hKT T
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hp0 : 0 < p := by linarith
  set C := (16 * etaZ b E * K) ^ p + (W₀ : ℝ) ^ p + 1
  have hC1 : 0 ≤ (16 * etaZ b E * K) ^ p := by positivity
  have hC2 : 0 ≤ (W₀ : ℝ) ^ p := by positivity
  refine ⟨C, fun W hW r hrT => ?_⟩
  set P := growthPathLaw W b
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWp : 0 ≤ (W : ℝ) ^ p / ((r : ℝ) + 1) ^ p := by positivity
  have hg := (measurable_pathConductance (W := W) b E r).aestronglyMeasurable (μ := P)
  by_cases hbig : W₀ ≤ W ∧ 1 ≤ r
  · obtain ⟨hWW, hr1⟩ := hbig
    have hq := hW₀ W hWW r hr1 hrT
    have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hgL : eLpNorm (pathConductance b E W r) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (4 * etaZ b E * (K * (1 + W / r))) := by
      have e : pathConductance b E W r =
          (4 * etaZ b E) • fun ω => passiveMass b E (pathX b E W r ω) := by
        funext ω; rw [pathConductance_eq_mass]; rfl
      rw [e, eLpNorm_const_smul, ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal_abs,
        abs_of_pos (by positivity)]
      exact mul_le_mul_right hq _
    refine (cm_lintegral_le hg hp0 (by positivity) hgL).trans (ENNReal.ofReal_le_ofReal ?_)
    have hreal := cm_real (w := (W : ℝ)) (by positivity) hr1' hp0.le
    have e2 : (4 * etaZ b E * (K * (1 + W / r))) ^ p =
        (4 * etaZ b E * K) ^ p * (1 + W / r) ^ p := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]; ring_nf
    have e3 : (16 * etaZ b E * K) ^ p = (4 * etaZ b E * K) ^ p * 4 ^ p := by
      rw [← Real.mul_rpow (by positivity) (by norm_num)]; ring_nf
    rw [e2]
    calc (4 * etaZ b E * K) ^ p * (1 + W / r) ^ p
        ≤ (4 * etaZ b E * K) ^ p * (4 ^ p * (1 + W ^ p / (r + 1) ^ p)) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = (16 * etaZ b E * K) ^ p * (1 + W ^ p / (r + 1) ^ p) := by rw [e3]; ring
      _ ≤ C * (1 + W ^ p / (r + 1) ^ p) :=
          mul_le_mul_of_nonneg_right (by simp only [C]; linarith) (by positivity)
  · -- `0 ≤ g ≤ W` almost surely
    have hgW : ∀ᵐ ω ∂P, ‖pathConductance b E W r ω‖ₑ ^ p ≤ ENNReal.ofReal ((W : ℝ) ^ p) := by
      filter_upwards [mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω hω
      have hq0 := passiveMass_nonneg b E hω
      have hqW := passiveMass_le_width (b := b) (by linarith) h1 h2 (pathX b E W r ω)
      have hg0 : 0 ≤ pathConductance b E W r ω := by rw [pathConductance_eq_mass]; positivity
      have hgW : pathConductance b E W r ω ≤ W := by
        rw [pathConductance_eq_mass]
        rw [le_div_iff₀ (by positivity)] at hqW
        linarith
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hg0, ENNReal.ofReal_rpow_of_nonneg hg0 hp0.le]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hg0 hgW hp0.le)
    refine (lintegral_mono_ae hgW).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hCW : (W : ℝ) ^ p ≤ C * (1 + W ^ p / (r + 1) ^ p) := by
      rcases not_and_or.mp hbig with h | h
      · have hlt : (W : ℝ) ≤ W₀ := by exact_mod_cast (Nat.lt_of_not_le h).le
        have : (W : ℝ) ^ p ≤ (W₀ : ℝ) ^ p := Real.rpow_le_rpow (by positivity) hlt hp0.le
        have : C ≤ C * (1 + W ^ p / (r + 1) ^ p) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
        simp only [C] at this ⊢; linarith
      · have hr0 : r = 0 := by omega
        subst hr0
        simp only [Nat.cast_zero, zero_add, Real.one_rpow, div_one]
        have : (W : ℝ) ^ p ≤ 1 + (W : ℝ) ^ p := by linarith
        have hC : 1 ≤ C := by simp only [C]; linarith
        exact this.trans (le_mul_of_one_le_left (by positivity) hC)
    exact hCW

example (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (h : PassiveSourceMixingContract) : PassiveSourceMixingContract :=
  { h with finiteConductance := conductanceMomentBound_holds hMT hGA hLp }

end BlockBand.Transmission.SourceMixing
