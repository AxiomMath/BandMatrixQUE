module

public import BlockBand.SourceProcess.RawTag.Core
public import BlockBand.Transmission.EnergyUniform.Holds
public import BlockBand.SourceProcess.ComplexSourceLaw.ExtJensen

/-!
# The raw tag moments `RawTagMoments`

`rawTagMoments_of`: under `RawUpdate`, `RawBirth` and the contract hypotheses, the tag forms have
bounded moments of every real order, uniformly in `W`. The core bound is transferred to massive
tags and real orders:

Masses: `ξ = √m · unitTag`, so the forms scale by `(m_jm_k)^{1/2}` (`tagForm_eq_rawForm`).
Real orders: `‖x‖^p ≤ 1 + ‖x‖^{4m}` with `4m ≥ p` (`rpow_le_one_add`). Independent tags:
`Γ = ℂ^W × ℂ^W`, `ν = CN ⊗ CN`, `g₁ = fst`, `g₂ = snd`; the same tag: `Γ = ℂ^W`, `g₁ = g₂ = id`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw
open scoped Matrix ENNReal

variable {W : ℕ}

/-- The mass factor: `‖√(m_jm_k)·x‖^p = (m_jm_k)^{p/2}‖x‖^p`. -/
theorem norm_mass_rpow {mj mk : ℝ} (hj : 0 ≤ mj) (hk : 0 ≤ mk) (x : ℂ) (p : ℝ) :
    ‖((Real.sqrt mj * Real.sqrt mk : ℝ) : ℂ) * x‖ ^ p = (mj * mk) ^ (p / 2) * ‖x‖ ^ p := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.sqrt_mul hj, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (mul_nonneg hj hk)]
  congr 2; ring

/-- `‖x‖^p ≤ 1 + (‖x‖²)^{2m}` for `p ≤ 4m`. -/
theorem norm_rpow_le_one_add {p : ℝ} (hp : 0 ≤ p) {m : ℕ} (hpm : p ≤ 4 * m) (x : ℂ) :
    ‖x‖ ^ p ≤ 1 + (‖x‖ ^ 2) ^ (2 * m) := by
  have h := rpow_le_one_add (norm_nonneg x) hp hpm
  have e : ‖x‖ ^ (4 * (m : ℝ)) = (‖x‖ ^ 2) ^ (2 * m) := by
    rw [← pow_mul, show 2 * (2 * m) = 4 * m by ring, ← Real.rpow_natCast]; push_cast; rfl
  rwa [e] at h

/-- The real-order, massive form of the core bound on a tag space. -/
theorem lintegral_massive_le {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ}
    [IsProbabilityMeasure ν] {μ : Measure (GrowthPath W)} [IsProbabilityMeasure μ]
    {F : GrowthPath W × Γ → ℂ} (hF : Measurable F) {p : ℝ} (hp : 0 ≤ p) {m : ℕ}
    (hpm : p ≤ 4 * m) {mj mk : ℝ} (hj : 0 ≤ mj) (hk : 0 ≤ mk) {C : ℝ}
    (hC : ∫⁻ w, ENNReal.ofReal ((‖F w‖ ^ 2) ^ (2 * m)) ∂(μ.prod ν) ≤ ENNReal.ofReal C) :
    ∫⁻ w, ENNReal.ofReal (‖((Real.sqrt mj * Real.sqrt mk : ℝ) : ℂ) * F w‖ ^ p) ∂(μ.prod ν) ≤
      ENNReal.ofReal ((1 + max C 0) * (mj * mk) ^ (p / 2)) := by
  have hmk : 0 ≤ (mj * mk) ^ (p / 2) := Real.rpow_nonneg (mul_nonneg hj hk) _
  have hm2 : Measurable fun w => ENNReal.ofReal ((‖F w‖ ^ 2) ^ (2 * m)) :=
    ((hF.norm.pow_const 2).pow_const _).ennreal_ofReal
  calc ∫⁻ w, ENNReal.ofReal (‖((Real.sqrt mj * Real.sqrt mk : ℝ) : ℂ) * F w‖ ^ p) ∂(μ.prod ν)
      ≤ ∫⁻ w, ENNReal.ofReal ((mj * mk) ^ (p / 2)) *
          (1 + ENNReal.ofReal ((‖F w‖ ^ 2) ^ (2 * m))) ∂(μ.prod ν) := by
        refine lintegral_mono fun w => ?_
        rw [norm_mass_rpow hj hk _ p, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
          (by positivity), ← ENNReal.ofReal_mul hmk]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (norm_rpow_le_one_add hp hpm _) hmk)
    _ = ENNReal.ofReal ((mj * mk) ^ (p / 2)) *
          (1 + ∫⁻ w, ENNReal.ofReal ((‖F w‖ ^ 2) ^ (2 * m)) ∂(μ.prod ν)) := by
        have hm3 : Measurable fun w => 1 + ENNReal.ofReal ((‖F w‖ ^ 2) ^ (2 * m)) :=
          measurable_const.add hm2
        rw [lintegral_const_mul _ hm3, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal ((mj * mk) ^ (p / 2)) * (1 + ENNReal.ofReal (max C 0)) :=
        mul_le_mul_right (add_le_add le_rfl (hC.trans (ENNReal.ofReal_le_ofReal
          (le_max_left _ _)))) _
    _ = _ := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (le_max_right _ _),
          ← ENNReal.ofReal_mul hmk, mul_comm]

/-- **`RawTagMoments` from the exact-algebra hypotheses `RawUpdate`, `RawBirth` and the input
hypotheses.** -/
theorem rawTagMoments_of (hU : RawUpdate) (hBirth : RawBirth) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract) :
    RawTagMoments := by
  intro b hb0 hb κI hκ T p hp
  set m := ⌈p⌉₊
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; have := Nat.le_ceil p; rw [show ⌈p⌉₊ = m from rfl, h0] at this; push_cast at this
    linarith)
  have hpm : p ≤ 4 * m := by
    have := Nat.le_ceil p
    have h1 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨C, W₀, hC⟩ := raw_core hU hBirth hGA hLp
    (BlockBand.Transmission.EnergyUniform.fullSourceMomentsEnergyUniform_holds hGA hLp hSR)
    (BlockBand.Transmission.LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp) hb0 hb hκ T
    hm
  refine ⟨1 + max C 0, W₀, fun W hW E hE n hn j k mj mk hj hk => ⟨?_, ?_⟩⟩
  · have hc := hC W hW E hE ((Fin W → ℂ) × (Fin W → ℂ))
      ((circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W))) Prod.fst Prod.snd
      measurable_fst measurable_snd (by rw [Measure.map_fst_prod, measure_univ, one_smul])
      (by rw [Measure.map_snd_prod, measure_univ, one_smul]) n (n - 1 - j.val) (n - 1 - k.val)
      (by omega) (by omega) hn
    have hF : Measurable fun w : GrowthPath W × ((Fin W → ℂ) × (Fin W → ℂ)) =>
        rawForm b E W n (n - 1 - j.val) (n - 1 - k.val) w.1 w.2.1 w.2.2 :=
      measurable_rawForm b E n _ _ measurable_fst (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd)
    simp_rw [tagForm_eq_rawForm b E n j k hj hk]
    exact lintegral_massive_le hF hp0 hpm hj hk hc
  · have hc := hC W hW E hE (Fin W → ℂ) (circularVectorLaw (Fin W)) id id measurable_id
      measurable_id Measure.map_id Measure.map_id n (n - 1 - j.val) (n - 1 - j.val) (by omega)
      (by omega) hn
    have hF : Measurable fun w : GrowthPath W × (Fin W → ℂ) =>
        rawForm b E W n (n - 1 - j.val) (n - 1 - j.val) w.1 w.2 w.2 :=
      measurable_rawForm b E n _ _ measurable_fst measurable_snd measurable_snd
    simp_rw [tagForm_eq_rawForm b E n j j hj hj]
    exact lintegral_massive_le hF hp0 hpm hj hj hc

end BlockBand.SourceProcess.RawTag
