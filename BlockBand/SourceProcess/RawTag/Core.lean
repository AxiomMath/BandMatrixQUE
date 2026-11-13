module

public import BlockBand.SourceProcess.RawTag.BirthBound
public import BlockBand.Transmission.LengthUniform.DeltaZero

/-!
# The raw-moment transport through `TW` layers

`raw_core`: under `RawUpdate`, `RawBirth`, `GaussianAbsorptionContract`, `GaussianLpGradient`,
`FullSourceMomentsEnergyUniformContract` and `DeltaZeroLengthUniform`, the moments of the raw tag
forms stay bounded along the `≤ TW` growth steps, uniformly in `W`. The proof iterates the one-step
bound by a discrete Gronwall inequality (`iterate_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.LengthUniform BlockBand.SourceProcess.FullSource
open scoped Matrix ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Discrete Gronwall** in `ℝ≥0∞`. -/
theorem iterate_le (e : ℕ → ℝ≥0∞) {r β : ℝ} (hr : 1 ≤ r) (hβ : 0 ≤ β) (l₀ : ℕ) :
    ∀ k : ℕ, (∀ j, j < k → e (l₀ + j + 1) ≤ ENNReal.ofReal r * e (l₀ + j) + ENNReal.ofReal β) →
      e (l₀ + k) ≤ ENNReal.ofReal (r ^ k) * (e l₀ + ENNReal.ofReal (k * β)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    have hk := ih fun j hj => h j (by omega)
    have hr0 : 0 ≤ r := by linarith
    have hrk : 1 ≤ r ^ (k + 1) := one_le_pow₀ hr
    have h1r : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (k + 1)) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hrk
    calc e (l₀ + (k + 1)) = e (l₀ + k + 1) := by rw [Nat.add_assoc]
      _ ≤ ENNReal.ofReal r * e (l₀ + k) + ENNReal.ofReal β := h k (by omega)
      _ ≤ ENNReal.ofReal r * (ENNReal.ofReal (r ^ k) * (e l₀ + ENNReal.ofReal (k * β))) +
          ENNReal.ofReal (r ^ (k + 1)) * ENNReal.ofReal β := by
          refine add_le_add (mul_le_mul_right hk _) ?_
          calc ENNReal.ofReal β = 1 * ENNReal.ofReal β := (one_mul _).symm
            _ ≤ _ := mul_le_mul_left h1r _
      _ = ENNReal.ofReal (r ^ (k + 1)) * (e l₀ + ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * β)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hr0, ← pow_succ', ← mul_add, add_assoc,
            ← ENNReal.ofReal_add (by positivity) hβ]
          congr 3; push_cast; ring

theorem stepBeta_nonneg (m : ℕ) {Cm Cf Cδ A : ℝ} (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) (hCδ : 0 ≤ Cδ)
    (hA : 0 ≤ A) : 0 ≤ stepBeta m Cm Cf Cδ A := by
  have := (stepK_pos (2 * m)).le
  unfold stepBeta; positivity

/-- **The raw-moment transport.** -/
theorem raw_core (hU : RawUpdate) (hBirth : RawBirth) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hFS : FullSourceMomentsEnergyUniformContract)
    (hδ : DeltaZeroLengthUniform) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    (T : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ (Γ : Type) [MeasurableSpace Γ] (ν : Measure Γ) [IsProbabilityMeasure ν]
      (g₁ g₂ : Γ → Fin W → ℂ), Measurable g₁ → Measurable g₂ →
      ν.map g₁ = circularVectorLaw (Fin W) → ν.map g₂ = circularVectorLaw (Fin W) →
      ∀ N β₁ β₂ : ℕ, β₁ < N → β₂ < N → (N : ℝ) ≤ T * W →
        ∫⁻ w, ENNReal.ofReal ((‖rawForm b E W N β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m))
          ∂((growthPathLaw W b).prod ν) ≤ ENNReal.ofReal C := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨Bb, WB, hbirth⟩ := birth_bound hBirth hGA hFS hb0 hb hκ T hm
  obtain ⟨Cm, Cf, W₁, hCm, hCf, hdf⟩ := delta_fresh_bounds hGA hLp b hb0 hb κ hκ (4 * m)
    (by linarith)
  obtain ⟨A, Wf, hA, hfr⟩ := momBd_frame hFS hb0 hb hκ T (r := 16 * m) (by linarith)
  obtain ⟨Cδ, hCδ, hδT⟩ := hδ b hb0 hb κ (16 * m) hκ (by linarith)
  obtain ⟨Wδ, hδW⟩ := hδT T
  set α := stepK (2 * m) + 4 * m
  set βc := stepBeta m Cm Cf Cδ A
  have hβc : 0 ≤ βc := stepBeta_nonneg m hCm hCf hCδ hA
  set Tp := max T 0
  have hα : 0 ≤ α := by have := (stepK_pos (2 * m)).le; positivity
  refine ⟨Real.exp (α * Tp) * (max Bb 0 + Tp * βc), max (max WB W₁) (max Wf (max Wδ 1)),
    fun W hW E hE Γ _ ν _ g₁ g₂ hg₁ hg₂ hl₁ hl₂ N β₁ β₂ h₁ h₂ hN => ?_⟩
  have hWB : WB ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hW)
  have hW₁ : W₁ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)
  have hWf : Wf ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hWδ : Wδ ≤ W :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW))
  have hW1 : 1 ≤ W :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW))
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hE' := hE
  obtain ⟨hE1, hE2⟩ := hE'
  have hκ2 : κ ≤ 2 := by linarith
  obtain ⟨hI, hmean, hF⟩ : _ ∧ _ ∧ _ := ⟨fun X hX => (hdf W hW₁ E hE X hX).1,
    fun X hX => (hdf W hW₁ E hE X hX).2.1, fun X hX => (hdf W hW₁ E hE X hX).2.2⟩
  have hupd := hU b E hb0 hb (by linarith) (by linarith) W hW1
  set l₀ := max β₁ β₂ + 1
  have hl₀N : l₀ ≤ N := by omega
  set e : ℕ → ℝ≥0∞ := fun l => ∫⁻ w, ENNReal.ofReal
    ((‖rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m)) ∂((growthPathLaw W b).prod ν)
  have hstep : ∀ j, j < N - l₀ → e (l₀ + j + 1) ≤
      ENNReal.ofReal (Real.exp (α / W)) * e (l₀ + j) + ENNReal.ofReal (βc / W) := by
    intro j hj
    set l := l₀ + j
    have hl1 : 1 ≤ l := by omega
    have hβ₁ : β₁ < l := by omega
    have hβ₂ : β₂ < l := by omega
    have hlT : (l : ℝ) ≤ T * W := le_trans (by exact_mod_cast (show l ≤ N by omega)) hN
    have hδl : MomBd (growthPathLaw W b) (fun ω => jetDistance0 b E (pathX b E W l ω)) (16 * m)
        (Cδ / W) :=
      ⟨((measurable_jetDistance0 (W := W) b E).comp
        (BlockBand.Transmission.PathJet.measurable_pathX b E l)).aestronglyMeasurable,
        hδW W hWδ E hE l hl1 hlT⟩
    have := step_scalar (by linarith) (by linarith) (by linarith) ν hg₁ hg₂ hm hWr hCm hCf hCδ hA
      (hupd.mono fun ω hω => hω l hl1 β₁ β₂ hβ₁ hβ₂) hI hmean hF
      (MomBd.comp_fst (ν := ν) hδl)
      (momBd_nearL_of_frame hg₁ (hfr W hWf E hE l β₁ hβ₁ hlT Γ ν g₁ hg₁ hl₁))
      (momBd_nearR_of_frame hg₂ (hfr W hWf E hE l β₂ hβ₂ hlT Γ ν g₂ hg₂ hl₂))
    exact this
  have hit := iterate_le e (Real.one_le_exp (by positivity)) (by positivity) l₀ (N - l₀) hstep
  rw [show l₀ + (N - l₀) = N by omega] at hit
  have hb0' : e l₀ ≤ ENNReal.ofReal (max Bb 0) := by
    have hmT : ((max β₁ β₂ : ℕ) : ℝ) ≤ T * W :=
      le_trans (by exact_mod_cast (show max β₁ β₂ ≤ N by omega)) hN
    exact (hbirth W hWB E hE Γ ν g₁ g₂ hg₁ hg₂ hl₁ hl₂ β₁ β₂ hmT).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hk : ((N - l₀ : ℕ) : ℝ) / W ≤ Tp := by
    rw [div_le_iff₀ hW0]
    have : ((N - l₀ : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N l₀
    nlinarith [le_max_left T 0, le_max_right T 0]
  refine hit.trans ?_
  rw [← Real.exp_nat_mul]
  have h1 : Real.exp (↑(N - l₀) * (α / W)) ≤ Real.exp (α * Tp) := by
    refine Real.exp_le_exp.mpr ?_
    rw [mul_div_assoc', mul_comm, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hk hα
  have h2 : ((N - l₀ : ℕ) : ℝ) * (βc / W) ≤ Tp * βc := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hk hβc |>.trans (le_of_eq (mul_comm _ _))
  calc ENNReal.ofReal (Real.exp (↑(N - l₀) * (α / W))) *
        (e l₀ + ENNReal.ofReal (↑(N - l₀) * (βc / W)))
      ≤ ENNReal.ofReal (Real.exp (α * Tp)) * (ENNReal.ofReal (max Bb 0) +
          ENNReal.ofReal (Tp * βc)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal h1) (add_le_add hb0' (ENNReal.ofReal_le_ofReal h2))
    _ = _ := by
        rw [← ENNReal.ofReal_add (le_max_right _ _) (mul_nonneg (le_max_right _ _) hβc),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]

end BlockBand.SourceProcess.RawTag
