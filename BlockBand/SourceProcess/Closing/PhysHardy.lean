module

public import BlockBand.SourceProcess.Closing.HardyMain
public import BlockBand.SourceProcess.FullSourceStops.WordValue

/-!
# The physical closing data satisfy the Hardy hypotheses

* `omittedProj_mul_self`, `omittedProj_conjTranspose`: the omitted projection `A_-` is an
  orthogonal projection; for `h² < 1`, the pairing satisfies
  `ΠΠᴴ = A_-` (`closingPairing_mul_conj`; only `S_ffᴴS_ff = 1 - T_far` is used).
* `farEmbed_mul`, `farEmbed_conjTranspose`: the far embedding is multiplicative and commutes
  with `ᴴ`.
* `ae_phaseAvg_physClosingDefect`: almost surely, if the omitted block `N = Π𝕊A` has `N^n → 0`
  (`‖r‖ < 1` for the finite path; this is a hypothesis here), then
  `E_z (C(z) - 1)(C(z) - 1)ᴴ = 2 farEmbed(A_-)` for the physical closing map.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Closing

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath
open scoped Matrix

variable {W : ℕ}

theorem continuousOn_spectrum (f : ℝ → ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ContinuousOn f (spectrum ℝ X) :=
  X.finite_real_spectrum.continuousOn _

theorem cfc_conjTranspose (f : ℝ → ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (cfc f X)ᴴ = cfc f X := by
  have h : IsSelfAdjoint (cfc f X) := cfc_predicate f X
  rw [← Matrix.star_eq_conjTranspose]
  exact h.star_eq

theorem omittedProj_mul_self (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    omittedProj b E h W n ω * omittedProj b E h W n ω = omittedProj b E h W n ω := by
  unfold omittedProj
  rw [← cfc_mul _ _ _ (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
  congr 1
  funext t
  unfold omitIndicator
  split_ifs <;> simp

theorem omittedProj_conjTranspose (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    (omittedProj b E h W n ω)ᴴ = omittedProj b E h W n ω :=
  cfc_conjTranspose _ _

theorem pairWeight_mul (h : ℝ) (hh : h ^ 2 < 1) (t : ℝ) :
    pairWeight h t * ((fun x => 1 - x) t * pairWeight h t) = omitIndicator h t := by
  unfold pairWeight omitIndicator
  split_ifs with ht
  · have hpos : 0 < 1 - t := by linarith
    have hs : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hsq := Real.mul_self_sqrt hpos.le
    field_simp
    linarith
  · simp

/-- **`ΠΠᴴ = A_-`** for `h² < 1`. -/
theorem closingPairing_mul_conj (b E h : ℝ) (hh : h ^ 2 < 1) (n : ℕ) (ω : GrowthPath W) :
    closingPairing b E h W n ω * (closingPairing b E h W n ω)ᴴ = omittedProj b E h W n ω := by
  set X := farTransmission b E W n ω
  set R := farReflection b E W n ω
  have hX : IsSelfAdjoint X := (isHermitian_farTransmission b E W n ω).isSelfAdjoint
  have hRR : Rᴴ * R = cfc (fun x : ℝ => 1 - x) X := by
    rw [cfc_sub _ _ X (continuousOn_spectrum _ _) (continuousOn_spectrum _ _), cfc_const_one ℝ X hX,
      cfc_id' ℝ X hX]
    simp only [X, farTransmission, R, sub_sub_cancel]
  have e : closingPairing b E h W n ω * (closingPairing b E h W n ω)ᴴ =
      cfc (pairWeight h) X * (cfc (fun x : ℝ => 1 - x) X * cfc (pairWeight h) X) := by
    simp only [closingPairing, conjTranspose_mul, conjTranspose_conjTranspose, cfc_conjTranspose,
      Matrix.mul_assoc, ← hRR]
    rfl
  rw [e, ← cfc_mul _ _ X (continuousOn_spectrum _ _) (continuousOn_spectrum _ _),
    ← cfc_mul _ _ X (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
  unfold omittedProj
  congr 1
  funext t
  exact pairWeight_mul h hh t

theorem farEmbed_mul (X Y : Matrix (Fin W) (Fin W) ℂ) :
    farEmbed X * farEmbed Y = farEmbed (X * Y) := by
  ext x y
  simp only [farEmbed, mul_apply, of_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases hx : x.1 = 1 <;> by_cases hy : y.1 = 1 <;> simp [hx, hy]

theorem farEmbed_conjTranspose (X : Matrix (Fin W) (Fin W) ℂ) :
    (farEmbed X)ᴴ = farEmbed Xᴴ := by
  ext x y
  simp only [farEmbed, conjTranspose_apply, of_apply]
  by_cases hx : x.1 = 1 <;> by_cases hy : y.1 = 1 <;> simp [hx, hy]

/-- **The closing covariance identity for the physical path**. Almost surely,
whenever the omitted block of the closed path satisfies `N^n → 0`, the phase average of
`(C(z) - 1)(C(z) - 1)ᴴ` is twice the embedded omitted projection. -/
theorem ae_phaseAvg_physClosingDefect {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (s T h : ℝ) (hh : h ^ 2 < 1) :
    ∀ᵐ ω ∂growthPathLaw W b,
      Tendsto (fun n => closingN (scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ ω)
        (farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω))
        (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ ω)) ^ n) atTop (𝓝 0) →
      phaseAvg (fun θ => (physClosingMap b E s T h W ω (phase θ) - 1) *
          (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) := by
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW] with ω hω hN
  refine phaseAvg_closingDefect ?_ ?_ ?_ (hω _).1 hN
  · rw [farEmbed_mul, omittedProj_mul_self]
  · rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  · rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]

end BlockBand.SourceProcess.Closing
