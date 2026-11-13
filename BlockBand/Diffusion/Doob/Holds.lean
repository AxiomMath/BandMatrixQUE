module

public import BlockBand.Diffusion.Doob.Law
public import BlockBand.Diffusion.Heat.All
public import BlockBand.Diffusion.Markov.HTransform

/-!
# The Doob killed law of the one-pair boundary dual, unconditionally

`dkLbkDoobKilledLaw_holds`: for every `D₀ > 0` the Doob killed law `DkLbkDoobKilledLaw D0` holds,
since its hypothesis `DkLbkCornerHeatIdentity D0` follows from the corner heat identity. The file
also records that `h(w) = (w₁ + w₂)⁻¹` is excessive for the base kernel off the corner, but not on
the whole strip.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set
open scoped ENNReal

/-- The named hypothesis `DkLbkCornerHeatIdentity D0` from the corner heat identity. -/
theorem dkLbkCornerHeatIdentity_holds (D0 : ℝ) (hD0 : 0 < D0) : DkLbkCornerHeatIdentity D0 :=
  fun w hw hw0 t ht => chLbkCornerHeatIdentity D0 hD0 w hw hw0 t ht

/-- **The Doob killed law `DkLbkDoobKilledLaw D0`, with no conditions**, for every `D₀ > 0`. -/
theorem dkLbkDoobKilledLaw_holds (D0 : ℝ) (hD0 : 0 < D0) : DkLbkDoobKilledLaw D0 :=
  dkLbkDoobKilledLaw_of hD0 (dkLbkCornerHeatIdentity_holds D0 hD0)

/-!
### Excessiveness
-/

/-- `ch_excessive` packaged as `IsExcessiveOn` with `μ = volume`, off the corner. -/
theorem dk_excessiveOn {D0 : ℝ} (hD0 : 0 < D0) :
    IsExcessiveOn (volume : Measure (ℝ × ℝ)) (exBaseStrip \ {((0 : ℝ), (0 : ℝ))})
      (fun t a b => ENNReal.ofReal (exKernel D0 t a b)) (fun w => ENNReal.ofReal (chHarm w)) :=
  fun _ ht _ ha => ch_excessive hD0 ha.1 ha.2 ht

open scoped Classical in
/-- The adapter `h' = ofReal H` on the strip, `1` off it: also excessive off the corner. -/
theorem dk_excessiveOn' {D0 : ℝ} (hD0 : 0 < D0) :
    IsExcessiveOn (volume : Measure (ℝ × ℝ)) (exBaseStrip \ {((0 : ℝ), (0 : ℝ))})
      (fun t a b => ENNReal.ofReal (exKernel D0 t a b))
      (fun w => if w ∈ exBaseStrip then ENNReal.ofReal (chHarm w) else 1) := by
  classical
  intro t ht a ha
  have e : ∀ b, ENNReal.ofReal (exKernel D0 t a b) *
      (if b ∈ exBaseStrip then ENNReal.ofReal (chHarm b) else 1) =
      ENNReal.ofReal (exKernel D0 t a b) * ENNReal.ofReal (chHarm b) := fun b => by
    by_cases hb : b ∈ exBaseStrip
    · simp [hb]
    · simp [hb, ch_exKernel_eq_zero_of_notMem t a hb]
  simp only [e]
  simp only [ha.1, ↓reduceIte]
  exact ch_excessive hD0 ha.1 ha.2 ht

/-- At the corner itself excessiveness fails in Lean (`H(0,0) = 0⁻¹ = 0`). -/
theorem dk_not_excessive_corner {D0 : ℝ} (hD0 : 0 < D0) :
    ¬ IsExcessiveOn (volume : Measure (ℝ × ℝ)) exBaseStrip
      (fun t a b => ENNReal.ofReal (exKernel D0 t a b))
      (fun w => ENNReal.ofReal (chHarm w)) := by
  intro h
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ exBaseStrip := by simp [exBaseStrip]
  have := h 1 one_pos _ h0
  have hc : chHarm ((0 : ℝ), (0 : ℝ)) = 0 := by simp [chHarm]
  simp only [] at this
  rw [hc, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
  -- `∫⁻ p_1((0,0),·) H = 0` would force `p_1((0,0),·) H = 0` a.e., contradicting mass one.
  have hm : Measurable fun b : ℝ × ℝ =>
      ENNReal.ofReal (exKernel D0 1 (0, 0) b) * ENNReal.ofReal (chHarm b) :=
    (((exKernel_measurable hD0).comp (f := fun b : ℝ × ℝ => ((1 : ℝ), ((0 : ℝ), (0 : ℝ)), b))
      (by fun_prop)).ennreal_ofReal).mul (by unfold chHarm; fun_prop)
  rw [lintegral_eq_zero_iff hm] at this
  have hpos : ∀ᵐ b ∂(volume : Measure (ℝ × ℝ)), exKernel D0 1 (0, 0) b ≠ 0 →
      ENNReal.ofReal (exKernel D0 1 (0, 0) b) * ENNReal.ofReal (chHarm b) ≠ 0 := by
    filter_upwards [ch_ae_ne_corner] with b hb hp
    have hbs := ch_mem_of_exKernel_ne_zero hp
    have hs := ch_pos_of_mem hbs hb
    have hk : 0 < exKernel D0 1 (0, 0) b := lt_of_le_of_ne (exKernel_nonneg hD0 _ _ _) (Ne.symm hp)
    simp [chHarm, hk, hs]
  have hz : ∀ᵐ b ∂(volume : Measure (ℝ × ℝ)), exKernel D0 1 (0, 0) b = 0 := by
    filter_upwards [this, hpos] with b hb hb'
    by_contra hne
    exact hb' hne hb
  have h1 := ch_integral_exKernel hD0 one_pos h0
  rw [integral_eq_zero_of_ae hz] at h1
  exact zero_ne_one h1

end BlockBand.Diffusion
