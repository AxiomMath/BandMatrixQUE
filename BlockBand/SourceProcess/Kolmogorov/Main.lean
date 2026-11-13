module

public import BlockBand.SourceProcess.ComplexSourceLaw.Interface
public import BlockBand.SourceProcess.Kolmogorov.Bound

/-!
# The conjugate Kolmogorov inequality

`kolmogorovConjugate_holds`: for `0 < p < 1` and `f` holomorphic on a disk of radius `R > 1` with
`f(0) = 0`, `∫|f(e^{iθ})|^p dθ ≤ C_p (2π)^{1-p} (∫|Im f(e^{iθ})| dθ)^p` with
`C_p = 2/cos(pπ/2)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Kolmogorov

open Complex Real Metric Set

theorem kolmogorovConjugate_holds :
    BlockBand.SourceProcess.ComplexSourceLaw.KolmogorovConjugate := by
  intro p hp0 hp1
  refine ⟨2 / Real.cos (p * π / 2), ?_⟩
  intro f R hR hf hf0
  have hc := cos_pos_of_lt_one hp0 hp1
  have key := cos_mul_circleAverage_norm_rpow_le_one hp0 hp1 hR hf hf0
  have h1 := integral_Ioc_eq_circleAverage (fun z ↦ ‖f z‖ ^ p)
  have h2 := integral_Ioc_eq_circleAverage (fun z ↦ |(f z).im|)
  rw [h1, h2]
  set X := circleAverage (fun z ↦ ‖f z‖ ^ p) 0 1
  set Y := circleAverage (fun z ↦ |(f z).im|) 0 1
  have hY0 : 0 ≤ Y := circleAverage_nonneg_of_nonneg (fun _ _ ↦ abs_nonneg _)
  have h2pi := two_pi_pos
  rw [Real.mul_rpow h2pi.le hY0]
  have hpow : (2 * π) ^ (1 - p) * (2 * π) ^ p = 2 * π := by
    rw [← Real.rpow_add h2pi]; simp
  have hX : X ≤ 2 * Y ^ p / Real.cos (p * π / 2) := by
    rw [le_div_iff₀ hc]; linarith
  calc 2 * π * X ≤ 2 * π * (2 * Y ^ p / Real.cos (p * π / 2)) := by gcongr
    _ = 2 / Real.cos (p * π / 2) * ((2 * π) ^ (1 - p) * (2 * π) ^ p) * Y ^ p := by
        rw [hpow]; ring
    _ = 2 / Real.cos (p * π / 2) * (2 * π) ^ (1 - p) * ((2 * π) ^ p * Y ^ p) := by ring

end BlockBand.SourceProcess.Kolmogorov
