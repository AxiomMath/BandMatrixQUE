module

public import BlockBand.Palm.MomentFlow.IndProps

/-!
# The continuous error of `CM(r)` from the error of `maxPath`

`contErr_of_rho`: if `0 ≤ ρ ≤ bnd` on `[s,c]` with `ρ` continuous, `∫_s^c bnd ≤ X` and
`bnd(c) ≤ X`, then `σ ↦ ρ(σ) + ∫_s^σ Kρ` is a continuous error (`ContErr`) on `[a', c]` with
bound `(1 + K) X`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set MeasureTheory intervalIntegral

/-- **`ContErr` from a dominated continuous error.** -/
theorem contErr_of_rho {ρ bnd : ℝ → ℝ} {s a' c K X : ℝ} (hsa : s ≤ a') (hac : a' ≤ c)
    (hca : c - a' ≤ 1) (hK : 0 ≤ K) (hρc : ContinuousOn ρ (Icc s c))
    (hρ0 : ∀ u ∈ Icc s c, 0 ≤ ρ u) (hρb : ∀ u ∈ Icc s c, ρ u ≤ bnd u)
    (hbi : IntervalIntegrable bnd volume s c) (hbX : (∫ u in s..c, bnd u) ≤ X)
    (hbc : bnd c ≤ X) :
    ContErr (fun σ => ρ σ + ∫ t in s..σ, K * ρ t) a' c ((1 + K) * X) := by
  have hsc : s ≤ c := hsa.trans hac
  have hsub : Icc a' c ⊆ Icc s c := Icc_subset_Icc hsa le_rfl
  have hρi : IntervalIntegrable ρ volume s c := hρc.intervalIntegrable_of_Icc hsc
  have hKρc : ContinuousOn (fun t => K * ρ t) (Icc s c) := continuousOn_const.mul hρc
  have hI : ∀ σ ∈ Icc s c, (∫ t in s..σ, K * ρ t) ≤ K * ∫ t in s..c, ρ t := by
    intro σ hσ
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hK
    have h1 : IntervalIntegrable ρ volume s σ :=
      (hρc.mono (Icc_subset_Icc le_rfl hσ.2)).intervalIntegrable_of_Icc hσ.1
    have h2 : IntervalIntegrable ρ volume σ c :=
      (hρc.mono (Icc_subset_Icc hσ.1 le_rfl)).intervalIntegrable_of_Icc hσ.2
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have : 0 ≤ ∫ t in σ..c, ρ t :=
      intervalIntegral.integral_nonneg hσ.2 fun t ht => hρ0 t ⟨hσ.1.trans ht.1, ht.2⟩
    linarith
  have hI0 : ∀ σ ∈ Icc s c, 0 ≤ ∫ t in s..σ, K * ρ t := fun σ hσ =>
    intervalIntegral.integral_nonneg hσ.1 fun t ht =>
      mul_nonneg hK (hρ0 t ⟨ht.1, ht.2.trans hσ.2⟩)
  have hρX : (∫ t in s..c, ρ t) ≤ X :=
    (intervalIntegral.integral_mono_on hsc hρi hbi hρb).trans hbX
  have hρX0 : 0 ≤ ∫ t in s..c, ρ t := intervalIntegral.integral_nonneg hsc hρ0
  have hprim : ContinuousOn (fun σ => ∫ t in s..σ, K * ρ t) (Icc s c) := by
    have := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (b₁ := s) (b₂ := c)
      (a := s) (f := fun t => K * ρ t) (hKρc.intervalIntegrable_of_Icc hsc) left_mem_uIcc
    rwa [uIcc_of_le hsc] at this
  refine ⟨(hρc.mono hsub).add (hprim.mono hsub), fun u hu => add_nonneg (hρ0 u (hsub hu))
    (hI0 u (hsub hu)), ?_, ?_⟩
  · have hei : IntervalIntegrable (fun σ => ρ σ + ∫ t in s..σ, K * ρ t) volume a' c :=
      ((hρc.mono hsub).add (hprim.mono hsub)).intervalIntegrable_of_Icc hac
    have hci : IntervalIntegrable (fun σ => ρ σ + K * ∫ t in s..c, ρ t) volume a' c :=
      ((hρc.mono hsub).add continuousOn_const).intervalIntegrable_of_Icc hac
    have h1 := intervalIntegral.integral_mono_on hac hei hci fun σ hσ => by
      have := hI σ (hsub hσ); linarith
    rw [intervalIntegral.integral_add (hρc.mono hsub |>.intervalIntegrable_of_Icc hac)
      intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h1
    have h2 : (∫ t in a'..c, ρ t) ≤ ∫ t in s..c, ρ t := by
      have i1 : IntervalIntegrable ρ volume s a' :=
        (hρc.mono (Icc_subset_Icc le_rfl hac)).intervalIntegrable_of_Icc hsa
      have i2 : IntervalIntegrable ρ volume a' c := (hρc.mono hsub).intervalIntegrable_of_Icc hac
      rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
      have : 0 ≤ ∫ t in s..a', ρ t :=
        intervalIntegral.integral_nonneg hsa fun t ht => hρ0 t ⟨ht.1, ht.2.trans hac⟩
      linarith
    have h3 : (c - a') * (K * ∫ t in s..c, ρ t) ≤ K * ∫ t in s..c, ρ t := by
      have : 0 ≤ K * ∫ t in s..c, ρ t := mul_nonneg hK hρX0
      nlinarith [sub_nonneg.2 hac]
    have h4 : K * ∫ t in s..c, ρ t ≤ K * X := mul_le_mul_of_nonneg_left hρX hK
    nlinarith
  · have h1 := hI c ⟨hsc, le_rfl⟩
    have h2 := (hρb c ⟨hsc, le_rfl⟩).trans hbc
    have h4 : K * ∫ t in s..c, ρ t ≤ K * X := mul_le_mul_of_nonneg_left hρX hK
    show ρ c + ∫ t in s..c, K * ρ t ≤ (1 + K) * X
    nlinarith

end BlockBand.Palm.MomentFlow
