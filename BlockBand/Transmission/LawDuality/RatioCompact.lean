module

public import BlockBand.Transmission.LawDuality.RatioBound

/-!
# `RatioDualityPrinciple`, step (b): bounds on compact subsets of the chamber

* `continuousOn_genCoef`, `continuousOn_expRate`: the coefficients of
  `abs_dualGenerator_ratioOn_le` are continuous on the chamber.
* **`exists_bound_dualGenerator_ratioOn`**: on a compact `K ⊆ 𝒞_p`, `|𝒟_pF_·(ν)(z)| ≤ C` for
  all `z ∈ K` and **all** finite measures `ν` on `[0,1]`.
* **`exists_bound_ratioDrift`**: on a compact `K ⊆ 𝒞_p` and for an absorption profile `κ`,
  `|ratioDrift D₀ E κ u z ν| ≤ C` for all `u ∈ ℝ`, `z ∈ K`, `ν`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {p : ℕ}

theorem continuousOn_genCoef : ContinuousOn (genCoef (p := p)) (dualChamber p) := by
  unfold genCoef
  have hX := fun i : Fin p => (continuous_apply i).comp (continuous_fst (X := Fin p → ℝ)
    (Y := Fin p → ℝ))
  have hY := fun i : Fin p => (continuous_apply i).comp (continuous_snd (X := Fin p → ℝ)
    (Y := Fin p → ℝ))
  refine ContinuousOn.add (continuousOn_finsetSum _ fun i _ => ?_)
    (continuousOn_finsetSum _ fun j _ => ?_)
  · exact (((hX i).mul (continuous_const.add (hX i))).continuousOn.abs).add
      (continuousOn_dualDriftX i).abs
  · have hne : ∀ z ∈ dualChamber p, 1 - z.2 j ≠ 0 := fun z hz =>
      (sub_pos.2 (hz.2.2.2 j).2).ne'
    have hinv : ContinuousOn (fun z : DualCoord p => (1 - z.2 j)⁻¹) (dualChamber p) :=
      (continuous_const.sub (hY j)).continuousOn.inv₀ hne
    exact (((hY j).mul (continuous_const.sub (hY j))).continuousOn.abs.mul (hinv.pow 2)).add
      ((continuousOn_dualDriftY j).abs.mul hinv)

theorem continuousOn_expRate (i0 : Fin p) : ContinuousOn (expRate i0) (dualChamber p) := by
  unfold expRate
  have hX := (continuous_apply i0).comp (continuous_fst (X := Fin p → ℝ) (Y := Fin p → ℝ))
  have hY := (continuous_apply i0).comp (continuous_snd (X := Fin p → ℝ) (Y := Fin p → ℝ))
  exact (hX.continuousOn.div (continuous_const.add hX).continuousOn fun z hz =>
    (add_pos one_pos (hz.2.2.1 i0)).ne').add hY.continuousOn

/-- **`𝒟_pF_·(ν)` is bounded on compacts of the chamber, uniformly in `ν`.** -/
theorem exists_bound_dualGenerator_ratioOn (D0 : ℝ) {K : Set (DualCoord p)} (hK : IsCompact K)
    (hKc : K ⊆ dualChamber p) : ∃ C, ∀ z ∈ K, ∀ ν : FiniteMeasure unitInterval,
      |dualGenerator D0 (ratioOn ν) z| ≤ C := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨0, fun z _ ν => by simp [dualGenerator]⟩
  · set i0 : Fin p := ⟨0, hp⟩
    have hE := continuousOn_expRate i0
    have hcont : ContinuousOn (fun z : DualCoord p => |D0| / 2 * genCoef z *
        (2 / expRate i0 z ^ 2 + 1 / expRate i0 z)) (dualChamber p) :=
      (continuousOn_const.mul continuousOn_genCoef).mul
        ((continuousOn_const.div (hE.pow 2) fun z hz => (pow_pos (expRate_pos hz i0) 2).ne').add
          (continuousOn_const.div hE fun z hz => (expRate_pos hz i0).ne'))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKc)
    refine ⟨C, fun z hz ν => (abs_dualGenerator_ratioOn_le ν D0 (hKc hz) i0).trans
      ((le_abs_self _).trans ?_)⟩
    have := hC z hz
    rwa [Real.norm_eq_abs] at this

/-- **The forward drift is bounded on compacts of the chamber, uniformly in `u` and `ν`.** -/
theorem exists_bound_ratioDrift (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ)
    {K : Set (DualCoord p)} (hK : IsCompact K) (hKc : K ⊆ dualChamber p) :
    ∃ C, ∀ u : ℝ, ∀ z ∈ K, ∀ ν : FiniteMeasure unitInterval,
      |ratioDrift D0 E κ u z ν| ≤ C := by
  obtain ⟨C1, hC1⟩ := exists_bound_dualGenerator_ratioOn D0 hK hKc
  obtain ⟨-, hκ0, Kκ, hKκ⟩ := hκ
  have hR : ContinuousOn (fun z : DualCoord p => ∑ i, (z.1 i + z.2 i)) K :=
    (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).add
      ((continuous_apply i).comp continuous_snd)).continuousOn
  obtain ⟨CR, hCR⟩ := hK.exists_bound_of_continuousOn hR
  set h0 := 4 * Real.pi * |Parameters.semicircleDensity E| * Kκ
  refine ⟨C1 + h0 * CR, fun u z hz ν => ?_⟩
  have hr := IsRatioParameter.isRatioRange (show IsRatioParameter z.1 z.2 from hKc hz)
  have hF := transmissionRatio_mem_vec hr ν
  have hKκ0 : 0 ≤ Kκ := (hκ0 0).trans (hKκ 0)
  have hh : |absorptionRate E κ u| ≤ h0 := by
    unfold absorptionRate
    rw [abs_mul, abs_mul, abs_of_nonneg (hκ0 u),
      abs_of_pos (show (0 : ℝ) < 4 * Real.pi by positivity)]
    exact mul_le_mul_of_nonneg_left (hKκ u) (by positivity)
  have hRz : |∑ i, (z.1 i + z.2 i)| ≤ CR := by
    have := hCR z hz; rwa [Real.norm_eq_abs] at this
  unfold ratioDrift
  calc |dualGenerator D0 (ratioOn ν) z -
        absorptionRate E κ u * (∑ i, (z.1 i + z.2 i)) * transmissionRatio z.1 z.2 ν|
      ≤ |dualGenerator D0 (ratioOn ν) z| +
        |absorptionRate E κ u| * |∑ i, (z.1 i + z.2 i)| * |transmissionRatio z.1 z.2 ν| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ C1 + h0 * CR * 1 := by
        refine add_le_add (hC1 z hz ν) (mul_le_mul (mul_le_mul hh hRz (abs_nonneg _)
          (by positivity)) ?_ (abs_nonneg _) (mul_nonneg (by positivity)
            ((abs_nonneg _).trans hRz)))
        rw [abs_of_pos hF.1]; exact hF.2
    _ = C1 + h0 * CR := by ring

end BlockBand.Transmission.LawDuality
