module

public import BlockBand.Transmission.LawDuality.RatioSmooth
public import BlockBand.Transmission.Dual.Generator
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Duality principle: the localized ratio test

For a compact `K` in the chamber `𝒞_q`, a smooth bump `χ` with compact support in `𝒞_q` and
`χ = 1` near `K` (`exists_chamber_bump`) localizes the ratio test to `χ·F_·(ν)`. Its generator
agrees with that of `F_·(ν)` where `χ = 1`, and the dual deletion process gives the corresponding
level-`q` martingale (`martingale_localRatio`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal ContDiff

variable {q : ℕ}

/-- **Smooth chamber bump.** For a compact `K ⊆ 𝒞_q` there is a `C^∞` function `χ` with values in
`[0,1]`, compact support inside `𝒞_q`, and `χ = 1` near every point of `K`. -/
theorem exists_chamber_bump {K : Set (DualCoord q)} (hK : IsCompact K)
    (hKC : K ⊆ dualChamber q) :
    ∃ χ : DualCoord q → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ dualChamber q ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ ∀ z ∈ K, χ =ᶠ[𝓝 z] fun _ => 1 := by
  obtain ⟨L₁, hL₁, hKL₁, hL₁C⟩ := exists_compact_between hK (isOpen_dualChamber q) hKC
  obtain ⟨L₂, hL₂, hL₁L₂, hL₂C⟩ := exists_compact_between hL₁ (isOpen_dualChamber q) hL₁C
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    isOpen_interior hL₁.isClosed hL₁L₂
  have hts : tsupport χ ⊆ L₂ := by
    unfold tsupport
    rw [hsupp]
    exact closure_minimal interior_subset hL₂.isClosed
  refine ⟨χ, hχ, hL₂.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hL₂C, fun z => hrange (mem_range_self z), fun z hz => ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.1 (hKL₁ hz)] with w hw
  exact (hone w).1 hw

variable (χ : DualCoord q → ℝ) (ν : FiniteMeasure unitInterval)

/-- The localized ratio test `χ·F_·(ν)`. -/
def localRatio : DualCoord q → ℝ := fun z => χ z * ratioOn ν z

variable {χ}

theorem tsupport_localRatio_subset : tsupport (localRatio χ ν) ⊆ tsupport χ :=
  tsupport_mul_subset_left

theorem hasCompactSupport_localRatio (hχc : HasCompactSupport χ) :
    HasCompactSupport (localRatio χ ν) :=
  hχc.mul_right

theorem contDiff_localRatio (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ dualChamber q) :
    ContDiff ℝ ∞ (localRatio χ ν) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ ratioOpen q
  · exact (hχ.contDiffAt.mul ((contDiffOn_ratioOn ν).contDiffAt
      (isOpen_ratioOpen.mem_nhds hz)))
  · have hz' : z ∉ tsupport (localRatio χ ν) := fun h =>
      hz (dualChamber_subset_ratioOpen (hχs (tsupport_localRatio_subset ν h)))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hz')

theorem localRatio_eventuallyEq {z : DualCoord q} (hz : χ =ᶠ[𝓝 z] fun _ => 1) :
    localRatio χ ν =ᶠ[𝓝 z] ratioOn ν := by
  filter_upwards [hz] with w hw
  simp [localRatio, hw]

theorem localRatio_eq_of_mem {z : DualCoord q} (hz : χ =ᶠ[𝓝 z] fun _ => 1) :
    localRatio χ ν z = ratioOn ν z :=
  (localRatio_eventuallyEq ν hz).eq_of_nhds

/-- On the region where `χ = 1` the generator of the localized test is that of `F_·(ν)`. -/
theorem dualGenerator_localRatio_of_mem (D0 : ℝ) {z : DualCoord q}
    (hz : χ =ᶠ[𝓝 z] fun _ => 1) :
    dualGenerator D0 (localRatio χ ν) z = dualGenerator D0 (ratioOn ν) z :=
  dualGenerator_congr (localRatio_eventuallyEq ν hz)

/-- **The martingale clause applies to the localized ratio test.** -/
theorem martingale_localRatio {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {p : ℕ}
    {x y : Fin p → ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hD : IsDualDeletionProcess P 𝓖 D0 x y N X Y) (hq1 : 1 ≤ q) (hqp : q ≤ p)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ dualChamber q) :
    Martingale (dualMartingale D0 q (localRatio χ ν) N X Y) 𝓖 P :=
  hD.martingale q hq1 hqp _ (contDiff_localRatio ν hχ hχs) (hasCompactSupport_localRatio ν hχc)
    ((tsupport_localRatio_subset ν).trans hχs)

end BlockBand.Transmission.LawDuality
