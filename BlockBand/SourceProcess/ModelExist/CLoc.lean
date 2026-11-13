module

public import BlockBand.SourceProcess.ModelExist.LocShift

/-!
# Complex localized compensated martingales

`CLocMart Q 𝓖 Z β`: the real and imaginary parts of `Z` are `LocMart`s with drifts `Re β`,
`Im β`. Closed under sums and under increments after a stopping time with a complex
`𝓕_τ`-measurable weight (`CLocMart.shift`). `CLocMart.pair`: if `N, N'` have drift `0` and `NN'`
has drift `Γ`, then `(N − N^σ)(N' − N'^{σ'})` has drift `1{σ ∨ σ' < s} Γ_s` (pathwise identity
`pair_identity` with the weights `N_σ`, `N'_{σ'}`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

variable (Q 𝓖) in
/-- Complex `LocMart`: real and imaginary parts. -/
def CLocMart (Z β : ℝ≥0 → Ω → ℂ) : Prop :=
  LocMart Q 𝓖 (fun t ω => (Z t ω).re) (fun t ω => (β t ω).re) ∧
    LocMart Q 𝓖 (fun t ω => (Z t ω).im) (fun t ω => (β t ω).im)

variable {Z β : ℝ≥0 → Ω → ℂ}

omit [MeasurableSpace Ω] in
/-- Pathwise identity for the product of two increments after `σ`, `σ'`. -/
theorem pair_identity (N N' : ℝ≥0 → Ω → ℂ) (σ σ' : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (N t ω - stoppedProcess N σ t ω) * (N' t ω - stoppedProcess N' σ' t ω) =
      1 * (N t ω * N' t ω - stoppedProcess (fun t ω => N t ω * N' t ω)
          (fun ω => max (σ ω) (σ' ω)) t ω) +
        (-stoppedValue N σ ω) * (N' t ω - stoppedProcess N' (fun ω => max (σ ω) (σ' ω)) t ω) +
        (-stoppedValue N' σ' ω) * (N t ω - stoppedProcess N (fun ω => max (σ ω) (σ' ω)) t ω) := by
  simp only [stoppedProcess_eq_stopTime, stoppedValue]
  rcases le_or_gt (t : WithTop ℝ≥0) (max (σ ω) (σ' ω)) with h | h
  · rw [stopTime_eq_self h]
    rcases le_max_iff.1 h with h1 | h1
    · rw [stopTime_eq_self h1]; ring
    · rw [stopTime_eq_self h1]; ring
  · have ha : σ ω < t := (le_max_left _ _).trans_lt h
    have hb : σ' ω < t := (le_max_right _ _).trans_lt h
    lift σ ω to ℝ≥0 using ha.ne_top with a
    lift σ' ω to ℝ≥0 using hb.ne_top with b
    have ha' : a ≤ t := (WithTop.coe_lt_coe.1 ha).le
    have hb' : b ≤ t := (WithTop.coe_lt_coe.1 hb).le
    rw [← WithTop.coe_max, stopTime_coe, stopTime_coe, stopTime_coe, min_eq_right ha',
      min_eq_right hb', min_eq_right (max_le ha' hb'), untopA_coe', untopA_coe']
    rcases le_total a b with hab | hab
    · rw [max_eq_right hab]; ring
    · rw [max_eq_left hab]; ring

variable [IsProbabilityMeasure Q]

theorem CLocMart.add {Z' β' : ℝ≥0 → Ω → ℂ} (h₁ : CLocMart Q 𝓖 Z β) (h₂ : CLocMart Q 𝓖 Z' β') :
    CLocMart Q 𝓖 (fun t ω => Z t ω + Z' t ω) (fun t ω => β t ω + β' t ω) := by
  refine ⟨?_, ?_⟩
  · simpa only [Complex.add_re] using h₁.1.add h₂.1
  · simpa only [Complex.add_im] using h₁.2.add h₂.2

theorem CLocMart.sum {ι : Type*} (s : Finset ι) {Z β : ι → ℝ≥0 → Ω → ℂ}
    (h : ∀ i ∈ s, CLocMart Q 𝓖 (Z i) (β i)) :
    CLocMart Q 𝓖 (fun t ω => ∑ i ∈ s, Z i t ω) (fun t ω => ∑ i ∈ s, β i t ω) := by
  refine ⟨?_, ?_⟩
  · simpa only [Complex.re_sum] using LocMart.sum s fun i hi => (h i hi).1
  · simpa only [Complex.im_sum] using LocMart.sum s fun i hi => (h i hi).2

omit [IsProbabilityMeasure Q] in
theorem CLocMart.congr_drift (h : CLocMart Q 𝓖 Z β) {β' : ℝ≥0 → Ω → ℂ}
    (hβ : ∀ᵐ ω ∂Q, ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), β' s.toNNReal ω = β s.toNNReal ω) :
    CLocMart Q 𝓖 Z β' :=
  ⟨h.1.congr_drift (hβ.mono fun ω h => h.mono fun s hs => by simp only [hs]),
    h.2.congr_drift (hβ.mono fun ω h => h.mono fun s hs => by simp only [hs])⟩

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
/-- Complex weights `𝓕_τ`-measurable: real and imaginary parts. -/
theorem stronglyMeasurable_re_im {m : MeasurableSpace Ω} {ζ : Ω → ℂ}
    (hζ : StronglyMeasurable[m] ζ) :
    StronglyMeasurable[m] (fun ω => (ζ ω).re) ∧ StronglyMeasurable[m] (fun ω => (ζ ω).im) :=
  ⟨Complex.continuous_re.comp_stronglyMeasurable hζ,
    Complex.continuous_im.comp_stronglyMeasurable hζ⟩

/-- **Increments after `τ` with a complex `𝓕_τ`-measurable weight.** -/
theorem CLocMart.shift (h : CLocMart Q 𝓖 Z β) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {ζ : Ω → ℂ} (hζ : StronglyMeasurable[hτ.measurableSpace] ζ) :
    CLocMart Q 𝓖 (fun t ω => ζ ω * (Z t ω - stoppedProcess Z τ t ω))
      (fun s ω => if τ ω < (s : WithTop ℝ≥0) then ζ ω * β s ω else 0) := by
  obtain ⟨hre, him⟩ := stronglyMeasurable_re_im hζ
  have hnim : StronglyMeasurable[hτ.measurableSpace] (fun ω => -(ζ ω).im) := him.neg
  have a1 := h.1.shift_unbdd hτ hre
  have a2 := h.2.shift_unbdd hτ hnim
  have a3 := h.2.shift_unbdd hτ hre
  have a4 := h.1.shift_unbdd hτ him
  refine ⟨?_, ?_⟩
  · convert a1.add a2 using 1
    · funext t ω
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, stoppedProcess_eq_stopTime]
      ring
    · funext t ω
      dsimp only
      by_cases hc : τ ω < (t : WithTop ℝ≥0)
      · simp only [hc, ↓reduceIte, Complex.mul_re]; ring
      · simp only [hc, ↓reduceIte, Complex.zero_re, add_zero]
  · convert a3.add a4 using 1
    · funext t ω
      simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, stoppedProcess_eq_stopTime]
    · funext t ω
      dsimp only
      by_cases hc : τ ω < (t : WithTop ℝ≥0)
      · simp only [hc, ↓reduceIte, Complex.mul_im]
      · simp only [hc, ↓reduceIte, Complex.zero_im, add_zero]

omit [IsProbabilityMeasure Q] in
/-- `𝓕_σ`-measurability of a stopped value of a `CLocMart` (progressive parts). -/
theorem CLocMart.stronglyMeasurable_stoppedValue (h : CLocMart Q 𝓖 Z β)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓖 σ) :
    StronglyMeasurable[hσ.measurableSpace] (stoppedValue Z σ) := by
  have h1 := measurable_stoppedValue h.1.prog hσ
  have h2 := measurable_stoppedValue h.2.prog hσ
  have e : stoppedValue Z σ = fun ω => ((stoppedValue (fun t ω => (Z t ω).re) σ ω : ℝ) : ℂ) +
      ((stoppedValue (fun t ω => (Z t ω).im) σ ω : ℝ) : ℂ) * Complex.I := by
    funext ω; simp only [stoppedValue, Complex.re_add_im]
  rw [e]
  exact ((Complex.measurable_ofReal.comp h1).add
    ((Complex.measurable_ofReal.comp h2).mul_const _)).stronglyMeasurable

/-- **Products of increments.** -/
theorem CLocMart.pair {N N' Γ : ℝ≥0 → Ω → ℂ} (hN : CLocMart Q 𝓖 N (fun _ _ => 0))
    (hN' : CLocMart Q 𝓖 N' (fun _ _ => 0))
    (hNN : CLocMart Q 𝓖 (fun t ω => N t ω * N' t ω) Γ) {σ σ' : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime 𝓖 σ) (hσ' : IsStoppingTime 𝓖 σ') :
    CLocMart Q 𝓖 (fun t ω => (N t ω - stoppedProcess N σ t ω) *
        (N' t ω - stoppedProcess N' σ' t ω))
      (fun s ω => if max (σ ω) (σ' ω) < (s : WithTop ℝ≥0) then Γ s ω else 0) := by
  have hρ : IsStoppingTime 𝓖 (fun ω => max (σ ω) (σ' ω)) := hσ.max hσ'
  have w1 : StronglyMeasurable[hρ.measurableSpace] (fun ω => -stoppedValue N σ ω) :=
    ((hN.stronglyMeasurable_stoppedValue hσ).mono
      (hσ.measurableSpace_mono hρ fun ω => le_max_left _ _)).neg
  have w2 : StronglyMeasurable[hρ.measurableSpace] (fun ω => -stoppedValue N' σ' ω) :=
    ((hN'.stronglyMeasurable_stoppedValue hσ').mono
      (hσ'.measurableSpace_mono hρ fun ω => le_max_right _ _)).neg
  have s1 := hNN.shift hρ (ζ := fun _ => 1) stronglyMeasurable_const
  have s2 := hN'.shift hρ w1
  have s3 := hN.shift hρ w2
  convert (s1.add s2).add s3 using 1
  · funext t ω
    exact pair_identity N N' σ σ' t ω
  · funext s ω
    split_ifs <;> simp

/-- A process vanishing up to `ρ` keeps its drift (switched on after `ρ`) under an
`𝓕_ρ`-measurable weight. -/
theorem CLocMart.weight {W : ℝ≥0 → Ω → ℂ} (hW : CLocMart Q 𝓖 W β) {ρ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime 𝓖 ρ) (h0 : ∀ t ω, stoppedProcess W ρ t ω = 0) {ζ : Ω → ℂ}
    (hζ : StronglyMeasurable[hρ.measurableSpace] ζ) :
    CLocMart Q 𝓖 (fun t ω => ζ ω * W t ω)
      (fun s ω => if ρ ω < (s : WithTop ℝ≥0) then ζ ω * β s ω else 0) := by
  convert hW.shift hρ hζ using 1
  funext t ω
  rw [h0, sub_zero]

end BlockBand.SourceProcess.ModelExist
