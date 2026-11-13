module

public import BlockBand.SourceProcess.PhysApprox.B3StepK
public import BlockBand.SourceProcess.PhysApprox.B3MeanClosed
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormDefs

/-!
# The closed-input bridge `ClosedKStepForm + ClosedJetL4Fam ⇒ ClosedKMeanInput`

The input `ClosedKMeanInput` of the `𝒦` mean and the pair `ClosedKStepForm Xcl`,
`ClosedJetHalf Xcl` of the `𝒦` step state nearly the same closed input. This file merges them for
one shared closed-input family `Xcl` (in applications, `b3ClosedX`):

* **`ClosedJetL4Fam Xcl`**: the closed jet in `L⁴` at the `W⁻¹` scale,
  `E δ₀(Xcl_j)⁴ ≤ C/W⁴` at every step `n_s ≤ j < ⌊WT⌋` after the first birth. It is
  `ClosedJetHalf` (`C/W²`) at the `W⁻¹` scale of the passive jet moments
  (`∫δ₀(X)⁴ ≤ C/W⁴`), stated in the shape of `ClosedJetHalf`;
* **`closedJetHalf_of_L4Fam`**: `ClosedJetL4Fam Xcl ⇒ ClosedJetHalf Xcl` (`W⁴ ≥ W²`);
* **`closedKMeanInput_of_stepForm`**: `ClosedKStepForm Xcl + ClosedJetL4Fam Xcl ⇒
  ClosedKMeanInput`, with witnesses `u, v` of `ClosedKStepForm` and `X = Xcl_i`. On a no-birth
  step `i`, "both tags born before `i + 1`" is "both tags old at `i`";
* `closedKMeanInput_of_b3ClosedX`, `closedJetHalf_of_b3ClosedX`: the same at `Xcl = b3ClosedX`.

With the bridge, the two hypotheses `ClosedKMeanInput` and `ClosedJetHalf` reduce to the single
hypothesis `ClosedJetL4Fam Xcl`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal ComplexOrder

/-- **`ClosedJetL4Fam Xcl`: the closed jet in `L⁴` at the `W⁻¹` scale** (the passive jet
moments at the closed input): on the domain, eventually, at every step `n_s ≤ j < ⌊WT⌋` after the
first birth, `E δ₀(Xcl_j)⁴ ≤ C/W⁴`. -/
def ClosedJetL4Fam (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ Cδ : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, (∃ i, ⌊(W : ℝ) * τ i⌋₊ < j) →
        ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (Xcl b E s h τ m W j y) ^ 4)
          ∂closedLaw b W np ≤ ENNReal.ofReal (Cδ / (W : ℝ) ^ 4)

/-- **`ClosedJetHalf` from the `L⁴` jet family** (`C/W⁴ ≤ max C 0/W²` for `W ≥ 1`). -/
theorem closedJetHalf_of_L4Fam {Xcl : ClosedInputFam} (hJ : ClosedJetL4Fam Xcl) :
    ClosedJetHalf Xcl := by
  intro b E np τ m T s h K Vs hD
  obtain ⟨Cδ, hev⟩ := hJ b E np τ m T s h K Vs hD
  refine ⟨max Cδ 0, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1 j hj hb
  refine (hW j hj hb).trans (ENNReal.ofReal_le_ofReal ?_)
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have h2 : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
  have h24 : (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 4 := pow_le_pow_right₀ hW1' (by norm_num)
  calc Cδ / (W : ℝ) ^ 4 ≤ max Cδ 0 / (W : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max Cδ 0 / (W : ℝ) ^ 2 := div_le_div_of_nonneg_left (le_max_right _ _) h2 h24

/-- **The closed-input bridge**: `ClosedKMeanInput` from the closed exact update
`ClosedKStepForm Xcl` and the closed `L⁴` jet family `ClosedJetL4Fam Xcl`, with the shared
witness `X = Xcl_i`. -/
theorem closedKMeanInput_of_stepForm {Xcl : ClosedInputFam} (hF : ClosedKStepForm Xcl)
    (hJ : ClosedJetL4Fam Xcl) : ClosedKMeanInput := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨Cf, hFW⟩ := hF b E np τ m T s h K Vs hD R
  obtain ⟨Cδ, hJW⟩ := hJ b E np τ m T s h K Vs hD
  refine ⟨Cf, Cδ, ?_⟩
  filter_upwards [hFW, hJW] with W hFj hJj ij i hi h1 h2
  have hiI : i ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊ := (Finset.mem_filter.1 hi).1
  have hnb : ¬ IsBirthStep τ W i := (Finset.mem_filter.1 hi).2
  have h1' : ⌊(W : ℝ) * τ ij.1⌋₊ < i :=
    lt_of_le_of_ne (by omega) fun he => hnb ⟨ij.1, he⟩
  have h2' : ⌊(W : ℝ) * τ ij.2⌋₊ < i :=
    lt_of_le_of_ne (by omega) fun he => hnb ⟨ij.2, he⟩
  obtain ⟨hXm, hXi, hXp, hform⟩ := hFj i hiI
  obtain ⟨u, v, hu, hv, hu', hv', hub, hvb, hae⟩ := hform ij h1' h2'
  refine ⟨u, v, Xcl b E s h τ m W i, ⟨hu, hv, hXm, hu', hv', hXi, hub, hvb, hXp, hae⟩, ?_⟩
  unfold ClosedJetL4
  refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (hJj i hiI ⟨ij.1, h1'⟩)
  exact (ENNReal.ofReal_pow (norm_nonneg _) 4).symm

/-- **`ClosedKMeanInput` at the closed input `b3ClosedX`.** -/
theorem closedKMeanInput_of_b3ClosedX (hF : ClosedKStepForm b3ClosedX)
    (hJ : ClosedJetL4Fam b3ClosedX) : ClosedKMeanInput :=
  closedKMeanInput_of_stepForm hF hJ

/-- **`ClosedJetHalf b3ClosedX` from the jet family at `b3ClosedX`.** -/
theorem closedJetHalf_of_b3ClosedX (hJ : ClosedJetL4Fam b3ClosedX) : ClosedJetHalf b3ClosedX :=
  closedJetHalf_of_L4Fam hJ

end BlockBand.SourceProcess.PhysApprox.B3
