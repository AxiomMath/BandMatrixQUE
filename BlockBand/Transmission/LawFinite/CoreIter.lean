module

public import BlockBand.Transmission.LawFinite.CoreFirst
public import BlockBand.Transmission.PathScalar.AbsorbedRecursion

/-!
# The finite-core entrance, with absorption

`q_r/W` stays bounded below in probability along the absorbed path, for `1 ≤ r ≤ TW`.
Hypotheses `PassiveBoundsStatement` and `PassiveInitialScalarContract` (only its
`absorbedMoment` clause, at `p = 1`).

* `delta_tail`: `P(d < δ₀(X_r)) ≤ (C/d)/W` for `1 ≤ r ≤ TW` (Markov on `absorbedMoment`);
* `core_iter_step`: `P(q_{r+1} < caW) ≤ P(q_r < aW) + C/W` for `r ≥ 1` (`cheb_absorbed` on the
  past event `{Hermitian blocks, δ₀(X_r) ≤ d, q_r ≥ aW}`, `step_prob_le`);
* **`finiteCoreEntrance_of hA hP : FiniteCoreEntrance`**: induction on `r ≥ 1` from
  `core_first`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

variable {W : ℕ}

theorem layerAbsorption_mem {κ : ℝ → ℝ} (hκ0 : ∀ s, 0 ≤ κ s) {Kκ : ℝ} (hK : ∀ s, κ s ≤ Kκ)
    (r : ℕ) (i : Fin r) :
    0 ≤ layerAbsorption W κ r i ∧ layerAbsorption W κ r i ≤ Kκ / (W : ℝ) ^ 2 :=
  ⟨div_nonneg (hκ0 _) (sq_nonneg _), div_le_div_of_nonneg_right (hK _) (sq_nonneg _)⟩

/-- **`δ₀` of the absorbed path at a fixed length, in probability** (Markov on the
`absorbedMoment` clause of `PassiveInitialScalarContract` at `p = 1`):
`P(d < δ₀(X_r)) ≤ (C/d)/W`. -/
theorem delta_tail (hP : PassiveInitialScalarContract) {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκI : 0 < κI) {κ : ℝ → ℝ} (hκ0 : ∀ s, 0 ≤ κ s) {Kκ : ℝ} (hKκ0 : 0 ≤ Kκ)
    (hK : ∀ s, κ s ≤ Kκ) (T : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ T * W → ∀ d : ℝ, 0 < d →
        growthPathLaw W b {ω | d < jetDistance0 b E (pathNearSchur b E κ W r ω)} ≤
          ENNReal.ofReal (C / d / W) := by
  obtain ⟨C, W₀, hC⟩ := hP.absorbedMoment b hb0 hb κI T Kκ 1 hκI hKκ0 le_rfl
  refine ⟨max C 0, W₀, le_max_right _ _, fun W hW E hE r hr hrT d hd => ?_⟩
  have hm := hC W hW E hE r hr hrT (layerAbsorption W κ r) (layerAbsorption_mem hκ0 hK r)
  have hm' : eLpNorm (fun ω => jetDistance0 b E (pathNearSchur b E κ W r ω)) (ENNReal.ofReal 1)
      (growthPathLaw W b) ≤ ENNReal.ofReal (max C 0 / W) :=
    hm.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _)
      (Nat.cast_nonneg _)))
  refine (markov_one (fun _ => norm_nonneg _) hd (by positivity) hm').trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-- **One finite-core step `r → r+1`, `r ≥ 1`**: `c > 0`, `C ≥ 0`, `W₀` uniform in
`E ∈ bulkInterval κI` and `a > 0`, with `P(q_{r+1} < caW) ≤ P(q_r < aW) + C/W`. -/
theorem core_iter_step (hA : PassiveLayer.PassiveBoundsStatement)
    (hP : PassiveInitialScalarContract) {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) (r : ℕ) (hr : 1 ≤ r) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ a : ℝ, 0 < a →
        growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W (r + 1) ω) < c * a * W} ≤
          growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W r ω) < a * W} +
            ENNReal.ofReal (C / W) := by
  obtain ⟨-, hκ0, K, hK⟩ := hκ
  set Kκ := max K 0
  have hKκ : ∀ s, κ s ≤ Kκ := fun s => (hK s).trans (le_max_left _ _)
  obtain ⟨d, c, C, hd, hc, hC, W₀, hch⟩ := cheb_absorbed hA hb0 hb hκI (le_max_right K 0)
  obtain ⟨Cm, Wm, hCm, hdt⟩ := delta_tail hP hb0 hb hκI hκ0 (le_max_right K 0) hKκ r
  refine ⟨c, C + Cm / d, hc, by positivity, max (max W₀ Wm) 1, fun W hW E hE a ha => ?_⟩
  have hW₀ : W₀ ≤ W := le_of_max_le_left (le_of_max_le_left hW)
  have hWm : Wm ≤ W := le_of_max_le_right (le_of_max_le_left hW)
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have h1 : -2 < E := by linarith [hE.1]
  have h2 : E < 2 := by linarith [hE.2]
  set G : Set (PastSample W r) := hermPast W r ∩
    {p | jetDistance0 b E (pastX b E κ W r p) ≤ d} ∩ {p | a * W ≤ passiveMass b E (pastX b E κ W r p)}
  have hGm : MeasurableSet G :=
    ((measurableSet_hermPast W r).inter (measurableSet_le
      ((measurable_jetDistance0 b E).comp (measurable_pastX b E κ r)) measurable_const)).inter
      (measurableSet_le measurable_const
        ((SourceMixing.measurable_passiveMass b E).comp (measurable_pastX b E κ r)))
  have hae : ∀ᵐ ω ∂growthPathLaw W b, pathNearSchur b E κ W (r + 1) ω =
      freshSchur E (stepInput b E κ W r (pastCoords W r ω)) (freshSample W r ω) := by
    filter_upwards [ae_pathNearSchur_succ_abs hb h1 h2 hW1 hκ0] with ω hω
    rw [hω r hr, pathNearSchur_eq_past]; rfl
  have hgood : ∀ p ∈ G, freshLaw W b {f | passiveMass b E (freshSchur E (stepInput b E κ W r p) f) <
      c * a * W} ≤ ENNReal.ofReal (C / W) := by
    rintro p ⟨⟨hph, hpd⟩, hpq⟩
    have hY := passiveY_pastX (by linarith) h1 h2 hκ0 hph (b := b) (E := E)
    have hq0 : 0 < passiveMass b E (pastX b E κ W r p) :=
      lt_of_lt_of_le (by positivity) hpq
    obtain ⟨hε0, hεK⟩ := layerAbsorption_mem (W := W) hκ0 hKκ (r + 1) 0
    refine (measure_mono fun f hf => ?_).trans
      (hch W hW₀ E hE _ hY hpd hq0 _ hε0 hεK)
    change passiveMass b E (freshSchur E (stepInput b E κ W r p) f) < c * a * W at hf
    change passiveMass b E (freshSchur E (absorbedInput (pastX b E κ W r p)
      (layerAbsorption W κ (r + 1) 0)) f) < c * passiveMass b E (pastX b E κ W r p)
    have : c * a * W ≤ c * passiveMass b E (pastX b E κ W r p) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpq hc.le
    exact lt_of_lt_of_le hf this
  refine (step_prob_le κ r (measurable_stepInput b E κ r) hae hGm hgood).trans ?_
  -- the bad past
  have hnull : growthPathLaw W b (pastCoords W r ⁻¹' (hermPast W r)ᶜ) = 0 := by
    rw [← Measure.map_apply (measurable_pastCoords W r) (measurableSet_hermPast W r).compl,
      growthPathLaw_map_pastCoords]
    exact ae_iff.mp (ae_pastLaw_hermitian W r b)
  have hsub : pastCoords W r ⁻¹' Gᶜ ⊆ (pastCoords W r ⁻¹' (hermPast W r)ᶜ ∪
      {ω | d < jetDistance0 b E (pathNearSchur b E κ W r ω)}) ∪
      {ω | passiveMass b E (pathNearSchur b E κ W r ω) < a * W} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff, G, Set.mem_inter_iff, Set.mem_ofPred_eq,
      not_and_or, not_le] at hω
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq,
      pathNearSchur_eq_past]
    tauto
  have hrT : (r : ℝ) ≤ r * W := le_mul_of_one_le_right (Nat.cast_nonneg _) hW1r
  calc growthPathLaw W b (pastCoords W r ⁻¹' Gᶜ) + ENNReal.ofReal (C / W)
      ≤ (0 + ENNReal.ofReal (Cm / d / W) +
          growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W r ω) < a * W}) +
          ENNReal.ofReal (C / W) := by
        gcongr
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add hnull.le ?_)) le_rfl))
        exact hdt W hWm E hE r hr hrT d hd
    _ = growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W r ω) < a * W} +
          ENNReal.ofReal ((C + Cm / d) / W) := by
        rw [zero_add, add_comm (ENNReal.ofReal _) _, add_assoc, ← ENNReal.ofReal_add
          (by positivity) (by positivity)]
        congr 2; ring

/-- **`FiniteCoreEntrance`** from `PassiveLayer.PassiveBoundsStatement` and
`PassiveInitialScalarContract` (`absorbedMoment` only; the latter is proved as
`Assembly.passiveInitialScalar_holds`).
-/
theorem finiteCoreEntrance_of (hA : PassiveLayer.PassiveBoundsStatement)
    (hP : PassiveInitialScalarContract) : FiniteCoreEntrance := by
  intro b hb0 hb κI hκI κ hκ δ hδ r hr
  induction r, hr using Nat.le_induction generalizing δ with
  | base => exact core_first hA hb0 hb hκI hκ hδ
  | succ r hr ih =>
    obtain ⟨c, C, hc, hC, W₀, hst⟩ := core_iter_step hA hP hb0 hb hκI hκ r hr
    obtain ⟨a, ha, W₁, hq⟩ := ih (δ / 2) (half_pos hδ)
    refine ⟨c * a, by positivity, max (max W₀ W₁) (⌈2 * C / δ⌉₊ + 1), fun W hW E hE => ?_⟩
    have hW₀ : W₀ ≤ W := le_of_max_le_left (le_of_max_le_left hW)
    have hW₁ : W₁ ≤ W := le_of_max_le_right (le_of_max_le_left hW)
    have hW2 : ⌈2 * C / δ⌉₊ + 1 ≤ W := le_of_max_le_right hW
    have hWr : 2 * C / δ + 1 ≤ (W : ℝ) := by
      have := Nat.le_ceil (2 * C / δ)
      have h' : ((⌈2 * C / δ⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW2
      push_cast at h'; linarith
    have hWp : (0 : ℝ) < W := by have : 0 ≤ 2 * C / δ := by positivity
                                 linarith
    have hCW : C / W ≤ δ / 2 := by
      rw [div_le_iff₀ hWp]
      have : 2 * C / δ ≤ W := by linarith
      rw [div_le_iff₀ hδ] at this; nlinarith
    refine (hst W hW₀ E hE a ha).trans ?_
    calc growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W r ω) < a * W} +
          ENNReal.ofReal (C / W) ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          add_le_add (hq W hW₁ E hE) (ENNReal.ofReal_le_ofReal hCW)
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end BlockBand.Transmission.LawFinite
