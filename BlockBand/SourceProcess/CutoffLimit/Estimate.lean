module

public import BlockBand.SourceProcess.CutoffLimit.InitBound
public import BlockBand.SourceProcess.CutoffLimit.Transform
public import BlockBand.SourceProcess.CutoffLimit.FrameAlg
public import BlockBand.SourceProcess.SourceProcessLaw.ModelValue

/-!
# Comparison of two cutoff values through a coupling

`IsCutoffCoupling.abs_sub_le`: two finite source model values at cutoffs `h₁ ≤ h₂`, realized by a
coupling of their frames, differ by at most `ε + P(trace ≥ L) + P(distance > u)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourcePins
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

/-- Pointwise: frames with bounded traces that are close give close probe transforms. -/
theorem probeVal_close {ι : Type*} [Fintype ι] {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π]
    {J : ℕ} {a : Fin J → π → ℝ} {ε L u δ : ℝ}
    (hδ : ∀ A B : Matrix π π ℂ, A ∈ psdBox π L → B ∈ psdBox π L →
      (∀ i j, ‖A i j - B i j‖ < δ) → |probeVal a A - probeVal a B| < ε)
    (huL : 2 * (Real.sqrt u * Real.sqrt L) < δ) {V₁ V₂ : Matrix ι (SrcCol K π) ℂ}
    (hL : hsSq V₁ + hsSq V₂ < L) (hu : hsSq (V₁ - V₂) ≤ u) :
    |probeVal a (probeBlock (sourceGram V₁)) - probeVal a (probeBlock (sourceGram V₂))| < ε := by
  have h1 := hsSq_nonneg V₁
  have h2 := hsSq_nonneg V₂
  have hbox : ∀ V : Matrix ι (SrcCol K π) ℂ, hsSq V ≤ L → probeBlock (sourceGram V) ∈ psdBox π L :=
    fun V hV => ⟨probeBlock_posSemidef V, fun i j => (norm_sourceGram_le_hsSq V _ _).trans hV⟩
  refine hδ _ _ (hbox V₁ (by linarith)) (hbox V₂ (by linarith)) fun i j => ?_
  refine lt_of_le_of_lt (norm_sourceGram_sub_le V₁ V₂ _ _) (lt_of_le_of_lt ?_ huL)
  have s0 := Real.sqrt_le_sqrt hu
  have s1 := Real.sqrt_le_sqrt (show hsSq V₁ ≤ L by linarith)
  have s2 := Real.sqrt_le_sqrt (show hsSq V₂ ≤ L by linarith)
  have := Real.sqrt_nonneg (hsSq (V₁ - V₂))
  have := Real.sqrt_nonneg u
  nlinarith [Real.sqrt_nonneg (hsSq V₁), Real.sqrt_nonneg (hsSq V₂)]

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h₁ h₂ : ℝ} {K M : ℕ}
  {ent : Measure (Measure unitInterval)} {ι S : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {Naux : ℕ} {P : Matrix ι ι ℂ}
  {Emb : Matrix ι (Fin K × Fin 2) ℂ}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι)))}
  {tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ}
  {σb : DriverSample S (SourceNoise ι) → Fin p × Fin M → ℝ} {nb : ℕ}
  {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → SrcCol K (Fin p × Fin M)}
  {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
  {X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin p × Fin M)) ℂ}

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
/-- The transform of a coupled frame is measurable (it is a model Gram state). -/
theorem measurable_transform {h : ℝ} {X : ℝ≥0 → DriverSample S (SourceNoise ι) →
      Matrix ι (SrcCol K (Fin p × Fin M)) ℂ}
    (hm : IsFiniteSourceModel b E s T q h K M ent 𝓖 (driverLaw (κ := SourceNoise ι) μ) tseq σb
      (fun t x => gramPair P (X t x))) {J : ℕ} (a : Fin J → Fin p → ℝ) (t : ℝ≥0) :
    Measurable fun x => sampledTransformValue a (gramPair P (X t x)) :=
  (measurable_sampledTransformValue a).comp
    (measurable_of_stronglyMeasurable_gram (𝓖.le _) (hm.solution.adapted t))

omit [DecidableEq ι] in
theorem transform_eq {J : ℕ} (a : Fin J → Fin p → ℝ) (V : Matrix ι (SrcCol K (Fin p × Fin M)) ℂ) :
    sampledTransformValue a (gramPair P V) =
      probeVal (fun j (i : Fin p × Fin M) => a j i.1) (probeBlock (sourceGram V)) := by
  rw [sampledTransformValue_eq]
  rfl

omit [DecidableEq ι] in
theorem transform_mem {J : ℕ} {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i)
    (V : Matrix ι (SrcCol K (Fin p × Fin M)) ℂ) :
    0 ≤ sampledTransformValue a (gramPair P V) ∧ sampledTransformValue a (gramPair P V) ≤ 1 := by
  rw [transform_eq]
  exact probeVal_mem (a := fun j (i : Fin p × Fin M) => a j i.1) (fun j i => ha j i.1)
    (probeBlock_posSemidef V)

/-- For `[0,1]`-valued measurable `f₁, f₂` with `|f₁ − f₂| < ε` off `A`:
`|E f₁ − E f₂| ≤ ε + P(A)` (outer measure; `A` need not be measurable). -/
theorem ofReal_abs_integral_sub_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {f₁ f₂ : Ω → ℝ} (m₁ : Measurable f₁) (m₂ : Measurable f₂)
    (b₁ : ∀ x, 0 ≤ f₁ x ∧ f₁ x ≤ 1) (b₂ : ∀ x, 0 ≤ f₂ x ∧ f₂ x ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {A : Set Ω} (hA : ∀ x, x ∉ A → |f₁ x - f₂ x| < ε) :
    ENNReal.ofReal |∫ x, f₁ x ∂Q - ∫ x, f₂ x ∂Q| ≤ ENNReal.ofReal ε + Q A := by
  have i₁ : Integrable f₁ Q := Integrable.of_bound m₁.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [b₁ x])
  have i₂ : Integrable f₂ Q := Integrable.of_bound m₂.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [b₂ x])
  set B := {x | ε ≤ |f₁ x - f₂ x|} with hB
  have hBm : MeasurableSet B := measurableSet_le measurable_const ((m₁.sub m₂).abs)
  have hI : Integrable (B.indicator (1 : Ω → ℝ)) Q := (integrable_const (1 : ℝ)).indicator hBm
  have hpt : ∀ x, |f₁ x - f₂ x| ≤ ε + B.indicator 1 x := fun x => by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, abs_le]
      constructor <;> linarith [b₁ x, b₂ x]
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact (not_le.1 hx).le
  have hint : |∫ x, f₁ x ∂Q - ∫ x, f₂ x ∂Q| ≤ ε + Q.real B := by
    rw [← integral_sub i₁ i₂]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |f₁ x - f₂ x| ∂Q ≤ ∫ x, (ε + B.indicator 1 x) ∂Q :=
          integral_mono (i₁.sub i₂).abs ((integrable_const ε).add hI) hpt
      _ = ε + Q.real B := by
          rw [integral_add (integrable_const ε) hI,
            integral_const, integral_indicator_one hBm, probReal_univ, one_smul]
  have hsub : B ⊆ A := fun x hx => by
    by_contra hn
    exact absurd hx (not_le.2 (hA x hn))
  calc _ ≤ ENNReal.ofReal (ε + Q.real B) := ENNReal.ofReal_le_ofReal hint
    _ ≤ ENNReal.ofReal ε + Q B := by
        rw [ENNReal.ofReal_add hε.le measureReal_nonneg]
        exact add_le_add le_rfl ENNReal.ofReal_toReal_le
    _ ≤ _ := add_le_add le_rfl (measure_mono hsub)

/-- **`|v₁ − v₂| ≤ ε + P(trace ≥ L) + P(distance > u)`.** -/
theorem IsCutoffCoupling.abs_sub_le
    (hC : IsCutoffCoupling b E s T q h₁ h₂ K M ent μ Naux P Emb 𝓖 tseq σb τ col w β X₁ X₂)
    {J : ℕ} {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i) {ε L u δ : ℝ} (hε : 0 < ε)
    (hδ : ∀ A B : Matrix (Fin p × Fin M) (Fin p × Fin M) ℂ, A ∈ psdBox _ L → B ∈ psdBox _ L →
      (∀ i j, ‖A i j - B i j‖ < δ) →
        |probeVal (fun j (i : Fin p × Fin M) => a j i.1) A -
          probeVal (fun j (i : Fin p × Fin M) => a j i.1) B| < ε)
    (huL : 2 * (Real.sqrt u * Real.sqrt L) < δ) {v₁ v₂ : ℝ}
    (hv₁ : FiniteSourceModelValue b E s T q h₁ K M ent a v₁)
    (hv₂ : FiniteSourceModelValue b E s T q h₂ K M ent a v₂) :
    ENNReal.ofReal |v₁ - v₂| ≤ ENNReal.ofReal ε +
      (driverLaw (κ := SourceNoise ι) μ
          {x | L ≤ hsSq (X₁ (T - s).toNNReal x) + hsSq (X₂ (T - s).toNNReal x)} +
        driverLaw (κ := SourceNoise ι) μ
          {x | u < hsSq (X₁ (T - s).toNNReal x - X₂ (T - s).toNNReal x)}) := by
  have e₁ : ∫ x, sampledTransformValue a (gramPair P (X₁ (T - s).toNNReal x))
      ∂driverLaw (κ := SourceNoise ι) μ = v₁ :=
    hv₁.2 (DriverSample S (SourceNoise ι)) inferInstance 𝓖 (driverLaw (κ := SourceNoise ι) μ)
      tseq σb (fun t x => gramPair P (X₁ t x)) hC.model₁
  have e₂ : ∫ x, sampledTransformValue a (gramPair P (X₂ (T - s).toNNReal x))
      ∂driverLaw (κ := SourceNoise ι) μ = v₂ :=
    hv₂.2 (DriverSample S (SourceNoise ι)) inferInstance 𝓖 (driverLaw (κ := SourceNoise ι) μ)
      tseq σb (fun t x => gramPair P (X₂ t x)) hC.model₂
  rw [← e₁, ← e₂]
  refine (ofReal_abs_integral_sub_le (measurable_transform hC.model₁ a _)
    (measurable_transform hC.model₂ a _) (fun x => transform_mem ha _)
    (fun x => transform_mem ha _) hε (A := {x | L ≤ hsSq (X₁ (T - s).toNNReal x) +
      hsSq (X₂ (T - s).toNNReal x)} ∪ {x | u < hsSq (X₁ (T - s).toNNReal x -
        X₂ (T - s).toNNReal x)}) fun x hx => ?_).trans (add_le_add le_rfl (measure_union_le _ _))
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_lt] at hx
  rw [transform_eq, transform_eq]
  exact probeVal_close (K := K) hδ huL hx.1 hx.2

end BlockBand.SourceProcess.CutoffLimit
