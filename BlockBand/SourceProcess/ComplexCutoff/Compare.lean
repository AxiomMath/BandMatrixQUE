module

public import BlockBand.SourceProcess.ComplexCutoff.DataAlg
public import BlockBand.SourceProcess.ComplexUniqueSegment.Model

/-!
# Comparison of two complex cutoff values through a coupling

Auxiliary bounds for comparing the values of two coupled complex finite models: a modulus of
uniform continuity of a bounded continuous `Φ` on a compact box of source data (`exists_modulus`),
the bound `|E f₁ − E f₂| ≤ ε + 2B P(A)` for functions bounded by `B` that are `ε`-close off `A`
(`ofReal_abs_integral_sub_le'`), and the closeness of the source data of close frames and close
`𝒦`s (`data_close`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.CutoffLimit
open BlockBand.SourceProcess.ComplexUniqueSegment
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

/-- The box `{y : |y_rij| ≤ Λ}` of the source data (on the underlying product space). -/
def dataBox (np : ℕ) (Λ : ℝ) : Set (Fin 4 → Fin np → Fin np → ℂ) := {y | ∀ r i j, ‖y r i j‖ ≤ Λ}

theorem isCompact_dataBox (np : ℕ) (Λ : ℝ) : IsCompact (dataBox np Λ) := by
  have h := isCompact_univ_pi fun _ : Fin 4 => isCompact_univ_pi fun _ : Fin np =>
    isCompact_univ_pi fun _ : Fin np => isCompact_closedBall (0 : ℂ) Λ
  have he : dataBox np Λ =
      Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall 0 Λ := by
    ext y
    simp [dataBox]
  rw [he]
  exact h

/-- **A modulus of uniform continuity of `Φ` on the box**, in the entrywise distance. -/
theorem exists_modulus {np : ℕ} (Φ : BoundedContinuousFunction (SourceData np) ℝ) (Λ ε : ℝ)
    (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ y z : SourceData np, (∀ r i j, ‖y r i j‖ ≤ Λ) →
      (∀ r i j, ‖z r i j‖ ≤ Λ) → (∀ r i j, ‖y r i j - z r i j‖ < δ) → |Φ y - Φ z| < ε := by
  let f : (Fin 4 → Fin np → Fin np → ℂ) → ℝ := fun y => Φ y
  have hc : Continuous f := Φ.continuous
  have huc : UniformContinuousOn f (dataBox np Λ) :=
    (isCompact_dataBox np Λ).uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  refine ⟨δ, hδ, fun y z hy hz hyz => ?_⟩
  let y' : Fin 4 → Fin np → Fin np → ℂ := y
  let z' : Fin 4 → Fin np → Fin np → ℂ := z
  have hd : dist y' z' < δ := by
    refine (dist_pi_lt_iff hδ).2 fun r => (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2
      fun j => ?_
    rw [dist_eq_norm]
    exact hyz r i j
  have := hδε y' hy z' hz hd
  rwa [Real.dist_eq] at this

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
attribute [local instance] matrix_pseudoMetrizable matrix_secondCountable jointState_borel

/-- For measurable `f₁, f₂` bounded by `B` with `|f₁ − f₂| < ε` off `A`:
`|E f₁ − E f₂| ≤ ε + 2B P(A)` (outer measure; `A` need not be measurable). -/
theorem ofReal_abs_integral_sub_le' {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {f₁ f₂ : Ω → ℝ} (m₁ : Measurable f₁) (m₂ : Measurable f₂) {B : ℝ}
    (hB : 0 ≤ B) (b₁ : ∀ x, |f₁ x| ≤ B) (b₂ : ∀ x, |f₂ x| ≤ B) {ε : ℝ} (hε : 0 < ε)
    {A : Set Ω} (hA : ∀ x, x ∉ A → |f₁ x - f₂ x| < ε) :
    ENNReal.ofReal |∫ x, f₁ x ∂Q - ∫ x, f₂ x ∂Q| ≤
      ENNReal.ofReal ε + ENNReal.ofReal (2 * B) * Q A := by
  have i₁ : Integrable f₁ Q := Integrable.of_bound m₁.aestronglyMeasurable B
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact b₁ x)
  have i₂ : Integrable f₂ Q := Integrable.of_bound m₂.aestronglyMeasurable B
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact b₂ x)
  set C := {x | ε ≤ |f₁ x - f₂ x|} with hC
  have hCm : MeasurableSet C := measurableSet_le measurable_const ((m₁.sub m₂).abs)
  have hI : Integrable (C.indicator fun _ => 2 * B) Q :=
    (integrable_const (2 * B)).indicator hCm
  have hpt : ∀ x, |f₁ x - f₂ x| ≤ ε + C.indicator (fun _ => 2 * B) x := fun x => by
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      have h1 := b₁ x
      have h2 := b₂ x
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact (not_le.1 hx).le
  have hint : |∫ x, f₁ x ∂Q - ∫ x, f₂ x ∂Q| ≤ ε + 2 * B * Q.real C := by
    rw [← integral_sub i₁ i₂]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |f₁ x - f₂ x| ∂Q ≤ ∫ x, (ε + C.indicator (fun _ => 2 * B) x) ∂Q :=
          integral_mono (i₁.sub i₂).abs ((integrable_const ε).add hI) hpt
      _ = ε + 2 * B * Q.real C := by
          rw [integral_add (integrable_const ε) hI, integral_const, integral_indicator hCm,
            setIntegral_const, probReal_univ, one_smul, smul_eq_mul, mul_comm]
  have hsub : C ⊆ A := fun x hx => by
    by_contra hn
    exact absurd hx (not_le.2 (hA x hn))
  calc _ ≤ ENNReal.ofReal (ε + 2 * B * Q.real C) := ENNReal.ofReal_le_ofReal hint
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal (2 * B) * Q C := by
        rw [ENNReal.ofReal_add hε.le (by positivity), ENNReal.ofReal_mul (by positivity)]
        exact add_le_add le_rfl (mul_le_mul_right ENNReal.ofReal_toReal_le _)
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_right (measure_mono hsub) _)

/-- The value integrand of a complex finite model is measurable. -/
theorem measurable_value {b E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {h : ℝ} {K : ℕ}
    {ent : Measure (Measure unitInterval)} {Ω : Type} {mΩ : MeasurableSpace Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {Q : Measure Ω} {tseq : Ω → ℕ → ℝ}
    {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hM : IsFiniteComplexSourceModel b E s τ m h K ent 𝓖 Q tseq G Kc)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (t : ℝ≥0) :
    Measurable fun ω => Φ (modelSourceData (srcSignature K (Fin np)) (Kc t ω) (G t ω)) :=
  (Φ.continuous.comp (continuous_modelSourceData _)).measurable.comp (model_measurable_joint hM t)

/-- Pointwise: frames with bounded traces that are close, and `𝒦`s that are bounded and close,
give source data in the box and entrywise close. -/
theorem data_close {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} {Naux K np : ℕ}
    (hP : IsNearProjection P Naux) {V₁ V₂ : Matrix ι (SrcCol K (Fin np)) ℂ}
    {K₁ K₂ : Matrix (Fin np) (Fin np) ℂ} {L u κ κ' Λ δ : ℝ}
    (hR : ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2 < L) (hX : ‖V₁ - V₂‖ ^ 2 ≤ u)
    (hK₁ : ∀ i j, ‖K₁ i j‖ ≤ κ) (hK₂ : ∀ i j, ‖K₂ i j‖ ≤ κ) (hK : ∀ i j, ‖K₁ i j - K₂ i j‖ ≤ κ')
    (hΛ : κ + L + L ^ 2 ≤ Λ) (hδ : κ' + Real.sqrt u * (2 * Real.sqrt L) * (1 + 2 * L) < δ) :
    (∀ r i j, ‖modelSourceData (srcSignature K (Fin np)) K₁ (gramPair P V₁) r i j‖ ≤ Λ) ∧
      (∀ r i j, ‖modelSourceData (srcSignature K (Fin np)) K₂ (gramPair P V₂) r i j‖ ≤ Λ) ∧
      ∀ r i j, ‖modelSourceData (srcSignature K (Fin np)) K₁ (gramPair P V₁) r i j -
        modelSourceData (srcSignature K (Fin np)) K₂ (gramPair P V₂) r i j‖ < δ := by
  have a1 := sq_nonneg ‖V₁‖
  have a2 := sq_nonneg ‖V₂‖
  have hL : 0 ≤ L := by linarith
  have q1 : ‖V₁‖ ^ 2 ≤ L := by linarith
  have q2 : ‖V₂‖ ^ 2 ≤ L := by linarith
  have q1' : ‖V₁‖ ^ 4 ≤ L ^ 2 := by
    rw [show ‖V₁‖ ^ 4 = (‖V₁‖ ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ a1 q1 2
  have q2' : ‖V₂‖ ^ 4 ≤ L ^ 2 := by
    rw [show ‖V₂‖ ^ 4 = (‖V₂‖ ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ a2 q2 2
  have s1 : ‖V₁‖ ≤ Real.sqrt L := Real.le_sqrt_of_sq_le q1
  have s2 : ‖V₂‖ ≤ Real.sqrt L := Real.le_sqrt_of_sq_le q2
  have s0 : ‖V₁ - V₂‖ ≤ Real.sqrt u := Real.le_sqrt_of_sq_le hX
  refine ⟨fun r i j => ?_, fun r i j => ?_, fun r i j => ?_⟩
  · exact (norm_data_le hP hK₁ V₁ r i j).trans (by linarith)
  · exact (norm_data_le hP hK₂ V₂ r i j).trans (by linarith)
  · refine (norm_data_sub_le hP hK V₁ V₂ r i j).trans_lt (lt_of_le_of_lt ?_ hδ)
    have m1 : ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) ≤ Real.sqrt u * (2 * Real.sqrt L) :=
      mul_le_mul s0 (by linarith) (by positivity) (Real.sqrt_nonneg _)
    have m2 : ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) ≤
        Real.sqrt u * (2 * Real.sqrt L) * (1 + 2 * L) :=
      mul_le_mul m1 (by linarith) (by positivity) (by positivity)
    linarith

end BlockBand.SourceProcess.ComplexCutoff
