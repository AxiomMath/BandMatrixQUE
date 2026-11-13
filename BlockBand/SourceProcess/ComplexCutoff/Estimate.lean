module

public import BlockBand.SourceProcess.ComplexCutoff.Compare

/-!
# The coupled comparison of two complex cutoff values

`IsComplexCutoffCoupling.abs_sub_le`: for two complex finite models at cutoffs `h₁ ≤ h₂` coupled on
one driver space, their values differ by at most `ε + 2‖Φ‖` times the sum of four probabilities
(large traces, distant frames, large or distant `𝒦`s).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.CutoffLimit
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- Entries of `J + (ΔY)_pr` are at most `‖J‖ + ‖ΔY‖`. -/
theorem norm_kEntry_le {K np : ℕ} (J : Matrix (Fin np) (Fin np) ℂ)
    (A : Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) (i j : Fin np) :
    ‖(J + probeBlock A) i j‖ ≤ ‖J‖ + ‖A‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_entry_le J i j) (norm_entry_le A _ _))

variable {b E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {h₁ h₂ : ℝ} {K : ℕ}
  {ent : Measure (Measure unitInterval)} {ι S : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {Naux : ℕ} {P : Matrix ι ι ℂ}
  {Emb : Matrix ι (Fin K × Fin 2) ℂ}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι)))}
  {tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ} {nb : ℕ}
  {tb : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → SrcCol K (Fin np)}
  {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
  {X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin np)) ℂ}
  {Y₁ Y₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ}

/-- **`|v₁ − v₂| ≤ ε + 2‖Φ‖ (four probabilities)`.** -/
theorem IsComplexCutoffCoupling.abs_sub_le
    (hC : IsComplexCutoffCoupling b E s τ m h₁ h₂ K ent μ Naux P Emb 𝓖 tseq tb col w β
      X₁ X₂ Y₁ Y₂) {T : ℝ} (Φ : BoundedContinuousFunction (SourceData np) ℝ)
    {ε L u Lk δk Λ δ : ℝ} (hε : 0 < ε)
    (hδ : ∀ y z : SourceData np, (∀ r i j, ‖y r i j‖ ≤ Λ) → (∀ r i j, ‖z r i j‖ ≤ Λ) →
      (∀ r i j, ‖y r i j - z r i j‖ < δ) → |Φ y - Φ z| < ε)
    (hΛ : ‖kBirthJump E (fun j => τ j - s) m ((T - s).toNNReal : ℝ)‖ + Real.sqrt Lk +
      Real.sqrt δk + L + L ^ 2 ≤ Λ)
    (hδΛ : Real.sqrt δk + Real.sqrt u * (2 * Real.sqrt L) * (1 + 2 * L) < δ) {v₁ v₂ : ℝ}
    (hv₁ : ComplexModelValue b E s T τ m h₁ K ent Φ v₁)
    (hv₂ : ComplexModelValue b E s T τ m h₂ K ent Φ v₂) :
    ENNReal.ofReal |v₁ - v₂| ≤ ENNReal.ofReal ε + ENNReal.ofReal (2 * ‖Φ‖) *
      (driverLaw (κ := SourceNoise ι) μ
          {x | L ≤ hsSq (X₁ (T - s).toNNReal x) + hsSq (X₂ (T - s).toNNReal x)} +
        driverLaw (κ := SourceNoise ι) μ
          {x | u < hsSq (X₁ (T - s).toNNReal x - X₂ (T - s).toNNReal x)} +
        driverLaw (κ := SourceNoise ι) μ
          {x | Lk < hsSq (Y₁ (T - s).toNNReal x - Y₁ 0 x)} +
        driverLaw (κ := SourceNoise ι) μ
          {x | δk < hsSq ((Y₁ (T - s).toNNReal x - Y₁ 0 x) -
            (Y₂ (T - s).toNNReal x - Y₂ 0 x))}) := by
  set t := (T - s).toNNReal
  set Q := driverLaw (κ := SourceNoise ι) μ
  set J := kBirthJump E (fun j => τ j - s) m (t : ℝ)
  have e₁ := hv₁.2 (DriverSample S (SourceNoise ι)) inferInstance 𝓖 Q tseq
    (fun t x => gramPair P (X₁ t x)) (kProc E s τ m Y₁) hC.model₁
  have e₂ := hv₂.2 (DriverSample S (SourceNoise ι)) inferInstance 𝓖 Q tseq
    (fun t x => gramPair P (X₂ t x)) (kProc E s τ m Y₂) hC.model₂
  rw [← e₁, ← e₂]
  have hbd : ∀ y : SourceData np, |Φ y| ≤ ‖Φ‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm y
  refine (ofReal_abs_integral_sub_le' (measurable_value hC.model₁ Φ t)
    (measurable_value hC.model₂ Φ t) (norm_nonneg Φ) (fun x => hbd _) (fun x => hbd _) hε
    (A := {x | L ≤ hsSq (X₁ t x) + hsSq (X₂ t x)} ∪ {x | u < hsSq (X₁ t x - X₂ t x)} ∪
      {x | Lk < hsSq (Y₁ t x - Y₁ 0 x)} ∪
      {x | δk < hsSq ((Y₁ t x - Y₁ 0 x) - (Y₂ t x - Y₂ 0 x))}) fun x hx => ?_).trans ?_
  · simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_lt] at hx
    obtain ⟨⟨⟨hR, hX⟩, hK1⟩, hK12⟩ := hx
    simp only [hsSq_eq] at hR hX hK1 hK12
    have hL1 : ‖Y₁ t x - Y₁ 0 x‖ ≤ Real.sqrt Lk := Real.le_sqrt_of_sq_le hK1
    have hL12 : ‖(Y₁ t x - Y₁ 0 x) - (Y₂ t x - Y₂ 0 x)‖ ≤ Real.sqrt δk :=
      Real.le_sqrt_of_sq_le hK12
    have hL2 : ‖Y₂ t x - Y₂ 0 x‖ ≤ Real.sqrt Lk + Real.sqrt δk := by
      have := norm_sub_le (Y₁ t x - Y₁ 0 x) ((Y₁ t x - Y₁ 0 x) - (Y₂ t x - Y₂ 0 x))
      rw [sub_sub_cancel] at this
      linarith
    have k1 : ∀ i j, ‖kProc E s τ m Y₁ t x i j‖ ≤ ‖J‖ + Real.sqrt Lk + Real.sqrt δk :=
      fun i j => (norm_kEntry_le J _ i j).trans (by linarith [Real.sqrt_nonneg δk])
    have k2 : ∀ i j, ‖kProc E s τ m Y₂ t x i j‖ ≤ ‖J‖ + Real.sqrt Lk + Real.sqrt δk :=
      fun i j => (norm_kEntry_le J _ i j).trans (by linarith)
    have k12 : ∀ i j, ‖kProc E s τ m Y₁ t x i j - kProc E s τ m Y₂ t x i j‖ ≤ Real.sqrt δk :=
      fun i j => by
        have h := norm_entry_le ((Y₁ t x - Y₁ 0 x) - (Y₂ t x - Y₂ 0 x)) (Sum.inr i) (Sum.inr j)
        simp only [kProc, Matrix.add_apply, probeBlock, Matrix.sub_apply] at h ⊢
        rw [add_sub_add_left_eq_sub]
        linarith
    obtain ⟨b1, b2, b12⟩ := data_close hC.nearProj hR hX k1 k2 k12 hΛ hδΛ
    exact hδ _ _ b1 b2 b12
  · refine add_le_add le_rfl (mul_le_mul_right ?_ _)
    exact (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)

end BlockBand.SourceProcess.ComplexCutoff
