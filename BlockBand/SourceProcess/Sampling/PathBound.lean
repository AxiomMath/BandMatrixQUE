module

public import BlockBand.SourceProcess.Sampling.RankOneSample
public import BlockBand.SourceProcess.Sampling.LindebergPi

/-!
# Positive-source sampling conditionally on the path

`|E[Π_j F(Σ_i a_{ji} Q̂_{M,i}) | path] - Π_j F(Σ_i a_{ji} Q_i)| ≤
  Σ_i 4M₄ (Σ_j a_{ji})² (m_i/M) Σ_k (q_{ik}/W) (W⁻¹ Re Tr Y_{n;k})²`
(`cond_lindeberg`, with `sampled_eq_hyb` and `srcIntegrand_eq_hyb`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.RawTag
open scoped ComplexOrder

variable {W n : ℕ}

/-- The law of one sample `(k, g)` of test `i`. -/
abbrev sampleLaw (W n : ℕ) (q : ℝ → ℝ) : Measure (ℕ × (Fin W → ℂ)) :=
  (tagSampleLaw W n q).prod (circularVectorLaw (Fin W))

/-- The conditional error bound. -/
def condErr (W n : ℕ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ) (M : ℕ)
    (Y : ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  ∑ i, 4 * gaussMoment 4 * (∑ j, a j i) ^ 2 * (gridMass W n (q i) / M) *
    ∑ k ∈ Finset.range n, q i (((k + 1 : ℕ) : ℝ) / W) / W * ((Y k).trace.re / W) ^ 2

/-- **Lindeberg for the sampled sources, given the path.** -/
theorem cond_lindeberg (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) {p J M : ℕ}
    {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) {a : Fin J → Fin p → ℝ} (ha : ∀ j i, 0 ≤ a j i)
    (hW : 0 < W) (hM : 0 < M) :
    |∫ z, hyb (fun _ => 0) (fun j (x : Fin p × Fin M) => a j x.1)
          (fun x => rankOne U (gridMass W n (q x.1) / (M * W)) (z x))
          ∂Measure.pi (fun x : Fin p × Fin M => sampleLaw W n (q x.1)) -
        hyb (fun _ => 0) (fun j (x : Fin p × Fin M) => a j x.1)
          (fun x => sampleMean U (q x.1) M)| ≤
      condErr W n q a M (fun k => Uᴴ * tagProjection W n k * U) := by
  have hP : ∀ x : Fin p × Fin M, IsProbabilityMeasure (sampleLaw W n (q x.1)) := fun x => by
    have := isProbabilityMeasure_tagSampleLaw W n (hq x.1); infer_instance
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  refine (lindeberg (fun x : Fin p × Fin M => sampleLaw W n (q x.1))
    (fun x => rankOne U (gridMass W n (q x.1) / (M * W))) (fun x => sampleMean U (q x.1) M)
    (fun x => isMatSample_rankOne U (hq x.1) hW hM) (fun _ : Fin J => 0)
    (fun _ => PosSemidef.zero) (fun j x => a j x.1) fun j x => ha j x.1).trans ?_
  rw [condErr, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  set S := ∑ k ∈ Finset.range n, q i (((k + 1 : ℕ) : ℝ) / W) / W *
    ((Uᴴ * tagProjection W n k * U).trace.re / W) ^ 2
  have hl : ∀ l : Fin M, 2 * (∑ j, a j i) ^ 2 * ∫ z, (rankOne U (gridMass W n (q i) / (M * W))
      z).trace.re ^ 2 ∂sampleLaw W n (q i) ≤
      2 * (∑ j, a j i) ^ 2 * (2 * gaussMoment 4 * (gridMass W n (q i) / (M : ℝ) ^ 2) * S) :=
    fun l => mul_le_mul_of_nonneg_left (integral_sq_rankOne_le U (hq i) hW hM) (by positivity)
  refine (Finset.sum_le_sum fun l _ => hl l).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem sum_smul_sum {p J M : ℕ} (a : Fin J → Fin p → ℝ) (j : Fin J)
    (ξ : Fin p × Fin M → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ i, (a j i : ℂ) • ∑ l, ξ (i, l) = 0 + ∑ x : Fin p × Fin M, (a j x.1 : ℂ) • ξ x := by
  rw [zero_add, Fintype.sum_prod_type]
  simp only [Finset.smul_sum]

/-- The sampled integrand as a hybrid value. -/
theorem sampled_eq_hyb (b E : ℝ) {p J M : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ)
    (ω : GrowthPath W) (z : Fin p × Fin M → ℕ × (Fin W → ℂ)) :
    ∏ j, ((1 + ∑ i, (a j i : ℂ) • sampledSource b E W n (q i) M (fun l => (z (i, l)).1)
        (fun l => (z (i, l)).2) ω).det⁻¹).re =
      hyb (fun _ => 0) (fun j (x : Fin p × Fin M) => a j x.1)
        (fun x => rankOne (boundaryToInterior b E W n ω) (gridMass W n (q x.1) / (M * W)) (z x)) := by
  simp only [hyb, invDet]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← sum_smul_sum a j (fun x : Fin p × Fin M => rankOne (boundaryToInterior b E W n ω)
    (gridMass W n (q x.1) / (M * W)) (z x))]
  rfl

/-- The unsampled integrand `srcIntegrand` as a hybrid value at the means. -/
theorem srcIntegrand_eq_hyb (b E : ℝ) {p J M : ℕ} (hM : 0 < M) (q : Fin p → ℝ → ℝ)
    (a : Fin J → Fin p → ℝ) (ω : GrowthPath W) :
    srcIntegrand b E W n q a ω = hyb (fun _ => 0) (fun j (x : Fin p × Fin M) => a j x.1)
      (fun x => sampleMean (boundaryToInterior b E W n ω) (q x.1) M) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ i, ∑ _l : Fin M, sampleMean (boundaryToInterior b E W n ω) (q i) M =
      intervalSource b E W n (q i) ω := fun i => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      sampleMean, smul_smul]
    have : (M : ℂ) * (((M : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by push_cast; exact mul_inv_cancel₀ hMc
    rw [this, one_smul]
    rfl
  simp only [srcIntegrand, hyb, invDet]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← sum_smul_sum a j (fun x : Fin p × Fin M =>
    sampleMean (boundaryToInterior b E W n ω) (q x.1) M)]
  simp only [key]

end BlockBand.SourceProcess.Sampling
