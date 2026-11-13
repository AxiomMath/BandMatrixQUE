module

public import BlockBand.Critical.RelativeVectors.MarkPerturb
public import BlockBand.Coarea.FreshPalmDensity

/-!
# Window decomposition and the window test

The comparison is applied, for each set `S` of ranks, to `f = M⁻¹ exp(-Σ_{m<|S|} φ(x_{ι m}, L z_m))`
on `B_S = 𝒢 ∩ {the ranks with |x| ≤ R are exactly S}` (`ι` the increasing enumeration of `S`).

*Points and marks.* For a matrix `K`, `x_ℓ(K) = Nρ(λ_ℓ(K) - E)` (`freshEigenvalue`, increasing
ranks) and `z_ℓ = √N e^{iθ_ℓ} V^*u_ℓ(K)` (`relativeMark`). *Laws.* `phaseVectorLaw N`
(`IsProbabilityMeasure` here), `circularVectorLaw`, `gaussianMarkLaw`.

* `windowSet ρ E R K = {ℓ : |x_ℓ(K)| ≤ R}`; `measurableSet_filter_eq`: `{ω : window(X ω) = S}`
  is measurable for every σ-algebra making the points measurable (used with `pathSigma`).
* `markedIntegrand`, `gaussIntegrand` (`Π_ℓ I_L(x_ℓ)`) and their measurability;
  `markedLaplace_eq`.
* `relativeMark_mul`: `z_ℓ(V₀T) = T^* z_ℓ(V₀)`.
* `windowTest`, `isC2Bounded_windowTest`, `isPathMarkTest_windowTest`,
  `integral_windowTest_gauss` (`∫ f dγ^{⊗n} = M⁻¹ Π_m I_L(y_m)`).
* `exp_marked_eq_windowTest`, `gaussIntegrand_eq_windowTest`: on `{window = S}` the marked and
  Gaussian integrands are `M` times the window test and its Gaussian average.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm

variable {N r : ℕ}

/-!
## Phases
-/

theorem measurable_phaseMap :
    Measurable (fun θ : ℝ => Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)) := by
  fun_prop

instance isProbabilityMeasure_phaseLaw : IsProbabilityMeasure phaseLaw := by
  refine ⟨?_⟩
  rw [phaseLaw, Measure.map_apply measurable_phaseMap MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Icc]
  simp

instance isProbabilityMeasure_phaseVectorLaw (N : ℕ) : IsProbabilityMeasure (phaseVectorLaw N) := by
  unfold phaseVectorLaw; infer_instance

/-!
## Window sets
-/

/-- `{ℓ : |Nρ(λ_ℓ(K) - E)| ≤ R}`. -/
def windowSet (ρ E R : ℝ) (K : Matrix (Fin N) (Fin N) ℂ) : Finset (Fin N) :=
  Finset.univ.filter fun ℓ => |(N : ℝ) * ρ * (freshEigenvalue K ℓ - E)| ≤ R

theorem measurableSet_filter_eq {Ω : Type*} {m : MeasurableSpace Ω} (X : Ω → Fin N → ℝ)
    (hX : ∀ ℓ, Measurable[m] fun ω => X ω ℓ) (R : ℝ) (S : Finset (Fin N)) :
    MeasurableSet[m] {ω | (Finset.univ.filter fun ℓ => |X ω ℓ| ≤ R) = S} := by
  have hset : {ω | (Finset.univ.filter fun ℓ => |X ω ℓ| ≤ R) = S} =
      ⋂ ℓ, {ω | |X ω ℓ| ≤ R ↔ ℓ ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.ext_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hset]
  refine MeasurableSet.iInter fun ℓ => ?_
  have hm : MeasurableSet[m] {ω | |X ω ℓ| ≤ R} :=
    measurableSet_le (continuous_abs.measurable.comp (hX ℓ)) measurable_const
  by_cases h : ℓ ∈ S
  · simpa [h] using hm
  · have he : {ω | |X ω ℓ| ≤ R ↔ ℓ ∈ S} = {ω | |X ω ℓ| ≤ R}ᶜ := by
      ext ω; simp only [h, iff_false, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [he]; exact hm.compl

theorem measurable_pi_of_forall {Ω : Type*} {m : MeasurableSpace Ω} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (h : ∀ i, Measurable[m] fun ω => Y ω i) : Measurable[m] Y :=
  measurable_pi_iff.2 h

/-!
## Integrands
-/

/-- `Ψ₁(K) = ∫ exp(-Σ_ℓ φ(x_ℓ(K), z_ℓ(V, K, θ))) dθ`. -/
def markedIntegrand (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ) (φ : ℝ × (Fin r → ℂ) → ℝ)
    (K : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∫ θ, Real.exp (-∑ ℓ : Fin N, φ ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E), relativeMark V K θ ℓ))
    ∂phaseVectorLaw N

/-- `Ψ₂(K) = Π_ℓ I_L(x_ℓ(K))`. -/
def gaussIntegrand (ρ E : ℝ) (φ : ℝ × (Fin r → ℂ) → ℝ) (L : Matrix (Fin r) (Fin r) ℂ)
    (K : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∏ ℓ : Fin N, markAverageL r φ L ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E))

theorem markedLaplace_eq (c : ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) (φ : ℝ × (Fin r → ℂ) → ℝ) :
    markedLaplace c F E V φ = ∫ G, markedIntegrand (unfoldingDensity F c E) E V φ (F + G)
      ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) := rfl

theorem measurable_relativeMark (V : Matrix (Fin N) (Fin r) ℂ) (ℓ : Fin N) :
    Measurable (fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) => relativeMark V p.1 p.2 ℓ) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [relativeMark, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
  refine measurable_const.mul (((measurable_pi_apply ℓ).comp measurable_snd).mul ?_)
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul
    ((BlockBand.Palm.MomentFlow.measurable_freshEigenvector ℓ j).comp measurable_fst)

theorem measurable_markedIntegrand {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ) :
    Measurable (markedIntegrand ρ E V φ) := by
  have h : Measurable (fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      Real.exp (-∑ ℓ : Fin N, φ ((N : ℝ) * ρ * (freshEigenvalue p.1 ℓ - E),
        relativeMark V p.1 p.2 ℓ))) := by
    refine Real.measurable_exp.comp (Measurable.neg ?_)
    refine Finset.measurable_sum _ fun ℓ _ => hφ.continuous.measurable.comp ?_
    refine Measurable.prodMk ?_ (measurable_relativeMark V ℓ)
    exact measurable_const.mul
      (((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).comp measurable_fst).sub
        measurable_const)
  exact (h.stronglyMeasurable.integral_prod_right' (ν := phaseVectorLaw N)).measurable

theorem continuous_markAverageL {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (L : Matrix (Fin r) (Fin r) ℂ) :
    Continuous (markAverageL r φ L) := by
  unfold markAverageL
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
  · intro x
    exact (continuous_exp_neg_L hφ L x).aestronglyMeasurable
  · intro x
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (hφ.nonneg _))
  · filter_upwards with g
    exact Real.continuous_exp.comp ((hφ.continuous.comp
      (continuous_id.prodMk continuous_const)).neg)

theorem measurable_gaussIntegrand {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (ρ E : ℝ) (L : Matrix (Fin r) (Fin r) ℂ) :
    Measurable (gaussIntegrand (N := N) ρ E φ L) := by
  unfold gaussIntegrand
  refine Finset.measurable_prod _ fun ℓ _ => (continuous_markAverageL hφ L).measurable.comp ?_
  exact measurable_const.mul
    ((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).sub measurable_const)

theorem markedIntegrand_mem {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ)
    (K' : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ markedIntegrand ρ E V φ K' ∧ markedIntegrand ρ E V φ K' ≤ 1 := by
  refine ⟨integral_nonneg fun _ => (Real.exp_pos _).le, ?_⟩
  have hb : ∀ θ, Real.exp (-∑ ℓ : Fin N, φ ((N : ℝ) * ρ * (freshEigenvalue K' ℓ - E),
      relativeMark V K' θ ℓ)) ≤ 1 := fun θ =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Finset.sum_nonneg fun _ _ => hφ.nonneg _))
  calc markedIntegrand ρ E V φ K' ≤ ∫ _θ, (1 : ℝ) ∂phaseVectorLaw N := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
          (integrable_const _) (Filter.Eventually.of_forall hb)
    _ = 1 := by simp

theorem gaussIntegrand_mem {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (ρ E : ℝ) (L : Matrix (Fin r) (Fin r) ℂ)
    (K' : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ gaussIntegrand ρ E φ L K' ∧ gaussIntegrand ρ E φ L K' ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (markAverageL_mem hφ L _).1,
    Finset.prod_le_one₀ (fun _ _ => (markAverageL_mem hφ L _).1)
      fun _ _ => (markAverageL_mem hφ L _).2⟩

/-!
## Frame change of the marks
-/

theorem relativeMark_mul (V₀ : Matrix (Fin N) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) ℂ)
    (K : Matrix (Fin N) (Fin N) ℂ) (θ : Fin N → ℂ) (ℓ : Fin N) :
    relativeMark (V₀ * T) K θ ℓ = Tᴴ *ᵥ relativeMark V₀ K θ ℓ := by
  unfold relativeMark
  rw [conjTranspose_mul, ← mulVec_mulVec, mulVec_smul, mulVec_smul]

/-!
## Enumerating a finite set of ranks
-/

theorem sum_orderEmbOfFin {β : Type*} [AddCommMonoid β] (S : Finset (Fin N)) (f : Fin N → β) :
    ∑ ℓ ∈ S, f ℓ = ∑ m : Fin S.card, f (S.orderEmbOfFin rfl m) := by
  conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
  rw [Finset.sum_image fun x _ y _ h => (S.orderEmbOfFin rfl).injective h]

theorem prod_orderEmbOfFin {β : Type*} [CommMonoid β] (S : Finset (Fin N)) (f : Fin N → β) :
    ∏ ℓ ∈ S, f ℓ = ∏ m : Fin S.card, f (S.orderEmbOfFin rfl m) := by
  conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
  rw [Finset.prod_image fun x _ y _ h => (S.orderEmbOfFin rfl).injective h]

/-!
## The window test
-/

/-- `f(y, z) = M⁻¹ exp(-Σ_m φ(y_m, L z_m))`, `M = expSumConst n K B`. -/
def windowTest (n : ℕ) (K B : ℝ) (φ : ℝ × (Fin r → ℂ) → ℝ) (L : Matrix (Fin r) (Fin r) ℂ)
    (y : Fin n → ℝ) (z : MarkArray n r) : ℝ :=
  (expSumConst n K B)⁻¹ * Real.exp (-∑ m, φ (y m, L *ᵥ z m))

theorem isC2Bounded_windowTest {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) {n : ℕ} {B : ℝ} {L : Matrix (Fin r) (Fin r) ℂ}
    (hB : ‖matCLM L‖ ≤ B) (y : Fin n → ℝ) : IsC2Bounded 1 (windowTest n K B φ L y) :=
  isC2Bounded_expSum (fun m w => φ (y m, w)) (fun m => hφ.c2 (y m)) (fun _ _ => hφ.nonneg _) L hB

theorem continuous_windowTest {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (n : ℕ) (B : ℝ) (L : Matrix (Fin r) (Fin r) ℂ) :
    Continuous (fun p : (Fin n → ℝ) × MarkArray n r => windowTest n K B φ L p.1 p.2) := by
  unfold windowTest
  refine continuous_const.mul (Real.continuous_exp.comp (continuous_finsetSum _ fun m _ =>
    hφ.continuous.comp ?_).neg)
  exact ((continuous_apply m).comp continuous_fst).prodMk
    ((matCLM L).continuous.comp ((continuous_apply m).comp continuous_snd))

theorem isPathMarkTest_windowTest {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) {n : ℕ} {B : ℝ} {L : Matrix (Fin r) (Fin r) ℂ}
    (hB : ‖matCLM L‖ ≤ B) {Ω : Type*} (𝓛 : MeasurableSpace Ω) (Y : Ω → Fin n → ℝ)
    (hY : Measurable[𝓛] Y) :
    IsPathMarkTest 𝓛 (fun ω z => windowTest n K B φ L (Y ω) z) := by
  refine ⟨?_, fun ω => isC2Bounded_windowTest hφ hB (Y ω)⟩
  let mP : MeasurableSpace (Ω × MarkArray n r) := MeasurableSpace.comap Prod.fst 𝓛 ⊔
    MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (MarkArray n r))
  have hfst : Measurable[mP, 𝓛] (Prod.fst : Ω × MarkArray n r → Ω) :=
    Measurable.of_comap_le le_sup_left
  have hsnd : Measurable[mP] (Prod.snd : Ω × MarkArray n r → MarkArray n r) :=
    Measurable.of_comap_le le_sup_right
  have hpair : Measurable[mP] (fun p : Ω × MarkArray n r => (Y p.1, p.2)) :=
    (hY.comp hfst).prodMk hsnd
  exact (continuous_windowTest hφ n B L).measurable.comp hpair

theorem integral_windowTest_gauss {K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (n : ℕ) (B : ℝ) (L : Matrix (Fin r) (Fin r) ℂ)
    (y : Fin n → ℝ) :
    ∫ g, windowTest n K B φ L y g ∂gaussianMarkLaw n r =
      (expSumConst n K B)⁻¹ * ∏ m, markAverageL r φ L (y m) := by
  unfold windowTest gaussianMarkLaw markAverageL
  rw [integral_const_mul]
  congr 1
  have h : ∀ g : MarkArray n r, Real.exp (-∑ m, φ (y m, L *ᵥ g m)) =
      ∏ m, Real.exp (-φ (y m, L *ᵥ g m)) := fun g => by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [h]
  exact integral_fintype_prod_eq_prod (fun m w => Real.exp (-φ (y m, L *ᵥ w)))

/-!
## The integrands on `{window = S}`
-/

/-- On `{window = S}`, `exp(-Σ_ℓ φ(x_ℓ, z_ℓ(V₀T)))` is `M` times the window test at
`(x_{ι m})_m` and `(z_{ι m}(V₀))_m`, `L = T^*`. -/
theorem exp_marked_eq_windowTest {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (B : ℝ) (hB0 : 0 ≤ B) (ρ E : ℝ) (V₀ : Matrix (Fin N) (Fin r) ℂ)
    (T : Matrix (Fin r) (Fin r) ℂ) (K' : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (hS : windowSet ρ E R K' = S) (θ : Fin N → ℂ) :
    Real.exp (-∑ ℓ : Fin N, φ ((N : ℝ) * ρ * (freshEigenvalue K' ℓ - E),
        relativeMark (V₀ * T) K' θ ℓ)) =
      expSumConst S.card K B * windowTest S.card K B φ Tᴴ
        (fun m => (N : ℝ) * ρ * (freshEigenvalue K' (S.orderEmbOfFin rfl m) - E))
        (fun m => relativeMark V₀ K' θ (S.orderEmbOfFin rfl m)) := by
  have hK : 0 ≤ K := (hφ.c2 0).nonneg
  have hM : expSumConst S.card K B ≠ 0 := by unfold expSumConst; positivity
  unfold windowTest
  rw [← mul_assoc, mul_inv_cancel₀ hM, one_mul]
  congr 2
  simp_rw [relativeMark_mul]
  rw [← sum_orderEmbOfFin S (fun ℓ => φ ((N : ℝ) * ρ * (freshEigenvalue K' ℓ - E),
    Tᴴ *ᵥ relativeMark V₀ K' θ ℓ))]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun ℓ _ hℓ => ?_
  apply hφ.support
  rw [← hS] at hℓ
  simpa [windowSet] using hℓ

theorem gaussIntegrand_eq_windowTest {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (B : ℝ) (hB0 : 0 ≤ B) (ρ E : ℝ)
    (L : Matrix (Fin r) (Fin r) ℂ) (K' : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (hS : windowSet ρ E R K' = S) :
    gaussIntegrand ρ E φ L K' =
      expSumConst S.card K B * ∫ g, windowTest S.card K B φ L
        (fun m => (N : ℝ) * ρ * (freshEigenvalue K' (S.orderEmbOfFin rfl m) - E)) g
        ∂gaussianMarkLaw S.card r := by
  have hK : 0 ≤ K := (hφ.c2 0).nonneg
  have hM : expSumConst S.card K B ≠ 0 := by unfold expSumConst; positivity
  rw [integral_windowTest_gauss, ← mul_assoc, mul_inv_cancel₀ hM, one_mul, gaussIntegrand,
    ← prod_orderEmbOfFin S (fun ℓ => markAverageL r φ L ((N : ℝ) * ρ * (freshEigenvalue K' ℓ - E)))]
  symm
  refine Finset.prod_subset (Finset.subset_univ _) fun ℓ _ hℓ => ?_
  apply markAverageL_eq_one hφ
  rw [← hS] at hℓ
  simpa [windowSet] using hℓ

end BlockBand.Critical.RelativeVectors
