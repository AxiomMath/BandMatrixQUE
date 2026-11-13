module

public import BlockBand.Critical.RelativeVectors.GoodSample
public import BlockBand.Critical.RelativeVectors.Equilibrate
public import BlockBand.Critical.RelativeVectors.DuhamelInterface

/-!
# The comparison on a set of good paths

* `crudeTime_genDiff_le`, `crudeSample_integral_le`: on paths with the long-gap bound only
  (without the interval and distant-label bounds), the generator difference is polynomially
  bounded: the long coefficients and the Ornstein–Uhlenbeck floor are polynomially bounded on `𝓡`,
  and the true vectors are bounded by `√N‖V‖`, so the contribution on `𝒜ᶜ` is `O(N^{-D+C(A)})`.
* `equilSample_le`: the equilibration bound `|g_a(z) - ∫ f̄ dγ| ≤ e^{-b₀N(c-a)/(2ℓ)}(‖z‖₂ + √(Nr))`,
  from `reference_equilibration` (law identification `map_reference_gaussian_eq`).
* `testedTail_le_card`, `arrayNormSq_frameArray_le`: the crude row-tail and array-norm bounds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.CoarseRelative

variable {N r k : ℕ}

section Crude

variable {F : Matrix (Fin N) (Fin N) ℂ} {a c b₀ : ℝ} {ℓ : ℕ} {ω : FlowSample N}
  {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux} [IsProbabilityMeasure Paux]
  {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}

theorem testedTail_le_card (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ) (hb₀ : 0 ≤ b₀)
    {s : ℝ} (hs : s ∈ Icc a c) (ι : Fin k → Fin N) (J : Finset (Fin N)) :
    testedTail Paux ι (𝓜 s c) J ≤ k := by
  unfold testedTail
  calc ∑ m, ∫ ω', rowTail (𝓜 s c ω') J (ι m) ∂Paux ≤ ∑ _m : Fin k, (1 : ℝ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        calc ∫ ω', rowTail (𝓜 s c ω') J (ι m) ∂Paux ≤ ∫ _ω', (1 : ℝ) ∂Paux := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ =>
                rowTail_nonneg _ _ _) (integrable_const _) (Filter.Eventually.of_forall fun ω' => ?_)
              refine le_trans (Finset.sum_le_sum fun j _ => ?_)
                (rows_reference hR hb₀ hs.1 hs.2 le_rfl ω' (ι m))
              split_ifs
              · positivity
              · exact le_rfl
          _ = 1 := by simp
    _ = k := by simp

/-- **The crude one-time bound** (long gaps only). -/
theorem crudeTime_genDiff_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1) {a : ℝ}
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {c₁ b₀ : ℝ} (hc₁ : 0 < c₁) (hb₀ : 0 < b₀) {ω : FlowSample N}
    {σ : ℝ} (hσ : σ ∈ Icc a c)
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux} [IsProbabilityMeasure Paux]
    {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}
    (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    (ι : Fin k → Fin N) {f : MarkArray k r → ℝ} (hf : IsC2Bounded 1 f) :
    |complexAngularGenerator N r (flowEigenvalue F a ω σ)
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 σ c ω') z + Ξ σ c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω σ)) -
      referenceArrayGenerator F a b₀ ω ℓ σ
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 σ c ω') z + Ξ σ c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω σ))| ≤
      tbQ0 N r k 0 0 (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2))
          (b₀ * N / ℓ) 1 +
        tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * frameZsq N A c s₀ v₀ + 1))
            (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) 1 * k := by
  set z := frameArray V (flowMatrix F a ω σ) with hz
  set Zsq := frameZsq N A c s₀ v₀ with hZsq
  set cbar : ℝ := (N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) with hcbar
  have hZ0 : 0 ≤ Zsq := frameZsq_nonneg hK
  have hc0 : 0 ≤ cbar := by positivity
  have hS := testedSetting_reference hR hb₀.le hσ ι hf
  have hg := contDiff_backward hR hσ ι hf
  have hinv := hinv_reference hR hσ ι hf
  have hrow := rows_reference hR hb₀.le hσ.1 hσ.2 le_rfl
  have hc : ∀ i j, ℓ ≤ labelDist i j → |dysonCoupling N (flowEigenvalue F a ω σ) i j| ≤ cbar :=
    abs_dysonCoupling_le_long hc₁ hℓ hgap
  have hzZ : ∀ i q, ‖z i q‖ ^ 2 ≤ Zsq := fun i q =>
    frameArray_entry_sq_le_Z hN hK hC hV _ i q
  have hz' : ∀ i q, ‖z i q‖ ≤ Real.sqrt Zsq := fun i q => Real.le_sqrt_of_sq_le (hzZ i q)
  have h := genDiff_rowTail_le ι hS hg hinv hrow F a b₀ ω hℓ σ z ∅ le_rfl (Real.sqrt_nonneg _)
    (fun i hi => absurd hi (Finset.notMem_empty i)) hz' hc0 hc le_rfl
    (fun i hi => absurd hi (Finset.notMem_empty i))
    (fun i _ p => exteriorX_le hc0 hZ0 hc hzZ i p) (by positivity)
    (fun i hi => absurd hi (Finset.notMem_empty i)) (abs_refDamping_sub_le F a hb₀.le ω ℓ σ)
    one_pos
  have hT := testedTail_le_card hR hb₀.le hσ ι ∅
  have hQ1 : 0 ≤ tbQ1 N r k (cbar * N * (r * Zsq + 1)) (Real.sqrt Zsq) cbar (b₀ * N / ℓ) 1 := by
    unfold tbQ1
    have := Real.sqrt_nonneg Zsq
    positivity
  refine h.trans ?_
  have e : (1 * (2 * (r : ℝ) ^ 2 * k * 0 + ((k : ℝ) * r) ^ 2 * (0 * (Real.sqrt 2 * cbar))) +
          1 * (Real.sqrt Zsq * Real.sqrt Zsq * (cbar * N)) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * 1 +
          b₀ * N / ℓ * (1 / 2 * 1 * Real.sqrt Zsq) * ((N : ℝ) * 1 / 2)) =
        tbQ0 N r k 0 0 (Real.sqrt Zsq) cbar (b₀ * N / ℓ) 1 := by
    unfold tbQ0; ring
  have e2 : (1 * (2 * (r : ℝ) ^ 2 * (cbar * N * (r * Zsq + 1))) + b₀ * N / ℓ * (1 / 2 * r * 1) +
          1 * (Real.sqrt Zsq * Real.sqrt Zsq * (cbar * N)) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / 1 +
          b₀ * N / ℓ * (1 / 2 * 1 * Real.sqrt Zsq) / (2 * 1)) =
        tbQ1 N r k (cbar * N * (r * Zsq + 1)) (Real.sqrt Zsq) cbar (b₀ * N / ℓ) 1 := by
    unfold tbQ1; ring
  rw [e, e2]
  gcongr

/-- **The crude time integral** (long gaps on `[a, c]` only). -/
theorem crudeSample_integral_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1) {a : ℝ} (hac : a ≤ c)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {c₁ b₀ : ℝ} (hc₁ : 0 < c₁) (hb₀ : 0 < b₀) {ω : FlowSample N}
    (hgap : ∀ σ ∈ Icc a c, ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux} [IsProbabilityMeasure Paux]
    {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}
    (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    (ι : Fin k → Fin N) {f : MarkArray k r → ℝ} (hf : IsC2Bounded 1 f) :
    ∫ s in Ioc a c, |complexAngularGenerator N r (flowEigenvalue F a ω s)
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s)) -
      referenceArrayGenerator F a b₀ ω ℓ s
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s))| ≤
      (c - a) * (tbQ0 N r k 0 0 (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2))
          (b₀ * N / ℓ) 1 +
        tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * frameZsq N A c s₀ v₀ + 1))
            (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) 1 * k) := by
  set Q := tbQ0 N r k 0 0 (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2))
          (b₀ * N / ℓ) 1 +
        tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * frameZsq N A c s₀ v₀ + 1))
            (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) 1 * k
  have hpt : ∀ s ∈ Ioc a c, |complexAngularGenerator N r (flowEigenvalue F a ω s)
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s)) -
      referenceArrayGenerator F a b₀ ω ℓ s
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s))| ≤ Q := fun s hs =>
    crudeTime_genDiff_le hN hK hC hV hℓ hc₁ hb₀ (Ioc_subset_Icc_self hs)
      (hgap s (Ioc_subset_Icc_self hs)) hR ι hf
  calc _ ≤ ∫ _s in Ioc a c, Q :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrableOn_const (by simp))
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt))
    _ = (c - a) * Q := by
        rw [setIntegral_const]; simp [Real.volume_real_Ioc_of_le hac]

end Crude

/-!
## Equilibration at one sample
-/

theorem arrayNormSq_frameArray_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1)
    (K : Matrix (Fin N) (Fin N) ℂ) :
    arrayNormSq (frameArray V K) ≤ N * r * frameZsq N A c s₀ v₀ := by
  unfold arrayNormSq
  calc ∑ i, ∑ q, ‖frameArray V K i q‖ ^ 2 ≤ ∑ _i : Fin N, ∑ _q : Fin r, frameZsq N A c s₀ v₀ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun q _ =>
          frameArray_entry_sq_le_Z hN hK hC hV K i q
    _ = N * r * frameZsq N A c s₀ v₀ := by simp; ring

/-- **Equilibration at one sample**: the backward function at the start time is within
`e^{-b₀N(c-a)/(2ℓ)}(‖z‖₂ + √(Nr))` of the Gaussian average of the test. -/
theorem equilSample_le {F : Matrix (Fin N) (Fin N) ℂ} {a c b₀ : ℝ} {ℓ : ℕ} {ω : FlowSample N}
    (hac : a ≤ c) {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux}
    [IsProbabilityMeasure Paux]
    {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}
    (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    {h : (Fin N → Fin r → ℂ) → ℝ} (hh : IsArrayC2Bounded 1 h) (z : Fin N → Fin r → ℂ) :
    |∫ ω', h (arrayMul (𝓜 a c ω') z + Ξ a c ω') ∂Paux - ∫ g, h g ∂gaussianMarkLaw N r| ≤
      Real.exp (-(b₀ * N * (c - a) / (2 * ℓ))) *
        (Real.sqrt (arrayNormSq z) + Real.sqrt ((N : ℝ) * r)) := by
  have hE := reference_equilibration Paux (𝓜 a c) (Ξ a c) (hR.measurable a c).1
    (hR.measurable a c).2 (hR.covariance a c le_rfl hac le_rfl) (Real.exp_pos _).le
    (hR.contraction a c le_rfl hac le_rfl) h hh.contDiff.continuous hh.bound zero_le_one
    (fun x y => lipschitz_of_isArrayC2Bounded hh x y) z
  rw [one_mul] at hE
  exact hE

end BlockBand.Critical.RelativeVectors
