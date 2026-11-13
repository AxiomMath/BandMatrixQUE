module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.GenBound
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.SimpleSet
public import BlockBand.Critical.RelativeVectors.Angular.ConcreteFlow

/-!
# The space-time test for the relative Duhamel identity

Fix the data of `RelativeDuhamelStatement`: a reference flow `(Paux, 𝓜, Ξ)` of every path with
simple spectrum on `[a, c]`, a test `h` and its backward function `g = backwardFn Paux 𝓜 Ξ c h`.
On the concrete flow (`FlowSample N`, start `flowInit F`, Brownian motion `flowBM N`, start time
`0`, horizon `T = c - a`), with `ω̂ = hermProj ω` and `S₀ = simpleRatSet F a c`:

* `clampTime a c v = max a (min (a + v) c)`: the flow time `a + v` clamped to `[a, c]` (it is
  `a + v` on `[0, T]`; the clamp makes `measurable` and `phase` hold for every `v : ℝ`, as
  `IsSpaceTimeAngularTest` requires);
* `switchTest`: `h̃(ω, v) = g(ω̂, clampTime v)` if `ω̂ ∈ S₀`, else `h(ω̂)`;
* `switchTestDeriv`: `h̃_t(ω, v, z) = -𝓛_ref(clampTime v) g(ω̂, clampTime v)(z)` if `ω̂ ∈ S₀`,
  else `0`.

`isSpaceTimeAngularTest_switchTest`: for every `n > 0`, `(h̃, h̃_t)` is an
`IsSpaceTimeAngularTest` for `eigenPathSigma (flowInit F) (flowBM N) 0`, the gap stop
`gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n` and the horizon `(c - a).toNNReal`.
Measurability goes through `measurable_switch_derivs` (with `π = hermProj`) and
`comap_hermProj_pathSigma_le`; regularity and the time derivative come from
`IsReferenceFlow.backward` at `ω̂` (simple spectrum by `hermProj_mem_simpleRatSet_iff`); the time
bound from `gap_gt_of_lt_gapStop` and `abs_referenceArrayGenerator_le`.

All `if`s on `ω̂ ∈ S₀` use the classical decidability instance, the same one that is passed to
`measurable_switch_derivs`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel

open MeasureTheory Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Critical.RelativeVectors
open BlockBand.Palm.MomentFlow
open scoped NNReal

attribute [local instance] Classical.propDecidable

variable {N r : ℕ}

/-!
## The clamped time
-/

/-- Flow time `a + v` clamped to `[a, c]`. -/
def clampTime (a c v : ℝ) : ℝ := max a (min (a + v) c)

/-- The clamped time lies in `[a, c]`. -/
theorem clampTime_mem {a c : ℝ} (hac : a ≤ c) (v : ℝ) : clampTime a c v ∈ Icc a c :=
  ⟨le_max_left _ _, max_le hac (min_le_right _ _)⟩

/-- On `[0, c - a]` the clamped time is `a + v`. -/
theorem clampTime_eq {a c v : ℝ} (hv0 : 0 ≤ v) (hvT : v ≤ c - a) : clampTime a c v = a + v := by
  unfold clampTime
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/-- The clamped time is continuous. -/
theorem continuous_clampTime (a c : ℝ) : Continuous (clampTime a c) :=
  continuous_const.max ((continuous_const.add continuous_id).min continuous_const)

/-- Composition with the clamped time maps `[0, c - a] × E` into `[a, c] × E`. -/
theorem continuousOn_comp_clampTime {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {a c : ℝ} (hac : a ≤ c) {f : ℝ × E → X} (hf : ContinuousOn f (Icc a c ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × E => f (clampTime a c p.1, p.2)) (Icc (0 : ℝ) (c - a) ×ˢ univ) :=
  hf.comp (((continuous_clampTime a c).comp continuous_fst).prodMk continuous_snd).continuousOn
    fun p _ => ⟨clampTime_mem hac p.1, mem_univ _⟩

/-- Composition with the clamped time maps `(0, c - a) × E` into `(a, c) × E`. -/
theorem continuousOn_comp_clampTime_Ioo {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {a c : ℝ} {f : ℝ × E → X} (hf : ContinuousOn f (Ioo a c ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × E => f (clampTime a c p.1, p.2)) (Ioo (0 : ℝ) (c - a) ×ˢ univ) := by
  refine hf.comp (((continuous_clampTime a c).comp continuous_fst).prodMk
    continuous_snd).continuousOn fun p hp => ⟨?_, mem_univ _⟩
  show clampTime a c p.1 ∈ Ioo a c
  rw [clampTime_eq hp.1.1.le hp.1.2.le]
  exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩

/-!
## The switched test and its time derivative
-/

/-- **The space-time test**: `h̃(ω, v) = g(ω̂, clampTime v)` if `ω̂ = hermProj ω` lies in the
switch set `simpleRatSet F a c`, else `h(ω̂)`. -/
def switchTest {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (F : Matrix (Fin N) (Fin N) ℂ)
    (a c : ℝ) (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ) (ω : FlowSample N) (v : ℝ) :
    (Fin N → Fin r → ℂ) → ℝ :=
  if hermProj ω ∈ simpleRatSet F a c then
    backwardFn Paux 𝓜 Ξ c h (hermProj ω) (clampTime a c v)
  else h (hermProj ω)

/-- **Its time derivative**: `h̃_t(ω, v, z) = -𝓛_ref(clampTime v) g(ω̂, clampTime v)(z)` on the
switch set, `0` off it. -/
def switchTestDeriv {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (F : Matrix (Fin N) (Fin N) ℂ)
    (a c b₀ : ℝ) (ℓ : ℕ) (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ) (ω : FlowSample N) (v : ℝ)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  if hermProj ω ∈ simpleRatSet F a c then
    -referenceArrayGenerator F a b₀ (hermProj ω) ℓ (clampTime a c v)
      (backwardFn Paux 𝓜 Ξ c h (hermProj ω) (clampTime a c v)) z
  else 0

section Switch

variable {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
  (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
  (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) (F : Matrix (Fin N) (Fin N) ℂ)
  (a c b₀ : ℝ) (ℓ : ℕ) (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)

/-- `h̃` on the switch set. -/
theorem switchTest_of_mem {ω : FlowSample N} (hω : hermProj ω ∈ simpleRatSet F a c) (v : ℝ) :
    switchTest Paux 𝓜 Ξ F a c h ω v = backwardFn Paux 𝓜 Ξ c h (hermProj ω) (clampTime a c v) :=
  ite_eq_left hω

/-- `h̃` off the switch set. -/
theorem switchTest_of_not_mem {ω : FlowSample N} (hω : hermProj ω ∉ simpleRatSet F a c)
    (v : ℝ) : switchTest Paux 𝓜 Ξ F a c h ω v = h (hermProj ω) :=
  ite_eq_right hω

/-- `h̃_t` on the switch set. -/
theorem switchTestDeriv_of_mem {ω : FlowSample N} (hω : hermProj ω ∈ simpleRatSet F a c)
    (v : ℝ) (z : Fin N → Fin r → ℂ) :
    switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω v z =
      -referenceArrayGenerator F a b₀ (hermProj ω) ℓ (clampTime a c v)
        (backwardFn Paux 𝓜 Ξ c h (hermProj ω) (clampTime a c v)) z :=
  ite_eq_left hω

/-- `h̃_t` off the switch set. -/
theorem switchTestDeriv_of_not_mem {ω : FlowSample N} (hω : hermProj ω ∉ simpleRatSet F a c)
    (v : ℝ) (z : Fin N → Fin r → ℂ) : switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω v z = 0 :=
  ite_eq_right hω

/-- `h̃_t` is the negated reference generator applied to `h̃` itself on the switch set. -/
theorem switchTestDeriv_eq_ite (ω : FlowSample N) (v : ℝ) (z : Fin N → Fin r → ℂ) :
    switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω v z =
      if hermProj ω ∈ simpleRatSet F a c then
        -referenceArrayGenerator F a b₀ (hermProj ω) ℓ (clampTime a c v)
          (switchTest Paux 𝓜 Ξ F a c h ω v) z
      else 0 := by
  by_cases hω : hermProj ω ∈ simpleRatSet F a c
  · rw [ite_eq_left hω, switchTestDeriv_of_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω,
      switchTest_of_mem Paux 𝓜 Ξ F a c h hω]
  · rw [ite_eq_right hω, switchTestDeriv_of_not_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω]

end Switch

/-!
## The backward equation in `backwardFn` form
-/

/-- `IsReferenceFlow.backward` for `f = h ω`, stated with `backwardFn`. -/
theorem refFlow_backward {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux}
    {𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ}
    {Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ} {F : Matrix (Fin N) (Fin N) ℂ}
    {a c b₀ : ℝ} {ℓ : ℕ} {h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ} {ω : FlowSample N}
    (hRF : IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω)) {C : ℝ}
    (hC : IsArrayC2Bounded C (h ω)) :
    (∀ s ∈ Icc a c, IsArrayC2Bounded C (backwardFn Paux 𝓜 Ξ c h ω s)) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => backwardFn Paux 𝓜 Ξ c h ω p.1 p.2)
      (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (backwardFn Paux 𝓜 Ξ c h ω p.1) p.2)
      (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
      fderiv ℝ (fderiv ℝ (backwardFn Paux 𝓜 Ξ c h ω p.1)) p.2) (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
      referenceArrayGenerator F a b₀ ω ℓ p.1 (backwardFn Paux 𝓜 Ξ c h ω p.1) p.2)
      (Ioo a c ×ˢ univ) ∧
    ∀ z, ∀ s ∈ Ioo a c, HasDerivAt (fun s' => backwardFn Paux 𝓜 Ξ c h ω s' z)
      (-(referenceArrayGenerator F a b₀ ω ℓ s (backwardFn Paux 𝓜 Ξ c h ω s) z)) s :=
  hRF.backward C (h ω) hC

/-!
## Measurability of the reference generator in the path
-/

/-- The couplings `c_ij(σ)` of `π ω`, `σ ∈ [a, c]`, are measurable when `π` is measurable into
`pathSigma F a a c`. -/
theorem measurable_flowRate_comp {α : Type*} {m : MeasurableSpace α}
    (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) {π : α → FlowSample N}
    (hπ : @Measurable α (FlowSample N) m (pathSigma F a a c) π) {σ : ℝ} (hσ : σ ∈ Icc a c)
    (i j : Fin N) : Measurable fun ω => flowRate F a (π ω) σ i j := by
  have hi := (measurable_flowEigenvalue_pathSigma F a a c hσ i).comp hπ
  have hj := (measurable_flowEigenvalue_pathSigma F a a c hσ j).comp hπ
  unfold flowRate
  exact (measurable_const.mul ((hi.sub hj).pow_const 2)).inv

/-- **The reference generator is measurable in the path.** If `π` is measurable into
`pathSigma F a a c`, `σ ∈ [a, c]`, and the first and second directional derivatives of `K ω` at
every point are measurable in `ω`, then `ω ↦ 𝓛_ref(σ)[π ω] (K ω)(z)` is measurable. -/
theorem measurable_referenceArrayGenerator_comp {α : Type*} {m : MeasurableSpace α}
    (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) {π : α → FlowSample N}
    (hπ : @Measurable α (FlowSample N) m (pathSigma F a a c) π) {σ : ℝ} (hσ : σ ∈ Icc a c)
    (K : α → (Fin N → Fin r → ℂ) → ℝ)
    (hK : ∀ z v w : Fin N → Fin r → ℂ, Measurable (fun ω => fderiv ℝ (K ω) z v) ∧
      Measurable (fun ω => fderiv ℝ (fderiv ℝ (K ω)) z v w))
    (z : Fin N → Fin r → ℂ) :
    Measurable fun ω => referenceArrayGenerator F a b₀ (π ω) ℓ σ (K ω) z := by
  have hrate := measurable_flowRate_comp F a c hπ hσ
  have hdamp : ∀ i, Measurable fun ω => refDamping F a b₀ (π ω) ℓ σ i := by
    intro i
    unfold refDamping longCoupling
    exact (Finset.measurable_sum _ fun k _ => hrate i k).max measurable_const
  have hfs : ∀ W : (Fin N → Fin r → ℂ) → (Fin N → Fin r → ℂ),
      Measurable fun ω => fieldSq W (K ω) z := fun W =>
    (hK z (W z) (W z)).2.add (hK z (W (W z)) 0).1
  unfold referenceArrayGenerator
  refine (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => (hrate i j).mul ((hfs _).add (hfs _)))).add
    (Finset.measurable_sum _ fun i _ => (hdamp i).mul ?_)
  exact (measurable_const.mul (hK z _ 0).1).add (measurable_const.mul
    (Finset.measurable_sum _ fun q _ => (hK z _ _).2.add (hK z _ _).2))

/-!
## The space-time test
-/

/-- The constant of the reference-generator bound is nonnegative. -/
theorem refGenConst_nonneg {C : ℝ} (hC : 0 ≤ C) (n : ℕ) (b₀ : ℝ) (ℓ : ℕ) :
    0 ≤ refGenConst N r C n b₀ ℓ := by
  have hM := supC2Const_nonneg (N := N) (r := r) hC
  have hmax : 0 ≤ max ((N : ℝ) * (n : ℝ) ^ 2) (b₀ * N / ℓ) := le_max_of_le_left (by positivity)
  unfold refGenConst
  positivity

/-- The measurable-space inclusion used for the angular martingale test: `hermProj⁻¹(pathSigma F a a c)`
is contained in the eigenvalue-path σ-algebra of the concrete flow at start time `0`. -/
theorem comap_hermProj_le_eigenPathSigma_zero (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) :
    MeasurableSpace.comap hermProj (pathSigma F a a c) ≤
      eigenPathSigma (flowInit F) (flowBM N) 0 := by
  have := Angular.comap_hermProj_pathSigma_le F (le_refl a) c
  rwa [sub_self, Real.toNNReal_zero] at this

/-- Every `h ω` is Borel measurable (a section of the jointly measurable `h`). -/
theorem measurable_section {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ}
    {h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ}
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h)) (ω : FlowSample N) : Measurable (h ω) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  exact hh.comp (measurable_const.prodMk measurable_id)

section Main

variable {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
  (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
  (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) {F : Matrix (Fin N) (Fin N) ℂ}
  {a c : ℝ} (b₀ : ℝ) (ℓ : ℕ) {C : ℝ} (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ)

/-- On the switch set, `hermProj ω` carries a reference flow. -/
theorem refFlow_of_switch (hF : F.IsHermitian) (hac : a ≤ c)
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    {ω : FlowSample N} (hω : hermProj ω ∈ simpleRatSet F a c) :
    IsReferenceFlow F a c b₀ ℓ (hermProj ω) Paux (𝓜 (hermProj ω)) (Ξ (hermProj ω)) :=
  hRF _ ((hermProj_mem_simpleRatSet_iff hF hac ω).1 hω)

/-- Every slice `h̃(ω, v)` is Euclidean bounded-`C²` with the constant `C` of `h`. -/
theorem switchTest_c2 (hF : F.IsHermitian) (hac : a ≤ c)
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω))
    (ω : FlowSample N) (v : ℝ) : IsArrayC2Bounded C (switchTest Paux 𝓜 Ξ F a c h ω v) := by
  by_cases hω : hermProj ω ∈ simpleRatSet F a c
  · rw [switchTest_of_mem Paux 𝓜 Ξ F a c h hω]
    exact (refFlow_backward (refFlow_of_switch Paux 𝓜 Ξ b₀ ℓ hF hac hRF hω)
      (hC _).1).1 _ (clampTime_mem hac v)
  · rw [switchTest_of_not_mem Paux 𝓜 Ξ F a c h hω]
    exact (hC _).1

/-- **Measurability field.** `ω ↦ h̃(ω, v, z)` and `ω ↦ h̃_t(ω, v, z)` are measurable for
`eigenPathSigma (flowInit F) (flowBM N) 0`. -/
theorem measurable_switchTest [IsProbabilityMeasure Paux] (hF : F.IsHermitian) (hac : a ≤ c)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω))
    (v : ℝ) (z : Fin N → Fin r → ℂ) :
    Measurable[eigenPathSigma (flowInit F) (flowBM N) 0]
        (fun ω => switchTest Paux 𝓜 Ξ F a c h ω v z) ∧
      Measurable[eigenPathSigma (flowInit F) (flowBM N) 0]
        (fun ω => switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω v z) := by
  set m : MeasurableSpace (FlowSample N) := MeasurableSpace.comap hermProj (pathSigma F a a c)
  have hle : m ≤ eigenPathSigma (flowInit F) (flowBM N) 0 :=
    comap_hermProj_le_eigenPathSigma_zero F a c
  have hπ : @Measurable (FlowSample N) (FlowSample N) m (pathSigma F a a c) hermProj :=
    comap_measurable hermProj
  have hS := measurableSet_simpleRatSet F hac
  have hs := clampTime_mem hac v
  have hgS : ∀ ω, hermProj ω ∈ simpleRatSet F a c →
      ContDiff ℝ 2 (backwardFn Paux 𝓜 Ξ c h (hermProj ω) (clampTime a c v)) := fun ω hω =>
    ((refFlow_backward (refFlow_of_switch Paux 𝓜 Ξ b₀ ℓ hF hac hRF hω) (hC _).1).1 _ hs).contDiff
  have key := measurable_switch_derivs Paux 𝓜 Ξ F a c hMΞ h hh m hermProj hπ
    (simpleRatSet F a c) hS (clampTime a c v) hgS (fun ω => (hC _).1.contDiff)
  have hK : ∀ z' v' w' : Fin N → Fin r → ℂ,
      Measurable[m] (fun ω => fderiv ℝ (switchTest Paux 𝓜 Ξ F a c h ω v) z' v') ∧
        Measurable[m] (fun ω => fderiv ℝ (fderiv ℝ (switchTest Paux 𝓜 Ξ F a c h ω v)) z' v' w') :=
    fun z' v' w' => ⟨(key z' v' w').2.1, (key z' v' w').2.2⟩
  refine ⟨((key z 0 0).1).mono hle le_rfl, ?_⟩
  have e : (fun ω => switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω v z) = fun ω =>
      if hermProj ω ∈ simpleRatSet F a c then
        -referenceArrayGenerator F a b₀ (hermProj ω) ℓ (clampTime a c v)
          (switchTest Paux 𝓜 Ξ F a c h ω v) z
      else 0 := by
    funext ω
    exact switchTestDeriv_eq_ite Paux 𝓜 Ξ F a c b₀ ℓ h ω v z
  rw [e]
  refine Measurable.mono ?_ hle le_rfl
  exact Measurable.ite (hπ hS) (measurable_referenceArrayGenerator_comp F a c b₀ ℓ hπ hs
    (fun ω => switchTest Paux 𝓜 Ξ F a c h ω v) hK z).neg measurable_const

/-- **Phase field.** Every slice `h̃(ω, v)` is label-phase invariant (for every `v : ℝ`). -/
theorem phase_switchTest (hF : F.IsHermitian) (hac : a ≤ c)
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω))
    (ω : FlowSample N) (v : ℝ) : IsLabelPhaseInvariant (switchTest Paux 𝓜 Ξ F a c h ω v) := by
  by_cases hω : hermProj ω ∈ simpleRatSet F a c
  · rw [switchTest_of_mem Paux 𝓜 Ξ F a c h hω]
    exact backwardFn_phaseInvariant Paux 𝓜 Ξ h (hermProj ω)
      (refFlow_of_switch Paux 𝓜 Ξ b₀ ℓ hF hac hRF hω) (hC _).2 (measurable_section hh _)
      (clampTime_mem hac v)
  · rw [switchTest_of_not_mem Paux 𝓜 Ξ F a c h hω]
    exact (hC _).2

/-- **Time-derivative field.** On `(0, c - a)`, `∂_v h̃(ω, v, z) = h̃_t(ω, v, z)`. -/
theorem hasDerivAt_switchTest (hF : F.IsHermitian) (hac : a ≤ c)
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω))
    (ω : FlowSample N) (z : Fin N → Fin r → ℂ) {v : ℝ} (hv : v ∈ Ioo 0 (c - a)) :
    HasDerivAt (fun v' => switchTest Paux 𝓜 Ξ F a c h ω v' z)
      (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω v z) v := by
  by_cases hω : hermProj ω ∈ simpleRatSet F a c
  · rw [switchTestDeriv_of_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω, clampTime_eq hv.1.le hv.2.le]
    simp only [switchTest_of_mem Paux 𝓜 Ξ F a c h hω]
    have hd := (refFlow_backward (refFlow_of_switch Paux 𝓜 Ξ b₀ ℓ hF hac hRF hω)
      (hC _).1).2.2.2.2.2 z (a + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine (hd.comp_const_add a v).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with v' hv'
    rw [clampTime_eq hv'.1.le hv'.2.le]
  · simp only [switchTest_of_not_mem Paux 𝓜 Ξ F a c h hω,
      switchTestDeriv_of_not_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω]
    exact hasDerivAt_const v _

/-- **Continuity field.** `h̃`, `D_z h̃`, `D_z² h̃` are jointly continuous on `[0, c - a] × ℂ^{N×r}`
and `h̃_t` on `(0, c - a) × ℂ^{N×r}`. -/
theorem continuousOn_switchTest (hF : F.IsHermitian) (hac : a ≤ c)
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω)) (ω : FlowSample N) :
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => switchTest Paux 𝓜 Ξ F a c h ω p.1 p.2)
      (Icc (0 : ℝ) (c - a) ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
      fderiv ℝ (switchTest Paux 𝓜 Ξ F a c h ω p.1) p.2) (Icc (0 : ℝ) (c - a) ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
      fderiv ℝ (fderiv ℝ (switchTest Paux 𝓜 Ξ F a c h ω p.1)) p.2)
      (Icc (0 : ℝ) (c - a) ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
      switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω p.1 p.2) (Ioo (0 : ℝ) (c - a) ×ˢ univ) := by
  by_cases hω : hermProj ω ∈ simpleRatSet F a c
  · obtain ⟨-, h1, h2, h3, h4, -⟩ :=
      refFlow_backward (refFlow_of_switch Paux 𝓜 Ξ b₀ ℓ hF hac hRF hω) (hC (hermProj ω)).1
    simp only [switchTest_of_mem Paux 𝓜 Ξ F a c h hω,
      switchTestDeriv_of_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω]
    refine ⟨continuousOn_comp_clampTime hac
        (f := fun p => backwardFn Paux 𝓜 Ξ c h (hermProj ω) p.1 p.2) h1,
      continuousOn_comp_clampTime hac
        (f := fun p => fderiv ℝ (backwardFn Paux 𝓜 Ξ c h (hermProj ω) p.1) p.2) h2,
      continuousOn_comp_clampTime hac
        (f := fun p => fderiv ℝ (fderiv ℝ (backwardFn Paux 𝓜 Ξ c h (hermProj ω) p.1)) p.2) h3,
      ?_⟩
    exact (continuousOn_comp_clampTime_Ioo (f := fun p => referenceArrayGenerator F a b₀
      (hermProj ω) ℓ p.1 (backwardFn Paux 𝓜 Ξ c h (hermProj ω) p.1) p.2) h4).neg
  · have hcd := (hC (hermProj ω)).1.contDiff
    simp only [switchTest_of_not_mem Paux 𝓜 Ξ F a c h hω,
      switchTestDeriv_of_not_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω]
    exact ⟨(hcd.continuous.comp continuous_snd).continuousOn,
      ((hcd.continuous_fderiv (by norm_num)).comp continuous_snd).continuousOn,
      (((hcd.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).comp
        continuous_snd).continuousOn, continuousOn_const⟩

/-- **Time-bound field.** Before the gap stop `σ_n`, `|h̃_t(ω, v, z)| ≤ refGenConst (1 + ‖z‖²)`. -/
theorem time_bound_switchTest (hF : F.IsHermitian) (hac : a ≤ c)
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω)) {n : ℕ} (hn : 0 < n)
    (ω : FlowSample N) {v : ℝ} (hv : v ∈ Ioo 0 (c - a))
    (hσ : ((Real.toNNReal v : ℝ≥0) : WithTop ℝ≥0) <
      gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n ω)
    (z : Fin N → Fin r → ℂ) :
    |switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h ω v z| ≤ refGenConst N r C n b₀ ℓ * (1 + ‖z‖ ^ 2) := by
  by_cases hω : hermProj ω ∈ simpleRatSet F a c
  · rw [switchTestDeriv_of_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω, abs_neg, clampTime_eq hv.1.le hv.2.le]
    have hg := (refFlow_backward (refFlow_of_switch Paux 𝓜 Ξ b₀ ℓ hF hac hRF hω)
      (hC (hermProj ω)).1).1 (a + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine abs_referenceArrayGenerator_le hg F a b₀ (hermProj ω) ℓ (a + v) hn ?_ z
    intro i j hij
    have hH : (flowMatrix F a (hermProj ω) (a + v)).IsHermitian :=
      flowMatrix_isHermitian_of hF a (hermPart_isHermitian ω.1) _
    have hgap := Angular.gap_gt_of_lt_gapStop (fun t ω => flowInit F ω + flowBM N t ω) 0 n ω hσ
      (fun e => hij (Fin.rev_injective e))
    simp only [zero_add] at hgap
    rw [flowInit_add_flowBM F a ω, Real.coe_toNNReal v hv.1.le] at hgap
    simp only [flowEigenvalue]
    rw [freshEigenvalue_eq_dyson hH, freshEigenvalue_eq_dyson hH]
    exact hgap
  · rw [switchTestDeriv_of_not_mem Paux 𝓜 Ξ F a c b₀ ℓ h hω, abs_zero]
    exact mul_nonneg (refGenConst_nonneg (arrayC2_nonneg (hC ω).1) n b₀ ℓ) (by positivity)

/-- **The space-time test is admissible.** For every `n > 0`, `(h̃, h̃_t)` is an
`IsSpaceTimeAngularTest` for the eigenvalue-path σ-algebra `eigenPathSigma (flowInit F) (flowBM N) 0`
of the concrete flow, the gap stop `σ_n` at start time `0` and the horizon `(c - a).toNNReal`. -/
theorem isSpaceTimeAngularTest_switchTest [IsProbabilityMeasure Paux] (hF : F.IsHermitian) (hac : a ≤ c)
    (hMΞ : ∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2))
    (hRF : ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω))
    (hh : Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h))
    (hC : ∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω)) {n : ℕ} (hn : 0 < n) :
    IsSpaceTimeAngularTest (eigenPathSigma (flowInit F) (flowBM N) 0)
      (gapStop N (fun t ω => flowInit F ω + flowBM N t ω) 0 n) (Real.toNNReal (c - a))
      (switchTest Paux 𝓜 Ξ F a c h) (switchTestDeriv Paux 𝓜 Ξ F a c b₀ ℓ h) := by
  have hT : ((Real.toNNReal (c - a) : ℝ≥0) : ℝ) = c - a := Real.coe_toNNReal _ (sub_nonneg.2 hac)
  refine ⟨fun v z => measurable_switchTest Paux 𝓜 Ξ b₀ ℓ h hF hac hMΞ hRF hh hC v z,
    fun ω v => phase_switchTest Paux 𝓜 Ξ b₀ ℓ h hF hac hRF hh hC ω v,
    fun ω v _ => (switchTest_c2 Paux 𝓜 Ξ b₀ ℓ h hF hac hRF hC ω v).contDiff,
    fun ω z v hv => hasDerivAt_switchTest Paux 𝓜 Ξ b₀ ℓ h hF hac hRF hC ω z
      (by rw [hT] at hv; exact hv),
    fun ω => by rw [hT]; exact continuousOn_switchTest Paux 𝓜 Ξ b₀ ℓ h hF hac hRF hC ω,
    ⟨max C (supC2Const N r C), fun ω v _ z => ?_⟩,
    ⟨refGenConst N r C n b₀ ℓ, fun ω v hv hσ z =>
      time_bound_switchTest Paux 𝓜 Ξ b₀ ℓ h hF hac hRF hC hn ω (by rw [hT] at hv; exact hv) hσ
        z⟩⟩
  have hg := switchTest_c2 Paux 𝓜 Ξ b₀ ℓ h hF hac hRF hC ω v
  exact ⟨(arrayC2_abs_le hg z).trans (le_max_left _ _),
    (norm_fderiv_le_supC2Const hg z).trans (le_max_right _ _),
    (norm_fderiv_fderiv_le_supC2Const hg z).trans (le_max_right _ _)⟩

end Main

end BlockBand.Critical.RelativeVectors.RelativeDuhamel
