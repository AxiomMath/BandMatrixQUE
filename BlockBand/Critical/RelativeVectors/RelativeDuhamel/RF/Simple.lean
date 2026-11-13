module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.SimpleSet
public import BlockBand.Palm.RelativeLocalizationBridgeRates

/-!
# Reference flow jointly measurable in the path: the simple-spectrum paths

* `strictMono_iff_mem_simpleRatSet`: for Hermitian `F`, `a ≤ c` and every flow sample `ω`, the
  spectrum of the flow is simple on `[a, c]` iff `ω ∈ simpleRatSet F a c`. For Hermitian `ω.1`
  this is `mem_simpleRatSet_iff`. For non-Hermitian `ω.1` the flow matrix is never Hermitian, so
  every ordered eigenvalue is `0` (`rawIncreasingEigenvalue`): if `N ≥ 2` both sides fail; if
  `N ≤ 1` both sides hold (no two distinct labels).
* `continuousOn_shortRate_of_mem`, `continuousOn_refDamping_of_mem`: on `simpleRatSet F a c` the
  coefficients `shortRate`, `refDamping` are continuous on `[a, c]` (constant when `N ≤ 1`).
* `measurable_shortRate_pathSigma`, `measurable_refDamping_pathSigma`: for `x ∈ [a, c]`, each
  coefficient at time `x` is `pathSigma F a a c`-measurable in `ω`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow (pathSigma measurable_flowEigenvalue_pathSigma
  hermitianBrownian_isHermitian)
open BlockBand.Palm.RelativeLocalization.StochasticBridge

variable {N : ℕ}

/-- If some flow matrix `H_σ = F + ω.1 + B(σ - a)` is Hermitian (with `F` Hermitian), then so
is `ω.1`. -/
theorem isHermitian_fst_of_flowMatrix {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a σ : ℝ} {ω : FlowSample N} (h : (flowMatrix F a ω σ).IsHermitian) : ω.1.IsHermitian := by
  have e : ω.1 = flowMatrix F a ω σ - F - hermitianBrownian ω.2 (σ - a) := by
    simp only [flowMatrix]
    abel
  rw [e]
  exact (h.sub hF).sub (hermitianBrownian_isHermitian _ _)

/-- For non-Hermitian `ω.1`, every ordered flow eigenvalue is `0`. -/
theorem flowEigenvalue_eq_zero_of_not_isHermitian {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (a : ℝ) {ω : FlowSample N} (hω : ¬ ω.1.IsHermitian) (σ : ℝ)
    (k : Fin N) : flowEigenvalue F a ω σ k = 0 := by
  have h : ¬ (flowMatrix F a ω σ).IsHermitian := fun h => hω (isHermitian_fst_of_flowMatrix hF h)
  simp only [flowEigenvalue, freshEigenvalue, BlockBand.Model.Construction.rawIncreasingEigenvalue,
    h, dite_false]

/-- For `N ≤ 1` every two labels coincide. -/
theorem eq_of_le_one (hN : N ≤ 1) (k l : Fin N) : k = l := by
  apply Fin.ext
  have := k.2
  have := l.2
  omega

/-- For `N ≤ 1` every sample lies in `simpleRatSet F a c` (there are no two distinct labels). -/
theorem mem_simpleRatSet_of_le_one (hN : N ≤ 1) (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ)
    (ω : FlowSample N) : ω ∈ RelativeDuhamel.simpleRatSet F a c :=
  ⟨0, fun _ _ i j hij => absurd (eq_of_le_one hN i j) hij⟩

/-- For `N ≥ 2`, a sample of `simpleRatSet F a c` has Hermitian `ω.1`. -/
theorem isHermitian_of_mem_simpleRatSet {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (hN : 2 ≤ N) {ω : FlowSample N} (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) :
    ω.1.IsHermitian := by
  by_contra hH
  obtain ⟨m, hm⟩ := hω
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (Fin.mk.inj_iff.1 h) (by norm_num)
  have := hm a (Or.inl (mem_insert a _)) _ _ h01
  rw [flowEigenvalue_eq_zero_of_not_isHermitian hF a hH,
    flowEigenvalue_eq_zero_of_not_isHermitian hF a hH, sub_self, abs_zero] at this
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

/-- **The quantifier domain.** For Hermitian `F`, `a ≤ c` and every flow sample `ω`: the
spectrum of the flow is simple at every time of `[a, c]` iff `ω ∈ simpleRatSet F a c`. -/
theorem strictMono_iff_mem_simpleRatSet {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (hac : a ≤ c) (ω : FlowSample N) :
    (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) ↔ ω ∈ RelativeDuhamel.simpleRatSet F a c := by
  rcases le_or_gt N 1 with hN | hN
  · refine ⟨fun _ => mem_simpleRatSet_of_le_one hN F a c ω, fun _ σ _ i j hij => ?_⟩
    exact absurd (eq_of_le_one hN i j) hij.ne
  · by_cases hH : ω.1.IsHermitian
    · exact (RelativeDuhamel.mem_simpleRatSet_iff hF hac hH).symm
    · refine ⟨fun h => ?_, fun h => absurd (isHermitian_of_mem_simpleRatSet hF hN h) hH⟩
      have h01 : (⟨0, by omega⟩ : Fin N) < ⟨1, by omega⟩ := Fin.mk_lt_mk.2 zero_lt_one
      have := h a ⟨le_rfl, hac⟩ h01
      rw [flowEigenvalue_eq_zero_of_not_isHermitian hF a hH,
        flowEigenvalue_eq_zero_of_not_isHermitian hF a hH] at this
      exact absurd this (lt_irrefl 0)

/-- For `N ≥ 2`, a sample of `simpleRatSet F a c` (`a ≤ c`) has no collision on `[a, c]`. -/
theorem noCollision_of_mem_simpleRatSet {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (hac : a ≤ c) (hN : 2 ≤ N) {ω : FlowSample N} (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) :
    NoCollision F a c ω := by
  have hH := isHermitian_of_mem_simpleRatSet hF hN hω
  have hs := (RelativeDuhamel.mem_simpleRatSet_iff hF hac hH).1 hω
  exact ⟨hH, fun σ hσ k l hkl => (hs σ hσ).injective.ne hkl⟩

/-- For `N ≤ 1` every flow rate vanishes. -/
theorem flowRate_eq_zero_of_le_one (hN : N ≤ 1) (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (ω : FlowSample N) (σ : ℝ) (k l : Fin N) : flowRate F a ω σ k l = 0 := by
  rw [eq_of_le_one hN k l]
  simp only [flowRate, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, inv_zero]

/-- **Continuity of the short rates on simple paths.** For `ω ∈ simpleRatSet F a c`,
`shortRate F a ω ℓ` is continuous on `[a, c]`. -/
theorem continuousOn_shortRate_of_mem {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (hac : a ≤ c) {ω : FlowSample N} (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) (ℓ : ℕ) :
    ContinuousOn (shortRate F a ω ℓ) (Icc a c) := by
  rcases le_or_gt N 1 with hN | hN
  · have e : shortRate F a ω ℓ = fun _ _ _ => 0 := by
      funext σ k l
      simp only [shortRate, flowRate_eq_zero_of_le_one hN, ite_self]
    rw [e]
    exact continuousOn_const
  · exact continuousOn_shortRate hF (noCollision_of_mem_simpleRatSet hF hac hN hω) ℓ

/-- **Continuity of the reference damping on simple paths.** For `ω ∈ simpleRatSet F a c`,
`refDamping F a b₀ ω ℓ` is continuous on `[a, c]`. -/
theorem continuousOn_refDamping_of_mem {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (hac : a ≤ c) {ω : FlowSample N} (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) (b₀ : ℝ)
    (ℓ : ℕ) : ContinuousOn (refDamping F a b₀ ω ℓ) (Icc a c) := by
  rcases le_or_gt N 1 with hN | hN
  · have e : refDamping F a b₀ ω ℓ = fun _ _ => max 0 (b₀ * N / ℓ) := by
      funext σ k
      simp only [refDamping, longCoupling, flowRate_eq_zero_of_le_one hN, Finset.sum_const_zero]
    rw [e]
    exact continuousOn_const
  · exact continuousOn_refDamping hF (noCollision_of_mem_simpleRatSet hF hac hN hω) b₀ ℓ

/-- Every flow rate at a time of `[a, c]` is `pathSigma F a a c`-measurable. -/
theorem measurable_flowRate_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) {a c x : ℝ}
    (hx : x ∈ Icc a c) (k l : Fin N) :
    Measurable[pathSigma F a a c] (fun ω : FlowSample N => flowRate F a ω x k l) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  have hk : Measurable fun ω : FlowSample N => flowEigenvalue F a ω x k :=
    measurable_flowEigenvalue_pathSigma F a a c hx k
  have hl : Measurable fun ω : FlowSample N => flowEigenvalue F a ω x l :=
    measurable_flowEigenvalue_pathSigma F a a c hx l
  exact (measurable_const.mul ((hk.sub hl).pow_const 2)).inv

/-- **Path measurability of the short rates.** For `x ∈ [a, c]`,
`ω ↦ shortRate F a ω ℓ x k l` is `pathSigma F a a c`-measurable. -/
theorem measurable_shortRate_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) {a c x : ℝ}
    (hx : x ∈ Icc a c) (ℓ : ℕ) (k l : Fin N) :
    Measurable[pathSigma F a a c] (fun ω : FlowSample N => shortRate F a ω ℓ x k l) := by
  by_cases h : k ≠ l ∧ labelDist k l < ℓ
  · simp only [shortRate, ite_eq_left h]
    exact measurable_flowRate_pathSigma F hx k l
  · simp only [shortRate, ite_eq_right h]
    exact @measurable_const _ _ _ (pathSigma F a a c) _

/-- **Path measurability of the reference damping.** For `x ∈ [a, c]`,
`ω ↦ refDamping F a b₀ ω ℓ x k` is `pathSigma F a a c`-measurable. -/
theorem measurable_refDamping_pathSigma (F : Matrix (Fin N) (Fin N) ℂ) {a c x : ℝ}
    (hx : x ∈ Icc a c) (b₀ : ℝ) (ℓ : ℕ) (k : Fin N) :
    Measurable[pathSigma F a a c] (fun ω : FlowSample N => refDamping F a b₀ ω ℓ x k) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  have h : Measurable fun ω : FlowSample N => longCoupling F a ω ℓ x k := by
    simp only [longCoupling]
    exact Finset.measurable_sum _ fun m _ => measurable_flowRate_pathSigma F hx k m
  exact h.max measurable_const

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
