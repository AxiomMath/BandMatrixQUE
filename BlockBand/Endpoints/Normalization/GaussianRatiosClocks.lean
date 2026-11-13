module

public import BlockBand.Endpoints.Normalization.GaussianRatiosEngine

/-!
# Uniform joint comparison of finitely many positive clocks

The joint-law comparison inside the proof of the Gaussian ratios theorem and Step 1 of the
two-positive-clocks lemma, in a form covering both.

**Statement** (`clock_weak_comparison`). Assumes `CoareaPalm.FreshPalmContract` and the
normalizer interface `NormalizerLowerBound` (`hZ`, the statement of the deterministic
normalizer corollary). Fixed first: `A, c₀, r₀, s₀, v₀` (`FreshConstants`), a finite index type
`ι`, a trace ratio `R ≥ 0` and a bounded continuous test `h : ℝ^ι → ℝ`. For every `ε > 0` there
is `N₀`; for `N ≥ N₀`, every `F` in `FreshClass F A c₀ E r₀ s₀ v₀`, every family
`P : ι → M_N(ℂ)` of positive semidefinite matrices, every `T > 0` with `Tr(ΓP_i) ≤ RT` for all
`i` (no norm, condition-number or Loewner restriction) and every `M` with `MM* = Γ`: `Z > 0` and
`|Â[h((N v*P_iv/T)_i)] - E_g h((g*M*P_iMg/T)_i)| ≤ ε`.

Proof: `weak_comparison_of_moments` applied to the family of all such data, with
`μ = Â ∘ (palmClocks)⁻¹`, `ν = CN(0,I) ∘ (gaussClocks ∘ M)⁻¹`, size `N`; the moment hypothesis is
`mixed_moment_uniform`; the factorial bound is `E(g*Qg)^m ≤ m!(Tr Q)^m` with
`Q = M*(Σ_i P_i)M/T`, `Tr Q ≤ |ι| R`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix Filter Topology BoundedContinuousFunction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder Matrix

/-- The data of one member of the clock class (all sizes `N ≥ N₁`). -/
structure ClockDatum (ι : Type*) (A c₀ r₀ s₀ v₀ R : ℝ) (N₁ : ℕ) where
  N : ℕ
  hN : N₁ ≤ N
  F : Matrix (Fin N) (Fin N) ℂ
  E : ℝ
  hF : FreshClass F A c₀ E r₀ s₀ v₀
  P : ι → Matrix (Fin N) (Fin N) ℂ
  hP : ∀ i, (P i).PosSemidef
  T : ℝ
  hT : 0 < T
  hR : ∀ i, traceAgainst (freshGamma F c₀ E) (P i) ≤ R * T
  M : Matrix (Fin N) (Fin N) ℂ
  hM : M * Mᴴ = freshGamma F c₀ E
  hZ : 0 < palmMass F c₀ E

variable {N : ℕ}

theorem continuous_palmClocks {ι : Type*} (N : ℕ) (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ) :
    Continuous (palmClocks N P T) :=
  continuous_pi fun i => (continuous_const.mul (continuous_quadForm' (P i))).div_const T

theorem continuous_gaussClocks {ι : Type*} (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ) :
    Continuous (gaussClocks P T) :=
  continuous_pi fun i => (continuous_quadForm' (P i)).div_const T

/-- `T⁻¹ Σ_i P_i`. -/
def sumMatrix {ι : Type*} [Fintype ι] (P : ι → Matrix (Fin N) (Fin N) ℂ) (T : ℝ) :
    Matrix (Fin N) (Fin N) ℂ := ((T⁻¹ : ℝ) : ℂ) • ∑ i, P i

theorem absSum_gaussClocks {ι : Type*} [Fintype ι] {P : ι → Matrix (Fin N) (Fin N) ℂ}
    (hP : ∀ i, (P i).PosSemidef) {T : ℝ} (hT : 0 < T) (x : Fin N → ℂ) :
    absSum (gaussClocks P T x) = quadForm (sumMatrix P T) x := by
  unfold absSum gaussClocks sumMatrix
  rw [quadForm_smul, quadForm_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_of_nonneg (div_nonneg (quadForm_nonneg_of_posSemidef (hP i) x) hT.le), div_eq_inv_mul]

theorem sumMatrix_posSemidef {ι : Type*} [Fintype ι] {P : ι → Matrix (Fin N) (Fin N) ℂ}
    (hP : ∀ i, (P i).PosSemidef) {T : ℝ} (hT : 0 < T) : (sumMatrix P T).PosSemidef := by
  unfold sumMatrix
  have h : 0 ≤ ((T⁻¹ : ℝ) : ℂ) := by exact_mod_cast (inv_pos.mpr hT).le
  exact (posSemidef_finset_sum Finset.univ fun i => hP i).smul h

theorem traceAgainst_sumMatrix_le {ι : Type*} [Fintype ι] {P : ι → Matrix (Fin N) (Fin N) ℂ}
    {Γ : Matrix (Fin N) (Fin N) ℂ} {T R : ℝ} (hT : 0 < T)
    (hR : ∀ i, traceAgainst Γ (P i) ≤ R * T) :
    traceAgainst Γ (sumMatrix P T) ≤ Fintype.card ι * R := by
  unfold sumMatrix traceAgainst
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have : (Γ * ∑ i, P i).trace.re = ∑ i, traceAgainst Γ (P i) :=
    traceAgainst_finset_sum Finset.univ Γ _
  rw [this, Finset.mul_sum]
  calc ∑ i, T⁻¹ * traceAgainst Γ (P i) ≤ ∑ _i : ι, R :=
        Finset.sum_le_sum fun i _ => by rw [inv_mul_eq_div, div_le_iff₀ hT]; exact hR i
    _ = Fintype.card ι * R := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem measurableSet_orthant (ι : Type*) [Fintype ι] :
    MeasurableSet {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
  have : {x : ι → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} := by ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)

/-- **Uniform joint comparison of positive clocks.** Conditional on `FreshPalmContract` and
the normalizer interface `hZ`. -/
theorem clock_weak_comparison (hPalm : FreshPalmContract) (hZ : NormalizerLowerBound)
    {A c₀ r₀ s₀ v₀ : ℝ} (hc : FreshConstants c₀ r₀ s₀ v₀) {ι : Type*} [Fintype ι]
    (R : ℝ) (hR0 : 0 ≤ R) (h : (ι → ℝ) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ P : ι → Matrix (Fin N) (Fin N) ℂ, (∀ i, (P i).PosSemidef) →
      ∀ T : ℝ, 0 < T → (∀ i, traceAgainst (freshGamma F c₀ E) (P i) ≤ R * T) →
      ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
        0 < palmMass F c₀ E ∧
        |palmExpect F c₀ E (fun v => h (palmClocks N P T v)) -
            ∫ g, h (gaussClocks P T (M *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤ ε := by
  classical
  -- the size threshold for `Z > 0`
  obtain ⟨N₁, hN₁⟩ := (mixed_moment_uniform hPalm hZ (A := A) hc (ι := ι) R hR0
    (r := 0) (fun i => i.elim0) 1 one_pos)
  let α := ClockDatum ι A c₀ r₀ s₀ v₀ R N₁
  let μ : α → Measure (ι → ℝ) := fun a => (palmMeasure a.F c₀ a.E).map (palmClocks a.N a.P a.T)
  let ν : α → Measure (ι → ℝ) := fun a =>
    (circularVectorLaw (Fin a.N)).map fun g => gaussClocks a.P a.T (a.M *ᵥ g)
  have hμp : ∀ a : α, IsProbabilityMeasure (μ a) := fun a => by
    have := isProbabilityMeasure_palmMeasure a.F c₀ a.E a.hZ
    infer_instance
  have hνp : ∀ a : α, IsProbabilityMeasure (ν a) := fun a => inferInstance
  have hgm : ∀ a : α, Measurable fun g : Fin a.N → ℂ => gaussClocks a.P a.T (a.M *ᵥ g) :=
    fun a => ((continuous_gaussClocks a.P a.T).comp
      (Matrix.toLin' a.M).continuous_of_finiteDimensional).measurable
  have hpm : ∀ a : α, Measurable (palmClocks a.N a.P a.T) := fun a =>
    (continuous_palmClocks a.N a.P a.T).measurable
  have hposμ : ∀ a, ∀ᵐ x ∂(μ a), ∀ i, 0 ≤ x i := by
    intro a
    refine (ae_map_iff (hpm a).aemeasurable (measurableSet_orthant ι)).mpr
      (Eventually.of_forall fun v i => ?_)
    unfold palmClocks
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (quadForm_nonneg_of_posSemidef (a.hP i) v))
      a.hT.le
  have hposν : ∀ a, ∀ᵐ x ∂(ν a), ∀ i, 0 ≤ x i := by
    intro a
    refine (ae_map_iff (hgm a).aemeasurable (measurableSet_orthant ι)).mpr
      (Eventually.of_forall fun g i => ?_)
    unfold gaussClocks
    exact div_nonneg (quadForm_nonneg_of_posSemidef (a.hP i) _) a.hT.le
  have hintμ : ∀ a (r : ℕ) (f : Fin r → ι), Integrable (monomial f) (μ a) := by
    intro a r f
    rw [integrable_map_measure (continuous_monomial f).aestronglyMeasurable (hpm a).aemeasurable]
    exact integrable_palmMeasure_of_continuous a.F c₀ a.E
      ((continuous_monomial f).comp (continuous_palmClocks a.N a.P a.T))
  have hintν : ∀ a (r : ℕ) (f : Fin r → ι), Integrable (monomial f) (ν a) := by
    intro a r f
    rw [integrable_map_measure (continuous_monomial f).aestronglyMeasurable (hgm a).aemeasurable]
    refine (integrable_quadForm_mulVec_pow (sumMatrix_posSemidef a.hP a.hT) a.M r).mono'
      ((continuous_monomial f).measurable.comp (hgm a)).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, Function.comp_apply, ← absSum_gaussClocks a.hP a.hT]
    exact abs_monomial_le f _
  have hint_palm : ∀ a : α, ∀ φ : (ι → ℝ) → ℝ, Continuous φ →
      ∫ x, φ x ∂(μ a) = palmExpect a.F c₀ a.E (fun v => φ (palmClocks a.N a.P a.T v)) := by
    intro a φ hφ
    rw [integral_map (hpm a).aemeasurable hφ.aestronglyMeasurable]
    exact (palmExpect_eq_integral_of_continuous a.F c₀ a.E
      (φ := fun v => φ (palmClocks a.N a.P a.T v)) (hφ.comp (continuous_palmClocks _ _ _))).symm
  have hint_gauss : ∀ a : α, ∀ φ : (ι → ℝ) → ℝ, Continuous φ →
      ∫ x, φ x ∂(ν a) = ∫ g, φ (gaussClocks a.P a.T (a.M *ᵥ g)) ∂circularVectorLaw (Fin a.N) :=
    fun a φ hφ => integral_map (hgm a).aemeasurable hφ.aestronglyMeasurable
  have hmom : ∀ (r : ℕ) (f : Fin r → ι) (η : ℝ), 0 < η → ∃ n₀ : ℕ, ∀ a : α, n₀ ≤ a.N →
      |∫ x, monomial f x ∂(μ a) - ∫ x, monomial f x ∂(ν a)| ≤ η := by
    intro r f η hη
    obtain ⟨n₀, hn₀⟩ := mixed_moment_uniform hPalm hZ (A := A) hc R hR0 f η hη
    refine ⟨n₀, fun a ha => ?_⟩
    rw [hint_palm a _ (continuous_monomial f), hint_gauss a _ (continuous_monomial f)]
    exact (hn₀ a.N ha a.F a.E a.hF a.P a.hP a.T a.hT a.hR a.M a.hM).2
  have hbound : ∀ (a : α) (m : ℕ), ∫ x, absSum x ^ m ∂(ν a) ≤
      m.factorial * (Fintype.card ι * R) ^ m := by
    intro a m
    rw [hint_gauss a (fun x => absSum x ^ m) (continuous_absSum.pow m)]
    simp_rw [absSum_gaussClocks a.hP a.hT]
    refine (integral_quadForm_mulVec_pow_le (sumMatrix_posSemidef a.hP a.hT) a.M _ a.hM m).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ (traceAgainst_sumMatrix_le a.hT a.hR) m)
      (Nat.cast_nonneg _)
    exact BlockBand.Endpoints.Clock.traceAgainst_nonneg
      (BlockBand.Endpoints.Clock.freshGamma_posSemidef a.F hc.1.le a.E)
      (sumMatrix_posSemidef a.hP a.hT)
  obtain ⟨n₀, hn₀⟩ := weak_comparison_of_moments (fun a : α => a.N) μ ν hposμ hposν hintμ hintν
    hmom (Fintype.card ι * R) (by positivity) hbound h ε hε
  refine ⟨max n₀ N₁, fun N hN F E hF P hP T hT hR M hM => ?_⟩
  have hZpos : 0 < palmMass F c₀ E :=
    (hN₁ N (le_of_max_le_right hN) F E hF P hP T hT hR M hM).1
  refine ⟨hZpos, ?_⟩
  let a : α := ⟨N, le_of_max_le_right hN, F, E, hF, P, hP, T, hT, hR, M, hM, hZpos⟩
  have := hn₀ a (le_of_max_le_left hN)
  rw [hint_palm a _ h.continuous, hint_gauss a _ h.continuous] at this
  exact this

end BlockBand.Endpoints.Normalization
