module

public import BlockBand.Critical.RelativeVectors.Statement
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Smooth decorated tests approximating continuous compactly supported tests

The decorated clause of the relative mixed-vectors theorem (`RelativeMixedVectorsDecorated`) is
stated for tests that are bounded `C²` in the mark (`IsDecoratedTest`), while the collar poles
clause needs every nonnegative `f ∈ C_c(ℝ × ℂ^r)` (for instance `(x, g) ↦ φ(x, π⁻¹gg^*)`).
This file bridges the two by uniform approximation.

Deterministic; no measure.

* `norm_iteratedFDeriv_partial_le`: `‖D^i_z ψ(x, ·)(z)‖ ≤ ‖D^i ψ(x, z)‖`.
* `exists_isC2Bounded_partial`: a smooth compactly supported `ψ` is bounded `C²` in the mark,
  uniformly in the location; `isDecoratedTest_of_smooth`.
* **`exists_smooth_approx`**: every nonnegative `f ∈ C_c(ℝ × ℂ^r)` is uniformly `η`-close to a
  nonnegative smooth compactly supported `ψ` (`ψ = χ g²`, `g` a smooth uniform approximant of `√f`
  from Mathlib `UniformContinuous.exists_contDiff_dist_le`, `χ` a smooth bump equal to `1` on the
  support of `f`); `f` and every such `ψ` vanish for `|x| > R`, `R` depending on `f` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open Metric
open BlockBand.Critical.RelativeVectors
open scoped ContDiff

variable {r : ℕ}

theorem natCast_le_infty (i : ℕ) : ((i : ℕ∞) : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.2 le_top

/-- Partial iterated derivatives in the mark are bounded by the joint ones. -/
theorem norm_iteratedFDeriv_partial_le {ψ : ℝ × (Fin r → ℂ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : ℝ)
    (z : Fin r → ℂ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun w => ψ (x, w)) z‖ ≤ ‖iteratedFDeriv ℝ i ψ (x, z)‖ := by
  set L : (Fin r → ℂ) →L[ℝ] ℝ × (Fin r → ℂ) := ContinuousLinearMap.inr ℝ ℝ (Fin r → ℂ)
  set h : ℝ × (Fin r → ℂ) → ℝ := fun q => ψ ((x, 0) + q)
  have hfun : (fun w => ψ (x, w)) = h ∘ L := by
    funext w; simp [h, L]
  have hh : ContDiff ℝ ∞ h := hψ.comp (contDiff_const.add contDiff_id)
  rw [hfun, L.iteratedFDeriv_comp_right hh z (natCast_le_infty i)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ (Fin r → ℂ)
  have hprod : ∏ _j : Fin i, ‖L‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hL
  have he : iteratedFDeriv ℝ i h (L z) = iteratedFDeriv ℝ i ψ (x, z) := by
    rw [show h = fun q => ψ ((x, 0) + q) from rfl, iteratedFDeriv_comp_add_left]
    congr 1
    simp [L]
  rw [he]
  calc ‖iteratedFDeriv ℝ i ψ (x, z)‖ * ∏ _j : Fin i, ‖L‖ ≤ ‖iteratedFDeriv ℝ i ψ (x, z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := mul_one _

/-- A smooth compactly supported function on `ℝ × ℂ^r` is bounded `C²` in the mark, uniformly in
the location. -/
theorem exists_isC2Bounded_partial {ψ : ℝ × (Fin r → ℂ) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) : ∃ K : ℝ, ∀ x, IsC2Bounded K (fun z => ψ (x, z)) := by
  have hbd : ∀ i : ℕ, ∃ C, ∀ p, ‖iteratedFDeriv ℝ i ψ p‖ ≤ C := fun i =>
    (hψ.continuous_iteratedFDeriv (natCast_le_infty i)).bounded_above_of_compact_support
      (hc.iteratedFDeriv i)
  obtain ⟨C0, hC0⟩ := hbd 0
  obtain ⟨C1, hC1⟩ := hbd 1
  obtain ⟨C2, hC2⟩ := hbd 2
  refine ⟨max C0 (max C1 C2), fun x => ⟨?_, fun z => ?_, fun z => ?_, fun z => ?_⟩⟩
  · exact (hψ.comp (contDiff_const.prodMk contDiff_id)).of_le (natCast_le_infty 2)
  · have := hC0 (x, z)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [← norm_iteratedFDeriv_one]
    exact ((norm_iteratedFDeriv_partial_le hψ x z 1).trans (hC1 (x, z))).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact ((norm_iteratedFDeriv_partial_le hψ x z 2).trans (hC2 (x, z))).trans
      ((le_max_right _ _).trans (le_max_right _ _))

/-- A smooth nonnegative compactly supported test vanishing for `|x| > R` is a decorated test. -/
theorem isDecoratedTest_of_smooth {ψ : ℝ × (Fin r → ℂ) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (h0 : ∀ p, 0 ≤ ψ p) {R : ℝ}
    (hR : ∀ x z, R < |x| → ψ (x, z) = 0) : ∃ K : ℝ, IsDecoratedTest r R K ψ := by
  obtain ⟨K, hK⟩ := exists_isC2Bounded_partial hψ hc
  exact ⟨K, ⟨hψ.continuous, h0, hR, hK⟩⟩

/-- **Smooth approximation of a nonnegative compactly supported test.** -/
theorem exists_smooth_approx (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ)
    (hf : ∀ p, 0 ≤ f p) :
    ∃ R : ℝ, 0 ≤ R ∧ (∀ x z, R < |x| → f (x, z) = 0) ∧ ∀ η : ℝ, 0 < η →
      ∃ ψ : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ, ContDiff ℝ ∞ ψ ∧
        (∀ p, 0 ≤ ψ p) ∧ (∀ p, |ψ p - f p| ≤ η) ∧ ∀ x z, R < |x| → ψ (x, z) = 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
  set ρ₁ := max ρ₀ 1
  have hρ₁ : 0 < ρ₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨ρ₁ + 1, by linarith, fun x z hx => ?_, fun η hη => ?_⟩
  · refine image_eq_zero_of_notMem_tsupport fun ht => ?_
    have h1 := hρ₀ ht
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : |x| ≤ ‖(x, z)‖ := by simp
    have h3 : ρ₀ ≤ ρ₁ := le_max_left _ _
    linarith
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  set M' := max M 0
  have hfM : ∀ p, f p ≤ M' := fun p => by
    have := hM p
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  set s : ℝ × (Fin r → ℂ) → ℝ := fun p => Real.sqrt (f p)
  have hsc : Continuous s := Real.continuous_sqrt.comp f.continuous
  have hss : HasCompactSupport s := f.hasCompactSupport.comp_left Real.sqrt_zero
  have hsu : UniformContinuous s := hss.uniformContinuous_of_continuous hsc
  set A := 2 * Real.sqrt M' + 1
  have hA : 0 < A := by positivity
  set η' := min 1 (η / A)
  have hη' : 0 < η' := lt_min one_pos (div_pos hη hA)
  have hη'1 : η' ≤ 1 := min_le_left _ _
  have hη'A : η' * A ≤ η := by
    have := min_le_right 1 (η / A)
    calc η' * A ≤ η / A * A := mul_le_mul_of_nonneg_right this hA.le
      _ = η := div_mul_cancel₀ η hA.ne'
  obtain ⟨g, hg, hgs⟩ := hsu.exists_contDiff_dist_le hη'
  set χ : ContDiffBump (0 : ℝ × (Fin r → ℂ)) := ⟨ρ₁, ρ₁ + 1, hρ₁, by linarith⟩
  set ψf : ℝ × (Fin r → ℂ) → ℝ := fun p => χ p * g p ^ 2
  have hψd : ContDiff ℝ ∞ ψf := χ.contDiff.mul (hg.pow 2)
  have hψc : HasCompactSupport ψf := by
    have : ψf = (χ : ℝ × (Fin r → ℂ) → ℝ) * fun p => g p ^ 2 := rfl
    rw [this]
    exact χ.hasCompactSupport.mul_right
  refine ⟨⟨⟨ψf, hψd.continuous⟩, hψc⟩, hψd, fun p => mul_nonneg χ.nonneg (sq_nonneg _),
    fun p => ?_, fun x z hx => ?_⟩
  · change |χ p * g p ^ 2 - f p| ≤ η
    have hgs' : |g p - s p| < η' := by rw [← Real.dist_eq]; exact hgs p
    have hs0 : 0 ≤ s p := Real.sqrt_nonneg _
    have hsM : s p ≤ Real.sqrt M' := Real.sqrt_le_sqrt (hfM p)
    have hfs : f p = s p ^ 2 := (Real.sq_sqrt (hf p)).symm
    by_cases hp : p ∈ closedBall (0 : ℝ × (Fin r → ℂ)) ρ₁
    · rw [χ.one_of_mem_closedBall hp, one_mul, hfs]
      have hfac : g p ^ 2 - s p ^ 2 = (g p - s p) * (g p + s p) := by ring
      rw [hfac, abs_mul]
      have h1 : |g p + s p| ≤ η' + 2 * Real.sqrt M' := by
        have : g p + s p = (g p - s p) + 2 * s p := by ring
        rw [this]
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s p)]
        linarith
      calc |g p - s p| * |g p + s p| ≤ η' * (η' + 2 * Real.sqrt M') :=
            mul_le_mul hgs'.le h1 (abs_nonneg _) hη'.le
        _ ≤ η' * A := mul_le_mul_of_nonneg_left (by simp only [A]; linarith) hη'.le
        _ ≤ η := hη'A
    · have hfp : f p = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun ht => hp ?_
        exact closedBall_subset_closedBall (le_max_left _ _) (hρ₀ ht)
      have hsp : s p = 0 := by simp [s, hfp]
      rw [hsp, sub_zero] at hgs'
      rw [hfp, sub_zero, abs_of_nonneg (mul_nonneg χ.nonneg (sq_nonneg _))]
      have hg2 : g p ^ 2 ≤ η' * η' := by
        rw [sq]
        have := abs_mul_abs_self (g p)
        nlinarith [abs_nonneg (g p)]
      calc χ p * g p ^ 2 ≤ 1 * g p ^ 2 := mul_le_mul_of_nonneg_right χ.le_one (sq_nonneg _)
        _ ≤ η' * η' := by rw [one_mul]; exact hg2
        _ ≤ η' * A := by
          refine mul_le_mul_of_nonneg_left ?_ hη'.le
          have : 0 ≤ Real.sqrt M' := Real.sqrt_nonneg _
          simp only [A]; linarith
        _ ≤ η := hη'A
  · change χ (x, z) * g (x, z) ^ 2 = 0
    rw [χ.zero_of_le_dist, zero_mul]
    rw [dist_zero_right]
    exact (le_of_lt hx).trans (by simp)

end BlockBand.Critical.MatrixClosing.Poles
