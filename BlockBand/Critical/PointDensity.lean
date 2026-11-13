module

public import BlockBand.Critical.PointDensity.MeanDensity
public import BlockBand.Critical.PointDensity.Boundary
public import BlockBand.Critical.PointDensity.Johansson

/-!
# The point-density lemma

This file proves `PointDensityContract` from the external sine-kernel input `ExternalSine`:
the mean eigenvalue measure of the fresh deformed ensemble has a continuous density `ρ`, and
`|ρ(x) - Im m/π| ≤ ε_N` uniformly, with `ε_N → 0`.

## Proof

1. *(all `N`)* `freshMeanEigenvalueMeasure N c F = volume.withDensity (meanDensity F c)` with
   `meanDensity` continuous, strictly positive and `≤ N/√(2πc)` (by the scalar
   split); so a continuous density exists, and every continuous density equals
   `meanDensityReal F c` everywhere.
2. *(small `N < N₁`)* `|ρ(x) - Im m/π| ≤ N/√(2πc) + v₀⁻¹/π` (regularity gives
   `Im m ≤ v₀⁻¹`).
3. *(large `N ≥ N₁`)* translate `F ↦ F' = F - xI`; `‖F'‖ ≤ 2N^A + 2v₀⁻¹ ≤ N^{A'}`,
   and `M = (F - x - cm)⁻¹` solves `IsBoundaryMDE c F' 0 M` with `⟨M⟩ = m`.
   `ExternalSine` gives a continuous kernel with `deformedFactorialCorrelation … 1 =
   volume.withDensity (Re K(y,y))` (diagonal of the kernel); pushing forward by `v ↦ v 0 + x` this is
   `N • freshMeanEigenvalueMeasure N c F` (by the Johansson formula). Continuous densities agree, so
   `N · meanDensity(x) = ofReal(Re K(0,0))`, and clause (b) gives
   `|ρ(x) - Im m/π| ≤ |Re K(0,0)/N - Im m/π| ≤ C N^{-1/2}`.
4. `ε_N = N/√(2πc) + v₀⁻¹/π` for `N < N₁` and `C N^{-1/2}` after; `ε_N → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.PointDensity

open MeasureTheory Matrix Filter Topology Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Critical
  BlockBand.External
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- `max(k,0)/N` is at least as close to a nonnegative `r` as `k/N`. -/
theorem abs_max_div_sub_le {k r n : ℝ} (hn : 0 < n) (hr : 0 ≤ r) :
    |max k 0 / n - r| ≤ |k / n - r| := by
  rcases le_total k 0 with hk | hk
  · rw [max_eq_right hk, zero_div, zero_sub, abs_neg, abs_of_nonneg hr]
    have h1 : k / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hk hn.le
    have h2 := neg_abs_le (k / n - r)
    linarith
  · rw [max_eq_left hk]

/-- `2N^A + 2v₀⁻¹ ≤ N^{max(A,0)+1}` once `N ≥ 2 + 2v₀⁻¹`. -/
theorem two_rpow_add_le {N : ℕ} {A v₀ : ℝ} (hv0 : 0 < v₀) (hN : 2 + 2 * v₀⁻¹ ≤ (N : ℝ)) :
    2 * (N : ℝ) ^ A + 2 * v₀⁻¹ ≤ (N : ℝ) ^ (max A 0 + 1) := by
  have hv : 0 ≤ v₀⁻¹ := inv_nonneg.2 hv0.le
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (N : ℝ) ≠ 0 := by positivity
  have h1 : (N : ℝ) ^ A ≤ (N : ℝ) ^ max A 0 :=
    Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ (N : ℝ) ^ max A 0 := Real.one_le_rpow hN1 (le_max_right _ _)
  rw [Real.rpow_add_one hNpos]
  nlinarith

/-- **`PointDensityContract` from `Inputs.ExternalSine`.**
Law `GUE_N(c/N)` (`gueMeasure`), normalized mean eigenvalue measure of `F + G_c`; for the fixed `A`
and `FreshConstants c r₀ s₀ v₀` a sequence `ε_N → 0` such that, uniformly in `N ≥ 1`, Hermitian `F`
with `‖F‖ ≤ N^A` (Euclidean operator norm, via `CoareaPalm.NormBound`), regular at `(c, x)`:
a continuous density exists and every continuous density `ρ` has
`|ρ(x) - Im m_{F,c}(x)/π| ≤ ε_N`.
The only hypothesis is `Inputs.ExternalSine`.
-/
theorem pointDensity_holds (hS : BlockBand.Internal.Contracts.Inputs.ExternalSine) :
    PointDensityContract := by
  intro A c r₀ s₀ v₀ hK
  have hc0 : 0 < c := hK.1
  have hv₀ : 0 < v₀ := hK.2.2.2.2.2
  obtain ⟨⟨C, N₀, hES⟩, -⟩ := hS (max A 0 + 1) c c v₀ 0 0 0 hc0 le_rfl hv₀
  set N₁ : ℕ := max N₀ ⌈2 + 2 * v₀⁻¹⌉₊ with hN₁def
  set ε : ℕ → ℝ := fun N => if N < N₁ then densityBound c N + v₀⁻¹ / Real.pi
    else C * (N : ℝ) ^ (-(1 : ℝ) / 2) with hεdef
  refine ⟨ε, ?_, ?_⟩
  · have h0 : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
      have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul C
      rw [mul_zero] at h
      refine h.congr fun N => ?_
      simp only [Function.comp]
      congr 2
      ring
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop N₁] with N hN
    simp only [hεdef, not_lt.2 hN, ite_false]
  · intro N hN F x hC
    have hF : F.IsHermitian := hC.1
    obtain ⟨hv, hv'⟩ := freshDyson_im_bounds hK hC
    have hm : 0 < (freshDyson F c x).im := lt_of_lt_of_le hv₀ hv
    refine ⟨⟨meanDensityReal F c, continuous_meanDensityReal hN F c, ?_⟩, ?_⟩
    · rw [freshMeanEigenvalueMeasure_eq_withDensity hN hF hc0]
      congr 1
      funext y
      exact (ofReal_meanDensityReal hN F c y).symm
    intro ρ hρ hμ
    rw [apply_eq_meanDensityReal hN hF hc0 hρ hμ x]
    have hr0 : 0 ≤ (freshDyson F c x).im / Real.pi := div_nonneg hm.le Real.pi_pos.le
    by_cases hN₁ : N < N₁
    · simp only [hεdef, hN₁, ite_true]
      have h1 := meanDensityReal_nonneg F c x
      have h2 := meanDensityReal_le hN F c x
      have h3 : (freshDyson F c x).im / Real.pi ≤ v₀⁻¹ / Real.pi :=
        div_le_div_of_nonneg_right hv' Real.pi_pos.le
      rw [abs_le]
      constructor <;> linarith
    simp only [hεdef, hN₁, ite_false]
    have hNN : N₁ ≤ N := not_lt.1 hN₁
    have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hNN
    have hN2 : 2 + 2 * v₀⁻¹ ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hNN)
    have hF' : (F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian :=
      hF.sub (isHermitian_one.smul (Complex.conj_ofReal x))
    have hnorm : ‖F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ (N : ℝ) ^ (max A 0 + 1) :=
      (opNorm_sub_center_le hF hN hC.2.1 hc0 hv₀ hv).trans (two_rpow_add_le hv₀ hN2)
    obtain ⟨hMDE, htr⟩ := isBoundaryMDE_freshM hF hc0 hm
    have ht : ((Real.toNNReal c : ℝ≥0) : ℝ) = c := Real.coe_toNNReal _ hc0.le
    obtain ⟨Kern, -, hKc, hcorr, -, hdiag⟩ := hES N hNN₀ _ hF' hnorm (Real.toNNReal c)
      (by rw [ht]; exact ⟨le_rfl, le_rfl⟩) 0 ⟨le_rfl, le_rfl⟩ (freshM F c x)
      (by rw [ht]; exact hMDE) (by rw [htr]; exact hv)
    rw [htr] at hdiag
    have h1 := hcorr 1 (by omega)
    have hpush := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (fun v => v 0 + x)) h1
    rw [map_deformedFactorialCorrelation_one hN hF hc0 x hF', map_shift_withDensity,
      freshMeanEigenvalueMeasure_eq_withDensity hN hF hc0,
      ← withDensity_smul _ (measurable_meanDensity F c)] at hpush
    have hfun : (fun y : ℝ => ENNReal.ofReal (Matrix.det (fun i j : Fin 1 =>
        Kern ((fun _ : Fin 1 => y - x) i) ((fun _ : Fin 1 => y - x) j))).re) =
        fun y => ENNReal.ofReal (Kern (y - x) (y - x)).re := by
      funext y
      have hd := Matrix.det_unique (R := ℂ) (n := Fin 1) (Matrix.of fun i j : Fin 1 =>
        Kern ((fun _ : Fin 1 => y - x) i) ((fun _ : Fin 1 => y - x) j))
      exact congrArg (fun z : ℂ => ENNReal.ofReal z.re) hd
    rw [hfun] at hpush
    have hsm : (N : ℝ≥0∞) • meanDensity F c = fun y => (N : ℝ≥0∞) * meanDensity F c y := rfl
    rw [hsm] at hpush
    have hcont : Continuous fun y : ℝ => ENNReal.ofReal (Kern (y - x) (y - x)).re := by
      have hd : Continuous fun y : ℝ => (y - x, y - x) :=
        (continuous_id.sub continuous_const).prodMk (continuous_id.sub continuous_const)
      exact ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (hKc.comp hd))
    have heq := eq_of_withDensity_eq_of_continuous
      ((ENNReal.continuous_const_mul (ENNReal.natCast_ne_top N)).comp
        (continuous_meanDensity hN F c)) hcont hpush
    have hx := congrFun heq x
    simp only [Function.comp, sub_self] at hx
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hval : meanDensityReal F c x = max (Kern 0 0).re 0 / N := by
      have h := congrArg ENNReal.toReal hx
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal'] at h
      unfold meanDensityReal
      rw [← h]
      field_simp
    rw [hval]
    refine (abs_max_div_sub_le hNr hr0).trans ?_
    refine le_trans ?_ hdiag
    have hre : (Kern 0 0 / ((N : ℝ) : ℂ) -
        (((freshDyson F c x).im / Real.pi : ℝ) : ℂ)).re =
        (Kern 0 0).re / N - (freshDyson F c x).im / Real.pi := by
      rw [Complex.sub_re, Complex.div_ofReal_re, Complex.ofReal_re]
    rw [← hre]
    exact Complex.abs_re_le_norm _

end BlockBand.Critical.PointDensity
