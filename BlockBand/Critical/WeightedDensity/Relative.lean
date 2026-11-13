module

public import BlockBand.Critical.WeightedDensity.Global
public import BlockBand.Critical.PointDensity

/-!
# The global weighted density on the regular class and the relative matrix density

*Law.* `G ~ GUE_N(c/N)`; the scalar split `G = A⁰ + ζ I` and the scalar Palm weights `w_{ℓ,x}` of
`FreshPalmContract`.
*Class.* The regular polynomial deformation class: `FreshConstants c r₀ s₀ v₀` (`0 < c < 1`,
`r₀, s₀, v₀ > 0`, `s₀ < c/2`) and the norm exponent `A` come first, then `F` with
`FreshClass F A c E r₀ s₀ v₀` (Hermitian, `‖F‖ ≤ N^A`, `v₀ ≤ Im m_s ≤ v₀⁻¹` near `E`).
`Γ_F(x) = freshGamma F c x = c|F - x - c m_c(x)|^{-2}`, `r_{F,c}(x) = π⁻¹ Im m_{F,c}(x)`
(`freshDyson`).
*Hypotheses.* `FreshPalmContract` (used at order `r = 1`, `K = 1`) and `PointDensityContract`.

## Main results

* `sigma_palm_bound`: `|q*Σ_F(x)q - ρ_{F,c}(x) q*Γq| ≤ (C₁N^{-κ}ρ_{F,c}(x) + C₂N⁻¹) q*Γq` (the
  `r = 1` Palm bound summed over all ranks, divided by `N`).
* `globalWeightedDensity_regular`: on the regular class,
  `(F-e+iη)Σ_F(e)(F-e-iη) ⪯ C I`, `C = C(A,c,r₀,s₀,v₀,η)`.
* `relativeMatrixDensity`: uniformly for `|x - E| ≤ r₀ - r₁` (any fixed `0 < r₁ < r₀`),
  `-ε_N Γ_F(x) ⪯ Σ_F(x) - r_{F,c}(x) Γ_F(x) ⪯ ε_N Γ_F(x)`, `ε_N → 0`, and
  `relativeMatrixDensity_congr`: the same after congruence by every rectangular `B`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.WeightedDensity

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Critical
  BlockBand.Coarea.FreshPalm BlockBand.Critical.PointDensity
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

variable {N : ℕ}

/-!
## Bookkeeping
-/

/-- `Σ_ℓ Z_{ℓ,x} = N ρ_{F,c}(x)` (`Z_{ℓ,x} = E w_{ℓ,x}`). -/
theorem sum_integral_palmWeight (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (c x : ℝ) :
    ∑ ℓ : Fin N, ∫ A0, palmWeight F c x ℓ A0 ∂freshTracelessLaw N c =
      N * meanDensityReal F c x := by
  have hZ : ∀ ℓ : Fin N, ∫ A0, palmWeight F c x ℓ A0 ∂freshTracelessLaw N c =
      (rankDensity F c ℓ x).toReal := by
    intro ℓ
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun A0 =>
      palmWeight_nonneg F c x ℓ A0) (measurable_palmWeight F c x ℓ).aestronglyMeasurable]
    simp [rankDensity, palmSide]
  have hfin : ∀ ℓ : Fin N, rankDensity F c ℓ x ≠ ∞ := fun ℓ =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rankDensity_le F c ℓ x)
  simp_rw [hZ]
  rw [← ENNReal.toReal_sum fun ℓ _ => hfin ℓ, meanDensityReal, meanDensity, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), one_mul]

theorem quadForm_freshGamma_nonneg (F : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c) (x : ℝ)
    (q : Fin N → ℂ) : 0 ≤ quadForm (freshGamma F c x) q :=
  quadForm_nonneg_of_posSemidef (posSemidef_gammaShape _ hc) q

theorem freshGamma_isHermitian (F : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    (freshGamma F c x).IsHermitian :=
  (posSemidef_gammaShape _ hc).1

/-- Regularity on `[E - r₀, E + r₀]` gives regularity at every `x` with `|x - E| ≤ r₀ - r₁`, on
the smaller window of radius `r₁`. -/
theorem freshClass_shift {F : Matrix (Fin N) (Fin N) ℂ} {A c E r₀ s₀ v₀ r₁ x : ℝ}
    (h : FreshClass F A c E r₀ s₀ v₀) (hx : |x - E| ≤ r₀ - r₁) :
    FreshClass F A c x r₁ s₀ v₀ := by
  refine ⟨h.1, h.2.1, fun s hs y hy η hη => h.2.2 s hs y ?_ η hη⟩
  calc |y - E| = |(y - x) + (x - E)| := by ring_nf
    _ ≤ |y - x| + |x - E| := abs_add_le _ _
    _ ≤ r₀ := by linarith

/-- The canonical density `meanDensityReal` is a continuous version of `ρ_{F,c}`. -/
theorem meanDensityReal_isDensity (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) :
    freshMeanEigenvalueMeasure N c F =
      volume.withDensity (fun y => ENNReal.ofReal (meanDensityReal F c y)) := by
  rw [freshMeanEigenvalueMeasure_eq_withDensity hN hF hc]
  congr 1
  funext y
  rw [ofReal_meanDensityReal hN F c y]

/-!
## The summed Palm bound
-/

/-- **The `r = 1` Palm bound summed over all ranks, divided by `N`**:
`|q*Σ_F(x)q - ρ_{F,c}(x) q*Γ_F(x)q| ≤ (C₁ N^{-κ} ρ_{F,c}(x) + C₂ N⁻¹) q*Γ_F(x)q`, for every
deterministic `q`, uniformly over the class at `(c, x)`. -/
theorem sigma_palm_bound (hP : FreshPalmContract) (A c r₀ s₀ v₀ : ℝ)
    (hK : FreshConstants c r₀ s₀ v₀) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ N : ℕ, 0 < N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (x : ℝ), FreshClass F A c x r₀ s₀ v₀ → ∀ q : Fin N → ℂ,
        |quadForm (sigma F c x) q - meanDensityReal F c x * quadForm (freshGamma F c x) q| ≤
          (C₁ * (N : ℝ) ^ (-κ) * meanDensityReal F c x + C₂ * (N : ℝ)⁻¹) *
            quadForm (freshGamma F c x) q := by
  obtain ⟨κ, hκ, Cr, hCr⟩ := hP A c r₀ s₀ v₀ hK 1 le_rfl
  obtain ⟨CrK, hCrK⟩ := hCr 1 one_pos
  refine ⟨κ, hκ, |Cr|, |Cr| * |CrK|, abs_nonneg _, by positivity, fun N hN F x hFC q => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c := hK.1
  set γ := quadForm (freshGamma F c x) q
  have hγ : 0 ≤ γ := quadForm_freshGamma_nonneg F hc.le x q
  set ρ := meanDensityReal F c x
  have hρ : 0 ≤ ρ := meanDensityReal_nonneg F c x
  set Z : Fin N → ℝ := fun ℓ => ∫ A0, palmWeight F c x ℓ A0 ∂freshTracelessLaw N c
  set M : Fin N → ℝ := fun ℓ => ∫ A0, palmWeight F c x ℓ A0 * palmOverlap F q ℓ A0 ^ 1
    ∂freshTracelessLaw N c
  have hZ0 : ∀ ℓ, 0 ≤ Z ℓ := fun ℓ => integral_nonneg fun A0 => palmWeight_nonneg F c x ℓ A0
  have hb : ∀ ℓ, |M ℓ - γ * Z ℓ| ≤ Cr * ((N : ℝ) ^ (-κ) * Z ℓ + CrK * (N : ℝ)⁻¹) * γ := by
    intro ℓ
    have h := hCrK N hN F x hFC q ℓ
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one, Real.rpow_neg_one] at h
    simpa [M, Z, γ] using h
  have hM : ∑ ℓ, M ℓ = N * quadForm (sigma F c x) q := by
    rw [quadForm_sigma_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [M, palmOverlap, pow_one]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun A0 => ?_)
    simp only
    ring
  have hZs : ∑ ℓ, Z ℓ = N * ρ := sum_integral_palmWeight hN F c x
  have hsum : |N * quadForm (sigma F c x) q - N * ρ * γ| ≤
      N * ((|Cr| * (N : ℝ) ^ (-κ) * ρ + |Cr| * |CrK| * (N : ℝ)⁻¹) * γ) := by
    calc |N * quadForm (sigma F c x) q - N * ρ * γ| = |∑ ℓ, (M ℓ - γ * Z ℓ)| := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hM, hZs]; ring_nf
      _ ≤ ∑ ℓ, |M ℓ - γ * Z ℓ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ℓ, |Cr| * ((N : ℝ) ^ (-κ) * Z ℓ + |CrK| * (N : ℝ)⁻¹) * γ := by
          refine Finset.sum_le_sum fun ℓ _ => (hb ℓ).trans ?_
          have hp : 0 ≤ (N : ℝ) ^ (-κ) * Z ℓ := mul_nonneg (by positivity) (hZ0 ℓ)
          have h1 : Cr * ((N : ℝ) ^ (-κ) * Z ℓ + CrK * (N : ℝ)⁻¹) ≤
              |Cr| * ((N : ℝ) ^ (-κ) * Z ℓ + |CrK| * (N : ℝ)⁻¹) := by
            calc Cr * ((N : ℝ) ^ (-κ) * Z ℓ + CrK * (N : ℝ)⁻¹)
                ≤ |Cr * ((N : ℝ) ^ (-κ) * Z ℓ + CrK * (N : ℝ)⁻¹)| := le_abs_self _
              _ = |Cr| * |(N : ℝ) ^ (-κ) * Z ℓ + CrK * (N : ℝ)⁻¹| := abs_mul _ _
              _ ≤ |Cr| * ((N : ℝ) ^ (-κ) * Z ℓ + |CrK| * (N : ℝ)⁻¹) := by
                  gcongr
                  refine (abs_add_le _ _).trans ?_
                  rw [abs_of_nonneg hp, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N : ℝ)⁻¹)]
          exact mul_le_mul_of_nonneg_right h1 hγ
      _ = N * ((|Cr| * (N : ℝ) ^ (-κ) * ρ + |Cr| * |CrK| * (N : ℝ)⁻¹) * γ) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hZs,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hfac : N * quadForm (sigma F c x) q - N * ρ * γ =
      N * (quadForm (sigma F c x) q - ρ * γ) := by ring
  rw [hfac, abs_mul, abs_of_pos hNr] at hsum
  exact le_of_mul_le_mul_left hsum hNr

/-!
## Point-density input
-/

/-- From `PointDensityContract`: a uniform bound `ρ_{F,c}(x) ≤ v₀⁻¹/π + |ε'_N|` and
`|ρ_{F,c}(x) - r_{F,c}(x)| ≤ ε'_N` for the canonical continuous density. -/
theorem meanDensityReal_bounds (hPD : PointDensityContract) (A c r₀ s₀ v₀ : ℝ)
    (hK : FreshConstants c r₀ s₀ v₀) :
    ∃ ε' : ℕ → ℝ, Tendsto ε' atTop (𝓝 0) ∧ ∀ N : ℕ, 0 < N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (x : ℝ), FreshClass F A c x r₀ s₀ v₀ →
        |meanDensityReal F c x - (freshDyson F c x).im / Real.pi| ≤ ε' N ∧
          meanDensityReal F c x ≤ v₀⁻¹ / Real.pi + |ε' N| := by
  obtain ⟨ε', hε', h⟩ := hPD A c r₀ s₀ v₀ hK
  refine ⟨ε', hε', fun N hN F x hFC => ?_⟩
  have h1 := (h N hN F x hFC).2 (meanDensityReal F c) (continuous_meanDensityReal hN F c)
    (meanDensityReal_isDensity hN hFC.1 hK.1)
  refine ⟨h1, ?_⟩
  have hm := (freshDyson_im_bounds hK hFC).2
  have : (freshDyson F c x).im / Real.pi ≤ v₀⁻¹ / Real.pi :=
    div_le_div_of_nonneg_right hm Real.pi_pos.le
  have := le_abs_self (ε' N)
  have := (abs_le.1 h1).2
  linarith

/-!
## The global weighted density, regular class
-/

/-- **The global weighted density bound, second assertion.**
Fixed first: the norm exponent `A`, the constants `FreshConstants c r₀ s₀ v₀` of the regular
class, and `η`. Then there is `C` such that for every `N ≥ 1`, every `F` in the
regular class at `(c, e)` (`FreshClass F A c e r₀ s₀ v₀`) and every continuous matrix spectral
density `S` of `F + G`, `G ~ GUE_N(c/N)`: `(F - e + iη) S(e) (F - e - iη) ⪯ C I`.
`e` is the centre of the regularity window (other points of the window: `freshClass_shift`).
Existence and uniqueness: for every `N ≥ 1` and Hermitian `F` (in particular every `F` in the
class) a continuous matrix spectral density exists (`sigma F c`: `continuous_sigma`,
`isMatrixSpectralDensity_sigma`) and is unique (`eq_sigma_of_isMatrixSpectralDensity`), so the
quantification over continuous `S` is not vacuous; existence is bundled in
`globalWeightedDensity_general`.
Hypotheses: `FreshPalmContract`, `PointDensityContract`. -/
theorem globalWeightedDensity_regular (hP : FreshPalmContract) (hPD : PointDensityContract)
    (A c r₀ s₀ v₀ : ℝ) (hK : FreshConstants c r₀ s₀ v₀) (η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (e : ℝ),
      FreshClass F A c e r₀ s₀ v₀ →
      ∀ S : ℝ → Matrix (Fin N) (Fin N) ℂ, Continuous S → IsMatrixSpectralDensity N c F S →
        (((C : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
          (F - ((e : ℂ) - (η : ℂ) * Complex.I) • 1) * S e *
            (F - ((e : ℂ) + (η : ℂ) * Complex.I) • 1)).PosSemidef := by
  obtain ⟨κ, hκ, C₁, C₂, hC₁, hC₂, hpb⟩ := sigma_palm_bound hP A c r₀ s₀ v₀ hK
  obtain ⟨ε', hε', hpd⟩ := meanDensityReal_bounds hPD A c r₀ s₀ v₀ hK
  obtain ⟨Bε, hBε⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto ε' hε')
  have hc : 0 < c := hK.1
  have hv : 0 < v₀ := hK.2.2.2.2.2
  set ρmax := v₀⁻¹ / Real.pi + |Bε|
  have hρmax : 0 ≤ ρmax := by have := Real.pi_pos; positivity
  set D := (1 + C₁) * ρmax + C₂
  have hD : 0 ≤ D := by positivity
  set KΓ := c * (2 + (2 * c ^ 2 * ((c * v₀)⁻¹) ^ 2 + η ^ 2) / (c ^ 2 * v₀ ^ 2))
  have hKΓ : 0 ≤ KΓ := by positivity
  refine ⟨D * KΓ, mul_nonneg hD hKΓ, fun N hN F e hFC S hS hSd => ?_⟩
  have hF := hFC.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [eq_sigma_of_isMatrixSpectralDensity hN hF hc hS hSd, ← conjTranspose_sub_shift hF e η]
  refine posSemidef_smul_one_sub_of_le (sigma_isHermitian F c e) _ fun q => ?_
  set y := (F - ((e : ℂ) + (η : ℂ) * Complex.I) • 1) *ᵥ q
  set γ := quadForm (freshGamma F c e) y
  have hγ : 0 ≤ γ := quadForm_freshGamma_nonneg F hc.le e y
  set ρ := meanDensityReal F c e
  have hρ0 : 0 ≤ ρ := meanDensityReal_nonneg F c e
  have hρ : ρ ≤ ρmax := by
    have h := (hpd N hN F e hFC).2
    have hb : |ε' N| ≤ |Bε| := by
      have := hBε (ε' N) ⟨N, rfl⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    linarith
  have hpow : (N : ℝ) ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have h1 := hpb N hN F e hFC y
  have hσ : quadForm (sigma F c e) y ≤ D * γ := by
    have h2 := (abs_le.1 h1).2
    have h3 : (C₁ * (N : ℝ) ^ (-κ) * ρ + C₂ * (N : ℝ)⁻¹) ≤ C₁ * ρmax + C₂ := by
      have : C₁ * (N : ℝ) ^ (-κ) * ρ ≤ C₁ * 1 * ρmax := by
        gcongr
      have : C₂ * (N : ℝ)⁻¹ ≤ C₂ * 1 := by gcongr
      linarith
    have h4 : (C₁ * (N : ℝ) ^ (-κ) * ρ + C₂ * (N : ℝ)⁻¹) * γ ≤ (C₁ * ρmax + C₂) * γ :=
      mul_le_mul_of_nonneg_right h3 hγ
    have h5 : ρ * γ ≤ ρmax * γ := mul_le_mul_of_nonneg_right hρ hγ
    simp only [D]
    nlinarith
  -- the diagonal bound
  set m := freshDyson F c e
  have hm := freshDyson_im_bounds hK hFC
  have hmpos : 0 < m.im := lt_of_lt_of_le hv hm.1
  have hnorm : ‖m‖ ≤ (c * v₀)⁻¹ := (norm_freshDyson_le hF hN hc hmpos).trans
    (inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hm.1 hc.le))
  have hΓ : γ ≤ c * (2 + (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) / (c ^ 2 * m.im ^ 2)) * ∑ a, ‖q a‖ ^ 2 :=
    quadForm_gammaShape_le hF hc e η hmpos q
  have hratio : (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) / (c ^ 2 * m.im ^ 2) ≤
      (2 * c ^ 2 * ((c * v₀)⁻¹) ^ 2 + η ^ 2) / (c ^ 2 * v₀ ^ 2) := by
    gcongr
    · exact hm.1
  have hKm : c * (2 + (2 * c ^ 2 * ‖m‖ ^ 2 + η ^ 2) / (c ^ 2 * m.im ^ 2)) ≤ KΓ := by
    simp only [KΓ]; gcongr
  have hnq : 0 ≤ ∑ a, ‖q a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΓ' : γ ≤ KΓ * ∑ a, ‖q a‖ ^ 2 := hΓ.trans (mul_le_mul_of_nonneg_right hKm hnq)
  calc quadForm (sigma F c e) y ≤ D * γ := hσ
    _ ≤ D * (KΓ * ∑ a, ‖q a‖ ^ 2) := mul_le_mul_of_nonneg_left hΓ' hD
    _ = D * KΓ * ∑ a, ‖q a‖ ^ 2 := by ring

/-!
## The relative matrix density
-/

/-- The relative deviation `Σ_F(x) - r_{F,c}(x) Γ_F(x)` of a matrix-valued `S`. -/
def relativeDeviation (F : Matrix (Fin N) (Fin N) ℂ) (c x : ℝ) (S : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  S - (((freshDyson F c x).im / Real.pi : ℝ) : ℂ) • freshGamma F c x

/-- **The relative matrix density.** Fixed first: the norm exponent `A`,
`FreshConstants c r₀ s₀ v₀` of the regular class, and the radius `r₁ > 0` of the smaller
regularity interval. Then there is a deterministic `ε_N ≥ 0`, `ε_N → 0`, such that for every
`N ≥ 1`, every `F` in the regular class at `(c, E)` (`FreshClass F A c E r₀ s₀ v₀`), uniformly for
`|x - E| ≤ r₀ - r₁`, and every continuous matrix spectral density `S` of `F + G`
(`G ~ GUE_N(c/N)`): `-ε_N Γ_F(x) ⪯ S(x) - r_{F,c}(x) Γ_F(x) ⪯ ε_N Γ_F(x)` (Loewner order, no
dimension factor). Existence and uniqueness: for every `N ≥ 1` and Hermitian `F` (in particular
every `F` in the class) a continuous matrix spectral density exists (`sigma F c`:
`continuous_sigma`, `isMatrixSpectralDensity_sigma`) and is unique
(`eq_sigma_of_isMatrixSpectralDensity`), so the quantification over continuous `S` is not
vacuous; existence is bundled in `globalWeightedDensity_general`.
Hypotheses: `FreshPalmContract` (`r = 1`), `PointDensityContract`. -/
theorem relativeMatrixDensity (hP : FreshPalmContract) (hPD : PointDensityContract)
    (A c r₀ s₀ v₀ : ℝ) (hK : FreshConstants c r₀ s₀ v₀) {r₁ : ℝ} (hr₁ : 0 < r₁) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ N, 0 ≤ ε N) ∧ ∀ N : ℕ, 0 < N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      ∀ x : ℝ, |x - E| ≤ r₀ - r₁ →
      ∀ S : ℝ → Matrix (Fin N) (Fin N) ℂ, Continuous S → IsMatrixSpectralDensity N c F S →
        (((ε N : ℝ) : ℂ) • freshGamma F c x - relativeDeviation F c x (S x)).PosSemidef ∧
          (relativeDeviation F c x (S x) + ((ε N : ℝ) : ℂ) • freshGamma F c x).PosSemidef := by
  have hK₁ : FreshConstants c r₁ s₀ v₀ :=
    ⟨hK.1, hK.2.1, hr₁, hK.2.2.2.1, hK.2.2.2.2.1, hK.2.2.2.2.2⟩
  obtain ⟨κ, hκ, C₁, C₂, hC₁, hC₂, hpb⟩ := sigma_palm_bound hP A c r₁ s₀ v₀ hK₁
  obtain ⟨ε', hε', hpd⟩ := meanDensityReal_bounds hPD A c r₁ s₀ v₀ hK₁
  have hc : 0 < c := hK.1
  set ε : ℕ → ℝ := fun N => C₁ * (N : ℝ) ^ (-κ) * (v₀⁻¹ / Real.pi + |ε' N|) +
    C₂ * (N : ℝ)⁻¹ + |ε' N| with hεdef
  have hv : 0 < v₀ := hK.2.2.2.2.2
  have hε0 : ∀ N, 0 ≤ ε N := fun N => by
    have := Real.pi_pos
    have : 0 ≤ (N : ℝ) ^ (-κ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    simp only [hεdef]
    positivity
  refine ⟨ε, ?_, hε0, fun N hN F E hFC x hx S hS hSd => ?_⟩
  · have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-κ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
    have h3 : Tendsto (fun N => |ε' N|) atTop (𝓝 0) := by simpa using hε'.abs
    have := (((tendsto_const_nhds (x := C₁)).mul h1).mul
      ((tendsto_const_nhds (x := v₀⁻¹ / Real.pi)).add h3)).add
        ((tendsto_const_nhds (x := C₂)).mul h2) |>.add h3
    simpa [hεdef] using this
  have hFx := freshClass_shift (r₁ := r₁) hFC hx
  have hF := hFC.1
  rw [eq_sigma_of_isMatrixSpectralDensity hN hF hc hS hSd]
  set r := (freshDyson F c x).im / Real.pi
  set Γ := freshGamma F c x
  have hΓh : Γ.IsHermitian := freshGamma_isHermitian F hc.le x
  have hDh : (relativeDeviation F c x (sigma F c x)).IsHermitian :=
    (sigma_isHermitian F c x).sub (hΓh.smul (Complex.conj_ofReal r))
  have hεΓ : ((((ε N : ℝ)) : ℂ) • Γ).IsHermitian := hΓh.smul (Complex.conj_ofReal _)
  -- the quadratic-form bound
  have key : ∀ q : Fin N → ℂ, |quadForm (relativeDeviation F c x (sigma F c x)) q| ≤
      ε N * quadForm Γ q := by
    intro q
    have hγ : 0 ≤ quadForm Γ q := quadForm_freshGamma_nonneg F hc.le x q
    have hρ0 : 0 ≤ meanDensityReal F c x := meanDensityReal_nonneg F c x
    obtain ⟨hρr, hρ⟩ := hpd N hN F x hFx
    have h1 := hpb N hN F x hFx q
    have hpow : 0 ≤ (N : ℝ) ^ (-κ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    rw [relativeDeviation, quadForm_sub, quadForm_real_smul]
    have e1 : |quadForm (sigma F c x) q - r * quadForm Γ q| ≤
        |quadForm (sigma F c x) q - meanDensityReal F c x * quadForm Γ q| +
          |meanDensityReal F c x - r| * quadForm Γ q := by
      have : quadForm (sigma F c x) q - r * quadForm Γ q =
          (quadForm (sigma F c x) q - meanDensityReal F c x * quadForm Γ q) +
            (meanDensityReal F c x - r) * quadForm Γ q := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hγ]
    have e2 : |meanDensityReal F c x - r| ≤ |ε' N| := hρr.trans (le_abs_self _)
    have e3 : C₁ * (N : ℝ) ^ (-κ) * meanDensityReal F c x ≤
        C₁ * (N : ℝ) ^ (-κ) * (v₀⁻¹ / Real.pi + |ε' N|) := by gcongr
    have e4 : (C₁ * (N : ℝ) ^ (-κ) * meanDensityReal F c x + C₂ * (N : ℝ)⁻¹) * quadForm Γ q ≤
        (C₁ * (N : ℝ) ^ (-κ) * (v₀⁻¹ / Real.pi + |ε' N|) + C₂ * (N : ℝ)⁻¹) * quadForm Γ q :=
      mul_le_mul_of_nonneg_right (by linarith) hγ
    have e5 : |meanDensityReal F c x - r| * quadForm Γ q ≤ |ε' N| * quadForm Γ q :=
      mul_le_mul_of_nonneg_right e2 hγ
    calc |quadForm (sigma F c x) q - r * quadForm Γ q| ≤ _ := e1
      _ ≤ ε N * quadForm Γ q := by
          simp only [hεdef]
          nlinarith
  refine ⟨posSemidef_of_quadForm_nonneg (hεΓ.sub hDh) fun q => ?_,
    posSemidef_of_quadForm_nonneg (hDh.add hεΓ) fun q => ?_⟩
  · rw [quadForm_sub, quadForm_real_smul]
    linarith [(abs_le.1 (key q)).2]
  · rw [quadForm_add, quadForm_real_smul]
    linarith [(abs_le.1 (key q)).1]

/-- Congruence preserves both Loewner bounds: for every rectangular `B`,
`-ε Bᴴ Γ B ⪯ Bᴴ D B ⪯ ε Bᴴ Γ B` whenever `-εΓ ⪯ D ⪯ εΓ`. -/
theorem congr_two_sided {κ : Type*} [Fintype κ] {ε : ℝ} {Γ D : Matrix (Fin N) (Fin N) ℂ}
    (h : (((ε : ℝ) : ℂ) • Γ - D).PosSemidef ∧ (D + ((ε : ℝ) : ℂ) • Γ).PosSemidef)
    (B : Matrix (Fin N) κ ℂ) :
    (((ε : ℝ) : ℂ) • (Bᴴ * Γ * B) - Bᴴ * D * B).PosSemidef ∧
      (Bᴴ * D * B + ((ε : ℝ) : ℂ) • (Bᴴ * Γ * B)).PosSemidef := by
  have e1 : Bᴴ * (((ε : ℝ) : ℂ) • Γ - D) * B = ((ε : ℝ) : ℂ) • (Bᴴ * Γ * B) - Bᴴ * D * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : Bᴴ * (D + ((ε : ℝ) : ℂ) • Γ) * B = Bᴴ * D * B + ((ε : ℝ) : ℂ) • (Bᴴ * Γ * B) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  exact ⟨e1 ▸ h.1.conjTranspose_mul_mul_same B, e2 ▸ h.2.conjTranspose_mul_mul_same B⟩

/-- **The relative matrix density, congruence form**: the two-sided bound of
`relativeMatrixDensity`, with the same `ε_N`, after multiplication on both sides by any
deterministic rectangular matrix `B` (no norm restriction on `B`).
Existence and uniqueness: for every `N ≥ 1` and Hermitian `F` (in particular every `F` in the
class) a continuous matrix spectral density exists (`sigma F c`: `continuous_sigma`,
`isMatrixSpectralDensity_sigma`) and is unique (`eq_sigma_of_isMatrixSpectralDensity`), so the
quantification over continuous `S` is not vacuous; existence is bundled in
`globalWeightedDensity_general`.
Hypotheses: as `relativeMatrixDensity`. -/
theorem relativeMatrixDensity_congr (hP : FreshPalmContract) (hPD : PointDensityContract)
    (A c r₀ s₀ v₀ : ℝ) (hK : FreshConstants c r₀ s₀ v₀) {r₁ : ℝ} (hr₁ : 0 < r₁) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ N, 0 ≤ ε N) ∧ ∀ N : ℕ, 0 < N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      ∀ x : ℝ, |x - E| ≤ r₀ - r₁ →
      ∀ S : ℝ → Matrix (Fin N) (Fin N) ℂ, Continuous S → IsMatrixSpectralDensity N c F S →
      ∀ (κ : Type) [Fintype κ] (B : Matrix (Fin N) κ ℂ),
        (((ε N : ℝ) : ℂ) • (Bᴴ * freshGamma F c x * B) -
            Bᴴ * relativeDeviation F c x (S x) * B).PosSemidef ∧
          (Bᴴ * relativeDeviation F c x (S x) * B +
            ((ε N : ℝ) : ℂ) • (Bᴴ * freshGamma F c x * B)).PosSemidef := by
  obtain ⟨ε, hε, hε0, h⟩ := relativeMatrixDensity hP hPD A c r₀ s₀ v₀ hK hr₁
  exact ⟨ε, hε, hε0, fun N hN F E hFC x hx S hS hSd κ _ B =>
    congr_two_sided (h N hN F E hFC x hx S hS hSd) B⟩

end BlockBand.Critical.WeightedDensity
