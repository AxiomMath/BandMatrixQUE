module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Definitions for the radial Gaussian comparison

The hyperbolic heat kernel `gcHypKernel T c` (through McKean's integral representation
`gcMcKeanG`), its angular average `gcHypRadial T x x'` in the coordinate `x = (cosh r - 1)/2`
(`gcX`), the planar Gaussian angular average `gcEuclRadial T r r'` with the weight
`√(σ(r)σ(r'))`, `σ(s) = s/sinh s` (`gcSdivSinh`), and the comparison statement
`GcLbkHypRadialGaussCompare`: for every `T₀ > 0` there are `c, C > 0` with
`c · gcEuclRadial ≤ gcHypRadial ≤ C · gcEuclRadial` for `0 < T ≤ T₀` and `r, r' ≥ 0`.
Basic positivity, continuity and integrability lemmas follow.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-!
### Definitions
-/

/-- `s / sinh s`, continuously extended by `1` at `s = 0`. -/
def gcSdivSinh (s : ℝ) : ℝ := if s = 0 then 1 else s / Real.sinh s

/-- McKean's integrand after the substitution `cosh s = w`:
`G_T(w) = 2 (s / sinh s) e^{-s²/(4T)}`, `s = arcosh w`.
-/
def gcMcKeanG (T w : ℝ) : ℝ :=
  2 * gcSdivSinh (Real.arcosh w) * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T))

/-- McKean's heat kernel of `e^{TΔ}` on `H²` as a function of `c = cosh ρ`. -/
def gcHypKernel (T c : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ) *
    ∫ v in Ioi (0 : ℝ), gcMcKeanG T (max c 1 + v ^ 2)

/-- The hyperbolic law of cosines in the coordinates `x = (cosh r - 1)/2`. -/
def gcHypCos (x x' φ : ℝ) : ℝ :=
  (1 + 2 * x) * (1 + 2 * x') - 4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))) * Real.cos φ

/-- The angle-averaged hyperbolic kernel, density relative to `dx'`. -/
def gcHypRadial (T x x' : ℝ) : ℝ :=
  2 * ∫ φ in (0 : ℝ)..(2 * π), gcHypKernel T (gcHypCos x x' φ)

/-- The radial coordinate change `x(r) = (cosh r - 1)/2`. -/
def gcX (r : ℝ) : ℝ := (Real.cosh r - 1) / 2

/-- The `h`-conjugated planar radial heat kernel as a density in `x'`. -/
def gcEuclRadial (T r r' : ℝ) : ℝ :=
  2 / (4 * π * T) * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
    ∫ φ in Ioo (-π) π, Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T))

/-- Two-sided Gaussian comparison of the hyperbolic radial kernel. -/
def GcLbkHypRadialGaussCompare : Prop :=
  ∀ T₀ : ℝ, 0 < T₀ → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ T ∈ Ioc 0 T₀, ∀ r r' : ℝ, 0 ≤ r → 0 ≤ r' →
      c * gcEuclRadial T r r' ≤ gcHypRadial T (gcX r) (gcX r') ∧
        gcHypRadial T (gcX r) (gcX r') ≤ C * gcEuclRadial T r r'

/-!
### Basic lemmas
-/

theorem gc_sdivSinh_continuous : Continuous gcSdivSinh := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    rw [← continuousWithinAt_compl_self]
    have hd : Tendsto (fun t => t⁻¹ • (Real.sinh (0 + t) - Real.sinh 0)) (𝓝[≠] 0)
        (𝓝 (Real.cosh 0)) := hasDerivAt_iff_tendsto_slope_zero.1 (Real.hasDerivAt_sinh 0)
    simp only [zero_add, Real.sinh_zero, sub_zero, smul_eq_mul, Real.cosh_zero] at hd
    have hinv := hd.inv₀ one_ne_zero
    rw [inv_one] at hinv
    show Tendsto gcSdivSinh (𝓝[≠] 0) (𝓝 (gcSdivSinh 0))
    rw [show gcSdivSinh 0 = 1 by simp [gcSdivSinh]]
    refine hinv.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht' : t ≠ 0 := ht
    simp only [gcSdivSinh, ht', ↓reduceIte]
    rw [mul_inv, inv_inv, div_eq_mul_inv]
  · have hsh : Real.sinh s ≠ 0 := fun h => hs (Real.sinh_eq_zero.1 h)
    refine (continuousAt_id.div Real.continuous_sinh.continuousAt hsh).congr ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    have ht' : t ≠ 0 := ht
    simp [gcSdivSinh, ht']

theorem gc_sdivSinh_pos (s : ℝ) : 0 < gcSdivSinh s := by
  unfold gcSdivSinh
  split_ifs with hs
  · exact one_pos
  · rcases lt_or_gt_of_ne hs with h | h
    · exact div_pos_of_neg_of_neg h (Real.sinh_neg_iff.2 h)
    · exact div_pos h (Real.sinh_pos_iff.2 h)

theorem gc_sdivSinh_le_one (s : ℝ) : gcSdivSinh s ≤ 1 := by
  unfold gcSdivSinh
  split_ifs with hs
  · exact le_rfl
  · rcases lt_or_gt_of_ne hs with h | h
    · exact (div_le_one_of_neg (Real.sinh_neg_iff.2 h)).2 (Real.sinh_le_self_iff.2 h.le)
    · exact (div_le_one (Real.sinh_pos_iff.2 h)).2 (Real.self_le_sinh_iff.2 h.le)

theorem gc_mcKeanG_pos (T w : ℝ) : 0 < gcMcKeanG T w := by
  unfold gcMcKeanG
  have := gc_sdivSinh_pos (Real.arcosh w)
  positivity

theorem gc_mcKeanG_le {T w v : ℝ} (hT : 0 < T) (hw : 1 + v ^ 2 ≤ w) :
    gcMcKeanG T w ≤ 2 * Real.exp T * (1 + v ^ 2)⁻¹ := by
  have hv : (0 : ℝ) < 1 + v ^ 2 := by positivity
  have hw0 : 0 < w := lt_of_lt_of_le hv hw
  have hw1 : 1 ≤ w := le_trans (by nlinarith [sq_nonneg v]) hw
  have ha : Real.log (1 + v ^ 2) ≤ Real.arcosh w := by
    refine (Real.log_le_log hv hw).trans ?_
    rw [Real.log_le_iff_le_exp hw0, Real.exp_arcosh hw1]
    linarith [Real.sqrt_nonneg (w ^ 2 - 1)]
  have hexp : Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) ≤ Real.exp T * (1 + v ^ 2)⁻¹ := by
    have hinv : (1 + v ^ 2)⁻¹ = Real.exp (-Real.log (1 + v ^ 2)) := by
      rw [Real.exp_neg, Real.exp_log hv]
    rw [hinv, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h4 : Real.arcosh w ≤ (Real.arcosh w) ^ 2 / (4 * T) + T := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Real.arcosh w - 2 * T)]
    have : -(Real.arcosh w) ^ 2 / (4 * T) = -((Real.arcosh w) ^ 2 / (4 * T)) := by ring
    linarith
  have hσ0 := (gc_sdivSinh_pos (Real.arcosh w)).le
  have hσ1 := gc_sdivSinh_le_one (Real.arcosh w)
  unfold gcMcKeanG
  calc 2 * gcSdivSinh (Real.arcosh w) * Real.exp (-(Real.arcosh w) ^ 2 / (4 * T))
      ≤ 2 * 1 * (Real.exp T * (1 + v ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

theorem gc_arc_continuous : Continuous fun p : ℝ × ℝ => Real.arcosh (max p.1 1 + p.2 ^ 2) :=
  Real.continuousOn_arcosh.comp_continuous (by fun_prop) fun p => by
    simp only [mem_Ici]
    nlinarith [le_max_right p.1 1, sq_nonneg p.2]

theorem gc_G_continuous (T : ℝ) :
    Continuous fun p : ℝ × ℝ => gcMcKeanG T (max p.1 1 + p.2 ^ 2) := by
  unfold gcMcKeanG
  have h := gc_arc_continuous
  exact (continuous_const.mul (gc_sdivSinh_continuous.comp h)).mul
    (Real.continuous_exp.comp ((h.pow 2).neg.div_const _))

theorem gc_G_le {T : ℝ} (hT : 0 < T) (c v : ℝ) :
    ‖gcMcKeanG T (max c 1 + v ^ 2)‖ ≤ 2 * Real.exp T * (1 + v ^ 2)⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_pos (gc_mcKeanG_pos _ _)]
  exact gc_mcKeanG_le hT (by linarith [le_max_right c 1])

theorem gc_integrableOn_G {T : ℝ} (hT : 0 < T) (c : ℝ) :
    IntegrableOn (fun v => gcMcKeanG T (max c 1 + v ^ 2)) (Ioi 0) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * Real.exp T)).integrableOn
    ((gc_G_continuous T).comp (continuous_const.prodMk continuous_id :
      Continuous fun v : ℝ => (c, v))).aestronglyMeasurable (ae_of_all _ fun v => gc_G_le hT c v)

theorem gc_hypKernel_continuous {T : ℝ} (hT : 0 < T) : Continuous (gcHypKernel T) := by
  unfold gcHypKernel
  refine continuous_const.mul ?_
  refine continuous_of_dominated (bound := fun v => 2 * Real.exp T * (1 + v ^ 2)⁻¹)
    (fun c => ?_) (fun c => ae_of_all _ fun v => gc_G_le hT c v)
    (integrable_inv_one_add_sq.const_mul _).integrableOn
    (ae_of_all _ fun v => (gc_G_continuous T).comp (continuous_id.prodMk continuous_const :
      Continuous fun c : ℝ => (c, v)))
  exact ((gc_G_continuous T).comp (continuous_const.prodMk continuous_id :
    Continuous fun v : ℝ => (c, v))).aestronglyMeasurable

theorem gc_hypKernel_pos {T : ℝ} (hT : 0 < T) (c : ℝ) : 0 < gcHypKernel T c := by
  unfold gcHypKernel
  have hb : 0 < 4 * π * T := mul_pos (mul_pos (by norm_num) Real.pi_pos) hT
  have h1 : 0 < Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ) := by
    have := Real.rpow_pos_of_pos hb (3 / 2 : ℝ)
    positivity
  refine mul_pos h1 ?_
  rw [integral_pos_iff_support_of_nonneg (fun v => (gc_mcKeanG_pos _ _).le)
    (gc_integrableOn_G hT c)]
  have : Function.support (fun v => gcMcKeanG T (max c 1 + v ^ 2)) = univ := by
    ext v
    simp [(gc_mcKeanG_pos T _).ne']
  rw [this]
  simp

end BlockBand.Diffusion
