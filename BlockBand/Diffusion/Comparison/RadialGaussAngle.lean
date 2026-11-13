module

public import BlockBand.Diffusion.Comparison.RadialGaussPole
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The angle change of variables `ψ ↦ φ` (package K-B′)

For `r, r' > 0` put `A = cosh r cosh r'`, `B = sinh r sinh r'` and
`y(ψ) = r² + r'² - 2rr' cos ψ` (`gcAngY`, the squared Euclidean distance). The map
`Φ(ψ) = arccos((A - cosh √y(ψ))/B)` (`gcAngPhi`) is the angle at which the hyperbolic law of
cosines produces the same distance: `A - B cos Φ(ψ) = cosh √y(ψ)`. It is a strictly increasing
bijection of `(0, π)` with explicit derivative `gcAngPhiD`, so (`gc_half_hyp_eq`)

`∫_{(0,π)} K(A - B cos φ) dφ = ∫_{(0,π)} Φ'(ψ) K(cosh √y(ψ)) dψ`.

**Jacobian bounds** (`gc_angJac_lower`, `gc_angJac_upper`), with `σ = gcSdivSinh`,
`ρ = √y(ψ)`, `δ = |r - r'|`:

`√(σ(r)σ(r')) cos(ψ/2) ≤ Φ'(ψ) √σ(ρ) ≤ √(σ(r)σ(r')) e^{(ρ - δ)/2}`.

Writing `P = cosh ρ - cosh δ`, `Q = cosh(r+r') - cosh ρ`, `u = 1 - cos ψ`, `w = 1 + cos ψ`, one has
`Φ'² σ(ρ) = sinh ρ (rr')² uw / (ρ P Q)` and `σ(r)σ(r') = rr'/B`, `2B = P + Q`; both bounds then
follow from the tangent-line inequalities `gc_cosh_sub_le`, `gc_le_cosh_sub` and
`σ(δ) ≤ σ(ρ)e^{ρ-δ}`. (The ratio `Φ'√σ(ρ)/√(σ(r)σ(r'))` is unbounded as `r + r' → ∞` with `ψ`
fixed, so a bounded pointwise comparison is impossible; the Gaussian factor absorbs the growth.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set Real

/-- The squared planar distance `r² + r'² - 2rr' cos ψ`. -/
def gcAngY (r r' ψ : ℝ) : ℝ := r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos ψ

/-- `cos Φ(ψ) = (A - cosh √y(ψ)) / B`. -/
def gcAngZ (r r' ψ : ℝ) : ℝ :=
  (Real.cosh r * Real.cosh r' - Real.cosh (Real.sqrt (gcAngY r r' ψ))) /
    (Real.sinh r * Real.sinh r')

/-- The angle substitution `Φ(ψ) = arccos((A - cosh √y(ψ)) / B)`. -/
def gcAngPhi (r r' ψ : ℝ) : ℝ := Real.arccos (gcAngZ r r' ψ)

/-- The derivative of `gcAngPhi` on `(0, π)`. -/
def gcAngPhiD (r r' ψ : ℝ) : ℝ :=
  Real.sinh (Real.sqrt (gcAngY r r' ψ)) * (r * r' * Real.sin ψ) /
    (Real.sqrt (gcAngY r r' ψ) *
      (Real.sinh r * Real.sinh r' * Real.sqrt (1 - gcAngZ r r' ψ ^ 2)))

theorem gc_hypCos_X {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (φ : ℝ) :
    gcHypCos (gcX r) (gcX r') φ =
      Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ := by
  unfold gcHypCos gcX
  have h1 : (Real.cosh r - 1) / 2 * (1 + (Real.cosh r - 1) / 2) = (Real.sinh r / 2) ^ 2 := by
    linear_combination (1 / 4) * Real.cosh_sq r
  have h2 : (Real.cosh r' - 1) / 2 * (1 + (Real.cosh r' - 1) / 2) = (Real.sinh r' / 2) ^ 2 := by
    linear_combination (1 / 4) * Real.cosh_sq r'
  have hs : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.2 hr
  have hs' : 0 ≤ Real.sinh r' := Real.sinh_nonneg_iff.2 hr'
  rw [h1, h2, show (Real.sinh r / 2) ^ 2 * (Real.sinh r' / 2) ^ 2 =
    (Real.sinh r * Real.sinh r' / 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  ring

theorem gc_angY_sub (r r' ψ : ℝ) :
    gcAngY r r' ψ - (r - r') ^ 2 = 2 * r * r' * (1 - Real.cos ψ) := by
  unfold gcAngY; ring

theorem gc_angY_sub' (r r' ψ : ℝ) :
    (r + r') ^ 2 - gcAngY r r' ψ = 2 * r * r' * (1 + Real.cos ψ) := by
  unfold gcAngY; ring

theorem gc_angY_bounds {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (ψ : ℝ) :
    (r - r') ^ 2 ≤ gcAngY r r' ψ ∧ gcAngY r r' ψ ≤ (r + r') ^ 2 := by
  have h1 := gc_angY_sub r r' ψ
  have h2 := gc_angY_sub' r r' ψ
  have hc1 := Real.cos_le_one ψ
  have hc2 := Real.neg_one_le_cos ψ
  have hrr : 0 ≤ r * r' := mul_nonneg hr hr'
  constructor <;> nlinarith

theorem gc_cos_mem_Ioo {ψ : ℝ} (hψ : ψ ∈ Ioo 0 π) : -1 < Real.cos ψ ∧ Real.cos ψ < 1 := by
  constructor
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi hψ.1.le le_rfl hψ.2
    rwa [Real.cos_pi] at this
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hψ.2.le hψ.1
    rwa [Real.cos_zero] at this

theorem gc_angY_bounds_strict {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') {ψ : ℝ}
    (hψ : ψ ∈ Ioo 0 π) : (r - r') ^ 2 < gcAngY r r' ψ ∧ gcAngY r r' ψ < (r + r') ^ 2 := by
  have h1 := gc_angY_sub r r' ψ
  have h2 := gc_angY_sub' r r' ψ
  obtain ⟨hc1, hc2⟩ := gc_cos_mem_Ioo hψ
  have hrr : 0 < r * r' := mul_pos hr hr'
  constructor <;> nlinarith

theorem gc_ang_sqrt_bounds {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (ψ : ℝ) :
    |r - r'| ≤ Real.sqrt (gcAngY r r' ψ) ∧ Real.sqrt (gcAngY r r' ψ) ≤ r + r' := by
  obtain ⟨h1, h2⟩ := gc_angY_bounds hr hr' ψ
  refine ⟨Real.abs_le_sqrt h1, ?_⟩
  calc Real.sqrt (gcAngY r r' ψ) ≤ Real.sqrt ((r + r') ^ 2) := Real.sqrt_le_sqrt h2
    _ = r + r' := Real.sqrt_sq (by positivity)

theorem gc_ang_sqrt_bounds_strict {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') {ψ : ℝ}
    (hψ : ψ ∈ Ioo 0 π) :
    |r - r'| < Real.sqrt (gcAngY r r' ψ) ∧ Real.sqrt (gcAngY r r' ψ) < r + r' := by
  obtain ⟨h1, h2⟩ := gc_angY_bounds_strict hr hr' hψ
  refine ⟨(Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; exact h1), ?_⟩
  exact (Real.sqrt_lt' (by positivity)).2 h2

theorem gc_sinh_mul_pos {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    0 < Real.sinh r * Real.sinh r' :=
  mul_pos (Real.sinh_pos_iff.2 hr) (Real.sinh_pos_iff.2 hr')

theorem gc_cosh_abs_sub (r r' : ℝ) :
    Real.cosh |r - r'| = Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' := by
  rw [Real.cosh_abs, Real.cosh_sub]

theorem gc_angZ_bounds {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ψ : ℝ) :
    -1 ≤ gcAngZ r r' ψ ∧ gcAngZ r r' ψ ≤ 1 := by
  have hB := gc_sinh_mul_pos hr hr'
  obtain ⟨h1, h2⟩ := gc_ang_sqrt_bounds hr.le hr'.le ψ
  have hρ := Real.sqrt_nonneg (gcAngY r r' ψ)
  have c1 : Real.cosh |r - r'| ≤ Real.cosh (Real.sqrt (gcAngY r r' ψ)) := by
    rw [Real.cosh_le_cosh, abs_abs, abs_of_nonneg hρ]; exact h1
  have c2 : Real.cosh (Real.sqrt (gcAngY r r' ψ)) ≤ Real.cosh (r + r') := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hρ, abs_of_nonneg (by positivity)]; exact h2
  rw [gc_cosh_abs_sub] at c1
  rw [Real.cosh_add] at c2
  unfold gcAngZ
  constructor
  · rw [le_div_iff₀ hB]; linarith
  · rw [div_le_one hB]; linarith

theorem gc_angZ_bounds_strict {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') {ψ : ℝ}
    (hψ : ψ ∈ Ioo 0 π) : -1 < gcAngZ r r' ψ ∧ gcAngZ r r' ψ < 1 := by
  have hB := gc_sinh_mul_pos hr hr'
  obtain ⟨h1, h2⟩ := gc_ang_sqrt_bounds_strict hr hr' hψ
  have hρ := Real.sqrt_nonneg (gcAngY r r' ψ)
  have c1 : Real.cosh |r - r'| < Real.cosh (Real.sqrt (gcAngY r r' ψ)) := by
    rw [Real.cosh_lt_cosh, abs_abs, abs_of_nonneg hρ]; exact h1
  have c2 : Real.cosh (Real.sqrt (gcAngY r r' ψ)) < Real.cosh (r + r') := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg hρ, abs_of_nonneg (by positivity)]; exact h2
  rw [gc_cosh_abs_sub] at c1
  rw [Real.cosh_add] at c2
  unfold gcAngZ
  constructor
  · rw [lt_div_iff₀ hB]; linarith
  · rw [div_lt_one hB]; linarith

theorem gc_angPhi_zero {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') : gcAngPhi r r' 0 = 0 := by
  have hB := gc_sinh_mul_pos hr hr'
  unfold gcAngPhi gcAngZ gcAngY
  rw [Real.cos_zero, show r ^ 2 + r' ^ 2 - 2 * r * r' * 1 = (r - r') ^ 2 by ring,
    Real.sqrt_sq_eq_abs, gc_cosh_abs_sub,
    show Real.cosh r * Real.cosh r' - (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r')
      = Real.sinh r * Real.sinh r' by ring, div_self hB.ne', Real.arccos_one]

theorem gc_angPhi_pi {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') : gcAngPhi r r' π = π := by
  have hB := gc_sinh_mul_pos hr hr'
  unfold gcAngPhi gcAngZ gcAngY
  rw [Real.cos_pi, show r ^ 2 + r' ^ 2 - 2 * r * r' * -1 = (r + r') ^ 2 by ring,
    Real.sqrt_sq (by positivity), Real.cosh_add,
    show Real.cosh r * Real.cosh r' - (Real.cosh r * Real.cosh r' + Real.sinh r * Real.sinh r')
      = -(Real.sinh r * Real.sinh r') by ring, neg_div, div_self hB.ne', Real.arccos_neg_one]

theorem gc_angZ_continuous (r r' : ℝ) : Continuous (gcAngZ r r') := by
  unfold gcAngZ gcAngY
  fun_prop

theorem gc_angPhi_continuous (r r' : ℝ) : Continuous (gcAngPhi r r') :=
  Real.continuous_arccos.comp (gc_angZ_continuous r r')

theorem gc_angPhi_hasDerivAt {r r' ψ : ℝ} (hr : 0 < r) (hr' : 0 < r') (hψ : ψ ∈ Ioo 0 π) :
    HasDerivAt (gcAngPhi r r') (gcAngPhiD r r' ψ) ψ := by
  have hB := gc_sinh_mul_pos hr hr'
  have hy : HasDerivAt (gcAngY r r') (2 * r * r' * Real.sin ψ) ψ := by
    have h := (hasDerivAt_const ψ (r ^ 2 + r' ^ 2)).sub
      ((Real.hasDerivAt_cos ψ).const_mul (2 * r * r'))
    have e : gcAngY r r' = fun x => r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos x := rfl
    rw [e]
    convert h using 1
    ring
  obtain ⟨hδ, _⟩ := gc_ang_sqrt_bounds_strict hr hr' hψ
  have hρ : 0 < Real.sqrt (gcAngY r r' ψ) := lt_of_le_of_lt (abs_nonneg _) hδ
  have hy0 : gcAngY r r' ψ ≠ 0 := fun h => by rw [h, Real.sqrt_zero] at hρ; exact lt_irrefl _ hρ
  have hz := ((hy.sqrt hy0).cosh.const_sub (Real.cosh r * Real.cosh r')).div_const
    (Real.sinh r * Real.sinh r')
  obtain ⟨hz1, hz2⟩ := gc_angZ_bounds_strict hr hr' hψ
  have ha := (Real.hasDerivAt_arccos hz1.ne' hz2.ne).comp ψ hz
  have hS : 0 < Real.sqrt (1 - gcAngZ r r' ψ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  refine HasDerivAt.congr_deriv ha ?_
  unfold gcAngPhiD
  simp only [gcAngZ] at hS ⊢
  field_simp

theorem gc_angPhiD_pos {r r' ψ : ℝ} (hr : 0 < r) (hr' : 0 < r') (hψ : ψ ∈ Ioo 0 π) :
    0 < gcAngPhiD r r' ψ := by
  have hB := gc_sinh_mul_pos hr hr'
  obtain ⟨hδ, _⟩ := gc_ang_sqrt_bounds_strict hr hr' hψ
  have hρ : 0 < Real.sqrt (gcAngY r r' ψ) := lt_of_le_of_lt (abs_nonneg _) hδ
  obtain ⟨hz1, hz2⟩ := gc_angZ_bounds_strict hr hr' hψ
  have hS : 0 < Real.sqrt (1 - gcAngZ r r' ψ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hsin := Real.sin_pos_of_pos_of_lt_pi hψ.1 hψ.2
  have hsh := Real.sinh_pos_iff.2 hρ
  unfold gcAngPhiD
  positivity

theorem gc_angPhi_strictMonoOn {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    StrictMonoOn (gcAngPhi r r') (Icc 0 π) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 π) (gc_angPhi_continuous r r').continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(gc_angPhi_hasDerivAt hr hr' hx).deriv]
  exact gc_angPhiD_pos hr hr' hx

theorem gc_angPhi_image {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    gcAngPhi r r' '' Ioo 0 π = Ioo 0 π := by
  have hpi := Real.pi_pos
  have hm := gc_angPhi_strictMonoOn hr hr'
  apply Subset.antisymm
  · rintro _ ⟨ψ, hψ, rfl⟩
    have h0 := hm ⟨le_rfl, hpi.le⟩ ⟨hψ.1.le, hψ.2.le⟩ hψ.1
    have h1 := hm ⟨hψ.1.le, hψ.2.le⟩ ⟨hpi.le, le_rfl⟩ hψ.2
    rw [gc_angPhi_zero hr hr'] at h0
    rw [gc_angPhi_pi hr hr'] at h1
    exact ⟨h0, h1⟩
  · have := intermediate_value_Ioo hpi.le (gc_angPhi_continuous r r').continuousOn
    rwa [gc_angPhi_zero hr hr', gc_angPhi_pi hr hr'] at this

theorem gc_cos_angPhi {r r' ψ : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos (gcAngPhi r r' ψ) =
      Real.cosh (Real.sqrt (gcAngY r r' ψ)) := by
  have hB := gc_sinh_mul_pos hr hr'
  obtain ⟨h1, h2⟩ := gc_angZ_bounds hr hr' ψ
  unfold gcAngPhi
  rw [Real.cos_arccos h1 h2]
  unfold gcAngZ
  field_simp
  ring

/-- **The change of variables** `φ = Φ(ψ)` in the half-angle hyperbolic integral. -/
theorem gc_half_hyp_eq {T r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    ∫ φ in Ioo 0 π, gcHypKernel T
        (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) =
      ∫ ψ in Ioo 0 π, gcAngPhiD r r' ψ * gcHypKernel T (Real.cosh (Real.sqrt (gcAngY r r' ψ))) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (gc_angPhi_hasDerivAt hr hr' hx).hasDerivWithinAt)
    ((gc_angPhi_strictMonoOn hr hr').injOn.mono Ioo_subset_Icc_self)
    (fun φ => gcHypKernel T
      (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ))
  rw [gc_angPhi_image hr hr'] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun ψ hψ => ?_
  simp only [smul_eq_mul]
  rw [abs_of_pos (gc_angPhiD_pos hr hr' hψ), gc_cos_angPhi hr hr']

theorem gc_half_hyp_integrableOn {T r r' : ℝ} (hT : 0 < T) (hr : 0 < r) (hr' : 0 < r') :
    IntegrableOn
      (fun ψ => gcAngPhiD r r' ψ * gcHypKernel T (Real.cosh (Real.sqrt (gcAngY r r' ψ))))
      (Ioo 0 π) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (gc_angPhi_hasDerivAt hr hr' hx).hasDerivWithinAt)
    ((gc_angPhi_strictMonoOn hr hr').injOn.mono Ioo_subset_Icc_self)
    (fun φ => gcHypKernel T
      (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ))
  rw [gc_angPhi_image hr hr'] at h
  have hg : Continuous fun φ => gcHypKernel T
      (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) :=
    (gc_hypKernel_continuous hT).comp (by fun_prop)
  have h2 := h.1 ((hg.integrableOn_Icc (a := 0) (b := π)).mono_set Ioo_subset_Icc_self)
  refine h2.congr_fun (fun ψ hψ => ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  rw [abs_of_pos (gc_angPhiD_pos hr hr' hψ), gc_cos_angPhi hr hr']

theorem gc_sdivSinh_mul_eq {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    gcSdivSinh r * gcSdivSinh r' = r * r' / (Real.sinh r * Real.sinh r') := by
  rw [gc_sdivSinh_of_ne hr.ne', gc_sdivSinh_of_ne hr'.ne', div_mul_div_comm]

/-- The squared Jacobian bounds. -/
theorem gc_angJac_sq {r r' ψ : ℝ} (hr : 0 < r) (hr' : 0 < r') (hψ : ψ ∈ Ioo 0 π) :
    r * r' / (Real.sinh r * Real.sinh r') * ((1 + Real.cos ψ) / 2) ≤
        gcAngPhiD r r' ψ ^ 2 * gcSdivSinh (Real.sqrt (gcAngY r r' ψ)) ∧
      gcAngPhiD r r' ψ ^ 2 * gcSdivSinh (Real.sqrt (gcAngY r r' ψ)) ≤
        r * r' / (Real.sinh r * Real.sinh r') *
          (gcSdivSinh |r - r'| / gcSdivSinh (Real.sqrt (gcAngY r r' ψ))) := by
  have hB := gc_sinh_mul_pos hr hr'
  have hrr : 0 < r * r' := mul_pos hr hr'
  obtain ⟨hδρ, hρΔ⟩ := gc_ang_sqrt_bounds_strict hr hr' hψ
  obtain ⟨hz1, hz2⟩ := gc_angZ_bounds_strict hr hr' hψ
  obtain ⟨hc1, hc2⟩ := gc_cos_mem_Ioo hψ
  have hyu := gc_angY_sub r r' ψ
  have hyw := gc_angY_sub' r r' ψ
  have hy0 : 0 ≤ gcAngY r r' ψ := le_trans (sq_nonneg _) (gc_angY_bounds hr.le hr'.le ψ).1
  have hρ2 : Real.sqrt (gcAngY r r' ψ) ^ 2 = gcAngY r r' ψ := Real.sq_sqrt hy0
  set y := gcAngY r r' ψ
  set ρ := Real.sqrt y
  set A := Real.cosh r * Real.cosh r'
  set B := Real.sinh r * Real.sinh r'
  set z := gcAngZ r r' ψ with hz_def
  set δ := |r - r'|
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hρ : 0 < ρ := lt_of_le_of_lt hδ0 hδρ
  have hδ2 : δ ^ 2 = (r - r') ^ 2 := sq_abs _
  have hcδ : Real.cosh δ = A - B := gc_cosh_abs_sub r r'
  have hcΔ : Real.cosh (r + r') = A + B := Real.cosh_add r r'
  set c := Real.cosh ρ
  set P := c - Real.cosh δ
  set Q := Real.cosh (r + r') - c
  have hP : 0 < P := by
    have : Real.cosh δ < c := by
      rw [Real.cosh_lt_cosh, abs_of_nonneg hδ0, abs_of_pos hρ]; exact hδρ
    simp only [P]; linarith
  have hQ : 0 < Q := by
    have : c < Real.cosh (r + r') := by
      rw [Real.cosh_lt_cosh, abs_of_pos hρ, abs_of_pos (by positivity)]; exact hρΔ
    simp only [Q]; linarith
  have hPQ2B : P + Q = 2 * B := by simp only [P, Q]; rw [hcδ, hcΔ]; ring
  have hzB : z * B = A - c := by
    simp only [z, gcAngZ]; exact div_mul_cancel₀ _ hB.ne'
  have hBPQ : B ^ 2 * (1 - z ^ 2) = P * Q := by
    have e : B ^ 2 * (1 - z ^ 2) = B ^ 2 - (z * B) ^ 2 := by ring
    rw [e, hzB]; simp only [P, Q]; rw [hcδ, hcΔ]; ring
  have hS2 : Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by nlinarith)
  set u := 1 - Real.cos ψ
  set w := 1 + Real.cos ψ
  have hu : 0 < u := by simp only [u]; linarith
  have hw : 0 < w := by simp only [w]; linarith
  have hsin : Real.sin ψ ^ 2 = u * w := by rw [Real.sin_sq]; simp only [u, w]; ring
  set σρ := gcSdivSinh ρ
  have hσρ0 : 0 < σρ := gc_sdivSinh_pos ρ
  have hσρ : σρ * Real.sinh ρ = ρ := gc_sdivSinh_mul_sinh ρ
  have hsh : 0 < Real.sinh ρ := Real.sinh_pos_iff.2 hρ
  set σδ := gcSdivSinh δ
  have hσδ0 : 0 < σδ := gc_sdivSinh_pos δ
  -- the three tangent-line inequalities
  have i1 : 2 * σρ * P ≤ 2 * r * r' * u := by
    have := gc_cosh_sub_le hδ0 hδρ.le
    rw [hρ2, hδ2, hyu] at this; exact this
  have i2 : 2 * r * r' * u ≤ 2 * σδ * P := by
    have := gc_le_cosh_sub hδ0 hδρ.le
    rw [hρ2, hδ2, hyu] at this; exact this
  have i3 : 2 * r * r' * w ≤ 2 * σρ * Q := by
    have := gc_le_cosh_sub hρ.le hρΔ.le
    rw [hρ2, hyw] at this; exact this
  -- the Jacobian identity
  have hJ : gcAngPhiD r r' ψ ^ 2 * σρ = Real.sinh ρ * (r * r') ^ 2 * (u * w) / (ρ * (P * Q)) := by
    have e : gcAngPhiD r r' ψ ^ 2 = Real.sinh ρ ^ 2 * ((r * r') ^ 2 * Real.sin ψ ^ 2) /
        (ρ ^ 2 * (B ^ 2 * Real.sqrt (1 - z ^ 2) ^ 2)) := by
      simp only [gcAngPhiD]; ring
    rw [e, hS2, hsin, hBPQ, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (Real.sinh ρ * (r * r') ^ 2 * (u * w) * ρ * (P * Q)) * hσρ
  rw [hJ]
  constructor
  · -- lower bound
    have hρP : ρ * P ≤ r * r' * u * Real.sinh ρ := by
      have := mul_le_mul_of_nonneg_right i1 hsh.le
      have e : ρ * P = σρ * Real.sinh ρ * P := by rw [hσρ]
      linarith
    have hQB : Q ≤ 2 * B := by linarith
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have s1 : r * r' * w * (ρ * P) * Q ≤ r * r' * w * (r * r' * u * Real.sinh ρ) * Q := by
      gcongr
    have s2 : r * r' * w * (r * r' * u * Real.sinh ρ) * Q ≤
        r * r' * w * (r * r' * u * Real.sinh ρ) * (2 * B) := by gcongr
    calc r * r' * w * (ρ * (P * Q)) = r * r' * w * (ρ * P) * Q := by ring
      _ ≤ r * r' * w * (r * r' * u * Real.sinh ρ) * (2 * B) := s1.trans s2
      _ = _ := by ring
  · -- upper bound
    have hwP : w * P ≤ u * Q := by
      have s1 : σρ * P * (r * r' * w) ≤ r * r' * u * (r * r' * w) := by
        have := mul_le_mul_of_nonneg_right i1 (by positivity : (0 : ℝ) ≤ r * r' * w)
        linarith
      have s2 : r * r' * u * (r * r' * w) ≤ r * r' * u * (σρ * Q) := by
        have := mul_le_mul_of_nonneg_left i3 (by positivity : (0 : ℝ) ≤ r * r' * u)
        linarith
      have s3 : (σρ * (r * r')) * (w * P) ≤ (σρ * (r * r')) * (u * Q) := by
        have := s1.trans s2
        calc (σρ * (r * r')) * (w * P) = σρ * P * (r * r' * w) := by ring
          _ ≤ r * r' * u * (σρ * Q) := this
          _ = _ := by ring
      exact le_of_mul_le_mul_left s3 (by positivity)
    have hwB : w * B ≤ Q := by
      have huw : u + w = 2 := by simp only [u, w]; ring
      have e1 : 2 * (w * B) = w * P + w * Q := by rw [← mul_add, hPQ2B]; ring
      have e2 : u * Q + w * Q = 2 * Q := by rw [← add_mul, huw]
      linarith
    have hrP : r * r' * u ≤ σδ * P := by linarith
    have key : r * r' * u * w * B ≤ σδ * P * Q := by
      calc r * r' * u * w * B = r * r' * u * (w * B) := by ring
        _ ≤ r * r' * u * Q := by gcongr
        _ ≤ σδ * P * Q := by gcongr
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have e : Real.sinh ρ * (r * r') ^ 2 * (u * w) * (B * σρ) =
        ρ * (r * r') * (r * r' * u * w * B) := by
      linear_combination ((r * r') ^ 2 * (u * w) * B) * hσρ
    rw [e]
    have : ρ * (r * r') * (r * r' * u * w * B) ≤ ρ * (r * r') * (σδ * P * Q) := by gcongr
    calc ρ * (r * r') * (r * r' * u * w * B) ≤ ρ * (r * r') * (σδ * P * Q) := this
      _ = _ := by ring

theorem gc_angJac_lower {r r' ψ : ℝ} (hr : 0 < r) (hr' : 0 < r') (hψ : ψ ∈ Ioo 0 π) :
    Real.sqrt (gcSdivSinh r * gcSdivSinh r') * Real.cos (ψ / 2) ≤
      gcAngPhiD r r' ψ * Real.sqrt (gcSdivSinh (Real.sqrt (gcAngY r r' ψ))) := by
  have hc : 0 ≤ Real.cos (ψ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hψ.1, Real.pi_pos], by linarith [hψ.2]⟩
  have hD := gc_angPhiD_pos hr hr' hψ
  have hσ := gc_sdivSinh_pos (Real.sqrt (gcAngY r r' ψ))
  refine (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg _) hc)
    (mul_nonneg hD.le (Real.sqrt_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (mul_pos (gc_sdivSinh_pos r) (gc_sdivSinh_pos r')).le,
    Real.sq_sqrt hσ.le,
    gc_sdivSinh_mul_eq hr hr', Real.cos_sq (ψ / 2), show 2 * (ψ / 2) = ψ by ring,
    show (1 : ℝ) / 2 + Real.cos ψ / 2 = (1 + Real.cos ψ) / 2 by ring]
  exact (gc_angJac_sq hr hr' hψ).1

theorem gc_angJac_upper {r r' ψ : ℝ} (hr : 0 < r) (hr' : 0 < r') (hψ : ψ ∈ Ioo 0 π) :
    gcAngPhiD r r' ψ * Real.sqrt (gcSdivSinh (Real.sqrt (gcAngY r r' ψ))) ≤
      Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
        Real.exp ((Real.sqrt (gcAngY r r' ψ) - |r - r'|) / 2) := by
  have hD := gc_angPhiD_pos hr hr' hψ
  set ρ := Real.sqrt (gcAngY r r' ψ)
  have hσ := gc_sdivSinh_pos ρ
  have hσσ := mul_pos (gc_sdivSinh_pos r) (gc_sdivSinh_pos r')
  obtain ⟨hδρ, _⟩ := gc_ang_sqrt_bounds_strict hr hr' hψ
  have hlip := gc_sdivSinh_le_mul_exp (abs_nonneg (r - r')) hδρ.le
  refine (pow_le_pow_iff_left₀ (mul_nonneg hD.le (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hσσ.le, ← Real.exp_nat_mul,
    show ((2 : ℕ) : ℝ) * ((ρ - |r - r'|) / 2) = ρ - |r - r'| by push_cast; ring]
  refine (gc_angJac_sq hr hr' hψ).2.trans ?_
  rw [← gc_sdivSinh_mul_eq hr hr']
  gcongr
  rw [div_le_iff₀ hσ]
  linarith [mul_comm (gcSdivSinh ρ) (Real.exp (ρ - |r - r'|))]

end BlockBand.Diffusion
