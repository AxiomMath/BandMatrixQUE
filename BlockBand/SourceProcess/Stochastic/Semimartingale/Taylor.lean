module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Uniform second-order Taylor bounds on compact sets

Deterministic. `E` is a finite-dimensional real normed space, `U ⊆ E` open, `K ⊆ U`
compact and `φ ∈ C²(U)`. With the remainder
`taylorRem φ y z = φ z - φ y - Dφ(y)(z - y) - ½ D²φ(y)(z - y)(z - y)`
(`D = fderiv ℝ`, `D²φ = fderiv ℝ (fderiv ℝ φ)`, first slot = direction of the outer
derivative), `taylorRem_uniform` gives a constant `C` with `|R(y,z)| ≤ C ‖z - y‖²` on
`K × K` and, for every `ε > 0`, a `δ > 0` with `|R(y,z)| ≤ ε ‖z - y‖²` when
`‖z - y‖ ≤ δ`. No symmetry of `D²φ` is used.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open Set Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second-order Taylor remainder of `φ` at `y`, evaluated at `z`. -/
def taylorRem (φ : E → ℝ) (y z : E) : ℝ :=
  φ z - φ y - fderiv ℝ φ y (z - y) - (1 / 2) * fderiv ℝ (fderiv ℝ φ) y (z - y) (z - y)

/-- Local Taylor bound along a segment inside `U`, in terms of the oscillation of `D²φ`. -/
theorem taylorRem_le_of_segment {U : Set E} (hU : IsOpen U) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) {y h : E} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, y + s • h ∈ U) {η : ℝ}
    (hη : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ φ) (y + s • h) - fderiv ℝ (fderiv ℝ φ) y‖ ≤ η) :
    |taylorRem φ y (y + h)| ≤ η * ‖h‖ ^ 2 := by
  have hd1 : ∀ p ∈ U, HasFDerivAt φ (fderiv ℝ φ p) p := fun p hp =>
    ((hφ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hd2 : ∀ p ∈ U, HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) p) p := fun p hp =>
    (((hφ.contDiffAt (hU.mem_nhds hp)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => y + s • h) h s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const h).const_add y
  set B := fderiv ℝ (fderiv ℝ φ) y
  set Dy := fderiv ℝ φ y
  have hη0 : 0 ≤ η := (norm_nonneg (fderiv ℝ (fderiv ℝ φ) (y + (0 : ℝ) • h) - B)).trans
    (hη 0 ⟨le_rfl, zero_le_one⟩)
  -- first-order step: `ψ s = Dφ(y + s h) - s • B h`
  set ψ : ℝ → E →L[ℝ] ℝ := fun s => fderiv ℝ φ (y + s • h) - s • B h
  have hψ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt ψ
      (fderiv ℝ (fderiv ℝ φ) (y + s • h) h - B h) (Icc 0 1) s := by
    intro s hs
    have h1 := HasFDerivAt.comp_hasDerivAt s (hd2 _ (hseg s hs)) (hpath s)
    have h2 := ((hasDerivAt_id s).smul_const (B h))
    have h3 : HasDerivAt ψ (fderiv ℝ (fderiv ℝ φ) (y + s • h) h - B h) s := by
      have := h1.sub h2
      simp only [one_smul] at this
      exact this
    exact h3.hasDerivWithinAt
  have hψb : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ φ) (y + s • h) h - B h‖ ≤ η * ‖h‖ := by
    intro s hs
    rw [show fderiv ℝ (fderiv ℝ φ) (y + s • h) h - B h = (fderiv ℝ (fderiv ℝ φ) (y + s • h) - B) h
      from rfl]
    exact ((fderiv ℝ (fderiv ℝ φ) (y + s • h) - B).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (hη s (Ico_subset_Icc_self hs)) (norm_nonneg _))
  have hψ0 : ψ 0 = Dy := by simp [ψ, Dy]
  have hψs := norm_image_sub_le_of_norm_deriv_le_segment' hψ hψb
  -- second step: `k s = φ(y + s h) - s Dy h - s² (B h h)/2`
  set k : ℝ → ℝ := fun s => φ (y + s • h) - s * Dy h - s ^ 2 * (B h h / 2)
  have hk : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt k ((ψ s - ψ 0) h) (Icc 0 1) s := by
    intro s hs
    have h1 := HasFDerivAt.comp_hasDerivAt s (hd1 _ (hseg s hs)) (hpath s)
    have h2 := (hasDerivAt_id s).mul_const (Dy h)
    have h3 := (hasDerivAt_pow 2 s).mul_const (B h h / 2)
    have h4 : HasDerivAt k ((ψ s - ψ 0) h) s := by
      refine ((h1.sub h2).sub h3).congr_deriv ?_
      simp [ψ, Dy]; ring
    exact h4.hasDerivWithinAt
  have hkb : ∀ s ∈ Ico (0 : ℝ) 1, ‖(ψ s - ψ 0) h‖ ≤ η * ‖h‖ ^ 2 := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
    refine ((ψ s - ψ 0).le_opNorm h).trans ?_
    have := hψs s hs'
    have : ‖ψ s - ψ 0‖ ≤ η * ‖h‖ := by
      refine this.trans ?_
      have : s - 0 ≤ 1 := by linarith [hs.2]
      calc η * ‖h‖ * (s - 0) ≤ η * ‖h‖ * 1 :=
            mul_le_mul_of_nonneg_left this (mul_nonneg hη0 (norm_nonneg _))
        _ = η * ‖h‖ := mul_one _
    calc ‖ψ s - ψ 0‖ * ‖h‖ ≤ η * ‖h‖ * ‖h‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = η * ‖h‖ ^ 2 := by ring
  have hk1 := norm_image_sub_le_of_norm_deriv_le_segment' hk hkb 1 (by simp)
  have hrem : taylorRem φ y (y + h) = k 1 - k 0 := by
    simp [taylorRem, k, Dy, B]
    ring
  rw [hrem, ← Real.norm_eq_abs]
  simpa using hk1

variable [FiniteDimensional ℝ E]

/-- **Uniform Taylor bound on a compact set.** -/
theorem taylorRem_uniform {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {φ : E → ℝ} (hφ : ContDiffOn ℝ 2 φ U) :
    ∃ C, 0 ≤ C ∧ (∀ y ∈ K, ∀ z ∈ K, |taylorRem φ y z| ≤ C * ‖z - y‖ ^ 2) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ y ∈ K, ∀ z ∈ K, ‖z - y‖ ≤ δ →
        |taylorRem φ y z| ≤ ε * ‖z - y‖ ^ 2 := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  set K' := cthickening δ₀ K
  have hK' : IsCompact K' := hK.cthickening
  have c0 : ContinuousOn φ U := hφ.continuousOn
  have c1 : ContinuousOn (fderiv ℝ φ) U := hφ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have c2 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U :=
    (hφ.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (f := φ) (c0.mono hKU)
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ φ) (c1.mono hKU)
  obtain ⟨M₂, hM₂⟩ := hK'.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ φ))
    (c2.mono hδ₀U)
  have hM₂0 : ∀ y ∈ K, 0 ≤ M₂ := fun y hy =>
    (norm_nonneg _).trans (hM₂ y (self_subset_cthickening K hy))
  have hseg : ∀ y ∈ K, ∀ h : E, ‖h‖ ≤ δ₀ → ∀ s ∈ Icc (0 : ℝ) 1, y + s • h ∈ K' := by
    intro y hy h hh s hs
    refine mem_cthickening_of_dist_le _ y _ _ hy ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg h]
  have hloc : ∀ η, (∀ p ∈ K', ∀ y ∈ K, dist p y ≤ δ₀ →
      ‖fderiv ℝ (fderiv ℝ φ) p - fderiv ℝ (fderiv ℝ φ) y‖ ≤ η) →
      ∀ y ∈ K, ∀ z ∈ K, ‖z - y‖ ≤ δ₀ → |taylorRem φ y z| ≤ η * ‖z - y‖ ^ 2 := by
    intro η hη y hy z _ hzy
    have := taylorRem_le_of_segment hU hφ (y := y) (h := z - y)
      (fun s hs => hδ₀U (hseg y hy _ hzy s hs)) (η := η) (fun s hs => ?_)
    · simpa using this
    refine hη _ (hseg y hy _ hzy s hs) y hy ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg (z - y)]
  set C := 2 * |M₂| + (2 * |M₀| / δ₀ ^ 2 + |M₁| / δ₀ + |M₂| / 2) with hCdef
  refine ⟨C, ?_, ?_, ?_⟩
  · rw [hCdef]; positivity
  · intro y hy z hz
    have hM2 := hM₂0 y hy
    by_cases hzy : ‖z - y‖ ≤ δ₀
    · have h1 := hloc (2 * |M₂|) (fun p hp y' hy' _ =>
        (norm_sub_le (fderiv ℝ (fderiv ℝ φ) p) (fderiv ℝ (fderiv ℝ φ) y')).trans (by
        linarith [hM₂ p hp, hM₂ y' (self_subset_cthickening K hy'), le_abs_self M₂]))
        y hy z hz hzy
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have : 0 ≤ 2 * |M₀| / δ₀ ^ 2 + |M₁| / δ₀ + |M₂| / 2 := by positivity
      rw [hCdef]; linarith
    · push Not at hzy
      set r := ‖z - y‖
      have hr : δ₀ < r := hzy
      have hr0 : 0 < r := hδ₀.trans hr
      have b1 : |fderiv ℝ φ y (z - y)| ≤ |M₁| * r :=
        (le_of_eq (Real.norm_eq_abs _).symm).trans (((fderiv ℝ φ y).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right ((hM₁ y hy).trans (le_abs_self _)) (norm_nonneg _)))
      have b2 : |fderiv ℝ (fderiv ℝ φ) y (z - y) (z - y)| ≤ |M₂| * r ^ 2 := by
        rw [← Real.norm_eq_abs]
        refine ((fderiv ℝ (fderiv ℝ φ) y (z - y)).le_opNorm _).trans ?_
        refine (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ φ) y).le_opNorm _)
          (norm_nonneg _)).trans ?_
        have := (hM₂ y (self_subset_cthickening K hy)).trans (le_abs_self M₂)
        calc ‖fderiv ℝ (fderiv ℝ φ) y‖ * r * r ≤ |M₂| * r * r := by gcongr
          _ = |M₂| * r ^ 2 := by ring
      have b0 : |φ z - φ y| ≤ 2 * |M₀| := by
        have := hM₀ z hz; have := hM₀ y hy
        rw [Real.norm_eq_abs] at *
        calc |φ z - φ y| ≤ |φ z| + |φ y| := abs_sub _ _
          _ ≤ 2 * |M₀| := by linarith [le_abs_self M₀]
      have hR : |taylorRem φ y z| ≤ 2 * |M₀| + |M₁| * r + |M₂| / 2 * r ^ 2 := by
        unfold taylorRem
        have := abs_sub (φ z - φ y - fderiv ℝ φ y (z - y))
          ((1 / 2) * fderiv ℝ (fderiv ℝ φ) y (z - y) (z - y))
        have := abs_sub (φ z - φ y) (fderiv ℝ φ y (z - y))
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at *
        nlinarith
      refine hR.trans ?_
      have e0 : 2 * |M₀| ≤ 2 * |M₀| / δ₀ ^ 2 * r ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : δ₀ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hδ₀.le hr.le 2
        nlinarith [abs_nonneg M₀]
      have e1 : |M₁| * r ≤ |M₁| / δ₀ * r ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ₀]
        have : δ₀ * r ≤ r * r := mul_le_mul_of_nonneg_right hr.le hr0.le
        nlinarith [abs_nonneg M₁]
      have : 0 ≤ 2 * |M₂| * r ^ 2 := by positivity
      have hC : C * r ^ 2 = 2 * |M₂| * r ^ 2 + 2 * |M₀| / δ₀ ^ 2 * r ^ 2 + |M₁| / δ₀ * r ^ 2 +
        |M₂| / 2 * r ^ 2 := by rw [hCdef]; ring
      linarith
  · intro ε hε
    obtain ⟨δ₁, hδ₁, hu⟩ := (Metric.uniformContinuousOn_iff_le (β := E →L[ℝ] E →L[ℝ] ℝ)
      (f := fderiv ℝ (fderiv ℝ φ)) (s := K')).1
      (hK'.uniformContinuousOn_of_continuous (f := fderiv ℝ (fderiv ℝ φ)) (c2.mono hδ₀U)) ε hε
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun y hy z hz hzy => ?_⟩
    have hseg' := hseg y hy (z - y) (hzy.trans (min_le_left _ _))
    have := taylorRem_le_of_segment hU hφ (y := y) (h := z - y)
      (fun s hs => hδ₀U (hseg' s hs)) (η := ε) (fun s hs => ?_)
    · simpa using this
    have hd := hu _ (hseg' s hs) y (self_subset_cthickening K hy) ?_
    · rwa [dist_eq_norm (E := E →L[ℝ] E →L[ℝ] ℝ)] at hd
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    have := hzy.trans (min_le_right _ _)
    nlinarith [hs.2, norm_nonneg (z - y)]

end BlockBand.SourceProcess.Stochastic.Semimartingale
