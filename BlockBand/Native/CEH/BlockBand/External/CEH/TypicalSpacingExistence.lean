module

public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEQuantitative

/-!
# CEH typical-spacing existence for the unconditional MDE branch

This module proves the existence of the CEH typical spacing.  For the exact CEH
normalization

`q(x, η) = N η ρ_s(x + iη)`

we prove continuity, strict height monotonicity and the mass-one limit directly
for the scalar MDE branch.  The generic measurable-root construction from
`CEH.MDE` then supplies the unique positive measurable typical spacing.  The
regular boundary window is retained in the node theorem because that is the
source context, although the spacing construction is stronger and holds at
every real energy.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- Exact CEH typical-spacing left side, scalarized through the unconditional
MDE branch.  It is extended by zero at nonpositive heights. -/
def spacingQuantity {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x η : ℝ) : ℝ :=
  if 0 < η then
    (N : ℝ) * η * density
      (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I))
  else 0

@[simp] theorem spacingQuantity_of_nonpos {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ)
    {η : ℝ} (hη : η ≤ 0) :
    spacingQuantity hN f hs x η = 0 := by
  simp [spacingQuantity, not_lt.mpr hη]

@[simp] theorem spacingQuantity_zero {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    spacingQuantity hN f hs x 0 = 0 := by
  simp [spacingQuantity]

/-- On positive heights the scalar quantity is exactly the matrix-valued CEH
normalization used by `IsLocalETHTypicalSpacing`. -/
theorem spacingQuantity_eq_matrix {N : ℕ} (hN : 0 < N)
    {F : LocalETHMatrix N} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    (x : ℝ) {η : ℝ} (hη : 0 < η) :
    spacingQuantity hN (hermitianSpectrum hF) hs x η =
      (N : ℝ) * η * localETHMDEDensity
        (hermitianMDEBranch hF hs
          ((x : ℂ) + (η : ℂ) * Complex.I)) := by
  simp only [spacingQuantity, ite_eq_left hη]
  rw [localETHMDEDensity_eq_density hF hN hs]
  simpa using hη

/-- The scalar MDE mean is bounded by reciprocal height. -/
theorem norm_upperBranch_le_inv_im {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 0 < z.im) :
    ‖upperBranch hN f hs z‖ ≤ (z.im)⁻¹ := by
  let m := upperBranch hN f hs z
  have hm := upperBranch_isSolution hN f hs hz
  have hh : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    nlinarith [hm.2]
  calc
    ‖m‖ = ‖average (entry f s z m)‖ := congrArg norm (by simpa [m] using hm.1)
    _ ≤ averageReal (fun i => ‖entry f s z m i‖) := norm_average_le hN _
    _ ≤ averageReal (fun _ : Fin N => (effectiveHeight s z m)⁻¹) := by
      unfold averageReal
      gcongr with i
      exact norm_entry_le_inv_effectiveHeight f hh i
    _ = (effectiveHeight s z m)⁻¹ := by
      unfold averageReal
      simp [hN.ne']
    _ ≤ (z.im)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hz (by
        unfold effectiveHeight
        nlinarith [hs, hm.2])

/-- The upper MDE mean tends to zero along every vertical ray. -/
theorem tendsto_upperBranch_vertical_atTop {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Tendsto (fun η : ℝ =>
      upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A, hA⟩ := exists_nat_gt ε⁻¹
  refine ⟨max (A : ℝ) 1, fun η hη => ?_⟩
  have hη1 : 1 ≤ η := (le_max_right (A : ℝ) 1).trans hη
  have hηpos : 0 < η := zero_lt_one.trans_le hη1
  have hbound := norm_upperBranch_le_inv_im hN f hs
    (z := (x : ℂ) + (η : ℂ) * Complex.I) (by simpa using hηpos)
  rw [show (((x : ℂ) + (η : ℂ) * Complex.I).im) = η by simp] at hbound
  rw [dist_zero_right]
  apply lt_of_le_of_lt hbound
  rw [inv_lt_comm₀ hηpos hε]
  exact lt_of_lt_of_le (by exact_mod_cast hA) (le_max_left (A : ℝ) 1 |>.trans hη)

/-- Each normalized scalar resolvent entry has mass-one vertical asymptotics. -/
theorem tendsto_height_mul_entry_vertical_atTop {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ)
    (i : Fin N) :
    Tendsto (fun η : ℝ =>
      (η : ℂ) * entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
        (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)) i)
      atTop (𝓝 Complex.I) := by
  let m : ℝ → ℂ := fun η =>
    upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)
  have hm : Tendsto m atTop (𝓝 0) := tendsto_upperBranch_vertical_atTop hN f hs x
  have hetaR : Tendsto (fun η : ℝ => η⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have heta : Tendsto (fun η : ℝ => ((η : ℂ))⁻¹) atTop (𝓝 0) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp hetaR using 1
    funext η
    simp [Function.comp_apply]
  have hden : Tendsto (fun η : ℝ =>
      ((f i : ℂ) - (x : ℂ)) * (η : ℂ)⁻¹ - Complex.I -
        (s : ℂ) * m η * (η : ℂ)⁻¹)
      atTop (𝓝 (-Complex.I)) := by
    convert (((tendsto_const_nhds.mul heta).sub tendsto_const_nhds).sub
      ((tendsto_const_nhds.mul hm).mul heta)) using 1 ; simp
  have hinv := hden.inv₀ (by simp)
  have heq : (fun η : ℝ =>
      (η : ℂ) * entry f s ((x : ℂ) + (η : ℂ) * Complex.I) (m η) i) =ᶠ[atTop]
      (fun η : ℝ =>
        (((f i : ℂ) - (x : ℂ)) * (η : ℂ)⁻¹ - Complex.I -
          (s : ℂ) * m η * (η : ℂ)⁻¹)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
    unfold entry
    field_simp [hη.ne']
    ring
  rw [show (-Complex.I)⁻¹ = Complex.I by norm_num [Complex.ext_iff]] at hinv
  exact hinv.congr' heq.symm

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- The normalized scalar MDE mean has total Stieltjes mass one. -/
theorem tendsto_height_mul_upperBranch_vertical_atTop {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Tendsto (fun η : ℝ =>
      (η : ℂ) * upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      atTop (𝓝 Complex.I) := by
  have hsum : Tendsto (fun η : ℝ =>
      ∑ i : Fin N,
        (η : ℂ) * entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
          (upperBranch hN f hs
            ((x : ℂ) + (η : ℂ) * Complex.I)) i)
      atTop (𝓝 (∑ _i : Fin N, Complex.I)) := by
    apply tendsto_finsetSum Finset.univ
    intro i _hi
    exact tendsto_height_mul_entry_vertical_atTop hN f hs x i
  have hentries : Tendsto (fun η : ℝ =>
      average (fun i =>
        (η : ℂ) * entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
          (upperBranch hN f hs
            ((x : ℂ) + (η : ℂ) * Complex.I)) i))
      atTop (𝓝 (average (fun _ : Fin N => Complex.I))) := by
    unfold average
    exact hsum.div_const (N : ℂ)
  have heq : (fun η : ℝ =>
      (η : ℂ) * upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I)) =ᶠ[atTop]
      (fun η : ℝ => average (fun i =>
        (η : ℂ) * entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
          (upperBranch hN f hs
            ((x : ℂ) + (η : ℂ) * Complex.I)) i)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
    have hz : 0 < (((x : ℂ) + (η : ℂ) * Complex.I).im) := by
      simpa using hη
    have hm : IsSolution f s ((x : ℂ) + (η : ℂ) * Complex.I)
        (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)) :=
      upperBranch_isSolution hN f hs hz
    calc
      (η : ℂ) * upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I) =
          (η : ℂ) * average (entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
            (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I))) :=
        congrArg ((η : ℂ) * ·) hm.1
      _ = average (fun i => (η : ℂ) *
          entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
            (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)) i) :=
        (average_const_mul _ _).symm
  have hconst : average (fun _ : Fin N => Complex.I) = Complex.I := by
    unfold average
    simp [hN.ne']
  rw [hconst] at hentries
  exact hentries.congr' heq.symm

/-- The exact CEH typical-spacing left side tends to `N / π`. -/
theorem tendsto_spacingQuantity_atTop {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Tendsto (spacingQuantity hN f hs x) atTop
      (𝓝 ((N : ℝ) / Real.pi)) := by
  have hm := tendsto_height_mul_upperBranch_vertical_atTop hN f hs x
  have him : Tendsto (fun η : ℝ =>
      η * (upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I)).im)
      atTop (𝓝 1) := by
    have hi := Complex.continuous_im.continuousAt.tendsto.comp hm
    convert hi using 1
    · funext η
      rw [Function.comp_apply, Complex.mul_im]
      simp
    · simp
  have hdensity : Tendsto (fun η : ℝ =>
      η * density (upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I)))
      atTop (𝓝 (1 / Real.pi)) := by
    simpa [density, div_eq_mul_inv, mul_assoc] using him.div_const Real.pi
  have hq : Tendsto (fun η : ℝ => (N : ℝ) *
      (η * density (upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I)))) atTop
      (𝓝 ((N : ℝ) / Real.pi)) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hdensity
  apply hq.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
  simp only [spacingQuantity, ite_eq_left hη]
  ring

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- The exact spacing quantity vanishes continuously at height zero; the
uniform density bound `ρ ≤ (π√s)⁻¹` rules out an atom there. -/
theorem tendsto_spacingQuantity_zero {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Tendsto (spacingQuantity hN f hs x) (𝓝 0) (𝓝 0) := by
  let g : ℝ → ℝ := fun η => if 0 < η then
    density (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)) else 0
  have hg_nonneg (η : ℝ) : 0 ≤ g η := by
    by_cases hη : 0 < η
    · simp only [g, ite_eq_left hη]
      unfold density
      exact div_nonneg
        (upperBranch_isSolution hN f hs (by simpa using hη)).2.le Real.pi_pos.le
    · simp [g, hη]
  have hg_bound (η : ℝ) : g η ≤ (Real.pi * Real.sqrt s)⁻¹ := by
    by_cases hη : 0 < η
    · simp only [g, ite_eq_left hη]
      exact density_le_inv_pi_sqrt hN f hs (by simpa using hη)
        (upperBranch_isSolution hN f hs (by simpa using hη))
    · simp only [g, ite_eq_right hη]
      positivity
  have hgbdd : IsBoundedUnder (· ≤ ·) (𝓝 0) (norm ∘ g) := by
    apply isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall fun η => by
      rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hg_nonneg η)]
      exact hg_bound η
  have heta : Tendsto (fun η : ℝ => η) (𝓝 0) (𝓝 0) := tendsto_id
  have hprod : Tendsto (fun η : ℝ => η * g η) (𝓝 0) (𝓝 0) :=
    heta.zero_mul_isBoundedUnder_le hgbdd
  have hscaled : Tendsto (fun η : ℝ => (N : ℝ) * (η * g η))
      (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hprod :
      Tendsto (fun η : ℝ => (N : ℝ) * (η * g η)) (𝓝 0) (𝓝 ((N : ℝ) * 0)))
  apply hscaled.congr'
  filter_upwards with η
  simp only [spacingQuantity, g]
  split_ifs <;> ring

/-- At every positive height the spacing quantity is continuous in height. -/
theorem continuousAt_spacingQuantity_of_pos {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ContinuousAt (spacingQuantity hN f hs x) η := by
  let z : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I
  have hzη : 0 < (z η).im := by simpa [z] using hη
  have hzcont : ContinuousAt z η := by fun_prop
  have hmcont : ContinuousAt
      (fun t => upperBranch hN f hs (z t)) η :=
    (continuousAt_upperBranch hN f hs hzη).comp_of_eq hzcont rfl
  have hdcont : ContinuousAt
      (fun t => density (upperBranch hN f hs (z t))) η := by
    unfold density
    fun_prop
  have hmain : ContinuousAt (fun t : ℝ =>
      (N : ℝ) * t * density (upperBranch hN f hs (z t))) η := by
    fun_prop
  apply hmain.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioi.mem_nhds hη)] with t ht
  change 0 < t at ht
  simp only [spacingQuantity, ite_eq_left ht, z]

/-- At every negative height the totalized spacing quantity is locally zero. -/
theorem continuousAt_spacingQuantity_of_neg {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ)
    {η : ℝ} (hη : η < 0) :
    ContinuousAt (spacingQuantity hN f hs x) η := by
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) η).congr_of_eventuallyEq
  filter_upwards [(isOpen_Iio.mem_nhds hη)] with t ht
  simp only [spacingQuantity, ite_eq_right (not_lt.mpr ht.le)]

/-- Height continuity of the exact CEH spacing quantity on all of `ℝ`. -/
theorem continuous_spacingQuantity {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Continuous (spacingQuantity hN f hs x) := by
  rw [continuous_iff_continuousAt]
  intro η
  rcases lt_trichotomy η 0 with hη | rfl | hη
  · exact continuousAt_spacingQuantity_of_neg hN f hs x hη
  · rw [ContinuousAt, spacingQuantity_zero]
    exact tendsto_spacingQuantity_zero hN f hs x
  · exact continuousAt_spacingQuantity_of_pos hN f hs x hη

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- Cauchy–Schwarz for the normalized finite complex average. -/
theorem norm_average_mul_sq_le {N : ℕ} (hN : 0 < N)
    (a b : Fin N → ℂ) :
    ‖average (fun i => a i * b i)‖ ^ 2 ≤
      averageReal (fun i => ‖a i‖ ^ 2) *
        averageReal (fun i => ‖b i‖ ^ 2) := by
  have havg := norm_average_le hN (fun i => a i * b i)
  have hnonneg : 0 ≤ averageReal (fun i => ‖a i * b i‖) := by
    unfold averageReal
    positivity
  have hsquare : ‖average (fun i => a i * b i)‖ ^ 2 ≤
      averageReal (fun i => ‖a i * b i‖) ^ 2 := by
    nlinarith [norm_nonneg (average (fun i => a i * b i))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin N)) (fun i => ‖a i‖) (fun i => ‖b i‖)
  unfold averageReal at hsquare ⊢
  simp only [norm_mul] at hsquare
  apply hsquare.trans
  rw [div_pow, div_mul_div_comm]
  gcongr
  simp [pow_two]

/-- Difference identity for upper scalar-MDE solutions at two spectral
parameters. -/
theorem upperSolution_difference_identity {N : ℕ} (_hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : IsSolution f s z₁ m₁) (hm₂ : IsSolution f s z₂ m₂) :
    m₁ - m₂ = (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
      average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i) := by
  have hh₁ : 0 < effectiveHeight s z₁ m₁ := by
    unfold effectiveHeight
    nlinarith [hm₁.2]
  have hh₂ : 0 < effectiveHeight s z₂ m₂ := by
    unfold effectiveHeight
    nlinarith [hm₂.2]
  have hentry (i : Fin N) :
      entry f s z₁ m₁ i - entry f s z₂ m₂ i =
        (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
          entry f s z₁ m₁ i * entry f s z₂ m₂ i := by
    have h₁ := denominator_ne_zero f hh₁ i
    have h₂ := denominator_ne_zero f hh₂ i
    unfold entry
    rw [inv_sub_inv' h₁ h₂]
    ring
  calc
    m₁ - m₂ = average (entry f s z₁ m₁) -
        average (entry f s z₂ m₂) := congrArg₂ (· - ·) hm₁.1 hm₂.1
    _ = average (fun i => entry f s z₁ m₁ i - entry f s z₂ m₂ i) := by
      unfold average
      rw [Finset.sum_sub_distrib]
      ring
    _ = average (fun i =>
        (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
          (entry f s z₁ m₁ i * entry f s z₂ m₂ i)) := by
      congr 1
      funext i
      rw [hentry]
      ring
    _ = (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
        average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i) :=
      average_const_mul _ _

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- The exact CEH quantity `N η ρ_s(x+iη)` is strictly increasing at positive
height.  The proof is the scalar resolvent comparison behind the Stieltjes
monotonicity statement: Cauchy–Schwarz and the Ward identity make equality
impossible at two distinct heights. -/
theorem strictMonoOn_spacingQuantity {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    StrictMonoOn (spacingQuantity hN f hs x) (Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ hlt
  change 0 < η₁ at hη₁
  change 0 < η₂ at hη₂
  let z₁ : ℂ := (x : ℂ) + (η₁ : ℂ) * Complex.I
  let z₂ : ℂ := (x : ℂ) + (η₂ : ℂ) * Complex.I
  let m₁ : ℂ := upperBranch hN f hs z₁
  let m₂ : ℂ := upperBranch hN f hs z₂
  let b₁ : ℝ := m₁.im
  let b₂ : ℝ := m₂.im
  let d : ℝ := η₂ - η₁
  let e : ℝ := b₁ - b₂
  let A : ℂ := average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i)
  have hz₁ : 0 < z₁.im := by simpa [z₁] using hη₁
  have hz₂ : 0 < z₂.im := by simpa [z₂] using hη₂
  have hm₁ : IsSolution f s z₁ m₁ := upperBranch_isSolution hN f hs hz₁
  have hm₂ : IsSolution f s z₂ m₂ := upperBranch_isSolution hN f hs hz₂
  have hb₁ : 0 < b₁ := hm₁.2
  have hb₂ : 0 < b₂ := hm₂.2
  have hd : 0 < d := by dsimp [d]; linarith
  by_contra hn
  have hprod : η₂ * b₂ ≤ η₁ * b₁ := by
    have hn' := le_of_not_gt hn
    simp only [spacingQuantity, ite_eq_left hη₁, ite_eq_left hη₂,
      density] at hn'
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hpi : 0 < Real.pi := Real.pi_pos
    field_simp [Real.pi_ne_zero] at hn'
    have hz₁' : (x : ℂ) + Complex.I * (η₁ : ℂ) = z₁ := by
      dsimp [z₁]
      ring
    rw [hz₁'] at hn'
    change η₂ * b₂ ≤ η₁ * b₁ at hn'
    exact hn'
  have he : 0 < e := by
    dsimp [e, d]
    nlinarith
  have hk : 0 ≤ η₁ * e - d * b₂ := by
    dsimp [e, d]
    nlinarith
  have hdiff := upperSolution_difference_identity hN f hs hz₁ hz₂ hm₁ hm₂
  change m₁ - m₂ = (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) * A at hdiff
  have hza : ‖z₁ - z₂‖ = d := by
    have heqz : z₁ - z₂ = ((η₁ - η₂ : ℝ) : ℂ) * Complex.I := by
      dsimp [z₁, z₂]
      push_cast
      ring
    rw [heqz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (sub_neg.mpr hlt)]
    simp [d]
  have hnormdiff : ‖m₁ - m₂‖ ≤
      (d + s * ‖m₁ - m₂‖) * ‖A‖ := by
    calc
      ‖m₁ - m₂‖ =
          ‖(z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) * A‖ := congrArg norm hdiff
      _ = ‖z₁ - z₂ + (s : ℂ) * (m₁ - m₂)‖ * ‖A‖ := norm_mul _ _
      _ ≤ (d + s * ‖m₁ - m₂‖) * ‖A‖ := by
        gcongr
        calc
          ‖z₁ - z₂ + (s : ℂ) * (m₁ - m₂)‖ ≤
              ‖z₁ - z₂‖ + ‖(s : ℂ) * (m₁ - m₂)‖ := norm_add_le _ _
          _ = d + s * ‖m₁ - m₂‖ := by
            rw [hza, norm_mul]
            simp [abs_of_pos hs]
  have himdiff : e ≤ ‖m₁ - m₂‖ := by
    have him := Complex.abs_im_le_norm (m₁ - m₂)
    have : (m₁ - m₂).im = e := by rfl
    rw [this, abs_of_pos he] at him
    exact him
  have hA_nonneg : 0 ≤ ‖A‖ := norm_nonneg _
  have hsA : s * ‖A‖ < 1 := by
    have htmp := mixed_average_norm_lt_inv hN f hs hz₁ hz₂ hm₁ hm₂ false
    simp only [Bool.false_eq_true, ↓reduceIte] at htmp
    exact htmp
  have hone : 0 < 1 - s * ‖A‖ := sub_pos.mpr hsA
  have heA : e ≤ ‖A‖ * (d + s * e) := by
    have hrearrange : (1 - s * ‖A‖) * ‖m₁ - m₂‖ ≤ d * ‖A‖ := by
      nlinarith [hnormdiff]
    have hmul := mul_le_mul_of_nonneg_left himdiff hone.le
    nlinarith
  have hsq : e ^ 2 ≤ ‖A‖ ^ 2 * (d + s * e) ^ 2 := by
    have hright : 0 ≤ ‖A‖ * (d + s * e) := by positivity
    nlinarith
  have hh₁ : 0 < effectiveHeight s z₁ m₁ := by
    unfold effectiveHeight
    nlinarith [hm₁.2]
  have hh₂ : 0 < effectiveHeight s z₂ m₂ := by
    unfold effectiveHeight
    nlinarith [hm₂.2]
  have hward₁ := averageReal_normSq_eq_im_div_effectiveHeight hN f hh₁ hm₁
  have hward₂ := averageReal_normSq_eq_im_div_effectiveHeight hN f hh₂ hm₂
  have heff₁ : effectiveHeight s z₁ m₁ = η₁ + s * b₁ := by
    simp [effectiveHeight, z₁, b₁]
  have heff₂ : effectiveHeight s z₂ m₂ = η₂ + s * b₂ := by
    simp [effectiveHeight, z₂, b₂]
  rw [heff₁] at hward₁
  rw [heff₂] at hward₂
  change averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) =
    b₁ / (η₁ + s * b₁) at hward₁
  change averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2) =
    b₂ / (η₂ + s * b₂) at hward₂
  have hcs := norm_average_mul_sq_le hN
    (entry f s z₁ m₁) (entry f s z₂ m₂)
  change ‖A‖ ^ 2 ≤
    averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) *
      averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2) at hcs
  rw [hward₁, hward₂] at hcs
  have hden₁ : 0 < η₁ + s * b₁ := by positivity
  have hden₂ : 0 < η₂ + s * b₂ := by positivity
  have hcross : e ^ 2 * ((η₁ + s * b₁) * (η₂ + s * b₂)) ≤
      b₁ * b₂ * (d + s * e) ^ 2 := by
    have hD : 0 ≤ (d + s * e) ^ 2 := sq_nonneg _
    have hscaled := mul_le_mul_of_nonneg_right hcs hD
    have hcomb := hsq.trans hscaled
    rw [div_mul_div_comm] at hcomb
    have hcomb' : e ^ 2 ≤
        (b₁ * b₂ * (d + s * e) ^ 2) /
          ((η₁ + s * b₁) * (η₂ + s * b₂)) := by
      calc
        e ^ 2 ≤ b₁ * b₂ / ((η₁ + s * b₁) * (η₂ + s * b₂)) *
            (d + s * e) ^ 2 := hcomb
        _ = (b₁ * b₂ * (d + s * e) ^ 2) /
            ((η₁ + s * b₁) * (η₂ + s * b₂)) := by ring
    exact (le_div_iff₀ (mul_pos hden₁ hden₂)).mp hcomb'
  let k : ℝ := η₁ * e - d * b₂
  have hk' : 0 ≤ k := hk
  have halgebra :
      e ^ 2 * ((η₁ + s * b₁) * (η₂ + s * b₂)) -
          b₁ * b₂ * (d + s * e) ^ 2 =
        2 * s * b₂ * e * k + s * d * e ^ 3 + s * e ^ 2 * k +
          2 * b₂ * d * k + d * e * k + k ^ 2 := by
    dsimp [k, d, e]
    ring
  have hstrict : 0 <
      e ^ 2 * ((η₁ + s * b₁) * (η₂ + s * b₂)) -
        b₁ * b₂ * (d + s * e) ^ 2 := by
    rw [halgebra]
    positivity
  nlinarith

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- At fixed positive height, the exact spacing quantity is continuous in the
energy variable. -/
theorem continuous_spacingQuantity_energy {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    Continuous (fun x => spacingQuantity hN f hs x η) := by
  by_cases hη : 0 < η
  · rw [continuous_iff_continuousAt]
    intro x
    let z : ℝ → ℂ := fun y => (y : ℂ) + (η : ℂ) * Complex.I
    have hz : 0 < (z x).im := by simpa [z] using hη
    have hzcont : ContinuousAt z x := by fun_prop
    have hmcont : ContinuousAt
        (fun y => upperBranch hN f hs (z y)) x :=
      (continuousAt_upperBranch hN f hs hz).comp_of_eq hzcont rfl
    have hdcont : ContinuousAt
        (fun y => density (upperBranch hN f hs (z y))) x := by
      unfold density
      fun_prop
    have hmain : ContinuousAt (fun y =>
        (N : ℝ) * η * density (upperBranch hN f hs (z y))) x := by
      fun_prop
    simpa only [spacingQuantity, ite_eq_left hη, z] using hmain
  · simp only [spacingQuantity, ite_eq_right hη]
    fun_prop

/-- The scalar branch supplies all regularity required by the generic
measurable typical-spacing construction. -/
theorem spacingRegularity {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) :
    SpacingRegularity N (spacingQuantity hN f hs) where
  continuous_height := continuous_spacingQuantity hN f hs
  zero_height := spacingQuantity_zero hN f hs
  strictMono_height := strictMonoOn_spacingQuantity hN f hs
  atTop_height := tendsto_spacingQuantity_atTop hN f hs
  measurable_energy := fun η => (continuous_spacingQuantity_energy hN f hs η).measurable

/-- The canonical CEH typical spacing of the unconditional scalar MDE branch. -/
noncomputable def cehTypicalSpacing (N : ℕ) (hN : 4 ≤ N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) : ℝ :=
  typicalSpacing N hN (spacingQuantity (by omega) f hs)
    (spacingRegularity (by omega) f hs) x

/-- Positivity and the exact scalar typical-spacing equation. -/
theorem cehTypicalSpacing_spec (N : ℕ) (hN : 4 ≤ N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 < cehTypicalSpacing N hN f hs x ∧
      spacingQuantity (by omega) f hs x (cehTypicalSpacing N hN f hs x) = 1 := by
  exact ⟨typicalSpacing_pos N hN _ (spacingRegularity (by omega) f hs) x,
    typicalSpacing_equation N hN _ (spacingRegularity (by omega) f hs) x⟩

/-- The canonical CEH typical spacing is measurable in energy. -/
theorem measurable_cehTypicalSpacing (N : ℕ) (hN : 4 ≤ N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) :
    Measurable (cehTypicalSpacing N hN f hs) := by
  exact measurable_typicalSpacing N hN _ (spacingRegularity (by omega) f hs)

/-- The scalar construction solves the exact matrix-normalized CEH equation. -/
theorem cehTypicalSpacing_isLocalETHTypicalSpacing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    IsLocalETHTypicalSpacing (hermitianMDEBranch hF hs) x
      (cehTypicalSpacing N hN (hermitianSpectrum hF) hs x) := by
  have hspec := cehTypicalSpacing_spec N hN (hermitianSpectrum hF) hs x
  refine ⟨hspec.1, ?_⟩
  rw [← spacingQuantity_eq_matrix (by omega) hF hs x hspec.1]
  exact hspec.2

/-- Uniqueness of every positive solution of the exact matrix-normalized CEH
typical-spacing equation. -/
theorem isLocalETHTypicalSpacing_eq_cehTypicalSpacing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) (x η : ℝ)
    (hη : IsLocalETHTypicalSpacing (hermitianMDEBranch hF hs) x η) :
    η = cehTypicalSpacing N hN (hermitianSpectrum hF) hs x := by
  have heq : spacingQuantity (by omega) (hermitianSpectrum hF) hs x η = 1 := by
    rw [spacingQuantity_eq_matrix (by omega) hF hs x hη.1]
    exact hη.2
  exact typicalSpacing_unique (spacingRegularity (by omega)
    (hermitianSpectrum hF) hs) hη.1
      (cehTypicalSpacing_spec N hN (hermitianSpectrum hF) hs x).1 heq
      (cehTypicalSpacing_spec N hN (hermitianSpectrum hF) hs x).2

/-- **CEH (2.11).**  For `N ≥ 4`, positive variance, and a Hermitian deformation, the
exactly normalized equation

`N η ρ_s(x + iη) = 1`

has a unique positive solution at every energy (hence in every regular boundary
window), and the solution is measurable in energy.  The regular-window binder
records the source context; no window property is needed for this stronger
finite-dimensional Stieltjes fact. -/
theorem lem_ext_ceh_spacing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {E₀ r c K : ℝ}
    (_hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K) :
    ∃ etaF : ℝ → ℝ,
      Measurable etaF ∧
      (∀ x : ℝ, IsLocalETHTypicalSpacing
        (hermitianMDEBranch hF hs) x (etaF x)) ∧
      (∀ x η : ℝ,
        IsLocalETHTypicalSpacing (hermitianMDEBranch hF hs) x η →
          η = etaF x) := by
  refine ⟨cehTypicalSpacing N hN (hermitianSpectrum hF) hs,
    measurable_cehTypicalSpacing N hN (hermitianSpectrum hF) hs, ?_, ?_⟩
  · exact cehTypicalSpacing_isLocalETHTypicalSpacing hN hF hs
  · exact isLocalETHTypicalSpacing_eq_cehTypicalSpacing hN hF hs

end CEHNative.BlockBand.CEH
