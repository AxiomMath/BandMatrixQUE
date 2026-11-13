module

public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEExistence
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic dependence of the finite-dimensional scalar MDE

The upper branch of the scalar Dyson equation of a finite Hermitian deformation is analytic on
the open upper half-plane, by the holomorphic implicit function theorem (the derivative in the
mean variable is the stability denominator); the lower branch is its conjugate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped ComplexConjugate Topology

/-- The holomorphic equation whose zero set is the scalar Dyson equation. -/
def mdeResidual {N : ℕ} (f : DeformationSpectrum N) (s : ℝ) (p : ℂ × ℂ) : ℂ :=
  p.2 - average (entry f s p.1 p.2)

/-- The residual is analytic at every point where all scalar denominators are nonzero. -/
theorem analyticAt_mdeResidual {N : ℕ} (f : DeformationSpectrum N) (s : ℝ)
    {p : ℂ × ℂ} (hne : ∀ i, (f i : ℂ) - p.1 - (s : ℂ) * p.2 ≠ 0) :
    AnalyticAt ℂ (mdeResidual f s) p := by
  let g₁ : ℂ × ℂ → ℂ := fun q => q.1
  let g₂ : ℂ × ℂ → ℂ := fun q => q.2
  have hg₁ : AnalyticAt ℂ g₁ p := analyticAt_fst
  have hg₂ : AnalyticAt ℂ g₂ p := analyticAt_snd
  have hi (i : Fin N) : AnalyticAt ℂ
      (fun q => ((f i : ℂ) - g₁ q - (s : ℂ) * g₂ q)⁻¹) p := by
    apply AnalyticAt.inv
    · exact (analyticAt_const.sub hg₁).sub (analyticAt_const.mul hg₂)
    · simpa [g₁, g₂] using hne i
  have hsum_aux : ∀ t : Finset (Fin N), AnalyticAt ℂ
      (fun q => ∑ i ∈ t, ((f i : ℂ) - g₁ q - (s : ℂ) * g₂ q)⁻¹) p := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ => (0 : ℂ)) p)
    | @insert a t ha iht =>
        simp only [Finset.sum_insert ha]
        exact (hi a).add iht
  have hsum : AnalyticAt ℂ
      (fun q => ∑ i : Fin N, ((f i : ℂ) - g₁ q - (s : ℂ) * g₂ q)⁻¹) p := by
    simpa using hsum_aux Finset.univ
  unfold mdeResidual average entry
  change AnalyticAt ℂ (fun q => g₂ q -
    (∑ i, ((f i : ℂ) - g₁ q - (s : ℂ) * g₂ q)⁻¹) * ((N : ℂ)⁻¹)) p
  exact hg₂.sub (hsum.mul analyticAt_const)

/-- Hence the residual is complex `C^ω` at such a point. -/
theorem contDiffAt_mdeResidual {N : ℕ} (f : DeformationSpectrum N) (s : ℝ)
    {p : ℂ × ℂ} (hne : ∀ i, (f i : ℂ) - p.1 - (s : ℂ) * p.2 ≠ 0) :
    ContDiffAt ℂ ⊤ (mdeResidual f s) p :=
  (analyticAt_mdeResidual f s hne).contDiffAt

/-- The derivative in the mean variable is the stability denominator. -/
theorem hasDerivAt_mdeResidual_snd {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ)
    (hne : ∀ i, (f i : ℂ) - z - (s : ℂ) * m ≠ 0) :
    HasDerivAt (fun w => mdeResidual f s (z, w))
      (stabilityDenominator f s z m) m := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi (i : Fin N) : HasDerivAt
      (fun w : ℂ => ((f i : ℂ) - z - (s : ℂ) * w)⁻¹)
      ((s : ℂ) * (((f i : ℂ) - z - (s : ℂ) * m)⁻¹) ^ 2) m := by
    have hd : HasDerivAt (fun w : ℂ => (f i : ℂ) - z - (s : ℂ) * w)
        (-(s : ℂ)) m := by
      convert (hasDerivAt_const m ((f i : ℂ) - z)).sub
        ((hasDerivAt_id m).const_mul (s : ℂ)) using 1
      · funext w
        rfl
      · ring
    convert hd.inv (hne i) using 1
    simp [inv_pow, div_eq_mul_inv]
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N)))
    (fun i _ => hi i)
  have hcoeff : (∑ i : Fin N,
      (s : ℂ) * (((f i : ℂ) - z - (s : ℂ) * m)⁻¹) ^ 2) / (N : ℂ) =
      (s : ℂ) * average (fun i => entry f s z m i ^ 2) := by
    unfold average entry
    rw [← Finset.mul_sum]
    ring
  have havg : HasDerivAt
      (fun w : ℂ => (∑ i, ((f i : ℂ) - z - (s : ℂ) * w)⁻¹) / (N : ℂ))
      ((s : ℂ) * average (fun i => entry f s z m i ^ 2)) m := by
    convert hsum.div_const (N : ℂ) using 1
    exact hcoeff.symm
  convert (hasDerivAt_id m).sub havg using 1
  · funext w
    rfl
  · rfl

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- At an upper solution the partial derivative in the mean coordinate is invertible. -/
theorem mdeResidual_snd_isInvertible {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z m : ℂ}
    (hz : 0 < z.im) (hm : IsSolution f s z m) :
    (fderiv ℂ (mdeResidual f s) (z, m) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  have hheight : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    nlinarith [hm.2]
  have hne : ∀ i, (f i : ℂ) - z - (s : ℂ) * m ≠ 0 :=
    denominator_ne_zero f hheight
  have hcdf := contDiffAt_mdeResidual f s (p := (z, m)) hne
  have hder := hasDerivAt_mdeResidual_snd hN f s z m hne
  have hdiff : DifferentiableAt ℂ (mdeResidual f s) (z, m) :=
    hcdf.differentiableAt (by simp)
  have hcomp := (hdiff.hasFDerivAt.comp m
    (hasFDerivAt_prodMk_right z m)).unique hder.hasFDerivAt
  rw [hcomp]
  rw [ContinuousLinearMap.isInvertible_iff_isHomeomorph]
  convert isHomeomorph_smul₀ (α := ℂ)
    (stabilityDenominator_ne_zero hN f hs hz hm) using 1
  funext x
  simp
  ring

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- A total representative of the upper branch, set to zero outside the upper
half-plane.  Its restriction to `Im z > 0` is independent of this extension. -/
noncomputable def upperBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then upperSolution hN f hs z hz else 0

 theorem upperBranch_isSolution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    IsSolution f s z (upperBranch hN f hs z) := by
  simp only [upperBranch, dite_eq_left hz]
  exact upperSolution_isSolution hN f hs z hz

/-- The upper scalar-MDE branch is analytic at every point of the upper half-plane. -/
theorem analyticAt_upperBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (upperBranch hN f hs) z := by
  let m := upperBranch hN f hs z
  have hm : IsSolution f s z m := upperBranch_isSolution hN f hs hz
  have hheight : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    nlinarith [hm.2]
  have hne : ∀ i, (f i : ℂ) - z - (s : ℂ) * m ≠ 0 :=
    denominator_ne_zero f hheight
  let cdf : ContDiffAt ℂ ⊤ (mdeResidual f s) (z, m) :=
    contDiffAt_mdeResidual f s (p := (z, m)) hne
  let hinv : (fderiv ℂ (mdeResidual f s) (z, m) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible :=
    mdeResidual_snd_isInvertible hN f hs hz hm
  let ψ : ℂ → ℂ := cdf.implicitFunction (by simp) hinv
  have hψsmooth : ContDiffAt ℂ ⊤ ψ z := by
    exact cdf.contDiffAt_implicitFunction (by simp) hinv
  have hψanalytic : AnalyticAt ℂ ψ z := hψsmooth.analyticAt
  have hψcont : ContinuousAt ψ z := hψsmooth.continuousAt
  have hψself : ψ z = m := cdf.implicitFunction_apply_self (by simp) hinv
  have heq0 : mdeResidual f s (z, m) = 0 := by
    unfold mdeResidual
    exact sub_eq_zero.mpr hm.1
  have heventEq : ∀ᶠ w in 𝓝 z,
      mdeResidual f s (w, ψ w) = 0 := by
    filter_upwards [cdf.eventually_apply_implicitFunction (by simp) hinv] with w hw
    simpa [heq0] using hw
  have heventZ : ∀ᶠ w in 𝓝 z, 0 < w.im := by
    exact (Complex.continuous_im.tendsto z) (Ioi_mem_nhds hz)
  have heventPsi : ∀ᶠ w in 𝓝 z, 0 < (ψ w).im := by
    have ht0 : Tendsto (fun w => (ψ w).im) (𝓝 z) (𝓝 (ψ z).im) :=
      Complex.continuous_im.continuousAt.tendsto.comp hψcont.tendsto
    have ht : Tendsto (fun w => (ψ w).im) (𝓝 z) (𝓝 m.im) := by
      simpa [hψself] using ht0
    filter_upwards [ht (Ioi_mem_nhds hm.2)] with w hw
    exact hw
  have hlocal : ψ =ᶠ[𝓝 z] upperBranch hN f hs := by
    filter_upwards [heventEq, heventZ, heventPsi] with w heq hwz hwp
    have hsol : IsSolution f s w (ψ w) := by
      refine ⟨?_, hwp⟩
      unfold mdeResidual at heq
      exact sub_eq_zero.mp heq
    simp only [upperBranch, dite_eq_left hwz]
    exact eq_upperSolution hN f hs hwz hsol
  exact hψanalytic.congr hlocal

/-- Continuity of the upper branch, obtained from analyticity rather than assumed. -/
theorem continuousAt_upperBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (upperBranch hN f hs) z :=
  (analyticAt_upperBranch hN f hs hz).continuousAt

/-- Analyticity on the open upper half-plane. -/
theorem analyticOnNhd_upperBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (upperBranch hN f hs) {z : ℂ | 0 < z.im} :=
  fun _ hz => analyticAt_upperBranch hN f hs hz

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter Set Function
open scoped ComplexConjugate Topology

/-- The total lower branch obtained by conjugating the total upper branch. -/
noncomputable def lowerBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (z : ℂ) : ℂ :=
  star (upperBranch hN f hs (star z))

 theorem lowerBranch_isLowerSolution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im < 0) :
    IsLowerSolution f s z (lowerBranch hN f hs z) := by
  have hzstar : 0 < (star z).im := by simp; linarith
  have hu := upperBranch_isSolution hN f hs hzstar
  refine ⟨?_, ?_⟩
  · unfold lowerBranch
    calc
      star (upperBranch hN f hs (star z)) =
          star (average (entry f s (star z) (upperBranch hN f hs (star z)))) :=
        congrArg star hu.1
      _ = average (entry f s (star (star z))
          (star (upperBranch hN f hs (star z)))) :=
        star_average_entry f s (star z) (upperBranch hN f hs (star z))
      _ = average (entry f s z (star (upperBranch hN f hs (star z)))) := by simp
  · unfold lowerBranch
    simp
    exact hu.2

/-- The conjugated lower branch is analytic throughout the lower half-plane. -/
theorem analyticAt_lowerBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im < 0) :
    AnalyticAt ℂ (lowerBranch hN f hs) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hevent : ∀ᶠ w in 𝓝 z, w.im < 0 :=
    (Complex.continuous_im.tendsto z) (Iio_mem_nhds hz)
  filter_upwards [hevent] with w hw
  have hwstar : 0 < (star w).im := by simp; linarith
  have hd : DifferentiableAt ℂ (upperBranch hN f hs) (star w) :=
    (analyticAt_upperBranch hN f hs hwstar).differentiableAt
  have hc := hd.conj_conj
  change DifferentiableAt ℂ (fun x => star (upperBranch hN f hs (star x))) w
  convert hc using 1 <;> simp [Function.comp_def]

 theorem continuousAt_lowerBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im < 0) :
    ContinuousAt (lowerBranch hN f hs) z :=
  (analyticAt_lowerBranch hN f hs hz).continuousAt

 theorem analyticOnNhd_lowerBranch {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (lowerBranch hN f hs) {z : ℂ | z.im < 0} :=
  fun _ hz => analyticAt_lowerBranch hN f hs hz

end CEHNative.BlockBand.CEH
