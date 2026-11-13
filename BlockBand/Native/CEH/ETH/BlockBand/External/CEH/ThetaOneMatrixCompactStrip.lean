module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneGermCompactAssembly

/-!
# Matrix lift of compatible CEH boundary germs

This module performs the exact matrix lift used in the fixed-dimension
compact-strip argument.  A scalar IFT germ is transported through the spectral
calculus with the original CEH normalization.  Every matrix entry is
holomorphic, and local scalar agreement implies local equality with both the
real boundary matrix and the unconditional positive-height matrix branch.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set Matrix
open scoped Topology ComplexConjugate

/-- Spectral matrix lift of a scalar MDE germ. -/
def liftedMDEGerm {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (s : ℝ) (ψ : ℂ → ℂ) (z : ℂ) : LocalETHMatrix N :=
  spectralLift hF (entry (hermitianSpectrum hF) s z (ψ z))

/-- Every entry of the lifted germ is holomorphic wherever the scalar germ is
holomorphic and the finite rational denominators are nonzero. -/
theorem analyticAt_liftedMDEGerm_apply
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (s : ℝ) {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : AnalyticAt ℂ ψ z)
    (hne : ∀ k, (hermitianSpectrum hF k : ℂ) - z - (s : ℂ) * ψ z ≠ 0)
    (i j : Fin N) :
    AnalyticAt ℂ (fun w => liftedMDEGerm hF s ψ w i j) z := by
  have hk (k : Fin N) : AnalyticAt ℂ
      (fun w => entry (hermitianSpectrum hF) s w (ψ w) k) z :=
    analyticAt_entry (hermitianSpectrum hF) s ψ k hψ (hne k)
  unfold liftedMDEGerm
  simp only [spectralLift_apply]
  have hsum : ∀ t : Finset (Fin N), AnalyticAt ℂ (fun w =>
      ∑ k ∈ t, (hF.eigenvectorUnitary : LocalETHMatrix N) i k *
        entry (hermitianSpectrum hF) s w (ψ w) k *
        star ((hF.eigenvectorUnitary : LocalETHMatrix N) j k)) z := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
    | @insert k t hkt iht =>
        simp only [Finset.sum_insert hkt]
        exact ((analyticAt_const.mul (hk k)).mul analyticAt_const).add iht
  simpa using hsum Finset.univ

/-- Scalar germ agreement with the upper branch lifts entrywise to agreement
with the unconditional Hermitian matrix MDE branch. -/
theorem liftedMDEGerm_eq_hermitianMDEBranch_of_upper
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {ψ : ℂ → ℂ} {z : ℂ}
    (hz : 0 < z.im)
    (hψ : ψ z = upperBranch hN (hermitianSpectrum hF) hs z) :
    liftedMDEGerm hF s ψ z = hermitianMDEBranch hF hs z := by
  simp [liftedMDEGerm, hermitianMDEBranch, hN,
    hermitianMDEMean, hz, hψ]

/-- Agreement of a scalar germ with the normalized trace of an identified real
boundary matrix lifts to exact agreement with that matrix. -/
theorem liftedMDEGerm_eq_boundary_of_identified
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (s : ℝ) {Mb : ℝ → LocalETHMatrix N} {ψ : ℂ → ℂ} {x : ℝ}
    (hidentified : Mb x = spectralLift hF
      (entry (hermitianSpectrum hF) s (x : ℂ)
        (Conventions.normalizedTrace (Mb x))))
    (hψ : ψ (x : ℂ) = Conventions.normalizedTrace (Mb x)) :
    liftedMDEGerm hF s ψ (x : ℂ) = Mb x := by
  rw [hidentified]
  simp [liftedMDEGerm, hψ]

/-- A compatible scalar germ therefore gives a continuous matrix
extension through its base boundary point, entry by entry. -/
theorem continuousAt_liftedMDEGerm_apply_at_boundary
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) {ψ : ℂ → ℂ} {x : ℝ} {m : ℂ}
    (hψ : AnalyticAt ℂ ψ (x : ℂ)) (hψx : ψ (x : ℂ) = m)
    (hmim : 0 < m.im) (i j : Fin N) :
    ContinuousAt (fun z => liftedMDEGerm hF s ψ z i j) (x : ℂ) := by
  have hh : 0 < effectiveHeight s (x : ℂ) m := by
    simpa [effectiveHeight] using mul_pos hs hmim
  have hne : ∀ k, (hermitianSpectrum hF k : ℂ) - (x : ℂ) -
      (s : ℂ) * ψ (x : ℂ) ≠ 0 := by
    simpa [hψx] using denominator_ne_zero (hermitianSpectrum hF) hh
  exact (analyticAt_liftedMDEGerm_apply hF s hψ hne i j).continuousAt

/-- Local real and upper-half-plane scalar compatibility lifts simultaneously
to the matrix level.  This is the exact local joint-extension package used by
a finite compact cover. -/
theorem eventually_liftedMDEGerm_agrees_boundary_and_upper
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {Mb : ℝ → LocalETHMatrix N}
    {ψ : ℂ → ℂ} {x : ℝ}
    (hreal : (fun y : ℝ => ψ (y : ℂ)) =ᶠ[nhds x]
      fun y => Conventions.normalizedTrace (Mb y))
    (hidentified : ∀ᶠ y : ℝ in nhds x,
      Mb y = spectralLift hF (entry (hermitianSpectrum hF) s (y : ℂ)
        (Conventions.normalizedTrace (Mb y))))
    (hupper : ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
      upperBranch hN (hermitianSpectrum hF) hs) :
    ((fun y : ℝ => liftedMDEGerm hF s ψ (y : ℂ)) =ᶠ[nhds x] Mb) ∧
    (liftedMDEGerm hF s ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
      hermitianMDEBranch hF hs) := by
  constructor
  · filter_upwards [hreal, hidentified] with y hψ hid
    exact liftedMDEGerm_eq_boundary_of_identified hF s hid hψ
  · filter_upwards [hupper, self_mem_nhdsWithin] with z hψ hz
    exact liftedMDEGerm_eq_hermitianMDEBranch_of_upper hF hN hs hz hψ

end CEHNative.BlockBand.CEH
