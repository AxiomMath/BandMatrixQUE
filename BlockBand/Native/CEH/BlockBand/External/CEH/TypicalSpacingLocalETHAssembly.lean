module

public import BlockBand.Native.CEH.BlockBand.External.CEH.TypicalSpacingExistence

/-!
# Canonical typical-spacing assembly for the local-ETH interface

This module applies the CEH typical-spacing construction to the local-ETH
interface.  The published local-ETH interface quantifies over an arbitrary
matrix MDE branch and an arbitrary function solving the typical-spacing
equation.  Matrix-MDE uniqueness and typical-spacing uniqueness collapse both
choices to the unconditional Hermitian branch and `cehTypicalSpacing`.

In particular, every CEH spectral point, center, and bad event formed from an
admissible branch and spacing function agrees exactly with the canonical one.
This is an adapter only: it introduces no local-law or ETH assumption.  The
boundary-to-strip step needs, in addition, a quantitative uniform boundary
propagation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open MeasureTheory

/-- Any branch satisfying the published MDE contract agrees with the
unconditional Hermitian branch away from the real axis. -/
theorem localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) {Mf : ℂ → LocalETHMatrix N}
    (hMf : IsLocalETHMDEBranch s F Mf) {z : ℂ} (hz : z.im ≠ 0) :
    Mf z = hermitianMDEBranch hF hs z :=
  isLocalETHMDESolution_unique hF hs hz (hMf z hz)

/-- At positive height, the typical-spacing predicate is independent of the
chosen MDE branch satisfying the published contract. -/
theorem isLocalETHTypicalSpacing_iff_canonicalBranch
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) {Mf : ℂ → LocalETHMatrix N}
    (hMf : IsLocalETHMDEBranch s F Mf) (x η : ℝ) :
    IsLocalETHTypicalSpacing Mf x η ↔
      IsLocalETHTypicalSpacing (hermitianMDEBranch hF hs) x η := by
  constructor
  · intro hη
    refine ⟨hη.1, ?_⟩
    have hzpos :
        0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by
      simpa using hη.1
    have heq := localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne
      hF hs hMf (z := (x : ℂ) + (η : ℂ) * Complex.I) hzpos.ne'
    rw [← heq]
    exact hη.2
  · intro hη
    refine ⟨hη.1, ?_⟩
    have hzpos :
        0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by
      simpa using hη.1
    have heq := localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne
      hF hs hMf (z := (x : ℂ) + (η : ℂ) * Complex.I) hzpos.ne'
    rw [heq]
    exact hη.2

/-- The exact canonical spacing solves the published equation for every
admissible matrix MDE branch. -/
theorem cehTypicalSpacing_isLocalETHTypicalSpacing_of_branch
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    (x : ℝ) :
    IsLocalETHTypicalSpacing Mf x
      (cehTypicalSpacing N hN (hermitianSpectrum hF) hs x) := by
  rw [isLocalETHTypicalSpacing_iff_canonicalBranch hF hs hMf]
  exact cehTypicalSpacing_isLocalETHTypicalSpacing hN hF hs x

/-- Every solution used by the local-ETH interface is the exact canonical
spacing, even when the interface supplied a different presentation of the MDE
branch. -/
theorem isLocalETHTypicalSpacing_eq_cehTypicalSpacing_of_branch
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    (x η : ℝ) (hη : IsLocalETHTypicalSpacing Mf x η) :
    η = cehTypicalSpacing N hN (hermitianSpectrum hF) hs x := by
  apply isLocalETHTypicalSpacing_eq_cehTypicalSpacing hN hF hs
  exact (isLocalETHTypicalSpacing_iff_canonicalBranch hF hs hMf x η).mp hη

/-- Function-level uniqueness: the arbitrary spacing function quantified by
`LocalETHRegularWindowBound` is definitionally replaceable by the canonical
measurable spacing. -/
theorem localETHTypicalSpacingFunction_eq_canonical
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    {etaF : ℝ → ℝ}
    (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) :
    etaF = cehTypicalSpacing N hN (hermitianSpectrum hF) hs := by
  funext x
  exact isLocalETHTypicalSpacing_eq_cehTypicalSpacing_of_branch
    hN hF hs hMf x (etaF x) (hetaF x)

/-- Existential assembly in exactly the shape needed by the local-ETH
consumer: the canonical function is measurable, solves the equation for the
supplied branch, and is the unique pointwise solution. -/
theorem canonicalTypicalSpacing_localETHAssembly
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf) :
    ∃ etaF : ℝ → ℝ,
      Measurable etaF ∧
      (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) ∧
      (∀ etaF' : ℝ → ℝ,
        (∀ x, IsLocalETHTypicalSpacing Mf x (etaF' x)) →
          etaF' = etaF) := by
  refine ⟨cehTypicalSpacing N hN (hermitianSpectrum hF) hs,
    measurable_cehTypicalSpacing N hN (hermitianSpectrum hF) hs,
    cehTypicalSpacing_isLocalETHTypicalSpacing_of_branch hN hF hs hMf, ?_⟩
  intro etaF' hetaF'
  exact localETHTypicalSpacingFunction_eq_canonical hN hF hs hMf hetaF'

/-- The CEH spectral point formed from any admissible spacing function is
exactly the one formed from the canonical spacing, with the source's
`N^ξ η_f(x)` normalization unchanged. -/
theorem localETHSpectralPoint_eq_canonicalSpacing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    {etaF : ℝ → ℝ}
    (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x))
    (ξ x : ℝ) :
    localETHSpectralPoint N etaF ξ x =
      localETHSpectralPoint N
        (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ x := by
  rw [localETHTypicalSpacingFunction_eq_canonical hN hF hs hMf hetaF]

/-- An admissible CEH spectral point lies strictly in the upper half-plane.
The positivity uses both factors in the exact height `N^ξ η_f(x)`. -/
theorem localETHSpectralPoint_im_pos
    {N : ℕ} (hN : 4 ≤ N) {Mf : ℂ → LocalETHMatrix N}
    {etaF : ℝ → ℝ}
    (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x))
    (ξ x : ℝ) :
    0 < (localETHSpectralPoint N etaF ξ x).im := by
  rw [localETHSpectralPoint]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
    mul_zero, add_zero]
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  exact mul_pos (Real.rpow_pos_of_pos hNpos ξ) (hetaF x).1

/-- Evaluation of an arbitrary admissible branch at an admissible CEH spectral
point agrees with evaluation of the unconditional Hermitian branch. -/
theorem localETHMDEBranch_spectralPoint_eq_canonicalBranch
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    {etaF : ℝ → ℝ}
    (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x))
    (ξ x : ℝ) :
    Mf (localETHSpectralPoint N etaF ξ x) =
      hermitianMDEBranch hF hs
        (localETHSpectralPoint N
          (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ x) := by
  rw [← localETHSpectralPoint_eq_canonicalSpacing
    hN hF hs hMf hetaF ξ x]
  exact localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf
    (localETHSpectralPoint_im_pos hN hetaF ξ x).ne'

/-- The deterministic diagonal center in the ETH error is independent of all
presentational choices of MDE branch and typical-spacing function. -/
theorem localETHCenter_eq_canonicalSpacing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    {etaF : ℝ → ℝ}
    (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x))
    (ξ x : ℝ) (J : LocalETHMatrix N) :
    localETHCenter Mf etaF ξ x J =
      localETHCenter (hermitianMDEBranch hF hs)
        (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ x J := by
  unfold localETHCenter
  rw [localETHMDEBranch_spectralPoint_eq_canonicalBranch
    hN hF hs hMf hetaF ξ x]

/-- Consequently the exact overlap error used by the published local-ETH
interface is unchanged by canonicalization. -/
theorem localETHError_eq_canonicalSpacing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    {etaF : ℝ → ℝ}
    (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x))
    (ξ : ℝ) (J : LocalETHMatrix N) (lam : Fin N → ℝ)
    (u : Fin N → Fin N → ℂ) (i j : Fin N) :
    localETHError Mf etaF ξ J lam u i j =
      localETHError (hermitianMDEBranch hF hs)
        (cehTypicalSpacing N hN (hermitianSpectrum hF) hs)
        ξ J lam u i j := by
  unfold localETHError
  rw [localETHCenter_eq_canonicalSpacing
    hN hF hs hMf hetaF ξ (lam i) J]

/-- The simultaneous every-eigenbasis bad event is exactly the canonical
event.  Thus downstream probability estimates may use the concrete spacing
without changing any quantifier, threshold, or normalization. -/
theorem localETHWindowBad_iff_canonicalSpacing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    {etaF : ℝ → ℝ}
    (hetaF : ∀ x, IsLocalETHTypicalSpacing Mf x (etaF x))
    (ξ β δ E₀ : ℝ) (J : LocalETHMatrix N)
    (G : HermitianMatrix (Fin N)) :
    LocalETHWindowBad Mf etaF ξ β δ E₀ F J G ↔
      LocalETHWindowBad (hermitianMDEBranch hF hs)
        (cehTypicalSpacing N hN (hermitianSpectrum hF) hs)
        ξ β δ E₀ F J G := by
  unfold LocalETHWindowBad
  simp_rw [localETHError_eq_canonicalSpacing
    hN hF hs hMf hetaF ξ J]

end CEHNative.BlockBand.CEH
