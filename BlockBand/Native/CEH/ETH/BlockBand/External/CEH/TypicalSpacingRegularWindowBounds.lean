module

public import BlockBand.Native.CEH.BlockBand.External.CEH.TypicalSpacingExistence
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEQuantitative

/-!
# Deterministic lower bounds for the CEH typical spacing

This module records the uniform positive lower bound needed when lifting a
regular-window real grid to the exact CEH spectral height.  The proof uses the
exact typical-spacing normalization and the unconditional scalar-MDE density
bound; hence it is stronger than a statement conditional on a regular boundary
window.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

/-- The exact CEH typical spacing is uniformly bounded below by
`π √s / N`.  This is the direct consequence of `N η ρ = 1` and the
source-normalized density bound `ρ ≤ (π √s)⁻¹`. -/
theorem pi_mul_sqrt_div_natCast_le_cehTypicalSpacing
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Real.pi * Real.sqrt s / (N : ℝ) ≤
      cehTypicalSpacing N hN f hs x := by
  let η := cehTypicalSpacing N hN f hs x
  let z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  let m : ℂ := upperBranch (by omega) f hs z
  have hη : 0 < η := (cehTypicalSpacing_spec N hN f hs x).1
  have hz : 0 < z.im := by simpa [z] using hη
  have hm : IsSolution f s z m := upperBranch_isSolution (by omega) f hs hz
  have hρ := density_le_inv_pi_sqrt (by omega) f hs hz hm
  have heq := (cehTypicalSpacing_spec N hN f hs x).2
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < Real.pi * Real.sqrt s := mul_pos hpi hsqrt
  have heq' : (N : ℝ) * η * density m = 1 := by
    rw [spacingQuantity, ite_eq_left hη] at heq
    simpa only [η, m, z] using heq
  apply (div_le_iff₀ hNreal).2
  have hmul : Real.pi * Real.sqrt s * density m ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hρ hden.le
    calc
      Real.pi * Real.sqrt s * density m =
          (Real.pi * Real.sqrt s) * density m := by ring
      _ ≤ (Real.pi * Real.sqrt s) * (Real.pi * Real.sqrt s)⁻¹ := h
      _ = 1 := by field_simp [hden.ne']
  calc
    Real.pi * Real.sqrt s =
        Real.pi * Real.sqrt s * ((N : ℝ) * η * density m) := by rw [heq', mul_one]
    _ = ((N : ℝ) * η) * (Real.pi * Real.sqrt s * density m) := by ring
    _ ≤ ((N : ℝ) * η) * 1 := by
      exact mul_le_mul_of_nonneg_left hmul (mul_nonneg hNreal.le hη.le)
    _ = η * (N : ℝ) := by ring

/-- After the CEH spectral lift, the imaginary height has the explicit positive
lower bound `N^ξ · (π √s / N)`, uniformly in the energy. -/
theorem rpow_mul_pi_sqrt_div_natCast_le_rpow_mul_cehTypicalSpacing
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (ξ x : ℝ) :
    (N : ℝ) ^ ξ * (Real.pi * Real.sqrt s / (N : ℝ)) ≤
      (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x := by
  exact mul_le_mul_of_nonneg_left
    (pi_mul_sqrt_div_natCast_le_cehTypicalSpacing hN f hs x)
    (Real.rpow_nonneg (by positivity) ξ)

/-- In particular the exact CEH lifted height is strictly positive, with a
single lower bound valid on every regular window (indeed, at every energy). -/
theorem rpow_mul_cehTypicalSpacing_pos
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (ξ x : ℝ) :
    0 < (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x := by
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) ξ)
    (cehTypicalSpacing_spec N hN f hs x).1

end CEHNative.BlockBand.CEH
