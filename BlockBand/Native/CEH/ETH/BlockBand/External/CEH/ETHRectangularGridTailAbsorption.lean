module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHRectangularGridProbability

/-!
# Absorbing the polynomial rectangular-grid loss

The fixed-pair two-resolvent estimate may be requested with an arbitrarily large
tail exponent.  This module records the elementary but quantifier-critical step
which spends `2 * q` powers of `N` on a rectangular grid of cardinality at most
`N ^ q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open MeasureTheory
open scoped ENNReal

/-- A squared grid-cardinality loss bounded by `N ^ (2q)` is absorbed by
requesting `2q` additional powers in the fixed-pair tail.  The statement uses
natural exponents so that it is an exact identity in `ENNReal`; a real-valued
polynomial tail can later be strengthened to such an integer exponent. -/
theorem measure_localETHTwoResolventRandomBadEvent_le_inv_pow_of_rectangularGrid
    {Ω : Type*} [MeasurableSpace Ω] {N realMesh heightMesh D q : ℕ}
    (hN : 0 < N) (μ : Measure Ω) (f : Ω → ℂ → ℂ → ℂ)
    (etaF : ℝ → ℝ) (ξ E₀ R etaMin etaMax : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ)
    (gridThreshold : ℝ)
    (hsubset :
      localETHTwoResolventRandomBadEvent f etaF ξ lam threshold ⊆
        fixedTwoResolventGridBadEvent f
          (localETHRectangularSpectralGridPoint
            E₀ R etaMin etaMax realMesh heightMesh)
          gridThreshold)
    (hcard :
      ((((realMesh + 1) * (heightMesh + 1) : ℕ) : ENNReal)) ≤
        (N : ENNReal) ^ q)
    (hpair : ∀ a b : Fin (realMesh + 1) × Fin (heightMesh + 1),
      μ (fixedTwoResolventGridPairBadEvent f
        (localETHRectangularSpectralGridPoint
          E₀ R etaMin etaMax realMesh heightMesh)
        gridThreshold a b) ≤
          ((N : ENNReal)⁻¹) ^ (D + 2 * q)) :
    μ (localETHTwoResolventRandomBadEvent f etaF ξ lam threshold) ≤
      ((N : ENNReal)⁻¹) ^ D := by
  have hraw :=
    measure_localETHTwoResolventRandomBadEvent_le_rectangularGrid_sq_mul
      μ f etaF ξ E₀ R etaMin etaMax lam threshold gridThreshold
      (((N : ENNReal)⁻¹) ^ (D + 2 * q)) hsubset hpair
  calc
    μ (localETHTwoResolventRandomBadEvent f etaF ξ lam threshold) ≤
        ((((realMesh + 1) * (heightMesh + 1) : ℕ) : ENNReal) ^ 2) *
          ((N : ENNReal)⁻¹) ^ (D + 2 * q) := hraw
    _ ≤ (((N : ENNReal) ^ q) ^ 2) *
          ((N : ENNReal)⁻¹) ^ (D + 2 * q) := by gcongr
    _ = ((N : ENNReal)⁻¹) ^ D := by
      rw [pow_add]
      have hne : (N : ENNReal) ≠ 0 := by exact_mod_cast hN.ne'
      have htop : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
      calc
        ((N : ENNReal) ^ q) ^ 2 *
              (((N : ENNReal)⁻¹) ^ D * ((N : ENNReal)⁻¹) ^ (2 * q)) =
            ((N : ENNReal)⁻¹) ^ D *
              (((N : ENNReal) ^ q) ^ 2 * ((N : ENNReal)⁻¹) ^ (2 * q)) := by
          ac_rfl
        _ = ((N : ENNReal)⁻¹) ^ D *
              ((((N : ENNReal) ^ q) * ((N : ENNReal)⁻¹) ^ q) ^ 2) := by
          congr 1
          rw [show 2 * q = q * 2 by omega, ← pow_mul, ← mul_pow]
          rw [ENNReal.mul_inv_cancel hne htop, one_pow]
          rw [← mul_pow, ENNReal.mul_inv_cancel hne htop, one_pow, one_pow]
        _ = ((N : ENNReal)⁻¹) ^ D := by
          rw [← mul_pow, ENNReal.mul_inv_cancel hne htop, one_pow, one_pow, mul_one]

/-- The canonical polynomial product mesh has polynomial cardinality.  The two
extra powers account for the `+1` endpoint in each coordinate. -/
theorem rectangularGrid_card_le_pow
    {N a b : ℕ} (hN : 2 ≤ N) :
    (((N ^ a + 1) * (N ^ b + 1) : ℕ) : ENNReal) ≤
      (N : ENNReal) ^ (a + b + 2) := by
  norm_cast
  have ha1 : 1 ≤ N ^ a := one_le_pow₀ (by omega)
  have hb1 : 1 ≤ N ^ b := one_le_pow₀ (by omega)
  have ha : N ^ a + 1 ≤ N ^ (a + 1) := by
    rw [pow_succ]
    calc
      N ^ a + 1 ≤ N ^ a + N ^ a := Nat.add_le_add_left ha1 _
      _ = N ^ a * 2 := by omega
      _ ≤ N ^ a * N := Nat.mul_le_mul_left _ hN
  have hb : N ^ b + 1 ≤ N ^ (b + 1) := by
    rw [pow_succ]
    calc
      N ^ b + 1 ≤ N ^ b + N ^ b := Nat.add_le_add_left hb1 _
      _ = N ^ b * 2 := by omega
      _ ≤ N ^ b * N := Nat.mul_le_mul_left _ hN
  calc
    (N ^ a + 1) * (N ^ b + 1) ≤
        N ^ (a + 1) * N ^ (b + 1) := Nat.mul_le_mul ha hb
    _ = N ^ (a + b + 2) := by
      rw [← pow_add]
      congr 1
      omega

/-- Concrete polynomial meshes absorb their exact ordered-pair union loss.
The fixed-pair estimate is requested with `2 * (a+b+2)` extra powers, after
which the random spectral-pair event has the desired `N⁻ᴰ` tail. -/
theorem measure_localETHTwoResolventRandomBadEvent_le_inv_pow_of_pow_meshes
    {Ω : Type*} [MeasurableSpace Ω] {N D a b : ℕ}
    (hN : 2 ≤ N) (μ : Measure Ω) (f : Ω → ℂ → ℂ → ℂ)
    (etaF : ℝ → ℝ) (ξ E₀ R etaMin etaMax : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ)
    (gridThreshold : ℝ)
    (hsubset :
      localETHTwoResolventRandomBadEvent f etaF ξ lam threshold ⊆
        fixedTwoResolventGridBadEvent f
          (localETHRectangularSpectralGridPoint
            E₀ R etaMin etaMax (N ^ a) (N ^ b))
          gridThreshold)
    (hpair : ∀ x y : Fin (N ^ a + 1) × Fin (N ^ b + 1),
      μ (fixedTwoResolventGridPairBadEvent f
        (localETHRectangularSpectralGridPoint
          E₀ R etaMin etaMax (N ^ a) (N ^ b))
        gridThreshold x y) ≤
          ((N : ENNReal)⁻¹) ^ (D + 2 * (a + b + 2))) :
    μ (localETHTwoResolventRandomBadEvent f etaF ξ lam threshold) ≤
      ((N : ENNReal)⁻¹) ^ D := by
  exact measure_localETHTwoResolventRandomBadEvent_le_inv_pow_of_rectangularGrid
    (by omega) μ f etaF ξ E₀ R etaMin etaMax lam threshold gridThreshold
    hsubset (rectangularGrid_card_le_pow hN) hpair

end CEHNative.BlockBand.External.CEH
