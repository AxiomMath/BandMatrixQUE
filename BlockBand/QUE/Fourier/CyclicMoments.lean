module
public import BlockBand.QUE.Fourier.FiniteAlgebra
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# Fourier moments under cyclic invariance

Under cyclic invariance of the law, distinct Fourier modes are orthogonal in expectation, block
masses have cyclic covariance with the modes, and the `n/2`-normalized signed pair numerator is
given explicitly (`signed_pair_numerator`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open MeasureTheory
variable {n : ℕ} [NeZero n] {Ω : Type*} [MeasurableSpace Ω]

/-- Distinct modes are orthogonal in expectation under cyclic invariance (Bochner integrals with
the same measure on both sides). -/
theorem expected_distinct_mode_orthogonality
    (μ : Measure Ω) (p : Ω → ZMod n → ℂ) (r s : ZMod n) (hrs : r ≠ s)
    (hshift :
      (∫ ω, mode (fun k => p ω (k + 1)) r *
        starRingEnd ℂ (mode (fun k => p ω (k + 1)) s) ∂μ) =
      ∫ ω, mode (p ω) r * starRingEnd ℂ (mode (p ω) s) ∂μ) :
    (∫ ω, mode (p ω) r * starRingEnd ℂ (mode (p ω) s) ∂μ) = 0 := by
  have hpoint (ω : Ω) : mode (fun k => p ω (k + 1)) r *
      starRingEnd ℂ (mode (fun k => p ω (k + 1)) s) =
      ZMod.stdAddChar (r - s) *
        (mode (p ω) r * starRingEnd ℂ (mode (p ω) s)) := by
    rw [mode_translate, mode_translate, (starRingEnd ℂ).map_mul, character_conj]
    simp only [one_mul]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hpoint] at hshift
  rw [integral_const_mul] at hshift
  have hc : ZMod.stdAddChar (r - s) ≠ (1 : ℂ) := by
    intro h
    have hz : r - s = 0 := ZMod.injective_stdAddChar (by simpa using h)
    exact hrs (sub_eq_zero.mp hz)
  have he : (ZMod.stdAddChar (r - s) - 1) *
      (∫ ω, mode (p ω) r * starRingEnd ℂ (mode (p ω) s) ∂μ) = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hc)
/-- Cyclic covariance of a block mass with a Fourier mode. The shift hypothesis translates the
full profile and the selected block simultaneously. -/
theorem expected_mass_mode_covariance
    (μ : Measure Ω) (p : Ω → ZMod n → ℂ) (m i : ZMod n)
    (hint : ∀ k, Integrable (fun ω => p ω k * starRingEnd ℂ (mode (p ω) m)) μ)
    (hshift : ∀ a : ZMod n,
      (∫ ω, p ω a * starRingEnd ℂ (mode (fun k => p ω (k + a)) m) ∂μ) =
      ∫ ω, p ω 0 * starRingEnd ℂ (mode (p ω) m) ∂μ) :
    (∫ ω, p ω i * starRingEnd ℂ (mode (p ω) m) ∂μ) =
      ZMod.stdAddChar (i * m) * (n : ℂ)⁻¹ *
        (∫ ω, mode (p ω) m * starRingEnd ℂ (mode (p ω) m) ∂μ) := by
  let M (a : ZMod n) := ∫ ω, p ω a * starRingEnd ℂ (mode (p ω) m) ∂μ
  have hM (a : ZMod n) : M a = ZMod.stdAddChar (a * m) * M 0 := by
    have h := hshift a
    simp only [mode_translate, (starRingEnd ℂ).map_mul, character_conj] at h
    have he (ω : Ω) : p ω a *
        (ZMod.stdAddChar (-(a * m)) * starRingEnd ℂ (mode (p ω) m)) =
        ZMod.stdAddChar (-(a * m)) *
          (p ω a * starRingEnd ℂ (mode (p ω) m)) := by ring
    simp_rw [he] at h
    rw [integral_const_mul] at h
    change ZMod.stdAddChar (-(a * m)) * M a = M 0 at h
    rw [← h, ← mul_assoc, ← AddChar.map_add_eq_mul]
    simp
  have hΓ : (∫ ω, mode (p ω) m * starRingEnd ℂ (mode (p ω) m) ∂μ) =
      (n : ℂ) * M 0 := by
    have he (ω : Ω) : mode (p ω) m * starRingEnd ℂ (mode (p ω) m) =
        ∑ k, ZMod.stdAddChar (-(k * m)) *
          (p ω k * starRingEnd ℂ (mode (p ω) m)) := by
      simp only [mode, ZMod.dft_apply, smul_eq_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun k _ => (hint k).const_mul _)]
    simp_rw [integral_const_mul]
    change (∑ k, ZMod.stdAddChar (-(k * m)) * M k) = _
    calc
      (∑ k, ZMod.stdAddChar (-(k * m)) * M k) = ∑ _k : ZMod n, M 0 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hM k, ← mul_assoc, ← AddChar.map_add_eq_mul]
        simp
      _ = (n : ℂ) * M 0 := by simp
  change M i = _
  rw [hΓ, hM i]
  field_simp [NeZero.ne (n : ℂ)]
/-- The `n/2`-normalized signed numerator identity, from the cyclic covariance. -/
theorem signed_pair_numerator
    (μ : Measure Ω) (p : Ω → ZMod n → ℂ) (m i : ZMod n)
    (hint : ∀ k, Integrable (fun ω => p ω k * starRingEnd ℂ (mode (p ω) m)) μ)
    (hshift : ∀ a : ZMod n,
      (∫ ω, p ω a * starRingEnd ℂ (mode (fun k => p ω (k + a)) m) ∂μ) =
      ∫ ω, p ω 0 * starRingEnd ℂ (mode (p ω) m) ∂μ) :
    (n : ℂ) / 2 * (∫ ω, (p ω i - p ω (i + 1)) *
      starRingEnd ℂ (mode (p ω) m) ∂μ) =
      (1 - ZMod.stdAddChar m) / 2 * ZMod.stdAddChar (i * m) *
        (∫ ω, mode (p ω) m * starRingEnd ℂ (mode (p ω) m) ∂μ) := by
  simp_rw [sub_mul]
  rw [integral_sub (hint i) (hint (i + 1)),
    expected_mass_mode_covariance μ p m i hint hshift,
    expected_mass_mode_covariance μ p m (i + 1) hint hshift]
  rw [add_mul, one_mul, AddChar.map_add_eq_mul]
  field_simp [NeZero.ne (n : ℂ)]
end BlockBand.QUE.Fourier
