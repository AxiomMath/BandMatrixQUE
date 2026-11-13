module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic

/-!
# Cyclic Fourier algebra

The discrete Fourier transform on `ZMod n`: the normalized test coefficients and the mass modes,
bilinear and normalized Parseval identities, the behaviour under translation and conjugation, and
the expansion of a test against a zero-total-mass profile over the nonzero modes.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The normalized positive-sign test coefficient. -/
def coefficient (t : ZMod n → ℂ) (m : ZMod n) : ℂ :=
  (n : ℂ)⁻¹ * ZMod.dft t (-m)

/-- The negative-sign mass mode. -/
def mode (p : ZMod n → ℂ) (m : ZMod n) : ℂ := ZMod.dft p m

/-- Symmetry of the finite DFT pairing, with no complex conjugation. -/
theorem dft_pairing (f g : ZMod n → ℂ) :
    (∑ m, ZMod.dft f m * g m) = ∑ k, f k * ZMod.dft g k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro m _
  rw [mul_comm m k]
  ring

/-- Bilinear Parseval, with the counting-measure factor `n`. -/
theorem bilinear_parseval (f g : ZMod n → ℂ) :
    (∑ m, ZMod.dft f m * ZMod.dft g m) =
      (n : ℂ) * ∑ k, f k * g (-k) := by
  rw [dft_pairing, ZMod.dft_dft, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_eq_mul]
  ring

/-- Normalized test/mass Fourier expansion, before removing mode zero. -/
theorem coefficient_mode_pairing (t p : ZMod n → ℂ) :
    (∑ m, coefficient t m * mode p m) = ∑ k, t k * p k := by
  have h := bilinear_parseval (fun k => t (-k)) p
  rw [ZMod.dft_comp_neg] at h
  simp only [coefficient, mode]
  calc
    (∑ m, ((n : ℂ)⁻¹ * ZMod.dft t (-m)) * ZMod.dft p m) =
        (n : ℂ)⁻¹ * ∑ m, ZMod.dft t (-m) * ZMod.dft p m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ k, t (-k) * p (-k) := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (n : ℂ)), one_mul]
    _ = ∑ k, t k * p k := by
      exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun k => by simp)

/-- The zero mass mode is the total mass. -/
theorem mode_zero (p : ZMod n → ℂ) : mode p 0 = ∑ k, p k :=
  ZMod.dft_apply_zero p

/-- A cyclic translate multiplies a mass mode by its positive character. -/
theorem mode_translate (p : ZMod n → ℂ) (a m : ZMod n) :
    mode (fun k => p (k + a)) m = ZMod.stdAddChar (a * m) * mode p m := by
  unfold mode
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ ?_
  intro k
  change ZMod.stdAddChar (-(k * m)) * p (k + a) =
    ZMod.stdAddChar (a * m) * (ZMod.stdAddChar (-((k + a) * m)) * p (k + a))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring
/-- Conjugation reverses the standard cyclic character. -/
theorem character_conj (x : ZMod n) :
    starRingEnd ℂ (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- Conjugation reverses a Fourier frequency. -/
theorem dft_conj (f : ZMod n → ℂ) (m : ZMod n) :
    ZMod.dft (fun k => starRingEnd ℂ (f k)) m =
      starRingEnd ℂ (ZMod.dft f (-m)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, character_conj]
  simp only [mul_neg, neg_neg]

/-- Counting-measure Parseval for the unnormalized mass modes. -/
theorem parseval (f : ZMod n → ℂ) :
    (∑ m, ‖ZMod.dft f m‖ ^ 2) = (n : ℝ) * ∑ k, ‖f k‖ ^ 2 := by
  have h := bilinear_parseval f (fun k => starRingEnd ℂ (f (-k)))
  have hg (m : ZMod n) : ZMod.dft (fun k => starRingEnd ℂ (f (-k))) m =
      starRingEnd ℂ (ZMod.dft f m) := by
    change ZMod.dft (fun k => (fun j => starRingEnd ℂ (f j)) (-k)) m = _
    calc
      _ = ZMod.dft (fun j => starRingEnd ℂ (f j)) (-m) :=
        congr_fun (ZMod.dft_comp_neg (fun j => starRingEnd ℂ (f j))) m
      _ = _ := by rw [dft_conj, neg_neg]
  simp only [hg, neg_neg, Complex.mul_conj'] at h
  exact_mod_cast h

/-- Normalized Parseval in the test-coefficient convention. -/
theorem normalized_parseval (t : ZMod n → ℂ) :
    (∑ m, ‖coefficient t m‖ ^ 2) = (n : ℝ)⁻¹ * ∑ k, ‖t k‖ ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp only [coefficient, norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum]
  have he : (∑ m : ZMod n, ‖ZMod.dft t (-m)‖ ^ 2) =
      ∑ m : ZMod n, ‖ZMod.dft t m‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun m => by simp)
  rw [he, parseval]
  field_simp

/-- Tests with sup norm at most one have normalized Fourier energy at most one. -/
theorem coefficient_energy_le_one (t : ZMod n → ℂ) (ht : ∀ k, ‖t k‖ ≤ 1) :
    (∑ m, ‖coefficient t m‖ ^ 2) ≤ 1 := by
  rw [normalized_parseval]
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  have hs : (∑ k, ‖t k‖ ^ 2) ≤ (n : ℝ) := by
    calc
      (∑ k, ‖t k‖ ^ 2) ≤ ∑ _k : ZMod n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        nlinarith [norm_nonneg (t k), ht k]
      _ = (n : ℝ) := by simp
  calc
    (n : ℝ)⁻¹ * (∑ k, ‖t k‖ ^ 2) ≤ (n : ℝ)⁻¹ * n :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
    _ = 1 := inv_mul_cancel₀ hn.ne'
/-- Zero-total-mass profiles have only nonzero modes in the test expansion. -/
theorem centered_pairing (t p : ZMod n → ℂ) (hp : ∑ k, p k = 0) :
    (∑ k, t k * p k) =
      ∑ m ∈ (Finset.univ.erase 0), coefficient t m * mode p m := by
  rw [← coefficient_mode_pairing]
  have hzero : coefficient t 0 * mode p 0 = 0 := by rw [mode_zero, hp, mul_zero]
  have h := Finset.sum_erase_add (s := Finset.univ)
    (f := fun m => coefficient t m * mode p m) (Finset.mem_univ (0 : ZMod n))
  simpa only [hzero, add_zero] using h.symm
end BlockBand.QUE.Fourier
