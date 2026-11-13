module

public import Mathlib
public import BlockBand.External.ErdosRiabov.Control

/-!
# The bulk box lies in the Erdős–Riabov spectral domain

The bulk box `|e| ≤ 2 - κ`, `N^{-1+δ₀} ≤ η`, `|e + iη| ≤ C₀` of the short-ring local law
lies in the spectral domain of Erdős–Riabov (2.9); the phase clause follows from a
deterministic bound on the semicircle branch.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External

/-- Phase separation in the bulk (Erdős–Riabov (2.9), third clause), uniformly in the height:
for `0 < κ < 2`, `|e| ≤ 2 - κ` and every real `η`,
`κ ≤ ‖(m/|m|)² - 1‖` with `m = semicircleM (e + iη)` the ER branch. Proof: from
`m² + zm + 1 = 0`, `e|m|² = -Re m (|m|² + 1)`, so `4 (Re m)² ≤ e² |m|²`, and
`-Re((m/|m|)² - 1) = 2 (Im m)²/|m|² ≥ κ`. Deterministic. -/
theorem phase_of_bulk {e η κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < 2) (he : |e| ≤ 2 - κ) :
    κ ≤ ‖(ErdosRiabov.semicircleM ((e : ℂ) + (η : ℂ) * Complex.I) /
        ‖ErdosRiabov.semicircleM ((e : ℂ) + (η : ℂ) * Complex.I)‖) ^ 2 - 1‖ := by
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I with hz
  set m := ErdosRiabov.semicircleM z with hmdef
  have hD : m ^ 2 + z * m + 1 = 0 := ErdosRiabov.semicircleM_dyson z
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hD
    simp at hD
  have hre := congrArg Complex.re hD
  have him := congrArg Complex.im hD
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, hz,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
  set a := m.re
  set c := m.im
  have hs : ‖m‖ ^ 2 = a ^ 2 + c ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hr : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  set s := ‖m‖ ^ 2 with hsdef
  have hspos : 0 < s := by positivity
  have hE : e * s = -(a * (s + 1)) := by
    rw [hs]
    have : a * (a * a - c * c + (e * a - η * c) + 1) +
        c * (a * c + c * a + (e * c + η * a)) = 0 := by
      rw [show a * a - c * c + (e * a - η * c) + 1 = 0 by linarith,
        show a * c + c * a + (e * c + η * a) = 0 by linarith]
      ring
    nlinarith [this]
  have he2 : e ^ 2 ≤ (2 - κ) ^ 2 := by
    have h0 : 0 ≤ 2 - κ := by linarith
    have := abs_le.mp he
    nlinarith
  have hA : 4 * a ^ 2 * s ≤ e ^ 2 * s ^ 2 := by
    have : e ^ 2 * s ^ 2 = a ^ 2 * (s + 1) ^ 2 := by
      have h := congrArg (fun t => t ^ 2) hE
      simp only [mul_pow, neg_sq] at h
      linarith
    rw [this]
    nlinarith [sq_nonneg (s - 1), sq_nonneg a]
  have hA' : 4 * a ^ 2 ≤ (2 - κ) ^ 2 * s := by
    have h1 : 4 * a ^ 2 * s ≤ (2 - κ) ^ 2 * s * s := by
      nlinarith [mul_le_mul_of_nonneg_right he2 (sq_nonneg s)]
    exact le_of_mul_le_mul_right h1 hspos
  have hkey : κ * s ≤ 2 * c ^ 2 := by
    have hc : c ^ 2 = s - a ^ 2 := by rw [hs]; ring
    rw [hc]
    nlinarith [mul_pos hκ (show 0 < 2 - κ by linarith), hspos]
  have hre_u : ((m / (‖m‖ : ℂ)) ^ 2 - 1).re = (a ^ 2 - c ^ 2) / s - 1 := by
    rw [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re,
      Complex.div_ofReal_re, Complex.div_ofReal_im]
    rw [hsdef]
    field_simp
    rfl
  have hnorm : -(((m / (‖m‖ : ℂ)) ^ 2 - 1).re) ≤ ‖(m / (‖m‖ : ℂ)) ^ 2 - 1‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [hre_u] at hnorm
  have hval : -((a ^ 2 - c ^ 2) / s - 1) = 2 * c ^ 2 / s := by
    field_simp
    rw [hs]
    ring
  rw [hval] at hnorm
  refine le_trans ?_ hnorm
  rw [le_div_iff₀ hspos]
  linarith

/-- The bulk box of the short-ring local law lies in the ER spectral domain
(Erdős–Riabov (2.9)): for parameters `q` with `q.kappa ≤ κ`, `q.kappa < 2`, and for
`|e| ≤ 2 - κ`, `N^{-1+q.delta0} ≤ η`, `‖e + iη‖ ≤ q.C0`, with `N ≥ 1`. The phase clause uses
`phase_of_bulk` at `q.kappa` (the bulk at `κ` is contained in the bulk at `q.kappa`).
Deterministic; uniform in `N`, `e`, `η`. -/
theorem spectralDomain_of_bulk (q : ErdosRiabov.ModelParameters) (N : ℕ) (hN : 0 < N)
    {κ e η : ℝ} (hqκ : q.kappa ≤ κ) (hq2 : q.kappa < 2) (he : |e| ≤ 2 - κ)
    (hη : (N : ℝ) ^ (-1 + q.delta0) ≤ η) (hz : ‖(e : ℂ) + (η : ℂ) * Complex.I‖ ≤ q.C0) :
    ErdosRiabov.SpectralDomain q N ((e : ℂ) + (η : ℂ) * Complex.I) := by
  have hηpos : 0 < η :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hη
  refine ⟨?_, hz, phase_of_bulk q.kappa_pos hq2 (by linarith)⟩
  have him : ((e : ℂ) + (η : ℂ) * Complex.I).im = η := by simp
  rw [him, abs_of_pos hηpos]
  exact hη

end BlockBand.Adapters.ErdosRiabov
