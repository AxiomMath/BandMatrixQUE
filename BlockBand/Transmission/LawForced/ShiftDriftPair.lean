module

public import BlockBand.Transmission.LawForced.ShiftDriftLip

/-!
# The `κ ≡ 0` ratio drift between two contractions

For `0 ⪯ T, T' ⪯ I`, `TrLip T' T c`, `c ≥ 0`:
* `abs_re_trace_sub_le`, `abs_eigS_sub_le_gen`, `abs_third_sub_le`;
* **`abs_dsum_sub_le`**: `|dsum z T' − dsum z T| ≤ dsK z·c·(g + g' + 1)`.

This is the main input of the drift comparison `ratioDrift_shift_le`, proved in a sibling module.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {p W : ℕ}

theorem abs_re_trace_sub_le {A' A : Matrix (Fin W) (Fin W) ℂ} {C : ℝ} (h : TrLip A' A C)
    (hC : 0 ≤ C) : |A'.trace.re - A.trace.re| ≤ C := by
  have h1 := h 1
  rw [Matrix.one_mul, trace_sub] at h1
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (h1.trans
    (mul_le_of_le_one_left hC PassiveLayer.norm_one_le'))

theorem abs_sq_sub_le {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') :
    |a' ^ 2 - a ^ 2| ≤ |a' - a| * (a' + a) := by
  rw [show a' ^ 2 - a ^ 2 = (a' - a) * (a' + a) by ring, abs_mul,
    abs_of_nonneg (show 0 ≤ a' + a by linarith)]

section Two

variable {T T' : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef)
  (hT' : T'.PosSemidef) (hT1' : (1 - T').PosSemidef) {c : ℝ} (hc : 0 ≤ c) (hL : TrLip T' T c)
include hT hT1 hT' hT1' hc hL

omit hT hT1 hT' hT1' in
theorem trLip_resM {w ρ : ℝ} (hρ : 0 ≤ ρ) (hn : ‖resM w T‖ ≤ ρ) (hn' : ‖resM w T'‖ ≤ ρ)
    (hr : (1 + (w : ℂ) • T) * resM w T = 1) (hl' : resM w T' * (1 + (w : ℂ) • T') = 1) :
    TrLip (resM w T') (resM w T) (|w| * ρ * ρ * c) :=
  trLip_mono (trLip_inv hc hL w hr hl') (by
    have := abs_nonneg w
    have h1 : ‖resM w T‖ * ‖resM w T'‖ ≤ ρ * ρ :=
      mul_le_mul hn hn' (norm_nonneg _) hρ
    have h2 : |w| * ‖resM w T‖ * ‖resM w T'‖ ≤ |w| * ρ * ρ := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg w)
    exact mul_le_mul_of_nonneg_right h2 hc)

omit hT1' in
theorem abs_eigS_sub_le_gen {w ρ : ℝ} (hρ : 0 ≤ ρ) (hw : ∀ k, 0 < 1 + w * ts_lam hT k)
    (hw' : ∀ k, 0 < 1 + w * ts_lam hT' k) (hn : ‖resM w T‖ ≤ ρ) (hn' : ‖resM w T'‖ ≤ ρ)
    (hr : (1 + (w : ℂ) • T) * resM w T = 1) (hl' : resM w T' * (1 + (w : ℂ) • T') = 1) :
    |eigS hT'.1 w - eigS hT.1 w| ≤ (ρ + |w| * ρ * ρ) * c := by
  rw [eigS_eq_trace hT hw, eigS_eq_trace hT' hw']
  have hR := trLip_resM hc hL hρ hn hn' hr hl'
  have hP := trLip_mul hc (by positivity) hL hR
  refine abs_re_trace_sub_le (trLip_mono hP ?_) (by positivity)
  have hT0 := (norm_T_le hT hT1).1
  have : ‖T‖ * (|w| * ρ * ρ * c) ≤ |w| * ρ * ρ * c :=
    mul_le_of_le_one_left (by positivity) hT0
  nlinarith [mul_le_mul_of_nonneg_right hn' hc]

theorem trLip_lamM {z : DualCoord p} (hz : IsRatioRange z.1 z.2) :
    TrLip (lamM z T') (lamM z T) (lamLip2 z * c) := by
  have hx : ∀ i ∈ Finset.univ, TrLip ((z.1 i : ℂ) • resM (z.1 i) T') ((z.1 i : ℂ) • resM (z.1 i) T)
      (z.1 i ^ 2 * c) := fun i _ => by
    obtain ⟨n, r, -, -, -⟩ := facts_x hz hT hT1 i
    obtain ⟨n', -, l', -, -⟩ := facts_x hz hT' hT1' i
    refine trLip_mono (trLip_smul (trLip_resM hc hL zero_le_one n n' r l') _) ?_
    rw [abs_of_nonneg (hz.1 i)]; nlinarith [abs_of_nonneg (hz.1 i)]
  have hy : ∀ j ∈ Finset.univ, TrLip ((z.2 j : ℂ) • resM (-z.2 j) T')
      ((z.2 j : ℂ) • resM (-z.2 j) T) (z.2 j ^ 2 * rhoY (z.2 j) ^ 2 * c) := fun j _ => by
    obtain ⟨n, r, -, -, -⟩ := facts_y hz hT hT1 j
    obtain ⟨n', -, l', -, -⟩ := facts_y hz hT' hT1' j
    refine trLip_mono (trLip_smul (trLip_resM hc hL (rhoY_pos hz j).le n n'
      r l') _) ?_
    rw [abs_of_nonneg (hz.2 j).1, abs_neg, abs_of_nonneg (hz.2 j).1]
    nlinarith
  have h := trLip_add (trLip_sum _ hx) (trLip_sum _ hy)
  refine trLip_mono h (le_of_eq ?_)
  rw [lamLip2, add_mul, Finset.sum_mul, Finset.sum_mul]

theorem abs_third_sub_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) :
    |(T' * T' * (1 - T') * lamM z T' * lamM z T').trace.re -
        (T * T * (1 - T) * lamM z T * lamM z T).trace.re| ≤
      (3 * lamHat z ^ 2 + 2 * lamHat z * lamLip2 z) * c := by
  obtain ⟨n0, n1⟩ := norm_T_le hT hT1
  obtain ⟨n0', n1'⟩ := norm_T_le hT' hT1'
  have hΛ := norm_lamM_le hz hT hT1
  have hΛ' := norm_lamM_le hz hT' hT1'
  have hΛ0 := lamHat_nonneg hz
  have hL2 := lamLip2_nonneg hz
  have hLm := trLip_lamM hT hT1 hT' hT1' hc hL hz
  have nTT : ‖T * T‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg T])
  have nTT1 : ‖T * T * (1 - T)‖ ≤ 1 :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (T * T), norm_nonneg (1 - T)])
  have nTTL : ‖T * T * (1 - T) * lamM z T‖ ≤ lamHat z :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (T * T * (1 - T)), norm_nonneg (lamM z T)])
  have s1 := trLip_mono (trLip_mul hc hc hL hL) (show ‖T'‖ * c + ‖T‖ * c ≤ 2 * c by nlinarith)
  have s2 := trLip_mono (trLip_mul (by positivity) hc s1 (trLip_one_sub hL))
    (show ‖1 - T'‖ * (2 * c) + ‖T * T‖ * c ≤ 3 * c by nlinarith)
  have s3 := trLip_mono (trLip_mul (by positivity) (by positivity) s2 hLm)
    (show ‖lamM z T'‖ * (3 * c) + ‖T * T * (1 - T)‖ * (lamLip2 z * c) ≤
      (3 * lamHat z + lamLip2 z) * c by
      have a1 := mul_le_mul_of_nonneg_right hΛ' (by positivity : (0 : ℝ) ≤ 3 * c)
      have a2 := mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ lamLip2 z * c) nTT1
      nlinarith)
  have s4 := trLip_mono (trLip_mul (by positivity) (by positivity) s3 hLm)
    (show ‖lamM z T'‖ * ((3 * lamHat z + lamLip2 z) * c) +
      ‖T * T * (1 - T) * lamM z T‖ * (lamLip2 z * c) ≤
      (3 * lamHat z ^ 2 + 2 * lamHat z * lamLip2 z) * c by
      have a1 := mul_le_mul_of_nonneg_right hΛ' (by positivity :
        (0 : ℝ) ≤ (3 * lamHat z + lamLip2 z) * c)
      have a2 := mul_le_mul_of_nonneg_right nTTL (by positivity : (0 : ℝ) ≤ lamLip2 z * c)
      nlinarith)
  exact abs_re_trace_sub_le s4 (by positivity)

/-- **The bracket is trace-Lipschitz.** -/
theorem abs_dsum_sub_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) :
    |dsum z hT' - dsum z hT| ≤ dsK z * c * (T.trace.re + T'.trace.re + 1) := by
  have hg := (mm_trace_posSemidef hT).1
  have hg' := (mm_trace_posSemidef hT').1
  have hx : ∀ i, |z.1 i * (1 + z.1 i) * eigS hT'.1 (z.1 i) ^ 2 -
      z.1 i * (1 + z.1 i) * eigS hT.1 (z.1 i) ^ 2| ≤
      z.1 i * (1 + z.1 i) * (1 + z.1 i) * c * (T.trace.re + T'.trace.re + 1) := fun i => by
    obtain ⟨n, r, -, a0, a1⟩ := facts_x hz hT hT1 i
    obtain ⟨n', -, l', a0', a1'⟩ := facts_x hz hT' hT1' i
    have hd := abs_eigS_sub_le_gen hT hT1 hT' hc hL zero_le_one
      (one_add_pos_x hz hT hT1 i) (one_add_pos_x hz hT' hT1' i) n n' r l'
    rw [abs_of_nonneg (hz.1 i)] at hd
    have hs := abs_sq_sub_le a0 a0'
    have hxi := hz.1 i
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have : |eigS hT'.1 (z.1 i) - eigS hT.1 (z.1 i)| * (eigS hT'.1 (z.1 i) + eigS hT.1 (z.1 i))
        ≤ ((1 + z.1 i * 1 * 1) * c) * (T.trace.re + T'.trace.re + 1) :=
      mul_le_mul hd (by linarith) (by positivity) (by positivity)
    calc z.1 i * (1 + z.1 i) * |eigS hT'.1 (z.1 i) ^ 2 - eigS hT.1 (z.1 i) ^ 2|
        ≤ z.1 i * (1 + z.1 i) * (((1 + z.1 i * 1 * 1) * c) * (T.trace.re + T'.trace.re + 1)) :=
          mul_le_mul_of_nonneg_left (hs.trans this) (by positivity)
      _ = _ := by ring
  have hy : ∀ j, |z.2 j * (1 - z.2 j) * eigS hT'.1 (-z.2 j) ^ 2 -
      z.2 j * (1 - z.2 j) * eigS hT.1 (-z.2 j) ^ 2| ≤
      z.2 j * (1 - z.2 j) * (rhoY (z.2 j) + z.2 j * rhoY (z.2 j) ^ 2) * rhoY (z.2 j) * c *
        (T.trace.re + T'.trace.re + 1) := fun j => by
    obtain ⟨n, r, -, a0, a1⟩ := facts_y hz hT hT1 j
    obtain ⟨n', -, l', a0', a1'⟩ := facts_y hz hT' hT1' j
    have hρ := rhoY_pos hz j
    have hd := abs_eigS_sub_le_gen hT hT1 hT' hc hL hρ.le
      (one_add_pos_y hz hT hT1 j) (one_add_pos_y hz hT' hT1' j) n n' r l'
    rw [abs_neg, abs_of_nonneg (hz.2 j).1] at hd
    have hs := abs_sq_sub_le a0 a0'
    have hyj := (hz.2 j).1
    have hy1 : 0 ≤ 1 - z.2 j := by linarith [(hz.2 j).2]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    have hsum : eigS hT'.1 (-z.2 j) + eigS hT.1 (-z.2 j) ≤
        rhoY (z.2 j) * (T.trace.re + T'.trace.re + 1) := by nlinarith
    have : |eigS hT'.1 (-z.2 j) - eigS hT.1 (-z.2 j)| *
        (eigS hT'.1 (-z.2 j) + eigS hT.1 (-z.2 j)) ≤
        ((rhoY (z.2 j) + z.2 j * rhoY (z.2 j) * rhoY (z.2 j)) * c) *
          (rhoY (z.2 j) * (T.trace.re + T'.trace.re + 1)) :=
      mul_le_mul hd hsum (by positivity) (by positivity)
    calc z.2 j * (1 - z.2 j) * |eigS hT'.1 (-z.2 j) ^ 2 - eigS hT.1 (-z.2 j) ^ 2|
        ≤ z.2 j * (1 - z.2 j) * (((rhoY (z.2 j) + z.2 j * rhoY (z.2 j) * rhoY (z.2 j)) * c) *
          (rhoY (z.2 j) * (T.trace.re + T'.trace.re + 1))) :=
          mul_le_mul_of_nonneg_left (hs.trans this) (by positivity)
      _ = _ := by ring
  have h3 := abs_third_sub_le hT hT1 hT' hT1' hc hL hz
  rw [← third_eq_trace hz hT hT1, ← third_eq_trace hz hT' hT1'] at h3
  unfold dsum
  set A := T.trace.re + T'.trace.re + 1
  have hA : 1 ≤ A := by linarith
  have s1 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hx i)
  have s2 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hy j)
  rw [Finset.sum_sub_distrib] at s1 s2
  rw [← Finset.sum_mul, ← Finset.sum_mul] at s1 s2
  have h3' : (3 * lamHat z ^ 2 + 2 * lamHat z * lamLip2 z) * c ≤
      (3 * lamHat z ^ 2 + 2 * lamHat z * lamLip2 z) * c * A := by
    have := lamHat_nonneg hz; have := lamLip2_nonneg hz
    exact le_mul_of_one_le_right (by positivity) hA
  have e : ∀ a b c' a' b' c'' : ℝ, a' + b' + c'' - (a + b + c') = (a' - a) + (b' - b) + (c'' - c') :=
    fun _ _ _ _ _ _ => by ring
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  unfold dsK
  nlinarith

end Two

end BlockBand.Transmission.LawForced
