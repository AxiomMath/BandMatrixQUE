module

public import BlockBand.Transmission.LawForced.ShiftDrift

/-!
# Resolvent facts for the trace-Lipschitz bound of the `κ ≡ 0` ratio drift

For `0 ⪯ T ⪯ I`, `g = Re Tr T` and a chamber point `z`:
* `resM_facts`, `facts_x`, `facts_y`: `R_w = (1 + wT)⁻¹` is a two-sided inverse with `‖R_w‖ ≤ ρ`
  and `0 ≤ S_T(w) ≤ ρ g` (`ρ = 1` at `w = x_i`, `ρ = (1 − y_j)⁻¹` at `w = −y_j`);
* `norm_lamM_le`: `‖Λ(T)‖ ≤ lamHat z`; `norm_T_le`: `‖T‖ ≤ 1` and `‖1 − T‖ ≤ 1`;
* **`dsum_nonneg_le`**: `0 ≤ dsum z T ≤ dsB z·(g + 1)²`;
* `abs_exp_sub_exp_le`: `|e^a − e^b| ≤ |a − b|` for `a, b ≤ 0`.

These feed the shift bounds `abs_eigS_sub_le_gen`, `abs_third_sub_le`, `abs_dsum_sub_le` and
`ratioDrift_shift_le`: `|ratioDrift D₀ E 0 u z μ_{T'} − ratioDrift D₀ E 0 u z μ_T| ≤
|D₀|/2·(ℓ·dsB(g'+1)² + dsK·c·(g+g'+1))` when `TrLip T' T c` and `|log F(T') − log F(T)| ≤ ℓ`.
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

theorem abs_exp_sub_exp_le {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  have key : ∀ u v : ℝ, v ≤ u → u ≤ 0 → Real.exp u - Real.exp v ≤ u - v := fun u v hvu hu => by
    have h1 := Real.add_one_le_exp (v - u)
    have h2 : Real.exp v = Real.exp u * Real.exp (v - u) := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp u ≤ 1 := Real.exp_le_one_iff.2 hu
    have h4 : 0 < Real.exp u := Real.exp_pos u
    rw [h2]; nlinarith
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact key a b h ha
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 h)]
    exact key b a h hb

section One

variable {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {T : Matrix (Fin W) (Fin W) ℂ}
  (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef)
include hz hT hT1

omit hz in
theorem resM_facts {w ρ : ℝ} (hw : ∀ k, 0 < 1 + w * ts_lam hT k)
    (hρ : ∀ k, (1 + w * ts_lam hT k)⁻¹ ≤ ρ) (hρ0 : 0 ≤ ρ) :
    ‖resM w T‖ ≤ ρ ∧ (1 + (w : ℂ) • T) * resM w T = 1 ∧ resM w T * (1 + (w : ℂ) • T) = 1 ∧
      0 ≤ eigS hT.1 w ∧ eigS hT.1 w ≤ ρ * T.trace.re := by
  obtain ⟨e, hr, hl⟩ := resM_eq_cjf hT (w := w) fun k => (hw k).ne'
  rw [e]
  refine ⟨norm_cjf_le hT hρ0 fun k => ?_, hr, hl, ?_, ?_⟩
  · rw [abs_of_pos (inv_pos.2 (hw k))]; exact hρ k
  · exact Finset.sum_nonneg fun k _ => div_nonneg (eigenvalues_mem hT hT1 k).1 (hw k).le
  · rw [← ts_sum_lam hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h0 := (eigenvalues_mem hT hT1 k).1
    rw [div_eq_mul_inv, mul_comm ρ]
    exact mul_le_mul_of_nonneg_left (hρ k) h0

theorem facts_x (i : Fin p) :
    ‖resM (z.1 i) T‖ ≤ 1 ∧ (1 + (z.1 i : ℂ) • T) * resM (z.1 i) T = 1 ∧
      resM (z.1 i) T * (1 + (z.1 i : ℂ) • T) = 1 ∧ 0 ≤ eigS hT.1 (z.1 i) ∧
      eigS hT.1 (z.1 i) ≤ 1 * T.trace.re :=
  resM_facts hT hT1 (one_add_pos_x hz hT hT1 i)
    (fun k => inv_le_one_of_one_le₀ (by nlinarith [hz.1 i, ts_lam_nonneg hT k]))
    zero_le_one

theorem facts_y (j : Fin p) :
    ‖resM (-z.2 j) T‖ ≤ rhoY (z.2 j) ∧ (1 + ((-z.2 j : ℝ) : ℂ) • T) * resM (-z.2 j) T = 1 ∧
      resM (-z.2 j) T * (1 + ((-z.2 j : ℝ) : ℂ) • T) = 1 ∧ 0 ≤ eigS hT.1 (-z.2 j) ∧
      eigS hT.1 (-z.2 j) ≤ rhoY (z.2 j) * T.trace.re :=
  resM_facts hT hT1 (one_add_pos_y hz hT hT1 j)
    (fun k => inv_anti₀ (by linarith [(hz.2 j).2]) (by
      nlinarith [(hz.2 j).1, ts_lam_le_one hT hT1 k]))
    (rhoY_pos hz j).le

theorem norm_lamM_le : ‖lamM z T‖ ≤ lamHat z := by
  rw [lamM_eq_cjf hz hT hT1]
  refine norm_cjf_le hT (lamHat_nonneg hz) fun k => ?_
  have h0 := ts_lam_nonneg hT k
  have h1 := ts_lam_le_one hT hT1 k
  rw [abs_of_nonneg (dualLam_nonneg hz h0 h1)]
  exact dualLam_le_lamHat hz h0 h1

omit hz in
theorem norm_T_le : ‖T‖ ≤ 1 ∧ ‖1 - T‖ ≤ 1 :=
  ⟨norm_le_one_of_psd hT hT1, norm_le_one_of_psd hT1 (by rw [sub_sub_cancel]; exact hT)⟩

theorem dsum_nonneg_le : 0 ≤ dsum z hT ∧ dsum z hT ≤ dsB z * (T.trace.re + 1) ^ 2 := by
  have hg : 0 ≤ T.trace.re := (mm_trace_posSemidef hT).1
  have hx : ∀ i, z.1 i * (1 + z.1 i) * eigS hT.1 (z.1 i) ^ 2 ≤
      z.1 i * (1 + z.1 i) * (T.trace.re + 1) ^ 2 := fun i => by
    obtain ⟨-, -, -, h0, h1⟩ := facts_x hz hT hT1 i
    have := hz.1 i
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (by linarith) 2) (by positivity)
  have hy : ∀ j, z.2 j * (1 - z.2 j) * eigS hT.1 (-z.2 j) ^ 2 ≤
      z.2 j * (1 - z.2 j) * rhoY (z.2 j) ^ 2 * (T.trace.re + 1) ^ 2 := fun j => by
    obtain ⟨-, -, -, h0, h1⟩ := facts_y hz hT hT1 j
    have := (hz.2 j).1; have : 0 ≤ 1 - z.2 j := by linarith [(hz.2 j).2]
    have hr := rhoY_pos hz j
    have : eigS hT.1 (-z.2 j) ^ 2 ≤ (rhoY (z.2 j) * (T.trace.re + 1)) ^ 2 :=
      pow_le_pow_left₀ h0 (h1.trans (by nlinarith)) 2
    calc z.2 j * (1 - z.2 j) * eigS hT.1 (-z.2 j) ^ 2
        ≤ z.2 j * (1 - z.2 j) * (rhoY (z.2 j) * (T.trace.re + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hk : ∀ k, 0 ≤ hT.1.eigenvalues k ^ 2 * (1 - hT.1.eigenvalues k) *
      dualLam z (hT.1.eigenvalues k) ^ 2 := fun k => by
    have hm := eigenvalues_mem hT hT1 k
    have : 0 ≤ 1 - hT.1.eigenvalues k := by linarith [hm.2]
    positivity
  have h3 : ∑ k, hT.1.eigenvalues k ^ 2 * (1 - hT.1.eigenvalues k) *
      dualLam z (hT.1.eigenvalues k) ^ 2 ≤ lamHat z ^ 2 * (T.trace.re + 1) ^ 2 := by
    calc _ ≤ ∑ k, lamHat z ^ 2 * hT.1.eigenvalues k := Finset.sum_le_sum fun k _ => by
          have hm := eigenvalues_mem hT hT1 k
          have hL := dualLam_le_lamHat hz hm.1 hm.2
          have hL0 := dualLam_nonneg hz hm.1 hm.2
          have : dualLam z (hT.1.eigenvalues k) ^ 2 ≤ lamHat z ^ 2 := pow_le_pow_left₀ hL0 hL 2
          have : hT.1.eigenvalues k ^ 2 * (1 - hT.1.eigenvalues k) ≤ hT.1.eigenvalues k := by
            nlinarith [hm.1, hm.2]
          have : 0 ≤ hT.1.eigenvalues k ^ 2 * (1 - hT.1.eigenvalues k) := by
            have : 0 ≤ 1 - hT.1.eigenvalues k := by linarith [hm.2]
            positivity
          nlinarith [sq_nonneg (lamHat z)]
      _ = lamHat z ^ 2 * T.trace.re := by rw [← Finset.mul_sum]; rw [← ts_sum_lam hT]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  refine ⟨add_nonneg (add_nonneg (Finset.sum_nonneg fun i _ => by
      have := hz.1 i; positivity) (Finset.sum_nonneg fun j _ => by
      have := (hz.2 j).1; have : 0 ≤ 1 - z.2 j := by linarith [(hz.2 j).2]
      positivity)) (Finset.sum_nonneg fun k _ => hk k), ?_⟩
  unfold dsum dsB
  have s1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hx i
  have s2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hy j
  rw [← Finset.sum_mul] at s1 s2
  nlinarith

end One

end BlockBand.Transmission.LawForced
