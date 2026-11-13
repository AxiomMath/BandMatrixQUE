module

public import BlockBand.Native.ErdosRiabov.Grid.Constants

set_option autoImplicit false

/-!
# The grid constant `C_g` and the side conditions of `gridToUniform_*_two`

The constants of the grid step and a proof that all its numerical side conditions hold for `N`
large.

Constants from the data `d : VSData` (`K = vsK = 8`, `D'' = d.Dpp`):
* `zigF d = K(2D''+1) + 2` (the floor exponent `F`), `zigB d k N = max 2 ((k-1)(C₀+1)² N)`
  (`b = 2`), `zigFloor d z N = min 1 (Im z/√(C₀+1)) N^{-K(2D''+1)}` (the floor `φ`);
* `zigN0 d`: the elementary threshold.

**`zig_conditions`**: for `N ≥ zigN0 d`, `1 ≤ k ≤ 8`, `P.D = d.D`, `z ∈ 𝒟`
(`BulkDomain N δ₀ κ C₀ z`), all numerical side conditions of `gridToUniform_iso_two` /
`gridToUniform_av_two` with `C = vsCg d`, `b = 2`, `F = zigF d`, `B = zigB d k N`,
`φ = zigFloor d z N` hold: `2 ≤ B`, `hBL`, `B ≤ N²`, `0 < φ`, `N^{-F} ≤ φ`, `(Im z)⁻¹ ≤ N`, `hCg`,
`2k + 1 ≤ N`, `hqE`, and `N ≥ (1 + √(C₀+1))^{K(2+D)}` (the `hNA` of the floor lemmas).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi

/-- The grid exponent `C_g = 3(81 + 16 D'')`. -/
def vsCg (d : VSData) : ℝ := 3 * (81 + 16 * d.Dpp)

/-- The floor exponent `F = K(2D''+1) + 2`. -/
def zigF (d : VSData) : ℝ := (vsK : ℝ) * (2 * d.Dpp + 1) + 2

/-- The M-term constant `B = max 2 ((k-1)(C₀+1)² N)`. -/
def zigB (d : VSData) (k N : ℕ) : ℝ := max 2 (((k - 1 : ℕ) : ℝ) * (d.C0 + 1) ^ 2 * N)

/-- The normalization floor `φ = min 1 (Im z/√(C₀+1)) N^{-K(2D''+1)}`. -/
def zigFloor (d : VSData) (z : ℂ) (N : ℕ) : ℝ :=
  min 1 (z.im / Real.sqrt (d.C0 + 1)) * (N : ℝ) ^ (-((vsK : ℝ) * (2 * d.Dpp + 1)))

/-- The elementary threshold for `N`. -/
def zigN0 (d : VSData) : ℝ :=
  max (max ((1 + Real.sqrt (d.C0 + 1)) ^ ((vsK : ℝ) * (2 + d.D))) (7 * (d.C0 + 1) ^ 2 + 2))
    (max (Real.sqrt (d.C0 + 1)) (max 17 (2 * (15 + 2 * d.D))))

theorem Dpp_nonneg (d : VSData) : 0 ≤ d.Dpp := d.Dpp_pos.le

theorem vsCg_facts (d : VSData) : 243 ≤ vsCg d ∧ 2 ≤ vsCg d ∧ 0 ≤ vsCg d := by
  have h := Dpp_nonneg d
  unfold vsCg
  refine ⟨by linarith, by linarith, by linarith⟩

theorem zigN0_ge (d : VSData) : 17 ≤ zigN0 d :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem normExp_le (k : ℕ) (hk : k ≤ 8) {D : ℝ} (hD : 0 ≤ D) : normExp k D ≤ 15 + 2 * D := by
  have hk' : (k : ℝ) ≤ 8 := by exact_mod_cast hk
  unfold normExp
  nlinarith

/-- **All numerical side conditions of `gridToUniform_*_two`** from `VSData` and `z ∈ 𝒟`, for
`N ≥ zigN0 d`. -/
theorem zig_conditions (d : VSData) {N : ℕ} (hN0 : zigN0 d ≤ N) {z : ℂ}
    (hz : BulkDomain N d.delta0 d.kappa d.C0 z) {k : ℕ} (hk : 1 ≤ k) (hk8 : k ≤ 8) :
    2 ≤ zigB d k N ∧
      ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM z‖ ^ 2)⁻¹ ≤ zigB d k N ∧
      zigB d k N ≤ (N : ℝ) ^ (2 : ℝ) ∧
      0 < zigFloor d z N ∧ (N : ℝ) ^ (-zigF d) ≤ zigFloor d z N ∧
      z.im⁻¹ ≤ N ∧
      (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * 2 + zigF d + 3 ≤ vsCg d / 3 ∧
      2 * (k : ℝ) + 1 ≤ N ∧
      (N : ℝ) ^ (-vsCg d) / z.im * normExp k d.D ≤ 1 / 2 ∧
      (1 + Real.sqrt (d.C0 + 1)) ^ ((vsK : ℝ) * (2 + d.D)) ≤ N := by
  have h17 := zigN0_ge d
  have hN17 : (17 : ℝ) ≤ N := h17.trans hN0
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hN0' : (0 : ℝ) < N := by linarith
  have hC1 : 0 < d.C0 + 1 := d.C0_add_one_pos
  have hC0 : 0 ≤ d.C0 := by linarith [d.C0_ge_one]
  have hD : 0 ≤ d.D := by linarith [d.D_ge_six]
  have hk' : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hzpos := hz.im_pos hNpos
  have hzN := im_inv_le_of_bulk hNpos d.delta0_pos.le hz
  -- the four components of `zigN0`
  have hA : (1 + Real.sqrt (d.C0 + 1)) ^ ((vsK : ℝ) * (2 + d.D)) ≤ N :=
    (le_max_left _ _ |>.trans (le_max_left _ _)).trans hN0
  have hBth : 7 * (d.C0 + 1) ^ 2 + 2 ≤ N := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hN0
  have hsq : Real.sqrt (d.C0 + 1) ≤ N := (le_max_left _ _ |>.trans (le_max_right _ _)).trans hN0
  have hEth : 2 * (15 + 2 * d.D) ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hN0
  -- `B`
  have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ 7 := by
    rw [Nat.cast_sub hk]
    push_cast
    linarith
  have hkm0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hB2 : 2 ≤ zigB d k N := le_max_left _ _
  have hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM z‖ ^ 2)⁻¹ ≤ zigB d k N := by
    have h1 := inv_one_sub_normSq_le hC0 hzpos hz.2.2
    have h2 : (d.C0 + 1) ^ 2 / z.im ≤ (d.C0 + 1) ^ 2 * N := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hzN (by positivity)
    refine le_trans ?_ (le_max_right _ _)
    calc ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM z‖ ^ 2)⁻¹
        ≤ ((k - 1 : ℕ) : ℝ) * ((d.C0 + 1) ^ 2 * N) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hkm0
      _ = ((k - 1 : ℕ) : ℝ) * (d.C0 + 1) ^ 2 * N := by ring
  have hBN : zigB d k N ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    apply max_le
    · nlinarith
    · have h1 : ((k - 1 : ℕ) : ℝ) * (d.C0 + 1) ^ 2 ≤ 7 * (d.C0 + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hkm1 (by positivity)
      have h2 : ((k - 1 : ℕ) : ℝ) * (d.C0 + 1) ^ 2 * N ≤ 7 * (d.C0 + 1) ^ 2 * N :=
        mul_le_mul_of_nonneg_right h1 hN0'.le
      nlinarith
  -- the floor
  have hsq0 : 0 < Real.sqrt (d.C0 + 1) := Real.sqrt_pos.mpr hC1
  have hφpos : 0 < zigFloor d z N := by
    unfold zigFloor
    exact mul_pos (lt_min one_pos (div_pos hzpos hsq0)) (Real.rpow_pos_of_pos hN0' _)
  have hφF : (N : ℝ) ^ (-zigF d) ≤ zigFloor d z N := by
    unfold zigFloor zigF
    have hm : (N : ℝ) ^ (-(2 : ℝ)) ≤ min 1 (z.im / Real.sqrt (d.C0 + 1)) := by
      apply le_min
      · exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
      · rw [Real.rpow_neg hN0'.le, Real.rpow_two, le_div_iff₀ hsq0]
        have hzi : (N : ℝ)⁻¹ ≤ z.im := by
          rw [inv_le_comm₀ hN0' hzpos]
          exact hzN
        calc ((N : ℝ) ^ 2)⁻¹ * Real.sqrt (d.C0 + 1) ≤ ((N : ℝ) ^ 2)⁻¹ * N :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (N : ℝ)⁻¹ := by field_simp
          _ ≤ z.im := hzi
    rw [show -((vsK : ℝ) * (2 * d.Dpp + 1) + 2) = -(2 : ℝ) + -((vsK : ℝ) * (2 * d.Dpp + 1)) by
      ring, Real.rpow_add hN0']
    exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hN0'.le _)
  -- `hCg`
  have hCg : (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * 2 + zigF d + 3 ≤ vsCg d / 3 := by
    unfold zigF vsCg vsK
    push_cast
    linarith
  -- `hqE`
  have hqE : (N : ℝ) ^ (-vsCg d) / z.im * normExp k d.D ≤ 1 / 2 := by
    have hE := normExp_le k hk8 hD
    have hE0 := normExp_nonneg k hD
    have hCg2 := (vsCg_facts d).2.1
    have h1 : (N : ℝ) ^ (-vsCg d) / z.im ≤ (N : ℝ) ^ (-vsCg d) * N := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hzN (Real.rpow_nonneg hN0'.le _)
    have h2 : (N : ℝ) ^ (-vsCg d) * N ≤ (N : ℝ)⁻¹ := by
      calc (N : ℝ) ^ (-vsCg d) * N = (N : ℝ) ^ (-vsCg d + 1) := by
            rw [Real.rpow_add hN0', Real.rpow_one]
        _ ≤ (N : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = (N : ℝ)⁻¹ := Real.rpow_neg_one _
    have h3 : (N : ℝ)⁻¹ * normExp k d.D ≤ 1 / 2 := by
      rw [inv_mul_le_iff₀ hN0']
      linarith
    calc (N : ℝ) ^ (-vsCg d) / z.im * normExp k d.D ≤ (N : ℝ)⁻¹ * normExp k d.D :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hE0
      _ ≤ 1 / 2 := h3
  exact ⟨hB2, hBL, hBN, hφpos, hφF, hzN, hCg, by linarith, hqE, hA⟩

end BlockBand.Native.ErdosRiabov.Grid
