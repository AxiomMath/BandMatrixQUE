module

public import BlockBand.Native.ErdosRiabov.SatLin.Fixed
public import BlockBand.Native.ErdosRiabov.LLGrid.P7

/-!
# The side conditions of the grid step from `VSData`

Grid exponent `C = LLGrid.llCg d`, mesh `h = N^{-C}`, level `N^{-C/3}`,
`B = Grid.zigB d k N`, floor `φ = Grid.zigFloor d z N`, `N ≥ Grid.zigN0 d`, any `1 ≤ k ≤ 8`.
These are the `k`-general forms of `LLGrid.floor_le_norm`, `LLGrid.errLip_le_floor` and the
factor bound in `LLGrid.norm_ratio_le_two` (stated there for `k = n+4`), with the same proofs;
the real-arithmetic helpers `LLGrid.crude_le_pow`, `LLGrid.pow_five_mul_le`,
`LLGrid.mesh_le_floor`, `LLGrid.im_add_one_le` are reused.

* `side_floor`, `side_errLip`, `side_factor`, `side_herr`, `absorb_lin`: the side conditions of
  `satLin_measure_le` at `C = llCg d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open scoped NNReal

/-- **Absorption of the additive error of `linQ_le_near`** (real arithmetic). -/
theorem absorb_lin {Nr h r y M eL φ k : ℝ} (hN : 17 ≤ Nr) (hr0 : 0 ≤ r) (hr : r ≤ Nr)
    (hy : y + 1 ≤ Nr) (hk0 : 0 ≤ k) (hk : k ≤ 8) (hM0 : 0 ≤ M)
    (hM : M ≤ 2 * Nr ^ 27) (hh0 : 0 ≤ h) (hh : 16 * Nr ^ 33 * h ≤ φ) (heL0 : 0 ≤ eL)
    (heL : Nr ^ 5 * eL ≤ φ / 2) :
    (y + 1) * (k * (Nr * (h * r ^ 2) * M + r * (Nr * eL))) ≤ φ := by
  have hN0 : 0 ≤ Nr := by linarith
  have hA : (y + 1) * (k * (Nr * (h * r ^ 2) * M)) ≤ Nr * (8 * (Nr * (h * Nr ^ 2) *
      (2 * Nr ^ 27))) := by gcongr
  have hB : (y + 1) * (k * (r * (Nr * eL))) ≤ Nr * (8 * (Nr * (Nr * eL))) := by gcongr
  have e1 : Nr * (8 * (Nr * (h * Nr ^ 2) * (2 * Nr ^ 27))) = 16 * h * Nr ^ 31 := by ring
  have e2 : Nr * (8 * (Nr * (Nr * eL))) = 8 * Nr ^ 3 * eL := by ring
  have hsq : 16 ≤ Nr ^ 2 := by nlinarith
  have h31 : 16 * (16 * h * Nr ^ 31) ≤ 16 * Nr ^ 33 * h := by
    have : Nr ^ 33 = Nr ^ 31 * Nr ^ 2 := by ring
    rw [this]
    have := pow_nonneg hN0 31
    nlinarith [mul_nonneg (mul_nonneg this hh0) (sub_nonneg.2 hsq)]
  have h3 : 2 * (8 * Nr ^ 3 * eL) ≤ Nr ^ 5 * eL := by
    have : Nr ^ 5 = Nr ^ 3 * Nr ^ 2 := by ring
    rw [this]
    have := pow_nonneg hN0 3
    nlinarith [mul_nonneg (mul_nonneg this heL0) (sub_nonneg.2 hsq)]
  have hφ0 : 0 ≤ φ := le_trans (by positivity) hh
  nlinarith

section Side

variable (d : VSData) {p : BlockBand.Parameters} (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
  (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hN0 : Grid.zigN0 d ≤ ((p.n * p.W : ℕ) : ℝ))

include hPW hPD hz hN0 in
/-- The floor `φ = zigFloor d z N ≤ L_t^{β_k} s^av_t(u)` on `[0,1]` (`1 ≤ k ≤ 8`). -/
theorem side_floor {k : ℕ} (hk : 1 ≤ k) (hk8 : k ≤ 8) (u : Fin k → Fin (p.n * p.W)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      Grid.zigFloor d P.z (p.n * p.W) ≤ P.lEta t ^ Expo.lossBeta k * P.sAv u t := by
  intro t ht
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hWN : p.W ≤ p.n * p.W := Nat.le_mul_of_pos_left _ (by have := p.n_ge_four; omega)
  have hD : 0 ≤ P.D := by rw [hPD]; linarith [d.D_ge_six]
  obtain ⟨-, -, -, -, -, -, -, -, -, hNA⟩ := Grid.zig_conditions d hN0 hz hk hk8
  have hDpp : (vsK : ℝ) * (2 + P.D) + 1 ≤ (vsK : ℝ) * (2 * d.Dpp + 1) := by
    rw [hPD]; exact floor_exponent_le_of_vsData d
  have hNA' : (1 + Real.sqrt (d.C0 + 1)) ^ ((vsK : ℝ) * (2 + P.D)) ≤
      ((p.n * p.W : ℕ) : ℝ) := by
    rw [hPD]; exact hNA
  exact (Grid.PsiData.normAv_floor P) hNpos p.W_pos hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hD hz hPW hk (by unfold vsK; omega) hDpp hNA' t ht
    ((fun _ => false), u)

include hz hN0 in
/-- `errLip_k(N^{-C/3}, τ, B) ≤ N^{-8} φ` for `τ ≤ N^{-C}` (`C = llCg d`, `1 ≤ k ≤ 8`). -/
theorem side_errLip {k : ℕ} (hk : 1 ≤ k) (hk8 : k ≤ 8) {τ : ℝ}
    (hτ : τ ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d)) :
    (Grid.PsiData.errLip P) k (((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d / 3)) τ
        (Grid.zigB d k (p.n * p.W)) ≤
      ((p.n * p.W : ℕ) : ℝ) ^ (-(8 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hNpos
  have h17 := Grid.zigN0_ge d
  have hN1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hNr0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by linarith
  obtain ⟨hB2, -, hBN, hφ, hφF, hzN, -, hNk, -, -⟩ := Grid.zig_conditions d hN0 hz hk hk8
  obtain ⟨hC0, -, -, -⟩ := LLGrid.llCg_facts d
  have hφ' : 0 < ((p.n * p.W : ℕ) : ℝ) ^ (-(6 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) :=
    mul_pos (Real.rpow_pos_of_pos hNr0 _) hφ
  have hφ'F : ((p.n * p.W : ℕ) : ℝ) ^ (-(Grid.zigF d + 6)) ≤
      ((p.n * p.W : ℕ) : ℝ) ^ (-(6 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) := by
    rw [show -(Grid.zigF d + 6) = -(6 : ℝ) + -Grid.zigF d by ring, Real.rpow_add hNr0]
    exact mul_le_mul_of_nonneg_left hφF (Real.rpow_pos_of_pos hNr0 _).le
  have hk8' : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hCg' : (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * 2 + (Grid.zigF d + 6) + 3 ≤ LLGrid.llCg d / 3 := by
    unfold LLGrid.llCg
    linarith
  have hB0 : 0 ≤ Grid.zigB d k (p.n * p.W) := by linarith
  have herr := (Grid.PsiData.errLip_div_le_inv P) hN1 hzi hzN hB0 hBN (by norm_num) hφ' hφ'F
    hC0.le hk hCg' hNk
  have h1 := (Grid.PsiData.errLip_mono P) k
    (δ := ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d / 3)) hτ hB0
  have h2 := (div_le_iff₀ hφ').mp herr
  calc _ ≤ _ := h1
    _ ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-(2 : ℝ)) *
        (((p.n * p.W : ℕ) : ℝ) ^ (-(6 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W)) := h2
    _ = ((p.n * p.W : ℕ) : ℝ) ^ (-(8 : ℝ)) * Grid.zigFloor d P.z (p.n * p.W) := by
        rw [← mul_assoc, ← Real.rpow_add hNr0]
        norm_num

include hPD hz hN0 in
/-- `1 + h/Im z ≤ 2` and `(1 + h/Im z)^{E_k} ≤ 2` at `h = N^{-C}` (`C = llCg d`). -/
theorem side_factor {k : ℕ} (hk : 1 ≤ k) (hk8 : k ≤ 8) :
    1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) (LLGrid.llCg d) : ℝ) / P.z.im ≤ 2 ∧
      (1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) (LLGrid.llCg d) : ℝ) / P.z.im) ^
        Grid.normExp k P.D ≤ 2 := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hNpos
  have hD : 0 ≤ P.D := by rw [hPD]; linarith [d.D_ge_six]
  have h17 := Grid.zigN0_ge d
  have hN1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  obtain ⟨-, -, -, -, -, -, -, -, hqE, -⟩ := Grid.zig_conditions d hN0 hz hk hk8
  obtain ⟨-, hCv, -, -⟩ := LLGrid.llCg_facts d
  rw [VS.meshPow_coe (by linarith)]
  have hhv : ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d) ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-Grid.vsCg d) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hE1 : 1 ≤ Grid.normExp k P.D := by
    unfold Grid.normExp
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  have hx0 : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d) / P.z.im :=
    div_nonneg (Real.rpow_nonneg (by linarith) _) hzi.le
  have hxE : ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d) / P.z.im * Grid.normExp k P.D ≤ 1 / 2 := by
    rw [hPD] at hE1 ⊢
    calc ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d) / P.z.im * Grid.normExp k d.D
        ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-Grid.vsCg d) / P.z.im * Grid.normExp k d.D := by
          gcongr
      _ ≤ 1 / 2 := hqE
  refine ⟨?_, Grid.factor_le_two hx0 (by linarith) hxE⟩
  have : ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d) / P.z.im ≤
      ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d) / P.z.im * Grid.normExp k P.D :=
    le_mul_of_one_le_right hx0 hE1
  linarith

include hz hN0 in
/-- **The error condition of the grid step** at `C = llCg d`, `B = zigB`, `φ = zigFloor`. -/
theorem side_herr {k : ℕ} (hk : 1 ≤ k) (hk8 : k ≤ 8) :
    (P.z.im + 1) * (k * ((p.n * p.W : ℕ) *
        ((VS.meshPow ((p.n * p.W : ℕ) : ℝ) (LLGrid.llCg d) : ℝ) * P.z.im⁻¹ ^ 2) *
        ((p.n * p.W : ℕ) * (max 1 P.z.im⁻¹) ^ k +
          (p.n * p.W : ℕ) * Grid.zigB d k (p.n * p.W) ^ (2 * (k - 1) - 1)) +
        P.z.im⁻¹ * ((p.n * p.W : ℕ) * (Grid.PsiData.errLip P) k
          (((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d / 3))
          (VS.meshPow ((p.n * p.W : ℕ) : ℝ) (LLGrid.llCg d)) (Grid.zigB d k (p.n * p.W))))) ≤
      Grid.zigFloor d P.z (p.n * p.W) := by
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hzi := hz.im_pos hNpos
  have h17 := Grid.zigN0_ge d
  have hN17 : (17 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := h17.trans hN0
  have hN2 : (2 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hNr0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by linarith
  obtain ⟨hB2, -, hBN, hφ, hφF, hzN, -, -, -, -⟩ := Grid.zig_conditions d hN0 hz hk hk8
  obtain ⟨-, -, hF0, hCF⟩ := LLGrid.llCg_facts d
  have hmesh : (VS.meshPow ((p.n * p.W : ℕ) : ℝ) (LLGrid.llCg d) : ℝ) =
      ((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d) := VS.meshPow_coe hNr0.le _
  have hB0 : 0 ≤ Grid.zigB d k (p.n * p.W) := by linarith
  have hBN' : Grid.zigB d k (p.n * p.W) ≤ ((p.n * p.W : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_two]; exact hBN
  have hM27 := LLGrid.crude_le_pow (by linarith) (le_trans zero_le_one (le_max_left _ _))
    (max_le (by linarith) hzN) hB0 hBN' hk8
  have herr := side_errLip d P hz hN0 hk hk8 (τ := (VS.meshPow ((p.n * p.W : ℕ) : ℝ)
    (LLGrid.llCg d) : ℝ)) hmesh.le
  have heL := LLGrid.pow_five_mul_le hN2 hφ.le herr
  have hhφ := LLGrid.mesh_le_floor (C := LLGrid.llCg d) hN2 (by linarith) hφF
  rw [← hmesh] at hhφ
  have hk' : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hM0 : 0 ≤ ((p.n * p.W : ℕ) : ℝ) * (max 1 P.z.im⁻¹) ^ k +
      (p.n * p.W : ℕ) * Grid.zigB d k (p.n * p.W) ^ (2 * (k - 1) - 1) := by
    have : 0 ≤ max 1 P.z.im⁻¹ := zero_le_one.trans (le_max_left _ _)
    positivity
  have heL0 : 0 ≤ (Grid.PsiData.errLip P) k (((p.n * p.W : ℕ) : ℝ) ^ (-LLGrid.llCg d / 3))
      (VS.meshPow ((p.n * p.W : ℕ) : ℝ) (LLGrid.llCg d)) (Grid.zigB d k (p.n * p.W)) :=
    (Grid.PsiData.errLip_nonneg P) k (Real.rpow_nonneg hNr0.le _) (NNReal.coe_nonneg _) hB0
  exact absorb_lin hN17 (inv_nonneg.2 hzi.le) hzN (LLGrid.im_add_one_le d P hz hN0)
    (Nat.cast_nonneg _) hk' hM0 hM27 (NNReal.coe_nonneg _) hhφ heL0 heL

end Side

end BlockBand.Native.ErdosRiabov.SatLin
