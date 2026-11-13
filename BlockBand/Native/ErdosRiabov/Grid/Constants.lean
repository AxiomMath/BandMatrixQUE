module

public import BlockBand.Native.ErdosRiabov.Grid.Uniform

set_option autoImplicit false

/-!
# Grid to uniform: the constants for `Ψ_t ≤ 2X + N^{-1}`

* `factor_le_two`: `(1 + x)^E ≤ 2` if `x, E ≥ 0`, `x E ≤ 1/2`;
* `im_inv_le_of_bulk`: `(Im z)⁻¹ ≤ N` on the bulk domain;
* `inv_one_sub_normSq_le`: `(1 - |m|²)⁻¹ ≤ (C₀+1)²/Im z` for `m = m(z)`, `Im z > 0`, `|z| ≤ C₀`;
* `PsiData.errLip_div_le_inv`: if `(Im z)⁻¹ ≤ N`, `0 ≤ B ≤ N^b`, `φ ≥ N^{-F}`, `N ≥ 2k + 1`
  and `C/3 ≥ k + 4 + 4(k-1)b + F + 3`, then `errLip(N^{-C/3}, N^{-C})/φ ≤ N^{-2}`
  (so also `N errLip/φ ≤ N^{-1}` for `Ψ^{av}`);
* **`PsiData.gridToUniform_iso_two`**, **`PsiData.gridToUniform_av_two`**: under these conditions
  and `(Im z)⁻¹ N^{-C} E ≤ 1/2`, for `X ≥ 0`:
  `P(∃ t ≤ T, Ψ_t > 2X + N^{-1}) ≤ P(grid violation) + P(modulus event)`; combine with
  `modulusEvent_whp` for `≤ … + N^{-D}`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open MeasureTheory Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

theorem factor_le_two {x E : ℝ} (hx : 0 ≤ x) (hE : 0 ≤ E) (hxE : x * E ≤ 1 / 2) :
    (1 + x) ^ E ≤ 2 := by
  have h1 : (1 + x) ^ E ≤ Real.exp x ^ E :=
    Real.rpow_le_rpow (by linarith) (by linarith [Real.add_one_le_exp x]) hE
  rw [← Real.exp_mul] at h1
  have h2 : Real.exp (x * E) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 hxE
  have h3 : Real.exp (1 / 2) ≤ 2 := by
    have he := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

theorem inv_one_sub_normSq_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {z : ℂ} (hz : 0 < z.im) (hzC : ‖z‖ ≤ C₀) :
    (1 - ‖semicircleM z‖ ^ 2)⁻¹ ≤ (C₀ + 1) ^ 2 / z.im := by
  have hid := vsHeight_identity z 1
  have hη1 : vsHeight z 1 = z.im := by simp [vsHeight]
  rw [hη1, one_mul] at hid
  have hm1 := norm_semicircleM_lt_one hz.ne'
  have hmge := semicircleM_norm_ge hC₀ hz.ne' hzC
  have hmim := semicircleM_im_pos hz
  have hmim1 : (semicircleM z).im ≤ 1 := (Complex.im_le_norm _).trans hm1.le
  have hm0 : 0 ≤ ‖semicircleM z‖ := norm_nonneg _
  have hpos : 0 < 1 - ‖semicircleM z‖ ^ 2 := by nlinarith
  have hC1 : 0 < C₀ + 1 := by linarith
  have hsq : ((C₀ + 1) ^ 2)⁻¹ ≤ ‖semicircleM z‖ ^ 2 := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hmge 2
  -- `1 - |m|² ≥ |m|² Im z ≥ Im z/(C₀+1)²`
  have hlow : z.im / (C₀ + 1) ^ 2 ≤ 1 - ‖semicircleM z‖ ^ 2 := by
    have h1 : ‖semicircleM z‖ ^ 2 * z.im ≤ 1 - ‖semicircleM z‖ ^ 2 := by
      rw [hid]
      exact mul_le_of_le_one_left hpos.le hmim1
    calc z.im / (C₀ + 1) ^ 2 = ((C₀ + 1) ^ 2)⁻¹ * z.im := by ring
      _ ≤ ‖semicircleM z‖ ^ 2 * z.im := by gcongr
      _ ≤ _ := h1
  calc (1 - ‖semicircleM z‖ ^ 2)⁻¹ ≤ (z.im / (C₀ + 1) ^ 2)⁻¹ :=
        inv_anti₀ (div_pos hz (by positivity)) hlow
    _ = (C₀ + 1) ^ 2 / z.im := by rw [inv_div]

/-- `(Im z)⁻¹ ≤ N` on the bulk domain (`δ₀ ≥ 0`, `N ≥ 1`). -/
theorem im_inv_le_of_bulk {N : ℕ} (hN : 0 < N) {δ₀ κ C₀ : ℝ} (hδ₀ : 0 ≤ δ₀) {z : ℂ}
    (hz : BulkDomain N δ₀ κ C₀ z) : z.im⁻¹ ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ (-(1 : ℝ)) ≤ z.im :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hz.2.1
  rw [Real.rpow_neg_one] at h1
  have hzpos := hz.im_pos hN
  calc z.im⁻¹ ≤ ((N : ℝ)⁻¹)⁻¹ := inv_anti₀ (by positivity) h1
    _ = N := inv_inv _

namespace PsiData

variable {N k : ℕ} (P : PsiData N)

/-- **The error term at mesh `N^{-C}`, level `N^{-C/3}`**: `errLip/φ ≤ N^{-2}`. -/
theorem errLip_div_le_inv (hN1 : 1 ≤ (N : ℝ)) (hz : 0 < P.z.im) (hzN : P.z.im⁻¹ ≤ N) {B b : ℝ}
    (hB0 : 0 ≤ B) (hBN : B ≤ (N : ℝ) ^ b) (hb : 0 ≤ b) {F φ : ℝ} (hφ0 : 0 < φ)
    (hφ : (N : ℝ) ^ (-F) ≤ φ) {C : ℝ} (hC : 0 ≤ C) (hk : 1 ≤ k)
    (hCg : (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * b + F + 3 ≤ C / 3)
    (hNk : 2 * (k : ℝ) + 1 ≤ N) :
    (PsiData.errLip P) k ((N : ℝ) ^ (-C / 3)) ((N : ℝ) ^ (-C)) B / φ ≤ (N : ℝ) ^ (-(2 : ℝ)) := by
  have hN0 : 0 < (N : ℝ) := by linarith
  have rp : ∀ a : ℝ, 0 < (N : ℝ) ^ a := fun a => Real.rpow_pos_of_pos hN0 a
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set A : ℝ := (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * b with hA
  -- the pieces as powers of `N`
  have hc : max 1 P.z.im⁻¹ ≤ (N : ℝ) := max_le hN1 hzN
  have hck : (max 1 P.z.im⁻¹) ^ k ≤ (N : ℝ) ^ (k : ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hc k
  have hz2 : P.z.im⁻¹ ^ 2 ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (inv_nonneg.2 hz.le) hzN 2
  have hpow1 : (N : ℝ) ^ (-C) ≤ (N : ℝ) ^ (2 - C / 3) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsum : (N : ℝ) ^ 2 * (N : ℝ) ^ (-C / 3) + (N : ℝ) ^ (-C) ≤ 2 * (N : ℝ) ^ (2 - C / 3) := by
    have e : (N : ℝ) ^ 2 * (N : ℝ) ^ (-C / 3) = (N : ℝ) ^ (2 - C / 3) := by
      rw [← Real.rpow_two, ← Real.rpow_add hN0]
      ring_nf
    rw [e]
    linarith
  have hBk : B ^ (4 * (k - 1)) ≤ (N : ℝ) ^ (4 * ((k : ℝ) - 1) * b) := by
    have h1 : B ^ (4 * (k - 1)) ≤ ((N : ℝ) ^ b) ^ (4 * (k - 1)) := pow_le_pow_left₀ hB0 hBN _
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub hk]
    push_cast
    ring
  have hterm1 : (k : ℝ) * (max 1 P.z.im⁻¹) ^ k *
      (P.z.im⁻¹ ^ 2 * ((N : ℝ) ^ 2 * (N : ℝ) ^ (-C / 3) + (N : ℝ) ^ (-C))) ≤
      2 * k * (N : ℝ) ^ (A - C / 3) := by
    have e : (N : ℝ) ^ (A - C / 3) ≥ (N : ℝ) ^ (k : ℝ) * ((N : ℝ) ^ (2 : ℝ) *
        (N : ℝ) ^ (2 - C / 3)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      rw [hA]
      nlinarith
    have hm0 : 0 ≤ (max 1 P.z.im⁻¹) ^ k := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    calc (k : ℝ) * (max 1 P.z.im⁻¹) ^ k *
          (P.z.im⁻¹ ^ 2 * ((N : ℝ) ^ 2 * (N : ℝ) ^ (-C / 3) + (N : ℝ) ^ (-C)))
        ≤ (k : ℝ) * (N : ℝ) ^ (k : ℝ) * ((N : ℝ) ^ (2 : ℝ) * (2 * (N : ℝ) ^ (2 - C / 3))) := by
          gcongr
      _ = 2 * k * ((N : ℝ) ^ (k : ℝ) * ((N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (2 - C / 3))) := by ring
      _ ≤ 2 * k * (N : ℝ) ^ (A - C / 3) := by gcongr
  have hterm2 : B ^ (4 * (k - 1)) * (N : ℝ) ^ (-C) ≤ (N : ℝ) ^ (A - C / 3) := by
    calc B ^ (4 * (k - 1)) * (N : ℝ) ^ (-C)
        ≤ (N : ℝ) ^ (4 * ((k : ℝ) - 1) * b) * (N : ℝ) ^ (-C) :=
          mul_le_mul_of_nonneg_right hBk (rp _).le
      _ = (N : ℝ) ^ (4 * ((k : ℝ) - 1) * b + -C) := (Real.rpow_add hN0 _ _).symm
      _ ≤ (N : ℝ) ^ (A - C / 3) := Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hA]; linarith)
  have htot : (PsiData.errLip P) k ((N : ℝ) ^ (-C / 3)) ((N : ℝ) ^ (-C)) B ≤
      (2 * k + 1) * (N : ℝ) ^ (A - C / 3) := by
    unfold PsiData.errLip
    nlinarith [hterm1, hterm2]
  have hφinv : φ⁻¹ ≤ (N : ℝ) ^ F := by
    calc φ⁻¹ ≤ ((N : ℝ) ^ (-F))⁻¹ := inv_anti₀ (rp _) hφ
      _ = (N : ℝ) ^ F := by rw [Real.rpow_neg hN0.le, inv_inv]
  have hE0 : 0 ≤ (PsiData.errLip P) k ((N : ℝ) ^ (-C / 3)) ((N : ℝ) ^ (-C)) B :=
    (PsiData.errLip_nonneg P) k (rp _).le (rp _).le hB0
  calc (PsiData.errLip P) k ((N : ℝ) ^ (-C / 3)) ((N : ℝ) ^ (-C)) B / φ
      = (PsiData.errLip P) k ((N : ℝ) ^ (-C / 3)) ((N : ℝ) ^ (-C)) B * φ⁻¹ := div_eq_mul_inv _ _
    _ ≤ ((2 * k + 1) * (N : ℝ) ^ (A - C / 3)) * (N : ℝ) ^ F :=
        mul_le_mul htot hφinv (inv_nonneg.2 hφ0.le) (by positivity)
    _ ≤ (N : ℝ) * (N : ℝ) ^ (A - C / 3) * (N : ℝ) ^ F := by gcongr
    _ = (N : ℝ) ^ (1 + (A - C / 3) + F) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]
    _ ≤ (N : ℝ) ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hA] at *; linarith)

end PsiData

namespace PsiData

variable {p : BlockBand.Parameters} {k : ℕ} (P : PsiData (p.n * p.W))

theorem grid_factor_le_two (hz : 0 < P.z.im) (hD : 0 ≤ P.D) {C : ℝ}
    (hqE : ((p.n * p.W : ℕ) : ℝ) ^ (-C) / P.z.im * normExp k P.D ≤ 1 / 2) :
    (1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) / P.z.im) ^ normExp k P.D ≤ 2 := by
  rw [VS.meshPow_coe (Nat.cast_nonneg _)]
  exact factor_le_two (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hz.le)
    (normExp_nonneg k hD) hqE

/-- **`Ψ^iso_t ≤ 2X + N^{-1}`** (grid lemma form): under the constant conditions of
`errLip_div_le_inv` and `grid_factor_le_two`, for `X ≥ 0`,
`P(∃ t ≤ T, Ψ^iso_t > 2X + N^{-1}) ≤ P(grid violation at level X) + P(modulus event)`. -/
theorem gridToUniform_iso_two (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k)
    (hk8 : k ≤ 8) {C : ℝ} (hC : 0 ≤ C) {B b : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    (hBN : B ≤ ((p.n * p.W : ℕ) : ℝ) ^ b) (hb : 0 ≤ b) {F φ : ℝ} (hφ : 0 < φ)
    (hφF : ((p.n * p.W : ℕ) : ℝ) ^ (-F) ≤ φ) (hfl : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ i : IsoIdx (p.n * p.W) k,
        φ ≤ P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t)
    (hzN : P.z.im⁻¹ ≤ ((p.n * p.W : ℕ) : ℝ))
    (hCg : (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * b + F + 3 ≤ C / 3)
    (hNk : 2 * (k : ℝ) + 1 ≤ ((p.n * p.W : ℕ) : ℝ))
    (hqE : ((p.n * p.W : ℕ) : ℝ) ^ (-C) / P.z.im * normExp k P.D ≤ 1 / 2)
    (T : RingSample p → ℝ≥0) (hT : ∀ x, T x ≤ 1) {X : ℝ} (hX : 0 ≤ X) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
        2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiIso k t (VS.vsBandFin p t x)} ≤
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
        (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
        X < P.bigPsiIso k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
          (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
        driverLaw (κ := Fin (ringDim p)) μ (modulusEvent p C) := by
  have hN1 := VS.one_le_dim p
  have hN0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hfac := (PsiData.grid_factor_le_two P) hz hD hqE
  have herr := (PsiData.errLip_div_le_inv P) hN1 hz hzN (by linarith) hBN hb hφ hφF hC hk hCg hNk
  have hmesh : (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) = ((p.n * p.W : ℕ) : ℝ) ^ (-C) :=
    VS.meshPow_coe (Nat.cast_nonneg _) C
  have hN2 : ((p.n * p.W : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ ((p.n * p.W : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  refine le_trans (measure_mono fun x hx => ?_)
    ((PsiData.gridToUniform_iso P) μ hW hz hS hD hk hk8 C hB2 hBL hφ hfl T hT X)
  obtain ⟨t, ht, hlt⟩ := hx
  refine ⟨t, ht, lt_of_le_of_lt ?_ hlt⟩
  rw [← hmesh] at herr
  have h1 := mul_le_mul_of_nonneg_right hfac hX
  linarith

/-- **`Ψ^av_t ≤ 2X + N^{-1}`** (grid lemma form). -/
theorem gridToUniform_av_two (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k)
    (hk8 : k ≤ 8) {C : ℝ} (hC : 0 ≤ C) {B b : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    (hBN : B ≤ ((p.n * p.W : ℕ) : ℝ) ^ b) (hb : 0 ≤ b) {F φ : ℝ} (hφ : 0 < φ)
    (hφF : ((p.n * p.W : ℕ) : ℝ) ^ (-F) ≤ φ) (hfl : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ i : AvIdx (p.n * p.W) k, φ ≤ P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t)
    (hzN : P.z.im⁻¹ ≤ ((p.n * p.W : ℕ) : ℝ))
    (hCg : (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * b + F + 3 ≤ C / 3)
    (hNk : 2 * (k : ℝ) + 1 ≤ ((p.n * p.W : ℕ) : ℝ))
    (hqE : ((p.n * p.W : ℕ) : ℝ) ^ (-C) / P.z.im * normExp k P.D ≤ 1 / 2)
    (T : RingSample p → ℝ≥0) (hT : ∀ x, T x ≤ 1) {X : ℝ} (hX : 0 ≤ X) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
        2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiAv k t (VS.vsBandFin p t x)} ≤
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
        (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
        X < P.bigPsiAv k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
          (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
        driverLaw (κ := Fin (ringDim p)) μ (modulusEvent p C) := by
  have hN1 := VS.one_le_dim p
  have hN0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hfac := (PsiData.grid_factor_le_two P) hz hD hqE
  have herr := (PsiData.errLip_div_le_inv P) hN1 hz hzN (by linarith) hBN hb hφ hφF hC hk hCg hNk
  have hmesh : (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) = ((p.n * p.W : ℕ) : ℝ) ^ (-C) :=
    VS.meshPow_coe (Nat.cast_nonneg _) C
  have hN2 : ((p.n * p.W : ℕ) : ℝ) * ((p.n * p.W : ℕ) : ℝ) ^ (-(2 : ℝ)) =
      ((p.n * p.W : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_one_add' hN0.le (by norm_num)]
    norm_num
  refine le_trans (measure_mono fun x hx => ?_)
    ((PsiData.gridToUniform_av P) μ hW hz hS hD hk hk8 C hB2 hBL hφ hfl T hT X)
  obtain ⟨t, ht, hlt⟩ := hx
  refine ⟨t, ht, lt_of_le_of_lt ?_ hlt⟩
  rw [← hmesh] at herr
  have h1 := mul_le_mul_of_nonneg_right hfac hX
  have h2 : ((p.n * p.W : ℕ) : ℝ) * (PsiData.errLip P) k (((p.n * p.W : ℕ) : ℝ) ^ (-C / 3))
      (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) B / φ ≤ ((p.n * p.W : ℕ) : ℝ)⁻¹ := by
    rw [mul_div_assoc, ← hN2]
    exact mul_le_mul_of_nonneg_left herr hN0.le
  linarith

end PsiData

end BlockBand.Native.ErdosRiabov.Grid
