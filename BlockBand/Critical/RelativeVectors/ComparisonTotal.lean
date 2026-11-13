module

public import BlockBand.Critical.RelativeVectors.ComparisonScales
public import BlockBand.Critical.RelativeVectors.ComparisonPoly

/-!
# The total error is `O(N^{-1/5000})`

`rmv_total_le`: at the critical scales, with `P = N^{3+2max(A,1)}`, `ε = P^{-5}`, the
localization exponent `D_sp ≥ 10(3+2max(A,1))` and the good-path exponent `D₁ ≥ 5(3+2max(A,1))`,
the sum of
* the integrated generator difference on good samples (`goodSample_integral_le`),
* the crude integrated generator difference times the conditional failure `N^{-D₁}`
  (`crudeSample_integral_le`, `step1_goodPaths`),
* the equilibration `e^{-b₀Nt/(2ℓ)}(‖z‖₂ + √(Nr))` (`equilSample_le`, `arrayNormSq ≤ N r Z²`)

is at most `rmvConst · N^{-1/5000}`, with `rmvConst` independent of `N` and of `D₁, D_sp`.
The rate `1/5000` is the variation exponent `κ - 3θ/2 + 2ε = -2/10000`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.CoarseRelative

variable {N : ℕ}

/-- The order `m = ⌈5000(3 + 2max(A,1))⌉` of the factorial bound for the equilibration. -/
def rmvOrder (A : ℝ) : ℕ := ⌈5000 * (3 + 2 * max A 1)⌉₊

/-- The constant of the total error bound. -/
def rmvConst (r k : ℕ) (A c r₀ s₀ v₀ I R γ c₁ Csp Cd b₀ : ℝ) : ℝ :=
  rmvMainConst r k I R γ c₁ Csp Cd r₀ +
    rmvKpoly r k (1 + rmvKZ c s₀ v₀) (1 / c₁ ^ 2) b₀ (1 / c₁ ^ 2 * (r * rmvKZ c s₀ v₀ + 1)) *
      (1 + k + (1 + k)) +
    ((rmvOrder A).factorial : ℝ) * (2 / b₀) ^ rmvOrder A * (2 + r * rmvKZ c s₀ v₀ + r)

theorem inv_rmvP_le (hN : 1 ≤ N) (A : ℝ) : (rmvP N A)⁻¹ ≤ (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  calc (rmvP N A)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hN0 (natCast_le_rmvP hN A)
    _ = (N : ℝ) ^ (-(1 : ℝ)) := (Real.rpow_neg_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)

set_option maxHeartbeats 1600000 in
/-- **The total error.** See the module docstring. -/
theorem rmv_total_le (hN : 1 ≤ N) {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀)
    (r k : ℕ) {I R Cd c₁ Csp b₀ D₁ Dsp : ℝ} (hI : 0 ≤ I) (hR : 0 ≤ R) (hCd : 0 ≤ Cd)
    (hγ : 0 ≤ gammaShiftConst c r₀ s₀ v₀) (hc₁ : 0 < c₁) (hCsp : 0 ≤ Csp) (hb₀ : 0 < b₀)
    (hD₁ : (3 + 2 * max A 1) * (5 : ℕ) ≤ D₁) (hDsp : (3 + 2 * max A 1) * (10 : ℕ) ≤ Dsp) :
    (N : ℝ) ^ (-(1 / 500 : ℝ)) * tbQ0 N r k
          (diagXJ N c r₀ s₀ v₀ ((N : ℝ) ^ (-(1 / 500 : ℝ))) ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
            ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
            c₁ Csp (147 * I * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) Cd)
          (R * (N * (N : ℝ) ^ (-(1 / 100 : ℝ)))) (Real.sqrt (frameZsq N A c s₀ v₀))
          ((N : ℝ) / (c₁ ^ 2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2))
          (b₀ * N / (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ)) ((rmvP N A ^ 5)⁻¹) +
        tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2) * N *
            (r * frameZsq N A c s₀ v₀ + 1)) (Real.sqrt (frameZsq N A c s₀ v₀))
          ((N : ℝ) / (c₁ ^ 2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2))
          (b₀ * N / (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ)) ((rmvP N A ^ 5)⁻¹) *
          (k * (N : ℝ) ^ (-Dsp)) +
      (N : ℝ) ^ (-(1 / 500 : ℝ)) * (tbQ0 N r k 0 0 (Real.sqrt (frameZsq N A c s₀ v₀))
          ((N : ℝ) / (c₁ ^ 2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2))
          (b₀ * N / (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ)) 1 +
        tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2) * N *
            (r * frameZsq N A c s₀ v₀ + 1)) (Real.sqrt (frameZsq N A c s₀ v₀))
          ((N : ℝ) / (c₁ ^ 2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) ^ 2))
          (b₀ * N / (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ)) 1 * k) * (N : ℝ) ^ (-D₁) +
      Real.exp (-(b₀ * N * (N : ℝ) ^ (-(1 / 500 : ℝ)) /
          (2 * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ)))) *
        (Real.sqrt (N * r * frameZsq N A c s₀ v₀) + Real.sqrt ((N : ℝ) * r)) ≤
      rmvConst r k A c r₀ s₀ v₀ I R (gammaShiftConst c r₀ s₀ v₀) c₁ Csp Cd b₀ *
        (N : ℝ) ^ (-(1 / 5000 : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set P := rmvP N A with hPdef
  have hP := one_le_rmvP hN A
  have hP0 : 0 < P := by linarith
  have hNP := natCast_le_rmvP hN A
  set L : ℝ := (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ : ℝ) with hL
  have hL1 : 1 ≤ L := by
    have hx : (1 : ℝ) ≤ (N : ℝ) ^ (1 - 13 / 5000 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    rw [hL]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0; rw [Nat.floor_eq_zero] at h0; linarith)
  set t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ)) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  set KZ := rmvKZ c s₀ v₀ with hKZ
  have hKZ0 : 0 ≤ KZ := rmvKZ_nonneg hK
  set Zsq := frameZsq N A c s₀ v₀ with hZsq
  have hZsq0 : 0 ≤ Zsq := frameZsq_nonneg hK
  have hZsqP : Zsq ≤ KZ * P := frameZsq_le_rmvP hN hK
  set Z := Real.sqrt Zsq with hZ
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hZP : Z ≤ (1 + KZ) * P := by
    have := sqrt_le_one_add hZsq0
    nlinarith
  set cbar := (N : ℝ) / (c₁ ^ 2 * L ^ 2) with hcbar
  have hcbar0 : 0 ≤ cbar := by positivity
  have hcbarP : cbar ≤ 1 / c₁ ^ 2 * P := by
    rw [hcbar, div_le_iff₀ (by positivity)]
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    have : 1 / c₁ ^ 2 * P * (c₁ ^ 2 * L ^ 2) = P * L ^ 2 := by field_simp
    rw [this]; nlinarith
  set bf := b₀ * N / L with hbf
  have hbf0 : 0 ≤ bf := by positivity
  have hbfP : bf ≤ b₀ * P := by
    rw [hbf, div_le_iff₀ (lt_of_lt_of_le one_pos hL1)]
    nlinarith [mul_le_mul_of_nonneg_left hNP hb₀.le,
      mul_le_mul_of_nonneg_left hL1 (by positivity : 0 ≤ b₀ * P)]
  set Xext := cbar * N * (r * Zsq + 1) with hXext
  have hXP : Xext ≤ 1 / c₁ ^ 2 * (r * KZ + 1) * P ^ 3 := by
    have h1 : (r : ℝ) * Zsq + 1 ≤ (r * KZ + 1) * P := by
      have : (r : ℝ) * Zsq ≤ r * (KZ * P) := by gcongr
      nlinarith
    calc Xext ≤ (1 / c₁ ^ 2 * P) * P * ((r * KZ + 1) * P) := by
          rw [hXext]; gcongr
      _ = _ := by ring
  set Zb := 1 + KZ
  set cb := 1 / c₁ ^ 2
  set Xb := 1 / c₁ ^ 2 * (r * KZ + 1)
  set Kp := rmvKpoly r k Zb cb b₀ Xb with hKp
  have hZb0 : 0 ≤ Zb := by positivity
  have hcb0 : 0 ≤ cb := by positivity
  have hXb0 : 0 ≤ Xb := by positivity
  have hKp0 : 0 ≤ Kp := by rw [hKp]; unfold rmvKpoly; positivity
  set ε := (P ^ 5)⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hP)
  have hP4ε : P ^ 4 * ε = P⁻¹ := by rw [hε]; field_simp
  have hiP := inv_rmvP_le hN A
  set χN := (N : ℝ) ^ (-(1 / 5000 : ℝ)) with hχN
  have hχ0 : 0 ≤ χN := by positivity
  -- term 1
  have hQ0 := tbQ0_poly_le (N := N) (r := r) (k := k)
    (XJ := diagXJ N c r₀ s₀ v₀ t ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
            ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
            c₁ Csp (147 * I * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) Cd)
    (B := R * (N * (N : ℝ) ^ (-(1 / 100 : ℝ)))) hP hNP hZ0 hZP hcbar0 hcbarP hbfP hε0.le
    hZb0 hcb0 hb₀.le hXb0
  have hmain := rmv_main_le hN r k hI hR hγ hc₁ hCsp hCd hK.2.2.1
  have hT1 : t * tbQ0 N r k
          (diagXJ N c r₀ s₀ v₀ t ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
            ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
            c₁ Csp (147 * I * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) Cd)
          (R * (N * (N : ℝ) ^ (-(1 / 100 : ℝ)))) Z cbar bf ε ≤
      rmvMainConst r k I R (gammaShiftConst c r₀ s₀ v₀) c₁ Csp Cd r₀ * χN + Kp * χN := by
    calc _ ≤ t * ((2 * (r : ℝ) ^ 2 * k * diagXJ N c r₀ s₀ v₀ t ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
            ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
            c₁ Csp (147 * I * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) Cd +
          ((k : ℝ) * r) ^ 2 * (R * (N * (N : ℝ) ^ (-(1 / 100 : ℝ))) * (Real.sqrt 2 * cbar))) +
          Kp * P ^ 4 * ε) := mul_le_mul_of_nonneg_left hQ0 ht0
      _ = t * (2 * (r : ℝ) ^ 2 * k * diagXJ N c r₀ s₀ v₀ t ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
            ⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
            c₁ Csp (147 * I * (N : ℝ) ^ (1 - 1 / 100 + 1 / 10000 : ℝ)) Cd +
          ((k : ℝ) * r) ^ 2 * (R * (N * (N : ℝ) ^ (-(1 / 100 : ℝ))) * (Real.sqrt 2 * cbar))) +
          t * (Kp * (P ^ 4 * ε)) := by ring
      _ ≤ _ := by
          rw [hP4ε]
          refine add_le_add hmain ?_
          calc t * (Kp * P⁻¹) ≤ 1 * (Kp * χN) := by
                gcongr
          _ = Kp * χN := one_mul _
  -- term 2
  have hQ1 := tbQ1_poly_le (N := N) (r := r) (k := k) hP hNP hXP hZ0 hZP hcbar0 hcbarP hbfP
    hε0 hε1 hZb0 hcb0 hb₀.le hXb0
  have hD10 := rpow_neg_le_rmvP hN A 10 hDsp
  have hT2 : tbQ1 N r k Xext Z cbar bf ε * (k * (N : ℝ) ^ (-Dsp)) ≤ Kp * k * χN := by
    have hq0 : 0 ≤ tbQ1 N r k Xext Z cbar bf ε := by
      unfold tbQ1; positivity
    calc _ ≤ Kp * P ^ 4 / ε * (k * (P ^ 10)⁻¹) := by gcongr
      _ = Kp * k * P⁻¹ := by rw [hε]; field_simp
      _ ≤ Kp * k * χN := mul_le_mul_of_nonneg_left hiP (by positivity)
  -- term 3
  have hQ0c := tbQ0_poly_le (N := N) (r := r) (k := k) (XJ := 0) (B := 0) hP hNP hZ0 hZP hcbar0
    hcbarP hbfP zero_le_one hZb0 hcb0 hb₀.le hXb0
  have hQ1c := tbQ1_poly_le (N := N) (r := r) (k := k) hP hNP hXP hZ0 hZP hcbar0 hcbarP hbfP
    one_pos le_rfl hZb0 hcb0 hb₀.le hXb0
  have hD5 := rpow_neg_le_rmvP hN A 5 hD₁
  have hT3 : t * (tbQ0 N r k 0 0 Z cbar bf 1 + tbQ1 N r k Xext Z cbar bf 1 * k) *
      (N : ℝ) ^ (-D₁) ≤ Kp * (1 + k) * χN := by
    have hc0 : 0 ≤ tbQ0 N r k 0 0 Z cbar bf 1 + tbQ1 N r k Xext Z cbar bf 1 * k := by
      unfold tbQ0 tbQ1; positivity
    simp only [mul_zero, zero_mul, add_zero, mul_one, div_one] at hQ0c hQ1c
    calc _ ≤ 1 * (Kp * P ^ 4 + Kp * P ^ 4 * k) * (P ^ 5)⁻¹ := by
          gcongr
          · simpa using hQ0c
      _ = Kp * (1 + k) * P⁻¹ := by field_simp
      _ ≤ Kp * (1 + k) * χN := mul_le_mul_of_nonneg_left hiP (by positivity)
  -- term 4
  set m := rmvOrder A with hm
  have hmc : 5000 * (3 + 2 * max A 1) ≤ (m : ℝ) := Nat.le_ceil _
  clear_value m
  have hy0 : 0 < b₀ / 2 * (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500) := by positivity
  have hy := rmv_equilibration_rate_ge hN hb₀.le
  have hexp : Real.exp (-(b₀ * N * t / (2 * L))) ≤
      (m.factorial : ℝ) / (b₀ / 2 * (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500)) ^ m := by
    refine (Real.exp_le_exp.mpr (neg_le_neg hy)).trans ?_
    exact exp_neg_le_factorial hy0 m
  have hpow : P ^ 3 ≤ ((N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500)) ^ m := by
    rw [hPdef, rmvP, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    simp only [Nat.cast_ofNat]
    linarith
  have hsq : Real.sqrt (N * r * Zsq) + Real.sqrt ((N : ℝ) * r) ≤ (2 + r * KZ + r) * P ^ 2 := by
    have h1 := sqrt_le_one_add (show (0 : ℝ) ≤ N * r * Zsq by positivity)
    have h2 := sqrt_le_one_add (show (0 : ℝ) ≤ N * r by positivity)
    have hP2 : P ≤ P ^ 2 := by nlinarith
    have h3 : (N : ℝ) * r * Zsq ≤ r * KZ * P ^ 2 := by
      calc (N : ℝ) * r * Zsq ≤ P * r * (KZ * P) := by gcongr
        _ = r * KZ * P ^ 2 := by ring
    have h4 : (N : ℝ) * r ≤ r * P ^ 2 := by
      calc (N : ℝ) * r ≤ P * r := by gcongr
        _ ≤ P ^ 2 * r := by gcongr
        _ = r * P ^ 2 := by ring
    have h5 : (1 : ℝ) ≤ P ^ 2 := one_le_pow₀ hP
    nlinarith
  have hT4 : Real.exp (-(b₀ * N * t / (2 * L))) *
      (Real.sqrt (N * r * Zsq) + Real.sqrt ((N : ℝ) * r)) ≤
      (m.factorial : ℝ) * (2 / b₀) ^ m * (2 + r * KZ + r) * χN := by
    have hN0' : 0 < (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500) := by positivity
    calc _ ≤ (m.factorial : ℝ) / (b₀ / 2 * (N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500)) ^ m *
          ((2 + r * KZ + r) * P ^ 2) := by gcongr
      _ = (m.factorial : ℝ) * (2 / b₀) ^ m * (2 + r * KZ + r) * P ^ 2 /
          ((N : ℝ) ^ ((13 / 5000 : ℝ) - 1 / 500)) ^ m := by
          have key : (b₀ / 2) ^ m * (2 / b₀) ^ m = 1 := by
            rw [← mul_pow, show b₀ / 2 * (2 / b₀) = 1 by field_simp, one_pow]
          rw [mul_pow]; field_simp; exact key.symm
      _ ≤ (m.factorial : ℝ) * (2 / b₀) ^ m * (2 + r * KZ + r) * P ^ 2 / P ^ 3 := by
          gcongr
      _ = (m.factorial : ℝ) * (2 / b₀) ^ m * (2 + r * KZ + r) * P⁻¹ := by field_simp
      _ ≤ _ := by gcongr
  unfold rmvConst
  rw [← hKp, ← hm]
  have e : (N : ℝ) ^ (-(1 / 500 : ℝ)) = t := rfl
  linarith

end BlockBand.Critical.RelativeVectors
