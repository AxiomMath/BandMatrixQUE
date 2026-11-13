module

public import BlockBand.Diffusion.Kernel.McKeanPDEBackward
public import BlockBand.Diffusion.Kernel.McKeanPDESecond

/-!
# McKean's integrand near the endpoint `w = 1`; global bounds on the kernel derivatives

The closed forms `∂_w G = 2E N₁/R³`, `∂_w² G = 2E N₂/R⁵` (`McKeanPDEPoint`) have removable
singularities at `w = 1` (`R = sinh S → 0`). Taylor bounds from `Real.exp_bound`
(`mk_cosh_taylor`, `mk_sinh_taylor`) give, for `0 ≤ S ≤ 1/2`,
`|sinh S - S cosh S| ≤ S³` and `|S(2cosh²S + 1) - 3 cosh S sinh S| ≤ 2 S⁵`, hence
(`mk_gw_near`), for `T > 0` and `1 < w ≤ cosh(1/2)`, each of `G`, `∂_w G`, `∂_w² G`, `∂_T G`,
`∂_T² G`, `∂_T∂_w G` is at most `mkBn T = 10(1 + 1/T)⁴` (the proof passes through
`|∂_w G| ≤ 2 + 1/T`).
With `mk_gw_le` this gives the global majorant `mk_gw_global`
(all six functions `≤ mkBdG T₁ T₂ · w⁻⁶` for every `w > 1`, `T ∈ [T₁, T₂] ⊂ (0,∞)`), then
`mk_f_global` (`|F_j(T, c)| ≤ mkBdG T₁ T₂ · (π/2) · c⁻⁵` for `c > 1`) and `mk_k_global`
(`|∂_c K|, |∂_c² K| ≤ |A_T| M`, `|∂_T K|, |∂_c∂_T K| ≤ (|A'_T| + |A_T|) M`,
`|∂_T² K| ≤ (|A''_T| + 2|A'_T| + |A_T|) M`, `M = mkBdG T₁ T₂ · (π/2) · c⁻⁵`).
In particular `∂_c K`, `∂_c² K`, `∂_T K` are bounded on `(1, ∞)`, locally uniformly in `T > 0`
(McKean's kernel is `C²` up to `c = 1` from the right); this handles the diagonal of
`pX`. We also record measurability of `mkK1 T`, `mkK2 T`, `mkKT T`, `mkKTT T`, `mkKTc T`
(`mk_k_measurable`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-!
### Taylor bounds
-/

theorem mk_cosh_taylor {u : ℝ} (hu : |u| ≤ 1) :
    |Real.cosh u - (1 + u ^ 2 / 2)| ≤ 5 / 96 * |u| ^ 4 := by
  have h1 := Real.exp_bound hu (n := 4) (by norm_num)
  have h2 := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  rw [show (-u) ^ 3 = -u ^ 3 by ring] at h2
  rw [Real.cosh_eq]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem mk_sinh_taylor {u : ℝ} (hu : |u| ≤ 1) :
    |Real.sinh u - (u + u ^ 3 / 6)| ≤ 1 / 100 * |u| ^ 5 := by
  have h1 := Real.exp_bound hu (n := 5) (by norm_num)
  have h2 := Real.exp_bound (x := -u) (by rwa [abs_neg]) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  rw [show (-u) ^ 3 = -u ^ 3 by ring, show (-u) ^ 4 = u ^ 4 by ring] at h2
  rw [Real.sinh_eq]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem mk_A_le {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 1 / 2) :
    |Real.sinh S - S * Real.cosh S| ≤ S ^ 3 := by
  have hS : |S| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hc := mk_cosh_taylor hS
  have hs := mk_sinh_taylor hS
  rw [abs_of_nonneg h0] at hc hs
  have e : Real.sinh S - S * Real.cosh S = (Real.sinh S - (S + S ^ 3 / 6)) -
      S * (Real.cosh S - (1 + S ^ 2 / 2)) - S ^ 3 / 3 := by ring
  rw [e]
  have hSc : |S * (Real.cosh S - (1 + S ^ 2 / 2))| ≤ S * (5 / 96 * S ^ 4) := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left hc h0
  have hS2 : S ^ 2 ≤ 1 / 4 := by nlinarith
  have hS3 : 0 ≤ S ^ 3 := by positivity
  calc |(Real.sinh S - (S + S ^ 3 / 6)) - S * (Real.cosh S - (1 + S ^ 2 / 2)) - S ^ 3 / 3|
      ≤ |(Real.sinh S - (S + S ^ 3 / 6)) - S * (Real.cosh S - (1 + S ^ 2 / 2))| + |S ^ 3 / 3| :=
        abs_sub _ _
    _ ≤ |Real.sinh S - (S + S ^ 3 / 6)| + |S * (Real.cosh S - (1 + S ^ 2 / 2))| + |S ^ 3 / 3| := by
        gcongr; exact abs_sub _ _
    _ ≤ 1 / 100 * S ^ 5 + S * (5 / 96 * S ^ 4) + S ^ 3 / 3 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ S ^ 3 / 3)]; linarith
    _ = S ^ 3 * (S ^ 2 * (1 / 100 + 5 / 96) + 1 / 3) := by ring
    _ ≤ S ^ 3 * (1 / 4 * (1 / 100 + 5 / 96) + 1 / 3) := by gcongr
    _ ≤ S ^ 3 * 1 := by gcongr; norm_num
    _ = S ^ 3 := mul_one _

theorem mk_h0_le {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 1 / 2) :
    |S * (2 * Real.cosh S ^ 2 + 1) - 3 * Real.cosh S * Real.sinh S| ≤ 2 * S ^ 5 := by
  set u := 2 * S with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : |u| ≤ 1 := by rw [abs_of_nonneg hu0]; linarith
  have hc := mk_cosh_taylor hu1
  have hs := mk_sinh_taylor hu1
  rw [abs_of_nonneg hu0] at hc hs
  have hcu : Real.cosh u = 2 * Real.cosh S ^ 2 - 1 := by
    rw [hu, Real.cosh_two_mul, Real.cosh_sq']; ring
  have hsu : Real.sinh u = 2 * Real.sinh S * Real.cosh S := by rw [hu, Real.sinh_two_mul]
  have e : S * (2 * Real.cosh S ^ 2 + 1) - 3 * Real.cosh S * Real.sinh S =
      (u * (Real.cosh u - (1 + u ^ 2 / 2)) - 3 * (Real.sinh u - (u + u ^ 3 / 6))) / 2 := by
    rw [hcu, hsu, hu]; ring
  rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2 : |u * (Real.cosh u - (1 + u ^ 2 / 2))| ≤ u * (5 / 96 * u ^ 4) := by
    rw [abs_mul, abs_of_nonneg hu0]; exact mul_le_mul_of_nonneg_left hc hu0
  have h3 : |3 * (Real.sinh u - (u + u ^ 3 / 6))| ≤ 3 * (1 / 100 * u ^ 5) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith
  have h4 := abs_sub (u * (Real.cosh u - (1 + u ^ 2 / 2))) (3 * (Real.sinh u - (u + u ^ 3 / 6)))
  have hu5 : u ^ 5 = 32 * S ^ 5 := by rw [hu]; ring
  have : 0 ≤ S ^ 5 := by positivity
  have hm : u * (5 / 96 * u ^ 4) = 5 / 96 * u ^ 5 := by ring
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-!
### Bounds near `w = 1`
-/

/-- The near-endpoint constant. -/
def mkBn (T₁ : ℝ) : ℝ := 10 * (1 + T₁⁻¹) ^ 4

/-- **Bounds near the endpoint.** For `T > 0` and `1 < w ≤ cosh(1/2)`, each of `G`, `∂_w G`,
`∂_w² G`, `∂_T G`, `∂_T² G`, `∂_T∂_w G` is at most `10 (1 + 1/T)⁴`. -/
theorem mk_gw_near {T w : ℝ} (hT : 0 < T) (hw : 1 < w) (hw' : w ≤ Real.cosh (1 / 2)) :
    |mkMcKeanG T w| ≤ mkBn T ∧ |mkGw1 T w| ≤ mkBn T ∧ |mkGw2 T w| ≤ mkBn T ∧
      |mkGT T w| ≤ mkBn T ∧ |mkGTT T w| ≤ mkBn T ∧ |mkGTw T w| ≤ mkBn T := by
  have hg0 := mk_mcKeanG_pos T w
  have hgE : mkMcKeanG T w ≤ 2 := by
    unfold mkMcKeanG
    have := mk_sdivSinh_le_one (Real.arcosh w)
    have h0 := (mk_sdivSinh_pos (Real.arcosh w)).le
    have : Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (Real.arcosh w) ^ 2 / (4 * T) := by positivity
      rw [neg_div]; linarith
    have := Real.exp_pos (-(Real.arcosh w) ^ 2 / (4 * T))
    nlinarith
  have hgS : mkMcKeanG T w = 2 * (Real.arcosh w / Real.sqrt (w ^ 2 - 1)) *
      Real.exp (-(Real.arcosh w) ^ 2 / (4 * T)) := mk_mcKeanG_eq hw
  unfold mkGTT mkGTw
  unfold mkGT
  unfold mkGw1 mkGw2
  set g := mkMcKeanG T w with hgdef
  set S := Real.arcosh w with hSdef
  set R := Real.sqrt (w ^ 2 - 1) with hRdef
  have hS0 : 0 < S := Real.arcosh_pos hw
  have hS1 : S ≤ 1 / 2 := by
    have h := (Real.arcosh_le_arcosh (by linarith) (Real.cosh_pos _)).2 hw'
    rwa [Real.arcosh_cosh (by norm_num)] at h
  have hRs : R = Real.sinh S := (Real.sinh_arcosh hw.le).symm
  have hws : w = Real.cosh S := (Real.cosh_arcosh hw.le).symm
  have hSR : S ≤ R := by rw [hRs]; exact Real.self_le_sinh_iff.2 hS0.le
  have hR0 : 0 < R := lt_of_lt_of_le hS0 hSR
  set E := Real.exp (-S ^ 2 / (4 * T)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hEdef, Real.exp_le_one_iff]
    have : 0 ≤ S ^ 2 / (4 * T) := by positivity
    rw [neg_div]; linarith
  set τ := 1 + T⁻¹ with hτ
  have hTi : 0 < T⁻¹ := inv_pos.2 hT
  have hτ1 : 1 ≤ τ := by linarith
  have hTτ : T⁻¹ ≤ τ := by linarith
  have hBn : mkBn T = 10 * τ ^ 4 := rfl
  rw [hBn]
  have hτ2 : τ ≤ τ ^ 2 := le_self_pow₀ hτ1 (by norm_num)
  have hτ3 : τ ^ 2 ≤ τ ^ 3 := pow_le_pow_right₀ hτ1 (by norm_num)
  have hτ4 : τ ^ 3 ≤ τ ^ 4 := pow_le_pow_right₀ hτ1 (by norm_num)
  have h1τ4 : (1 : ℝ) ≤ τ ^ 4 := one_le_pow₀ hτ1
  have hS2 : S ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ hS0.le hS1 2
    norm_num at this ⊢; linarith
  set q := S / R with hq
  have hq0 : 0 < q := div_pos hS0 hR0
  have hq1 : q ≤ 1 := (div_le_one hR0).2 hSR
  have hSq : S = q * R := by rw [hq]; field_simp
  -- `A = R - S w = sinh S - S cosh S`
  have hA : |R - S * w| ≤ S ^ 3 := by rw [hRs, hws]; exact mk_A_le hS0.le hS1
  have hG1 : |2 * E * mkN1 T S R w / R ^ 3| ≤ 2 * τ := by
    have hN1 : |mkN1 T S R w| ≤ S ^ 3 + R * S ^ 2 * T⁻¹ / 2 := by
      have e : mkN1 T S R w = (R - S * w) - R * S ^ 2 * T⁻¹ / 2 := by
        unfold mkN1; field_simp
      rw [e]
      have : 0 ≤ R * S ^ 2 * T⁻¹ / 2 := by positivity
      calc |(R - S * w) - R * S ^ 2 * T⁻¹ / 2| ≤ |R - S * w| + |R * S ^ 2 * T⁻¹ / 2| :=
            abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg this]; linarith
    have e2 : (S ^ 3 + R * S ^ 2 * T⁻¹ / 2) / R ^ 3 = q ^ 3 + q ^ 2 * T⁻¹ / 2 := by
      rw [hSq]; field_simp
    have hq3 : q ^ 3 ≤ 1 := pow_le_one₀ hq0.le hq1
    have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hE0, abs_of_pos (pow_pos hR0 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * E * |mkN1 T S R w| / R ^ 3 ≤ 2 * 1 * (S ^ 3 + R * S ^ 2 * T⁻¹ / 2) / R ^ 3 := by
          gcongr
      _ = 2 * (q ^ 3 + q ^ 2 * T⁻¹ / 2) := by rw [mul_one, mul_div_assoc, e2]
      _ ≤ 2 * (1 + 1 * T⁻¹ / 2) := by gcongr
      _ ≤ 2 * τ := by linarith
  have hG1' : |2 * E * mkN1 T S R w / R ^ 3| ≤ 10 * τ ^ 4 := by linarith
  have hSS : S ^ 2 / (4 * T ^ 2) ≤ τ ^ 2 / 16 := by
    rw [div_eq_mul_inv, mul_inv, ← inv_pow]
    have h2 : T⁻¹ ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hTi.le hTτ 2
    calc S ^ 2 * ((4 : ℝ)⁻¹ * T⁻¹ ^ 2) ≤ 1 / 4 * ((4 : ℝ)⁻¹ * τ ^ 2) := by gcongr
      _ = τ ^ 2 / 16 := by ring
  have hS3 : S ^ 2 / (2 * T ^ 3) ≤ τ ^ 3 / 8 := by
    rw [div_eq_mul_inv, mul_inv, ← inv_pow]
    have h2 : T⁻¹ ^ 3 ≤ τ ^ 3 := pow_le_pow_left₀ hTi.le hTτ 3
    calc S ^ 2 * ((2 : ℝ)⁻¹ * T⁻¹ ^ 3) ≤ 1 / 4 * ((2 : ℝ)⁻¹ * τ ^ 3) := by gcongr
      _ = τ ^ 3 / 8 := by ring
  have hS1R : S / (2 * T ^ 2 * R) ≤ τ ^ 2 / 2 := by
    have e : S / (2 * T ^ 2 * R) = q * T⁻¹ ^ 2 / 2 := by rw [hSq]; field_simp
    rw [e]
    have h2 : T⁻¹ ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hTi.le hTτ 2
    calc q * T⁻¹ ^ 2 / 2 ≤ 1 * τ ^ 2 / 2 := by gcongr
      _ = τ ^ 2 / 2 := by ring
  have hGT : |g * (S ^ 2 / (4 * T ^ 2))| ≤ τ ^ 2 / 8 := by
    rw [abs_mul, abs_of_pos hg0, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (4 * T ^ 2))]
    calc g * (S ^ 2 / (4 * T ^ 2)) ≤ 2 * (τ ^ 2 / 16) := by gcongr
      _ = τ ^ 2 / 8 := by ring
  have hτ0 : 0 ≤ τ ^ 4 := by positivity
  refine ⟨?_, hG1', ?_, ?_, ?_, ?_⟩
  · rw [abs_of_pos hg0]
    linarith
  · -- `∂_w² G`
    have e : mkN2 T S R w = (-(S * R ^ 2) - 3 * w * (R - S * w)) -
        3 * T⁻¹ / 2 * (S * R * (R - S * w)) + R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4 := by
      unfold mkN2 mkN1 mkN1d; field_simp; ring
    have hh0 : |-(S * R ^ 2) - 3 * w * (R - S * w)| ≤ 2 * S ^ 5 := by
      have e2 : -(S * R ^ 2) - 3 * w * (R - S * w) =
          S * (2 * Real.cosh S ^ 2 + 1) - 3 * Real.cosh S * Real.sinh S := by
        rw [← hRs, ← hws]
        have hR2 : R ^ 2 = w ^ 2 - 1 := by rw [hRdef]; exact Real.sq_sqrt (by nlinarith)
        rw [hR2]; ring
      rw [e2]; exact mk_h0_le hS0.le hS1
    have hm : |3 * T⁻¹ / 2 * (S * R * (R - S * w))| ≤ 3 * T⁻¹ / 2 * (S * R * S ^ 3) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * T⁻¹ / 2),
        abs_of_nonneg (by positivity : 0 ≤ S * R)]
      gcongr
    have hl : |R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4| = R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4 :=
      abs_of_nonneg (by positivity)
    have hN2 : |mkN2 T S R w| ≤ 2 * S ^ 5 + 3 * T⁻¹ / 2 * (S * R * S ^ 3) +
        R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4 := by
      rw [e]
      calc _ ≤ |(-(S * R ^ 2) - 3 * w * (R - S * w)) - 3 * T⁻¹ / 2 * (S * R * (R - S * w))| +
            |R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4| := abs_add_le _ _
        _ ≤ |-(S * R ^ 2) - 3 * w * (R - S * w)| + |3 * T⁻¹ / 2 * (S * R * (R - S * w))| +
            |R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4| := by gcongr; exact abs_sub _ _
        _ ≤ _ := by rw [hl]; linarith
    have e2 : (2 * S ^ 5 + 3 * T⁻¹ / 2 * (S * R * S ^ 3) + R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4) / R ^ 5 =
        2 * q ^ 5 + 3 * T⁻¹ / 2 * q ^ 4 + T⁻¹ ^ 2 / 4 * q ^ 3 := by
      rw [hSq]; field_simp
    have hq5 : q ^ 5 ≤ 1 := pow_le_one₀ hq0.le hq1
    have hq4 : q ^ 4 ≤ 1 := pow_le_one₀ hq0.le hq1
    have hq3 : q ^ 3 ≤ 1 := pow_le_one₀ hq0.le hq1
    have h2 : T⁻¹ ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hTi.le hTτ 2
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hE0, abs_of_pos (pow_pos hR0 5),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * E * |mkN2 T S R w| / R ^ 5 ≤ 2 * 1 * (2 * S ^ 5 + 3 * T⁻¹ / 2 * (S * R * S ^ 3) +
          R ^ 2 * S ^ 3 * T⁻¹ ^ 2 / 4) / R ^ 5 := by gcongr
      _ = 2 * (2 * q ^ 5 + 3 * T⁻¹ / 2 * q ^ 4 + T⁻¹ ^ 2 / 4 * q ^ 3) := by
          rw [mul_one, mul_div_assoc, e2]
      _ ≤ 2 * (2 * 1 + 3 * τ / 2 * 1 + τ ^ 2 / 4 * 1) := by gcongr
      _ ≤ 10 * τ ^ 4 := by linarith
  · linarith [hGT]
  · have h1 : |g * (S ^ 2 / (4 * T ^ 2)) * (S ^ 2 / (4 * T ^ 2))| ≤ τ ^ 2 / 8 * (τ ^ 2 / 16) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (4 * T ^ 2))]
      gcongr
    have h2 : |g * (S ^ 2 / (2 * T ^ 3))| ≤ 2 * (τ ^ 3 / 8) := by
      rw [abs_mul, abs_of_pos hg0, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (2 * T ^ 3))]
      gcongr
    calc |g * (S ^ 2 / (4 * T ^ 2)) * (S ^ 2 / (4 * T ^ 2)) - g * (S ^ 2 / (2 * T ^ 3))|
        ≤ |g * (S ^ 2 / (4 * T ^ 2)) * (S ^ 2 / (4 * T ^ 2))| + |g * (S ^ 2 / (2 * T ^ 3))| :=
          abs_sub _ _
      _ ≤ 10 * τ ^ 4 := by
          have : τ ^ 2 / 8 * (τ ^ 2 / 16) = τ ^ 4 / 128 := by ring
          linarith
  · have h1 : |2 * E * mkN1 T S R w / R ^ 3 * (S ^ 2 / (4 * T ^ 2))| ≤ 2 * τ * (τ ^ 2 / 16) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ S ^ 2 / (4 * T ^ 2))]
      gcongr
    have h2 : |g * (S / (2 * T ^ 2 * R))| ≤ 2 * (τ ^ 2 / 2) := by
      rw [abs_mul, abs_of_pos hg0, abs_of_nonneg (by positivity : 0 ≤ S / (2 * T ^ 2 * R))]
      gcongr
    calc |2 * E * mkN1 T S R w / R ^ 3 * (S ^ 2 / (4 * T ^ 2)) + g * (S / (2 * T ^ 2 * R))|
        ≤ |2 * E * mkN1 T S R w / R ^ 3 * (S ^ 2 / (4 * T ^ 2))| +
            |g * (S / (2 * T ^ 2 * R))| := abs_add_le _ _
      _ ≤ 10 * τ ^ 4 := by
          have : 2 * τ * (τ ^ 2 / 16) = τ ^ 3 / 8 := by ring
          linarith

/-!
### Global bounds
-/

/-- The global constant: near-endpoint bound plus `mkBd` at `c₀ = cosh(1/2)`. -/
def mkBdG (T₁ T₂ : ℝ) : ℝ :=
  mkBn T₁ * Real.cosh (1 / 2) ^ 6 + mkBd T₁ T₂ (Real.cosh (1 / 2))

theorem mk_one_lt_cosh_half : 1 < Real.cosh (1 / 2) := Real.one_lt_cosh.2 (by norm_num)

theorem mk_bdG_nonneg {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) : 0 ≤ mkBdG T₁ T₂ := by
  unfold mkBdG mkBn
  have := mk_bd_nonneg (T₂ := T₂) hT₁ mk_one_lt_cosh_half
  have := inv_pos.2 hT₁
  positivity

/-- **Global majorant.** For `0 < T₁ ≤ T ≤ T₂` and every `w > 1`, each of the six functions
`G, ∂_w G, ∂_w² G, ∂_T G, ∂_T² G, ∂_T∂_w G` is at most `mkBdG T₁ T₂ · w⁻⁶`. -/
theorem mk_gw_global {T₁ T₂ T w : ℝ} (hT₁ : 0 < T₁) (h₁ : T₁ ≤ T) (h₂ : T ≤ T₂) (hw : 1 < w) :
    |mkMcKeanG T w| ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ ∧ |mkGw1 T w| ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ ∧
      |mkGw2 T w| ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ ∧ |mkGT T w| ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ ∧
      |mkGTT T w| ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ ∧ |mkGTw T w| ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ := by
  have hT : 0 < T := lt_of_lt_of_le hT₁ h₁
  have hw0 : 0 < w := by linarith
  set c := Real.cosh (1 / 2)
  have hc := mk_one_lt_cosh_half
  have hBd := mk_bd_nonneg (T₂ := T₂) hT₁ hc
  have hBn0 : 0 ≤ mkBn T₁ := by unfold mkBn; have := inv_pos.2 hT₁; positivity
  rcases le_or_gt w c with hwc | hwc
  · have hn := mk_gw_near hT hw hwc
    have hmono : mkBn T ≤ mkBn T₁ := by
      unfold mkBn
      have : T⁻¹ ≤ T₁⁻¹ := inv_anti₀ hT₁ h₁
      have : 0 ≤ T⁻¹ := (inv_pos.2 hT).le
      gcongr
    have hstep : mkBn T₁ ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ := by
      have h6 : w ^ 6 ≤ c ^ 6 := pow_le_pow_left₀ hw0.le hwc 6
      have h1 : 1 ≤ c ^ 6 * (w ^ 6)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
      have h2 : 0 ≤ mkBd T₁ T₂ c * (w ^ 6)⁻¹ := by positivity
      calc mkBn T₁ = mkBn T₁ * 1 := (mul_one _).symm
        _ ≤ mkBn T₁ * (c ^ 6 * (w ^ 6)⁻¹) := by gcongr
        _ ≤ mkBn T₁ * (c ^ 6 * (w ^ 6)⁻¹) + mkBd T₁ T₂ c * (w ^ 6)⁻¹ := by linarith
        _ = mkBdG T₁ T₂ * (w ^ 6)⁻¹ := by unfold mkBdG; ring
    have k := fun y (hy : y ≤ mkBn T) => (hy.trans hmono).trans hstep
    exact ⟨k _ hn.1, k _ hn.2.1, k _ hn.2.2.1, k _ hn.2.2.2.1, k _ hn.2.2.2.2.1,
      k _ hn.2.2.2.2.2⟩
  · have hf := mk_gw_le hT₁ h₁ h₂ hc hwc.le
    have hstep : mkBd T₁ T₂ c * (w ^ 6)⁻¹ ≤ mkBdG T₁ T₂ * (w ^ 6)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold mkBdG
      have : 0 ≤ mkBn T₁ * c ^ 6 := by positivity
      linarith
    have k := fun y (hy : y ≤ mkBd T₁ T₂ c * (w ^ 6)⁻¹) => hy.trans hstep
    exact ⟨k _ hf.1, k _ hf.2.1, k _ hf.2.2.1, k _ hf.2.2.2.1, k _ hf.2.2.2.2.1,
      k _ hf.2.2.2.2.2⟩

theorem mk_inv_six_le_five {c v : ℝ} (hc : 1 ≤ c) :
    ((c + v ^ 2) ^ 6)⁻¹ ≤ (c ^ 5)⁻¹ * (1 + v ^ 2)⁻¹ := by
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  have hc0 : 0 ≤ c := by linarith
  have h1 : c ^ 5 ≤ (c + v ^ 2) ^ 5 := pow_le_pow_left₀ hc0 (by nlinarith [sq_nonneg v]) 5
  have h2 : 1 + v ^ 2 ≤ c + v ^ 2 := by linarith
  calc c ^ 5 * (1 + v ^ 2) ≤ (c + v ^ 2) ^ 5 * (c + v ^ 2) := by gcongr
    _ = (c + v ^ 2) ^ 6 := by ring

/-- **Global bounds on the `v`-integrals.** For `0 < T₁ ≤ T ≤ T₂` and `c > 1`, each of
`F₀, F₁, F₂, F_T, F_TT, F_Tw` is at most `mkBdG T₁ T₂ · (π/2) · c⁻⁵`. -/
theorem mk_f_global {T₁ T₂ T c : ℝ} (hT₁ : 0 < T₁) (h₁ : T₁ ≤ T) (h₂ : T ≤ T₂) (hc : 1 < c) :
    |mkF0 T c| ≤ mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ ∧
      |mkF1 T c| ≤ mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ ∧
      |mkF2 T c| ≤ mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ ∧
      |mkFT T c| ≤ mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ ∧
      |mkFTT T c| ≤ mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ ∧
      |mkFTw T c| ≤ mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ := by
  set B := mkBdG T₁ T₂ * (c ^ 5)⁻¹
  have hB0 : 0 ≤ mkBdG T₁ T₂ := mk_bdG_nonneg hT₁
  have hb : ∀ v : ℝ, ∀ y : ℝ, |y| ≤ mkBdG T₁ T₂ * ((c + v ^ 2) ^ 6)⁻¹ →
      |y| ≤ B * (1 + v ^ 2)⁻¹ := fun v y hy => by
    refine hy.trans ?_
    calc mkBdG T₁ T₂ * ((c + v ^ 2) ^ 6)⁻¹ ≤ mkBdG T₁ T₂ * ((c ^ 5)⁻¹ * (1 + v ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (mk_inv_six_le_five hc.le) hB0
      _ = B * (1 + v ^ 2)⁻¹ := by ring
  have hg := fun v => mk_gw_global (w := c + v ^ 2) hT₁ h₁ h₂ (by nlinarith [sq_nonneg v])
  have hI : ∫ v in Ioi (0 : ℝ), B * (1 + v ^ 2)⁻¹ = mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ := by
    rw [integral_const_mul, mk_integral_inv_one_add_sq_Ioi]; ring
  have key : ∀ f : ℝ → ℝ, (∀ v, |f v| ≤ B * (1 + v ^ 2)⁻¹) →
      |∫ v in Ioi (0 : ℝ), f v| ≤ mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹ := fun f hf => by
    rw [← hI]
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun v => abs_nonneg _)
      (integrable_inv_one_add_sq.const_mul _).integrableOn (ae_of_all _ fun v => hf v)
  exact ⟨key _ fun v => hb v _ (hg v).1, key _ fun v => hb v _ (hg v).2.1,
    key _ fun v => hb v _ (hg v).2.2.1, key _ fun v => hb v _ (hg v).2.2.2.1,
    key _ fun v => hb v _ (hg v).2.2.2.2.1, key _ fun v => hb v _ (hg v).2.2.2.2.2⟩

/-!
### Measurability in `c`
-/

theorem mk_integral_shift_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun c : ℝ => ∫ v in Ioi (0 : ℝ), f (c + v ^ 2) := by
  have hm : StronglyMeasurable (Function.uncurry fun (c : ℝ) (v : ℝ) => f (c + v ^ 2)) :=
    (hf.comp (by fun_prop : Measurable fun q : ℝ × ℝ => q.1 + q.2 ^ 2)).stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume.restrict (Ioi 0))).measurable

theorem mk_k_measurable (T : ℝ) :
    Measurable (mkK1 T) ∧ Measurable (mkK2 T) ∧ Measurable (mkKT T) ∧ Measurable (mkKTT T) ∧
      Measurable (mkKTc T) := by
  have h0 : Measurable (mkF0 T) := mk_integral_shift_measurable (mk_mcKeanG_measurable T)
  have h1 : Measurable (mkF1 T) := mk_integral_shift_measurable (mk_gw1_measurable T)
  have h2 : Measurable (mkF2 T) := mk_integral_shift_measurable (mk_gw2_measurable T)
  have hT : Measurable (mkFT T) := mk_integral_shift_measurable (mk_gT_measurable T)
  have hTT : Measurable (mkFTT T) := mk_integral_shift_measurable (mk_gTT_measurable T)
  have hTw : Measurable (mkFTw T) := mk_integral_shift_measurable (mk_gTw_measurable T)
  have k1 : Measurable (mkK1 T) := h1.const_mul _
  have k2 : Measurable (mkK2 T) := h2.const_mul _
  refine ⟨k1, k2, ?_, ?_, ?_⟩
  · unfold mkKT; fun_prop
  · unfold mkKTT; fun_prop
  · unfold mkKTc; fun_prop

/-!
### Global bounds on the kernel derivatives
-/

/-- For `0 < T₁ ≤ T ≤ T₂` and `c > 1`: with `M = mkBdG T₁ T₂ · π/2 · c⁻⁵`,
`|∂_cK| ≤ |A| M`, `|∂_c²K| ≤ |A| M`, `|∂_TK| ≤ (|A'| + |A|) M`,
`|∂_T²K| ≤ (|A''| + 2|A'| + |A|) M`, `|∂_c∂_TK| ≤ (|A'| + |A|) M`. -/
theorem mk_k_global {T₁ T₂ T c : ℝ} (hT₁ : 0 < T₁) (h₁ : T₁ ≤ T) (h₂ : T ≤ T₂) (hc : 1 < c) :
    |mkK1 T c| ≤ |mkA T| * (mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹) ∧
      |mkK2 T c| ≤ |mkA T| * (mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹) ∧
      |mkKT T c| ≤ (|mkA1 T| + |mkA T|) * (mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹) ∧
      |mkKTT T c| ≤ (|mkA2 T| + 2 * |mkA1 T| + |mkA T|) * (mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹) ∧
      |mkKTc T c| ≤ (|mkA1 T| + |mkA T|) * (mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹) := by
  have hT : 0 < T := lt_of_lt_of_le hT₁ h₁
  obtain ⟨b0, b1, b2, bT, bTT, bTw⟩ := mk_f_global hT₁ h₁ h₂ hc
  set M := mkBdG T₁ T₂ * (π / 2) * (c ^ 5)⁻¹
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold mkK1; rw [abs_mul]; gcongr
  · unfold mkK2; rw [abs_mul]; gcongr
  · rw [mk_kT_eq hT hc]
    calc |mkA1 T * mkF0 T c + mkA T * mkFT T c| ≤ |mkA1 T| * |mkF0 T c| + |mkA T| * |mkFT T c| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |mkA1 T| * M + |mkA T| * M := by gcongr
      _ = _ := by ring
  · unfold mkKTT
    calc |mkA2 T * mkF0 T c + 2 * mkA1 T * mkFT T c + mkA T * mkFTT T c|
        ≤ |mkA2 T| * |mkF0 T c| + 2 * |mkA1 T| * |mkFT T c| + |mkA T| * |mkFTT T c| := by
          have e : |2 * mkA1 T * mkFT T c| = 2 * |mkA1 T| * |mkFT T c| := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          rw [← abs_mul, ← e, ← abs_mul]
          exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ |mkA2 T| * M + 2 * |mkA1 T| * M + |mkA T| * M := by gcongr
      _ = _ := by ring
  · unfold mkKTc
    calc |mkA1 T * mkF1 T c + mkA T * mkFTw T c|
        ≤ |mkA1 T| * |mkF1 T c| + |mkA T| * |mkFTw T c| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |mkA1 T| * M + |mkA T| * M := by gcongr
      _ = _ := by ring

end BlockBand.Diffusion
