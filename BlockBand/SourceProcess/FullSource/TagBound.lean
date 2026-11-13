module

public import BlockBand.SourceProcess.FullSource.TagFinal

/-!
# The tag moment at one width

* `superexp_absorbs`: `⌊TW⌋ e^{-cW log W} · A^m B ≤ 1` for `m ≤ RW`, `W ≥ W₀` ("Hölder and the
  superexponential exit probability remove every stop");
* `tag_moment_bound`: at one width,
  `E t_{k+1+m}^n ≤ (1+α/W)^m(1+Kd)B_n + (B_{2n}(C_N^{4n})^m P)^{1/2}`, given the birth moments
  `B_n, B_{2n}` and `μ(G_{k+1+m}ᶜ) ≤ P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

/-- **The superexponential exit absorbs the crude growth.** -/
theorem superexp_absorbs {A B c T R : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ m : ℕ, (m : ℝ) ≤ R * W →
      (⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W)) * (A ^ m * B) ≤ 1 := by
  set T₀ := max T 0
  set L := (T₀ + R * Real.log A + B) / c
  refine ⟨⌈Real.exp L⌉₊ + 1, fun W hW m hm => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := by omega
    exact_mod_cast this
  have hW0 : (0 : ℝ) < W := by linarith
  have hexpL : Real.exp L < W := by
    have h1 := Nat.le_ceil (Real.exp L)
    have h2 : ((⌈Real.exp L⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2; linarith
  have hlog : L < Real.log W := (Real.lt_log_iff_exp_lt hW0).2 hexpL
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hT₀ : 0 ≤ T₀ := le_max_right _ _
  -- each factor is an exponential
  have h1 : (⌊T * W⌋₊ : ℝ) ≤ Real.exp (T₀ * W) := by
    have : (⌊T * W⌋₊ : ℝ) ≤ T₀ * W := by
      rcases le_total 0 (T * W) with h | h
      · exact (Nat.floor_le h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le)
      · rw [Nat.floor_eq_zero.2 (by linarith)]; push_cast; positivity
    exact this.trans ((Real.add_one_le_exp _).trans' (by linarith))
  have h2 : A ^ m ≤ Real.exp (R * W * Real.log A) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.2 (by nlinarith)
  have h3 : B ≤ Real.exp B := (Real.add_one_le_exp _).trans' (by linarith)
  have hprod : (⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W)) * (A ^ m * B) ≤
      Real.exp (T₀ * W) * Real.exp (-(c * W * Real.log W)) *
        (Real.exp (R * W * Real.log A) * Real.exp B) := by
    gcongr
  refine hprod.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
  have hcL : c * L = T₀ + R * Real.log A + B := by simp only [L]; field_simp
  have : c * W * L ≤ c * W * Real.log W := mul_le_mul_of_nonneg_left hlog.le (by positivity)
  have hB' : B ≤ B * W := le_mul_of_one_le_right hB hW1
  nlinarith

variable {W : ℕ}

/-- **The tag moment at one width.** -/
theorem tag_moment_bound {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {n k : ℕ} (hW : 1 ≤ W) (hn : 2 ≤ n)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W n Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lcoef Ca n ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lcoef Ca n * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) (hd0 : 0 ≤ d)
    (m : ℕ) {Bn B2n P : ℝ} (hBn : 0 ≤ Bn) (hB2n : 0 ≤ B2n) (hP0 : 0 ≤ P)
    (hbn : ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ n) ∂growthPathLaw W b ≤
      ENNReal.ofReal Bn)
    (hb2n : ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ (2 * n)) ∂growthPathLaw W b ≤
      ENNReal.ofReal B2n)
    (hP : growthPathLaw W b (stopEv b E W k d (k + 1 + m))ᶜ ≤ ENNReal.ofReal P) :
    ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + m) k ω ^ n) ∂growthPathLaw W b ≤
      ENNReal.ofReal ((1 + alphaW K Cm Ca C₂ Cn Cf CN n / W) ^ m * ((1 + K * d) * Bn) +
        (B2n * (CN ^ (2 * (2 * n))) ^ m * P) ^ (1 / 2 : ℝ)) := by
  set μ := growthPathLaw W b
  set α := alphaW K Cm Ca C₂ Cn Cf CN n
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hα : 0 ≤ α := by
    have := lcoef_nonneg hCa n; have := acoef_nonneg (C₂ := C₂) hCa hCn n
    simp only [α, alphaW]; positivity
  have hKd : 0 ≤ 1 + K * d := add_nonneg zero_le_one (mul_nonneg hK hd0)
  have h1α : 0 ≤ 1 + α / W := add_nonneg zero_le_one (div_nonneg hα hW0.le)
  have hrem := stop_removal (W := W) b E (k := k) (n := n) hK d (k + 1 + m)
  have hiter := stopped_tag_iter hb0 hb hE1 hE2 (k := k) hW hn hL hCa hC₂ hCn hCN hCf hCm hK
    hρ0 hρ1 hKL hd1 hρLd hdd₀ m
  have hbirth : ∫⁻ ω, (stopEv b E W k d (k + 1)).indicator (tagWeight b E W k n K (k + 1)) ω ∂μ ≤
      ENNReal.ofReal (1 + K * d) * ENNReal.ofReal Bn := by
    calc ∫⁻ ω, (stopEv b E W k d (k + 1)).indicator (tagWeight b E W k n K (k + 1)) ω ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (1 + K * d) *
            ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ n) ∂μ := by
          refine lintegral_mono fun ω => ?_
          by_cases h : ω ∈ stopEv b E W k d (k + 1)
          · rw [Set.indicator_of_mem h, tagWeight, ← ENNReal.ofReal_mul hKd]
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
              (pow_nonneg (tagMass_nonneg b E _ k ω) n))
            have := h (k + 1) le_rfl le_rfl
            nlinarith
          · rw [Set.indicator_of_notMem h]; exact zero_le
      _ = ENNReal.ofReal (1 + K * d) * ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ n) ∂μ :=
          lintegral_const_mul _ ((measurable_tagMass b E _ k).pow_const n).ennreal_ofReal
      _ ≤ ENNReal.ofReal (1 + K * d) * ENNReal.ofReal Bn := mul_le_mul_of_nonneg_left hbn zero_le
  have hcrude := crude_tag_iter hb0 hb hE1 hE2 (q := 2 * n) (k := k) hW (by omega) hCN hL.N m
  have h2 : ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + m) k ω ^ (2 * n)) ∂μ ≤
      ENNReal.ofReal (B2n * (CN ^ (2 * (2 * n))) ^ m) := by
    refine hcrude.trans ((mul_le_mul_of_nonneg_left hb2n zero_le).trans (le_of_eq ?_))
    rw [ENNReal.ofReal_mul hB2n, ENNReal.ofReal_pow (pow_nonneg hCN _), mul_comm]
  refine hrem.trans ?_
  rw [ENNReal.ofReal_add (mul_nonneg (pow_nonneg h1α m) (mul_nonneg hKd hBn))
    (Real.rpow_nonneg (mul_nonneg (mul_nonneg hB2n (pow_nonneg (pow_nonneg hCN _) m)) hP0) _)]
  refine add_le_add (hiter.trans ?_) ?_
  · rw [ENNReal.ofReal_mul (pow_nonneg h1α m), ENNReal.ofReal_pow h1α,
      ENNReal.ofReal_mul hKd]
    exact mul_le_mul_of_nonneg_left hbirth zero_le
  · have hP' : μ (stopEv b E W k d (k + 1 + m))ᶜ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal P ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hP (by norm_num)
    have h2' := ENNReal.rpow_le_rpow h2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    refine (mul_le_mul h2' hP' zero_le zero_le).trans (le_of_eq ?_)
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.ofReal_mul (mul_nonneg hB2n (pow_nonneg (pow_nonneg hCN _) m)),
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (mul_nonneg hB2n (pow_nonneg (pow_nonneg hCN _) m))
        hP0) (by norm_num)]

end BlockBand.SourceProcess.FullSource
