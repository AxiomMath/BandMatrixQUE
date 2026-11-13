module

public import BlockBand.SourceProcess.PhysApprox.B3FracMomPath

/-!
# Uniform `q`-th moments and `FarFracTraceMomentsAt`

* `pathPow_succ_pow_le`: Jensen-lite, `E P^{q+1} ≥ (E P^q)^{(q+1)/q} / 4`;
* **`fracPow_bound`**: `FracPowStep α q` + MT, GA, Lp give `E (Tr T_{⌊Wt⌋}^α)^q ≤ C` for
  `W ≥ W₀`, for every `t > 0` (run the comparison `ode_iter` over the last `⌊Wt/2⌋` layers from
  the trivial start `E P^q ≤ W^q`);
* **`farFracTraceMomentsAt_four_of_step`**: `FracPowStep (1/8) 4` + MT, GA, Lp give
  `Jet.FarFracTraceMomentsAt 4` (`α = 1/8`);
* **`farFracTraceMoments_of_step`**: `∀ q ≥ 1, FracPowStep (1/(2q)) q` + MT, GA, Lp give
  `Jet.FarFracTraceMoments` (`q = ⌈p⌉`, `α = 1/(2q)`, `F^p ≤ 1 + F^q`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.FracMom

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.FractionalBulk
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- **Jensen-lite**: with `x = (E P^q)^{1/q}`, `x^{q+1} ≤ 4 E P^{q+1}`. -/
theorem pathPow_succ_pow_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {b : ℝ} (hb : b < 1 / 2)
    {E : ℝ} (h1 : -2 < E) (h2 : E < 2) (r : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    (pathPow α b E W r q ^ ((q : ℝ)⁻¹)) ^ (q + 1) ≤ 4 * pathPow α b E W r (q + 1) := by
  have := Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  set x := pathPow α b E W r q ^ ((q : ℝ)⁻¹)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (pathPow_nonneg _ _ _ _ _) _
  have hxq : x ^ q = pathPow α b E W r q :=
    Real.rpow_inv_natCast_pow (pathPow_nonneg _ _ _ _ _) (by omega)
  obtain ⟨hPq, -⟩ := pathFrac_pow_facts (W := W) hα0 hα1 hb h1 h2 r q
  obtain ⟨hPq1, -⟩ := pathFrac_pow_facts (W := W) hα0 hα1 hb h1 h2 r (q + 1)
  set Pf := fun ω => fracTrace α (pathTransmission b E (fun _ => 0) W r ω)
  have hpt : ∀ ω, Pf ω ^ q * x ≤ 2 * Pf ω ^ (q + 1) + (2 ^ q)⁻¹ * x ^ (q + 1) := fun ω => by
    have h := young_pow (fracTrace_nonneg' α (pathTransmission b E (fun _ => 0) W r ω)) hx0
      (by norm_num : (0 : ℝ) < 2) q 1
    simpa using h
  have hint := integral_mono (f := fun ω => Pf ω ^ q * x)
    (g := fun ω => 2 * Pf ω ^ (q + 1) + (2 ^ q)⁻¹ * x ^ (q + 1)) (hPq.mul_const x)
    ((hPq1.const_mul 2).add (integrable_const _)) hpt
  rw [integral_mul_const, integral_add (hPq1.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const] at hint
  simp only [probReal_univ, smul_eq_mul, one_mul] at hint
  have e1 : ∫ ω, Pf ω ^ q ∂growthPathLaw W b = x ^ q := hxq.symm
  have e2 : ∫ ω, Pf ω ^ (q + 1) ∂growthPathLaw W b = pathPow α b E W r (q + 1) := rfl
  rw [e1, e2] at hint
  have h2q : (2 ^ q)⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 1 ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
    norm_num at this ⊢; linarith
  have hxq1 : 0 ≤ x ^ (q + 1) := pow_nonneg hx0 _
  have e3 : x ^ q * x = x ^ (q + 1) := (pow_succ x q).symm
  rw [e3] at hint
  nlinarith [mul_le_mul_of_nonneg_right h2q hxq1]

/-- `(E P^q)^{1/q} ≤ W`. -/
theorem pathPow_rpow_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {b : ℝ} (hb : b < 1 / 2)
    {E : ℝ} (h1 : -2 < E) (h2 : E < 2) (r : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    pathPow α b E W r q ^ ((q : ℝ)⁻¹) ≤ W := by
  obtain ⟨-, hle⟩ := pathFrac_pow_facts (W := W) hα0 hα1 hb h1 h2 r q
  calc pathPow α b E W r q ^ ((q : ℝ)⁻¹) ≤ ((W : ℝ) ^ q) ^ ((q : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pathPow_nonneg _ _ _ _ _) hle (by positivity)
    _ = W := Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by omega)

/-- **Uniform `q`-th moments at every time `t > 0`.** -/
theorem fracPow_bound (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {q : ℕ} (hq : 1 ≤ q)
    (hS : FracPowStep α q) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {t : ℝ} (ht : 0 < t) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → pathPow α b E W ⌊(W : ℝ) * t⌋₊ q ≤ C := by
  obtain ⟨c, K, hc, hc1, hK, hR⟩ := fracPow_rec hMT hGA hLp hα0 hα1 hq hS hb0 hb h1 h2
    (ε' := t / 4) (by positivity)
  set M := max 1 (8 * K / c)
  have hM1 : 1 ≤ M := le_max_left _ _
  set R := max (M + K) (32 * q / (c * t))
  refine ⟨R ^ q, ?_⟩
  obtain ⟨W₁, hW₁⟩ := hR t
  refine ⟨max W₁ (⌈8 / t⌉₊ + 1), fun W hW => ?_⟩
  have hWW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW8 : ⌈8 / t⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWr : (8 / t : ℝ) < W := by
    have := Nat.le_ceil (8 / t)
    have : ((⌈8 / t⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW8
    push_cast at this; linarith
  have hWp : (0 : ℝ) < W := lt_of_le_of_lt (by positivity) hWr
  set x := (W : ℝ) * t with hx
  have hx8 : 8 < x := by rw [hx]; rwa [div_lt_iff₀ ht] at hWr
  set r₁ := ⌊(W : ℝ) * t⌋₊
  set m₀ := ⌊(W : ℝ) * t / 2⌋₊
  have hm₀le : (m₀ : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have hm₀ge : x / 2 - 1 < m₀ := by
    have := Nat.lt_floor_add_one ((W : ℝ) * t / 2); rw [← hx] at this; linarith
  have hr₁le : (r₁ : ℝ) ≤ W * t := Nat.floor_le (by positivity)
  have hr₁ge : (W : ℝ) * t - 1 < r₁ := by have := Nat.lt_floor_add_one ((W : ℝ) * t); linarith
  have hm₀r₁ : m₀ ≤ r₁ := by
    have : (m₀ : ℝ) < r₁ + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  set r₀ := r₁ - m₀
  have hr₀ : (r₀ : ℝ) = r₁ - m₀ := by rw [Nat.cast_sub hm₀r₁]
  have hr₀ge : x / 4 ≤ r₀ := by rw [hr₀]; linarith
  have hsum : r₀ + m₀ = r₁ := Nat.sub_add_cancel hm₀r₁
  -- the sequence `x_m = (E P_{r₀+m}^q)^{1/q}`
  set xs : ℕ → ℝ := fun m => pathPow α b E W (r₀ + m) q ^ ((q : ℝ)⁻¹)
  have hxs0 : ∀ m, 0 ≤ xs m := fun m => Real.rpow_nonneg (pathPow_nonneg _ _ _ _ _) _
  have hxsq : ∀ m, xs m ^ q = pathPow α b E W (r₀ + m) q := fun m =>
    Real.rpow_inv_natCast_pow (pathPow_nonneg _ _ _ _ _) (by omega)
  set a := c / (4 * W)
  have ha : 0 < a := by positivity
  have hrec : ∀ m, m < m₀ → xs (m + 1) ^ q ≤ xs m ^ q - a * xs m ^ (q + 1) + K / W := by
    intro m hm
    have hr1 : 1 ≤ r₀ + m := by
      have : (1 : ℝ) ≤ r₀ := by linarith
      have : 1 ≤ r₀ := by exact_mod_cast this
      omega
    have hrε : t / 4 * W ≤ ((r₀ + m : ℕ) : ℝ) := by
      push_cast
      have : t / 4 * W = x / 4 := by rw [hx]; ring
      rw [this]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    have hrT : ((r₀ + m : ℕ) : ℝ) ≤ t * W := by
      have : r₀ + m < r₁ := by omega
      have : ((r₀ + m : ℕ) : ℝ) < r₁ := by exact_mod_cast this
      nlinarith
    have h := hW₁ W hWW₁ (r₀ + m) hr1 hrε hrT
    have hJ := pathPow_succ_pow_le (W := W) hα0 hα1 hb h1 h2 (r₀ + m) hq
    rw [hxsq (m + 1), hxsq m, show r₀ + (m + 1) = r₀ + m + 1 by ring]
    have : a * xs m ^ (q + 1) ≤ c / W * pathPow α b E W (r₀ + m) (q + 1) := by
      have e : a * xs m ^ (q + 1) = c / W * (xs m ^ (q + 1) / 4) := by
        simp only [a]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hMK : 2 * (K / W) ≤ a * M ^ (q + 1) := by
    have hMq : M ≤ M ^ (q + 1) := le_self_pow₀ hM1 (by omega)
    have h8 : 8 * K / c ≤ M := le_max_right _ _
    have e : 2 * (K / W) = a * (8 * K / c) := by simp only [a]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (h8.trans hMq) ha.le
  have hqr : (q : ℝ) + 1 ≤ (q : ℝ) + 1 := le_rfl
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h0 : xs 0 ≤ max (M + K / W) (2 * q / (a * ((q : ℝ) + 1))) := by
    refine le_max_of_le_right ((pathPow_rpow_le (W := W) hα0 hα1 hb h1 h2 _ hq).trans ?_)
    have e : 2 * (q : ℝ) / (a * ((q : ℝ) + 1)) = W * (8 * q / (c * (q + 1))) := by
      simp only [a]; field_simp; norm_num
    rw [e]
    refine le_mul_of_one_le_right hWp.le ?_
    rw [one_le_div (by positivity)]
    have : c * ((q : ℝ) + 1) ≤ (q : ℝ) + 1 := mul_le_of_le_one_left (by positivity) hc1
    have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hit := ode_iter hq ha (by positivity) hM1 hMK hqr xs hxs0 m₀ hrec h0 m₀ le_rfl
  have hfin : xs m₀ ≤ R := by
    refine hit.trans (max_le_max ?_ ?_)
    · have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hW8
      have : K / W ≤ K := div_le_self hK hW1r
      linarith
    · have hm₀pos : (0 : ℝ) < m₀ := by linarith
      have e : 2 * (q : ℝ) / (a * ((q : ℝ) + 1 + m₀)) = 8 * q * W / (c * ((q : ℝ) + 1 + m₀)) :=
        by simp only [a]; field_simp; norm_num
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      have hWt : (W : ℝ) * t ≤ 4 * m₀ + 4 := by linarith
      have : (W : ℝ) * t ≤ 4 * ((q : ℝ) + 1 + m₀) := by linarith
      have h' := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 8 * q * c)
      nlinarith
  have hfq := pow_le_pow_left₀ (hxs0 m₀) hfin q
  rw [hxsq m₀, hsum] at hfq
  exact hfq

/-- The far `q`-th moment as an integral of the near one. -/
theorem lintegral_farFracTrace_pow_eq {α b E : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W) (n q : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Jet.farFracTrace b E α W n ω ^ q) ∂growthPathLaw W b =
      ENNReal.ofReal (pathPow α b E W n q) := by
  obtain ⟨hi, -⟩ := pathFrac_pow_facts (W := W) hα0 hα1 hb h1 h2 n q
  rw [pathPow, ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => pow_nonneg (fracTrace_nonneg' _ _) _)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_farFracTrace_eq hb h1 h2 hW α] with ω hω
  rw [hω n]

/-- **`FarFracTraceMomentsAt 4`** (`α = 1/8`) from `MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient` and `FracPowStep (1/8) 4`. -/
theorem farFracTraceMomentsAt_four_of_step (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) (hS : FracPowStep (1 / 8) 4) :
    Jet.FarFracTraceMomentsAt 4 := by
  intro b E hb0 hb h1 h2 s hs
  refine ⟨1 / 8, by norm_num, by norm_num, ?_⟩
  obtain ⟨C, W₀, hC⟩ := fracPow_bound hMT hGA hLp (by norm_num) (by norm_num) (q := 4)
    (by norm_num) hS hb0 hb h1 h2 hs
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (max W₀ 1)] with W hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have e : ∀ ω, Jet.farFracTrace b E (1 / 8) W (ClosedPath.closeLen s W) ω ^ (4 : ℝ) =
      Jet.farFracTrace b E (1 / 8) W (ClosedPath.closeLen s W) ω ^ (4 : ℕ) := fun ω => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [e]
  rw [lintegral_farFracTrace_pow_eq (by norm_num) (by norm_num) hb h1 h2 hW1]
  exact ENNReal.ofReal_le_ofReal (hC W (le_trans (le_max_left _ _) hW))

/-- `F^p ≤ 1 + F^q` for `F ≥ 0`, `p ≤ q`. -/
theorem rpow_le_one_add_pow {F p : ℝ} (hF : 0 ≤ F) (hp : 0 ≤ p) {q : ℕ} (hpq : p ≤ q) :
    F ^ p ≤ 1 + F ^ q := by
  rcases le_total F 1 with h | h
  · have := Real.rpow_le_one hF h hp
    have : 0 ≤ F ^ q := pow_nonneg hF q
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hpq
    rw [Real.rpow_natCast] at this
    linarith

/-- **`FarFracTraceMoments`** (every `p ≥ 1`; `q = ⌈p⌉`, `α = 1/(2q)`) from
`MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient` and
`FracPowStep (1/(2q)) q` for every `q ≥ 1`. -/
theorem farFracTraceMoments_of_step (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hS : ∀ q : ℕ, 1 ≤ q → FracPowStep (1 / (2 * q)) q) : Jet.FarFracTraceMoments := by
  intro b E hb0 hb h1 h2 s hs p hp
  set q := ⌈p⌉₊
  have hpq : p ≤ q := Nat.le_ceil p
  have hq : 1 ≤ q := by
    have : (1 : ℝ) ≤ q := hp.trans hpq
    exact_mod_cast this
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hα0 : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hα1 : 1 / (2 * (q : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  refine ⟨1 / (2 * q), hα0, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  obtain ⟨C, W₀, hC⟩ := fracPow_bound hMT hGA hLp hα0 hα1 hq (hS q hq) hb0 hb h1 h2 hs
  refine ⟨1 + C, ?_⟩
  filter_upwards [eventually_ge_atTop (max W₀ 1)] with W hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have := Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  have hle : ∀ ω, ENNReal.ofReal (Jet.farFracTrace b E (1 / (2 * q)) W
      (ClosedPath.closeLen s W) ω ^ p) ≤ 1 + ENNReal.ofReal (Jet.farFracTrace b E (1 / (2 * q))
        W (ClosedPath.closeLen s W) ω ^ q) := fun ω => by
    have hF0 : 0 ≤ Jet.farFracTrace b E (1 / (2 * q)) W (ClosedPath.closeLen s W) ω :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (le_max_right _ _) _
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (pow_nonneg hF0 _)]
    exact ENNReal.ofReal_le_ofReal (rpow_le_one_add_pow hF0 (by linarith) hpq)
  refine (lintegral_mono hle).trans ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_farFracTrace_pow_eq hα0 hα1 hb h1 h2 hW1, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (pathPow_nonneg _ _ _ _ _)]
  exact ENNReal.ofReal_le_ofReal (by linarith [hC W (le_trans (le_max_left _ _) hW)])

end BlockBand.SourceProcess.PhysApprox.B3.FracMom
