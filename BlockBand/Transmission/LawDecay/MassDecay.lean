module

public import BlockBand.Transmission.LawDecay.Window
public import BlockBand.Transmission.LengthUniform.ConductanceUniform
public import BlockBand.Transmission.Generator.DriftOneTools

/-!
# Exponential decay of the mean conductance at finite `W`

Fix `0 < b < 1/2`, bulk `E`, `c₀ = 5D₀(E)/512 > 0`. All constants are chosen before the moving
energy `e` (`|e W - E| ≤ C_e W⁻²`), the time `t ≥ 2` and the slack `δ > 0`.

* **`sqrt_decay`**: `∃ K ≥ 0`, eventually in `W`, `E√g_{⌊Wt⌋} ≤ K e^{-c₀(t-1)} + δ`. Proof:
  `ε = min(1, (δ/5)²)`, `lyap_window` from `r = W` (time 1), the initial bound
  `E Φ_ε(g_W, P₂) ≤ (E g_W + 2)/2 ≤ M₀` (length-uniform conductance moments, `p = 1`),
  `E√g ≤ (64/63)E Φ_ε`, and `S_W → 0` (`stepErr_sum_tendsto`, `stepCubic_sum_tendsto`).
  No stopping is needed: the shift `ε` replaces a stop at `g > ε`, and the a.s. bound `g ≤ W`
  a stop at `g < K`.
* **`mass_decay`**: `∃ C, c > 0`, eventually `E g_{⌊Wt⌋} ≤ C e^{-ct} + δ`, with `c = 2c₀/3`. Proof:
  `g ≤ λ√g + g²/λ²` with `λ = e^{c₀(t-1)/3}` and the length-uniform `E g² ≤ C₂` (the uniformly
  bounded second moment for `t ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Generator

theorem transportD0_pos {b E : ℝ} (hb0 : 0 < b) (h1 : -2 < E) (h2 : E < 2) :
    0 < transportD0 b E := by
  have : 0 < 4 - E ^ 2 := by nlinarith
  unfold transportD0; positivity

/-- The real moment bound `E g_r^n ≤ max C 0` from the lintegral form. -/
theorem integral_pow_le {b E' : ℝ} {W r : ℕ} (hb : b < 1) (h1' : -2 < E') (h2' : E' < 2) (n : ℕ)
    {C : ℝ} (h : ∫⁻ ω, ‖pathConductance b E' W r ω‖ₑ ^ ((n : ℕ) : ℝ) ∂growthPathLaw W b ≤
      ENNReal.ofReal C) :
    ∫ ω, pathPower b E' W 1 r ω ^ n ∂growthPathLaw W b ≤ max C 0 := by
  have hf : (fun ω => pathPower b E' W 1 r ω ^ n) = fun ω => pathConductance b E' W r ω ^ n :=
    funext fun ω => by rw [pathPower_one']
  rw [hf]
  have hm : Measurable (pathConductance b E' W r) := by
    have e : pathConductance b E' W r = pathPower b E' W 1 r :=
      funext fun ω => (pathPower_one' b E' W r ω).symm
    rw [e]; exact measurable_pathPower b E' 1 r
  refine integral_pow_le_of_lintegral hm ?_ n (le_max_right _ _)
    (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  filter_upwards [pathPower_mem (W := W) hb h1' h2'] with ω hω
  rw [← pathPower_one']; exact (hω 1 r le_rfl).1

theorem windowErr_tendsto (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {t ε : ℝ}
    (ht : 1 < t) : Tendsto (fun W : ℕ => windowErr b E (e W) ε t W) atTop (𝓝 0) := by
  have h := ((stepErr_sum_tendsto hMT hGA hLp hP hb0 hb h1 h2 he ht).const_mul
    ((Real.sqrt ε)⁻¹ ^ 5)).add
    ((stepCubic_sum_tendsto hMT hGA hLp hb0 hb h1 h2 he ht).const_mul (ε ^ (-7 / 2 : ℝ) / 6))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun W => ?_
  simp only [windowErr, Finset.sum_add_distrib, Finset.mul_sum]

/-- **`E√g_{⌊Wt⌋} ≤ K e^{-c₀(t-1)} + δ` eventually** (constants before `e, t, δ`). -/
theorem sqrt_decay (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → ∀ t : ℝ, 2 ≤ t →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ W : ℕ in atTop,
        ∫ ω, Real.sqrt (pathPower b (e W) W 1 ⌊(W : ℝ) * t⌋₊ ω) ∂growthPathLaw W b ≤
          K * Real.exp (-(5 / 512 * transportD0 b E * (t - 1))) + δ := by
  set c₀ := 5 / 512 * transportD0 b E
  set κI := min (E + 2) (2 - E)
  have hκ : 0 < κI := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval κI :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨C₁, hC₁⟩ := LengthUniform.lengthUniform_conductance_holds hMT hGA hLp b hb0 hb (κI / 2) (1 / 2)
    ((1 : ℕ) : ℝ) (by positivity) (by norm_num) (by norm_num)
  set M₀ := (max C₁ 0 + 2) / 2
  have hM₀ : 1 ≤ M₀ := by have := le_max_right C₁ 0; simp only [M₀]; linarith
  refine ⟨64 / 63 * Real.exp c₀ * M₀, by positivity, fun Ce e he t ht δ hδ => ?_⟩
  set ε := min 1 ((δ / 5) ^ 2)
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hsε : Real.sqrt ε ≤ δ / 5 := by
    have := Real.sqrt_le_sqrt (min_le_right 1 ((δ / 5) ^ 2))
    rwa [Real.sqrt_sq (by positivity)] at this
  obtain ⟨W₀, hW₀⟩ := hC₁ t
  have hS := windowErr_tendsto hMT hGA hLp hP hb0 hb h1 h2 he (ε := ε) (by linarith : 1 < t)
  filter_upwards [hS.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < δ / 4)),
    eventually_ge_atTop (max (max W₀ (EnergyUniform.windowWidth κI Ce)) (max 1 ⌈c₀⌉₊))]
    with W hSW hW
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₀', hWw⟩, hW1, hWc⟩ := hW
  have hWb := EnergyUniform.window_mem_bulkInterval hκ hWw hEb (he W (by omega))
  have h1' : -2 < e W := by have := hWb.1; linarith
  have h2' : e W < 2 := by have := hWb.2; linarith
  have hc : c₀ ≤ W := (Nat.le_ceil c₀).trans (by exact_mod_cast hWc)
  have hwin := lyap_window (W := W) (t := t) hb0 hb h1 h2 h1' h2' hε hε1 (by linarith) hW1 hc
  -- the initial bound at time 1
  have hy0 : lyapMean b (e W) W ε W ≤ M₀ := by
    have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have htW : (W : ℝ) ≤ t * W := by
      have := mul_le_mul_of_nonneg_right ht1 hW0.le; linarith
    have hm := hW₀ W hW₀' (e W) hWb W (by linarith) htW
    have := integral_pow_le (W := W) (r := W) (by linarith) h1' h2' 1 hm
    simp only [pow_one] at this
    exact (lyapMean_le (by linarith) h1' h2' hε hε1 W).trans (by simp only [M₀]; linarith)
  have hmax : max (lyapMean b (e W) W ε W - 2 * Real.sqrt ε) 0 ≤ M₀ :=
    max_le (by linarith [Real.sqrt_nonneg ε]) (by linarith)
  have hsq := sqrt_le_lyapMean (W := W) (b := b) (by linarith) h1' h2' hε hε1 ⌊(W : ℝ) * t⌋₊
  have hE : 0 ≤ Real.exp c₀ * Real.exp (-(c₀ * (t - 1))) := by positivity
  have := mul_le_mul_of_nonneg_left hmax hE
  have e1 : 64 / 63 * Real.exp c₀ * M₀ * Real.exp (-(c₀ * (t - 1))) =
      64 / 63 * (Real.exp c₀ * Real.exp (-(c₀ * (t - 1))) * M₀) := by ring
  rw [e1]
  nlinarith

theorem sqrt_le_lam {g lam : ℝ} (hg : 0 ≤ g) (hl : 0 < lam) :
    g ≤ lam * Real.sqrt g + g ^ 2 / lam ^ 2 := by
  have hs := Real.sqrt_nonneg g
  have hsq := Real.sq_sqrt hg
  have h0 : 0 ≤ g ^ 2 / lam ^ 2 := by positivity
  rcases le_total (Real.sqrt g) lam with h | h
  · have : g ≤ lam * Real.sqrt g := by nlinarith
    linarith
  · have hg2 : lam ^ 2 ≤ g := by nlinarith
    have : g ≤ g ^ 2 / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    nlinarith [mul_nonneg hl.le hs]

/-- `E g ≤ λE√g + E g²/λ²` at one width (integrability from `0 ≤ g ≤ W`). -/
theorem integral_le_lam {b E' : ℝ} {W r : ℕ} (hb : b < 1) (h1' : -2 < E') (h2' : E' < 2)
    {lam : ℝ} (hl : 0 < lam) :
    ∫ ω, pathPower b E' W 1 r ω ∂growthPathLaw W b ≤
      lam * ∫ ω, Real.sqrt (pathPower b E' W 1 r ω) ∂growthPathLaw W b +
        (∫ ω, pathPower b E' W 1 r ω ^ 2 ∂growthPathLaw W b) / lam ^ 2 := by
  have hd := pathPower_mem (W := W) hb h1' h2'
  have hm := measurable_pathPower (W := W) b E' 1 r
  have iG : Integrable (pathPower b E' W 1 r) (growthPathLaw W b) :=
    integrable_of_abs_le hm (pathPower_bound hb h1' h2' le_rfl r)
  have iS : Integrable (fun ω => Real.sqrt (pathPower b E' W 1 r ω)) (growthPathLaw W b) :=
    integrable_of_abs_le hm.sqrt (C := W + 1) (hd.mono fun ω h => by
      obtain ⟨a0, a1, a2⟩ := h 1 r le_rfl
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have hs := Real.sqrt_nonneg (pathPower b E' W 1 r ω)
      have hsq := Real.sq_sqrt a0
      nlinarith)
  have iQ : Integrable (fun ω => pathPower b E' W 1 r ω ^ 2) (growthPathLaw W b) :=
    integrable_of_abs_le (hm.pow_const 2) (C := (W : ℝ) ^ 2) (hd.mono fun ω h => by
      obtain ⟨a0, a1, a2⟩ := h 1 r le_rfl
      rw [abs_pow, abs_of_nonneg a0]; exact pow_le_pow_left₀ a0 (a1.trans a2) 2)
  have iR : Integrable (fun ω => lam * Real.sqrt (pathPower b E' W 1 r ω) +
      pathPower b E' W 1 r ω ^ 2 / lam ^ 2) (growthPathLaw W b) :=
    (iS.const_mul lam).add (iQ.div_const _)
  have := integral_mono_ae iG iR (hd.mono fun ω h => sqrt_le_lam (h 1 r le_rfl).1 hl)
  rwa [integral_add (iS.const_mul lam) (iQ.div_const _), integral_const_mul, integral_div] at this

/-- **Exponential decay of `E g_{⌊Wt⌋}` at finite `W`** (constants before `e, t, δ`). -/
theorem mass_decay (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    ∃ C c : ℝ, 0 < c ∧ ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → ∀ t : ℝ, 2 ≤ t →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ W : ℕ in atTop,
        ∫ ω, pathConductance b (e W) W ⌊(W : ℝ) * t⌋₊ ω ∂growthPathLaw W b ≤
          C * Real.exp (-(c * t)) + δ := by
  obtain ⟨K, hK0, hK⟩ := sqrt_decay hMT hGA hLp hP hb0 hb h1 h2
  set c₀ := 5 / 512 * transportD0 b E
  have hc₀ : 0 < c₀ := by have := transportD0_pos hb0 h1 h2; positivity
  set κI := min (E + 2) (2 - E)
  have hκ : 0 < κI := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval κI :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨C₂, hC₂⟩ := LengthUniform.lengthUniform_conductance_holds hMT hGA hLp b hb0 hb
    (κI / 2) (1 / 2) ((2 : ℕ) : ℝ) (by positivity) (by norm_num) (by norm_num)
  refine ⟨(K + max C₂ 0) * Real.exp (2 * c₀ / 3), 2 * c₀ / 3, by positivity,
    fun Ce e he t ht δ hδ => ?_⟩
  set lam := Real.exp (c₀ * (t - 1) / 3)
  have hl : 0 < lam := Real.exp_pos _
  obtain ⟨W₂, hW₂⟩ := hC₂ t
  filter_upwards [hK Ce e he t ht (δ / lam) (by positivity),
    eventually_ge_atTop (max W₂ (max (EnergyUniform.windowWidth κI Ce) 1))] with W hsq hW
  simp only [max_le_iff] at hW
  obtain ⟨hW₂', hWw, hW1⟩ := hW
  have hWb := EnergyUniform.window_mem_bulkInterval hκ hWw hEb (he W (by omega))
  have h1' : -2 < e W := by have := hWb.1; linarith
  have h2' : e W < 2 := by have := hWb.2; linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  set n := ⌊(W : ℝ) * t⌋₊
  have hn1 : (W : ℝ) ≤ n := by
    have : W ≤ n := Nat.le_floor (by nlinarith)
    exact_mod_cast this
  have hn2 : (n : ℝ) ≤ t * W := by
    rw [mul_comm]; exact Nat.floor_le (by positivity)
  have hg2 := integral_pow_le (W := W) (r := n) (by linarith) h1' h2' 2
    (hW₂ W hW₂' (e W) hWb n (by linarith) hn2)
  have hI := integral_le_lam (W := W) (r := n) (b := b) (by linarith) h1' h2' hl
  have hG : (fun ω => pathConductance b (e W) W n ω) = pathPower b (e W) W 1 n :=
    funext fun ω => (pathPower_one' _ _ _ _ _).symm
  rw [hG]
  have e1 : lam * Real.exp (-(c₀ * (t - 1))) = Real.exp (-(2 * c₀ / 3 * (t - 1))) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : (lam ^ 2)⁻¹ = Real.exp (-(2 * c₀ / 3 * (t - 1))) := by
    rw [sq, ← Real.exp_add, ← Real.exp_neg]; congr 1; ring
  have e3 : Real.exp (2 * c₀ / 3) * Real.exp (-(2 * c₀ / 3 * t)) =
      Real.exp (-(2 * c₀ / 3 * (t - 1))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hx : 0 ≤ Real.exp (-(2 * c₀ / 3 * (t - 1))) := (Real.exp_pos _).le
  have h3 : lam * (K * Real.exp (-(c₀ * (t - 1))) + δ / lam) =
      K * Real.exp (-(2 * c₀ / 3 * (t - 1))) + δ := by
    rw [mul_add, mul_div_cancel₀ _ hl.ne', ← e1]; ring
  have h4 : (∫ ω, pathPower b (e W) W 1 n ω ^ 2 ∂growthPathLaw W b) / lam ^ 2 ≤
      max C₂ 0 * Real.exp (-(2 * c₀ / 3 * (t - 1))) := by
    rw [div_eq_mul_inv, e2]; exact mul_le_mul_of_nonneg_right hg2 hx
  have h5 := mul_le_mul_of_nonneg_left hsq hl.le
  rw [h3] at h5
  calc ∫ ω, pathPower b (e W) W 1 n ω ∂growthPathLaw W b
      ≤ K * Real.exp (-(2 * c₀ / 3 * (t - 1))) + δ +
          max C₂ 0 * Real.exp (-(2 * c₀ / 3 * (t - 1))) := by linarith
    _ = (K + max C₂ 0) * Real.exp (2 * c₀ / 3) * Real.exp (-(2 * c₀ / 3 * t)) + δ := by
      rw [mul_assoc, e3]; ring

end BlockBand.Transmission.LawDecay
