module

public import BlockBand.Transmission.PathScalar.Moment

/-!
# The passive initial scalar lemma: the exit clause (Markov + union bound)

Main results:
* `markov_ofReal`: `P(d < f) ≤ (C/(dW))^p` from `‖f‖_p ≤ C/W` (real `f ≥ 0`);
* `union_lengths_le`: the union bound over `1 ≤ r ≤ TW` with real constant `N = ⌊TW⌋₊`;
* `exit_of_moment`: any family satisfying the `moment` clause satisfies the `exit` clause;
* `passiveInitialScalar_exit`: the `exit` field, from `MatchedTracesContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal

/-- Markov with a real moment: if `f ≥ 0` and `‖f‖_p ≤ C/W`, then `P(d < f) ≤ (C/(dW))^p`
(here written `d⁻¹^p (C/W)^p`), for `C ≥ 0`, `d > 0`, `p > 0`. -/
theorem markov_ofReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) {p d c : ℝ} (hp : 0 < p) (hd : 0 < d) (hc : 0 ≤ c)
    (hm : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal c) :
    μ {ω | d < f ω} ≤ ENNReal.ofReal (d⁻¹ ^ p * c ^ p) := by
  have hsub : {ω | d < f ω} ⊆ {ω | ENNReal.ofReal d ≤ ‖f ω‖ₑ} := fun ω hω => by
    change d < f ω at hω
    change ENNReal.ofReal d ≤ ‖f ω‖ₑ
    rw [Real.enorm_eq_ofReal (hf ω)]
    exact ENNReal.ofReal_le_ofReal hω.le
  have hM := meas_ge_le_mul_pow_eLpNorm_enorm μ (p := ENNReal.ofReal p)
    (by simpa using hp) ENNReal.ofReal_ne_top (f := f) (ε := ENNReal.ofReal d)
    (by simpa using hd) (fun h => absurd h ENNReal.ofReal_ne_top)
  rw [ENNReal.toReal_ofReal hp.le] at hM
  refine (measure_mono hsub).trans (hM.trans ?_)
  rw [← ENNReal.ofReal_inv_of_pos hd, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hd.le) hp.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.2 hd.le) _)]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_nonneg hc hp.le]
  exact ENNReal.rpow_le_rpow hm hp.le

/-- `1 ≤ r ≤ ⌊TW⌋₊` gives `r ≤ TW`. -/
theorem le_of_mem_Icc_floor {T x : ℝ} {r : ℕ} (hr : r ∈ Finset.Icc 1 ⌊T * x⌋₊) :
    (r : ℝ) ≤ T * x := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hr
  by_cases h : 0 ≤ T * x
  · exact (Nat.cast_le.2 h2).trans (Nat.floor_le h)
  · rw [Nat.floor_of_nonpos (le_of_not_ge h)] at h2; omega

/-- **Union bound over lengths**: if each length `1 ≤ r ≤ TW` has
`P(A_r) ≤ ofReal β`, then `P(∃ r, 1 ≤ r ≤ TW, A_r) ≤ ofReal (⌊TW⌋₊ β)`. -/
theorem union_lengths_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℕ → Set Ω)
    {T x β : ℝ}
    (h : ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * x → μ (A r) ≤ ENNReal.ofReal β) :
    μ {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * x ∧ ω ∈ A r} ≤
      ENNReal.ofReal ((⌊T * x⌋₊ : ℝ) * β) := by
  have hsub : {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * x ∧ ω ∈ A r} ⊆
      ⋃ r ∈ Finset.Icc 1 ⌊T * x⌋₊, A r := by
    rintro ω ⟨r, h1, h2, h3⟩
    exact Set.mem_biUnion (Finset.mem_Icc.2 ⟨h1, Nat.le_floor h2⟩) h3
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ r ∈ Finset.Icc 1 ⌊T * x⌋₊, μ (A r)
      ≤ ∑ _r ∈ Finset.Icc 1 ⌊T * x⌋₊, ENNReal.ofReal β :=
        Finset.sum_le_sum fun r hr =>
          h r (Finset.mem_Icc.1 hr).1 (le_of_mem_Icc_floor hr)
    _ = ENNReal.ofReal ((⌊T * x⌋₊ : ℝ) * β) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The real arithmetic of the exit bound: with `p = D + 2`, `N ≤ A W`, `A ≥ 0`,
`A d⁻¹^p C^p ≤ W` (with `A ≥ 0` implicit in `N ≤ AW`): `N d⁻¹^p (C/W)^p ≤ W^{-D}`. -/
theorem exit_arith {N A C d D x : ℝ} (hx : 0 < x) (hN : N ≤ A * x) (hC : 0 ≤ C)
    (hd : 0 < d) (hD : 0 < D) (hK : A * (d⁻¹ ^ (D + 2) * C ^ (D + 2)) ≤ x) :
    N * (d⁻¹ ^ (D + 2) * (C / x) ^ (D + 2)) ≤ x ^ (-D) := by
  have hK0 : 0 ≤ d⁻¹ ^ (D + 2) * C ^ (D + 2) :=
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 hd.le) _) (Real.rpow_nonneg hC _)
  have hxp : 0 < x ^ (D + 2) := Real.rpow_pos_of_pos hx _
  have e1 : x ^ (-D) = x * x ^ (-D - 1) := by
    rw [← Real.rpow_one_add' hx.le (by linarith)]; ring_nf
  have e2 : x / x ^ (D + 2) = x ^ (-D - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le, ← Real.rpow_one_add' hx.le (by linarith)]
    ring_nf
  have hpos : 0 ≤ x ^ (-D - 1) := Real.rpow_nonneg hx.le _
  rw [Real.div_rpow hC hx.le, e1]
  calc N * (d⁻¹ ^ (D + 2) * (C ^ (D + 2) / x ^ (D + 2)))
      = N * (d⁻¹ ^ (D + 2) * C ^ (D + 2)) / x ^ (D + 2) := by ring
    _ ≤ A * x * (d⁻¹ ^ (D + 2) * C ^ (D + 2)) / x ^ (D + 2) := by gcongr
    _ = A * (d⁻¹ ^ (D + 2) * C ^ (D + 2)) * (x / x ^ (D + 2)) := by ring
    _ ≤ x * x ^ (-D - 1) := by rw [e2]; exact mul_le_mul_of_nonneg_right hK hpos

/-- **The exit clause from the moment clause.** Any `δ : ℕ → ℕ → GrowthPath W → ℝ`-type family
(here the concrete `δ_{0,r}`) that satisfies the `moment` field also satisfies the `exit`
field: Markov at `p = D + 2` and the union bound over `r ≤ TW`. -/
theorem exit_of_moment
    (hmom : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ, 1 ≤ r →
        (r : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
            (growthPathLaw W b) ≤ ENNReal.ofReal (C / W)) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T d D : ℝ, 0 < κ → 0 < d → 0 < D →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
          d < jetDistance0 b E (pathX b E W r ω)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) := by
  intro b hb hb' κ T d D hκ hd hD
  obtain ⟨C, W₁, hC⟩ := hmom b hb hb' κ T (D + 2) hκ (by linarith)
  set Cp : ℝ := max C 0
  set A : ℝ := max T 0
  set K : ℝ := A * (d⁻¹ ^ (D + 2) * Cp ^ (D + 2))
  refine ⟨max W₁ (⌈K⌉₊ + 1), fun W hW E hE => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hWK : ⌈K⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hW
  have hx : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hKx : K ≤ W := by
    have h1 := Nat.le_ceil K
    have h2 : ((⌈K⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈K⌉₊ ≤ W)
    linarith
  refine (union_lengths_le (β := d⁻¹ ^ (D + 2) * (Cp / W) ^ (D + 2)) (growthPathLaw W b)
    (fun r => {ω | d < jetDistance0 b E (pathX b E W r ω)}) fun r hr hrT => ?_).trans ?_
  · refine markov_ofReal _ (fun ω => norm_nonneg _) (by linarith) hd
      (div_nonneg (le_max_right _ _) hx.le) ((hC W hW1 E hE r hr hrT).trans ?_)
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hx.le)
  · refine ENNReal.ofReal_le_ofReal (exit_arith hx ?_ (le_max_right _ _) hd hD hKx)
    by_cases h : 0 ≤ T * W
    · exact (Nat.floor_le h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx.le)
    · rw [Nat.floor_of_nonpos (le_of_not_ge h), Nat.cast_zero]
      exact mul_nonneg (le_max_right _ _) hx.le

/-- **`PassiveInitialScalarContract.exit`**, from `MatchedTracesContract` (via
`passiveInitialScalar_moment` and `exit_of_moment`). -/
theorem passiveInitialScalar_exit (hMT : MatchedTracesContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T d D : ℝ, 0 < κ → 0 < d → 0 < D →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
          d < jetDistance0 b E (pathX b E W r ω)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
  exit_of_moment (passiveInitialScalar_moment hMT)

end BlockBand.Transmission.PathScalar
