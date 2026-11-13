module

public import BlockBand.Native.ErdosRiabov.VS.ModulusWindow

set_option autoImplicit false

/-!
# Time regularity of the VS band process

Tail bounds for the supremum and the modulus of continuity of the entries of the VS band process.

* `exists_norm_ringMatrix_le`: every entry of `ringMatrix z` is bounded by `|z_i| + |z_j|` for
  two coordinates.
* **`vsBand_sup_tail`**: `P(∃ t ≤ T, ∃ a b, λ ≤ |H_t(a,b)|) ≤ d · 2 exp(-λ²/(8T))`,
  `d = ringDim p` (coordinate tail `measure_exists_abs_compensated_coord_ge_le`, union bound).
* **`vsBand_modulus`**: for a mesh `h > 0` and a horizon `T`,
  `P(∃ s ≤ t ≤ min(s + h, T), ∃ a b, λ ≤ |H_t(a,b) - H_s(a,b)|) ≤
    (⌊T/h⌋ + 1) · d · 2 exp(-λ²/(512 h))`
  (windows `[jh, jh + 2h]`, `measure_window_le`, union bound over windows and coordinates).
* `vsBand_modulus_pow` (power form): with `N ≥ 1`, `C` real (`C > 0` in use),
  `h = N^{-C}`, `λ = N^{-C/3}`:
  the modulus event `sup_{|t-s| ≤ N^{-C}, t ≤ T} ‖H_t - H_s‖_max ≥ N^{-C/3}` has probability
  `≤ (⌊T N^C⌋ + 1) · d · 2 exp(-N^{C/3}/512)`; and `vsBand_sup_tail` with `λ = N` gives
  `P(sup_{t ≤ 1} ‖H_t‖_max ≥ N) ≤ d · 2 exp(-N²/8)`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-!
### Entries of `ringMatrix`
-/

theorem exists_norm_ringMatrix_le (z : Fin (ringDim p) → ℝ) (a b : p.Site) :
    ∃ i₁ i₂ : Fin (ringDim p), ‖ringMatrix p z a b‖ ≤ |z i₁| + |z i₂| := by
  simp only [ringMatrix, BlockBand.Parameters.gaussianReconstruction]
  split_ifs
  · refine ⟨ringEquiv p (.inl a), ringEquiv p (.inl a), ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_nonneg (z (ringEquiv p (.inl a)))]
  · refine ⟨ringEquiv p (.inr (a, b, false)), ringEquiv p (.inr (a, b, true)), ?_⟩
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  · refine ⟨ringEquiv p (.inr (b, a, false)), ringEquiv p (.inr (b, a, true)), ?_⟩
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]

theorem exists_coord_of_le_norm_ringMatrix {z : Fin (ringDim p) → ℝ} {a b : p.Site} {lam : ℝ}
    (h : lam ≤ ‖ringMatrix p z a b‖) : ∃ i, lam / 2 ≤ |z i| := by
  obtain ⟨i₁, i₂, hle⟩ := exists_norm_ringMatrix_le z a b
  by_cases h1 : lam / 2 ≤ |z i₁|
  · exact ⟨i₁, h1⟩
  · exact ⟨i₂, by linarith⟩

/-!
### Sup bound
-/

/-- **Sup bound.** For `T > 0` and `λ ≥ 0`:
`P(∃ t ≤ T, ∃ a b, λ ≤ |H_t(a,b)|) ≤ d · 2 exp(-λ²/(8T))`, `d = ringDim p`. -/
theorem vsBand_sup_tail (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (T : ℝ≥0)
    (hT : 0 < T) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ ∃ a b : p.Site,
        lam ≤ ‖vsBand p t x a b‖} ≤
      (ringDim p : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (8 * T))))) := by
  have hT' : (0 : ℝ) < T := hT
  have hcoord : ∀ i : Fin (ringDim p), driverLaw (κ := Fin (ringDim p)) μ
      {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ ((T : ℝ≥0) : WithTop ℝ≥0) ∧
        lam / 2 ≤ |smCompensated (vsNoise p) (fun _ _ => 0) i t x|} ≤
      2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (8 * T)))) := fun i => by
    have h := measure_exists_abs_compensated_coord_ge_le (isContinuousSemimartingale_vsNoise μ) i
      (isStoppingTime_const (driverAugmented (κ := Fin (ringDim p)) μ) T) T hT'
      (ae_of_all _ fun x t htT _ => by
        have hv : volume.real (Ioc (0 : ℝ) (t : ℝ)) = t := by
          have := Real.volume_real_Ioc_of_le (NNReal.coe_nonneg t)
          rw [sub_zero] at this
          exact this
        rw [Matrix.diagonal_apply_eq, setIntegral_const, hv, smul_eq_mul]
        have h1 := ringVariance_le_one p i
        have h0 := ringVariance_nonneg p i
        have htT' : (t : ℝ) ≤ T := htT
        nlinarith [t.2])
      (div_nonneg hlam (by norm_num : (0 : ℝ) ≤ 2))
    have hexp : (lam / 2) ^ 2 / (2 * (T : ℝ)) = lam ^ 2 / (8 * T) := by
      field_simp
      ring
    rwa [hexp] at h
  calc driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ ∃ a b : p.Site,
        lam ≤ ‖vsBand p t x a b‖}
      ≤ driverLaw (κ := Fin (ringDim p)) μ (⋃ i, {x | ∃ t : ℝ≥0, t ≤ T ∧
          (t : WithTop ℝ≥0) ≤ ((T : ℝ≥0) : WithTop ℝ≥0) ∧
          lam / 2 ≤ |smCompensated (vsNoise p) (fun _ _ => 0) i t x|}) := by
        refine measure_mono fun x hx => ?_
        obtain ⟨t, htT, a, b, hlt⟩ := hx
        obtain ⟨i, hi⟩ := exists_coord_of_le_norm_ringMatrix hlt
        refine mem_iUnion.2 ⟨i, t, htT, by exact_mod_cast htT, ?_⟩
        simp only [smCompensated, vsNoise_zero, Pi.zero_apply, sub_zero, integral_zero]
        exact hi
    _ ≤ ∑ i, driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧
          (t : WithTop ℝ≥0) ≤ ((T : ℝ≥0) : WithTop ℝ≥0) ∧
          lam / 2 ≤ |smCompensated (vsNoise p) (fun _ _ => 0) i t x|} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (ringDim p), 2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (8 * T)))) :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-!
### Modulus of continuity
-/

/-- **Modulus of continuity.** For a mesh `h > 0`, a horizon `T` and `λ ≥ 0`:
`P(∃ s ≤ t, t ≤ s + h, t ≤ T, ∃ a b, λ ≤ |H_t(a,b) - H_s(a,b)|) ≤
  (⌊T/h⌋ + 1) · d · 2 exp(-λ²/(512 h))`, `d = ringDim p`. -/
theorem vsBand_modulus (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (T h : ℝ≥0)
    (hh : 0 < h) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ s t : ℝ≥0, s ≤ t ∧ t ≤ s + h ∧ t ≤ T ∧
        ∃ a b : p.Site, lam ≤ ‖vsBand p t x a b - vsBand p s x a b‖} ≤
      (((⌊T / h⌋₊ + 1) * ringDim p : ℕ) : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (512 * h))))) := by
  set W : ℕ × Fin (ringDim p) → Set (RingSample p) := fun ji =>
    {x | ∃ u : ℝ≥0, (ji.1 : ℝ≥0) * h ≤ u ∧ u ≤ (ji.1 : ℝ≥0) * h + 2 * h ∧
      lam / 4 ≤ |vsNoise p u x ji.2 - vsNoise p ((ji.1 : ℝ≥0) * h) x ji.2|} with hW
  have hwin : ∀ ji, driverLaw (κ := Fin (ringDim p)) μ (W ji) ≤
      2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (512 * h)))) := fun ji => by
    have h2 : (0 : ℝ≥0) < 2 * h := by positivity
    have hw := measure_window_le μ ji.2 ((ji.1 : ℝ≥0) * h) (2 * h) h2
      (div_nonneg hlam (by norm_num : (0 : ℝ) ≤ 4))
    have hexp : (lam / 4) ^ 2 / (16 * ((2 * h : ℝ≥0) : ℝ)) = lam ^ 2 / (512 * h) := by
      push_cast
      field_simp
      ring
    rw [hexp] at hw
    exact hw
  set J := Finset.range (⌊T / h⌋₊ + 1) ×ˢ (Finset.univ : Finset (Fin (ringDim p)))
  calc driverLaw (κ := Fin (ringDim p)) μ {x | ∃ s t : ℝ≥0, s ≤ t ∧ t ≤ s + h ∧ t ≤ T ∧
        ∃ a b : p.Site, lam ≤ ‖vsBand p t x a b - vsBand p s x a b‖}
      ≤ driverLaw (κ := Fin (ringDim p)) μ (⋃ ji ∈ J, W ji) := by
        refine measure_mono fun x hx => ?_
        obtain ⟨s, t, hst, hts, htT, a, b, hlt⟩ := hx
        have he : vsBand p t x a b - vsBand p s x a b =
            ringMatrix p (vsNoise p t x - vsNoise p s x) a b := by
          rw [ringMatrix_sub]
          rfl
        rw [he] at hlt
        obtain ⟨i, hi⟩ := exists_coord_of_le_norm_ringMatrix hlt
        simp only [Pi.sub_apply] at hi
        set j := ⌊s / h⌋₊ with hj
        have hjs : (j : ℝ≥0) * h ≤ s :=
          (le_div_iff₀ hh).1 (Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ s / h))
        have hsj : s < (j : ℝ≥0) * h + h := by
          have := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one (s / h))
          rw [add_mul, one_mul] at this
          exact this
        have hjT : j ≤ ⌊T / h⌋₊ := Nat.floor_le_floor (by gcongr; exact hst.trans htT)
        refine mem_iUnion₂.2 ⟨(j, i), Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega),
          Finset.mem_univ _⟩, ?_⟩
        have htri := abs_sub_le (vsNoise p t x i) (vsNoise p ((j : ℝ≥0) * h) x i)
          (vsNoise p s x i)
        rw [abs_sub_comm (vsNoise p ((j : ℝ≥0) * h) x i)] at htri
        have hu : t ≤ (j : ℝ≥0) * h + 2 * h := by
          calc t ≤ s + h := hts
            _ ≤ (j : ℝ≥0) * h + h + h := by gcongr
            _ = (j : ℝ≥0) * h + 2 * h := by ring
        by_cases h1 : lam / 4 ≤ |vsNoise p t x i - vsNoise p ((j : ℝ≥0) * h) x i|
        · exact ⟨t, hjs.trans hst, hu, h1⟩
        · refine ⟨s, hjs, (hst.trans hu), ?_⟩
          linarith
    _ ≤ ∑ ji ∈ J, driverLaw (κ := Fin (ringDim p)) μ (W ji) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _ji ∈ J, 2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (512 * h)))) :=
        Finset.sum_le_sum fun ji _ => hwin ji
    _ = _ := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]

/-- **Modulus of continuity, power form.** For `N ≥ 1`, any real `C` (meaningful for `C > 0`),
mesh `h = N^{-C}` and level `λ = N^{-C/3}`:
`P(∃ s ≤ t ≤ min(s + N^{-C}, T), ∃ a b, N^{-C/3} ≤ |H_t(a,b) - H_s(a,b)|) ≤
  (⌊T / N^{-C}⌋ + 1) · d · 2 exp(-N^{C/3}/512)`. -/
theorem vsBand_modulus_pow (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (T : ℝ≥0)
    {N C : ℝ} (hN : 1 ≤ N) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ s t : ℝ≥0, s ≤ t ∧
        t ≤ s + ⟨N ^ (-C), Real.rpow_nonneg (by linarith) _⟩ ∧ t ≤ T ∧
        ∃ a b : p.Site, N ^ (-C / 3) ≤ ‖vsBand p t x a b - vsBand p s x a b‖} ≤
      (((⌊T / ⟨N ^ (-C), Real.rpow_nonneg (by linarith) _⟩⌋₊ + 1) * ringDim p : ℕ) :
        ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-(N ^ (C / 3) / 512)))) := by
  have hN0 : 0 < N := by linarith
  set h : ℝ≥0 := ⟨N ^ (-C), Real.rpow_nonneg (by linarith) _⟩ with hh
  have hpos : 0 < h := by
    have : (0 : ℝ) < (h : ℝ) := Real.rpow_pos_of_pos hN0 _
    exact_mod_cast this
  have hlam : 0 ≤ N ^ (-C / 3) := Real.rpow_nonneg hN0.le _
  have e : (N ^ (-C / 3)) ^ 2 / (512 * (h : ℝ)) = N ^ (C / 3) / 512 := by
    have hc : (h : ℝ) = N ^ (-C) := rfl
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_comm (512 : ℝ), ← div_div,
      ← Real.rpow_sub hN0]
    congr 2
    push_cast
    ring
  have hm := vsBand_modulus μ T h hpos hlam
  rwa [e] at hm

end BlockBand.Native.ErdosRiabov.VS
