module

public import BlockBand.Palm.RelativeLocalizationScales
public import BlockBand.Palm.GoodEventHolds

/-!
# Relative localization: the fields `short_row` and `short_column`

The moving-centre short flow at the scales `θ = 1/100`.
`shortRow_holds`, `shortColumn_holds`: the exact types of the fields `short_row`,
`short_column` of `RelativeLocalizationContract`, from

* `SemimartingaleItoFormula (N + N)` for every `N`, `StoppedSemimartingale 1`,
  `DysonBrownianMotion N` for every `N`;
* the finer-scale good event `BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP`, i.e. the
  Gaussian inputs `GaussianLpGradient`, `MultivariateGaussianIBP`.

`c' = min(1/C, r₀/128)/2` with `C` the count constant of the good event. If no label is
`R`-far the event is empty; otherwise `N^ε < ν = N/ℓ` and `row_core`/`col_core` with
`ν = N/ℓ`, `d = ℓ/N`, `R_c = r₀/128`, the tilt `K = κ` and the scale facts `s8_scales` give
`≤ N^{-(D+1)} + N^{-D}/2 ≤ N^{-D}` (`row_final`, `col_final`, `bound_of_exp4`, `ennreal_final`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix Real
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- Final exponent bookkeeping for the row field. -/
theorem row_final {N ℓ : ℕ} {ε c' C r₀ h K D₀ w : ℝ} (hℓ0 : 0 < (ℓ : ℝ)) (hN0 : 0 < (N : ℝ))
    (hC : 0 < C) (hr₀ : 0 < r₀) (hc' : c' = min (1 / C) (r₀ / 128) / 2)
    (hfar : (N : ℝ) ^ ε < N / ℓ) (hνh : (N / ℓ) * h ≤ 1) (hKτ : K * w ≤ 1)
    (hD₀ : (N / ℓ : ℝ) * (2 * D₀) ≤ 1) :
    Real.exp (K * w) * (N * Real.exp (-((N / ℓ : ℝ) *
        min ((N : ℝ) ^ ε * ℓ / (C * N) - h - ℓ / N) (r₀ / 128)))) /
      (Real.exp (-(c' * (N : ℝ) ^ ε)) * Real.exp (-((N / ℓ : ℝ) * (2 * D₀)))) ≤
      Real.exp 4 * (N * Real.exp (-(c' * (N : ℝ) ^ ε))) := by
  set ν : ℝ := N / ℓ with hν
  set y : ℝ := (N : ℝ) ^ ε with hy
  have hν0 : 0 < ν := div_pos hN0 hℓ0
  have hy0 : 0 ≤ y := Real.rpow_nonneg hN0.le _
  have hA : ν * (y * ℓ / (C * N) - h - ℓ / N) = y / C - ν * h - 1 := by
    simp only [hν]; field_simp
  have hmin : 2 * c' * y - 2 ≤ ν * min (y * ℓ / (C * N) - h - ℓ / N) (r₀ / 128) := by
    rw [mul_min_of_nonneg _ _ hν0.le, hA, le_min_iff]
    have hm1 : min (1 / C) (r₀ / 128) ≤ 1 / C := min_le_left _ _
    have hm2 : min (1 / C) (r₀ / 128) ≤ r₀ / 128 := min_le_right _ _
    rw [hc']
    constructor
    · have : min (1 / C) (r₀ / 128) * y ≤ y / C := by
        calc min (1 / C) (r₀ / 128) * y ≤ 1 / C * y := mul_le_mul_of_nonneg_right hm1 hy0
          _ = y / C := by ring
      nlinarith
    · have : min (1 / C) (r₀ / 128) * y ≤ r₀ / 128 * ν := by
        calc min (1 / C) (r₀ / 128) * y ≤ r₀ / 128 * y := mul_le_mul_of_nonneg_right hm2 hy0
          _ ≤ r₀ / 128 * ν := mul_le_mul_of_nonneg_left hfar.le (by positivity)
      nlinarith
  set m := ν * min (y * ℓ / (C * N) - h - ℓ / N) (r₀ / 128) with hm
  have e1 : Real.exp (-(c' * y)) * Real.exp (-(ν * (2 * D₀))) =
      Real.exp (-(c' * y + ν * (2 * D₀))) := by rw [← Real.exp_add]; ring_nf
  calc Real.exp (K * w) * (N * Real.exp (-m)) /
        (Real.exp (-(c' * y)) * Real.exp (-(ν * (2 * D₀))))
      = N * (Real.exp (K * w) * Real.exp (-m) * Real.exp (c' * y + ν * (2 * D₀))) := by
        rw [e1, div_eq_mul_inv, ← Real.exp_neg, neg_neg]; ring
    _ = N * Real.exp (K * w + -m + (c' * y + ν * (2 * D₀))) := by
        rw [Real.exp_add (K * w + -m), Real.exp_add (K * w), Real.exp_add (c' * y)]
    _ ≤ N * Real.exp (4 + -(c' * y)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hN0.le
    _ = Real.exp 4 * (N * Real.exp (-(c' * y))) := by rw [Real.exp_add]; ring

/-- Final exponent bookkeeping for the column field. -/
theorem col_final {N ℓ : ℕ} {ε c' C r₀ h K D₀ w : ℝ} (hℓ0 : 0 < (ℓ : ℝ)) (hN0 : 0 < (N : ℝ))
    (hC : 0 < C) (hr₀ : 0 < r₀) (hc' : c' = min (1 / C) (r₀ / 128) / 2)
    (hfar : (N : ℝ) ^ ε < N / ℓ) (hνh : (N / ℓ) * h ≤ 1) (hKτ : K * w ≤ 1)
    (hD₀ : (N / ℓ : ℝ) * (2 * D₀) ≤ 1) (hN1 : 1 ≤ (N : ℝ)) :
    Real.exp (K * w) * 1 /
      (Real.exp (-(c' * (N : ℝ) ^ ε)) * Real.exp ((N / ℓ : ℝ) *
        min ((N : ℝ) ^ ε * ℓ / (C * N) - h - 2 * D₀ - ℓ / N) (r₀ / 128))) ≤
      Real.exp 4 * (N * Real.exp (-(c' * (N : ℝ) ^ ε))) := by
  set ν : ℝ := N / ℓ with hν
  set y : ℝ := (N : ℝ) ^ ε with hy
  have hν0 : 0 < ν := div_pos hN0 hℓ0
  have hy0 : 0 ≤ y := Real.rpow_nonneg hN0.le _
  have hA : ν * (y * ℓ / (C * N) - h - 2 * D₀ - ℓ / N) = y / C - ν * h - ν * (2 * D₀) - 1 := by
    simp only [hν]; field_simp
  have hmin : 2 * c' * y - 3 ≤ ν * min (y * ℓ / (C * N) - h - 2 * D₀ - ℓ / N) (r₀ / 128) := by
    rw [mul_min_of_nonneg _ _ hν0.le, hA, le_min_iff]
    have hm1 : min (1 / C) (r₀ / 128) ≤ 1 / C := min_le_left _ _
    have hm2 : min (1 / C) (r₀ / 128) ≤ r₀ / 128 := min_le_right _ _
    rw [hc']
    constructor
    · have : min (1 / C) (r₀ / 128) * y ≤ y / C := by
        calc min (1 / C) (r₀ / 128) * y ≤ 1 / C * y := mul_le_mul_of_nonneg_right hm1 hy0
          _ = y / C := by ring
      nlinarith
    · have : min (1 / C) (r₀ / 128) * y ≤ r₀ / 128 * ν := by
        calc min (1 / C) (r₀ / 128) * y ≤ r₀ / 128 * y := mul_le_mul_of_nonneg_right hm2 hy0
          _ ≤ r₀ / 128 * ν := mul_le_mul_of_nonneg_left hfar.le (by positivity)
      nlinarith
  set m := ν * min (y * ℓ / (C * N) - h - 2 * D₀ - ℓ / N) (r₀ / 128) with hm
  have e1 : Real.exp (-(c' * y)) * Real.exp m = Real.exp (-(c' * y) + m) := by rw [← Real.exp_add]
  calc Real.exp (K * w) * 1 / (Real.exp (-(c' * y)) * Real.exp m)
      = Real.exp (K * w + -(-(c' * y) + m)) := by
        rw [e1, mul_one, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
    _ ≤ Real.exp (4 + -(c' * y)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 4 * Real.exp (-(c' * y)) := by rw [Real.exp_add]
    _ ≤ Real.exp 4 * (N * Real.exp (-(c' * y))) := by
        gcongr
        exact le_mul_of_one_le_left (Real.exp_pos _).le hN1

theorem ennreal_final {N : ℕ} (hN2 : (2 : ℝ) ≤ N) {D b : ℝ}
    (hb : b ≤ (N : ℝ) ^ (-D) / 2) :
    ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal b ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hpos : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have h1 : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 2 := by
    rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num) hN2) hpos.le
  calc ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal b
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal (max b 0) := by
        gcongr; exact le_max_left _ _
    _ = ENNReal.ofReal ((N : ℝ) ^ (-(D + 1)) + max b 0) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (le_max_right _ _)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
        apply ENNReal.ofReal_le_ofReal
        have : max b 0 ≤ (N : ℝ) ^ (-D) / 2 := max_le hb (by positivity)
        linarith

theorem bound_of_exp4 {N : ℕ} {D y X : ℝ} (hN0 : (0 : ℝ) < N)
    (h : 2 * Real.exp 4 * ((N : ℝ) ^ (D + 1) * Real.exp (-y)) ≤ 1)
    (hX : X ≤ Real.exp 4 * (N * Real.exp (-y))) : X ≤ (N : ℝ) ^ (-D) / 2 := by
  have hpos : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hND : (N : ℝ) ^ (D + 1) * (N : ℝ) ^ (-D) = N := by
    rw [← Real.rpow_add hN0]; simp
  refine hX.trans ?_
  have := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (-D) / 2)
  calc Real.exp 4 * (N * Real.exp (-y))
      = Real.exp 4 * Real.exp (-y) * ((N : ℝ) ^ (D + 1) * (N : ℝ) ^ (-D)) := by rw [hND]; ring
    _ = 2 * Real.exp 4 * ((N : ℝ) ^ (D + 1) * Real.exp (-y)) * ((N : ℝ) ^ (-D) / 2) := by ring
    _ ≤ 1 * ((N : ℝ) ^ (-D) / 2) := this
    _ = _ := one_mul _

/-- **The `short_row` field.** -/
theorem shortRow_holds (hIto : ∀ N, SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
        flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
            ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
              (fun j => if R < (labelDist k j : ℝ) then 1 else 0) v ∧
              Real.exp (-(c' * (N : ℝ) ^ ε)) < v u k} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro A c r₀ s₀ v₀ hK ε hε
  have hc0 : 0 < c := hK.1
  have hr₀ : 0 < r₀ := hK.2.2.1
  obtain ⟨c₁, C₁, C, b₀, hc₁, hC₁, hC, hb₀, hD⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  set c' := min (1 / C) (r₀ / 128) / 2 with hc'
  have hc'0 : 0 < c' := by
    have : 0 < min (1 / C) (r₀ / 128) := lt_min (by positivity) (by positivity)
    positivity
  refine ⟨c', hc'0, fun D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hD (D + 1)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (s8_scales (C₁ := C₁) hr₀ hc0 hC hc₁ hε hc'0 D)
  refine ⟨max N₁ N₂, fun N hN F E hFC => ?_⟩
  intro a ℓ R s u has hsu huc k
  obtain ⟨hℓ1, hℓN, haτ, hκτ, hν2C, hνh, hν1, hνN, hexpD, hN2⟩ := hN₂ N (le_of_max_le_right hN)
  have hℓ1 : (1 : ℝ) ≤ ℓ := hℓ1
  have hℓN : (ℓ : ℝ) / N ≤ r₀ / 64 := hℓN
  have hκτ : kappaConst (r₀ / 128) c₁ C₁ * ((N : ℝ) / ℓ) * (1 + Real.log N) *
      (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 := hκτ
  have hν2C : ((N : ℝ) / ℓ) * (2 * (C * Real.sqrt ((N : ℝ) ^ (-(1 / 100 : ℝ))))) ≤ 1 := hν2C
  have hνh : ((N : ℝ) / ℓ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 := hνh
  have hν1 : 1 ≤ (N : ℝ) / ℓ := hν1
  have hνN : (N : ℝ) / ℓ ≤ N := hνN
  have ha0 : 0 < a := haτ
  have hF : F.IsHermitian := hFC.1
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hℓ1' : 1 ≤ ℓ := by exact_mod_cast hℓ1
  set τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hτ
  set ν : ℝ := (N : ℝ) / ℓ with hν
  have hνd : ν * (ℓ / N) = 1 := by simp only [hν]; field_simp
  set K := rowKappa N ℓ ν (ℓ / N) (r₀ / 128) c₁ C₁ with hKdef
  have hKle := rowKappa_le (by linarith : (1 : ℝ) ≤ N) (by positivity : (0 : ℝ) < r₀ / 128) hc₁ hC₁
    hν1 hνN hνd hνd (ℓ := ℓ)
  have hK0 : 0 ≤ K := by
    have := weightConst_pos
    simp only [hKdef, rowKappa, abs_of_pos (lt_of_lt_of_le one_pos hν1)]
    have hlog := Real.log_nonneg (by linarith : (1 : ℝ) ≤ N)
    have hd0 : (0 : ℝ) < ℓ / N := by positivity
    positivity
  have hus : u - s ≤ τ := by
    have : a = c - τ := rfl
    linarith
  have hKτ : K * (u - s) ≤ 1 := by
    calc K * (u - s) ≤ K * τ := mul_le_mul_of_nonneg_left hus hK0
      _ ≤ kappaConst (r₀ / 128) c₁ C₁ * ν * (1 + Real.log N) * τ :=
          mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hN0.le _)
      _ ≤ 1 := hκτ
  by_cases hfar : ∃ j : Fin N, R < (labelDist k j : ℝ)
  · obtain ⟨j, hj⟩ := hfar
    have hfarν : (N : ℝ) ^ ε < ν := by
      have hd : (labelDist k j : ℝ) < N := by exact_mod_cast labelDist_lt k j
      have : (N : ℝ) ^ ε * ℓ < N := lt_trans hj hd
      rw [hν, lt_div_iff₀ hℓ0]; exact this
    have hcore := row_core (hIto N) hStop (hDBM N) hF (a := a) (cT := c) (E := E) ha0 hr₀ hℓ1'
      (c₁ := c₁) (C₁ := C₁) (C := C) (b₀ := b₀) (h := τ) (D₀ := C * Real.sqrt τ) hc₁ hC₁ hC
      has hsu huc k (R := R) (ν := ν) (d := ℓ / N) (Rc := r₀ / 128) (K := K)
      (th := Real.exp (-(c' * (N : ℝ) ^ ε))) (by linarith) (by positivity) (by positivity)
      (by linarith) hK0 le_rfl (Real.exp_pos _)
    refine hcore.trans ?_
    have hB₁ : flowLaw N a {ω | ¬ ∀ σ ∈ Set.Icc a c,
        goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ τ (C * Real.sqrt τ) σ} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := hN₁ N (le_of_max_le_left hN) F E hFC
    have hbnd := row_final (N := N) (ℓ := ℓ) (ε := ε) (c' := c') (C := C) (r₀ := r₀) (h := τ)
      (K := K) (D₀ := C * Real.sqrt τ) (w := u - s) hℓ0 hN0 hC hr₀ hc' hfarν hνh hKτ hν2C
    have hR' : R = (N : ℝ) ^ ε * ℓ := rfl
    rw [hR']
    calc _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + _ := by gcongr
      _ ≤ _ := ennreal_final hN2 (bound_of_exp4 hN0 hexpD hbnd)
  · push Not at hfar
    have hempty : {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
        ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
          (fun j => if R < (labelDist k j : ℝ) then 1 else 0) v ∧
          Real.exp (-(c' * (N : ℝ) ^ ε)) < v u k} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
      intro _ v hv hlt
      have hzero : (fun j : Fin N => if R < (labelDist k j : ℝ) then (1 : ℝ) else 0) =
          fun _ => 0 := funext fun j => by simp [not_lt.mpr (hfar j)]
      rw [hzero] at hv
      have := forwardMass_le_const (shortGenerator_isSubGenerator F a ω ℓ s u) hv le_rfl
        (fun _ => le_rfl) u ⟨hsu, le_rfl⟩ k
      linarith [Real.exp_pos (-(c' * (N : ℝ) ^ ε))]
    rw [hempty, measure_empty]; exact bot_le

/-- **The `short_column` field.** -/
theorem shortColumn_holds (hIto : ∀ N, SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP) :
    ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
        flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
            ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
              (fun j => if j = k then 1 else 0) v ∧
              Real.exp (-(c' * (N : ℝ) ^ ε)) <
                ∑ j : Fin N, (if R < (labelDist k j : ℝ) then 1 else 0) * v u j} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro A c r₀ s₀ v₀ hK ε hε
  have hc0 : 0 < c := hK.1
  have hr₀ : 0 < r₀ := hK.2.2.1
  obtain ⟨c₁, C₁, C, b₀, hc₁, hC₁, hC, hb₀, hD⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  set c' := min (1 / C) (r₀ / 128) / 2 with hc'
  have hc'0 : 0 < c' := by
    have : 0 < min (1 / C) (r₀ / 128) := lt_min (by positivity) (by positivity)
    positivity
  refine ⟨c', hc'0, fun D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hD (D + 1)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (s8_scales (C₁ := C₁) hr₀ hc0 hC hc₁ hε hc'0 D)
  refine ⟨max N₁ N₂, fun N hN F E hFC => ?_⟩
  intro a ℓ R s u has hsu huc k
  obtain ⟨hℓ1, hℓN, haτ, hκτ, hν2C, hνh, hν1, hνN, hexpD, hN2⟩ := hN₂ N (le_of_max_le_right hN)
  have hℓ1 : (1 : ℝ) ≤ ℓ := hℓ1
  have hℓN : (ℓ : ℝ) / N ≤ r₀ / 64 := hℓN
  have hκτ : kappaConst (r₀ / 128) c₁ C₁ * ((N : ℝ) / ℓ) * (1 + Real.log N) *
      (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 := hκτ
  have hν2C : ((N : ℝ) / ℓ) * (2 * (C * Real.sqrt ((N : ℝ) ^ (-(1 / 100 : ℝ))))) ≤ 1 := hν2C
  have hνh : ((N : ℝ) / ℓ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 := hνh
  have hν1 : 1 ≤ (N : ℝ) / ℓ := hν1
  have hνN : (N : ℝ) / ℓ ≤ N := hνN
  have ha0 : 0 < a := haτ
  have hF : F.IsHermitian := hFC.1
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hℓ1' : 1 ≤ ℓ := by exact_mod_cast hℓ1
  set τ : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hτ
  set ν : ℝ := (N : ℝ) / ℓ with hν
  have hνd : ν * (ℓ / N) = 1 := by simp only [hν]; field_simp
  set K := rowKappa N ℓ ν (ℓ / N) (r₀ / 128) c₁ C₁ with hKdef
  have hKle := rowKappa_le (by linarith : (1 : ℝ) ≤ N) (by positivity : (0 : ℝ) < r₀ / 128) hc₁ hC₁
    hν1 hνN hνd hνd (ℓ := ℓ)
  have hK0 : 0 ≤ K := by
    have := weightConst_pos
    simp only [hKdef, rowKappa, abs_of_pos (lt_of_lt_of_le one_pos hν1)]
    have hlog := Real.log_nonneg (by linarith : (1 : ℝ) ≤ N)
    have hd0 : (0 : ℝ) < ℓ / N := by positivity
    positivity
  have hus : u - s ≤ τ := by
    have : a = c - τ := rfl
    linarith
  have hKτ : K * (u - s) ≤ 1 := by
    calc K * (u - s) ≤ K * τ := mul_le_mul_of_nonneg_left hus hK0
      _ ≤ kappaConst (r₀ / 128) c₁ C₁ * ν * (1 + Real.log N) * τ :=
          mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hN0.le _)
      _ ≤ 1 := hκτ
  by_cases hfar : ∃ j : Fin N, R < (labelDist k j : ℝ)
  · obtain ⟨j, hj⟩ := hfar
    have hfarν : (N : ℝ) ^ ε < ν := by
      have hd : (labelDist k j : ℝ) < N := by exact_mod_cast labelDist_lt k j
      have : (N : ℝ) ^ ε * ℓ < N := lt_trans hj hd
      rw [hν, lt_div_iff₀ hℓ0]; exact this
    have hcore := col_core (hIto N) hStop (hDBM N) hF (a := a) (cT := c) (E := E) ha0 hr₀ hℓ1'
      (c₁ := c₁) (C₁ := C₁) (C := C) (b₀ := b₀) (h := τ) (D₀ := C * Real.sqrt τ) hc₁ hC₁ hC
      has hsu huc k (R := R) (ν := ν) (d := ℓ / N) (Rc := r₀ / 128) (K := K)
      (th := Real.exp (-(c' * (N : ℝ) ^ ε))) (by linarith) (by positivity) (by positivity)
      (by linarith) hK0 le_rfl (Real.exp_pos _)
    refine hcore.trans ?_
    have hB₁ : flowLaw N a {ω | ¬ ∀ σ ∈ Set.Icc a c,
        goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ τ (C * Real.sqrt τ) σ} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := hN₁ N (le_of_max_le_left hN) F E hFC
    have hbnd := col_final (N := N) (ℓ := ℓ) (ε := ε) (c' := c') (C := C) (r₀ := r₀) (h := τ)
      (K := K) (D₀ := C * Real.sqrt τ) (w := u - s) hℓ0 hN0 hC hr₀ hc' hfarν hνh hKτ hν2C
      (by linarith)
    have hR' : R = (N : ℝ) ^ ε * ℓ := rfl
    rw [hR']
    calc _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + _ := by gcongr
      _ ≤ _ := ennreal_final hN2 (bound_of_exp4 hN0 hexpD hbnd)
  · push Not at hfar
    have hempty : {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
        ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
          (fun j => if j = k then 1 else 0) v ∧
          Real.exp (-(c' * (N : ℝ) ^ ε)) <
            ∑ j : Fin N, (if R < (labelDist k j : ℝ) then 1 else 0) * v u j} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
      intro _ v _ hlt
      have hzero : (∑ j : Fin N, (if R < (labelDist k j : ℝ) then (1 : ℝ) else 0) * v u j) = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [not_lt.mpr (hfar j)]
      rw [hzero] at hlt
      linarith [Real.exp_pos (-(c' * (N : ℝ) ^ ε))]
    rw [hempty, measure_empty]; exact bot_le

end BlockBand.Palm.RelativeLocalization
