module

public import BlockBand.Critical.MatrixClosing.MiddleShift.Bound
public import BlockBand.Critical.MatrixClosing.Reduction

/-!
# The middle-only shifted collar mean from the exact boundary mean

* `middle_error_arith`, `StrictMiddleClause`, `mem_bulkInterval_half`, `bulkInterval_mono_half`.
* `strictMiddle_of_exactBoundaryMean`: the strict (`Y ≻ 0`) clause, explicit constants.
* `middleKernel_radial`: `𝒫(tU_s𝔯(X)) = 𝒫(U_s𝔯(X_t))`, `X_t = radialOld b e t X`.
* **`middleShiftBoundaryMean_of_exactBoundaryMean : ExactBoundaryMeanContract →
  MiddleShiftBoundaryMeanStatement`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Scalar bookkeeping for `middleKernel_mean_le`. -/
theorem middle_error_arith {η η' Δn s err' ηmin LΔ Lz : ℝ} (hηmin : 0 < ηmin) (hη : ηmin ≤ η)
    (hη' : ηmin ≤ η') (hη'3 : η' ≤ 3) (hΔ0 : 0 ≤ Δn) (hΔ : Δn ≤ LΔ * |s|)
    (hdη : |η' - η| ≤ Lz * |s|) (hs1 : |s| ≤ 1) (herr : 0 ≤ err') (hLΔ : 0 ≤ LΔ) :
    η⁻¹ * (Δn * (η' * (1 + err') + bcConst η' err') + Δn ^ 2 * bcConst η' err' + η' * err' +
        |η' - η|) ≤
      ηmin⁻¹ * ((LΔ * (3 + 5 / (2 * ηmin)) + LΔ ^ 2 * (5 / (2 * ηmin)) + Lz) * |s| +
        (LΔ * (3 + 2 / ηmin) + LΔ ^ 2 * (2 / ηmin) + 3) * err') := by
  have hηpos : 0 < η := hηmin.trans_le hη
  have hη'pos : 0 < η' := hηmin.trans_le hη'
  have hs0 := abs_nonneg s
  set B0 := 5 / (2 * ηmin)
  set B1 := 2 / ηmin
  have hBc : bcConst η' err' ≤ B0 + B1 * err' := by
    have e1 : bcConst η' err' = 1 / (2 * η') + 2 * (1 + err') / η' := by
      unfold bcConst; field_simp; ring
    rw [e1]
    have h1 : 1 / (2 * η') ≤ 1 / (2 * ηmin) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    have h2 : 2 * (1 + err') / η' ≤ 2 * (1 + err') / ηmin :=
      div_le_div_of_nonneg_left (by positivity) hηmin hη'
    have h3 : 1 / (2 * ηmin) + 2 * (1 + err') / ηmin = B0 + B1 * err' := by
      simp only [B0, B1]; field_simp; ring
    linarith
  have hBc0 : 0 ≤ bcConst η' err' := by unfold bcConst; positivity
  have hΔ1 : Δn ≤ LΔ := hΔ.trans (by nlinarith)
  have t1 : Δn * (η' * (1 + err') + bcConst η' err') ≤
      LΔ * (3 + B0) * |s| + LΔ * (3 + B1) * err' := by
    have : η' * (1 + err') + bcConst η' err' ≤ (3 + B0) + (3 + B1) * err' := by
      have := mul_le_mul_of_nonneg_right hη'3 (by linarith : (0 : ℝ) ≤ 1 + err')
      linarith
    have hB0 : 0 ≤ B0 := by positivity
    have hB1 : 0 ≤ B1 := by positivity
    calc Δn * (η' * (1 + err') + bcConst η' err') ≤ LΔ * |s| * ((3 + B0) + (3 + B1) * err') :=
          mul_le_mul hΔ this (by positivity) (by positivity)
      _ = LΔ * (3 + B0) * |s| + LΔ * (3 + B1) * err' * |s| := by ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ LΔ * (3 + B1) * err')
          linarith
  have t2 : Δn ^ 2 * bcConst η' err' ≤ LΔ ^ 2 * B0 * |s| + LΔ ^ 2 * B1 * err' := by
    have hsq : Δn ^ 2 ≤ LΔ ^ 2 * |s| := by
      have : Δn ^ 2 ≤ (LΔ * |s|) * LΔ := by rw [sq]; exact mul_le_mul hΔ hΔ1 hΔ0 (by positivity)
      nlinarith
    have hB0 : 0 ≤ B0 := by positivity
    have hB1 : 0 ≤ B1 := by positivity
    calc Δn ^ 2 * bcConst η' err' ≤ (LΔ ^ 2 * |s|) * (B0 + B1 * err') :=
          mul_le_mul hsq hBc hBc0 (by positivity)
      _ = LΔ ^ 2 * B0 * |s| + LΔ ^ 2 * B1 * err' * |s| := by ring
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ LΔ ^ 2 * B1 * err')
          linarith
  have t3 : η' * err' ≤ 3 * err' := mul_le_mul_of_nonneg_right hη'3 herr
  have hin : 0 ≤ Δn * (η' * (1 + err') + bcConst η' err') + Δn ^ 2 * bcConst η' err' +
      η' * err' + |η' - η| := by positivity
  calc η⁻¹ * (Δn * (η' * (1 + err') + bcConst η' err') + Δn ^ 2 * bcConst η' err' + η' * err' +
        |η' - η|) ≤ ηmin⁻¹ * (Δn * (η' * (1 + err') + bcConst η' err') +
          Δn ^ 2 * bcConst η' err' + η' * err' + |η' - η|) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hηmin hη) hin
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hηmin.le)
        nlinarith

/-- The strict (`Y ≻ 0`) clause of `MiddleShiftBoundaryMeanStatement` with explicit constants and
regime `d(X) ≤ d₂`. -/
def StrictMiddleClause (b κ : ℝ) (ε : ℕ → ℝ) (C d₂ s₀ : ℝ) (W₀ : ℕ) : Prop :=
  ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-imPart X).PosDef →
      matchedDistance b e X ≤ d₂ →
        MiddleKernelIntegrable b e s 1 X ∧
          ‖expectedMiddleKernel b e s 1 X - 1‖ ≤ middleMeanError b e s ε C X

theorem mem_bulkInterval_half {κ e s : ℝ} (he : e ∈ bulkInterval κ) (hs : |s| ≤ κ / 2) :
    e + s ∈ bulkInterval (κ / 2) := by
  have h1 := he.1; have h2 := he.2
  have := abs_le.1 hs
  constructor <;> linarith

theorem bulkInterval_mono_half {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) :
    e ∈ bulkInterval (κ / 2) := by
  have h1 := he.1; have h2 := he.2
  constructor <;> linarith

/-- **Strict middle-shift clause from `ExactBoundaryMeanContract`.** -/
theorem strictMiddle_of_exactBoundaryMean (hEB : ExactBoundaryMeanContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 2) :
    ∃ (ε : ℕ → ℝ) (C d₂ s₀ : ℝ) (W₀ : ℕ), Tendsto ε atTop (𝓝 0) ∧ 0 < d₂ ∧ 0 < s₀ ∧ 0 ≤ C ∧
      (∀ W, 0 ≤ ε W) ∧ StrictMiddleClause b κ ε C d₂ s₀ W₀ := by
  set κ' := κ / 2 with hκ'def
  have hκ' : 0 < κ' := half_pos hκ
  obtain ⟨ε, C, d₁, W₀, hε, hd₁, hEB'⟩ := hEB b hb0 hb κ' hκ'
  have hm : 0 < 4 - (2 - κ') ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ' (by linarith)
  obtain ⟨m, hmdef⟩ : ∃ m, m = Real.sqrt (4 - (2 - κ') ^ 2) := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hmdef]; exact Real.sqrt_pos.2 hm
  obtain ⟨ηmin, hηmindef⟩ : ∃ x, x = (1 - b) * m / 2 := ⟨_, rfl⟩
  have hηmin : 0 < ηmin := by
    have : 0 < 1 - b := by linarith
    rw [hηmindef]; positivity
  obtain ⟨La, hLadef⟩ : ∃ x, x = 1 / 2 + 1 / m := ⟨_, rfl⟩
  obtain ⟨Lz, hLzdef⟩ : ∃ x, x = 1 + (1 - b) * La := ⟨_, rfl⟩
  obtain ⟨LΔ, hLΔdef⟩ : ∃ x, x = Lz + 1 := ⟨_, rfl⟩
  obtain ⟨Ld, hLddef⟩ : ∃ x, x = LΔ * (ηmin ^ 2)⁻¹ + La := ⟨_, rfl⟩
  obtain ⟨Kg, hKgdef⟩ : ∃ x, x = 3 / ηmin * (2 + 2 * LΔ ^ 2 / ηmin ^ 2) := ⟨_, rfl⟩
  have hLa : 0 ≤ La := by rw [hLadef]; positivity
  have hLz : 0 ≤ Lz := by
    have : 0 ≤ 1 - b := by linarith
    rw [hLzdef]; positivity
  have hLΔ : 0 ≤ LΔ := by rw [hLΔdef]; positivity
  have hLd : 0 < Ld := by
    rw [hLddef]
    have : 0 < LΔ := by rw [hLΔdef]; linarith
    positivity
  have hKg : 0 ≤ Kg := by rw [hKgdef]; positivity
  obtain ⟨As, hAsdef⟩ : ∃ x, x = LΔ * (3 + 5 / (2 * ηmin)) + LΔ ^ 2 * (5 / (2 * ηmin)) + Lz :=
    ⟨_, rfl⟩
  obtain ⟨Ae, hAedef⟩ : ∃ x, x = LΔ * (3 + 2 / ηmin) + LΔ ^ 2 * (2 / ηmin) + 3 := ⟨_, rfl⟩
  have hAs : 0 ≤ As := by rw [hAsdef]; positivity
  have hAe : 0 ≤ Ae := by rw [hAedef]; positivity
  obtain ⟨Cf, hCfdef⟩ : ∃ x, x = ηmin⁻¹ * (As + Ae * (|C| * (1 + Ld + Kg))) := ⟨_, rfl⟩
  have hCf : 0 ≤ Cf := by rw [hCfdef]; positivity
  obtain ⟨s₀, hs₀def⟩ : ∃ x, x = min 1 (min κ' (d₁ / (2 * Ld))) := ⟨_, rfl⟩
  have hs₀ : 0 < s₀ := by rw [hs₀def]; exact lt_min one_pos (lt_min hκ' (by positivity))
  refine ⟨fun W => |ε W|, Cf, d₁ / 2, s₀, W₀, ?_, by linarith, hs₀, hCf, fun W => abs_nonneg _, ?_⟩
  · have := hε.abs; simpa using this
  intro W hW hW₀ e he s hs X hY hd
  have hs' : |s| ≤ s₀ := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
  have hs1 : |s| ≤ 1 := hs'.trans (by rw [hs₀def]; exact min_le_left _ _)
  have hsκ : |s| ≤ κ' := hs'.trans (by rw [hs₀def]; exact (min_le_right _ _).trans (min_le_left _ _))
  have hsd : |s| ≤ d₁ / (2 * Ld) :=
    hs'.trans (by rw [hs₀def]; exact (min_le_right _ _).trans (min_le_right _ _))
  have he' : e ∈ bulkInterval κ' := bulkInterval_mono_half hκ he
  have hes : e + s ∈ bulkInterval κ' := mem_bulkInterval_half he hsκ
  have hηe : ηmin ≤ (boundaryZ b e).im := by
    obtain ⟨-, h⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith)
      hκ' he'
    rw [hηmindef, hmdef]; exact h
  have hηes : ηmin ≤ (boundaryZ b (e + s)).im := by
    obtain ⟨-, h⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith)
      hκ' hes
    rw [hηmindef, hmdef]; exact h
  set η := (boundaryZ b e).im
  set η' := (boundaryZ b (e + s)).im
  have hη : 0 < η := hηmin.trans_le hηe
  have hη' : 0 < η' := hηmin.trans_le hηes
  have hη'3 : η' ≤ 3 := by
    have h1 := Complex.abs_im_le_norm (boundaryZ b (e + s))
    have h2 := BlockBand.Layers.norm_boundaryZ_le (b := b) hb0.le (by linarith)
      ((BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ' hes).le)
    exact (le_abs_self _).trans (h1.trans h2)
  have hz : ‖boundaryZ b (e + s) - boundaryZ b e‖ ≤ Lz * |s| := by
    have := Collar.Density.norm_boundaryZ_sub_le (b := b) (by linarith) hκ' hes he'
    rw [add_sub_cancel_left] at this
    rw [hLzdef, hLadef, hmdef]; exact this
  have hΔ : ‖shiftDefect b e s‖ ≤ LΔ * |s| := by
    have : shiftDefect b e s = (boundaryZ b (e + s) - boundaryZ b e) + (s : ℂ) := by
      unfold shiftDefect; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hLΔdef]; linarith
  have hdη : |η' - η| ≤ Lz * |s| := by
    have : η' - η = (boundaryZ b (e + s) - boundaryZ b e).im := by simp [η, η']
    rw [this]; exact (Complex.abs_im_le_norm _).trans hz
  have ha : ‖matchedA (e + s) - matchedA e‖ ≤ La * |s| := by
    have := Collar.Density.norm_matchedA_sub_le hκ' hes he'
    rw [add_sub_cancel_left] at this
    rw [hLadef, hmdef]; exact this
  have hYs := hY.posSemidef
  have hd' : matchedDistance b (e + s) (X - (s : ℂ) • 1) ≤ matchedDistance b e X + Ld * |s| := by
    have h := matchedDistance_shift_le hW hη hη' hYs
    have h1 : ‖shiftDefect b e s‖ * (η' * η)⁻¹ ≤ LΔ * |s| * (ηmin ^ 2)⁻¹ := by
      refine mul_le_mul hΔ ?_ (by positivity) (by positivity)
      apply inv_anti₀ (by positivity)
      rw [sq]; exact mul_le_mul hηes hηe hηmin.le hη'.le
    have e1 : LΔ * |s| * (ηmin ^ 2)⁻¹ + La * |s| = Ld * |s| := by rw [hLddef]; ring
    linarith
  have hd1 : matchedDistance b (e + s) (X - (s : ℂ) • 1) ≤ d₁ := by
    have : Ld * |s| ≤ d₁ / 2 :=
      calc Ld * |s| ≤ Ld * (d₁ / (2 * Ld)) := mul_le_mul_of_nonneg_left hsd hLd.le
        _ = d₁ / 2 := by field_simp
    linarith
  have hg0 := Collar.Kernel.conductance_oldScattering_nonneg b e hη hYs
  have hg' : conductance (oldScattering b (e + s) (X - (s : ℂ) • 1)) ≤
      Kg * conductance (oldScattering b e X) := by
    refine (conductance_shift_le hη hη' hYs).trans (mul_le_mul_of_nonneg_right ?_ hg0)
    have hΔ1 : ‖shiftDefect b e s‖ ≤ LΔ := hΔ.trans (mul_le_of_le_one_right hLΔ hs1)
    have h1 : η' / η ≤ 3 / ηmin := div_le_div₀ (by norm_num) hη'3 hηmin hηe
    have h2 : 2 + 2 * ‖shiftDefect b e s‖ ^ 2 / η' ^ 2 ≤ 2 + 2 * LΔ ^ 2 / ηmin ^ 2 := by
      have : ‖shiftDefect b e s‖ ^ 2 ≤ LΔ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΔ1 2
      have h3 : 2 * ‖shiftDefect b e s‖ ^ 2 / η' ^ 2 ≤ 2 * LΔ ^ 2 / ηmin ^ 2 :=
        div_le_div₀ (by positivity) (by linarith) (by positivity) (pow_le_pow_left₀ hηmin.le hηes 2)
      linarith
    rw [hKgdef]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hY' : (-imPart (X - (s : ℂ) • 1)).PosDef := by rwa [imPart_sub_smul_one]
  obtain ⟨hint', hnorm'⟩ := (hEB' W hW hW₀ (e + s) hes (X - (s : ℂ) • 1) hd1).1 hY'
  set w8 := (W : ℝ) ^ (-(1 : ℝ) / 8)
  set w4 := (W : ℝ) ^ (-(1 : ℝ) / 4)
  have hw8 : 0 ≤ w8 := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw4 : 0 ≤ w4 := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set g := conductance (oldScattering b e X)
  set dX := matchedDistance b e X
  have hdX : 0 ≤ dX := le_max_of_le_left (norm_nonneg _)
  set err' := |C| * (dX + Ld * |s| + |ε W| + w8 + Kg * g * w4)
  have herr0 : 0 ≤ err' := by positivity
  have herr' : ‖expectedCollarKernel b (e + s) 0 0 1 (X - (s : ℂ) • 1) - 1‖ ≤ err' := by
    refine hnorm'.trans ?_
    set g' := conductance (oldScattering b (e + s) (X - (s : ℂ) • 1))
    set d' := matchedDistance b (e + s) (X - (s : ℂ) • 1)
    have hg'0 : 0 ≤ g' := Collar.Kernel.conductance_oldScattering_nonneg b (e + s) hη'
      (by rw [imPart_sub_smul_one]; exact hYs)
    have hd'0 : 0 ≤ d' := le_max_of_le_left (norm_nonneg _)
    have hx : |d' + ε W + w8 + g' * w4| ≤ dX + Ld * |s| + |ε W| + w8 + Kg * g * w4 := by
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add ?_ le_rfl)) ?_)) ?_
      · rw [abs_of_nonneg hd'0]; exact hd'
      · rw [abs_of_nonneg hw8]
      · rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right hg' hw4
    calc C * (d' + ε W + w8 + g' * w4) ≤ |C| * |d' + ε W + w8 + g' * w4| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ err' := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  obtain ⟨hint, hnorm⟩ := middleKernel_mean_le e s hη hη' hY hint' herr'
  refine ⟨hint, hnorm.trans ?_⟩
  have harith := middle_error_arith hηmin hηe hηes hη'3 (norm_nonneg _) hΔ hdη hs1 herr0 hLΔ
  rw [← hAsdef, ← hAedef] at harith
  refine harith.trans ?_
  unfold middleMeanError
  set S := dX + |ε W| + w8 + g * w4 + |s|
  have hS : 0 ≤ S := by positivity
  have hgw : 0 ≤ g * w4 := mul_nonneg hg0 hw4
  have hsS : |s| ≤ S := by
    have := abs_nonneg (ε W)
    simp only [S]; linarith
  have hgS : g * w4 ≤ S := by
    have := abs_nonneg (ε W)
    have := abs_nonneg s
    simp only [S]; linarith
  have hS1 : dX + |ε W| + w8 ≤ S := by
    have := abs_nonneg s
    simp only [S]; linarith
  have herrS : err' ≤ |C| * (1 + Ld + Kg) * S := by
    have h1 : Ld * |s| ≤ Ld * S := mul_le_mul_of_nonneg_left hsS hLd.le
    have h2 : Kg * (g * w4) ≤ Kg * S := mul_le_mul_of_nonneg_left hgS hKg
    have e1 : (1 + Ld + Kg) * S = S + Ld * S + Kg * S := by ring
    have e2 : Kg * g * w4 = Kg * (g * w4) := by ring
    have : dX + Ld * |s| + |ε W| + w8 + Kg * g * w4 ≤ (1 + Ld + Kg) * S := by
      rw [e1, e2]; linarith
    calc err' ≤ |C| * ((1 + Ld + Kg) * S) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  calc ηmin⁻¹ * (As * |s| + Ae * err') ≤ ηmin⁻¹ * (As * S + Ae * (|C| * (1 + Ld + Kg) * S)) := by
        gcongr
    _ = Cf * S := by rw [hCfdef]; ring

/-!
## Removing the radial regulator
-/

theorem middleKernel_radial (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosSemidef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ω : CollarSample W) :
    middleKernel b e s t X ω = middleKernel b e s 1 (Collar.Kernel.radialOld b e t X) ω := by
  rw [middleKernel, middleKernel, Collar.Kernel.oldScattering_radialOld b e hη hY ht0 ht1,
    Matrix.mul_smul, Complex.ofReal_one, one_smul]

/-- **The middle-only shifted collar mean, from `ExactBoundaryMeanContract`.**
`ExactBoundaryMeanContract → MiddleShiftBoundaryMeanStatement` (strict clause by the reference
change `(e, X) ↦ (e+s, X - s)` and the kernel comparison `middleKernel_mean_le`; boundary clause by
the radial regulator, as in `BoundaryMean.exactBoundaryMean_of_strict`).
-/
theorem middleShiftBoundaryMean_of_exactBoundaryMean (hEB : ExactBoundaryMeanContract) :
    MiddleShiftBoundaryMeanStatement := by
  intro b hb0 hb κ hκ
  by_cases hκ2 : κ ≤ 2
  swap
  · refine ⟨fun _ => 0, 0, 1, 1, 0, tendsto_const_nhds, one_pos, one_pos, ?_⟩
    intro W _ _ e he
    have h1 := he.1; have h2 := he.2
    exact absurd (h1.trans h2) (by linarith)
  obtain ⟨ε, C, d₂, s₀, W₀, hε, hd₂, hs₀, hC, hε0, hS⟩ :=
    strictMiddle_of_exactBoundaryMean hEB hb0 hb hκ hκ2
  refine ⟨ε, C, d₂ / 2, s₀, W₀, hε, by linarith, hs₀, ?_⟩
  intro W hW hW₀ e he s hs X hdX
  have hη : 0 < (boundaryZ b e).im := boundaryZ_im_pos hb hκ he
  refine ⟨fun hY => hS W hW hW₀ e he s hs X hY (by linarith), fun hY δ hδ => ?_⟩
  set η := (boundaryZ b e).im with hηdef
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set w4 : ℝ := (W : ℝ) ^ (-(1 : ℝ) / 4)
  have hw4 : 0 ≤ w4 := Real.rpow_nonneg hWr.le _
  set A : ℝ := C * (1 / (2 * η) + 4 * W * w4)
  have hA : 0 ≤ A := by positivity
  set u : ℝ := min (d₂ * η) (δ / (A + 1))
  have hu : 0 < u := lt_min (by positivity) (by positivity)
  refine ⟨max (1 - u) 0, max_lt (by linarith) one_pos, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht.1.le
  have htu : 1 - t < u := by
    have := (le_max_left (1 - u) 0).trans_lt ht.1
    linarith
  have ht1 := ht.2
  set X' := Collar.Kernel.radialOld b e t X
  have hY' := Collar.Kernel.posDef_neg_imPart_radialOld b e hη hY ht0 ht1
  have hd' := Collar.Kernel.matchedDistance_radialOld_le b e hη hW hY ht0 ht1
  have h1t : (1 - t) / (2 * η) ≤ d₂ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : u ≤ d₂ * η := min_le_left _ _
    nlinarith
  have hd'' : matchedDistance b e X' ≤ d₂ := by linarith
  obtain ⟨hint, hnorm⟩ := hS W hW hW₀ e he s hs X' hY' hd''
  have hfun : middleKernel b e s t X = middleKernel b e s 1 X' :=
    funext fun ω => middleKernel_radial b e s hη hY ht0 ht1 ω
  refine ⟨fun x y => by rw [hfun]; exact hint x y, ?_⟩
  rw [show expectedMiddleKernel b e s t X = expectedMiddleKernel b e s 1 X' by
    unfold expectedMiddleKernel; rw [hfun]]
  refine hnorm.trans ?_
  have hg := Collar.Kernel.conductance_oldScattering_nonneg b e hη hY
  have hg' : conductance (oldScattering b e X') ≤
      conductance (oldScattering b e X) + 2 * W * (1 - t ^ 2) := by
    rw [Collar.Kernel.oldScattering_radialOld b e hη hY ht0 ht1]
    exact Collar.Kernel.conductance_radial_le _ (by nlinarith) hg
  have hAu : A * (1 - t) ≤ δ := by
    have h1 : A * (1 - t) ≤ A * u := mul_le_mul_of_nonneg_left htu.le hA
    have h2 : u ≤ δ / (A + 1) := min_le_right _ _
    have h3 : A * u ≤ A * (δ / (A + 1)) := mul_le_mul_of_nonneg_left h2 hA
    have h4 : A * (δ / (A + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hsq : 1 - t ^ 2 ≤ 2 * (1 - t) := by nlinarith
  unfold middleMeanError
  show _ ≤ C * (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
    conductance (oldScattering b e X) * w4 + |s|) + δ
  have key : matchedDistance b e X' + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
      conductance (oldScattering b e X') * w4 + |s| ≤
      (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X) * w4 + |s|) +
        (1 - t) * (1 / (2 * η) + 4 * W * w4) := by
    have e1 : conductance (oldScattering b e X') * w4 ≤
        (conductance (oldScattering b e X) + 2 * W * (1 - t ^ 2)) * w4 :=
      mul_le_mul_of_nonneg_right hg' hw4
    have e2 : 2 * W * (1 - t ^ 2) * w4 ≤ 2 * W * (2 * (1 - t)) * w4 := by
      have : 0 ≤ 2 * (W : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq this) hw4
    have e3 : (1 - t) / (2 * η) = (1 - t) * (1 / (2 * η)) := by ring
    nlinarith
  calc C * (matchedDistance b e X' + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X') * w4 + |s|)
      ≤ C * ((matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X) * w4 + |s|) + (1 - t) * (1 / (2 * η) + 4 * W * w4)) :=
        mul_le_mul_of_nonneg_left key hC
    _ = C * (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
        conductance (oldScattering b e X) * w4 + |s|) + A * (1 - t) := by ring
    _ ≤ _ := by linarith

end BlockBand.Critical.MatrixClosing
