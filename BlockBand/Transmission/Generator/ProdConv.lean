module

public import BlockBand.Transmission.Generator.ProdShapes
public import BlockBand.Transmission.Generator.ProdExpand

/-!
# Convergence of the expanded finite-`W` tested product (finite side)

`finTest`/`limTest`: `E[Φ(past) H(P at pt)]` at width `W` and on the limit.
**`prod_conv hLU`**: along the fdd subsequence, the expansion `prod_expand` of
`E_n[Φ(M^W_kM^W_l - ΣB/W)]` converges to
`limTest hYY - ∫_s^t limTest(hYA, k, l) - ∫_s^t limTest(hYA, l, k) + ∫_s^t∫_s^t limTest(hAA)
- ∫_s^t limTest(hBr)`: each single sum is a Riemann sum (`riemann_point`, from `poly_point`), the
double sum is a Riemann sum of Riemann sums (two `riemann_tendsto`; the inner cells are bounded
via `exists_time`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology Finset
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `E_W[Φ(past)H(P at pt)]`. -/
def finTest (b : ℝ) (e : ℕ → ℝ) (W : ℕ) {m : ℕ} (pts : Fin m → ℕ × ℝ)
    (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) {q : ℕ} (H : (Fin q → ℝ) → ℝ)
    (pt : Fin q → ℕ × ℝ) : ℝ :=
  ∫ ω, Φ (finVec b e W pts ω) * H (finVec b e W pt ω) ∂growthPathLaw W b

/-- `E[Φ(past)H(P at pt)]` on the limit. -/
def limTest (P : Measure Ω) (Pk : ℕ → ℝ → Ω → ℝ) {m : ℕ} (pts : Fin m → ℕ × ℝ)
    (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) {q : ℕ} (H : (Fin q → ℝ) → ℝ)
    (pt : Fin q → ℕ × ℝ) : ℝ :=
  ∫ ω, Φ (limVec Pk pts ω) * H (limVec Pk pt ω) ∂P

theorem exists_time {W : ℕ} (hW : 0 < W) {s t : ℝ} (hst : s ≤ t) {r : ℕ}
    (hr : r ∈ Ico ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * t⌋₊) : ∃ u ∈ Set.Icc s t, ⌊(W : ℝ) * u⌋₊ = r := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hr1, hr2⟩ := mem_Ico.mp hr
  have hrt : (r : ℝ) < W * t := by
    have h1 : (r : ℝ) < ⌊(W : ℝ) * t⌋₊ := by exact_mod_cast hr2
    have h2 : (⌊(W : ℝ) * t⌋₊ : ℝ) ≤ W * t := Nat.floor_le (by
      rcases Nat.eq_zero_or_pos ⌊(W : ℝ) * t⌋₊ with h | h
      · omega
      · exact (Nat.floor_pos.mp h |> fun h' => (zero_le_one.trans h')))
    linarith
  by_cases h : (r : ℝ) / W ≤ s
  · refine ⟨s, ⟨le_rfl, hst⟩, le_antisymm hr1 (Nat.le_floor ?_)⟩
    rw [div_le_iff₀ hWr] at h; linarith
  · rw [not_le] at h
    refine ⟨r / W, ⟨h.le, ?_⟩, ?_⟩
    · rw [div_le_iff₀ hWr]; linarith
    · rw [mul_div_cancel₀ _ hWr.ne', Nat.floor_natCast]

/-- **Riemann sums of tested functionals.** -/
theorem riemann_point {b : ℝ} {e : ℕ → ℝ} {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) {m : ℕ}
    (pts : Fin m → ℕ × ℝ) (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) {q : ℕ}
    {H : (Fin q → ℝ) → ℝ} {pt : ℝ → Fin q → ℕ × ℝ} {g : ℝ → ℝ} {s t K : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (hK : 0 ≤ K)
    (hfin : ∀ᶠ n in atTop, ∀ u ∈ Set.Icc s t, ∫⁻ ω, ‖Φ (finVec b e (σ n) pts ω) *
      H (finVec b e (σ n) (pt u) ω)‖ₑ ^ 2 ∂growthPathLaw (σ n) b ≤ ENNReal.ofReal K)
    (hlim : ∀ u ∈ Set.Icc s t, Tendsto (fun n => finTest b e (σ n) pts Φ H (pt u)) atTop
      (𝓝 (g u)))
    (c : ℕ → ℕ → ℝ) (hc : ∀ n, ∀ u ∈ Set.Icc s t,
      c n ⌊((σ n : ℕ) : ℝ) * u⌋₊ = finTest b e (σ n) pts Φ H (pt u)) :
    Tendsto (fun n => ∑ r ∈ Ico ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊,
      c n r / (σ n : ℝ)) atTop (𝓝 (∫ u in s..t, g u)) := by
  refine riemann_tendsto hσ (K := 1 + K) hs hst ?_ fun u hu => ?_
  · filter_upwards [hfin] with n hn u hu
    rw [hc n u hu]; exact abs_integral_le_of_sq hK (hn u hu)
  · exact (hlim u hu).congr fun n => (hc n u hu).symm

/-- **The expanded finite-`W` tested product converges.** -/
theorem prod_conv (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e)
    {P : Measure Ω} {Pk : ℕ → ℝ → Ω → ℝ} {σ : ℕ → ℕ} (hS : LimitSetup b e P Pk σ)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {m : ℕ}
    (pts : Fin m → ℕ × ℝ) (hpts : ∀ i, 1 ≤ (pts i).1 ∧ 0 < (pts i).2)
    (Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    Tendsto (fun n => ∫ ω, Φ (finVec b e (σ n) pts ω) *
      (prodM b E (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω *
        prodM b E (e (σ n)) (σ n) l ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω -
        bracketSum b E (e (σ n)) (σ n) k l ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω)
      ∂growthPathLaw (σ n) b) atTop
      (𝓝 (limTest P Pk pts Φ hYY (ptYY k l s t) -
        (∫ u in s..t, limTest P Pk pts Φ (hYA (transportD0 b E) l) (ptYA k l s t u)) -
        (∫ u in s..t, limTest P Pk pts Φ (hYA (transportD0 b E) k) (ptYA l k s t u)) +
        (∫ v in s..t, ∫ u in s..t,
          limTest P Pk pts Φ (hAA (transportD0 b E) l k) (ptAA l k v u)) -
        ∫ u in s..t, limTest P Pk pts Φ (hBr (transportD0 b E) k l) (ptVec (k + l + 1) u))) := by
  set D := transportD0 b E
  have hD : 0 ≤ D := transportD0_nonneg hb0 hE1 hE2
  have hσ := hS.tends
  obtain ⟨K1, hK1, hf1, hl1⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    continuous_hYY hYY_le
  obtain ⟨K2, hK2, hf2, hl2⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hYA D l) (hYA_le hD l)
  obtain ⟨K3, hK3, hf3, hl3⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hYA D k) (hYA_le hD k)
  obtain ⟨K4, hK4, hf4, hl4⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hAA D l k) (hAA_le hD l k)
  obtain ⟨K5, hK5, hf5, hl5⟩ := poly_point hLU hb0 hb hE1 hE2 he hS (T := t) hs pts hpts Φ
    (continuous_hBr D k l) (hBr_le hD k l)
  -- notation for the finite-`W` cells
  set rs : ℕ → ℕ := fun n => ⌊((σ n : ℕ) : ℝ) * s⌋₊
  set rt : ℕ → ℕ := fun n => ⌊((σ n : ℕ) : ℝ) * t⌋₊
  set ψ : ∀ n, GrowthPath (σ n) → ℝ := fun n ω => Φ (finVec b e (σ n) pts ω)
  set c2 : ℕ → ℕ → ℝ := fun n r => ∫ ω, ψ n ω * (prodY b (e (σ n)) (σ n) k (rs n) (rt n) ω *
    prodA b E (e (σ n)) (σ n) l r ω) ∂growthPathLaw (σ n) b
  set c3 : ℕ → ℕ → ℝ := fun n r => ∫ ω, ψ n ω * (prodY b (e (σ n)) (σ n) l (rs n) (rt n) ω *
    prodA b E (e (σ n)) (σ n) k r ω) ∂growthPathLaw (σ n) b
  set d : ℕ → ℕ → ℕ → ℝ := fun n r' r => ∫ ω, ψ n ω * (prodA b E (e (σ n)) (σ n) l r' ω *
    prodA b E (e (σ n)) (σ n) k r ω) ∂growthPathLaw (σ n) b
  set c5 : ℕ → ℕ → ℝ := fun n r => ∫ ω, ψ n ω * prodB b E (e (σ n)) (σ n) k l r ω
    ∂growthPathLaw (σ n) b
  -- the five limits
  have T1 : Tendsto (fun n => ∫ ω, ψ n ω * (prodY b (e (σ n)) (σ n) k (rs n) (rt n) ω *
      prodY b (e (σ n)) (σ n) l (rs n) (rt n) ω) ∂growthPathLaw (σ n) b) atTop
      (𝓝 (limTest P Pk pts Φ hYY (ptYY k l s t))) := by
    refine ((hl1 _ (ptYY_mem hk hl hst)).2).congr fun n => ?_
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hYY_fin, prodY, ψ, rs, rt]
  have T2 := riemann_point hσ pts Φ (pt := fun u => ptYA k l s t u) hs.le hst hK2
    (by filter_upwards [hf2] with n hn u hu using hn _ (ptYA_mem hk hst hu))
    (fun u hu => (hl2 _ (ptYA_mem hk hst hu)).2) c2 fun n u _ =>
      integral_congr_ae (ae_of_all _ fun ω => by simp only [hYA_fin, prodY, prodA, ψ, rs, rt, D])
  have T3 := riemann_point hσ pts Φ (pt := fun u => ptYA l k s t u) hs.le hst hK3
    (by filter_upwards [hf3] with n hn u hu using hn _ (ptYA_mem hl hst hu))
    (fun u hu => (hl3 _ (ptYA_mem hl hst hu)).2) c3 fun n u _ =>
      integral_congr_ae (ae_of_all _ fun ω => by simp only [hYA_fin, prodY, prodA, ψ, rs, rt, D])
  have T5 := riemann_point hσ pts Φ (pt := fun u => ptVec (k + l + 1) u) hs.le hst hK5
    (by filter_upwards [hf5] with n hn u hu using hn _ (ptVec_mem hu))
    (fun u hu => (hl5 _ (ptVec_mem hu)).2) c5 fun n u _ =>
      integral_congr_ae (ae_of_all _ fun ω => by simp only [hBr_fin D b e _ hk, prodB, ψ, D])
  have hin : ∀ v ∈ Set.Icc s t, Tendsto (fun n => ∑ r ∈ Ico (rs n) (rt n),
      d n ⌊((σ n : ℕ) : ℝ) * v⌋₊ r / (σ n : ℝ)) atTop
      (𝓝 (∫ u in s..t, limTest P Pk pts Φ (hAA D l k) (ptAA l k v u))) := fun v hv =>
    riemann_point hσ pts Φ (pt := fun u => ptAA l k v u) hs.le hst hK4
      (by filter_upwards [hf4] with n hn u hu using hn _ (ptAA_mem hv hu))
      (fun u hu => (hl4 _ (ptAA_mem hv hu)).2) (fun n r => d n ⌊((σ n : ℕ) : ℝ) * v⌋₊ r)
      fun n u _ => integral_congr_ae (ae_of_all _ fun ω => by simp only [hAA_fin, prodA, ψ, D])
  have T4 := riemann_tendsto hσ (c := fun n r' => ∑ r ∈ Ico (rs n) (rt n), d n r' r / (σ n : ℝ))
    (K := (t - s + 1) * (1 + K4)) hs.le hst ?_ hin
  rotate_left
  · filter_upwards [hf4, hσ.eventually_ge_atTop 1] with n hn hn1 v hv
    have hW : (0 : ℝ) < (σ n : ℝ) := by exact_mod_cast hn1
    have hcell : ∀ r ∈ Ico (rs n) (rt n), |d n ⌊((σ n : ℕ) : ℝ) * v⌋₊ r / (σ n : ℝ)| ≤
        (1 + K4) / (σ n : ℝ) := by
      intro r hr
      obtain ⟨u, hu, rfl⟩ := exists_time hn1 hst hr
      rw [abs_div, Nat.abs_cast]
      refine div_le_div_of_nonneg_right ?_ hW.le
      have := abs_integral_le_of_sq hK4 (hn _ (ptAA_mem hv hu))
      simpa only [d, ψ, hAA_fin, prodA, D] using this
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hcell).trans ?_)
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hrst : rs n ≤ rt n := Nat.floor_mono (mul_le_mul_of_nonneg_left hst hW.le)
    have h1 : ((rt n - rs n : ℕ) : ℝ) ≤ (t - s + 1) * (σ n : ℝ) := by
      rw [Nat.cast_sub hrst]
      have a1 : (rt n : ℝ) ≤ (σ n : ℝ) * t := Nat.floor_le (mul_nonneg hW.le (hs.le.trans hst))
      have a2 : (σ n : ℝ) * s < rs n + 1 := Nat.lt_floor_add_one _
      have a3 : (1 : ℝ) ≤ (σ n : ℝ) := by exact_mod_cast hn1
      nlinarith
    calc ((rt n - rs n : ℕ) : ℝ) * ((1 + K4) / (σ n : ℝ))
        ≤ (t - s + 1) * (σ n : ℝ) * ((1 + K4) / (σ n : ℝ)) := by gcongr
      _ = (t - s + 1) * (1 + K4) := by field_simp
  -- assemble
  have hT := (((T1.sub T2).sub T3).add T4).sub T5
  refine hT.congr' ?_
  filter_upwards [hσ.eventually_ge_atTop (EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce)]
    with n hn
  obtain ⟨he1, he2⟩ := bulk_bounds' (by linarith [(mem_bulk_min hE1 hE2).1])
    (along_mem_bulk hE1 hE2 he hn)
  have hψm : Measurable (ψ n) := Φ.continuous.measurable.comp (measurable_finVec b e (σ n) pts)
  exact (prod_expand (by linarith : b < 1) he1 he2 hD hk hl (rs n) (rt n) hψm
    (fun ω => abs_bcf_le Φ _)).symm

end BlockBand.Transmission.Generator
