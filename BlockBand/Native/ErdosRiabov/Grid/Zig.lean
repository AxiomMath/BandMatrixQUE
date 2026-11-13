module

public import BlockBand.Native.ErdosRiabov.Grid.ZigConst
public import BlockBand.Native.ErdosRiabov.Psi.TauFacts

set_option autoImplicit false

/-!
# Grid to uniform for the zig step

A union bound over the time grid, combined with the grid-to-uniform comparison, reduces uniform
bounds on `Ψ` up to the stopping time to fixed-time bounds.

* `grid_index_le`, `grid_event_subset`, **`measure_grid_le_sum`**, `measure_grid_le_mul`: the
  finite union bound over the grid `{j N^{-C}} ∩ [0, T]`, `T ≤ 1`:
  `P(∃ j, jN^{-C} ≤ T ∧ Q_j) ≤ ∑_{j ≤ ⌊N^C⌋} P(jN^{-C} ≤ T ∧ Q_j) ≤ (⌊N^C⌋ + 1) ε` if each term is
  `≤ ε` (the shape of fixed-time bounds `P(Ψ_t > X ∧ t ≤ τ) ≤ N^{-D}`);
* `gridToUniform_iso_two_whp`, `gridToUniform_av_two_whp`: `_two` plus `modulusEvent_whp`;
* **`gridToUniform_iso_vs`**, **`gridToUniform_av_vs`**: from `VSData` alone. For every `D'`
  there is `N₀` (depending only on `d`, `D'`) such that for every ring with `N = n W ≥ N₀`, every
  law `μ` of the initial matrix, every `P` with `P.W = W`, `P.D = D`, `S` stochastic symmetric,
  `z ∈ 𝒟`, every `1 ≤ k ≤ 8`, `X ≥ 0` and `[0,1]`-valued `T`, with `C_g = vsCg d`:
  `P(∃ t ≤ T, Ψ_t > 2X + N^{-1}) ≤
    ∑_{j ≤ ⌊N^{C_g}⌋} P(jN^{-C_g} ≤ T ∧ Ψ_{jN^{-C_g}} > X) + N^{-D'}`;
* `tauT`, `coe_tauT`, `tauT_le_one` and **`gridToUniform_iso_tau`**, **`gridToUniform_av_tau`**:
  the same with `T = min(τ, 1) = τ`, `τ = Psi.tau` (events `t ≤ τ` in `WithTop ℝ≥0`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open MeasureTheory Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-!
### The finite union bound over the grid
-/

theorem grid_index_le {N : ℕ} (hN : 1 ≤ (N : ℝ)) (C : ℝ) {j : ℕ}
    (hj : (j : ℝ≥0) * VS.meshPow (N : ℝ) C ≤ 1) : j ≤ ⌊(N : ℝ) ^ C⌋₊ := by
  have hN0 : (0 : ℝ) < N := by linarith
  have h : (j : ℝ) * (N : ℝ) ^ (-C) ≤ 1 := by
    have := NNReal.coe_le_coe.2 hj
    rwa [NNReal.coe_mul, VS.meshPow_coe hN0.le, NNReal.coe_natCast, NNReal.coe_one] at this
  apply Nat.le_floor
  have hpos := Real.rpow_pos_of_pos hN0 C
  rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_le_iff₀ hpos, one_mul] at h
  exact h

theorem grid_event_subset (C : ℝ) (T : RingSample p → ℝ≥0) (hT : ∀ x, T x ≤ 1)
    (Q : ℕ → RingSample p → Prop) :
    {x | ∃ j : ℕ, (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧ Q j x} ⊆
      ⋃ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ C⌋₊ + 1),
        {x | (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧ Q j x} := by
  rintro x ⟨j, hj, hQ⟩
  refine mem_iUnion₂.2 ⟨j, Finset.mem_range.2 ?_, hj, hQ⟩
  have := grid_index_le (VS.one_le_dim p) C (hj.trans (hT x))
  omega

/-- **The finite union bound over the grid.** -/
theorem measure_grid_le_sum (μ : Measure p.SiteMatrix) (C : ℝ) (T : RingSample p → ℝ≥0)
    (hT : ∀ x, T x ≤ 1) (Q : ℕ → RingSample p → Prop) :
    driverLaw (κ := Fin (ringDim p)) μ
        {x | ∃ j : ℕ, (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧ Q j x} ≤
      ∑ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ C⌋₊ + 1), driverLaw (κ := Fin (ringDim p)) μ
        {x | (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧ Q j x} :=
  (measure_mono (grid_event_subset C T hT Q)).trans (measure_biUnion_finset_le _ _)

/-- The union bound with a uniform fixed-time bound `ε`. -/
theorem measure_grid_le_mul (μ : Measure p.SiteMatrix) (C : ℝ) (T : RingSample p → ℝ≥0)
    (hT : ∀ x, T x ≤ 1) (Q : ℕ → RingSample p → Prop) {ε : ℝ≥0∞}
    (hε : ∀ j ≤ ⌊((p.n * p.W : ℕ) : ℝ) ^ C⌋₊, driverLaw (κ := Fin (ringDim p)) μ
      {x | (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧ Q j x} ≤ ε) :
    driverLaw (κ := Fin (ringDim p)) μ
        {x | ∃ j : ℕ, (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧ Q j x} ≤
      ((⌊((p.n * p.W : ℕ) : ℝ) ^ C⌋₊ + 1 : ℕ) : ℝ≥0∞) * ε := by
  refine (measure_grid_le_sum μ C T hT Q).trans ?_
  refine (Finset.sum_le_sum fun j hj => hε j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).trans
    (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-!
### `_two` with the modulus bound
-/

namespace PsiData

/-- `gridToUniform_iso_two` together with `modulusEvent_whp`. -/
theorem gridToUniform_iso_two_whp {C : ℝ} (hC : 0 < C) (D' : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P : PsiData (p.n * p.W)) {k : ℕ} {B b F φ : ℝ} (T : RingSample p → ℝ≥0) {X : ℝ},
      0 < P.W → 0 < P.z.im → StochasticSymm P.S → 0 ≤ P.D → 1 ≤ k → k ≤ 8 → 2 ≤ B →
      ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B →
      B ≤ ((p.n * p.W : ℕ) : ℝ) ^ b → 0 ≤ b → 0 < φ → ((p.n * p.W : ℕ) : ℝ) ^ (-F) ≤ φ →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i : IsoIdx (p.n * p.W) k,
        φ ≤ P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t) →
      P.z.im⁻¹ ≤ ((p.n * p.W : ℕ) : ℝ) →
      (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * b + F + 3 ≤ C / 3 →
      2 * (k : ℝ) + 1 ≤ ((p.n * p.W : ℕ) : ℝ) →
      ((p.n * p.W : ℕ) : ℝ) ^ (-C) / P.z.im * normExp k P.D ≤ 1 / 2 →
      (∀ x, T x ≤ 1) → 0 ≤ X → N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
          2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiIso k t (VS.vsBandFin p t x)} ≤
        driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
          (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
          X < P.bigPsiIso k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
            (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨N₀, hN₀⟩ := modulusEvent_whp hC D'
  refine ⟨N₀, fun p μ _ P k B b F φ T X hW hz hS hD hk hk8 hB2 hBL hBN hb hφ hφF hfl hzN hCg hNk
    hqE hT hX hN => ?_⟩
  exact ((PsiData.gridToUniform_iso_two P) μ hW hz hS hD hk hk8 hC.le hB2 hBL hBN hb hφ hφF hfl
    hzN hCg hNk hqE T hT hX).trans (add_le_add le_rfl (hN₀ p μ hN))

/-- `gridToUniform_av_two` together with `modulusEvent_whp`. -/
theorem gridToUniform_av_two_whp {C : ℝ} (hC : 0 < C) (D' : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P : PsiData (p.n * p.W)) {k : ℕ} {B b F φ : ℝ} (T : RingSample p → ℝ≥0) {X : ℝ},
      0 < P.W → 0 < P.z.im → StochasticSymm P.S → 0 ≤ P.D → 1 ≤ k → k ≤ 8 → 2 ≤ B →
      ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B →
      B ≤ ((p.n * p.W : ℕ) : ℝ) ^ b → 0 ≤ b → 0 < φ → ((p.n * p.W : ℕ) : ℝ) ^ (-F) ≤ φ →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i : AvIdx (p.n * p.W) k,
        φ ≤ P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t) →
      P.z.im⁻¹ ≤ ((p.n * p.W : ℕ) : ℝ) →
      (k : ℝ) + 4 + 4 * ((k : ℝ) - 1) * b + F + 3 ≤ C / 3 →
      2 * (k : ℝ) + 1 ≤ ((p.n * p.W : ℕ) : ℝ) →
      ((p.n * p.W : ℕ) : ℝ) ^ (-C) / P.z.im * normExp k P.D ≤ 1 / 2 →
      (∀ x, T x ≤ 1) → 0 ≤ X → N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
          2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiAv k t (VS.vsBandFin p t x)} ≤
        driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
          (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
          X < P.bigPsiAv k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
            (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨N₀, hN₀⟩ := modulusEvent_whp hC D'
  refine ⟨N₀, fun p μ _ P k B b F φ T X hW hz hS hD hk hk8 hB2 hBL hBN hb hφ hφF hfl hzN hCg hNk
    hqE hT hX hN => ?_⟩
  exact ((PsiData.gridToUniform_av_two P) μ hW hz hS hD hk hk8 hC.le hB2 hBL hBN hb hφ hφF hfl
    hzN hCg hNk hqE T hT hX).trans (add_le_add le_rfl (hN₀ p μ hN))

/-!
### From `VSData` alone
-/

/-- **Grid step, `Ψ^iso`, from `VSData`.** -/
theorem gridToUniform_iso_vs (d : VSData) (D' : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P : PsiData (p.n * p.W)) {k : ℕ} (T : RingSample p → ℝ≥0) {X : ℝ},
      P.W = p.W → P.D = d.D → StochasticSymm P.S →
      BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z → 1 ≤ k → k ≤ 8 →
      (∀ x, T x ≤ 1) → 0 ≤ X → N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
          2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiIso k t (VS.vsBandFin p t x)} ≤
        ∑ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ vsCg d⌋₊ + 1),
          driverLaw (κ := Fin (ringDim p)) μ
            {x | (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) ≤ T x ∧
              X < P.bigPsiIso k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                ℝ) (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d)) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨N₁, hN₁⟩ := gridToUniform_iso_two_whp (C := vsCg d) (by linarith [(vsCg_facts d).1]) D'
  refine ⟨max N₁ (zigN0 d), fun p μ _ P k T X hPW hPD hS hz hk hk8 hT hX hN => ?_⟩
  have hNz : zigN0 d ≤ ((p.n * p.W : ℕ) : ℝ) := (le_max_right _ _).trans hN
  obtain ⟨hB2, hBL, hBN, hφ, hφF, hzN, hCg, hNk, hqE, hNA⟩ :=
    zig_conditions d hNz hz hk hk8
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hWN : p.W ≤ p.n * p.W := Nat.le_mul_of_pos_left _ (by have := p.n_ge_four; omega)
  have hD : 0 ≤ P.D := by rw [hPD]; linarith [d.D_ge_six]
  have hDpp : (vsK : ℝ) * (2 + P.D) + 1 ≤ (vsK : ℝ) * (2 * d.Dpp + 1) := by
    rw [hPD]; exact floor_exponent_le_of_vsData d
  have hNA' : (1 + Real.sqrt (d.C0 + 1)) ^ ((vsK : ℝ) * (2 + P.D)) ≤ ((p.n * p.W : ℕ) : ℝ) := by
    rw [hPD]; exact hNA
  have hfl := (PsiData.normIso_floor P) hNpos p.W_pos hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hD hz hPW hk (by unfold vsK; omega) hDpp hNA'
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hqE' : ((p.n * p.W : ℕ) : ℝ) ^ (-vsCg d) / P.z.im * normExp k P.D ≤ 1 / 2 := by
    rw [hPD]; exact hqE
  refine (hN₁ p μ P T hW (hz.im_pos hNpos) hS hD hk hk8 hB2 hBL hBN zero_le_two hφ hφF hfl hzN
    hCg hNk hqE' hT hX ((le_max_left _ _).trans hN)).trans ?_
  exact add_le_add (measure_grid_le_sum μ (vsCg d) T hT _) le_rfl

/-- **Grid step, `Ψ^av`, from `VSData`.** -/
theorem gridToUniform_av_vs (d : VSData) (D' : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P : PsiData (p.n * p.W)) {k : ℕ} (T : RingSample p → ℝ≥0) {X : ℝ},
      P.W = p.W → P.D = d.D → StochasticSymm P.S →
      BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z → 1 ≤ k → k ≤ 8 →
      (∀ x, T x ≤ 1) → 0 ≤ X → N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
          2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiAv k t (VS.vsBandFin p t x)} ≤
        ∑ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ vsCg d⌋₊ + 1),
          driverLaw (κ := Fin (ringDim p)) μ
            {x | (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) ≤ T x ∧
              X < P.bigPsiAv k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                ℝ) (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d)) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨N₁, hN₁⟩ := gridToUniform_av_two_whp (C := vsCg d) (by linarith [(vsCg_facts d).1]) D'
  refine ⟨max N₁ (zigN0 d), fun p μ _ P k T X hPW hPD hS hz hk hk8 hT hX hN => ?_⟩
  have hNz : zigN0 d ≤ ((p.n * p.W : ℕ) : ℝ) := (le_max_right _ _).trans hN
  obtain ⟨hB2, hBL, hBN, hφ, hφF, hzN, hCg, hNk, hqE, hNA⟩ :=
    zig_conditions d hNz hz hk hk8
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hWN : p.W ≤ p.n * p.W := Nat.le_mul_of_pos_left _ (by have := p.n_ge_four; omega)
  have hD : 0 ≤ P.D := by rw [hPD]; linarith [d.D_ge_six]
  have hDpp : (vsK : ℝ) * (2 + P.D) + 1 ≤ (vsK : ℝ) * (2 * d.Dpp + 1) := by
    rw [hPD]; exact floor_exponent_le_of_vsData d
  have hNA' : (1 + Real.sqrt (d.C0 + 1)) ^ ((vsK : ℝ) * (2 + P.D)) ≤ ((p.n * p.W : ℕ) : ℝ) := by
    rw [hPD]; exact hNA
  have hfl := (PsiData.normAv_floor P) hNpos p.W_pos hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hD hz hPW hk (by unfold vsK; omega) hDpp hNA'
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hqE' : ((p.n * p.W : ℕ) : ℝ) ^ (-vsCg d) / P.z.im * normExp k P.D ≤ 1 / 2 := by
    rw [hPD]; exact hqE
  refine (hN₁ p μ P T hW (hz.im_pos hNpos) hS hD hk hk8 hB2 hBL hBN zero_le_two hφ hφF hfl hzN
    hCg hNk hqE' hT hX ((le_max_left _ _).trans hN)).trans ?_
  exact add_le_add (measure_grid_le_sum μ (vsCg d) T hT _) le_rfl

end PsiData

/-!
### `T = τ`
-/

variable (p) in
/-- The stopping time `Psi.tau` as an `ℝ≥0`-valued time (`τ ≤ 1 < ⊤`). -/
def tauT (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p) : ℝ≥0 :=
  (tau p P psiI psiA x).untop (tau_ne_top P psiI psiA x)

theorem coe_tauT (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p) :
    ((tauT p P psiI psiA x : ℝ≥0) : WithTop ℝ≥0) = tau p P psiI psiA x :=
  WithTop.coe_untop _ _

theorem tauT_le_one (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p) :
    tauT p P psiI psiA x ≤ 1 := by
  have h := tau_le_one P psiI psiA x
  rw [← coe_tauT] at h
  exact WithTop.coe_le_coe.mp h

theorem le_tauT_iff (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p)
    (t : ℝ≥0) : t ≤ tauT p P psiI psiA x ↔ (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x := by
  rw [← coe_tauT, WithTop.coe_le_coe]

namespace PsiData

/-- **Grid step, `Ψ^iso`, up to `τ`.** For `τ = tau p P' ψ^{iso} ψ^{av}` (any `P'`, any
thresholds): `P(∃ t ≤ τ, Ψ^iso_t > 2X + N^{-1}) ≤ ∑_{j ≤ ⌊N^{C_g}⌋} P(jN^{-C_g} ≤ τ ∧
Ψ^iso_{jN^{-C_g}} > X) + N^{-D'}`. -/
theorem gridToUniform_iso_tau (d : VSData) (D' : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P P' : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) {k : ℕ} {X : ℝ},
      P.W = p.W → P.D = d.D → StochasticSymm P.S →
      BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z → 1 ≤ k → k ≤ 8 →
      0 ≤ X → N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0,
          (t : WithTop ℝ≥0) ≤ tau p P' psiI psiA x ∧
          2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiIso k t (VS.vsBandFin p t x)} ≤
        ∑ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ vsCg d⌋₊ + 1),
          driverLaw (κ := Fin (ringDim p)) μ
            {x | (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                WithTop ℝ≥0) ≤ tau p P' psiI psiA x ∧
              X < P.bigPsiIso k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                ℝ) (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d)) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨N₀, hN₀⟩ := gridToUniform_iso_vs d D'
  refine ⟨N₀, fun p μ _ P P' psiI psiA k X hPW hPD hS hz hk hk8 hX hN => ?_⟩
  have h := hN₀ p μ P (tauT p P' psiI psiA) hPW hPD hS hz hk hk8 (tauT_le_one P' psiI psiA) hX hN
  simp only [le_tauT_iff] at h
  exact h

/-- **Grid step, `Ψ^av`, up to `τ`.** -/
theorem gridToUniform_av_tau (d : VSData) (D' : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P P' : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) {k : ℕ} {X : ℝ},
      P.W = p.W → P.D = d.D → StochasticSymm P.S →
      BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z → 1 ≤ k → k ≤ 8 →
      0 ≤ X → N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0,
          (t : WithTop ℝ≥0) ≤ tau p P' psiI psiA x ∧
          2 * X + ((p.n * p.W : ℕ) : ℝ)⁻¹ < P.bigPsiAv k t (VS.vsBandFin p t x)} ≤
        ∑ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ vsCg d⌋₊ + 1),
          driverLaw (κ := Fin (ringDim p)) μ
            {x | (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                WithTop ℝ≥0) ≤ tau p P' psiI psiA x ∧
              X < P.bigPsiAv k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                ℝ) (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d)) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨N₀, hN₀⟩ := gridToUniform_av_vs d D'
  refine ⟨N₀, fun p μ _ P P' psiI psiA k X hPW hPD hS hz hk hk8 hX hN => ?_⟩
  have h := hN₀ p μ P (tauT p P' psiI psiA) hPW hPD hS hz hk hk8 (tauT_le_one P' psiI psiA) hX hN
  simp only [le_tauT_iff] at h
  exact h

end PsiData

end BlockBand.Native.ErdosRiabov.Grid
