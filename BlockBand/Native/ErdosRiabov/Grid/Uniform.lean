module

public import BlockBand.Native.ErdosRiabov.Grid.PsiNear
public import BlockBand.Native.ErdosRiabov.VS.ModulusGlue

set_option autoImplicit false

/-!
# Grid to uniform

Bounds on the control quantities `Ψ` on a time grid extend to all times, deterministically and
along the VS band process.

Setting as for `PsiData.bigPsiIso_le_of_near`, grid `𝒢 = {j h} ∩ [0, T]` with mesh `h > 0` and a
horizon `T ≤ 1`
(e.g. `T = min(τ, 1)`, any `[0,1]`-valued random time; no stopping-time property is used).

* `PsiData.errLip_mono`: `errLip` is monotone in the time increment.
* **`PsiData.bigPsiIso_grid`**, **`PsiData.bigPsiAv_grid`** (deterministic): for a Hermitian path
  `t ↦ H_t` with `|(H_t - H_s)_{ab}| ≤ δ` whenever `s ≤ t ≤ s + h`, `t ≤ 1`, and normalization
  floor `φ > 0` on `[0,1]`: if `Ψ_{jh}(H_{jh}) ≤ X` at every grid time `jh ≤ T`, then for every
  `t ≤ T`, `Ψ_t(H_t) ≤ (1 + h/Im z)^E X + errLip(δ, h)/φ` (`N errLip/φ` for `Ψ^{av}`).
* **`PsiData.gridToUniform_iso`**, **`PsiData.gridToUniform_av`** (along the VS band process
  `H_t = vsBandFin p t`, mesh `meshPow N C = N^{-C}`, `δ = N^{-C/3}`, `N = p.n p.W`):
  `P(∃ t ≤ T, Ψ_t > (1 + N^{-C}/Im z)^E X + errLip/φ) ≤ P(∃ grid time jN^{-C} ≤ T,
  Ψ_{jN^{-C}} > X) + P(modulus event)`, the modulus event being the failure of the
  increment bound `|(H_t - H_s)_{ab}| ≤ N^{-C/3}` for `|t - s| ≤ N^{-C}`; and
  **`PsiData.gridToUniform_iso_whp`**,
  **`PsiData.gridToUniform_av_whp`**: the last term is `≤ N^{-D}` for `N ≥ N₀(C, D)`, the `N₀` of
  `VS.vsBand_modulus_whp`.
* `PsiData.normIso_floor`, `PsiData.normAv_floor`: the normalizations are `≥ min 1 (Im z/√(C₀+1)) ·
  N^{-K(2D''+1)}` on `[0,1]` (`sizes_floor_vsK`, `Kernel.loc_bounds_of_le`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open MeasureTheory Matrix Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

namespace PsiData

variable {N k : ℕ} (P : PsiData N)

theorem errLip_mono (k : ℕ) {δ τ τ' B : ℝ} (hτ : τ ≤ τ') (hB : 0 ≤ B) :
    (PsiData.errLip P) k δ τ B ≤ (PsiData.errLip P) k δ τ' B := by
  unfold PsiData.errLip
  have h1 : 0 ≤ (k : ℝ) * (max 1 P.z.im⁻¹) ^ k * P.z.im⁻¹ ^ 2 := by
    have : 0 ≤ max 1 P.z.im⁻¹ := le_trans zero_le_one (le_max_left _ _)
    positivity
  have h2 : 0 ≤ B ^ (4 * (k - 1)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hτ h1, mul_le_mul_of_nonneg_left hτ h2]

/-- Grid point and remainder: `j = ⌊t/h⌋`, `jh ≤ t < jh + h`. -/
theorem grid_point {h : ℝ≥0} (hh : 0 < h) (t : ℝ≥0) :
    (⌊t / h⌋₊ : ℝ≥0) * h ≤ t ∧ t ≤ (⌊t / h⌋₊ : ℝ≥0) * h + h := by
  refine ⟨(le_div_iff₀ hh).1 (Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ t / h)), ?_⟩
  have := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one (t / h))
  rw [add_mul, one_mul] at this
  exact this.le

/-- The two-time inputs of the grid step. -/
theorem grid_step_inputs (hz : 0 < P.z.im) {h : ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t)
    (hts : t ≤ s + h) :
    (1 + |(t : ℝ) - s| / P.z.im) ≤ 1 + (h : ℝ) / P.z.im ∧ |(t : ℝ) - s| ≤ h := by
  have h1 : |(t : ℝ) - s| ≤ h := by
    rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hst))]
    have : (t : ℝ) ≤ s + h := by exact_mod_cast hts
    linarith
  refine ⟨?_, h1⟩
  have := div_le_div_of_nonneg_right h1 hz.le
  linarith

/-- **Grid to uniform for `Ψ^iso`** (deterministic). -/
theorem bigPsiIso_grid (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k) (hk8 : k ≤ 8)
    (Hf : ℝ≥0 → Matrix (Fin N) (Fin N) ℂ) (hHf : ∀ t, (Hf t).IsHermitian) {h : ℝ≥0}
    (hh : 0 < h) {δ : ℝ}
    (hmod : ∀ s t : ℝ≥0, s ≤ t → t ≤ s + h → t ≤ 1 → ∀ a b, ‖(Hf t - Hf s) a b‖ ≤ δ)
    {B : ℝ} (hB2 : 2 ≤ B) (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    {φ : ℝ} (hφ : 0 < φ) (hfl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : IsoIdx N k,
      φ ≤ P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t)
    {T : ℝ≥0} (hT : T ≤ 1) {X : ℝ}
    (hgrid : ∀ j : ℕ, (j : ℝ≥0) * h ≤ T →
      P.bigPsiIso k (((j : ℝ≥0) * h : ℝ≥0) : ℝ) (Hf ((j : ℝ≥0) * h)) ≤ X) :
    ∀ t : ℝ≥0, t ≤ T → P.bigPsiIso k t (Hf t) ≤
      (1 + (h : ℝ) / P.z.im) ^ normExp k P.D * X + (PsiData.errLip P) k δ h B / φ := by
  intro t htT
  obtain ⟨hjs, hjt⟩ := grid_point hh t
  set s : ℝ≥0 := (⌊t / h⌋₊ : ℝ≥0) * h
  have hsT : s ≤ T := hjs.trans htT
  have ht1 : t ≤ 1 := htT.trans hT
  have hδ : ∀ a b, ‖(Hf t - Hf s) a b‖ ≤ δ := hmod s t hjs hjt ht1
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨t.2, by exact_mod_cast ht1⟩
  have hsI : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨s.2, by exact_mod_cast hsT.trans hT⟩
  have hnear := (PsiData.bigPsiIso_le_of_near P) hN hW hz hS hD hk hk8 (hHf t) (hHf s) hδ hB2 hBL
    htI
    hsI hφ (hfl t htI)
  obtain ⟨hq, habs⟩ := (PsiData.grid_step_inputs P) hz (h := h) hjs hjt
  have hX : P.bigPsiIso k s (Hf s) ≤ X := hgrid _ hsT
  have hX0 : 0 ≤ X := (P.bigPsiIso_nonneg _ _).trans hX
  have hq1 := PsiData.q_ge_one P hz t s
  refine hnear.trans (add_le_add ?_ ?_)
  · exact mul_le_mul (Real.rpow_le_rpow (by linarith) hq (normExp_nonneg k hD)) hX
      (P.bigPsiIso_nonneg _ _) (Real.rpow_nonneg (by linarith) _)
  · exact div_le_div_of_nonneg_right ((PsiData.errLip_mono P) k habs (by linarith)) hφ.le

/-- **Grid to uniform for `Ψ^av`** (deterministic). -/
theorem bigPsiAv_grid (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k) (hk8 : k ≤ 8)
    (Hf : ℝ≥0 → Matrix (Fin N) (Fin N) ℂ) (hHf : ∀ t, (Hf t).IsHermitian) {h : ℝ≥0}
    (hh : 0 < h) {δ : ℝ}
    (hmod : ∀ s t : ℝ≥0, s ≤ t → t ≤ s + h → t ≤ 1 → ∀ a b, ‖(Hf t - Hf s) a b‖ ≤ δ)
    {B : ℝ} (hB2 : 2 ≤ B) (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    {φ : ℝ} (hφ : 0 < φ) (hfl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : AvIdx N k,
      φ ≤ P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t)
    {T : ℝ≥0} (hT : T ≤ 1) {X : ℝ}
    (hgrid : ∀ j : ℕ, (j : ℝ≥0) * h ≤ T →
      P.bigPsiAv k (((j : ℝ≥0) * h : ℝ≥0) : ℝ) (Hf ((j : ℝ≥0) * h)) ≤ X) :
    ∀ t : ℝ≥0, t ≤ T → P.bigPsiAv k t (Hf t) ≤
      (1 + (h : ℝ) / P.z.im) ^ normExp k P.D * X + N * (PsiData.errLip P) k δ h B / φ := by
  intro t htT
  obtain ⟨hjs, hjt⟩ := grid_point hh t
  set s : ℝ≥0 := (⌊t / h⌋₊ : ℝ≥0) * h
  have hsT : s ≤ T := hjs.trans htT
  have ht1 : t ≤ 1 := htT.trans hT
  have hδ : ∀ a b, ‖(Hf t - Hf s) a b‖ ≤ δ := hmod s t hjs hjt ht1
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨t.2, by exact_mod_cast ht1⟩
  have hsI : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨s.2, by exact_mod_cast hsT.trans hT⟩
  have hnear := (PsiData.bigPsiAv_le_of_near P) hN hW hz hS hD hk hk8 (hHf t) (hHf s) hδ hB2 hBL htI
    hsI hφ (hfl t htI)
  obtain ⟨hq, habs⟩ := (PsiData.grid_step_inputs P) hz (h := h) hjs hjt
  have hX : P.bigPsiAv k s (Hf s) ≤ X := hgrid _ hsT
  have hX0 : 0 ≤ X := (P.bigPsiAv_nonneg _ _).trans hX
  have hq1 := PsiData.q_ge_one P hz t s
  refine hnear.trans (add_le_add ?_ ?_)
  · exact mul_le_mul (Real.rpow_le_rpow (by linarith) hq (normExp_nonneg k hD)) hX
      (P.bigPsiAv_nonneg _ _) (Real.rpow_nonneg (by linarith) _)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((PsiData.errLip_mono P) k habs (by linarith)) (Nat.cast_nonneg N)) hφ.le

end PsiData

/-!
### Along the VS band process
-/

variable {p : BlockBand.Parameters} {k : ℕ}

/-- The modulus event at mesh `N^{-C}` and level `N^{-C/3}`, `N = p.n p.W`. -/
def modulusEvent (p : BlockBand.Parameters) (C : ℝ) : Set (RingSample p) :=
  {x | ∃ s t : ℝ≥0, s ≤ t ∧ t ≤ s + VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ∧ t ≤ 1 ∧
    ∃ a b : p.Site, ((p.n * p.W : ℕ) : ℝ) ^ (-C / 3) ≤ ‖VS.vsBand p t x a b - VS.vsBand p s x a b‖}

/-- Off the modulus event, the `Fin (p.n p.W)` process has increments `≤ N^{-C/3}` over times
`≤ N^{-C}` apart. -/
theorem modulus_of_not_mem {C : ℝ} {x : RingSample p} (hx : x ∉ modulusEvent p C) :
    ∀ s t : ℝ≥0, s ≤ t → t ≤ s + VS.meshPow ((p.n * p.W : ℕ) : ℝ) C → t ≤ 1 →
      ∀ a b, ‖(VS.vsBandFin p t x - VS.vsBandFin p s x) a b‖ ≤
        ((p.n * p.W : ℕ) : ℝ) ^ (-C / 3) := by
  intro s t hst hts ht a b
  by_contra hlt
  push Not at hlt
  refine hx ⟨s, t, hst, hts, ht, (VS.ringSiteEquiv p).symm a, (VS.ringSiteEquiv p).symm b, ?_⟩
  rw [Matrix.sub_apply, VS.vsBandFin_apply, VS.vsBandFin_apply] at hlt
  exact hlt.le

theorem meshPow_pos_dim (p : BlockBand.Parameters) (C : ℝ) :
    0 < VS.meshPow ((p.n * p.W : ℕ) : ℝ) C :=
  VS.meshPow_pos (by linarith [VS.one_le_dim p]) C

namespace PsiData

variable (P : PsiData (p.n * p.W))

/-- **Grid to uniform, `Ψ^iso` along the VS band process.** -/
theorem gridToUniform_iso (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k) (hk8 : k ≤ 8)
    (C : ℝ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    {φ : ℝ} (hφ : 0 < φ) (hfl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : IsoIdx (p.n * p.W) k,
      φ ≤ P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t)
    (T : RingSample p → ℝ≥0) (hT : ∀ x, T x ≤ 1) (X : ℝ) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
        (1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) / P.z.im) ^ normExp k P.D * X +
          (PsiData.errLip P) k (((p.n * p.W : ℕ) : ℝ) ^ (-C / 3))
            (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) B /
            φ < P.bigPsiIso k t (VS.vsBandFin p t x)} ≤
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
        (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
        X < P.bigPsiIso k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
          (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
        driverLaw (κ := Fin (ringDim p)) μ (modulusEvent p C) := by
  refine le_trans (measure_mono fun x hx => ?_) (measure_union_le _ _)
  obtain ⟨t, htT, hlt⟩ := hx
  by_contra hno
  simp only [mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hno
  obtain ⟨hgrid, hmod⟩ := hno
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have h := (PsiData.bigPsiIso_grid P) hN hW hz hS hD hk hk8 (fun t => VS.vsBandFin p t x)
    (fun t => VS.vsBandFin_isHermitian t x) (meshPow_pos_dim p C) (modulus_of_not_mem hmod)
    hB2 hBL hφ hfl (hT x) hgrid t htT
  exact absurd h (not_le.2 hlt)

/-- **Grid to uniform, `Ψ^av` along the VS band process.** -/
theorem gridToUniform_av (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (hD : 0 ≤ P.D) (hk : 1 ≤ k) (hk8 : k ≤ 8)
    (C : ℝ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    {φ : ℝ} (hφ : 0 < φ) (hfl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : AvIdx (p.n * p.W) k,
      φ ≤ P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t)
    (T : RingSample p → ℝ≥0) (hT : ∀ x, T x ≤ 1) (X : ℝ) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
        (1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) / P.z.im) ^ normExp k P.D * X +
          ((p.n * p.W : ℕ) : ℝ) * (PsiData.errLip P) k (((p.n * p.W : ℕ) : ℝ) ^ (-C / 3))
            (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) B / φ < P.bigPsiAv k t (VS.vsBandFin p t x)} ≤
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
        (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
        X < P.bigPsiAv k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
          (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
        driverLaw (κ := Fin (ringDim p)) μ (modulusEvent p C) := by
  refine le_trans (measure_mono fun x hx => ?_) (measure_union_le _ _)
  obtain ⟨t, htT, hlt⟩ := hx
  by_contra hno
  simp only [mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hno
  obtain ⟨hgrid, hmod⟩ := hno
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have h := (PsiData.bigPsiAv_grid P) hN hW hz hS hD hk hk8 (fun t => VS.vsBandFin p t x)
    (fun t => VS.vsBandFin_isHermitian t x) (meshPow_pos_dim p C) (modulus_of_not_mem hmod)
    hB2 hBL hφ hfl (hT x) hgrid t htT
  exact absurd h (not_le.2 hlt)

end PsiData

/-- The modulus event has probability `≤ N^{-D}` for `N ≥ N₀(C, D)` (`VS.vsBand_modulus_whp`). -/
theorem modulusEvent_whp {C : ℝ} (hC : 0 < C) (D : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ],
      N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ (modulusEvent p C) ≤
        ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) :=
  VS.vsBand_modulus_whp hC D

namespace PsiData

/-- **Grid to uniform, very-high-probability form (`Ψ^iso`)**: for `C > 0` and every `D` there is
`N₀`
(the `N₀` of `VS.vsBand_modulus_whp`) such that for `N = p.n p.W ≥ N₀` the probability that
`Ψ^iso_t > (1 + N^{-C}/Im z)^E X + errLip/φ` for some `t ≤ T` is at most the probability of a
grid violation plus `N^{-D}`. -/
theorem gridToUniform_iso_whp {C : ℝ} (hC : 0 < C) (D : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P : PsiData (p.n * p.W)), 0 < P.W → 0 < P.z.im → StochasticSymm P.S → 0 ≤ P.D →
      ∀ {k : ℕ}, 1 ≤ k → k ≤ 8 → ∀ {B : ℝ}, 2 ≤ B →
      ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B →
      ∀ {φ : ℝ}, 0 < φ → (∀ t ∈ Icc (0 : ℝ) 1, ∀ i : IsoIdx (p.n * p.W) k,
        φ ≤ P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t) →
      ∀ (T : RingSample p → ℝ≥0), (∀ x, T x ≤ 1) → ∀ X : ℝ,
      N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
          (1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) / P.z.im) ^ normExp k P.D * X +
            (PsiData.errLip P) k (((p.n * p.W : ℕ) : ℝ) ^ (-C / 3))
              (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C)
              B / φ < P.bigPsiIso k t (VS.vsBandFin p t x)} ≤
        driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
          (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
          X < P.bigPsiIso k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
            (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀⟩ := modulusEvent_whp hC D
  refine ⟨N₀, fun p μ _ P hW hz hS hD k hk hk8 B hB2 hBL φ hφ hfl T hT X hN => ?_⟩
  exact ((PsiData.gridToUniform_iso P) μ hW hz hS hD hk hk8 C hB2 hBL hφ hfl T hT X).trans
    (add_le_add le_rfl (hN₀ p μ hN))

/-- **Grid to uniform, very-high-probability form (`Ψ^av`)**. -/
theorem gridToUniform_av_whp {C : ℝ} (hC : 0 < C) (D : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P : PsiData (p.n * p.W)), 0 < P.W → 0 < P.z.im → StochasticSymm P.S → 0 ≤ P.D →
      ∀ {k : ℕ}, 1 ≤ k → k ≤ 8 → ∀ {B : ℝ}, 2 ≤ B →
      ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B →
      ∀ {φ : ℝ}, 0 < φ → (∀ t ∈ Icc (0 : ℝ) 1, ∀ i : AvIdx (p.n * p.W) k,
        φ ≤ P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t) →
      ∀ (T : RingSample p → ℝ≥0), (∀ x, T x ≤ 1) → ∀ X : ℝ,
      N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T x ∧
          (1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) / P.z.im) ^ normExp k P.D * X +
            ((p.n * p.W : ℕ) : ℝ) * (PsiData.errLip P) k (((p.n * p.W : ℕ) : ℝ) ^ (-C / 3))
              (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) B / φ <
            P.bigPsiAv k t (VS.vsBandFin p t x)} ≤
        driverLaw (κ := Fin (ringDim p)) μ {x | ∃ j : ℕ,
          (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T x ∧
          X < P.bigPsiAv k (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ≥0) : ℝ)
            (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) x)} +
          ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀⟩ := modulusEvent_whp hC D
  refine ⟨N₀, fun p μ _ P hW hz hS hD k hk hk8 B hB2 hBL φ hφ hfl T hT X hN => ?_⟩
  exact ((PsiData.gridToUniform_av P) μ hW hz hS hD hk hk8 C hB2 hBL hφ hfl T hT X).trans
    (add_le_add le_rfl (hN₀ p μ hN))

/-!
### The normalization floor
-/

theorem min_one_le_rpow {a α : ℝ} (ha : 0 < a) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    min 1 a ≤ a ^ α := by
  rcases le_total 1 a with h | h
  · exact (min_le_left _ _).trans (Real.one_le_rpow h hα0)
  · calc min 1 a ≤ a := min_le_right _ _
      _ = a ^ (1 : ℝ) := (Real.rpow_one a).symm
      _ ≤ a ^ α := Real.rpow_le_rpow_of_exponent_ge ha h hα1

variable {N k : ℕ} (P : PsiData N)

/-- `ℓ_tη_t ≥ Im z/√(C₀+1)` on `[0,1]` (`z ∈ 𝒟`, `1 ≤ W ≤ N`). -/
theorem lEta_ge {δ₀ κ C₀ : ℝ} {W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N) (hκ : 0 < κ)
    (hC₀ : 0 ≤ C₀) (hz : BulkDomain N δ₀ κ C₀ P.z) (hPW : P.W = W) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : P.z.im / Real.sqrt (C₀ + 1) ≤ P.lEta t := by
  obtain ⟨hη, hηC, -, -⟩ := P.height_bounds hN hW hWN hκ hC₀ hz hPW ht0 ht1
  have hloc := (loc_bounds_of_le (N := N) (W := W) hWN (by linarith : (1 : ℝ) ≤ C₀ + 1) hη
    hηC).1
  have hzim := hz.im_pos hN
  have hη' := im_le_vsHeight hzim ht1
  have hs : 0 < Real.sqrt (C₀ + 1) := Real.sqrt_pos.mpr (by linarith)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  unfold Psi.PsiData.lEta
  rw [hPW]
  calc P.z.im / Real.sqrt (C₀ + 1) = (1 / Real.sqrt (C₀ + 1)) * P.z.im := by ring
    _ ≤ ((W : ℝ) / Real.sqrt (C₀ + 1)) * vsHeight P.z t := by
        gcongr
    _ ≤ localizationLength N W (vsHeight P.z t) * vsHeight P.z t := by gcongr

/-- **Floor of the `Ψ^iso` normalizations** on `[0,1]`:
`(ℓη)^{α_k} s^{iso} ≥ min 1 (Im z/√(C₀+1)) N^{-K(2D''+1)}` under the hypotheses of
`sizes_floor_vsK`. -/
theorem normIso_floor {δ₀ κ C₀ Dpp : ℝ} {W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N)
    (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ P.D) (hz : BulkDomain N δ₀ κ C₀ P.z)
    (hPW : P.W = W) (hk : 1 ≤ k) (hkK : k ≤ vsK)
    (hDpp : (vsK : ℝ) * (2 + P.D) + 1 ≤ (vsK : ℝ) * (2 * Dpp + 1))
    (hNA : (1 + Real.sqrt (C₀ + 1)) ^ ((vsK : ℝ) * (2 + P.D)) ≤ N) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : IsoIdx N k,
      min 1 (P.z.im / Real.sqrt (C₀ + 1)) * (N : ℝ) ^ (-((vsK : ℝ) * (2 * Dpp + 1))) ≤
        P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t := by
  intro t ht i
  have hfl := (P.sizes_floor_vsK hN hW hWN hκ hC₀ hD hz hPW hk hkK hDpp hNA ht.1 ht.2).1
    i.2.1 i.2.2.1 i.2.2.2
  have hα := lossAlpha_mem (k := k) (by unfold vsK at hkK; omega)
  have hL := (PsiData.lEta_ge P) hN hW hWN hκ hC₀ hz hPW ht.1 ht.2
  have hLpos : 0 < P.lEta t := lt_of_lt_of_le (div_pos (hz.im_pos hN)
    (Real.sqrt_pos.mpr (by linarith))) hL
  have h1 : min 1 (P.z.im / Real.sqrt (C₀ + 1)) ≤ P.lEta t ^ Expo.lossAlpha k :=
    (min_le_min_left 1 hL).trans (min_one_le_rpow hLpos hα.1 (by linarith [hα.2]))
  exact mul_le_mul h1 hfl (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg hLpos.le _)

/-- **Floor of the `Ψ^av` normalizations** on `[0,1]`. -/
theorem normAv_floor {δ₀ κ C₀ Dpp : ℝ} {W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N)
    (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ P.D) (hz : BulkDomain N δ₀ κ C₀ P.z)
    (hPW : P.W = W) (hk : 1 ≤ k) (hkK : k ≤ vsK)
    (hDpp : (vsK : ℝ) * (2 + P.D) + 1 ≤ (vsK : ℝ) * (2 * Dpp + 1))
    (hNA : (1 + Real.sqrt (C₀ + 1)) ^ ((vsK : ℝ) * (2 + P.D)) ≤ N) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : AvIdx N k,
      min 1 (P.z.im / Real.sqrt (C₀ + 1)) * (N : ℝ) ^ (-((vsK : ℝ) * (2 * Dpp + 1))) ≤
        P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t := by
  intro t ht i
  have hfl := (P.sizes_floor_vsK hN hW hWN hκ hC₀ hD hz hPW hk hkK hDpp hNA ht.1 ht.2).2 i.2
  have hβ := lossBeta_mem (k := k) (by unfold vsK at hkK; omega)
  have hL := (PsiData.lEta_ge P) hN hW hWN hκ hC₀ hz hPW ht.1 ht.2
  have hLpos : 0 < P.lEta t := lt_of_lt_of_le (div_pos (hz.im_pos hN)
    (Real.sqrt_pos.mpr (by linarith))) hL
  have h1 : min 1 (P.z.im / Real.sqrt (C₀ + 1)) ≤ P.lEta t ^ Expo.lossBeta k :=
    (min_le_min_left 1 hL).trans (min_one_le_rpow hLpos hβ.1 hβ.2)
  exact mul_le_mul h1 hfl (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg hLpos.le _)

end PsiData

end BlockBand.Native.ErdosRiabov.Grid
