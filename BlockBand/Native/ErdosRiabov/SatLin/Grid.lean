module

public import BlockBand.Native.ErdosRiabov.SatLin.Lip

/-!
# From grid times to all times: the saturated linear term

Probability: `driverLaw μ` (only in the last section).

Grid `s'_j = min((j+1)h, T)`, `j ∈ ℕ`, mesh `h > 0`: every `s ∈ (0,T]` has the grid time
`s'_j ∈ [s, s + h) ∩ (0, T]` with `j = ⌈s/h⌉ - 1` (the upper grid point, so `s'_j ≤ T`).

* `gridPt h T j = min ((j+1) h) T` (in `ℝ≥0`); `exists_gridPt`.
* **`linQ_all_of_grid`** (deterministic): for a Hermitian path `H` with
  `|(H_t - H_s)_{ab}| ≤ δ` for `s ≤ t ≤ s + h`, `t ≤ 1`, if at every grid time and for every slot
  `i`, `η |T̂^{(i)}[𝒳](u)| ≤ b L^{β_k} s^av(u)`, then for every `s ∈ (0,T]`
  `η_s |T̂^{⊕k}_s[𝒳_s](u)| ≤ (4kb + 1) L_s^{β_k} s^av_s(u)`, under the side conditions
  `1 + h/Im z ≤ 2`, `(1 + h/Im z)^E ≤ 2` and `err(h, δ) ≤ φ ≤ L^{β_k} s^av` (floor).
* `slotBad`: the failure of the slot bound at one time.
* **`satLin_measure_le`**: `P(T ≤ τ, ∃ s ∈ (0,T], (4kb+1)-bound fails) ≤ P(modulus event) +
  Σ_i P(T ≤ τ, x ∉ E_i) + Σ_{j < ⌈N^C⌉} Σ_i P(s'_j ≤ τ, x ∈ E_i, slot `i` fails at `s'_j`)`,
  for the VS band process (mesh `N^{-C}`, level `N^{-C/3}`) and any events `E_i`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open MeasureTheory Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal ComplexConjugate

/-! ### The grid -/

/-- The grid time `s'_j = min ((j+1) h, T)`. -/
def gridPt (h T : ℝ≥0) (j : ℕ) : ℝ≥0 := min (((j : ℝ≥0) + 1) * h) T

theorem gridPt_le (h T : ℝ≥0) (j : ℕ) : gridPt h T j ≤ T := min_le_right _ _

/-- Every `s ∈ (0,T]` has a grid time `s'_j ∈ [s, s + h)` with `j h < T`. -/
theorem exists_gridPt {h T : ℝ≥0} (hh : 0 < h) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) T) :
    ∃ j : ℕ, (j : ℝ) * h < T ∧ s ≤ gridPt h T j ∧ (gridPt h T j : ℝ) ≤ s + h := by
  have hh' : (0 : ℝ) < h := hh
  set c := ⌈s / (h : ℝ)⌉₊
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (Nat.ceil_pos.mpr (div_pos hs.1 hh')))
  have hc_ge : s ≤ (c : ℝ) * h := by
    have := Nat.le_ceil (s / (h : ℝ))
    rwa [div_le_iff₀ hh'] at this
  have hc_lt : (c : ℝ) * h < s + h := by
    have := Nat.ceil_lt_add_one (div_pos hs.1 hh').le
    rw [← lt_div_iff₀ hh', add_div, div_self hh'.ne']
    exact this
  refine ⟨c - 1, ?_, ?_, ?_⟩
  · have e : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub hc1, Nat.cast_one]
    rw [e]
    nlinarith [hs.2]
  · have e : (((c - 1 : ℕ) : ℝ≥0) + 1) = (c : ℝ≥0) := by
      rw [← Nat.cast_one (R := ℝ≥0), ← Nat.cast_add, Nat.sub_add_cancel hc1]
    unfold gridPt
    rw [e, NNReal.coe_min, NNReal.coe_mul, NNReal.coe_natCast]
    exact le_min hc_ge hs.2
  · have e : (((c - 1 : ℕ) : ℝ≥0) + 1) = (c : ℝ≥0) := by
      rw [← Nat.cast_one (R := ℝ≥0), ← Nat.cast_add, Nat.sub_add_cancel hc1]
    unfold gridPt
    rw [e, NNReal.coe_min, NNReal.coe_mul, NNReal.coe_natCast]
    exact (min_le_left _ _).trans hc_lt.le

/-! ### The deterministic step -/

section Det

variable {N : ℕ} (P : PsiData N) (hN : 0 < N) (hW : 0 < P.W) {δ₀ κ C₀ : ℝ}
  (hz : BulkDomain N δ₀ κ C₀ P.z) (hS : StochasticSymm P.S) (hD : 0 ≤ P.D)
include hN hW hz hS hD

/-- **Grid times to all times** (deterministic): if the slot terms of the linear term are
bounded by `b L^{β_k} s^av` at every grid time `j h < T`, then, under the modulus, floor and
error hypotheses, `linQ ≤ (4 k b + 1) L_s^{β_k} s^av_s(u)` for every `s ∈ (0, T]`. -/
theorem linQ_all_of_grid {k : ℕ} (hk : 1 ≤ k) (hk8 : k ≤ 8) (σ : Fin k → Bool)
    (u : Fin k → Fin N) (H : ℝ → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ s, (H s).IsHermitian)
    {h T : ℝ≥0} (hh : 0 < h) (hT1 : (T : ℝ) ≤ 1) {δ : ℝ}
    (hmod : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ s + h → t ≤ 1 → ∀ a b, ‖(H t - H s) a b‖ ≤ δ)
    {B : ℝ} (hB2 : 2 ≤ B) (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    {φ : ℝ} (hfl : ∀ s ∈ Icc (0 : ℝ) 1, φ ≤ P.lEta s ^ Expo.lossBeta k * P.sAv u s)
    (hq : 1 + (h : ℝ) / P.z.im ≤ 2) (hqE : (1 + (h : ℝ) / P.z.im) ^ Grid.normExp k P.D ≤ 2)
    (herr : (P.z.im + 1) * (k * (N * ((h : ℝ) * P.z.im⁻¹ ^ 2) *
        (N * (max 1 P.z.im⁻¹) ^ k + N * B ^ (2 * (k - 1) - 1)) +
        P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ h B))) ≤ φ)
    {b : ℝ} (hb : 0 ≤ b)
    (hgrid : ∀ j : ℕ, (j : ℝ) * h < T → ∀ i : Fin k,
      vsHeight P.z (gridPt h T j) *
          ‖circSlot i (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) (gridPt h T j))
            (fun y => P.avErr σ y (gridPt h T j) (H (gridPt h T j))) u‖ ≤
        b * (P.lEta (gridPt h T j) ^ Expo.lossBeta k * P.sAv u (gridPt h T j))) :
    ∀ s ∈ Ioc (0 : ℝ) T, linQ P σ s (H s) u ≤
      (4 * k * b + 1) * (P.lEta s ^ Expo.lossBeta k * P.sAv u s) := by
  intro s hs
  have hzi := hz.im_pos hN
  obtain ⟨j, hjT, hss', hs'h⟩ := exists_gridPt hh hs
  set s' : ℝ := (gridPt h T j : ℝ)
  have hs1 : s ≤ 1 := hs.2.trans hT1
  have hs'T : s' ≤ T := gridPt_le h T j
  have hs'1 : s' ≤ 1 := hs'T.trans hT1
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs1⟩
  have hs'I : s' ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le.trans hss', hs'1⟩
  have hd : |s - s'| ≤ h := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  -- the two-time comparison
  have hδ : ∀ a b, ‖(H s - H s') a b‖ ≤ δ := fun a b => by
    rw [← norm_neg, ← Matrix.neg_apply, neg_sub]
    exact hmod s s' hs.1.le hss' hs'h hs'1 a b
  have hM : ∀ y, ‖P.avErr σ y s (H s)‖ ≤ N * (max 1 P.z.im⁻¹) ^ k + N * B ^ (2 * (k - 1) - 1) :=
    fun y => LLGrid.norm_avErr_le P hzi hS σ y (hH s) hB2 hBL hsI
  have hnear := linQ_le_near P hN hz hS σ (hH s) (hH s') hδ hB2 hBL hsI hs'I hM u
  -- the grid value
  have hη' : 0 ≤ vsHeight P.z s' := (vsHeight_pos hzi hs'1).le
  have hsum := linQ_le_sum P σ hη' (H s') u
  have hgj := hgrid j hjT
  have hgrid' : linQ P σ s' (H s') u ≤ k * (b * (P.lEta s' ^ Expo.lossBeta k * P.sAv u s')) := by
    refine hsum.trans ((Finset.sum_le_sum fun i _ => hgj i).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the normalizations
  have hβ := Grid.lossBeta_mem hk8
  have hcmp : P.lEta s' ^ Expo.lossBeta k * P.sAv u s' ≤
      2 * (P.lEta s ^ Expo.lossBeta k * P.sAv u s) := by
    have h1 := Grid.PsiData.norm_le_mul P hN hW hzi hs'1 hs1 hβ.1 hβ.2
      (P.sAv_pos hN hW hzi hs'1 u).le (P.sAv_pos hN hW hzi hs1 u).le
      (Grid.PsiData.sAv_le_mul P hN hW hzi hD hk hs'1 hs1 u)
    have hE0 : 0 ≤ Grid.normExp k P.D := Grid.normExp_nonneg k hD
    have hd' : |s' - s| ≤ h := by rwa [abs_sub_comm]
    have hqq : (1 + |s' - s| / P.z.im) ^ Grid.normExp k P.D ≤ 2 := by
      refine le_trans (Real.rpow_le_rpow (by positivity) ?_ hE0) hqE
      have := div_le_div_of_nonneg_right hd' hzi.le
      linarith
    have hn0 : 0 ≤ P.lEta s ^ Expo.lossBeta k * P.sAv u s :=
      mul_nonneg (Real.rpow_nonneg (P.lEta_pos hN hW hzi hs1).le _) (P.sAv_pos hN hW hzi hs1 u).le
    exact h1.trans (mul_le_mul_of_nonneg_right hqq hn0)
  -- the error
  have hr0 : 0 ≤ P.z.im⁻¹ := inv_nonneg.2 hzi.le
  have hM0 : 0 ≤ (N : ℝ) * (max 1 P.z.im⁻¹) ^ k + N * B ^ (2 * (k - 1) - 1) := by
    have : 0 ≤ max 1 P.z.im⁻¹ := zero_le_one.trans (le_max_left _ _)
    have : 0 ≤ B := by linarith
    positivity
  have hlip : (Grid.PsiData.errLip P) k δ |s - s'| B ≤ (Grid.PsiData.errLip P) k δ h B :=
    (Grid.PsiData.errLip_mono P) k hd (by linarith)
  have herr' : (P.z.im + 1) * (k * (N * (|s - s'| * P.z.im⁻¹ ^ 2) *
      (N * (max 1 P.z.im⁻¹) ^ k + N * B ^ (2 * (k - 1) - 1)) +
        P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ |s - s'| B))) ≤ φ := by
    refine le_trans ?_ herr
    have hz1 : 0 ≤ P.z.im + 1 := by linarith
    refine mul_le_mul_of_nonneg_left ?_ hz1
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine add_le_add ?_ ?_
    · refine mul_le_mul_of_nonneg_right ?_ hM0
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hd (pow_nonneg hr0 2)
    · refine mul_le_mul_of_nonneg_left ?_ hr0
      exact mul_le_mul_of_nonneg_left hlip (Nat.cast_nonneg _)
  have hq' : 1 + |s - s'| / P.z.im ≤ 2 := by
    have := div_le_div_of_nonneg_right hd hzi.le
    linarith
  have hfls := hfl s hsI
  have hL0 : 0 ≤ linQ P σ s' (H s') u := by unfold linQ; positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hn0' : 0 ≤ P.lEta s' ^ Expo.lossBeta k * P.sAv u s' :=
    mul_nonneg (Real.rpow_nonneg (P.lEta_pos hN hW hzi hs'1).le _)
      (P.sAv_pos hN hW hzi hs'1 u).le
  have hA : (1 + |s - s'| / P.z.im) * linQ P σ s' (H s') u ≤
      2 * (k * (b * (2 * (P.lEta s ^ Expo.lossBeta k * P.sAv u s)))) := by
    have h1 : (1 + |s - s'| / P.z.im) * linQ P σ s' (H s') u ≤ 2 * linQ P σ s' (H s') u :=
      mul_le_mul_of_nonneg_right hq' hL0
    have h2 : k * (b * (P.lEta s' ^ Expo.lossBeta k * P.sAv u s')) ≤
        k * (b * (2 * (P.lEta s ^ Expo.lossBeta k * P.sAv u s))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp hb) hk0
    linarith
  calc linQ P σ s (H s) u ≤ 2 * (k * (b * (2 * (P.lEta s ^ Expo.lossBeta k * P.sAv u s)))) + φ :=
        hnear.trans (add_le_add hA herr')
    _ ≤ (4 * k * b + 1) * (P.lEta s ^ Expo.lossBeta k * P.sAv u s) := by nlinarith

end Det

/-! ### The probabilistic step -/

variable {p : BlockBand.Parameters}

/-- The failure of the slot-`i` bound at time `s`:
`b L_s^{β_k} s^av_s(u) < η_s |T̂^{(i)}_s[𝒳_s](u)|` (along the VS band process). -/
def slotBad (P : PsiData (p.n * p.W)) {k : ℕ} (σ : Fin k → Bool) (u : Fin k → Fin (p.n * p.W))
    (b : ℝ) (i : Fin k) (s : ℝ) (x : RingSample p) : Prop :=
  b * (P.lEta s ^ Expo.lossBeta k * P.sAv u s) <
    vsHeight P.z s *
      ‖circSlot i (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
        (fun y => P.avErr σ y s (Evol.pathH p x s)) u‖

/-- The modulus of the VS band process off `Grid.modulusEvent`, along `pathH`. -/
theorem pathH_modulus {C : ℝ} {x : RingSample p} (hx : x ∉ Grid.modulusEvent p C) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ s + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) → t ≤ 1 →
      ∀ a b, ‖(Evol.pathH p x t - Evol.pathH p x s) a b‖ ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-C / 3) := by
  intro s t hs0 hst hth ht1 a b
  have ht0 : 0 ≤ t := hs0.trans hst
  refine Grid.modulus_of_not_mem hx s.toNNReal t.toNNReal (Real.toNNReal_le_toNNReal hst) ?_
    (by rw [← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal ht1) a b
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0, NNReal.coe_add, Real.coe_toNNReal _ hs0]
  exact hth

/-- **The union bound of the grid step.** For the VS band process, mesh `h = N^{-C}`,
level `δ = N^{-C/3}`, the side conditions of `linQ_all_of_grid` and any events
`E_i`: the failure probability of the `(4kb+1)`-bound on `(0, T]` is at most
`P(modulus) + Σ_i P(T ≤ τ, x ∉ E_i) + Σ_{j < ⌈N^C⌉} Σ_i P(s'_j ≤ τ, x ∈ E_i, slotBad i s'_j)`. -/
theorem satLin_measure_le (μ : Measure p.SiteMatrix) (P : PsiData (p.n * p.W)) (hW : 0 < P.W)
    {δ₀ κ C₀ : ℝ} (hz : BulkDomain (p.n * p.W) δ₀ κ C₀ P.z) (hS : StochasticSymm P.S)
    (hD : 0 ≤ P.D) {k : ℕ} (hk : 1 ≤ k) (hk8 : k ≤ 8) (σ : Fin k → Bool)
    (u : Fin k → Fin (p.n * p.W)) (τ : RingSample p → WithTop ℝ≥0) (T : ℝ≥0)
    (hT1 : (T : ℝ) ≤ 1) {C : ℝ} {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B)
    {φ : ℝ} (hfl : ∀ s ∈ Icc (0 : ℝ) 1, φ ≤ P.lEta s ^ Expo.lossBeta k * P.sAv u s)
    (hq : 1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) / P.z.im ≤ 2)
    (hqE : (1 + (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) / P.z.im) ^ Grid.normExp k P.D ≤ 2)
    (herr : (P.z.im + 1) * (k * ((p.n * p.W : ℕ) *
        ((VS.meshPow ((p.n * p.W : ℕ) : ℝ) C : ℝ) * P.z.im⁻¹ ^ 2) *
        ((p.n * p.W : ℕ) * (max 1 P.z.im⁻¹) ^ k + (p.n * p.W : ℕ) * B ^ (2 * (k - 1) - 1)) +
        P.z.im⁻¹ * ((p.n * p.W : ℕ) * (Grid.PsiData.errLip P) k
          (((p.n * p.W : ℕ) : ℝ) ^ (-C / 3)) (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) B))) ≤ φ)
    {b : ℝ} (hb : 0 ≤ b) (E : Fin k → Set (RingSample p)) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧
        ¬ ∀ s ∈ Ioc (0 : ℝ) T, vsHeight P.z s *
          ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
            (fun _ => conj (semicircleM P.z)) s) (fun y => P.avErr σ y s (Evol.pathH p x s)) u‖ ≤
          (4 * k * b + 1) * (P.lEta s ^ Expo.lossBeta k * P.sAv u s)} ≤
      driverLaw (κ := Fin (ringDim p)) μ (Grid.modulusEvent p C) +
        ∑ i, driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧ x ∉ E i} +
        ∑ j ∈ Finset.range ⌈((p.n * p.W : ℕ) : ℝ) ^ C⌉₊, ∑ i,
          driverLaw (κ := Fin (ringDim p)) μ
            {x | ((gridPt (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) T j : ℝ≥0) : WithTop ℝ≥0) ≤ τ x ∧
              x ∈ E i ∧ slotBad P σ u b i (gridPt (VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) T j) x} := by
  set ν := driverLaw (κ := Fin (ringDim p)) μ
  set h := VS.meshPow ((p.n * p.W : ℕ) : ℝ) C
  set M := ⌈((p.n * p.W : ℕ) : ℝ) ^ C⌉₊
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hNR : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := VS.one_le_dim p
  have hh : 0 < h := Grid.meshPow_pos_dim p C
  have hhR : (h : ℝ) = ((p.n * p.W : ℕ) : ℝ) ^ (-C) := VS.meshPow_coe (by linarith) C
  set A : Set (RingSample p) := Grid.modulusEvent p C
  set U : Set (RingSample p) := ⋃ i, {x | (T : WithTop ℝ≥0) ≤ τ x ∧ x ∉ E i}
  set V : Set (RingSample p) := ⋃ j ∈ Finset.range M, ⋃ i,
    {x | ((gridPt h T j : ℝ≥0) : WithTop ℝ≥0) ≤ τ x ∧ x ∈ E i ∧ slotBad P σ u b i (gridPt h T j) x}
  have hsub : {x | (T : WithTop ℝ≥0) ≤ τ x ∧
      ¬ ∀ s ∈ Ioc (0 : ℝ) T, vsHeight P.z s *
        ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
          (fun _ => conj (semicircleM P.z)) s) (fun y => P.avErr σ y s (Evol.pathH p x s)) u‖ ≤
        (4 * k * b + 1) * (P.lEta s ^ Expo.lossBeta k * P.sAv u s)} ⊆ A ∪ U ∪ V := by
    intro x ⟨hτ, hfail⟩
    by_contra hno
    simp only [mem_union, not_or] at hno
    obtain ⟨⟨hA, hU⟩, hV⟩ := hno
    apply hfail
    have hE : ∀ i, x ∈ E i := fun i => by
      by_contra hxi
      exact hU (mem_iUnion.mpr ⟨i, hτ, hxi⟩)
    refine linQ_all_of_grid P hN hW hz hS hD hk hk8 σ u (Evol.pathH p x)
      (fun s => VS.vsBandFin_isHermitian _ _) hh hT1 (pathH_modulus hA) hB2 hBL hfl hq hqE
      herr hb ?_
    intro j hj i
    by_contra hbad
    push Not at hbad
    have hjM : j ∈ Finset.range M := by
      refine Finset.mem_range.mpr ?_
      have h1 : (j : ℝ) < ((p.n * p.W : ℕ) : ℝ) ^ C := by
        have hjT : (j : ℝ) * h < 1 := hj.trans_le hT1
        rw [hhR, Real.rpow_neg (by linarith), ← div_eq_mul_inv,
          div_lt_one (Real.rpow_pos_of_pos (by linarith) C)] at hjT
        exact hjT
      exact_mod_cast h1.trans_le (Nat.le_ceil _)
    refine hV (mem_iUnion₂.mpr ⟨j, hjM, mem_iUnion.mpr ⟨i, ?_, hE i, hbad⟩⟩)
    exact (WithTop.coe_le_coe.mpr (gridPt_le h T j)).trans hτ
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _)))
    ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ =>
      measure_iUnion_fintype_le _ _))))

end BlockBand.Native.ErdosRiabov.SatLin
