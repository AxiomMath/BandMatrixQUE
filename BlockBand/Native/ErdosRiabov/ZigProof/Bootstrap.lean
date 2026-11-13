module

public import BlockBand.Native.ErdosRiabov.ZigProof.MasterIneq
public import BlockBand.Native.ErdosRiabov.Grid.Zig
public import BlockBand.Native.ErdosRiabov.Assembly.LocalLaw
public import BlockBand.Native.ErdosRiabov.Kernel.VSKernel

/-!
# The zig bootstrap from the master inequalities `MasterIneqConclusion`

The fixed-time master inequalities imply the conclusion of the zig step, by a union bound over
the indices, the grid-to-uniform step and the hitting property of `τ`.

Setting: `d : VSData`, a ring `p` (`N = p.n * p.W`), `driverLaw model.law`, `H_t = vsBandFin p t`,
`P = zigPsiData p d.D z`, `τ = zigTau p d z`, master-inequality levels
`X_k = miLevelIso/miLevelAv d C N k`.
* (2) `measure_le_tau_iso_le`, `measure_le_tau_av_le`: at a fixed time `t`,
  `P(t ≤ τ ∧ X < Ψ_{k,t}) ≤ |indices| · ε` from per-index bounds `ε` (empty for `t > 1`); with
  `Grid.PsiData.gridToUniform_iso_tau`, `Grid.PsiData.gridToUniform_av_tau` this bounds
  `P(∃ t ≤ τ, 2X_k + N^{-1} < Ψ_{k,t})`.
* (3)–(4) `zigBad_subset` (pathwise): if `2X_k + N^{-1} < ψ_k` for all `k`, the zig bad event
  at `N^{ξ+ε}` lies in `⋃_k {∃ t ≤ τ, 2X_k + N^{-1} < Ψ_{k,t}}` (iso or av): off this union
  `τ = 1` by the hitting property `Psi.exists_ge_at_tau`, and then
  `Ψ_{k,t} < ψ_k ≤ N^{ξ+ε}` on `[0,1]` (`VSData.vsThreshold_facts`).
* `ennreal_count_le`, `final_real_le`: the union bound and `N₀` (constant `8208`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.ZigProof

open MeasureTheory Set
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Assembly
open BlockBand.Native.ErdosRiabov.Grid (vsCg vsCg_facts)
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

variable {p : BlockBand.Parameters}

/-!
### (2) A fixed time: union over the indices
-/

/-- **Fixed time, isotropic.** If every isotropic index has
`P(t ≤ τ ∧ X < isoRatio i t H_t) ≤ ε` (when `t ≤ 1`), then
`P(t ≤ τ ∧ X < Ψ^iso_{k,t}(H_t)) ≤ |IsoIdx N k| · ε` (`X ≥ 0`; for `t > 1` the event is empty,
since `τ ≤ 1`).
-/
theorem measure_le_tau_iso_le (μ : Measure p.SiteMatrix) (P : PsiData (p.n * p.W))
    (psiI psiA : ℕ → ℝ) {k : ℕ} {X : ℝ} (hX : 0 ≤ X) {ε : ℝ≥0∞} (t : ℝ≥0)
    (hMI : t ≤ 1 → ∀ i : IsoIdx (p.n * p.W) k, driverLaw (κ := Fin (ringDim p)) μ
      {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
        X < P.isoRatio i t (VS.vsBandFin p t x)} ≤ ε) :
    driverLaw (κ := Fin (ringDim p)) μ
        {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.bigPsiIso k t (VS.vsBandFin p t x)} ≤
      (Fintype.card (IsoIdx (p.n * p.W) k) : ℝ≥0∞) * ε := by
  by_cases ht : t ≤ 1
  · have hsub : {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.bigPsiIso k t (VS.vsBandFin p t x)} ⊆
        ⋃ i : IsoIdx (p.n * p.W) k, {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.isoRatio i t (VS.vsBandFin p t x)} := by
      rintro x ⟨hxt, hx⟩
      obtain ⟨i, hi⟩ := exists_lt_isoRatio P hX hx
      exact mem_iUnion.2 ⟨i, hxt, hi⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ _ fun i _ => hMI ht i).trans ?_
    rw [Finset.card_univ, nsmul_eq_mul]
  · have hsub : {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.bigPsiIso k t (VS.vsBandFin p t x)} ⊆ ∅ := fun x hx =>
        absurd (WithTop.coe_le_coe.mp (hx.1.trans (tau_le_one P psiI psiA x))) ht
    exact (measure_mono hsub).trans (by rw [measure_empty]; exact zero_le)

/-- **Fixed time, averaged.** As `measure_le_tau_iso_le` for `Ψ^av` and `AvIdx`. -/
theorem measure_le_tau_av_le (μ : Measure p.SiteMatrix) (P : PsiData (p.n * p.W))
    (psiI psiA : ℕ → ℝ) {k : ℕ} {X : ℝ} (hX : 0 ≤ X) {ε : ℝ≥0∞} (t : ℝ≥0)
    (hMI : t ≤ 1 → ∀ i : AvIdx (p.n * p.W) k, driverLaw (κ := Fin (ringDim p)) μ
      {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
        X < P.avRatio i t (VS.vsBandFin p t x)} ≤ ε) :
    driverLaw (κ := Fin (ringDim p)) μ
        {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.bigPsiAv k t (VS.vsBandFin p t x)} ≤
      (Fintype.card (AvIdx (p.n * p.W) k) : ℝ≥0∞) * ε := by
  by_cases ht : t ≤ 1
  · have hsub : {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.bigPsiAv k t (VS.vsBandFin p t x)} ⊆
        ⋃ i : AvIdx (p.n * p.W) k, {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.avRatio i t (VS.vsBandFin p t x)} := by
      rintro x ⟨hxt, hx⟩
      obtain ⟨i, hi⟩ := exists_lt_avRatio P hX hx
      exact mem_iUnion.2 ⟨i, hxt, hi⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ _ fun i _ => hMI ht i).trans ?_
    rw [Finset.card_univ, nsmul_eq_mul]
  · have hsub : {x | (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x ∧
          X < P.bigPsiAv k t (VS.vsBandFin p t x)} ⊆ ∅ := fun x hx =>
        absurd (WithTop.coe_le_coe.mp (hx.1.trans (tau_le_one P psiI psiA x))) ht
    exact (measure_mono hsub).trans (by rw [measure_empty]; exact zero_le)

/-!
### (3)–(4) `τ = 1` and the zig event, pathwise
-/

/-- **Steps (3)–(4), pathwise.** If `2X^iso_k + N^{-1} < ψ^iso_k` and
`2X^av_k + N^{-1} < ψ^av_k` for all `k ∈ [1,8]`, then the zig bad event at `N^{ξ+ε}` lies in
`⋃_k ({∃ t ≤ τ, 2X^iso_k + N^{-1} < Ψ^iso_{k,t}} ∪ {∃ t ≤ τ, 2X^av_k + N^{-1} < Ψ^av_{k,t}})`.
Off this union all `Ψ_{k,t} < ψ_k` for `t ≤ τ`;
`τ < 1` would contradict the hitting property
`exists_ge_at_tau`, so `τ = 1`, and `Ψ_{k,t} < ψ_k ≤ N^{ξ+ε}` on `[0,1]`
(`VSData.vsThreshold_facts`). Every sample.
-/
theorem zigBad_subset (d : VSData) (z : ℂ) (XI XA : ℕ → ℝ) (hN : 0 < p.n * p.W)
    (hz : 0 < z.im) (hS : StochasticSymm (zigPsiData p d.D z).S)
    (hI : ∀ k ∈ kRange,
      2 * XI k + ((p.n * p.W : ℕ) : ℝ)⁻¹ < zigPsiI d (p.n * p.W) k)
    (hA : ∀ k ∈ kRange,
      2 * XA k + ((p.n * p.W : ℕ) : ℝ)⁻¹ < zigPsiA d (p.n * p.W) k) :
    zigBad p d.D z (((p.n * p.W : ℕ) : ℝ) ^ (d.xi + d.eps)) ⊆
      ⋃ k ∈ kRange,
        ({x | ∃ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
            2 * XI k + ((p.n * p.W : ℕ) : ℝ)⁻¹ <
              (zigPsiData p d.D z).bigPsiIso k t (VS.vsBandFin p t x)} ∪
          {x | ∃ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
            2 * XA k + ((p.n * p.W : ℕ) : ℝ)⁻¹ <
              (zigPsiData p d.D z).bigPsiAv k t (VS.vsBandFin p t x)}) := by
  rintro x ⟨t, ht1, k, hk, hbad⟩
  by_contra hx
  have hbI : ∀ k ∈ kRange, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ zigTau p d z x →
      (zigPsiData p d.D z).bigPsiIso k s (VS.vsBandFin p s x) < zigPsiI d (p.n * p.W) k := by
    intro k hk s hs
    by_contra hc
    exact hx (mem_iUnion₂.2 ⟨k, hk, Or.inl ⟨s, hs, lt_of_lt_of_le (hI k hk) (not_lt.1 hc)⟩⟩)
  have hbA : ∀ k ∈ kRange, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ zigTau p d z x →
      (zigPsiData p d.D z).bigPsiAv k s (VS.vsBandFin p s x) < zigPsiA d (p.n * p.W) k := by
    intro k hk s hs
    by_contra hc
    exact hx (mem_iUnion₂.2 ⟨k, hk, Or.inr ⟨s, hs, lt_of_lt_of_le (hA k hk) (not_lt.1 hc)⟩⟩)
  have hτ : ¬ zigTau p d z x < ((1 : ℝ≥0) : WithTop ℝ≥0) := by
    intro hlt
    obtain ⟨s, hs, -, k, hk, h⟩ := exists_ge_at_tau (P := zigPsiData p d.D z) hN p.W_pos hz hS
      (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) x hlt
    rcases h with h | h
    · exact absurd h (not_le.2 (hbI k hk s hs.le))
    · exact absurd h (not_le.2 (hbA k hk s hs.le))
  have ht : (t : WithTop ℝ≥0) ≤ zigTau p d z x :=
    (WithTop.coe_le_coe.2 ht1).trans (not_lt.1 hτ)
  have hk1 : (k : ℝ) ≤ (vsK : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
  obtain ⟨-, -, hIA, -, -, -, -, htop⟩ :=
    d.vsThreshold_facts hN (Nat.cast_nonneg k) (le_refl (k : ℝ))
  have hAtop := htop hk1
  rcases hbad with h | h
  · have h1 := hbI k hk t ht
    exact absurd (h.trans h1) (not_lt.2 (hIA.trans hAtop))
  · have h1 := hbA k hk t ht
    exact absurd (h.trans h1) (not_lt.2 hAtop)

/-!
### Arithmetic of the union bound
-/

/-- `M · (c · ofReal x) + ofReal y ≤ ofReal (A B x + y)` for `M ≤ A`, `c ≤ B`. -/
theorem ennreal_count_le {M c : ℕ} {x y A B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hM : (M : ℝ) ≤ A) (hc : (c : ℝ) ≤ B) :
    (M : ℝ≥0∞) * ((c : ℝ≥0∞) * ENNReal.ofReal x) + ENNReal.ofReal y ≤
      ENNReal.ofReal (A * B * x + y) := by
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_natCast c,
    ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hM0,
    ← ENNReal.ofReal_add (mul_nonneg hM0 (mul_nonneg hc0 hx)) hy]
  apply ENNReal.ofReal_le_ofReal
  have h1 : (c : ℝ) * x ≤ B * x := mul_le_mul_of_nonneg_right hc hx
  have h2 : (M : ℝ) * ((c : ℝ) * x) ≤ A * (B * x) :=
    mul_le_mul hM h1 (mul_nonneg hc0 hx) (hM0.trans hM)
  nlinarith

/-- The final real inequality: with `T = 2N^{C_g} · 256 N^{10} · N^{-(D₁+C_g+11)} + N^{-(D₁+1)}`,
`8 (T + T) ≤ N^{-D₁}` for `N ≥ 8208`. -/
theorem final_real_le {N Cg D₁ : ℝ} (hN : 8208 ≤ N) :
    ((8 : ℕ) : ℝ) * ((2 * N ^ Cg * (256 * N ^ (10 : ℝ)) * N ^ (-(D₁ + Cg + 11)) +
        N ^ (-(D₁ + 1))) + (2 * N ^ Cg * (256 * N ^ (10 : ℝ)) * N ^ (-(D₁ + Cg + 11)) +
        N ^ (-(D₁ + 1)))) ≤ N ^ (-D₁) := by
  have hN0 : 0 < N := by linarith
  have e : N ^ Cg * N ^ (10 : ℝ) * N ^ (-(D₁ + Cg + 11)) = N ^ (-(D₁ + 1)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have e2 : N ^ (-(D₁ + 1)) = N ^ (-D₁) * N⁻¹ := by
    rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have hT : 2 * N ^ Cg * (256 * N ^ (10 : ℝ)) * N ^ (-(D₁ + Cg + 11)) + N ^ (-(D₁ + 1)) =
      513 * (N ^ (-D₁) * N⁻¹) := by
    calc 2 * N ^ Cg * (256 * N ^ (10 : ℝ)) * N ^ (-(D₁ + Cg + 11)) + N ^ (-(D₁ + 1))
        = 512 * (N ^ Cg * N ^ (10 : ℝ) * N ^ (-(D₁ + Cg + 11))) + N ^ (-(D₁ + 1)) := by ring
      _ = 513 * (N ^ (-D₁) * N⁻¹) := by rw [e, e2]; ring
  rw [hT]
  have hP : 0 < N ^ (-D₁) := Real.rpow_pos_of_pos hN0 _
  have hinv : 8208 * N⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN0]
    exact hN
  push_cast
  nlinarith

/-!
### The zig conclusion
-/

/-- **The zig proposition from the fixed-time master inequalities.**
`MasterIneqConclusion → ZigConclusion`. For `d : VSData` and `D₁ > 0`: the MI hypothesis at
`D = D₁ + C_g + 11` (`C_g = vsCg d`) gives `C`, `N₀^MI`; the grid lemmas
`Grid.PsiData.gridToUniform_iso_tau`, `Grid.PsiData.gridToUniform_av_tau` at `D' = D₁ + 1` give
`N₀^iso`, `N₀^av`; `exists_margin_threshold` gives `N₀^m`;
`N₀ = max(N₀^MI, ⌈N₀^iso⌉, ⌈N₀^av⌉, ⌈N₀^m⌉, 8208)`. Then `ζ₀ < 1`
(`band_hyp_false_of_one_le_zeta0`), the margin `2X_k + N^{-1} < ψ_k` (`margin_lt`), the pathwise
inclusion `zigBad_subset` (steps (3)–(4)), the grid step and the fixed-time union (step (2)), and
`P(zigBad) ≤ 8208 N^{-D₁-1} ≤ N^{-D₁}`. The steps refer to the module docstring.
-/
theorem zigConclusion_of_masterIneq (hMI : MasterIneqConclusion) : ZigConclusion := by
  intro d D₁ hD₁
  have hCg0 : 0 ≤ vsCg d := (vsCg_facts d).2.2
  obtain ⟨C, hC, N₁, hN₁⟩ := hMI d (D₁ + vsCg d + 11) (by linarith)
  obtain ⟨NI, hNI⟩ := Grid.PsiData.gridToUniform_iso_tau d (D₁ + 1)
  obtain ⟨NA, hNA⟩ := Grid.PsiData.gridToUniform_av_tau d (D₁ + 1)
  obtain ⟨R, hR⟩ := exists_margin_threshold C d.nu_pos
  refine ⟨max (max N₁ ⌈NI⌉₊) (max ⌈NA⌉₊ (max ⌈R⌉₊ 8208)),
    fun p hpb hN hband model z hz => ?_⟩
  -- the size conditions
  have hN1 : N₁ ≤ p.n * p.W := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNIc : ⌈NI⌉₊ ≤ p.n * p.W := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNAc : ⌈NA⌉₊ ≤ p.n * p.W := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hRc : ⌈R⌉₊ ≤ p.n * p.W :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have h8c : 8208 ≤ p.n * p.W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNIr : NI ≤ ((p.n * p.W : ℕ) : ℝ) := (Nat.le_ceil NI).trans (by exact_mod_cast hNIc)
  have hNAr : NA ≤ ((p.n * p.W : ℕ) : ℝ) := (Nat.le_ceil NA).trans (by exact_mod_cast hNAc)
  have hRr : R ≤ ((p.n * p.W : ℕ) : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hRc)
  have h8r : (8208 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast h8c
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hNR1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hNR0 : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hζ : d.zeta0 < 1 := by
    by_contra h
    exact band_hyp_false_of_one_le_zeta0 p (not_lt.1 h) hband
  have hzim : 0 < z.im := hz.im_pos hNpos
  have hS : StochasticSymm (zigPsiData p d.D z).S :=
    shortRingProfile_stochasticSymm p.b_pos p.b_lt_half (by have := p.n_ge_four; omega)
      p.W_pos
  -- the margin
  have hbig := hR _ hRr
  have hXI0 : ∀ k : ℕ, 0 ≤ miLevelIso d C (p.n * p.W) k := fun k => by
    unfold miLevelIso VSData.psiIso
    positivity
  have hXA0 : ∀ k : ℕ, 0 ≤ miLevelAv d C (p.n * p.W) k := fun k => by
    unfold miLevelAv VSData.psiAv
    positivity
  have hI : ∀ k ∈ kRange, 2 * miLevelIso d C (p.n * p.W) k + ((p.n * p.W : ℕ) : ℝ)⁻¹ <
      zigPsiI d (p.n * p.W) k := fun k hk =>
    margin_lt hNR1 d.xi_pos.le d.nu_pos hC
      (rpow_le_psi (d := d) hNpos (Finset.mem_Icc.mp hk).1).1 hbig
  have hA : ∀ k ∈ kRange, 2 * miLevelAv d C (p.n * p.W) k + ((p.n * p.W : ℕ) : ℝ)⁻¹ <
      zigPsiA d (p.n * p.W) k := fun k hk =>
    margin_lt hNR1 d.xi_pos.le d.nu_pos hC
      (rpow_le_psi (d := d) hNpos (Finset.mem_Icc.mp hk).1).2 hbig
  -- the real bound `T` of each of the 16 terms
  set T : ℝ := 2 * ((p.n * p.W : ℕ) : ℝ) ^ vsCg d *
      (256 * ((p.n * p.W : ℕ) : ℝ) ^ (10 : ℝ)) *
      ((p.n * p.W : ℕ) : ℝ) ^ (-(D₁ + vsCg d + 11)) +
    ((p.n * p.W : ℕ) : ℝ) ^ (-(D₁ + 1)) with hT
  have hMle : ((⌊((p.n * p.W : ℕ) : ℝ) ^ vsCg d⌋₊ + 1 : ℕ) : ℝ) ≤
      2 * ((p.n * p.W : ℕ) : ℝ) ^ vsCg d := by
    have h1 : (1 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) ^ vsCg d := Real.one_le_rpow hNR1 hCg0
    have h2 := Nat.floor_le (le_trans zero_le_one h1)
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hx0 : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-(D₁ + vsCg d + 11)) := Real.rpow_nonneg hNR0.le _
  have hy0 : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (-(D₁ + 1)) := Real.rpow_nonneg hNR0.le _
  -- per-level bounds
  have hEI : ∀ k ∈ kRange, driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
      {x | ∃ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
        2 * miLevelIso d C (p.n * p.W) k + ((p.n * p.W : ℕ) : ℝ)⁻¹ <
          (zigPsiData p d.D z).bigPsiIso k t (VS.vsBandFin p t x)} ≤ ENNReal.ofReal T := by
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hk8 : k ≤ 8 := (Finset.mem_Icc.mp hk).2
    have hj : ∀ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ vsCg d⌋₊ + 1),
        driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
          {x | (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                WithTop ℝ≥0) ≤ zigTau p d z x ∧
            miLevelIso d C (p.n * p.W) k < (zigPsiData p d.D z).bigPsiIso k
              (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) : ℝ)
              (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d)) x)} ≤
          (Fintype.card (IsoIdx (p.n * p.W) k) : ℝ≥0∞) *
            ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-(D₁ + vsCg d + 11))) :=
      fun j _ => measure_le_tau_iso_le (model.law : Measure p.SiteMatrix) (zigPsiData p d.D z)
        (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (hXI0 k) _
        fun ht i => (hN₁ p hpb hN1 hζ hband model z hz _ ht k hk).1 i
    refine (hNI p (model.law : Measure p.SiteMatrix) (zigPsiData p d.D z) (zigPsiData p d.D z)
      (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) rfl rfl hS hz hk1 hk8 (hXI0 k)
      hNIr).trans ?_
    refine (add_le_add (Finset.sum_le_card_nsmul _ _ _ hj) le_rfl).trans ?_
    rw [Finset.card_range, nsmul_eq_mul]
    exact ennreal_count_le hx0 hy0 hMle (card_isoIdx_le hNpos hk8)
  have hEA : ∀ k ∈ kRange, driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
      {x | ∃ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ zigTau p d z x ∧
        2 * miLevelAv d C (p.n * p.W) k + ((p.n * p.W : ℕ) : ℝ)⁻¹ <
          (zigPsiData p d.D z).bigPsiAv k t (VS.vsBandFin p t x)} ≤ ENNReal.ofReal T := by
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hk8 : k ≤ 8 := (Finset.mem_Icc.mp hk).2
    have hj : ∀ j ∈ Finset.range (⌊((p.n * p.W : ℕ) : ℝ) ^ vsCg d⌋₊ + 1),
        driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
          {x | (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) :
                WithTop ℝ≥0) ≤ zigTau p d z x ∧
            miLevelAv d C (p.n * p.W) k < (zigPsiData p d.D z).bigPsiAv k
              (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d) : ℝ≥0) : ℝ)
              (VS.vsBandFin p ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (vsCg d)) x)} ≤
          (Fintype.card (AvIdx (p.n * p.W) k) : ℝ≥0∞) *
            ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-(D₁ + vsCg d + 11))) :=
      fun j _ => measure_le_tau_av_le (model.law : Measure p.SiteMatrix) (zigPsiData p d.D z)
        (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) (hXA0 k) _
        fun ht i => (hN₁ p hpb hN1 hζ hband model z hz _ ht k hk).2 i
    refine (hNA p (model.law : Measure p.SiteMatrix) (zigPsiData p d.D z) (zigPsiData p d.D z)
      (zigPsiI d (p.n * p.W)) (zigPsiA d (p.n * p.W)) rfl rfl hS hz hk1 hk8 (hXA0 k)
      hNAr).trans ?_
    refine (add_le_add (Finset.sum_le_card_nsmul _ _ _ hj) le_rfl).trans ?_
    rw [Finset.card_range, nsmul_eq_mul]
    exact ennreal_count_le hx0 hy0 hMle (card_avIdx_le hNpos hk8)
  -- the union bound
  refine (measure_mono (zigBad_subset d z (miLevelIso d C (p.n * p.W))
    (miLevelAv d C (p.n * p.W)) hNpos hzim hS hI hA)).trans ?_
  refine (measure_biUnion_finset_le kRange _).trans ?_
  refine (Finset.sum_le_sum fun k hk => (measure_union_le _ _).trans
    (add_le_add (hEI k hk) (hEA k hk))).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal T + ENNReal.ofReal T)
    fun k _ => le_rfl).trans ?_
  have hT0 : 0 ≤ T := by
    rw [hT]
    have : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ vsCg d := Real.rpow_nonneg hNR0.le _
    have : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (10 : ℝ) := Real.rpow_nonneg hNR0.le _
    positivity
  rw [card_kRange, nsmul_eq_mul, ← ENNReal.ofReal_add hT0 hT0, ← ENNReal.ofReal_natCast 8,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg 8)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hT]
  exact final_real_le (Cg := vsCg d) h8r

/-- **The short-ring local law from the master inequalities.** The statement
`BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw` from `MasterIneqConclusion`, via
`zigConclusion_of_masterIneq` and `Assembly.shortRingLocalLaw_of_zigConclusion`. -/
theorem shortRingLocalLaw_of_masterIneq (hMI : MasterIneqConclusion) :
    BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  shortRingLocalLaw_of_zigConclusion (zigConclusion_of_masterIneq hMI)

end BlockBand.Native.ErdosRiabov.ZigProof
