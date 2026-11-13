module

public import BlockBand.Native.ErdosRiabov.LLGrid.Near

/-!
# The (LL) event for all `s` at once: grid, union bound and continuity

The complement of the (LL) event `circLLEvent` has probability `≤ N^{-D}`, by a union bound over a
time grid and the sites together with the modulus of continuity of the band process.

Grid `s_j = j N^{-C}`, `C = llCg d`, `N = p.n p.W`, `k = n + 4`, `G = llGridLevel(B, ε, N, L_T)`,
`B₂ = llLevel(B, ε, N, L_T) = 2G + 1`.

* `compl_circLLEvent_subset` (deterministic): `(circLLEvent B₂ T)ᶜ` is contained in the union of
  the grid events `{s_j ≤ T, ∃ u, s_j ≤ τ, G L^β s^av_{s_j}(u) ≤ llQ_{s_j}(u)}` and the modulus
  event `Grid.modulusEvent p C` (for `N ≥ zigN0 d`; `llQ_le_of_grid`);
* `measure_llBad_le`: the grid events have probability `≤ (⌊N^C⌋ + 1) N^k 4 e^{-N^ε/4}`
  (`Grid.measure_grid_le_mul`, a union over the `N^k` sites, `llGrid_tail` at each `s_j`);
* **`measure_circLLEvent_compl_le_gen`**: for every `ε > 0` and `D` there is `N₀` (depending only
  on `d`, `ε`, `D`) such that, in the setting of `Circ.circLL_tail` with the forcing bound `hFB`
  (constant `B ≥ 0` on `(0, T]`) and the forcing a priori bound `hAPF` on `[0, T]`,
  `P((circLLEvent P σ τ B₂ T)ᶜ) ≤ N^{-D}` for `N ≥ N₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LLGrid

open MeasureTheory Set Function Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open scoped NNReal ENNReal ComplexConjugate

variable {p : BlockBand.Parameters}

/-- `H_t = vsBandFin p t` at `ℝ≥0` times. -/
theorem pathH_nnreal (x : RingSample p) (t : ℝ≥0) : pathH p x t = VS.vsBandFin p t x := by
  simp [Evol.pathH]

/-!
### The deterministic cover
-/

/-- **The cover of the complement of the (LL) event** (deterministic).
For `N ≥ zigN0 d`,
`G ≥ 0`, `T ≤ 1`:
`(circLLEvent P σ τ (2G + 1) T)ᶜ ⊆ (grid events at level G) ∪ modulusEvent`.
-/
theorem compl_circLLEvent_subset (d : VSData) (P : PsiData (p.n * p.W)) (hPW : P.W = p.W)
    (hPD : P.D = d.D) (hS : StochasticSymm P.S)
    (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
    (hN0 : Grid.zigN0 d ≤ ((p.n * p.W : ℕ) : ℝ)) {n : ℕ} (hn : n + 4 ≤ 8)
    (σ : Fin (n + 2 + 2) → Bool) (τ : RingSample p → WithTop ℝ≥0) {G : ℝ} (hG : 0 ≤ G)
    (T : ℝ≥0) (hT1 : T ≤ 1) :
    (circLLEvent P σ τ (2 * G + 1) T)ᶜ ⊆
      {x | ∃ j : ℕ, (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) ≤ T ∧
        ∃ u : Fin (n + 2 + 2) → Fin (p.n * p.W),
          (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : WithTop ℝ≥0) ≤ τ x ∧
          G * (P.lEta (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ) ^
              Expo.lossBeta (n + 4) *
            P.sAv u (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ)) ≤
          llQ P σ (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ)
            (pathH p x (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ))
            u} ∪ Grid.modulusEvent p (llCg d) := by
  intro x hx
  by_cases hm : x ∈ Grid.modulusEvent p (llCg d)
  · exact Or.inr hm
  refine Or.inl ?_
  rw [mem_compl_iff, circLLEvent, mem_ofPred_eq] at hx
  push Not at hx
  obtain ⟨s, hs, hsτ, y, hlt⟩ := hx
  obtain ⟨t, rfl⟩ : ∃ t : ℝ≥0, (t : ℝ) = s := ⟨s.toNNReal, Real.coe_toNNReal s hs.1.le⟩
  rw [Real.toNNReal_coe] at hsτ
  have htT : t ≤ T := by exact_mod_cast hs.2
  set h := VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d)
  obtain ⟨hjs, hjt⟩ := Grid.PsiData.grid_point (Grid.meshPow_pos_dim p (llCg d)) t
  refine ⟨⌊t / h⌋₊, hjs.trans htT, y, (WithTop.coe_le_coe.mpr hjs).trans hsτ, ?_⟩
  by_contra hno
  push Not at hno
  rw [pathH_nnreal] at hno
  have hnear := llQ_le_of_grid d P hPW hPD hS hz hN0 hn σ hjs hjt (htT.trans hT1)
    (VS.vsBandFin_isHermitian t x) (VS.vsBandFin_isHermitian _ x)
    (Grid.modulus_of_not_mem hm _ _ hjs hjt (htT.trans hT1)) hG y hno.le
  have h2 : llQ P σ t (pathH p x t) y ≤
      (2 * G + 1) * P.lEta t ^ Expo.lossBeta (n + 4) * P.sAv y t := by
    rw [pathH_nnreal, mul_assoc]
    exact hnear
  exact lt_irrefl _ (hlt.trans_le h2)

/-!
### The union bound over the grid and the sites
-/

section Bad

variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  {psiI psiA : ℕ → ℝ} {LamM : ℝ} (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j)
  (hAv : ∀ j, 0 ≤ psiA j) {τ : RingSample p → WithTop ℝ≥0}
  (hτ : IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) τ) (T : ℝ≥0)
  (hT1 : (T : ℝ) ≤ 1)
  (hAP : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
    ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → QV.APriori P psiI psiA LamM s (Evol.pathH p x s))
include hb hPS hPW hPD hz hP6 hLam hI hAv hτ hT1 hAP

/-- **The grid events are rare**: their probability is at most
`(⌊N^C⌋ + 1) · N^k · 4 exp(-N^ε/4)` (`C = llCg d`, `k = n + 4`, level `G = llGridLevel(L_T)`).
-/
theorem measure_llBad_le {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (hAPF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s : ℝ≥0, s ≤ T →
      (s : WithTop ℝ≥0) ≤ τ x → Forcing.APriori P s (pathH p x s) psiI psiA) (ε : ℝ) :
    driverLaw (κ := Fin (ringDim p)) μ
      {x | ∃ j : ℕ, (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) ≤ T ∧
        ∃ u : Fin (n + 2 + 2) → Fin (p.n * p.W),
          (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : WithTop ℝ≥0) ≤ τ x ∧
          llGridLevel d psiI psiA LamM n B ε (p.n * p.W) (P.lEta T) *
            (P.lEta (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ) ^
              Expo.lossBeta (n + 4) *
            P.sAv u (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ)) ≤
          llQ P σ (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ)
            (pathH p x (((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d) : ℝ≥0) : ℝ))
            u} ≤
      ((⌊((p.n * p.W : ℕ) : ℝ) ^ llCg d⌋₊ + 1 : ℕ) : ℝ≥0∞) *
        ((Fintype.card (Fin (n + 2 + 2) → Fin (p.n * p.W)) : ℝ≥0∞) *
          (4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ ε / 4))))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hflow := QV.qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hLT : 0 < P.lEta T := P.lEta_pos hN hW hzi hT1
  have hT1' : T ≤ 1 := by exact_mod_cast hT1
  refine Grid.measure_grid_le_mul μ (llCg d) (fun _ => T) (fun _ => hT1') _ fun j _ => ?_
  set sj : ℝ≥0 := (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) (llCg d)
  by_cases hj : sj ≤ T
  · have hj' : (sj : ℝ) ≤ T := by exact_mod_cast hj
    have hsj1 : (sj : ℝ) ≤ 1 := hj'.trans hT1
    have hAP' : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) sj,
        ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x →
          QV.APriori P psiI psiA LamM s (Evol.pathH p x s) :=
      hAP.mono fun x hx s hs hsτ => hx s ⟨hs.1, hs.2.trans hj'⟩ hsτ
    have hFB' : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) sj,
        ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
          ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
            extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
              B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s :=
      hFB.mono fun x hx s hs hsτ => hx s ⟨hs.1, hs.2.trans hj'⟩ hsτ
    have hAPF' : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, (sj : WithTop ℝ≥0) ≤ τ x →
        Forcing.APriori P sj (pathH p x sj) psiI psiA := hAPF.mono fun x hx => hx sj hj
    have hLs : P.lEta T ≤ P.lEta sj := hflow.anti sj ⟨NNReal.coe_nonneg _, hj'⟩
    have htail := fun u => llGrid_tail μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ sj hsj1 hAP' hn σ
      hσ u hB hFB' hAPF' ε hLT hLs
    refine (measure_mono fun x hx => ?_).trans ((measure_biUnion_finset_le Finset.univ _).trans
      ((Finset.sum_le_card_nsmul _ _ _ fun u _ => htail u).trans (le_of_eq ?_)))
    · obtain ⟨-, u, hu⟩ := hx
      exact mem_iUnion₂.2 ⟨u, Finset.mem_univ u, hu⟩
    · rw [Finset.card_univ, nsmul_eq_mul]
  · refine (measure_mono (t := (∅ : Set (RingSample p))) fun x hx => (hj hx.1).elim).trans ?_
    rw [measure_empty]
    exact zero_le

end Bad

/-!
### The numerical bound
-/

/-- The final real inequality: for `N ≥ 2` with `N^{C+8+D} e^{-N^ε/4} ≤ 1/16`, `k ≤ 8`:
`(⌊N^C⌋ + 1) N^k 4 e^{-N^ε/4} + N^{-(D+1)} ≤ N^{-D}`.
-/
theorem llFinal_real_le {Nr C D ε : ℝ} (hN2 : 2 ≤ Nr) (hC : 0 ≤ C) {k : ℕ} (hk : k ≤ 8)
    (hexp : Nr ^ (C + 8 + D) * Real.exp (-(1 / 4) * Nr ^ ε) ≤ 1 / 16) :
    ((⌊Nr ^ C⌋₊ : ℝ) + 1) * (Nr ^ k * (4 * Real.exp (-(Nr ^ ε / 4)))) + Nr ^ (-(D + 1)) ≤
      Nr ^ (-D) := by
  have hN0 : 0 < Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  set e := Real.exp (-(Nr ^ ε / 4)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he' : Real.exp (-(1 / 4) * Nr ^ ε) = e := by rw [he]; congr 1; ring
  rw [he'] at hexp
  have hC1 : 1 ≤ Nr ^ C := Real.one_le_rpow hN1 hC
  have hfl : (⌊Nr ^ C⌋₊ : ℝ) + 1 ≤ 2 * Nr ^ C := by
    have := Nat.floor_le (le_trans zero_le_one hC1)
    linarith
  have hk' : Nr ^ k ≤ Nr ^ (8 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by exact_mod_cast hk)
  have hsplit : Nr ^ (C + 8 + D) = Nr ^ C * Nr ^ (8 : ℝ) * Nr ^ D := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hD : Nr ^ (-D) * Nr ^ D = 1 := by
    rw [← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have hDpos : 0 < Nr ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hmain : Nr ^ C * Nr ^ (8 : ℝ) * e ≤ Nr ^ (-D) / 16 := by
    rw [hsplit] at hexp
    calc Nr ^ C * Nr ^ (8 : ℝ) * e = Nr ^ (-D) * (Nr ^ C * Nr ^ (8 : ℝ) * Nr ^ D * e) := by
          rw [show Nr ^ (-D) * (Nr ^ C * Nr ^ (8 : ℝ) * Nr ^ D * e) =
            (Nr ^ (-D) * Nr ^ D) * (Nr ^ C * Nr ^ (8 : ℝ) * e) by ring, hD, one_mul]
      _ ≤ Nr ^ (-D) * (1 / 16) := by gcongr
      _ = Nr ^ (-D) / 16 := by ring
  have h1 : ((⌊Nr ^ C⌋₊ : ℝ) + 1) * (Nr ^ k * (4 * e)) ≤ Nr ^ (-D) / 2 := by
    have hpk : 0 ≤ Nr ^ k := by positivity
    calc ((⌊Nr ^ C⌋₊ : ℝ) + 1) * (Nr ^ k * (4 * e))
        ≤ (2 * Nr ^ C) * (Nr ^ (8 : ℝ) * (4 * e)) := by gcongr
      _ = 8 * (Nr ^ C * Nr ^ (8 : ℝ) * e) := by ring
      _ ≤ 8 * (Nr ^ (-D) / 16) := by gcongr
      _ = Nr ^ (-D) / 2 := by ring
  have h2 : Nr ^ (-(D + 1)) ≤ Nr ^ (-D) / 2 := by
    rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have : Nr⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hN2
    calc Nr ^ (-D) * Nr⁻¹ ≤ Nr ^ (-D) * (1 / 2) := mul_le_mul_of_nonneg_left this hDpos.le
      _ = Nr ^ (-D) / 2 := by ring
  linarith

/-!
### The main estimate
-/

/-- **The (LL) event for all `s ≤ T` at once.** For every `d : VSData`, `ε > 0` and `D` there
is `N₀`
(depending only on `d`, `ε`, `D`) such that for every ring `p` with `N = p.n p.W ≥ N₀`, every law
`μ` of the old state, every `P` and `z ∈ 𝒟` with the VS side conditions of `Circ.circLL_tail`,
every thresholds `ψ ≥ 1`, `ψ^av ≥ 0`, `Λ_M ≥ 1`, stopping time `τ`, deterministic `T ≤ 1` with
the a priori bound `QV.APriori` on `(0, T] ∩ [0, τ]`, every `k = n + 4 ≤ 8`, saturated `σ`,
forcing constant `B ≥ 0` with `hFB` on `(0, T] ∩ [0, τ]` and the a priori bound
`Forcing.APriori` (`hAPF`) on `[0, T] ∩ [0, τ]`:
`P((circLLEvent P σ τ B₂ T)ᶜ) ≤ N^{-D}`, `B₂ = llLevel d ψ ψ^av Λ_M n B ε N L_T`
`= 2 (llCD B + N^{ε/2} llZ(L_T) + R₀) + 1`.
-/
theorem measure_circLLEvent_compl_le_gen (d : VSData) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∃ N₀ : ℝ, ∀ (p : BlockBand.Parameters) (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
      (P : PsiData (p.n * p.W)), d.b = p.b → P.S = shortRingProfile p.b p.n p.W → P.W = p.W →
      P.D = d.D → BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ {psiI psiA : ℕ → ℝ} {LamM : ℝ}, 1 ≤ LamM → (∀ j, 1 ≤ psiI j) → (∀ j, 0 ≤ psiA j) →
      ∀ {τ : RingSample p → WithTop ℝ≥0},
        IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) τ →
      ∀ T : ℝ≥0, (T : ℝ) ≤ 1 →
      (∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
        ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x →
          QV.APriori P psiI psiA LamM s (Evol.pathH p x s)) →
      ∀ {n : ℕ}, n + 4 ≤ 8 → ∀ σ : Fin (n + 2 + 2) → Bool, ¬ HasDesatFactor σ →
      ∀ {B : ℝ}, 0 ≤ B →
      (∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
        ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
          ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
            extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
              B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s) →
      (∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s : ℝ≥0, s ≤ T →
        (s : WithTop ℝ≥0) ≤ τ x → Forcing.APriori P s (pathH p x s) psiI psiA) →
      N₀ ≤ ((p.n * p.W : ℕ) : ℝ) →
      driverLaw (κ := Fin (ringDim p)) μ
          (circLLEvent P σ τ (llLevel d psiI psiA LamM n B ε (p.n * p.W) (P.lEta T)) T)ᶜ ≤
        ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨hC0, -, -, -⟩ := llCg_facts d
  obtain ⟨N₁, hN₁⟩ := Grid.modulusEvent_whp hC0 (D + 1)
  obtain ⟨N₂, hN₂⟩ := VS.exists_rpow_mul_exp_le (s := llCg d + 8 + D) (a := ε) (b := 1 / 4)
    (ε := 1 / 16) hε (by norm_num) (by norm_num)
  refine ⟨max (max N₁ N₂) (Grid.zigN0 d), fun p μ _ P hb hPS hPW hPD hz hP6 psiI psiA LamM hLam
    hI hAv τ hτ T hT1 hAP n hn σ hσ B hB hFB hAPF hN => ?_⟩
  have hNz : Grid.zigN0 d ≤ ((p.n * p.W : ℕ) : ℝ) := (le_max_right _ _).trans hN
  have hN1' : N₁ ≤ ((p.n * p.W : ℕ) : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hN2' : N₂ ≤ ((p.n * p.W : ℕ) : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNpos : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hNpos
  have hS : StochasticSymm P.S := hPS ▸ Evol.stochasticSymm_ring p
  have hLT : 0 < P.lEta T := P.lEta_pos hNpos hW hzi hT1
  have hG := llGridLevel_nonneg d hI hAv LamM hn hB ε (p.n * p.W) hLT
  have hT1' : T ≤ 1 := by exact_mod_cast hT1
  have hcov := compl_circLLEvent_subset d P hPW hPD hS hz hNz hn σ τ hG T hT1'
  have hbad := measure_llBad_le μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ hσ hB
    hFB hAPF ε
  have hmod := hN₁ p μ hN1'
  have h17 := Grid.zigN0_ge d
  have hN2 : (2 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hreal := llFinal_real_le hN2 hC0.le (k := n + 2 + 2) hn (hN₂ _ hN2').2
  refine (measure_mono hcov).trans ((measure_union_le _ _).trans
    ((add_le_add hbad hmod).trans (le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hreal))))
  have he0 : 0 ≤ Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ ε / 4)) := (Real.exp_pos _).le
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ENNReal.ofReal_add (by positivity)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
    ENNReal.ofReal_one, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat]
  push_cast
  ring

end BlockBand.Native.ErdosRiabov.LLGrid
