module

public import BlockBand.Native.ErdosRiabov.LLGrid.GainTail

/-!
# The grid union bound (factored) and the (LL) event at the gained level

A factored union bound over grid times and sites, and the probability bound for the complement of
the (LL) event at the gained level.

* **`grid_union_modulus_le`**: if `E ⊆ {that grid event} ∪ modulusEvent p C`, then
  `μ E ≤ (⌊N^C⌋ + 1) |ι| q + μ(modulusEvent p C)` (the grid × sites union plus the modulus);
* `llTail_gain_le`: the fixed-time tails at every `s ≤ T` at the level `llGridLevelGain(L_T)`
  (from `llGrid_tail_gain`), combined with `grid_union_le` over the grid;
* **`measure_circLLEvent_compl_le_gain_gen`**: `measure_circLLEvent_compl_le_gen`
  at the gained level `B₂ = llLevelGain d ψ ψ^av Λ_M n B ε N L_T`.
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

/-!
### The factored union bound
-/

/-- **The grid × sites union bound**.
For `C`, `T ≤ 1`, a finite
type `ι` and events `A s u` with `μ(A s u) ≤ q` for all `s ≤ T`, `u`:
`μ{∃ j, jN^{-C} ≤ T ∧ ∃ u, x ∈ A (jN^{-C}) u} ≤ (⌊N^C⌋ + 1) |ι| q`.
-/
theorem grid_union_le (μ : Measure p.SiteMatrix) (C : ℝ) (T : ℝ≥0) (hT : T ≤ 1)
    {ι : Type*} [Fintype ι] (A : ℝ≥0 → ι → Set (RingSample p)) {q : ℝ≥0∞}
    (hq : ∀ s : ℝ≥0, s ≤ T → ∀ u, driverLaw (κ := Fin (ringDim p)) μ (A s u) ≤ q) :
    driverLaw (κ := Fin (ringDim p)) μ
      {x | ∃ j : ℕ, (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T ∧
        ∃ u, x ∈ A ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) u} ≤
      ((⌊((p.n * p.W : ℕ) : ℝ) ^ C⌋₊ + 1 : ℕ) : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * q) := by
  refine Grid.measure_grid_le_mul μ C (fun _ => T) (fun _ => hT) _ fun j _ => ?_
  set sj : ℝ≥0 := (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C
  by_cases hj : sj ≤ T
  · refine (measure_mono fun x hx => ?_).trans ((measure_biUnion_finset_le Finset.univ _).trans
      ((Finset.sum_le_card_nsmul _ _ _ fun u _ => hq sj hj u).trans (le_of_eq ?_)))
    · obtain ⟨-, u, hu⟩ := hx
      exact mem_iUnion₂.2 ⟨u, Finset.mem_univ u, hu⟩
    · rw [Finset.card_univ, nsmul_eq_mul]
  · refine (measure_mono (t := (∅ : Set (RingSample p))) fun x hx => (hj hx.1).elim).trans ?_
    rw [measure_empty]
    exact zero_le

/-- **The grid × sites union bound plus the modulus event.** If
`E ⊆ {∃ j, jN^{-C} ≤ T ∧ ∃ u, x ∈ A (jN^{-C}) u} ∪ modulusEvent p C` and `μ(A s u) ≤ q` for
`s ≤ T`, then `μ E ≤ (⌊N^C⌋ + 1) |ι| q + μ(modulusEvent p C)`.
-/
theorem grid_union_modulus_le (μ : Measure p.SiteMatrix) (C : ℝ) (T : ℝ≥0) (hT : T ≤ 1)
    {ι : Type*} [Fintype ι] (A : ℝ≥0 → ι → Set (RingSample p)) {q : ℝ≥0∞}
    (hq : ∀ s : ℝ≥0, s ≤ T → ∀ u, driverLaw (κ := Fin (ringDim p)) μ (A s u) ≤ q)
    (E : Set (RingSample p))
    (hcov : E ⊆ {x | ∃ j : ℕ, (j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C ≤ T ∧
        ∃ u, x ∈ A ((j : ℝ≥0) * VS.meshPow ((p.n * p.W : ℕ) : ℝ) C) u} ∪
      Grid.modulusEvent p C) :
    driverLaw (κ := Fin (ringDim p)) μ E ≤
      ((⌊((p.n * p.W : ℕ) : ℝ) ^ C⌋₊ + 1 : ℕ) : ℝ≥0∞) * ((Fintype.card ι : ℝ≥0∞) * q) +
        driverLaw (κ := Fin (ringDim p)) μ (Grid.modulusEvent p C) :=
  (measure_mono hcov).trans ((measure_union_le _ _).trans
    (add_le_add (grid_union_le μ C T hT A hq) le_rfl))

/-!
### The gained level
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

/-- **The fixed-time tails at every `s ≤ T`, gained level `llGridLevelGain(L_T)`**:
`μ{s ≤ τ, G L_s^β s^av_s(u) ≤ llQ_s(u)} ≤ 4 exp(-N^ε/4)` (`llGrid_tail_gain` at `s` with
`L = L_T ≤ L_s`).
-/
theorem llTail_gain_le {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) {B : ℝ} (hB : 0 ≤ B)
    (hFB : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
      ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z s *
        ‖((fun x' => forcingAv P σ x' s (pathH p x s)) +
          extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p x s))) y‖ ≤
            B * P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv y s)
    (hAPF : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s : ℝ≥0, s ≤ T →
      (s : WithTop ℝ≥0) ≤ τ x → Forcing.APriori P s (pathH p x s) psiI psiA) (ε : ℝ)
    (s : ℝ≥0) (hs : s ≤ T) (u : Fin (n + 2 + 2) → Fin (p.n * p.W)) :
    driverLaw (κ := Fin (ringDim p)) μ {x | (s : WithTop ℝ≥0) ≤ τ x ∧
        llGridLevelGain d psiI psiA LamM n B ε (p.n * p.W) (P.lEta T) *
            (P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv u s) ≤
          llQ P σ s (pathH p x s) u} ≤
      4 * ENNReal.ofReal (Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ ε / 4))) := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  have hW : 0 < P.W := by rw [hPW]; exact p.W_pos
  have hzi := hz.im_pos hN
  have hflow := QV.qvFlow_of d hb hPS hPW hPD hz hP6 hT1
  have hLT : 0 < P.lEta T := P.lEta_pos hN hW hzi hT1
  have hs' : (s : ℝ) ≤ T := by exact_mod_cast hs
  have hs1 : (s : ℝ) ≤ 1 := hs'.trans hT1
  have hAP' : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ r ∈ Ioc (0 : ℝ) s,
      ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x →
        QV.APriori P psiI psiA LamM r (Evol.pathH p x r) :=
    hAP.mono fun x hx r hr hrτ => hx r ⟨hr.1, hr.2.trans hs'⟩ hrτ
  have hFB' : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ r ∈ Ioc (0 : ℝ) s,
      ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → ∀ y, vsHeight P.z r *
        ‖((fun x' => forcingAv P σ x' r (pathH p x r)) +
          extraForcingLong P.S P.z r (fun y => P.avErr σ y r (pathH p x r))) y‖ ≤
            B * P.lEta r ^ Expo.lossBeta (n + 4) * P.sAv y r :=
    hFB.mono fun x hx r hr hrτ => hx r ⟨hr.1, hr.2.trans hs'⟩ hrτ
  have hAPF' : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, (s : WithTop ℝ≥0) ≤ τ x →
      Forcing.APriori P s (pathH p x s) psiI psiA := hAPF.mono fun x hx => hx s hs
  have hLs : P.lEta T ≤ P.lEta s := hflow.anti s ⟨NNReal.coe_nonneg _, hs'⟩
  exact llGrid_tail_gain μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ s hs1 hAP' hn σ hσ u hB hFB'
    hAPF' ε hLT hLs

end Bad

/-- **The (LL) event for all `s ≤ T` at once, gained level**:
`measure_circLLEvent_compl_le_gen` with `B₂ = llLevelGain d ψ ψ^av Λ_M n B ε N L_T`
`= 2 (llCD B + N^{ε/2} llZ(L_T) + llR0Gain(L_T)) + 1`;
`N₀` depends only on `d`, `ε`, `D`.
-/
theorem measure_circLLEvent_compl_le_gain_gen (d : VSData) {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
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
          (circLLEvent P σ τ (llLevelGain d psiI psiA LamM n B ε (p.n * p.W) (P.lEta T)) T)ᶜ ≤
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
  have hG := llGridLevelGain_nonneg d hI hAv LamM hn hB ε (p.n * p.W) hLT
  have hT1' : T ≤ 1 := by exact_mod_cast hT1
  have hcov := compl_circLLEvent_subset d P hPW hPD hS hz hNz hn σ τ hG T hT1'
  have hbad := grid_union_modulus_le μ (llCg d) T hT1'
    (fun s u => {x | (s : WithTop ℝ≥0) ≤ τ x ∧
      llGridLevelGain d psiI psiA LamM n B ε (p.n * p.W) (P.lEta T) *
          (P.lEta s ^ Expo.lossBeta (n + 4) * P.sAv u s) ≤
        llQ P σ s (pathH p x s) u})
    (fun s hs u => llTail_gain_le μ d hb hPS hPW hPD hz hP6 hLam hI hAv hτ T hT1 hAP hn σ hσ hB
      hFB hAPF ε s hs u) _ hcov
  have hmod := hN₁ p μ hN1'
  have h17 := Grid.zigN0_ge d
  have hN2 : (2 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) := by linarith
  have hreal := llFinal_real_le hN2 hC0.le (k := n + 2 + 2) hn (hN₂ _ hN2').2
  refine hbad.trans ((add_le_add le_rfl hmod).trans
    (le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hreal)))
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
