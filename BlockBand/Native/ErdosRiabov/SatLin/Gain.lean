module

public import BlockBand.Native.ErdosRiabov.SatLin.Bridge
public import BlockBand.Native.ErdosRiabov.LLGrid.GainBound

/-!
# `LLGridHyp` from the gain-keeping (LL) level; `MI.MasterIneqSat` without hypotheses

Probability: `driverLaw model.law`.

* **`llGridHyp_holds`**: `LLGridHyp`, from `LLGrid.measure_circLLEvent_compl_le_gain_of_le` at
  `ε = ε'/4` with `B₂ = N^{ε'/4} φ^{av}_{k,T}`, using `LLGrid.llLevelGainP7_le`
  (`llLevelGainP7 ≤ N^{ε'/8} llGainA ℓ^{504} φ`) and `A ℓ^{757} ≤ N^{ε'/8}` for
  `N ≥ absorbN0 A 757 (ε'/8)`, `A = Σ_{n ≤ 4} |llGainA d n|`. Covers `k = 4, …, 8`.
* `llGridHyp8_holds`: the `k = 8` case (`LLGridHyp8`).
* **`masterIneqSat`**: `MI.MasterIneqSat` (no hypotheses).
* **`shortRingLocalLaw_of_satLin`**: `Inputs.ShortRingLocalLaw` through
  `MI.shortRingLocalLaw_of_masterIneqSat`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open MeasureTheory Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.MI (logL)
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.ZigProof (zigTau)
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

/-- **`LLGridHyp` holds** (gain-keeping level of the LLGrid repair, `k = 4, …, 8`). -/
theorem llGridHyp_holds : LLGridHyp := by
  intro d D hD
  have hε := d.epsP_pos
  obtain ⟨N₄, hN₄⟩ := LLGrid.measure_circLLEvent_compl_le_gain_of_le d D hD (d.epsP / 4)
    (by positivity)
  set A := ∑ n ∈ Finset.range 5, |LLGrid.llGainA d n|
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => abs_nonneg _
  refine ⟨max N₄ ⌈MI.absorbN0 A 757 (d.epsP / 8)⌉₊,
    fun p hpb hN hζ hband model z hz T hT n hn σ hσ => ?_⟩
  have hN4 : N₄ ≤ p.n * p.W := le_of_max_le_left hN
  have hNA : MI.absorbN0 A 757 (d.epsP / 8) ≤ ((p.n * p.W : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hN)
  have hT1 : (T : ℝ) ≤ 1 := by exact_mod_cast hT
  have hN0' : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast MI.mi_N_pos p
  have hℓ := MI.mi_logL_one (p := p)
  have hl := one_le_pow₀ hℓ (n := 757)
  have hAbs : A * logL (p.n * p.W) ^ 757 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) := by
    have := MI.absorb_of_logL (by positivity) hA0 le_rfl (by positivity) hNA
      (F := A * logL (p.n * p.W) ^ 757) (M := 0)
    unfold MI.Absorb at this
    rw [mul_zero, add_zero] at this
    exact this
  have hGA : LLGrid.llGainA d n ≤ A := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun n => |LLGrid.llGainA d n|) (fun n _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega)))
  have hlev := LLGrid.llLevelGainP7_le d hz hT1 hn (ε := d.epsP / 4) (by positivity)
  obtain ⟨-, -, hφ1⟩ := phiT_facts d hz hT1 (k := n + 4) (by omega) hn
  have hφ0 : 0 ≤ phiT d p z T (n + 4) := by linarith
  have e1 : ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4 / 2) = ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) := by
    congr 1; ring
  have e2 : ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) * ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) =
      ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4) := by
    rw [← Real.rpow_add hN0']; congr 1; ring
  have hl504 : logL (p.n * p.W) ^ 504 ≤ logL (p.n * p.W) ^ 757 :=
    pow_le_pow_right₀ hℓ (by norm_num)
  have hG : LLGrid.llGainA d n * logL (p.n * p.W) ^ 504 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) := by
    have h1 : LLGrid.llGainA d n * logL (p.n * p.W) ^ 504 ≤ A * logL (p.n * p.W) ^ 504 :=
      mul_le_mul_of_nonneg_right hGA (by positivity)
    have h2 : A * logL (p.n * p.W) ^ 504 ≤ A * logL (p.n * p.W) ^ 757 :=
      mul_le_mul_of_nonneg_left hl504 hA0
    linarith
  have hB₂ : LLGrid.llLevelGainP7 d p z n (d.epsP / 4) T ≤
      ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4) * phiT d p z T (n + 4) := by
    refine hlev.trans ?_
    rw [e1, ← e2]
    have hs0 : 0 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8) := Real.rpow_nonneg hN0'.le _
    have h3 := mul_le_mul_of_nonneg_left hG hs0
    have h4 := mul_le_mul_of_nonneg_right h3 hφ0
    exact h4
  refine (measure_mono ?_).trans (hN₄ p hpb hN4 hband model z hz T hT hn σ hσ _ hB₂)
  intro x hx
  exact hx.2

/-- The `k = 8` case: `LLGridHyp8` holds. -/
theorem llGridHyp8_holds : LLGridHyp8 := by
  intro d D hD
  obtain ⟨N₀, hN₀⟩ := llGridHyp_holds d D hD
  exact ⟨N₀, fun p hpb hN hζ hband model z hz T hT σ hσ =>
    hN₀ p hpb hN hζ hband model z hz T hT (n := 4) (by norm_num) σ hσ⟩

/-- **The saturated part of the master inequality, without hypotheses.**
`MI.MasterIneqSat` from `masterIneqSat_of_LL` and `llGridHyp_holds`. -/
theorem masterIneqSat : MI.MasterIneqSat := masterIneqSat_of_LL llGridHyp_holds

/-- **The short-ring local law** `Inputs.ShortRingLocalLaw` through
`MI.shortRingLocalLaw_of_masterIneqSat` and `masterIneqSat`. -/
theorem shortRingLocalLaw_of_satLin : BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  MI.shortRingLocalLaw_of_masterIneqSat masterIneqSat

end BlockBand.Native.ErdosRiabov.SatLin
