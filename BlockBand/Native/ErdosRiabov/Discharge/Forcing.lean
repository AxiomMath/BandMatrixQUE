module

public import BlockBand.Native.ErdosRiabov.Forcing.Cyc
public import BlockBand.Native.ErdosRiabov.Forcing.Main
public import BlockBand.Native.ErdosRiabov.MTerms.Algebra

/-!
# Unconditional corollaries for the forcing

The cyclic-rotation lemmas and the averaged forcing bound `forcing_av_uncond`, with
`Split.CyclicStatement` discharged by `MTerms.cyclic_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Discharge

section

open BlockBand.Native.ErdosRiabov.Forcing
open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)
variable {N k : ℕ}
variable (P : PsiData N) (t : ℝ)

/-- `Forcing.cycT_step` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved as
`MTerms.cyclic_holds`; the other hypotheses are as in `Forcing.cycT_step`. -/
theorem cycT_step_uncond (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {r : ℕ} (hr : 2 ≤ r) (σ' : Fin r → Bool)
    (w : Fin r → Fin N) :
    cycT P t σ' w ⟨r - 1, by omega⟩ =
      cycT P t (rotK (r - 1) σ') (rotK (r - 1) w) ⟨r - 1, by omega⟩ :=
  Forcing.cycT_step (P := P) (t := t) (hC := MTerms.cyclic_holds) (hS := hS) (hz := hz) (ht0 := ht0)
    (ht1 := ht1) (hr := hr) (σ' := σ') (w := w)

/-- `Forcing.cycT_rotK` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved as
`MTerms.cyclic_holds`; the other hypotheses are as in `Forcing.cycT_rotK`. -/
theorem cycT_rotK_uncond (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {r : ℕ} (hr : 2 ≤ r) (σ' : Fin r → Bool) (w : Fin r → Fin N)
    (s : ℕ) :
    cycT P t σ' w ⟨r - 1, by omega⟩ = cycT P t (rotK s σ') (rotK s w) ⟨r - 1, by omega⟩ :=
  Forcing.cycT_rotK (P := P) (t := t) (hC := MTerms.cyclic_holds) (hS := hS) (hz := hz) (ht0 := ht0)
    (ht1 := ht1) (hr := hr) (σ' := σ') (w := w) (s := s)

end

section

open BlockBand.Native.ErdosRiabov.Forcing
open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)
variable {N k : ℕ}
variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

/-- `Forcing.bMav_cyc` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved as
`MTerms.cyclic_holds`; the other hypotheses are as in `Forcing.bMav_cyc`. -/
theorem bMav_cyc_uncond (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {i j : Fin k} (hij : i < j) (q : Fin N) :
    bMav P σ x t i j q =
      ∑ a, P.mChain (glueRotPat σ i j) (glueRot x i j q) t a * (P.S q a : ℂ) :=
  Forcing.bMav_cyc (P := P) (σ := σ) (x := x) (t := t) (hC := MTerms.cyclic_holds) (hS := hS)
    (hz := hz) (ht0 := ht0) (ht1 := ht1) (hij := hij) (q := q)

end

section

open BlockBand.Native.ErdosRiabov.Forcing
open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)
variable {N k : ℕ}
variable {d : VSData} {P : PsiData N} {t : ℝ} (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
  {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA)
  (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (σ : Fin k → Bool) (x : Fin k → Fin N)
include c hAP hpsi1

/-- `Forcing.pair_avFM1` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved as
`MTerms.cyclic_holds`; the other hypotheses are as in `Forcing.pair_avFM1`. -/
theorem pair_avFM1_uncond (hk : k ≤ 8) {I : ℕ → ℝ}
    (hI : ∀ n ∈ kRange, IsoBAt P t n (I n)) (hI0 : ∀ n, 0 ≤ I n) {i j : Fin k} (hij : i < j) :
    vsHeight P.z t * ‖∑ q, (aG P σ t H (avSlots P.S x) i j q - aM P σ x t i j q) *
        bMav P σ x t i j q‖ ≤
      d.Cwc * I (k - ((j : ℕ) - i) + 1) * (psiA ((j : ℕ) - i + 1) *
          P.lEta t ^ (-(lossBeta k - lossBeta ((j : ℕ) - i + 1)))) *
        (P.lEta t ^ lossBeta k * P.sAv x t) :=
  Forcing.pair_avFM1 (c := c) (hAP := hAP) (hpsi1 := hpsi1) (σ := σ) (x := x)
    (hC := MTerms.cyclic_holds) (hk := hk) (hI := hI) (hI0 := hI0) (hij := hij)

end

section

open BlockBand.Native.ErdosRiabov.Forcing
open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)
variable {N k : ℕ}
variable {d : VSData} {P : PsiData N} {t : ℝ} (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
  {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA)
  (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) {I : ℕ → ℝ} (hI : ∀ n ∈ kRange, IsoBAt P t n (I n))
  (hI0 : ∀ n, 0 ≤ I n)
include c hAP hpsi1 hI hI0

/-- `Forcing.forcing_av` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved as
`MTerms.cyclic_holds`; the other hypotheses are as in `Forcing.forcing_av`. -/
theorem forcing_av_uncond {e : ℝ} (he0 : 0 ≤ e)
    (hE : 2 ≤ k → k ≤ 7 → ExtraBAt P t k e) (hk1 : 1 ≤ k) (hk : k ≤ 8) (σ : Fin k → Bool)
    (x : Fin k → Fin N) :
    vsHeight P.z t * ‖forcingAv P σ x t H‖ ≤
      avConst d I e k * (P.lEta t ^ lossBeta k * P.sAv x t) *
        phiAvF psiI psiA (P.lEta t) (yScale P t) k :=
  Forcing.forcing_av (c := c) (hAP := hAP) (hpsi1 := hpsi1) (hI := hI) (hI0 := hI0)
    (hC := MTerms.cyclic_holds) (he0 := he0) (hE := hE) (hk1 := hk1) (hk := hk) (σ := σ) (x := x)

end

end BlockBand.Native.ErdosRiabov.Discharge
