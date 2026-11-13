module

public import BlockBand.Native.ErdosRiabov.Psi.Zero
public import BlockBand.Native.ErdosRiabov.Psi.Tau
public import BlockBand.Native.ErdosRiabov.Psi.TauFacts
public import BlockBand.Native.ErdosRiabov.MTerms.Algebra

/-!
# Unconditional corollaries for the control quantities

The control quantities vanish at time zero, the stopping time is positive, and the control
bounds hold up to the stopping time, with `Split.ZeroStatement` discharged by
`MTerms.zero_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Discharge

section

open BlockBand.Native.ErdosRiabov.Psi.PsiData
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open Matrix
open scoped ComplexConjugate NNReal
variable {N k : ℕ}
variable (P : PsiData N)

/-- `Psi.PsiData.isoErr_zero` without its hypothesis `Split.ZeroStatement` (`hZ`), which is proved
as `MTerms.zero_holds`; the other hypotheses are as in `Psi.PsiData.isoErr_zero`. -/
theorem isoErr_zero_uncond (hk : 1 ≤ k) (σ : Fin k → Bool) (a b : Fin N)
    (x : Fin k → Fin N) : P.isoErr σ a b x 0 0 = 0 :=
  Psi.PsiData.isoErr_zero (P := P) (hZ := MTerms.zero_holds) (hk := hk) (σ := σ) (a := a) (b := b)
    (x := x)

/-- `Psi.PsiData.avErr_zero` without its hypothesis `Split.ZeroStatement` (`hZ`), which is proved as
`MTerms.zero_holds`; the other hypotheses are as in `Psi.PsiData.avErr_zero`. -/
theorem avErr_zero_uncond (hk : 1 ≤ k) (σ : Fin k → Bool)
    (x : Fin k → Fin N) : P.avErr σ x 0 0 = 0 :=
  Psi.PsiData.avErr_zero (P := P) (hZ := MTerms.zero_holds) (hk := hk) (σ := σ) (x := x)

/-- `Psi.PsiData.bigPsiIso_zero` without its hypothesis `Split.ZeroStatement` (`hZ`), which is
proved as `MTerms.zero_holds`; the other hypotheses are as in `Psi.PsiData.bigPsiIso_zero`. -/
theorem bigPsiIso_zero_uncond (hk : 1 ≤ k) : P.bigPsiIso k 0 0 = 0 :=
  Psi.PsiData.bigPsiIso_zero (P := P) (hZ := MTerms.zero_holds) (hk := hk)

/-- `Psi.PsiData.bigPsiAv_zero` without its hypothesis `Split.ZeroStatement` (`hZ`), which is proved
as `MTerms.zero_holds`; the other hypotheses are as in `Psi.PsiData.bigPsiAv_zero`. -/
theorem bigPsiAv_zero_uncond (hk : 1 ≤ k) : P.bigPsiAv k 0 0 = 0 :=
  Psi.PsiData.bigPsiAv_zero (P := P) (hZ := MTerms.zero_holds) (hk := hk)

end

section

open BlockBand.Native.ErdosRiabov.Psi
open MeasureTheory Filter Topology Set
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal
variable {N : ℕ}
variable (p : BlockBand.Parameters)
variable {p}

/-- `Psi.excessProc_zero` without its hypothesis `Split.ZeroStatement` (`hZ`), which is proved as
`MTerms.zero_holds`; the other hypotheses are as in `Psi.excessProc_zero`. -/
theorem excessProc_zero_uncond {P : PsiData (p.n * p.W)}
    {psiI psiA : ℕ → ℝ} (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k)
    (x : RingSample p) : excessProc p P psiI psiA 0 x < 0 :=
  Psi.excessProc_zero (p := p) (hZ := MTerms.zero_holds) (hI := hI) (hA := hA) (x := x)

/-- `Psi.tau_pos` without its hypothesis `Split.ZeroStatement` (`hZ`), which is proved as
`MTerms.zero_holds`; the other hypotheses are as in `Psi.tau_pos`. -/
theorem tau_pos_uncond {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W)
    (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S) {psiI psiA : ℕ → ℝ}
    (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k) (x : RingSample p) :
    0 < tau p P psiI psiA x :=
  Psi.tau_pos (p := p) (hZ := MTerms.zero_holds) (hN := hN) (hW := hW) (hz := hz) (hS := hS)
    (hI := hI) (hA := hA) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.Psi
open MeasureTheory Filter Topology Set
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal
variable {N : ℕ}
variable {p : BlockBand.Parameters}

/-- `Psi.bigPsi_le_of_le_tau_of_zero` without its hypothesis `Split.ZeroStatement` (`hZ`), which is
proved as `MTerms.zero_holds`; the other hypotheses are as in `Psi.bigPsi_le_of_le_tau_of_zero`. -/
theorem bigPsi_le_of_le_tau_of_zero_uncond {P : PsiData (p.n * p.W)}
    (hN : 0 < p.n * p.W) (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S)
    {psiI psiA : ℕ → ℝ} (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k)
    (x : RingSample p) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x) :
    ∀ k ∈ kRange, P.bigPsiIso k t (vsBandFin p t x) ≤ psiI k ∧
      P.bigPsiAv k t (vsBandFin p t x) ≤ psiA k :=
  Psi.bigPsi_le_of_le_tau_of_zero (hZ := MTerms.zero_holds) (hN := hN) (hW := hW) (hz := hz)
    (hS := hS) (hI := hI) (hA := hA) (x := x) (ht := ht)

end

end BlockBand.Native.ErdosRiabov.Discharge
