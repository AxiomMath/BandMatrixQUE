module

public import BlockBand.Native.ErdosRiabov.QV.APriori
public import BlockBand.Native.ErdosRiabov.QV.Bracket
public import BlockBand.Native.ErdosRiabov.QV.Iso
public import BlockBand.Native.ErdosRiabov.QV.Mart
public import BlockBand.Native.ErdosRiabov.MTerms.Algebra

/-!
# Unconditional corollaries for the quadratic variation

The quadratic-variation densities and brackets of the isotropic chains and the isotropic
martingale estimates, with `Split.ExplicitShortStatement` discharged by
`MTerms.explicitShort_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Discharge

section

open BlockBand.Native.ErdosRiabov.QV
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl shortRingProfile)
open Matrix
open scoped ComplexConjugate
variable {N : ℕ}

/-- `QV.qv_mChain_two` without its hypothesis `Split.ExplicitShortStatement` (`hES`), which is
proved as `MTerms.explicitShort_holds`; the other hypotheses are as in `QV.qv_mChain_two`. -/
theorem qv_mChain_two_uncond (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (β β' : Bool) (c e a : Fin N) :
    P.mChain (qvSig β [(c, β')]) (qvSites [(c, β')] e) s a =
      VS.patConj β (semicircleM P.z) * VS.patConj β' (semicircleM P.z) *
        ∑ d, Split.stabOp s P.S (VS.patConj β (semicircleM P.z) *
          VS.patConj β' (semicircleM P.z)) a d * (P.S c d : ℂ) :=
  QV.qv_mChain_two (hES := MTerms.explicitShort_holds) (P := P) (hS := hS) (hz := hz) (hs := hs)
    (β := β) (β' := β') (c := c) (e := e) (a := a)

end

section

open BlockBand.Native.ErdosRiabov.QV
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Chains (slotList slotProd segProd firstVar)
open Expo (lossAlpha lossBeta)
open Matrix Function
open scoped ComplexConjugate
variable {N : ℕ}
variable {d : VSData} {P : PsiData N} {psiI psiA : ℕ → ℝ} {LamM s : ℝ}
  {H : Matrix (Fin N) (Fin N) ℂ} (hin : QVInputs d P s) (hA : APriori P psiI psiA LamM s H)
  (hH : H.IsHermitian) (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j) (hAv : ∀ j, 0 ≤ psiA j)
  (hL1 : 1 ≤ P.lEta s)
include hin hA hH hLam hI hAv hL1

/-- `QV.qv_iso_density` without its hypothesis `Split.ExplicitShortStatement` (`hES`), which is
proved as `MTerms.explicitShort_holds`; the other hypotheses are as in `QV.qv_iso_density`. -/
theorem qv_iso_density_uncond (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool) (x : Fin (n + 1) → Fin N)
    (j : Fin (n + 1)) (a b : Fin N) :
    qvQIso P (qvW P s H (σ 0) ((qvPairs σ x).take j)) (qvW P s H (σ j) ((qvPairs σ x).drop j))
      a b ≤ qvBndIso d P psiI psiA LamM s (n + 1) * P.sIso a b x s ^ 2 :=
  QV.qv_iso_density (hin := hin) (hA := hA) (hH := hH) (hLam := hLam) (hI := hI) (hAv := hAv)
    (hL1 := hL1) (hES := MTerms.explicitShort_holds) (hS := hS) (hz := hz) (hs := hs)
    (hstab := hstab) (hn := hn) (σ := σ) (x := x) (j := j) (a := a) (b := b)

/-- `QV.qv_bracket_iso` without its hypothesis `Split.ExplicitShortStatement` (`hES`), which is
proved as `MTerms.explicitShort_holds`; the other hypotheses are as in `QV.qv_bracket_iso`. -/
theorem qv_bracket_iso_uncond (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    {n : ℕ} (hn : n + 1 ≤ 8) (σ : Fin (n + 1) → Bool) (a' b' : Fin N)
    (c : (Fin (n + 1) → Fin N) → ℂ) :
    ∑ a, ∑ b, P.S a b * ‖∑ α, c α * Matrix.trace ((Matrix.single b' a' (1 : ℂ) :
      Matrix (Fin N) (Fin N) ℂ) * firstVar (isoSlots P.S α) (fun j => qvRes P s H (σ j))
        (Matrix.single a b (1 : ℂ)))‖ ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 * qvBndIso d P psiI psiA LamM s (n + 1) *
        (∑ α, ‖c α‖ * P.sIso a' b' α s) ^ 2 :=
  QV.qv_bracket_iso (hin := hin) (hA := hA) (hH := hH) (hLam := hLam) (hI := hI) (hAv := hAv)
    (hL1 := hL1) (hES := MTerms.explicitShort_holds) (hS := hS) (hz := hz) (hs := hs)
    (hstab := hstab) (hn := hn) (σ := σ) (a' := a') (b' := b') (c := c)

end

section

open BlockBand.Native.ErdosRiabov.QV
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open Expo (lossAlpha lossBeta)
open Matrix
open scoped ComplexConjugate
variable {N : ℕ}
variable {d : VSData} {P : PsiData N} {psiI psiA : ℕ → ℝ} {LamM s : ℝ}
  {H : Matrix (Fin N) (Fin N) ℂ} (hin : QVInputs d P s) (hA : APriori P psiI psiA LamM s H)
  (hH : H.IsHermitian) (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j) (hAv : ∀ j, 0 ≤ psiA j)
  (hL1 : 1 ≤ P.lEta s)
include hin hA hH hLam hI hAv hL1

/-- `QV.qv_QV_iso_first` without its hypothesis `Split.ExplicitShortStatement` (`hES`), which is
proved as `MTerms.explicitShort_holds`; the other hypotheses are as in `QV.qv_QV_iso_first`. -/
theorem qv_QV_iso_first_uncond (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    (β₀ : Bool) (r : List (Fin N × Bool)) (hk : r.length + 1 ≤ 8) (a b : Fin N) :
    qvQIso P (qvRes P s H β₀) (qvW P s H β₀ r) a b ≤
      qvC d * LamM ^ 3 * qvPhiIso psiI psiA (r.length + 1) (P.lEta s) ^ 2 *
        P.lEta s ^ (2 * lossAlpha (r.length + 1)) / vsHeight P.z s *
          qvIsoSq P s a (r.map Prod.fst) b :=
  QV.qv_QV_iso_first (hin := hin) (hA := hA) (hH := hH) (hLam := hLam) (hI := hI) (hAv := hAv)
    (hL1 := hL1) (hES := MTerms.explicitShort_holds) (hS := hS) (hz := hz) (hs := hs)
    (hstab := hstab) (β₀ := β₀) (r := r) (hk := hk) (a := a) (b := b)

/-- `QV.qv_QV_iso_mid` without its hypothesis `Split.ExplicitShortStatement` (`hES`), which is
proved as `MTerms.explicitShort_holds`; the other hypotheses are as in `QV.qv_QV_iso_mid`. -/
theorem qv_QV_iso_mid_uncond (hS : StochasticSymm P.S)
    (hz : P.z.im ≠ 0) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hstab : ∀ x y, ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) x y‖ ≤
      (if x = y then 1 else 0) + Propagator.vsCK d * P.ups s x y)
    (β₀ : Bool) (r₁ : List (Fin N × Bool)) (c : Fin N) (β : Bool) (r₂ : List (Fin N × Bool))
    (hk : r₁.length + r₂.length + 2 ≤ 8) (a b : Fin N) :
    qvQIso P (qvW P s H β₀ (r₁ ++ [(c, β)])) (qvW P s H β r₂) a b ≤
      qvC d * LamM ^ 3 * qvPhiIso psiI psiA (r₁.length + r₂.length + 2) (P.lEta s) ^ 2 *
        P.lEta s ^ (2 * lossAlpha (r₁.length + r₂.length + 2)) / vsHeight P.z s *
          qvIsoSq P s a (r₁.map Prod.fst ++ c :: r₂.map Prod.fst) b :=
  QV.qv_QV_iso_mid (hin := hin) (hA := hA) (hH := hH) (hLam := hLam) (hI := hI) (hAv := hAv)
    (hL1 := hL1) (hES := MTerms.explicitShort_holds) (hS := hS) (hz := hz) (hs := hs)
    (hstab := hstab) (β₀ := β₀) (r₁ := r₁) (c := c) (β := β) (r₂ := r₂) (hk := hk) (a := a) (b := b)

end

section

open BlockBand.Native.ErdosRiabov.QV
open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.CEH.Flow
open Expo (lossAlpha lossBeta)
open scoped NNReal ENNReal ComplexConjugate
variable {p : BlockBand.Parameters}
variable (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] (d : VSData)
  {P : PsiData (p.n * p.W)} (hb : d.b = p.b) (hPS : P.S = shortRingProfile p.b p.n p.W)
  (hPW : P.W = p.W) (hPD : P.D = d.D) (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  {psiI psiA : ℕ → ℝ} {LamM : ℝ} (hLam : 1 ≤ LamM) (hI : ∀ j, 1 ≤ psiI j)
  (hAv : ∀ j, 0 ≤ psiA j) {τ : RingSample p → WithTop ℝ≥0}
  (hτ : IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) τ) (T : ℝ≥0)
  (hT1 : (T : ℝ) ≤ 1)
  (hAP : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ s ∈ Ioc (0 : ℝ) T,
    ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x → APriori P psiI psiA LamM s (Evol.pathH p x s))
include hb hPS hPW hPD hz hP6 hLam hI hAv hτ hT1 hAP

/-- `QV.martingaleEstimate_iso` without its hypothesis `Split.ExplicitShortStatement` (`hES`), which
is proved as `MTerms.explicitShort_holds`; the other hypotheses are as in
`QV.martingaleEstimate_iso`. -/
theorem martingaleEstimate_iso_uncond {n : ℕ} (hn : n + 2 ≤ 8)
    (σ : Fin (n + 2) → Bool) (a' b' : Fin (p.n * p.W)) (u : Fin (n + 2) → Fin (p.n * p.W))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => isoSlots P.S y)
          (fun _ => Matrix.single b' a' 1)
          (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartIso d P psiI psiA LamM T a' b' u *
        qvIntRule d P (1 - 2 * lossAlpha (n + 2)) T))))) :=
  QV.martingaleEstimate_iso (μ := μ) (d := d) (hb := hb) (hPS := hPS) (hPW := hPW) (hPD := hPD)
    (hz := hz) (hP6 := hP6) (hLam := hLam) (hI := hI) (hAv := hAv) (hτ := hτ) (T := T) (hT1 := hT1)
    (hAP := hAP) (hES := MTerms.explicitShort_holds) (hn := hn) (σ := σ) (a' := a') (b' := b')
    (u := u) (hlam := hlam)

/-- `QV.martingaleEstimate_iso_one` without its hypothesis `Split.ExplicitShortStatement` (`hES`),
which is proved as `MTerms.explicitShort_holds`; the other hypotheses are as in
`QV.martingaleEstimate_iso_one`. -/
theorem martingaleEstimate_iso_one_uncond (σ : Fin 1 → Bool)
    (a' b' : Fin (p.n * p.W)) (u : Fin 1 → Fin (p.n * p.W)) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ x ∧
        lam ≤ ‖combMg 0 (Evol.zfam P.z σ) (fun y => isoSlots P.S y)
          (fun _ => Matrix.single b' a' 1)
          (fun α s => vsTensorProp P.S (Evol.muIso P σ) (Evol.muNext P σ) s T u α) t x‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * (qvMartIsoOne d P psiI psiA LamM T a' b' u *
        qvIntRule d P 0 T))))) :=
  QV.martingaleEstimate_iso_one (μ := μ) (d := d) (hb := hb) (hPS := hPS) (hPW := hPW) (hPD := hPD)
    (hz := hz) (hP6 := hP6) (hLam := hLam) (hI := hI) (hAv := hAv) (hτ := hτ) (T := T) (hT1 := hT1)
    (hAP := hAP) (hES := MTerms.explicitShort_holds) (σ := σ) (a' := a') (b' := b') (u := u)
    (hlam := hlam)

end

end BlockBand.Native.ErdosRiabov.Discharge
