module

public import BlockBand.Native.ErdosRiabov.Evol.Defs
public import BlockBand.Native.ErdosRiabov.Evol.Main
public import BlockBand.Native.ErdosRiabov.Evol.Duhamel
public import BlockBand.Native.ErdosRiabov.Evol.RegSat
public import BlockBand.Native.ErdosRiabov.Evol.RegWard
public import BlockBand.Native.ErdosRiabov.MTerms.Algebra

/-!
# Unconditional corollaries for the chain evolution

The derivatives of the deterministic chains, the evolution and Duhamel equations of the chain
fluctuations and the Ward reductions, with the `Split` hypotheses discharged by the `MTerms`
proofs.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Discharge

section

open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open Set
open scoped ComplexConjugate
variable {N k : ℕ}
variable (P : PsiData N)

/-- `Evol.hasDerivAt_mChain` without its hypothesis `Split.DerivStatement` (`hD`), which is proved
as `MTerms.deriv_holds`; the other hypotheses are as in `Evol.hasDerivAt_mChain`. -/
theorem hasDerivAt_mChain_uncond (hz : P.z.im ≠ 0)
    (hS : StochasticSymm P.S) (hk : 1 ≤ k) (σ : Fin k → Bool) (x : Fin k → Fin N) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (a : Fin N) :
    HasDerivAt (fun r => P.mChain σ x r a) (mDerivP P σ x s a) s :=
  Evol.hasDerivAt_mChain (P := P) (hD := MTerms.deriv_holds) (hz := hz) (hS := hS) (hk := hk)
    (σ := σ) (x := x) (hs := hs) (a := a)

/-- `Evol.hasDerivAt_avM` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Evol.hasDerivAt_avM`. -/
theorem hasDerivAt_avM_uncond (hz : P.z.im ≠ 0) (hS : StochasticSymm P.S)
    (hk : 1 ≤ k) (σ : Fin k → Bool) (x : Fin k → Fin N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => avM P σ x r) (dMav P σ x s) s :=
  Evol.hasDerivAt_avM (P := P) (hD := MTerms.deriv_holds) (hz := hz) (hS := hS) (hk := hk) (σ := σ)
    (x := x) (hs := hs)

/-- `Evol.hasDerivAt_isoM` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Evol.hasDerivAt_isoM`. -/
theorem hasDerivAt_isoM_uncond (hz : P.z.im ≠ 0)
    (hS : StochasticSymm P.S) (hk : 1 ≤ k) (σ : Fin k → Bool) (a b : Fin N)
    (x : Fin k → Fin N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => isoM P σ a b x r) (dMiso P σ a b x s) s :=
  Evol.hasDerivAt_isoM (P := P) (hD := MTerms.deriv_holds) (hz := hz) (hS := hS) (hk := hk) (σ := σ)
    (a := a) (b := b) (x := x) (hs := hs)

end

section

open BlockBand.Native.ErdosRiabov.Evol
open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ComplexConjugate
variable {p : BlockBand.Parameters} {k : ℕ}

/-- `Evol.evol_av` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Evol.evol_av`. -/
theorem evol_av_uncond (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {P : PsiData (p.n * p.W)} (hz : 0 < P.z.im) (hS : StochasticSymm P.S)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (x : Fin k → Fin (p.n * p.W)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (avSlots P.S x) 1 ((t : ℝ), vsNoise p t ω) - (avM P σ x (min (t : ℝ) 1)).re)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) 1 t
          (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).re) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) 1 t
            (vsNoise p t ω)) ∧
      IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (avSlots P.S x) (-Complex.I • 1) ((t : ℝ), vsNoise p t ω) -
            (avM P σ x (min (t : ℝ) 1)).im)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x)
          (-Complex.I • 1) t (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).im) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x)
            (-Complex.I • 1) t (vsNoise p t ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ω : RingSample p,
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (avSlots P.S x) 1 ((t : ℝ), vsNoise p t ω) - (avM P σ x (min (t : ℝ) 1)).re =
          (P.avErr σ x t (vsBandFin p t ω)).re ∧
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (avSlots P.S x) (-Complex.I • 1) ((t : ℝ), vsNoise p t ω) -
            (avM P σ x (min (t : ℝ) 1)).im = (P.avErr σ x t (vsBandFin p t ω)).im ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) 1 t
            (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).re) t =
          (aTermAv P σ x t (vsBandFin p t ω) + forcingAv P σ x t (vsBandFin p t ω)).re ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (avSlots P.S x) (-Complex.I • 1) t
            (vsNoise p t ω) - frozenDeriv (fun s => (dMav P σ x s).im) t =
          (aTermAv P σ x t (vsBandFin p t ω) + forcingAv P σ x t (vsBandFin p t ω)).im :=
  Evol.evol_av (hD := MTerms.deriv_holds) (μ := μ) (hz := hz) (hS := hS) (hPS := hPS) (hk := hk)
    (σ := σ) (x := x)

/-- `Evol.evol_iso` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Evol.evol_iso`. -/
theorem evol_iso_uncond (μ : Measure p.SiteMatrix)
    [IsProbabilityMeasure μ] {P : PsiData (p.n * p.W)} (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a b : Fin (p.n * p.W)) (x : Fin k → Fin (p.n * p.W)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (isoSlots P.S x) (Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).re)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
          (Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).re) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (Matrix.single b a 1) t (vsNoise p t ω)) ∧
      IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
        (driverAugmented (κ := Fin (ringDim p)) μ)
        (fun t ω _ => chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
          (isoSlots P.S x) (-Complex.I • Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).im)
        (fun t ω _ => chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
          (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).im) t)
        (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
          chainBracket 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ ω : RingSample p,
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (isoSlots P.S x) (Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).re = (P.isoErr σ a b x t (vsBandFin p t ω)).re ∧
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ)
            (isoSlots P.S x) (-Complex.I • Matrix.single b a 1) ((t : ℝ), vsNoise p t ω) -
            (isoM P σ a b x (min (t : ℝ) 1)).im = (P.isoErr σ a b x t (vsBandFin p t ω)).im ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).re) t =
          (aTermIso P σ a b x t (vsBandFin p t ω) +
            forcingIso P σ a b x t (vsBandFin p t ω)).re ∧
        chainDrift 0 (vsPatternSpec P.z (semicircleM P.z) σ) (isoSlots P.S x)
            (-Complex.I • Matrix.single b a 1) t (vsNoise p t ω) -
            frozenDeriv (fun s => (dMiso P σ a b x s).im) t =
          (aTermIso P σ a b x t (vsBandFin p t ω) +
            forcingIso P σ a b x t (vsBandFin p t ω)).im :=
  Evol.evol_iso (hD := MTerms.deriv_holds) (μ := μ) (hz := hz) (hS := hS) (hPS := hPS) (hk := hk)
    (σ := σ) (a := a) (b := b) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.Evol
open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise pathwise_duhamel)
open scoped NNReal
variable {p : BlockBand.Parameters} {k : ℕ} {P : PsiData (p.n * p.W)}

/-- `Evol.duhamel_av` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Evol.duhamel_av`. -/
theorem duhamel_av_uncond (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (ω : RingSample p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.avErr σ x t (pathH p ω t)) =
      propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) 0 t)
          (fun x => P.avErr σ x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t, propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) s t)
          (fun x => forcingAv P σ x s (pathH p ω s))) +
        propagatedNoise (fun s t => propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) s t))
          (fun s => propOp (vsTensorGen P.S (muAv P σ) (muNext P σ) s))
          (fun r x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
            r.toNNReal ω) 0 t :=
  Evol.duhamel_av (hD := MTerms.deriv_holds) (hz := hz) (hPS := hPS) (hk := hk) (σ := σ) (ω := ω)
    (ht := ht)

/-- `Evol.duhamel_iso` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Evol.duhamel_iso`. -/
theorem duhamel_iso_uncond (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a b : Fin (p.n * p.W)) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.isoErr σ a b x t (pathH p ω t)) =
      propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) 0 t)
          (fun x => P.isoErr σ a b x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t, propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) s t)
          (fun x => forcingIso P σ a b x s (pathH p ω s))) +
        propagatedNoise (fun s t => propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) s t))
          (fun s => propOp (vsTensorGen P.S (muIso P σ) (muNext P σ) s))
          (fun r x => chainMg 0 (zfam P.z σ) (fun x => isoSlots P.S x)
            (fun _ => Matrix.single b a 1) x r.toNNReal ω) 0 t :=
  Evol.duhamel_iso (hD := MTerms.deriv_holds) (hz := hz) (hPS := hPS) (hk := hk) (σ := σ) (a := a)
    (b := b) (ω := ω) (ht := ht)

end

section

open BlockBand.Native.ErdosRiabov.Evol
open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise)
open scoped NNReal
variable {p : BlockBand.Parameters} {k : ℕ} {P : PsiData (p.n * p.W)}

/-- `Evol.duhamel_av_sat` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Evol.duhamel_av_sat`. -/
theorem duhamel_av_sat_uncond (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (ω : RingSample p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.avErr σ x t (pathH p ω t)) =
      (fun x => P.avErr σ x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t, fun x => aTermAv P σ x s (pathH p ω s) +
          forcingAv P σ x s (pathH p ω s)) +
        (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x t.toNNReal
          ω) :=
  Evol.duhamel_av_sat (hD := MTerms.deriv_holds) (hz := hz) (hPS := hPS) (hk := hk) (σ := σ)
    (ω := ω) (ht := ht)

end

section

open BlockBand.Native.ErdosRiabov.Evol
open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi
open scoped ComplexConjugate
variable {N n : ℕ}

/-- `Evol.ward_mChain` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement` (`hC`,
`hW`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses are as
in `Evol.ward_mChain`. -/
theorem ward_mChain_uncond (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0) (σ : Fin (n + 2) → Bool)
    (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ b, P.mChain σ x t b =
      (Split.zParam t (patM P.z σ (n + 2)) - Split.zParam t (patM P.z σ 1))⁻¹ *
        (∑ b, P.mChain (wardPatLast σ) (wardSites x) t b * obsSeq P.S (wardSites x) (n + 1) b -
          ∑ b, P.mChain (wardPatHead σ) (wardSites x) t b *
            obsSeq P.S (wardSites x) (n + 1) b) :=
  Evol.ward_mChain (hC := MTerms.cyclic_holds) (hW := MTerms.ward_holds) (P := P) (hS := hS)
    (hz := hz) (σ := σ) (hσ := hσ) (x := x) (ht := ht)

/-- `Evol.wardReduction` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hW`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `Evol.wardReduction`. -/
theorem wardReduction_uncond (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : 0 < P.z.im) (σ : Fin (n + 2) → Bool)
    (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ∑ a, P.avErr σ (update x (Fin.last (n + 1)) a) t H =
      (patZ P.z σ t (Fin.last (n + 1)) - patZ P.z σ t 0)⁻¹ *
        (P.avErr (wardPatLast σ) (wardSites x) t H -
          P.avErr (wardPatHead σ) (wardSites x) t H) :=
  Evol.wardReduction (hC := MTerms.cyclic_holds) (hW := MTerms.ward_holds) (P := P) (hS := hS)
    (hz := hz) (σ := σ) (hσ := hσ) (x := x) (ht := ht) (hH := hH)

/-- `Evol.wardReduction_norm` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hW`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `Evol.wardReduction_norm`. -/
theorem wardReduction_norm_uncond
    (P : PsiData N) (hS : StochasticSymm P.S) (hz : 0 < P.z.im) (σ : Fin (n + 2) → Bool)
    (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ‖∑ a, P.avErr σ (update x (Fin.last (n + 1)) a) t H‖ ≤
      (2 * vsHeight P.z t)⁻¹ * (‖P.avErr (wardPatLast σ) (wardSites x) t H‖ +
        ‖P.avErr (wardPatHead σ) (wardSites x) t H‖) :=
  Evol.wardReduction_norm (hC := MTerms.cyclic_holds) (hW := MTerms.ward_holds) (P := P) (hS := hS)
    (hz := hz) (σ := σ) (hσ := hσ) (x := x) (ht := ht) (hH := hH)

end

end BlockBand.Native.ErdosRiabov.Discharge
