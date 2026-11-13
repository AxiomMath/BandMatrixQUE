module

public import BlockBand.Native.ErdosRiabov.Circ.CircEvol
public import BlockBand.Native.ErdosRiabov.Circ.LongSat
public import BlockBand.Native.ErdosRiabov.Circ.LongLinear
public import BlockBand.Native.ErdosRiabov.Circ.ExtraForcing
public import BlockBand.Native.ErdosRiabov.Circ.LongExtra
public import BlockBand.Native.ErdosRiabov.Circ.LongWard
public import BlockBand.Native.ErdosRiabov.MTerms.Algebra

/-!
# Unconditional corollaries for the regularized chains

The equations and deterministic bounds of the regularized chains (`circEvol_*`,
`duhamel_av_sat_*`, `linTerm_evol*`, `extraForcing_*`, the Ward reductions) with the `Split`
hypotheses discharged by the `MTerms` proofs.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Discharge

section

open BlockBand.Native.ErdosRiabov.Circ
open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.SourceProcess.FiniteDriverIntegration
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise)
open scoped NNReal ComplexConjugate
variable {p : BlockBand.Parameters} {P : PsiData (p.n * p.W)}

/-- `Circ.circEvol_short` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Circ.circEvol_short`. -/
theorem circEvol_short_uncond (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩ (fun x => P.avErr σ x t (pathH p ω t)) =
      propOp (goodProp P.S P.z (fun _ => .sat) 0 t)
          (ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
            (fun x => P.avErr σ x 0 (pathH p ω 0))) +
        (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
          (ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
            ((fun x => forcingAv P σ x s (pathH p ω s)) +
              extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p ω s))))) +
        propagatedNoise (fun s t => propOp (goodProp P.S P.z (fun _ => .sat) s t))
          (fun s => propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
            (fun _ => conj (semicircleM P.z)) s))
          (fun r => propOp (circShortMat P.S P.z t)
            (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
              r.toNNReal ω)) 0 t :=
  Circ.circEvol_short (hD := MTerms.deriv_holds) (hz := hz) (hPS := hPS) (σ := σ) (hσ := hσ)
    (ω := ω) (ht := ht)

/-- `Circ.circEvol_long` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Circ.circEvol_long`. -/
theorem circEvol_long_uncond (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
        (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
          (fun x => P.avErr σ x t (pathH p ω t))) =
      propOp (goodProp P.S P.z (fun _ => .sat) 0 t)
          (ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
            (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
              (fun x => P.avErr σ x 0 (pathH p ω 0)))) +
        (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
          (ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
            (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
              ((fun x => forcingAv P σ x s (pathH p ω s)) +
                extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p ω s)))))) +
        propagatedNoise (fun s t => propOp (goodProp P.S P.z (fun _ => .sat) s t))
          (fun s => propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
            (fun _ => conj (semicircleM P.z)) s))
          (fun r => propOp (circLongMat P.S P.z t)
            (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
              r.toNNReal ω)) 0 t :=
  Circ.circEvol_long (hD := MTerms.deriv_holds) (hz := hz) (hPS := hPS) (σ := σ) (hσ := hσ) (ω := ω)
    (ht := ht)

/-- `Circ.circ_avErr_pathH_zero` without its hypothesis `Split.ZeroStatement` (`hZ`), which is
proved as `MTerms.zero_holds`; the other hypotheses are as in `Circ.circ_avErr_pathH_zero`. -/
theorem circ_avErr_pathH_zero_uncond {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool)
    (ω : RingSample p) : (fun x => P.avErr σ x 0 (pathH p ω 0)) = 0 :=
  Circ.circ_avErr_pathH_zero (hZ := MTerms.zero_holds) (hk := hk) (σ := σ) (ω := ω)

/-- `Circ.circEvol_short_combMg` without its hypotheses `Split.DerivStatement`,
`Split.ZeroStatement` (`hD`, `hZ`), which are proved as `MTerms.deriv_holds`, `MTerms.zero_holds`;
the other hypotheses are as in `Circ.circEvol_short_combMg`. -/
theorem circEvol_short_combMg_uncond (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
      ∀ u : Sites p (n + 2),
        ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
            (fun x => P.avErr σ x t (pathH p ω t)) u =
          (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
            (ringOp P.S P.z t (Fin.last (n + 1)) ⟨n, by omega⟩
              ((fun x => forcingAv P σ x s (pathH p ω s)) +
                extraForcingShort P.S P.z s (fun y => P.avErr σ y s (pathH p ω s))))) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α s => ((goodProp P.S P.z (fun _ => .sat) s t * circShortMat P.S P.z t :
              Matrix (Sites p (n + 2)) (Sites p (n + 2)) ℂ)) u α)
            t ω :=
  Circ.circEvol_short_combMg (μ₀ := μ₀) (hD := MTerms.deriv_holds) (hZ := MTerms.zero_holds)
    (hz := hz) (hPS := hPS) (σ := σ) (hσ := hσ)

/-- `Circ.circEvol_long_combMg` without its hypotheses `Split.DerivStatement`, `Split.ZeroStatement`
(`hD`, `hZ`), which are proved as `MTerms.deriv_holds`, `MTerms.zero_holds`; the other hypotheses
are as in `Circ.circEvol_long_combMg`. -/
theorem circEvol_long_combMg_uncond (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
      ∀ u : Sites p (n + 2 + 2),
        ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
            (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
              (fun x => P.avErr σ x t (pathH p ω t))) u =
          (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (fun _ => .sat) s t)
            (ringOp P.S P.z t ⟨n + 1, by omega⟩ ⟨n, by omega⟩
              (ringOp P.S P.z t (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩
                ((fun x => forcingAv P σ x s (pathH p ω s)) +
                  extraForcingLong P.S P.z s (fun y => P.avErr σ y s (pathH p ω s)))))) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α s => ((goodProp P.S P.z (fun _ => .sat) s t * circLongMat P.S P.z t :
              Matrix (Sites p (n + 2 + 2)) (Sites p (n + 2 + 2)) ℂ)) u α)
            t ω :=
  Circ.circEvol_long_combMg (μ₀ := μ₀) (hD := MTerms.deriv_holds) (hZ := MTerms.zero_holds)
    (hz := hz) (hPS := hPS) (σ := σ) (hσ := hσ)

end

section

open BlockBand.Native.ErdosRiabov.Circ
open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ComplexConjugate
variable {p : BlockBand.Parameters} {k : ℕ} {P : PsiData (p.n * p.W)}

/-- `Circ.duhamel_av_sat_tensor` without its hypothesis `Split.DerivStatement` (`hD`), which is
proved as `MTerms.deriv_holds`; the other hypotheses are as in `Circ.duhamel_av_sat_tensor`. -/
theorem duhamel_av_sat_tensor_uncond (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.avErr σ x t (pathH p ω t)) =
      (fun x => P.avErr σ x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t,
          propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
              (fun y => P.avErr σ y s (pathH p ω s)) +
            fun x => forcingAv P σ x s (pathH p ω s)) +
        (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x t.toNNReal
          ω) :=
  Circ.duhamel_av_sat_tensor (hD := MTerms.deriv_holds) (hz := hz) (hPS := hPS) (hk := hk) (σ := σ)
    (hσ := hσ) (ω := ω) (ht := ht)

/-- `Circ.duhamel_av_sat_combMg` without its hypotheses `Split.DerivStatement`,
`Split.ZeroStatement` (`hD`, `hZ`), which are proved as `MTerms.deriv_holds`, `MTerms.zero_holds`;
the other hypotheses are as in `Circ.duhamel_av_sat_combMg`. -/
theorem duhamel_av_sat_combMg_uncond (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ u : Sites p k,
      P.avErr σ u t (pathH p ω t) =
        (∫ s in (0 : ℝ)..t,
          propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
              (fun y => P.avErr σ y s (pathH p ω s)) +
            fun x => forcingAv P σ x s (pathH p ω s)) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α _ => if α = u then (1 : ℂ) else 0) t ω :=
  Circ.duhamel_av_sat_combMg (μ₀ := μ₀) (hD := MTerms.deriv_holds) (hZ := MTerms.zero_holds)
    (hz := hz) (hPS := hPS) (hk := hk) (σ := σ) (hσ := hσ)

end

section

open BlockBand.Native.ErdosRiabov.Circ
open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.SourceProcess.FiniteDriverIntegration
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise)
open scoped NNReal ComplexConjugate
variable {p : BlockBand.Parameters} {P : PsiData (p.n * p.W)}

/-- `Circ.linTerm_evol` without its hypothesis `Split.DerivStatement` (`hD`), which is proved as
`MTerms.deriv_holds`; the other hypotheses are as in `Circ.linTerm_evol`. -/
theorem linTerm_evol_uncond (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    circSlot (Fin.last (n + 2 + 1)) (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
        (fun x => P.avErr σ x t (pathH p ω t)) =
      propOp (goodProp P.S P.z (linFactor n) 0 t)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
            (fun x => P.avErr σ x 0 (pathH p ω 0))) +
        (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (linFactor n) s t)
          (circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
            ((fun x => forcingAv P σ x s (pathH p ω s)) +
              circSlot ⟨n + 1, by omega⟩
                (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
                (fun y => P.avErr σ y s (pathH p ω s))))) +
        propagatedNoise (fun s t => propOp (goodProp P.S P.z (linFactor n) s t))
          (fun s => propOp (vsTensorGen P.S (fun i => (linFactor n i).mu1 P.z)
            (fun i => (linFactor n i).mu2 P.z) s))
          (fun r => propOp (circLinMat P.S P.z t)
            (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
              r.toNNReal ω)) 0 t :=
  Circ.linTerm_evol (hD := MTerms.deriv_holds) (hz := hz) (hPS := hPS) (σ := σ) (hσ := hσ) (ω := ω)
    (ht := ht)

/-- `Circ.linTerm_evol_combMg` without its hypotheses `Split.DerivStatement`, `Split.ZeroStatement`
(`hD`, `hZ`), which are proved as `MTerms.deriv_holds`, `MTerms.zero_holds`; the other hypotheses
are as in `Circ.linTerm_evol_combMg`. -/
theorem linTerm_evol_combMg_uncond (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
      ∀ u : Sites p (n + 2 + 2),
        circSlot (Fin.last (n + 2 + 1))
            (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
            (fun x => P.avErr σ x t (pathH p ω t)) u =
          (∫ s in (0 : ℝ)..t, propOp (goodProp P.S P.z (linFactor n) s t)
            (circSlot (Fin.last (n + 2 + 1))
              (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t)
              ((fun x => forcingAv P σ x s (pathH p ω s)) +
                circSlot ⟨n + 1, by omega⟩
                  (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
                  (fun y => P.avErr σ y s (pathH p ω s))))) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α s => ((goodProp P.S P.z (linFactor n) s t * circLinMat P.S P.z t :
              Matrix (Sites p (n + 2 + 2)) (Sites p (n + 2 + 2)) ℂ)) u α)
            t ω :=
  Circ.linTerm_evol_combMg (μ₀ := μ₀) (hD := MTerms.deriv_holds) (hZ := MTerms.zero_holds)
    (hz := hz) (hPS := hPS) (σ := σ) (hσ := hσ)

end

section

open BlockBand.Native.ErdosRiabov.Circ
open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate
variable {N : ℕ}

/-- `Circ.circ_traceLast_le` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hWd`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `Circ.circ_traceLast_le`. -/
theorem circ_traceLast_le_uncond
    (P : PsiData N) (hS : StochasticSymm P.S) (hz : 0 < P.z.im) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hL : 0 < P.lEta s) (hsa : 0 < P.sAv (wardSites x) s) :
    ‖∑ b, P.avErr σ (update x (Fin.last (n + 1)) b) s H‖ ≤
      (vsHeight P.z s)⁻¹ * (P.bigPsiAv (n + 1) s H *
        (P.lEta s ^ Expo.lossBeta (n + 1) * P.sAv (wardSites x) s)) :=
  Circ.circ_traceLast_le (hC := MTerms.cyclic_holds) (hWd := MTerms.ward_holds) (P := P) (hS := hS)
    (hz := hz) (σ := σ) (hσ := hσ) (x := x) (hs := hs) (hH := hH) (hL := hL) (hsa := hsa)

/-- `Circ.extraForcing_two` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hWd`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `Circ.extraForcing_two`. -/
theorem extraForcing_two_uncond
    (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W)) (hPW : P.W = W)
    (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
    (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z) (σ : Fin 2 → Bool)
    (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) (x : Fin 2 → Fin (m * W)) :
    vsHeight P.z s * ‖extraForcingShort (n := 0) P.S P.z s (fun y => P.avErr σ y s H) x‖ ≤
      2 * vsCK d * P.bigPsiAv 1 s H * P.lEta s ^ Expo.lossBeta 1 * P.sAv x s :=
  Circ.extraForcing_two (hC := MTerms.cyclic_holds) (hWd := MTerms.ward_holds) (d := d) (hm := hm)
    (hW := hW) (P := P) (hPW := hPW) (hPD := hPD) (hPS := hPS) (hz := hz) (σ := σ) (hσ := hσ)
    (hs := hs) (hH := hH) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.Circ
open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate
variable {N : ℕ}
variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W)) (hPW : P.W = W)
  (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
include hm hW hPW hPD hPS hz

/-- `Circ.extraForcing_long` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hWd`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `Circ.extraForcing_long`. -/
theorem extraForcing_long_uncond {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian)
    (x : Fin (n + 2 + 2) → Fin (m * W)) :
    vsHeight P.z s * ‖extraForcingLong (n := n) P.S P.z s (fun y => P.avErr σ y s H) x‖ ≤
      4 * vsCK d * Real.sqrt d.C1pp * P.bigPsiAv (n + 3) s H * P.lEta s ^ Expo.lossBeta (n + 3) *
        P.sAv x s :=
  Circ.extraForcing_long (d := d) (hm := hm) (hW := hW) (P := P) (hPW := hPW) (hPD := hPD)
    (hPS := hPS) (hz := hz) (hC := MTerms.cyclic_holds) (hWd := MTerms.ward_holds) (σ := σ)
    (hσ := hσ) (hs := hs) (hH := hH) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.Circ
open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate
variable {N : ℕ}

/-- `Circ.circ_wardTwo` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement` (`hC`,
`hWd`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses are as
in `Circ.circ_wardTwo`. -/
theorem circ_wardTwo_uncond (P : PsiData N)
    (hS : StochasticSymm P.S) (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {n : ℕ}
    (σ : Fin (n + 2 + 2) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (x : Fin (n + 2 + 2) → Fin N) :
    ‖∑ b, ∑ c, P.avErr σ (update (update x ⟨n + 1, by omega⟩ b) (Fin.last (n + 2 + 1)) c) s H‖ ≤
      (vsHeight P.z s)⁻¹ ^ 2 * (P.bigPsiAv (n + 2) s H * (P.lEta s ^ Expo.lossBeta (n + 2) *
        P.sAv (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 3)) (wardSites x)) s)) :=
  Circ.circ_wardTwo (hC := MTerms.cyclic_holds) (hWd := MTerms.ward_holds) (P := P) (hS := hS)
    (hN := hN) (hW := hW) (hz := hz) (σ := σ) (hσ := hσ) (hs := hs) (hH := hH) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.Circ
open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open scoped ComplexConjugate
variable {N : ℕ}

/-- `Circ.circ_ward_mChain_mid` without its hypothesis `Split.WardStatement` (`hW`), which is proved
as `MTerms.ward_holds`; the other hypotheses are as in `Circ.circ_ward_mChain_mid`. -/
theorem circ_ward_mChain_mid_uncond (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0) {K : ℕ} (σ : Fin (K + 2) → Bool)
    (j : Fin (K + 1)) (hσ : σ j.castSucc ≠ σ j.succ) (x : Fin (K + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ b, P.mChain σ (update x j.castSucc b) t =
      (Split.zParam t (patM P.z σ ((j : ℕ) + 1)) - Split.zParam t (patM P.z σ ((j : ℕ) + 2)))⁻¹ •
        (P.mChain (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t -
          P.mChain (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t) :=
  Circ.circ_ward_mChain_mid (hW := MTerms.ward_holds) (P := P) (hS := hS) (hz := hz) (σ := σ)
    (j := j) (hσ := hσ) (x := x) (ht := ht)

/-- `Circ.circ_wardMid` without its hypothesis `Split.WardStatement` (`hW`), which is proved as
`MTerms.ward_holds`; the other hypotheses are as in `Circ.circ_wardMid`. -/
theorem circ_wardMid_uncond (P : PsiData N) (hS : StochasticSymm P.S)
    (hz : 0 < P.z.im) {K : ℕ} (σ : Fin (K + 2) → Bool) (j : Fin (K + 1))
    (hσ : σ j.castSucc ≠ σ j.succ) (x : Fin (K + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ∑ b, P.avErr σ (update x j.castSucc b) t H =
      (patZ P.z σ t j.castSucc - patZ P.z σ t j.succ)⁻¹ *
        (P.avErr (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t H -
          P.avErr (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t H) :=
  Circ.circ_wardMid (hW := MTerms.ward_holds) (P := P) (hS := hS) (hz := hz) (σ := σ) (j := j)
    (hσ := hσ) (x := x) (ht := ht) (hH := hH)

/-- `Circ.circ_wardMid_norm` without its hypothesis `Split.WardStatement` (`hW`), which is proved as
`MTerms.ward_holds`; the other hypotheses are as in `Circ.circ_wardMid_norm`. -/
theorem circ_wardMid_norm_uncond (P : PsiData N) (hS : StochasticSymm P.S)
    (hz : 0 < P.z.im) {K : ℕ} (σ : Fin (K + 2) → Bool) (j : Fin (K + 1))
    (hσ : σ j.castSucc ≠ σ j.succ) (x : Fin (K + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ‖∑ b, P.avErr σ (update x j.castSucc b) t H‖ ≤
      (2 * vsHeight P.z t)⁻¹ *
        (‖P.avErr (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t H‖ +
          ‖P.avErr (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t H‖) :=
  Circ.circ_wardMid_norm (hW := MTerms.ward_holds) (P := P) (hS := hS) (hz := hz) (σ := σ) (j := j)
    (hσ := hσ) (x := x) (ht := ht) (hH := hH)

end

end BlockBand.Native.ErdosRiabov.Discharge
