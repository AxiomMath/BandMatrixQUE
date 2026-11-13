module

public import BlockBand.Native.ErdosRiabov.MBound.SatEvol
public import BlockBand.Native.ErdosRiabov.MBound.SatV
public import BlockBand.Native.ErdosRiabov.MBound.SatZ
public import BlockBand.Native.ErdosRiabov.MBound.SatVB
public import BlockBand.Native.ErdosRiabov.MBound.Sat
public import BlockBand.Native.ErdosRiabov.MBound.NonSat
public import BlockBand.Native.ErdosRiabov.MBound.Iso
public import BlockBand.Native.ErdosRiabov.Discharge.MBound

/-!
# Unconditional intermediate lemmas of the `M`-bounds

The derivative, continuity, Duhamel and bound lemmas used in the proof of the `M`-bounds, with
the hypothesis `MBAlg` discharged by `mbAlg_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Discharge

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators
variable {N : ℕ}
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mb_hasDerivAt_X` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mb_hasDerivAt_X`. -/
theorem mb_hasDerivAt_X_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => fun x => avM P σ x r)
      (propOp (mbGenSat P (n + 3) s) (fun x => avM P σ x s) + fun x => mbFM P σ x s) s :=
  MBound.mb_hasDerivAt_X (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (hs := hs)

include hc in

/-- `MBound.mb_hasDerivAt_Y` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mb_hasDerivAt_Y`. -/
theorem mb_hasDerivAt_Y_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => mbY P σ r) (propOp (mbGenSat P (n + 4) s) (mbY P σ s) + mbGY P σ s) s :=
  MBound.mb_hasDerivAt_Y (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (hs := hs)

include hc in

/-- `MBound.mb_contOn_X` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mb_contOn_X`. -/
theorem mb_contOn_X_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun r => fun x => avM P σ x r) (Icc (0 : ℝ) 1) :=
  MBound.mb_contOn_X (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ)

include hc in

/-- `MBound.mb_contOn_F` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mb_contOn_F`. -/
theorem mb_contOn_F_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun r => fun x => mbFM P σ x r) (Icc (0 : ℝ) 1) :=
  MBound.mb_contOn_F (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ)

include hc in

/-- `MBound.mb_contOn_GY` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mb_contOn_GY`. -/
theorem mb_contOn_GY_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun r => mbGY P σ r) (Icc (0 : ℝ) 1) :=
  MBound.mb_contOn_GY (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ)

include hc in

/-- `MBound.mbY_duhamel` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mbY_duhamel`. -/
theorem mbY_duhamel_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mbY P σ t = propOp (mbPropSat P (n + 4) 0 t) (mbY P σ 0) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropSat P (n + 4) s t) (mbGY P σ s) :=
  MBound.mbY_duhamel (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (ht := ht)

include hc in

/-- `MBound.mbZ_duhamel` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mbZ_duhamel`. -/
theorem mbZ_duhamel_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mbZ P σ t = propOp (mbPropSat P (n + 4) 0 t)
        (mbRing (mbTheta P t) (mbJ' n) (mbA' n) (mbRing (mbTheta P t) (mbJ n) (mbA n)
          (fun x => avM P σ x 0))) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropSat P (n + 4) s t)
        (mbRing (mbTheta P t) (mbJ' n) (mbA' n) (mbRing (mbTheta P t) (mbJ n) (mbA n)
          ((fun x => mbFM P σ x s) + mbFtX P σ s))) :=
  MBound.mbZ_duhamel (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (ht := ht)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators
variable {N : ℕ}
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mb_contOn_GI` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mb_contOn_GI`. -/
theorem mb_contOn_GI_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) :
    ContinuousOn (fun s => mbGI P σ s) (Icc (0 : ℝ) 1) :=
  MBound.mb_contOn_GI (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ)

include hc in

/-- `MBound.mbX_duhamelI` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mbX_duhamelI`. -/
theorem mbX_duhamelI_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => avM P σ x t) = propOp (mbPropI P n 0 t) (fun x => avM P σ x 0) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropI P n s t) (mbGI P σ s) :=
  MBound.mbX_duhamelI (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (ht := ht)

include hc in

/-- `MBound.mbV_duhamel` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mbV_duhamel`. -/
theorem mbV_duhamel_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mbV P σ t = propOp (mbPropI P n 0 t) (mbSlot (mbTheta P t) (mbJ n) (fun x => avM P σ x 0)) +
      ∫ s in (0 : ℝ)..t, propOp (mbPropI P n s t) (mbSlot (mbTheta P t) (mbJ n) (mbGI P σ s)) :=
  MBound.mbV_duhamel (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (ht := ht)

include hc in

/-- `MBound.mbD_bound` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`; the
other hypotheses are as in `MBound.mbD_bound`. -/
theorem mbD_bound_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (y : Fin (n + 4) → Fin (m * W)) :
    ‖mbSlot (mbTheta P s) (mbJ' n) (mbSlot (mbTheta P s) (mbJ n) (fun x => avM P σ x s)) y‖ ≤
      ((mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A) / vsHeight P.z s ^ 2 * P.lEta s) *
        P.sAv y s :=
  MBound.mbD_bound (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I) (hA0 := hA0)
    (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hB₀ := hB₀) (hInit := hInit) (hs := hs) (y := y)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators
variable {N : ℕ}
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mb_FFt_bound` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mb_FFt_bound`. -/
theorem mb_FFt_bound_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (y : Fin (n + 4) → Fin (m * W)) :
    ‖((fun x => mbFM P σ x s) + mbFtX P σ s) y‖ ≤
      (d.Cwc * mbFPairSum (n + 4) A I + 4 * vsCK d * Real.sqrt d.C1pp * A (n + 3)) /
        vsHeight P.z s * (P.lEta s * P.sAv y s) :=
  MBound.mb_FFt_bound (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I)
    (hA0 := hA0) (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hs := hs) (y := y)

include hc in

/-- `MBound.mbZ_bound` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`; the
other hypotheses are as in `MBound.mbZ_bound`. -/
theorem mbZ_bound_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖mbZ P σ t x‖ ≤ onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) *
      (B₀ + mbLambda d (m * W) * (d.Cwc * mbFPairSum (n + 4) A I +
        4 * vsCK d * Real.sqrt d.C1pp * A (n + 3))) / vsHeight P.z t ^ 2 *
      (P.lEta t * P.sAv x t) :=
  MBound.mbZ_bound (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I) (hA0 := hA0)
    (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hB₀ := hB₀) (hInit := hInit) (ht := ht) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mbV_integrand_bound` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mbV_integrand_bound`. -/
theorem mbV_integrand_bound_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ)
    (A I : ℕ → ℝ) (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {s t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) t) (x : Fin (n + 4) → Fin (m * W)) :
    ‖propOp (mbPropI P n s t) (mbSlot (mbTheta P t) (mbJ n) (mbGI P σ s)) x‖ ≤
      ((vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * mbFc d n A I +
          kernelActionConst d ^ (n + 5) * (mbZc d (mbLambda d (m * W)) n A I B₀ + mbRc d n A)) /
            vsHeight P.z t * (P.lEta t * P.sAv x t)) * (vsHeight P.z s)⁻¹ :=
  MBound.mbV_integrand_bound (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I)
    (hA0 := hA0) (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hB₀ := hB₀) (hInit := hInit) (ht := ht)
    (hs := hs) (x := x)

include hc in

/-- `MBound.mbV_bound` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`; the
other hypotheses are as in `MBound.mbV_bound`. -/
theorem mbV_bound_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖mbV P σ t x‖ ≤ mbVc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z t *
      (P.lEta t * P.sAv x t) :=
  MBound.mbV_bound (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I) (hA0 := hA0)
    (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hB₀ := hB₀) (hInit := hInit) (ht := ht) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mb_oplus_bound` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mb_oplus_bound`. -/
theorem mb_oplus_bound_uncond
    {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ τ : Fin (n + 4) → Bool, ¬ HasDesatFactor τ →
      ∀ y, ‖avM P τ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖mbOplus (mbTheta P s) (fun y => avM P σ y s) x‖ ≤
      (n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z s *
        (P.lEta s * P.sAv x s) :=
  MBound.mb_oplus_bound (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I)
    (hA0 := hA0) (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hB₀ := hB₀) (hInit := hInit) (hs := hs)
    (x := x)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators
variable {N : ℕ}
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mb_hasDerivAt_X_gen` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mb_hasDerivAt_X_gen`. -/
theorem mb_hasDerivAt_X_gen_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => fun x => avM P σ x r)
      (propOp (vsTensorGen P.S (fun j => (propFactorOf σ j).mu1 P.z)
        (fun j => (propFactorOf σ j).mu2 P.z) s) (fun x => avM P σ x s) +
          fun x => mbFM P σ x s) s :=
  MBound.mb_hasDerivAt_X_gen (hc := hc) (hA := mbAlg_holds) (σ := σ) (hs := hs)

include hc in

/-- `MBound.mb_contOn_F_gen` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mb_contOn_F_gen`. -/
theorem mb_contOn_F_gen_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) :
    ContinuousOn (fun r => fun x => mbFM P σ x r) (Icc (0 : ℝ) 1) :=
  MBound.mb_contOn_F_gen (hc := hc) (hA := mbAlg_holds) (σ := σ)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators
variable {N : ℕ}
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mb_hasDerivAt_Y_iso` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mb_hasDerivAt_Y_iso`. -/
theorem mb_hasDerivAt_Y_iso_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) (a : Fin (m * W)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => fun x => P.mChain σ x r a)
      (propOp (mbIsoGen P σ s) (fun x => P.mChain σ x s a) + mbGIso P σ a s) s :=
  MBound.mb_hasDerivAt_Y_iso (hc := hc) (hA := mbAlg_holds) (σ := σ) (a := a) (hs := hs)

include hc in

/-- `MBound.mb_contOn_GIso` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mb_contOn_GIso`. -/
theorem mb_contOn_GIso_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) (a : Fin (m * W)) :
    ContinuousOn (fun r => mbGIso P σ a r) (Icc (0 : ℝ) 1) :=
  MBound.mb_contOn_GIso (hc := hc) (hA := mbAlg_holds) (σ := σ) (a := a)

end

end BlockBand.Native.ErdosRiabov.Discharge
