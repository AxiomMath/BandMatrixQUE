module

public import BlockBand.Native.ErdosRiabov.MBound.Ward
public import BlockBand.Native.ErdosRiabov.MBound.Rotate
public import BlockBand.Native.ErdosRiabov.MBound.Sat
public import BlockBand.Native.ErdosRiabov.MBound.NonSat
public import BlockBand.Native.ErdosRiabov.MBound.Iso
public import BlockBand.Native.ErdosRiabov.MBound.Joint
public import BlockBand.Native.ErdosRiabov.MBound.Pow
public import BlockBand.Native.ErdosRiabov.MZero.Init
public import BlockBand.Native.ErdosRiabov.MTerms.Algebra

/-!
# Unconditional corollaries for the `M`-bounds

The bounds on the deterministic `M`-chains with the `M`-term algebra discharged.

* `<name>_uncond`: the Ward, rotation, saturated, non-saturated and isotropic `M`-bound
  theorems with `Split.CyclicStatement`, `Split.WardStatement` and/or `MBAlg` discharged; every
  other hypothesis (in particular the initial bounds and `MBCtx`) is unchanged;
* `mbBounds_joint_of_init_uncond`, `mbBounds_joint_log_of_init_uncond`: `MBound.mbBounds_joint`,
  `MBound.mbBounds_joint_log` with `MBAlg` discharged (initial bounds with constants `B₀` kept);
  `mbBounds_joint_of_mzero_uncond`: `MZero.mbBounds_joint_of_mzero` with `MBAlg` discharged;
* `mbBounds_joint_uncond` (with the initial bounds `mzeroConst`; only `MBCtx`),
  `mbBounds_joint_log_uncond`
  (log-power constants with `B₀ = mzeroConst d`; `MBCtx` and `mzeroConst d j ≤ B`) and
  `mbBounds_joint_log_uncond_sum` (`B = ∑_{j ≤ k} mzeroConst d j`; only `MBCtx`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Discharge

/-- The `M`-term algebra as the `MBAlg` bundle of the `M`-bounds:
`MBound.MBAlg.of_mTermAlgebra MTerms.mTermAlgebra_holds`. -/
theorem mbAlg_holds : MBound.MBAlg :=
  MBound.MBAlg.of_mTermAlgebra MTerms.mTermAlgebra_holds

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Propagator
open scoped ComplexConjugate BigOperators
variable {N : ℕ}
variable {S : Matrix (Fin N) (Fin N) ℝ} (hS : Split.ProfileHyp S) {t : ℝ}
  (ht : t ∈ Icc (0 : ℝ) 1) {m : ℕ → ℂ} (hm1 : ∀ i, ‖m i‖ < 1) (hm0 : ∀ i, m i ≠ 0)

include hS ht hm1 hm0 in

/-- `MBound.mb_ward_trace` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hW`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `MBound.mb_ward_trace`. -/
theorem mb_ward_trace_uncond {n : ℕ}
    (A : ℕ → Fin N → ℂ) (hAk : A (n + 2) = fun _ => 1) (hmk : m (n + 2) ≠ m 1) :
    ∑ a, Split.chainM t S m A 1 (n + 2) a =
      (Split.zParam t (m (n + 2)) - Split.zParam t (m 1))⁻¹ *
        (∑ a, A (n + 1) a * Split.chainM t S (Split.dropAt 2 (Split.rotateChain (n + 2) m))
            (Split.dropAt 1 (Split.rotateChain (n + 2) A)) 1 (n + 1) a -
          ∑ a, A (n + 1) a * Split.chainM t S (Split.dropAt 1 (Split.rotateChain (n + 2) m))
            (Split.dropAt 1 (Split.rotateChain (n + 2) A)) 1 (n + 1) a) :=
  MBound.mb_ward_trace (hS := hS) (ht := ht) (hm1 := hm1) (hm0 := hm0) (hC := MTerms.cyclic_holds)
    (hW := MTerms.ward_holds) (A := A) (hAk := hAk) (hmk := hmk)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Propagator
open scoped ComplexConjugate BigOperators
variable {N : ℕ}
variable (P : PsiData N) (hS : Split.ProfileHyp P.S) (hz : 0 < P.z.im) {t : ℝ}
  (ht : t ∈ Icc (0 : ℝ) 1)

include hS hz ht in

/-- `MBound.mbAvM_ward_last` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hW`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `MBound.mbAvM_ward_last`. -/
theorem mbAvM_ward_last_uncond {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (y : Fin (n + 1) → Fin N) :
    ∑ c, Evol.avM P σ (Fin.insertNth (Fin.last (n + 1)) c y) t =
      (Split.zParam t (VS.patConj (σ (Fin.last (n + 1))) (semicircleM P.z)) -
          Split.zParam t (VS.patConj (σ 0) (semicircleM P.z)))⁻¹ *
        (Evol.avM P (mbPatRot σ) y t - Evol.avM P (Fin.init σ) y t) :=
  MBound.mbAvM_ward_last (P := P) (hS := hS) (hz := hz) (ht := ht) (hC := MTerms.cyclic_holds)
    (hW := MTerms.ward_holds) (σ := σ) (hσ := hσ) (y := y)

include hS hz ht in

/-- `MBound.mbAvM_ward_mid` without its hypothesis `Split.WardStatement` (`hW`), which is proved as
`MTerms.ward_holds`; the other hypotheses are as in `MBound.mbAvM_ward_mid`. -/
theorem mbAvM_ward_mid_uncond {n : ℕ} (σ : Fin (n + 2) → Bool)
    (j : Fin (n + 1)) (hσ : σ j.castSucc ≠ σ j.succ) (y : Fin (n + 1) → Fin N) :
    ∑ c, Evol.avM P σ (Fin.insertNth j.castSucc c y) t =
      (Split.zParam t (VS.patConj (σ j.castSucc) (semicircleM P.z)) -
          Split.zParam t (VS.patConj (σ j.succ) (semicircleM P.z)))⁻¹ *
        (Evol.avM P (Fin.removeNth j.succ σ) y t -
          Evol.avM P (Fin.removeNth j.castSucc σ) y t) :=
  MBound.mbAvM_ward_mid (P := P) (hS := hS) (hz := hz) (ht := ht) (hW := MTerms.ward_holds) (σ := σ)
    (j := j) (hσ := hσ) (y := y)

include hS hz ht in

/-- `MBound.mbWard_bounds` without its hypotheses `Split.CyclicStatement`, `Split.WardStatement`
(`hC`, `hW`), which are proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`; the other hypotheses
are as in `MBound.mbWard_bounds`. -/
theorem mbWard_bounds_uncond {n : ℕ}
    (σ : Fin (n + 4) → Bool) (hsat : ¬ HasDesatFactor σ) {A₃ A₂ : ℝ}
    (h3 : MBAvB P (n + 3) A₃) (h2 : MBAvB P (n + 2) A₂) (hη : 0 < vsHeight P.z t) :
    (∀ y, ‖mbTrL (fun x => Evol.avM P σ x t) y‖ ≤
        A₃ / vsHeight P.z t * (P.lEta t * P.sAv y t)) ∧
    (∀ y, ‖mbTrM (fun x => Evol.avM P σ x t) y‖ ≤
        A₃ / vsHeight P.z t * (P.lEta t * P.sAv y t)) ∧
    (∀ w, ‖mbTrLM (fun x => Evol.avM P σ x t) w‖ ≤
        A₂ / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv w t)) :=
  MBound.mbWard_bounds (P := P) (hS := hS) (hz := hz) (ht := ht) (hC := MTerms.cyclic_holds)
    (hW := MTerms.ward_holds) (σ := σ) (hsat := hsat) (h3 := h3) (h2 := h2) (hη := hη)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Evol BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Contr
open scoped BigOperators
variable {N : ℕ}

/-- `MBound.mbAvM_rotate_symm` without its hypothesis `Split.CyclicStatement` (`hC`), which is
proved as `MTerms.cyclic_holds`; the other hypotheses are as in `MBound.mbAvM_rotate_symm`. -/
theorem mbAvM_rotate_symm_uncond (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N) :
    avM P σ x t =
      avM P (fun r => σ ((finRotate (n + 2)).symm r)) (fun r => x ((finRotate (n + 2)).symm r))
        t :=
  MBound.mbAvM_rotate_symm (hC := MTerms.cyclic_holds) (P := P) (hS := hS) (hz := hz) (ht := ht)
    (σ := σ) (x := x)

/-- `MBound.mbAvM_rotate` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved as
`MTerms.cyclic_holds`; the other hypotheses are as in `MBound.mbAvM_rotate`. -/
theorem mbAvM_rotate_uncond (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N) :
    avM P σ x t =
      avM P (fun r => σ (finRotate (n + 2) r)) (fun r => x (finRotate (n + 2) r)) t :=
  MBound.mbAvM_rotate (hC := MTerms.cyclic_holds) (P := P) (hS := hS) (hz := hz) (ht := ht) (σ := σ)
    (x := x)

/-- `MBound.mbAvM_rotate_pow` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved
as `MTerms.cyclic_holds`; the other hypotheses are as in `MBound.mbAvM_rotate_pow`. -/
theorem mbAvM_rotate_pow_uncond (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (r : ℕ) (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N) :
    avM P σ x t = avM P (fun i => σ ((finRotate (n + 2) ^ r) i))
      (fun i => x ((finRotate (n + 2) ^ r) i)) t :=
  MBound.mbAvM_rotate_pow (hC := MTerms.cyclic_holds) (P := P) (hS := hS) (hz := hz) (ht := ht)
    (r := r) (σ := σ) (x := x)

/-- `MBound.mbSlot_avM_rotTo` without its hypothesis `Split.CyclicStatement` (`hC`), which is proved
as `MTerms.cyclic_holds`; the other hypotheses are as in `MBound.mbSlot_avM_rotTo`. -/
theorem mbSlot_avM_rotTo_uncond (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (σ : Fin (n + 2) → Bool) (j : Fin (n + 2))
    (x : Fin (n + 2) → Fin N) :
    mbSlot K j (fun y => avM P σ y t) x =
      mbSlot K (Fin.last (n + 1))
        (fun y => avM P (fun i => σ ((finRotate (n + 2) ^ ((j : ℕ) + 1)) i)) y t)
        (mbRotTo j x) :=
  MBound.mbSlot_avM_rotTo (hC := MTerms.cyclic_holds) (P := P) (hS := hS) (hz := hz) (ht := ht)
    (K := K) (σ := σ) (j := j) (x := x)

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

/-- `MBound.mbBounds_sat` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mbBounds_sat`. -/
theorem mbBounds_sat_uncond {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ τ : Fin (n + 4) → Bool, ¬ HasDesatFactor τ →
      ∀ y, ‖avM P τ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖avM P σ x t‖ ≤ mbAsat d (mbLambda d (m * W)) n A I B₀ * (P.lEta t * P.sAv x t) :=
  MBound.mbBounds_sat (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I)
    (hA0 := hA0) (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hB₀ := hB₀) (hInit := hInit) (ht := ht)
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

/-- `MBound.mbBounds_nonsat_av` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mbBounds_nonsat_av`. -/
theorem mbBounds_nonsat_av_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) (hσ : HasDesatFactor σ)
    (A I : ℕ → ℝ) (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 3) → Fin (m * W)) :
    ‖avM P σ x t‖ ≤ mbAns d (mbLambda d (m * W)) (n + 3) A I B₀ * (P.lEta t * P.sAv x t) :=
  MBound.mbBounds_nonsat_av (hc := hc) (hA := mbAlg_holds) (σ := σ) (hσ := hσ) (A := A) (I := I)
    (hA0 := hA0) (hI0 := hI0) (hAv := hAv) (hIso := hIso) (hB₀ := hB₀) (hInit := hInit) (ht := ht)
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

/-- `MBound.mbBounds_iso` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mbBounds_iso`. -/
theorem mbBounds_iso_uncond {n : ℕ} (σ : Fin (n + 3) → Bool) {Ak : ℝ} (hAk0 : 0 ≤ Ak)
    (hAk : MBAvB P (n + 3) Ak) (I : ℕ → ℝ) (hI0 : ∀ n, 0 ≤ I n)
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (a : Fin (m * W))
    (hInit : ∀ y, ‖P.mChain σ y 0 a‖ ≤ B₀ * (Real.sqrt (P.lEta 0) * P.sIso a a y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 3) → Fin (m * W)) :
    ‖P.mChain σ x t a‖ ≤
      mbIsoK d (mbLambda d (m * W)) (n + 3) Ak I B₀ * (Real.sqrt (P.lEta t) * P.sIso a a x t) :=
  MBound.mbBounds_iso (hc := hc) (hA := mbAlg_holds) (σ := σ) (hAk0 := hAk0) (hAk := hAk) (I := I)
    (hI0 := hI0) (hIso := hIso) (hB₀ := hB₀) (a := a) (hInit := hInit) (ht := ht) (x := x)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mbBounds_joint` without its hypothesis `MBAlg` (`hA`), which is proved as `mbAlg_holds`;
the other hypotheses are as in `MBound.mbBounds_joint`. -/
theorem mbBounds_joint_of_init_uncond (B₀ : ℕ → ℝ) (hB₀ : ∀ k, 0 ≤ B₀ k)
    (hInitAv : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin (m * W)),
      ‖avM P σ y 0‖ ≤ B₀ k * (P.lEta 0 * P.sAv y 0))
    (hInitIso : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin (m * W)) (y : Fin k → Fin (m * W)),
      ‖P.mChain σ y 0 a‖ ≤ B₀ k * (Real.sqrt (P.lEta 0) * P.sIso a a y 0)) :
    ∀ k, 1 ≤ k → MBAvB P k (mbConstA d (mbLambda d (m * W)) B₀ k) ∧
      MBIsoB P k (mbConstI d (mbLambda d (m * W)) B₀ k) :=
  MBound.mbBounds_joint (hc := hc) (hA := mbAlg_holds) (B₀ := B₀) (hB₀ := hB₀) (hInitAv := hInitAv)
    (hInitIso := hInitIso)

end

section

open BlockBand.Native.ErdosRiabov.MBound
open Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in

/-- `MBound.mbBounds_joint_log` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MBound.mbBounds_joint_log`. -/
theorem mbBounds_joint_log_of_init_uncond (B₀ : ℕ → ℝ) (hB₀ : ∀ k, 0 ≤ B₀ k)
    (hInitAv : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin (m * W)),
      ‖avM P σ y 0‖ ≤ B₀ k * (P.lEta 0 * P.sAv y 0))
    (hInitIso : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin (m * W)) (y : Fin k → Fin (m * W)),
      ‖P.mChain σ y 0 a‖ ≤ B₀ k * (Real.sqrt (P.lEta 0) * P.sIso a a y 0))
    {B : ℝ} (hB : 1 ≤ B) (k : ℕ) (hk : 1 ≤ k) (hBk : ∀ j, j ≤ k → B₀ j ≤ B) :
    MBAvB P k (mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) ∧
      MBIsoB P k
        (mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) :=
  MBound.mbBounds_joint_log (hc := hc) (hA := mbAlg_holds) (B₀ := B₀) (hB₀ := hB₀)
    (hInitAv := hInitAv) (hInitIso := hInitIso) (hB := hB) (k := k) (hk := hk) (hBk := hBk)

end

section

open BlockBand.Native.ErdosRiabov.MZero
open Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.MBound BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)

/-- `MZero.mbBounds_joint_of_mzero` without its hypothesis `MBAlg` (`hA`), which is proved as
`mbAlg_holds`; the other hypotheses are as in `MZero.mbBounds_joint_of_mzero`. -/
theorem mbBounds_joint_of_mzero_uncond {d : VSData} {m W : ℕ} {P : PsiData (m * W)}
    (hc : MBCtx d P) :
    ∀ k, 1 ≤ k → MBAvB P k (mbConstA d (mbLambda d (m * W)) (mzeroConst d) k) ∧
      MBIsoB P k (mbConstI d (mbLambda d (m * W)) (mzeroConst d) k) :=
  MZero.mbBounds_joint_of_mzero (hA := mbAlg_holds) (hc := hc)

end

/-!
## `Mbounds_joint` with every hypothesis except `MBCtx` discharged
-/

section Joint

open Set
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.MBound
open BlockBand.Native.ErdosRiabov.MZero BlockBand.Native.ErdosRiabov.Flow

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)}

/-- **The joint `M`-bounds without hypotheses on the `M`-term algebra**:
`MZero.mbBounds_joint_of_mzero_mTermAlgebra` with `hT : Split.MTermAlgebra` proved as
`MTerms.mTermAlgebra_holds`; the initial bounds are those of `MZero` (constants `mzeroConst d`).
Only hypothesis: `MBCtx d P`. For every `k ≥ 1`, all `t ∈ [0,1]`, patterns and sites,
`AvB(k, A_k)` and `IsoB(k, I_k)` with `A_k = mbConstA d Λ (mzeroConst d) k`,
`I_k = mbConstI d Λ (mzeroConst d) k`, `Λ = mbLambda d (m W)`; `mzeroConst d` depends on `d`
only. Deterministic. -/
theorem mbBounds_joint_uncond (hc : MBCtx d P) :
    ∀ k, 1 ≤ k → MBAvB P k (mbConstA d (mbLambda d (m * W)) (mzeroConst d) k) ∧
      MBIsoB P k (mbConstI d (mbLambda d (m * W)) (mzeroConst d) k) :=
  MZero.mbBounds_joint_of_mzero_mTermAlgebra MTerms.mTermAlgebra_holds hc

/-- **The joint `M`-bounds with the log-power constants**: the conclusion of
`MBound.mbBounds_joint_log` with `B₀ = mzeroConst d`, obtained from `mbBounds_joint_uncond` and
`MBound.mbConst_le_log_pow`; no `MBAlg` and no initial-bound hypothesis. If `mzeroConst d j ≤ B`
(`B ≥ 1`) for `j ≤ k`, `k ≥ 1`, then `AvB(k, C (log N)^{C'})` and `IsoB(k, C (log N)^{C'})`,
`N = m W`, `C = c_k C_log^{e_k}` (`c_k = mbPowC d B k`, `C_log = mbLogC d`),
`C' = e_k = 2^k − 4`. The hypotheses are `MBCtx d P` and the bound `B` on the constants
`mzeroConst d j`. -/
theorem mbBounds_joint_log_uncond (hc : MBCtx d P) {B : ℝ} (hB : 1 ≤ B) (k : ℕ)
    (hk : 1 ≤ k) (hBk : ∀ j, j ≤ k → mzeroConst d j ≤ B) :
    MBAvB P k (mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) ∧
      MBIsoB P k
        (mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) := by
  have hN : 2 ≤ m * W :=
    calc 2 ≤ 4 := by norm_num
      _ ≤ m := hc.hm
      _ ≤ m * W := Nat.le_mul_of_pos_right m hc.hW
  obtain ⟨hAv, hIso⟩ := mbBounds_joint_uncond hc k hk
  obtain ⟨hcA, hcI⟩ := mbConst_le_log_pow d hN hB (mzeroConst d) (mzeroConst_nonneg d) k hBk
  refine ⟨fun t ht σ x => (hAv t ht σ x).trans
    (mul_le_mul_of_nonneg_right hcA (mb_LsAv_pos_nonneg hc ht x)), fun t ht σ a x =>
      (hIso t ht σ a x).trans (mul_le_mul_of_nonneg_right hcI
        (mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P (hc.inputs ht) _ _ _)))⟩

/-- `B = ∑_{j ≤ k} mzeroConst d j` satisfies `1 ≤ B` and `mzeroConst d j ≤ B` for `j ≤ k`. -/
theorem mzeroConst_le_sum (d : VSData) (k : ℕ) :
    1 ≤ ∑ j ∈ Finset.range (k + 1), mzeroConst d j ∧
      ∀ j, j ≤ k → mzeroConst d j ≤ ∑ i ∈ Finset.range (k + 1), mzeroConst d i := by
  have hle : ∀ j, j ≤ k → mzeroConst d j ≤ ∑ i ∈ Finset.range (k + 1), mzeroConst d i :=
    fun j hj => Finset.single_le_sum (fun i _ => mzeroConst_nonneg d i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact ⟨(mzero_one_le_mzeroConst d 0).trans (hle 0 (Nat.zero_le k)), hle⟩

/-- **The joint `M`-bounds with the log-power constants, hypothesis-free form**:
`mbBounds_joint_log_uncond` at `B = ∑_{j ≤ k} mzeroConst d j` (`mzeroConst_le_sum`). Under
`MBCtx d P` only, for `k ≥ 1`: `AvB(k, C (log N)^{C'})` and `IsoB(k, C (log N)^{C'})`,
`N = m W`, `C = mbPowC d B k · mbLogC d ^ e_k` depending on `d`, `k` only,
`C' = e_k = 2^k − 4`. -/
theorem mbBounds_joint_log_uncond_sum (hc : MBCtx d P) (k : ℕ) (hk : 1 ≤ k) :
    MBAvB P k (mbPowC d (∑ j ∈ Finset.range (k + 1), mzeroConst d j) k * mbLogC d ^ mbPowExp k *
        Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) ∧
      MBIsoB P k (mbPowC d (∑ j ∈ Finset.range (k + 1), mzeroConst d j) k *
        mbLogC d ^ mbPowExp k * Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) :=
  mbBounds_joint_log_uncond hc (mzeroConst_le_sum d k).1 k hk (mzeroConst_le_sum d k).2

end Joint

end BlockBand.Native.ErdosRiabov.Discharge
