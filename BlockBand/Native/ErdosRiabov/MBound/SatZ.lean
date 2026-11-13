module

public import BlockBand.Native.ErdosRiabov.MBound.SatEvol
public import BlockBand.Native.ErdosRiabov.Flow.IntRules

/-!
# The bound on the doubly regularized term

Under `MBCtx d P`, for a saturated pattern of length `k = n+4`, `t ∈ [0,1]`, with
* the initial bound `|Tr[M_0](x)| ≤ B₀ L_0 s^av_{k,0}(x)` for all saturated patterns and sites
  (hypothesis hInit);
* `MBAvB P (n+3) A₃`, `MBAvB P (n+2) A₂` and the forcing hypotheses of `mbFM_bound`;
`mbZ_bound`: `|Z_t(x)| ≤ C_reg² C_P^k (B₀ + Λ (C_wc ΣIA + 4 C_K √C₁'' A₃)) η_t⁻² L_t s^av_{k,t}(x)`
(`Λ = mbLambda d N`, `ΣIA = mbFPairSum k A I`), via `mbZ_duhamel`, the two-ring
propagator bound `regProps_twoRings_apply`, the forcing bounds and the integration rule `vsIntRules`.

Deterministic. The bound is conditional on `MBAlg` (the `M`-term algebra) and on the initial
bound hInit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators

variable {N : ℕ}

/-! ## Integrals of coordinates -/

theorem mb_integral_apply {k : ℕ} {g : ℝ → (Fin k → Fin N) → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (x : Fin k → Fin N) :
    (∫ s in a..b, g s) x = ∫ s in a..b, g s x := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k → Fin N => ℂ) x
    ).intervalIntegral_comp_comm hg
  simpa using h.symm

/-- `‖(∫_0^t g) x‖ ≤ c ∫_0^t η_s⁻¹ ds` from a pointwise bound `‖g s x‖ ≤ c η_s⁻¹` on `[0,t]`. -/
theorem mb_norm_integral_le {k : ℕ} {z : ℂ} (hz : 0 < z.im) {g : ℝ → (Fin k → Fin N) → ℂ}
    {t c : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hg : IntervalIntegrable g volume 0 t)
    (x : Fin k → Fin N) (hb : ∀ s ∈ Icc (0 : ℝ) t, ‖g s x‖ ≤ c * (vsHeight z s)⁻¹) :
    ‖(∫ s in (0 : ℝ)..t, g s) x‖ ≤ c * ∫ s in (0 : ℝ)..t, (vsHeight z s)⁻¹ := by
  rw [mb_integral_apply hg x, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le ht.1
    (Filter.Eventually.of_forall fun s hs => hb s ⟨hs.1.le, hs.2⟩) ?_
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le ht.1]
  exact continuousOn_const.mul ((continuous_vsHeight z).continuousOn.inv₀ fun s hs =>
    (vsHeight_pos hz (hs.2.trans ht.2)).ne')

/-! ## The bound -/

section Bound

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hc in
theorem mb_goodProp_sat_eq {k : ℕ} (s t : ℝ) :
    goodProp (shortRingProfile d.b m W) P.z (fun _ => .sat) s t = mbPropSat P k s t := by
  rw [mbPropSat, ← hc.hPS]
  rfl

include hc in
theorem mb_ringOp_eq {k : ℕ} (t : ℝ) (j a : Fin k) (f : (Fin k → Fin (m * W)) → ℂ) :
    ringOp (shortRingProfile d.b m W) P.z t j a f = mbRing (mbTheta P t) j a f := by
  rw [mbTheta, ← hc.hPS]
  rfl

include hc in
theorem mb_LsAv_pos_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {k : ℕ}
    (x : Fin k → Fin (m * W)) : 0 ≤ P.lEta t * P.sAv x t :=
  mul_nonneg (hc.inputs ht).lEta_pos.le (mb_sAv_nonneg P (hc.inputs ht) x)

include hc in
/-- The two-ring propagator bound `regProps_twoRings_apply` in the `M`-bound notation: if `|f| ≤ φ s^av_{n+4,s}` then
`|P̂^{⊗}_{s,t} Θ̊_tΘ̊_t f(x)| ≤ C_reg² C_P^{n+4} φ η_t⁻² (L_t/L_s) s^av_{n+4,t}(x)`. -/
theorem mb_twoRings {n : ℕ} {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) {φ : ℝ}
    (hφ : 0 ≤ φ) (f : (Fin (n + 4) → Fin (m * W)) → ℂ) (hf : ∀ y, ‖f y‖ ≤ φ * P.sAv y s)
    (x : Fin (n + 4) → Fin (m * W)) :
    ‖propOp (mbPropSat P (n + 4) s t) (mbRing (mbTheta P t) (mbJ' n) (mbA' n)
        (mbRing (mbTheta P t) (mbJ n) (mbA n) f)) x‖ ≤
      onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) / vsHeight P.z t ^ 2 *
        (P.lEta t / P.lEta s) * φ * P.sAv x t := by
  have h := regProps_twoRings_apply d hc.hm hc.hW P hc.hPW hc.hPD hc.hz hs0 hst ht1 (n := n)
    hφ f hf x
  rw [mb_goodProp_sat_eq hc, mb_ringOp_eq hc, mb_ringOp_eq hc] at h
  exact h

include hA hc in

/-- The forcing `F_s + F̃_s` of the doubly regularized term, at a time `s ∈ [0,1]`:
`|F_s + F̃_s| ≤ (C_wc ΣIA + 4 C_K √C₁'' A₃)/η_s · L_s s^av_s`. -/
theorem mb_FFt_bound {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (y : Fin (n + 4) → Fin (m * W)) :
    ‖((fun x => mbFM P σ x s) + mbFtX P σ s) y‖ ≤
      (d.Cwc * mbFPairSum (n + 4) A I + 4 * vsCK d * Real.sqrt d.C1pp * A (n + 3)) /
        vsHeight P.z s * (P.lEta s * P.sAv y s) := by
  have hin := hc.inputs hs
  have hη := hin.height_pos
  have hF := mbFM_bound P hs hin A I hA0 hI0 (fun n' h3 h4 => hAv n' (by omega) h4) hIso σ y
  obtain ⟨hL, hM, -⟩ := mbWard_bounds P hc.profile hc.zpos hs hA.cyclic hA.ward σ hσ
    (hAv (n + 3) (by omega) (by omega)) (hAv (n + 2) (by omega) (by omega)) hη
  have hFt := mbFt_bound P s hin (mbTheta P s) (vsCK_pos d).le (hc.theta_bound hs)
    (fun x => avM P σ x s) (div_nonneg (hA0 _) hη.le) hL hM y
  simp only [Pi.add_apply]
  refine (norm_add_le _ _).trans ?_
  unfold mbFtX
  calc _ ≤ d.Cwc / vsHeight P.z s * mbFPairSum (n + 4) A I * (P.lEta s * P.sAv y s) +
        4 * vsCK d * Real.sqrt d.C1pp * (A (n + 3) / vsHeight P.z s) *
          (P.lEta s * P.sAv y s) := add_le_add hF hFt
    _ = _ := by ring

include hA hc in

/-- **The bound on the doubly regularized term** (conditional on `MBAlg` and the initial bound
`hInit`): for a saturated pattern of length `n+4` and `t ∈ [0,1]`,
`|Z_t(x)| ≤ C_reg² C_P^{n+4} (B₀ + Λ (C_wc ΣIA + 4 C_K √C₁'' A₃)) η_t⁻² L_t s^av_t(x)`. -/
theorem mbZ_bound {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ y, ‖avM P σ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖mbZ P σ t x‖ ≤ onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) *
      (B₀ + mbLambda d (m * W) * (d.Cwc * mbFPairSum (n + 4) A I +
        4 * vsCK d * Real.sqrt d.C1pp * A (n + 3))) / vsHeight P.z t ^ 2 *
      (P.lEta t * P.sAv x t) := by
  set C2 := onestepConst d ^ 2 * kernelActionConst d ^ (n + 4)
  set Fc := d.Cwc * mbFPairSum (n + 4) A I + 4 * vsCK d * Real.sqrt d.C1pp * A (n + 3)
  have hFc : 0 ≤ Fc := by
    have h1 := d.one_le_Cwc
    have h2 : 0 ≤ mbFPairSum (n + 4) A I := by
      unfold mbFPairSum
      refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
      split_ifs
      · exact mul_nonneg (hI0 _) (hA0 _)
      · exact le_rfl
    have h3 := (vsCK_pos d).le
    exact add_nonneg (mul_nonneg (by linarith) h2)
      (mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (hA0 _))
  have hC2 : 0 ≤ C2 := by
    have := kernelActionConst_ge_one d
    positivity
  have hzi := hc.zpos
  have hint := mb_intervalIntegrable_prop hc ht (G := fun s => mbRing (mbTheta P t) (mbJ' n)
    (mbA' n) (mbRing (mbTheta P t) (mbJ n) (mbA n) ((fun x => mbFM P σ x s) + mbFtX P σ s)))
    ?_
  · rw [mbZ_duhamel hA hc σ hσ ht, Pi.add_apply]
    have hin0 := hc.inputs (t := 0) ⟨le_rfl, zero_le_one⟩
    have hint_t := hc.inputs ht
    have hL0 := hin0.lEta_pos
    have hηt := hint_t.height_pos
    -- the initial term
    have h0 := mb_twoRings hc le_rfl ht.1 ht.2 (mul_nonneg hB₀ hL0.le) (fun y => avM P σ y 0)
      (fun y => (hInit y).trans (le_of_eq (by ring))) x
    have h0' : ‖propOp (mbPropSat P (n + 4) 0 t) (mbRing (mbTheta P t) (mbJ' n) (mbA' n)
        (mbRing (mbTheta P t) (mbJ n) (mbA n) fun x => avM P σ x 0)) x‖ ≤
        C2 * B₀ / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv x t) := by
      refine h0.trans (le_of_eq ?_)
      field_simp
      ring
    -- the forcing term
    have hb : ∀ s ∈ Icc (0 : ℝ) t,
        ‖propOp (mbPropSat P (n + 4) s t) (mbRing (mbTheta P t) (mbJ' n) (mbA' n)
          (mbRing (mbTheta P t) (mbJ n) (mbA n) ((fun x => mbFM P σ x s) + mbFtX P σ s))) x‖ ≤
        (C2 * Fc / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv x t)) * (vsHeight P.z s)⁻¹ := by
      intro s hs
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
      have hins := hc.inputs hs1
      have hLs := hins.lEta_pos
      have hηs := hins.height_pos
      have hφ : 0 ≤ Fc / vsHeight P.z s * P.lEta s := by positivity
      have h := mb_twoRings hc hs.1 hs.2 ht.2 hφ _
        (fun y => (mb_FFt_bound hA hc σ hσ A I hA0 hI0 hAv hIso hs1 y).trans
          (le_of_eq (by ring))) x
      refine h.trans (le_of_eq ?_)
      field_simp
      ring
    have hI := mb_norm_integral_le hzi ht hint x hb
    have hΛ : ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ ≤ mbLambda d (m * W) :=
      (vsIntRules (Nat.mul_pos (by have := hc.hm; omega) hc.hW) hc.hW d.delta0_pos.le
        d.kappa_pos (by linarith [d.C0_ge_one]) hc.hz ht.1 ht.2 one_pos).1
    have hLx := mb_LsAv_pos_nonneg hc ht x
    calc _ ≤ C2 * B₀ / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv x t) +
          C2 * Fc / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv x t) *
            ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ := (norm_add_le _ _).trans (add_le_add h0' hI)
      _ ≤ C2 * B₀ / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv x t) +
          C2 * Fc / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv x t) * mbLambda d (m * W) := by
          gcongr
      _ = _ := by ring
  · -- continuity of the forcing after the rings
    have hX := mb_contOn_X hA hc (n := n + 1) σ hσ
    have hF := mb_contOn_F hA hc (n := n + 1) σ hσ
    have hG := hF.add ((mb_contOn_G (mb_contOn_theta hc) hX (mbJ n) (mbA n)).add
      (mb_contOn_G (mb_contOn_theta hc) hX (mbJ' n) (mbA' n)))
    have hcont : ∀ (j a : Fin (n + 4)), Continuous (mbRing (N := m * W) (mbTheta P t) j a) := by
      intro j a
      refine continuous_pi fun x => ?_
      unfold mbRing
      exact continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_apply _)
    have hG' : ContinuousOn (fun s => (fun x => mbFM P σ x s) + mbFtX P σ s) (Icc 0 1) := by
      unfold mbFtX mbFt
      exact hG
    exact ((hcont _ _).comp ((hcont _ _))).comp_continuousOn hG'

end Bound

end BlockBand.Native.ErdosRiabov.MBound
