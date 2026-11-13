module

public import BlockBand.Native.ErdosRiabov.MBound.SatVB

/-!
# The saturated `M`-bound

For saturated patterns the averaged `M`-term is bounded by integrating its evolution in time.

* `mb_lsAv_antitone`: `L_s s^av_s ≤ L_t s^av_t` for `0 ≤ s ≤ t ≤ 1` (`mb_lsAv_mono` with the VS
  heights);
* `mb_oplus_bound`: `|(⊕_j T̂^{(j)}_s)[X_s](x)| ≤ k V_k η_s⁻¹ L_s s^av_s(x)` (every slot reduced
  to the last one by rotation, then the bound at the last slot);
* **`mbBounds_sat`**: for `k = n+4`, a saturated pattern, `t ∈ [0,1]` and the
  induction hypothesis (`AvB` for lengths `2..k-1`, `IsoB` for `3..k-1`),
  `|Tr[M^{(t)}_{[1,k]} S^{x_k}](x)| ≤ A^sat_k ℓ_tη_t s^av_{k,t}(x)`,
  `A^sat_k = B₀ + Λ (k V_k + F_k)` (`mbAsat`).
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

/-- `A^sat_k = B₀ + Λ (k V_k + F_k)` `k = n+4`. -/
def mbAsat (d : VSData) (Λ : ℝ) (n : ℕ) (A I : ℕ → ℝ) (B₀ : ℝ) : ℝ :=
  B₀ + Λ * ((n + 4 : ℕ) * mbVc d Λ n A I B₀ + mbFc d n A I)

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hc in
/-- `L_s s^av_s(x) ≤ L_t s^av_t(x)` for `0 ≤ s ≤ t ≤ 1`, `k ≥ 2`. -/
theorem mb_lsAv_antitone {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) {n : ℕ}
    (x : Fin (n + 2) → Fin (m * W)) :
    P.lEta s * P.sAv x s ≤ P.lEta t * P.sAv x t := by
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  have hηt := vsHeight_pos hc.zpos ht1
  have hts := mb_heights hc hst
  refine mb_lsAv_mono P t (hc.inputs ⟨hs0.trans hst, ht1⟩).lEta_pos ?_
    (hc.inputs ⟨hs0, hst.trans ht1⟩).nonneg ?_ x
  · unfold PsiData.lEta
    rw [hc.hPW]
    exact BlockBand.Adapters.ErdosRiabov.loc_mul_mono (m * W) W hηt hts
  · intro a b
    unfold PsiData.ups
    rw [hc.hPW, hc.hPD]
    exact polynomialControl_mono hN hc.hW (by linarith [d.D_ge_six]) hηt hts a b

include hA hc in

/-- The generator term at time `s` for a saturated pattern:
`|(⊕_j T̂^{(j)}_s)[X_s](x)| ≤ (n+4) V_k η_s⁻¹ L_s s^av_s(x)`.
-/
theorem mb_oplus_bound {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ τ : Fin (n + 4) → Bool, ¬ HasDesatFactor τ →
      ∀ y, ‖avM P τ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖mbOplus (mbTheta P s) (fun y => avM P σ y s) x‖ ≤
      (n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z s *
        (P.lEta s * P.sAv x s) := by
  unfold mbOplus
  refine (norm_sum_le _ _).trans ?_
  have hj : ∀ j : Fin (n + 4), ‖mbSlot (mbTheta P s) j (fun y => avM P σ y s) x‖ ≤
      mbVc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z s * (P.lEta s * P.sAv x s) := by
    intro j
    rw [mbSlot_avM_rotTo hA.cyclic P hc.profile hc.zpos.ne' hs (n := n + 2) _ σ j x]
    have hσ' := not_hasDesatFactor_comp hσ ((j : ℕ) + 1)
    have h := mbV_bound hA hc (fun i => σ ((finRotate (n + 4) ^ ((j : ℕ) + 1)) i)) hσ' A I hA0
      hI0 hAv hIso hB₀ (hInit _ hσ') hs (mbRotTo j x)
    rw [mb_sAv_rotTo] at h
    exact h
  calc _ ≤ ∑ j : Fin (n + 4), mbVc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z s *
        (P.lEta s * P.sAv x s) := Finset.sum_le_sum fun j _ => hj j
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

include hA hc in

/-- **The averaged `M`-bounds for saturated patterns** (under `MBAlg` and the initial bound
`hInit` for saturated patterns): for chain length `k = n+4`, a saturated pattern `σ`, the
induction hypothesis (`AvB(n', A n')` for `2 ≤ n' ≤ k-1`, `IsoB(n', I n')` for
`3 ≤ n' ≤ k-1`), `t ∈ [0,1]` and all sites:
`|Tr[M^{(t)}_{[1,k]}(x') S^{x_k}]| ≤ A^sat_k · ℓ_tη_t · s^av_{k,t}(x)` with
`A^sat_k = B₀ + Λ (k V_k + F_k)`, `Λ = c_m⁻¹ log((C₀+1)N)`. -/
theorem mbBounds_sat {n : ℕ} (σ : Fin (n + 4) → Bool) (hσ : ¬ HasDesatFactor σ) (A I : ℕ → ℝ)
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 4 → MBAvB P n' (A n'))
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 4 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hInit : ∀ τ : Fin (n + 4) → Bool, ¬ HasDesatFactor τ →
      ∀ y, ‖avM P τ y 0‖ ≤ B₀ * (P.lEta 0 * P.sAv y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 4) → Fin (m * W)) :
    ‖avM P σ x t‖ ≤ mbAsat d (mbLambda d (m * W)) n A I B₀ * (P.lEta t * P.sAv x t) := by
  have hΛ0 : 0 ≤ mbLambda d (m * W) :=
    mbLambda_nonneg d (Nat.mul_pos (by have := hc.hm; omega) hc.hW)
  obtain ⟨hFc, -, -, -, hVc⟩ := mb_consts_nonneg d hΛ0 n hA0 hI0 hB₀
  have hgen : ∀ s, propOp (mbGenSat P (n + 4) s) (fun y => avM P σ y s) =
      mbOplus (mbTheta P s) (fun y => avM P σ y s) := fun s => by
    rw [mbTheta, mbOplus_eq_propOp]
    rfl
  -- FTC
  have hcont : ContinuousOn (fun s => propOp (mbGenSat P (n + 4) s) (fun y => avM P σ y s) +
      fun y => mbFM P σ y s) (Icc (0 : ℝ) 1) := by
    simp_rw [hgen]
    exact (mb_contOn_oplus (mb_contOn_theta hc) (mb_contOn_X hA hc (n := n + 1) σ hσ)).add
      (mb_contOn_F hA hc (n := n + 1) σ hσ)
  have hint : IntervalIntegrable (fun s => propOp (mbGenSat P (n + 4) s)
      (fun y => avM P σ y s) + fun y => mbFM P σ y s) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact hcont.mono (Icc_subset_Icc le_rfl ht.2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => fun y => avM P σ y r)
    (fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact mb_hasDerivAt_X hA hc (n := n + 1) σ hσ ⟨hs.1, hs.2.trans ht.2⟩) hint
  have hX : avM P σ x t = avM P σ x 0 + (∫ s in (0 : ℝ)..t, (propOp (mbGenSat P (n + 4) s)
      (fun y => avM P σ y s) + fun y => mbFM P σ y s)) x := by
    rw [hftc]
    simp
  -- pointwise bound of the integrand
  have hb : ∀ s ∈ Icc (0 : ℝ) t, ‖(propOp (mbGenSat P (n + 4) s) (fun y => avM P σ y s) +
      fun y => mbFM P σ y s) x‖ ≤
      (((n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ + mbFc d n A I) *
        (P.lEta t * P.sAv x t)) * (vsHeight P.z s)⁻¹ := by
    intro s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hins := hc.inputs hs1
    have hηs := hins.height_pos
    have hmono := mb_lsAv_antitone hc hs.1 hs.2 ht.2 (n := n + 2) x
    rw [Pi.add_apply, hgen]
    have h1 := mb_oplus_bound hA hc σ hσ A I hA0 hI0 hAv hIso hB₀ hInit hs1 x
    have h2 := mbFM_bound P hs1 hins A I hA0 hI0 (fun n' h3 h4 => hAv n' (by omega) h4) hIso σ x
    have hLs : 0 ≤ P.lEta s * P.sAv x s := mb_LsAv_pos_nonneg hc hs1 x
    calc _ ≤ ‖mbOplus (mbTheta P s) (fun y => avM P σ y s) x‖ + ‖mbFM P σ x s‖ :=
          norm_add_le _ _
      _ ≤ (n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ / vsHeight P.z s *
            (P.lEta s * P.sAv x s) +
          d.Cwc / vsHeight P.z s * mbFPairSum (n + 4) A I * (P.lEta s * P.sAv x s) :=
          add_le_add h1 h2
      _ = (((n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ + mbFc d n A I) *
            (P.lEta s * P.sAv x s)) * (vsHeight P.z s)⁻¹ := by
          unfold mbFc
          field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono ?_)
            (inv_nonneg.mpr hηs.le)
          exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hVc) hFc
  have hI := mb_norm_integral_le hc.zpos ht hint x hb
  have hΛ : ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ ≤ mbLambda d (m * W) :=
    (vsIntRules (Nat.mul_pos (by have := hc.hm; omega) hc.hW) hc.hW d.delta0_pos.le
      d.kappa_pos (by linarith [d.C0_ge_one]) hc.hz ht.1 ht.2 one_pos).1
  have h0 : ‖avM P σ x 0‖ ≤ B₀ * (P.lEta t * P.sAv x t) :=
    (hInit σ hσ x).trans (mul_le_mul_of_nonneg_left
      (mb_lsAv_antitone hc le_rfl ht.1 ht.2 (n := n + 2) x) hB₀)
  have hLx := mb_LsAv_pos_nonneg hc ht x
  have hc0 : 0 ≤ ((n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ + mbFc d n A I) *
      (P.lEta t * P.sAv x t) :=
    mul_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hVc) hFc) hLx
  rw [hX]
  calc _ ≤ B₀ * (P.lEta t * P.sAv x t) +
        ((n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ + mbFc d n A I) *
          (P.lEta t * P.sAv x t) * ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ :=
      (norm_add_le _ _).trans (add_le_add h0 hI)
    _ ≤ B₀ * (P.lEta t * P.sAv x t) +
        ((n + 4 : ℕ) * mbVc d (mbLambda d (m * W)) n A I B₀ + mbFc d n A I) *
          (P.lEta t * P.sAv x t) * mbLambda d (m * W) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hΛ hc0)
    _ = _ := by
      unfold mbAsat
      ring

end BlockBand.Native.ErdosRiabov.MBound
