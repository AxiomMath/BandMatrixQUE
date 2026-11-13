module

public import BlockBand.Native.ErdosRiabov.Forcing.BoundAv

/-!
# Forcing bounds: the averaged F1 slot at `k = K = 8`

A bound on one F1 slot term of the averaged forcing for the longest chains `k = 8`.

The `9`-chain of the slot is cut after its fourth resolvent (`rot_cut`, `c = 3`): one cut works
for every slot `j`, since the rotated chain always starts at `ζ_j` (the two cases of `q(j)` in
Erdős–Riabov
are the same cut in the original labels). With the cut bounds `cutDiag`, `cutOff` and the
diagonal identity (`sAv_diag`):
`η |F1_j| ≤ C_S √C₁'' ((C₀+1)(I₄I₅ + I₄ + I₅) + √C₁'') · Y ψ^A_1 ψ^I_4 ψ^I_5 · L^{β_8} s^av_8`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Forcing

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)

variable {N : ℕ}

/-- The scalar inequality closing the `k = 8` bound, with `q = (ℓη)^{1/4}` and `s₁ = √C₁''`. -/
theorem k8_alg {η Y q sx pa p4 p5 i4 i5 s1 cS c0 : ℝ} (hη : 0 < η) (hηle : η ≤ c0 + 1)
    (hq1 : 1 ≤ q) (hY2 : (q ^ 2)⁻¹ ≤ Y) (hY4 : (q ^ 4)⁻¹ ≤ Y) (hsx : 0 ≤ sx) (hpa : 0 ≤ pa)
    (hp4 : 1 ≤ p4) (hp5 : 1 ≤ p5) (hi4 : 0 ≤ i4) (hi5 : 0 ≤ i5) (hs1 : 0 ≤ s1)
    (hcS : 0 ≤ cS) :
    η * (pa * (q ^ 4)⁻¹ * (p4 * 1 * (p5 * q) * (cS * (s1 * s1 / η * q ^ 2) * (q ^ 2 * sx)) +
      (i4 * q ^ 2 * (p5 * q) + p4 * 1 * (i5 * q ^ 2) + i4 * q ^ 2 * (i5 * q ^ 2)) *
        (cS * s1 * (q ^ 2)⁻¹ * (q ^ 2 * sx)))) ≤
      cS * s1 * ((c0 + 1) * (i4 * i5 + i4 + i5) + s1) * (Y * pa * p4 * p5) * (q ^ 3 * sx) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq1
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) hY2
  have e : η * (pa * (q ^ 4)⁻¹ * (p4 * 1 * (p5 * q) * (cS * (s1 * s1 / η * q ^ 2) *
      (q ^ 2 * sx)) + (i4 * q ^ 2 * (p5 * q) + p4 * 1 * (i5 * q ^ 2) +
        i4 * q ^ 2 * (i5 * q ^ 2)) * (cS * s1 * (q ^ 2)⁻¹ * (q ^ 2 * sx)))) =
      cS * s1 * (s1 * (pa * p4 * p5 * sx) * q +
        η * pa * sx * (i4 * p5 * q⁻¹ + p4 * i5 * (q ^ 2)⁻¹ + i4 * i5)) := by
    field_simp
  rw [e]
  have hYq2 : 1 ≤ Y * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hY2 (pow_pos hq0 2).le
    rwa [inv_mul_cancel₀ (pow_pos hq0 2).ne'] at h
  have hq2 : q ^ 2 ≤ q ^ 3 := pow_le_pow_right₀ hq1 (by norm_num)
  have hYq3 : 1 ≤ Y * q ^ 3 := hYq2.trans (mul_le_mul_of_nonneg_left hq2 hY.le)
  have hq3 : q ≤ Y * q ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hYq2 hq0.le
    calc q = q * 1 := (mul_one q).symm
      _ ≤ q * (Y * q ^ 2) := h
      _ = Y * q ^ 3 := by ring
  have hYr : q⁻¹ ≤ Y * q ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hY4 (pow_pos hq0 3).le
    calc q⁻¹ = (q ^ 4)⁻¹ * q ^ 3 := by field_simp
      _ ≤ Y * q ^ 3 := h
  have hYr2 : (q ^ 2)⁻¹ ≤ Y * q ^ 3 := hY2.trans (le_mul_of_one_le_right hY.le (one_le_pow₀ hq1))
  set Z := Y * q ^ 3
  have hZ0 : 0 ≤ Z := by positivity
  have h1 : i4 * p5 * q⁻¹ ≤ i4 * (Z * p4 * p5) := by
    have : q⁻¹ ≤ Z * p4 := hYr.trans (le_mul_of_one_le_right hZ0 hp4)
    calc i4 * p5 * q⁻¹ ≤ i4 * p5 * (Z * p4) := by gcongr
      _ = _ := by ring
  have h2 : p4 * i5 * (q ^ 2)⁻¹ ≤ i5 * (Z * p4 * p5) := by
    have : (q ^ 2)⁻¹ ≤ Z * p5 := hYr2.trans (le_mul_of_one_le_right hZ0 hp5)
    calc p4 * i5 * (q ^ 2)⁻¹ ≤ p4 * i5 * (Z * p5) := by gcongr
      _ = _ := by ring
  have h3 : i4 * i5 ≤ i4 * i5 * (Z * p4 * p5) := by
    have h45 : 1 ≤ p4 * p5 := one_le_mul_of_one_le_of_one_le hp4 hp5
    have : 1 ≤ Z * p4 * p5 := by
      calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ ≤ Z * (p4 * p5) := mul_le_mul hYq3 h45 zero_le_one hZ0
        _ = Z * p4 * p5 := by ring
    exact le_mul_of_one_le_right (mul_nonneg hi4 hi5) this
  have hin : i4 * p5 * q⁻¹ + p4 * i5 * (q ^ 2)⁻¹ + i4 * i5 ≤
      (i4 * i5 + i4 + i5) * (Z * p4 * p5) := by
    have := add_le_add (add_le_add h1 h2) h3
    linarith
  have hin0 : 0 ≤ i4 * p5 * q⁻¹ + p4 * i5 * (q ^ 2)⁻¹ + i4 * i5 := by positivity
  have hA : s1 * (pa * p4 * p5 * sx) * q ≤ s1 * (pa * p4 * p5 * sx) * Z :=
    mul_le_mul_of_nonneg_left hq3 (by positivity)
  have hB : η * pa * sx * (i4 * p5 * q⁻¹ + p4 * i5 * (q ^ 2)⁻¹ + i4 * i5) ≤
      (c0 + 1) * pa * sx * ((i4 * i5 + i4 + i5) * (Z * p4 * p5)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hηle hpa) hsx) hin
      hin0 (mul_nonneg (mul_nonneg (by linarith) hpa) hsx)
  calc cS * s1 * (s1 * (pa * p4 * p5 * sx) * q +
        η * pa * sx * (i4 * p5 * q⁻¹ + p4 * i5 * (q ^ 2)⁻¹ + i4 * i5))
      ≤ cS * s1 * (s1 * (pa * p4 * p5 * sx) * Z +
        (c0 + 1) * pa * sx * ((i4 * i5 + i4 + i5) * (Z * p4 * p5))) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (mul_nonneg hcS hs1)
    _ = _ := by simp only [Z]; ring

section K8

variable {d : VSData} {P : PsiData N} {t : ℝ} (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
  {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA)
  (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) (σ : Fin 8 → Bool) (x : Fin 8 → Fin N)
include c hAP hpsi1

/-- **F1**, one slot, `k = 8`. -/
theorem slot_avF1_K {I : ℕ → ℝ} (hI : ∀ n ∈ kRange, IsoBAt P t n (I n)) (hI0 : ∀ n, 0 ≤ I n)
    (j : Fin 8) :
    vsHeight P.z t * ‖f1Term P σ x t H j‖ ≤
      constS d * Real.sqrt d.C1pp * ((d.C0 + 1) * (I 4 * I 5 + I 4 + I 5) + Real.sqrt d.C1pp) *
        (yScale P t * psiA 1 * psiI 4 * psiI 5) * (P.lEta t ^ lossBeta 8 * P.sAv x t) := by
  have hη := c.height_pos
  have hL := c.lEta_pos
  have hU : ∀ a b, 0 ≤ P.ups t a b := fun a b => (c.pos a b).le
  have h4R : (4 : ℕ) ∈ kRange := mem_kRange (by norm_num) (by norm_num)
  have h5R : (5 : ℕ) ∈ kRange := mem_kRange (by norm_num) (by norm_num)
  set yA := segSites (rotSites x j) (⟨0, by omega⟩ : Fin 9) ⟨3, by omega⟩
  set yB := segSites (rotSites x j) (⟨4, by omega⟩ : Fin 9) ⟨8, by omega⟩
  set pA := segPat (rotPat σ j) (⟨0, by omega⟩ : Fin 9) ⟨3, by omega⟩
  set pB := segPat (rotPat σ j) (⟨4, by omega⟩ : Fin 9) ⟨8, by omega⟩
  set xs := rotSites x j ⟨3, by omega⟩
  set dA := psiI 4 * P.lEta t ^ lossAlpha 4
  set dB := psiI 5 * P.lEta t ^ lossAlpha 5
  set cA := I 4 * Real.sqrt (P.lEta t)
  set cB := I 5 * Real.sqrt (P.lEta t)
  have hdA : 0 ≤ dA := mul_nonneg (by linarith [(hpsi1 4).1]) (lEta_rpow_pos c _).le
  have hdB : 0 ≤ dB := mul_nonneg (by linarith [(hpsi1 5).1]) (lEta_rpow_pos c _).le
  have hcA : 0 ≤ cA := mul_nonneg (hI0 _) (Real.sqrt_nonneg _)
  have hcB : 0 ≤ cB := mul_nonneg (hI0 _) (Real.sqrt_nonneg _)
  have hpa : 0 ≤ psiA 1 := by linarith [(hpsi1 1).2]
  have hAb : ∀ p a, ‖gChain (patZ P.z pA t) (isoSlots P.S yA) H p a‖ ≤
      (dA + if p = a then cA else 0) * P.sIso p a yA t := by
    intro p a
    refine (norm_gChain_le c hAP h4R (hI 4 h4R) pA p a yA).trans (le_of_eq ?_)
    by_cases hpa' : p = a
    · subst hpa'; simp only [ite_true]; ring
    · simp only [hpa', ite_false]; ring
  have hBb : ∀ a p, ‖gChain (patZ P.z pB t) (isoSlots P.S yB) H a p‖ ≤
      (dB + if p = a then cB else 0) * P.sIso a p yB t := by
    intro a p
    refine (norm_gChain_le c hAP h5R (hI 5 h5R) pB a p yB).trans (le_of_eq ?_)
    by_cases hpa' : a = p
    · subst hpa'; simp only [ite_true]; ring
    · simp only [hpa', Ne.symm hpa', ite_false]; ring
  -- the diagonal entry of the cut chain
  have hG : ∀ p, ‖gChain (patZ P.z (rotPat σ j) t) (isoSlots P.S (rotSites x j)) H p p‖ ≤
      ∑ a, (P.S xs a) * ((dA + if p = a then cA else 0) * (dB + if p = a then cB else 0) *
        (P.sIso p a yA t * P.sIso a p yB t)) := by
    intro p
    rw [rot_cut P σ x t H j 3 (by norm_num), Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [obsMat, Matrix.mul_diagonal, norm_mul, norm_mul]
    simp only [Split.rowObs, Complex.norm_real, Real.norm_of_nonneg (c.stoch.nonneg _ _)]
    have h1 := hAb p a
    have h2 := hBb a p
    have hs1 := sIso_pos c p a yA
    have hs2 := sIso_pos c a p yB
    have hf1 : 0 ≤ dA + if p = a then cA else 0 := add_nonneg hdA (by split_ifs <;> simp [hcA])
    calc ‖gChain (patZ P.z pA t) (isoSlots P.S yA) H p a‖ * P.S xs a *
          ‖gChain (patZ P.z pB t) (isoSlots P.S yB) H a p‖
        ≤ ((dA + if p = a then cA else 0) * P.sIso p a yA t) * P.S xs a *
          ((dB + if p = a then cB else 0) * P.sIso a p yB t) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (c.stoch.nonneg _ _)) h2 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hf1 hs1.le) (c.stoch.nonneg _ _))
      _ = _ := by ring
  -- the two cut contractions
  let w : Fin 8 → Fin N := fun n => x ⟨((j : ℕ) + 4 + n) % 8, Nat.mod_lt _ (by norm_num)⟩
  have hwB : ∀ (n : ℕ) (hn : n < (8 : ℕ) - 4), yB ⟨n, by simp only; omega⟩ = w ⟨n, by omega⟩ := by
    intro n hn
    simp only [yB, w]
    rw [segSites_apply (rotSites x j) (by simp only [Fin.le_def]; omega)]
    simp only [rotSites]
    congr 1
    exact Fin.ext (by simp only; omega)
  have hwA : ∀ (n : ℕ) (hn : n < (3 : ℕ) - 0), yA ⟨n, by simp only; omega⟩ =
      w ⟨(8 : ℕ) - 4 + n, by omega⟩ := by
    intro n hn
    simp only [yA, w]
    rw [segSites_apply (rotSites x j) (by simp only [Fin.le_def]; omega)]
    simp only [rotSites]
    congr 1
    exact Fin.ext (by simp only; omega)
  have hoff := cutOff c (i := 3 - 0) (j := 8 - 4) (by norm_num) xs yA yB w hwB hwA
  have hdia := cutDiag c (i := 3 - 0) (j := 8 - 4) (by norm_num) xs yA yB w hwB hwA
  have hdiag := sAv_diag c (p := 7) (by norm_num) xs w w (fun n hn => rfl)
    (by simp only [w, xs, rotSites]; congr 1; exact Fin.ext (by simp only; omega))
  have hrot : P.sAv w t = P.sAv x t := contr_sAv_rotate P x w ((j : ℕ) + 4)
    (fun n hn => by simp only [w]; congr 1; exact Fin.ext (by simp only; omega)) t
  rw [hrot] at hdiag
  -- collecting the sum over `p`
  have hC' : 0 ≤ cA * dB + dA * cB + cA * cB := by positivity
  have hpt : ∀ p a : Fin N, (dA + if p = a then cA else 0) * (dB + if p = a then cB else 0) ≤
      dA * dB + if p = a then cA * dB + dA * cB + cA * cB else 0 := by
    intro p a
    split_ifs
    · nlinarith [mul_nonneg hcA hcB]
    · simp
  have hterm : ∀ p, ‖P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H *
      gChain (patZ P.z (rotPat σ j) t) (isoSlots P.S (rotSites x j)) H p p‖ ≤
      psiA 1 * (P.lEta t)⁻¹ * ∑ a, P.S xs a *
        ((dA * dB + if p = a then cA * dB + dA * cB + cA * cB else 0) *
          (P.sIso p a yA t * P.sIso a p yB t)) := by
    intro p
    rw [norm_mul]
    refine mul_le_mul (norm_avErr_one_le c hAP _ _) ((hG p).trans (Finset.sum_le_sum
      fun a _ => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hpt p a)
        (mul_nonneg (sIso_pos c _ _ _).le (sIso_pos c _ _ _).le)) (c.stoch.nonneg _ _)))
      (norm_nonneg _) (mul_nonneg hpa (inv_nonneg.mpr hL.le))
  have hsum : ∑ p, ∑ a, P.S xs a *
      ((dA * dB + if p = a then cA * dB + dA * cB + cA * cB else 0) *
        (P.sIso p a yA t * P.sIso a p yB t)) =
      dA * dB * ∑ a, P.S xs a * ∑ p, P.sIso p a yA t * P.sIso a p yB t +
        (cA * dB + dA * cB + cA * cB) *
          ∑ a, P.S xs a * (P.sIso a a yA t * P.sIso a a yB t) := by
    rw [Finset.sum_comm]
    have hin : ∀ a : Fin N, ∑ p, P.S xs a *
        ((dA * dB + if p = a then cA * dB + dA * cB + cA * cB else 0) *
          (P.sIso p a yA t * P.sIso a p yB t)) =
        dA * dB * (P.S xs a * ∑ p, P.sIso p a yA t * P.sIso a p yB t) +
          (cA * dB + dA * cB + cA * cB) * (P.S xs a * (P.sIso a a yA t * P.sIso a a yB t)) := by
      intro a
      rw [Finset.sum_congr rfl fun p _ => (show P.S xs a *
          ((dA * dB + if p = a then cA * dB + dA * cB + cA * cB else 0) *
            (P.sIso p a yA t * P.sIso a p yB t)) =
          dA * dB * (P.S xs a * (P.sIso p a yA t * P.sIso a p yB t)) +
            (if p = a then (cA * dB + dA * cB + cA * cB) *
              (P.S xs a * (P.sIso p a yA t * P.sIso a p yB t)) else 0) by split_ifs <;> ring),
        Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _),
        ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => hin a, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have hmain : ‖f1Term P σ x t H j‖ ≤ psiA 1 * (P.lEta t)⁻¹ *
      (dA * dB * (constS d * (d.C1pp / vsHeight P.z t * Real.sqrt (P.lEta t)) *
          P.sIso xs xs w t) +
        (cA * dB + dA * cB + cA * cB) *
          (constS d * Real.sqrt d.C1pp * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso xs xs w t)) := by
    unfold f1Term
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun p _ => hterm p).trans ?_)
    rw [← Finset.mul_sum, hsum]
    exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hoff
      (mul_nonneg hdA hdB)) (mul_le_mul_of_nonneg_left hdia hC'))
      (mul_nonneg hpa (inv_nonneg.mpr hL.le))
  -- powers of `L` in terms of `q = L^{1/4}`
  have hq0 : 0 < P.lEta t ^ (1 / 4 : ℝ) := lEta_rpow_pos c _
  have hq1 : 1 ≤ P.lEta t ^ (1 / 4 : ℝ) := Real.one_le_rpow c.one_le_lEta (by norm_num)
  have hpow : ∀ n : ℕ, P.lEta t ^ ((n : ℝ) / 4) = (P.lEta t ^ (1 / 4 : ℝ)) ^ n := fun n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have hq4 : P.lEta t = (P.lEta t ^ (1 / 4 : ℝ)) ^ 4 := by rw [← hpow 4]; norm_num
  have hsq : Real.sqrt (P.lEta t) = (P.lEta t ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← hpow 2]; norm_num
  have hh : P.lEta t ^ (-(1 / 2 : ℝ)) = ((P.lEta t ^ (1 / 4 : ℝ)) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hL.le, ← hpow 2]; norm_num
  have hb8 : P.lEta t ^ lossBeta 8 = (P.lEta t ^ (1 / 4 : ℝ)) ^ 3 := by
    rw [lossBeta_eight, ← hpow 3]; norm_num
  have ha4 : P.lEta t ^ lossAlpha 4 = 1 := by
    rw [lossAlpha_eq_zero (by norm_num), Real.rpow_zero]
  have ha5 : P.lEta t ^ lossAlpha 5 = P.lEta t ^ (1 / 4 : ℝ) := by rw [lossAlpha_five]
  have hSiso : P.sIso xs xs w t = (P.lEta t ^ (1 / 4 : ℝ)) ^ 2 * P.sAv x t := by
    rw [hdiag, hh]
    field_simp
  have hY2 : ((P.lEta t ^ (1 / 4 : ℝ)) ^ 2)⁻¹ ≤ yScale P t := hh ▸ rpow_neg_half_le_yScale c
  have hY4 : ((P.lEta t ^ (1 / 4 : ℝ)) ^ 4)⁻¹ ≤ yScale P t := hq4 ▸ inv_lEta_le_yScale c
  have hc1 : d.C1pp = Real.sqrt d.C1pp * Real.sqrt d.C1pp :=
    (Real.mul_self_sqrt (by linarith [d.one_le_C1pp])).symm
  have hcS : 0 ≤ constS d := by unfold constS; positivity
  have h := mul_le_mul_of_nonneg_left hmain hη.le
  simp only [dA, dB, cA, cB] at h
  rw [ha4, ha5, hsq, hh, hSiso] at h
  rw [show d.C1pp / vsHeight P.z t = Real.sqrt d.C1pp * Real.sqrt d.C1pp / vsHeight P.z t by
    rw [← hc1]] at h
  rw [hb8]
  conv at h => rhs; rw [show (P.lEta t)⁻¹ = (((P.lEta t ^ (1 / 4 : ℝ)) ^ 4))⁻¹ by rw [← hq4]]
  refine h.trans ?_
  exact k8_alg hη c.height_le hq1 hY2 hY4 (sAv_pos c x).le hpa (hpsi1 4).1 (hpsi1 5).1
    (hI0 4) (hI0 5) (Real.sqrt_nonneg d.C1pp) hcS

end K8

end BlockBand.Native.ErdosRiabov.Forcing
