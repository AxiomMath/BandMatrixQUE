module

public import BlockBand.Native.ErdosRiabov.Forcing.Phi
public import BlockBand.Native.ErdosRiabov.QV.Mart

/-!
# Master inequalities: monotonicity of `Φ` and `φ^{qv} ≤ φ`

Monotonicity of the forcing control parameters along the flow, and comparison of the
quadratic-variation control parameters with the control parameters `φ`.

* `lossBeta_mono`: `β_j ≤ β_k` for `j ≤ k ≤ 8`.
* `phiAvF_anti`, `phiIsoF_anti`: the forcing control parameters
  `Φ^{av/iso,f}_k(ψ, X, Y)` are antitone in `X = ℓη` and monotone in `Y = √(Nη)/(ℓη)` (every
  exponent of `X` is `≤ 0`, every exponent of `Y` is `≥ 0`), for `ψ ≥ 0`, `k ≤ 8`.
* `yScale_anti`: `Y_s ≤ Y_t` for `0 ≤ s ≤ t ≤ 1` (from `ℓ(η_t) ≤ √(η_s/η_t) ℓ(η_s)`).
* `qvPhiAv_le_phiAv`, `qvPhiIso_le_phiIso`: at the thresholds the quadratic-variation control
  parameters (`QV.qvPhiAv`, `QV.qvPhiIso`) are terms of the control parameters
  `Flow.Expo.phiAv`/`phiIso`, hence `≤` them.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MI

open Finset
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo
open BlockBand.Native.ErdosRiabov.Flow.Expo.Mono
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV

/-!
## Loss exponents
-/

/-- `β_j ≤ β_k` for `j ≤ k ≤ 8`. -/
theorem lossBeta_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ 8) : lossBeta j ≤ lossBeta k := by
  by_cases hk7 : k ≤ 7
  · rw [lossBeta_eq (hjk.trans hk7), lossBeta_eq hk7]
    exact lossAlpha_mono (by omega)
  · have hk8 : k = 8 := by omega
    subst hk8
    by_cases hj : j = 8
    · rw [hj]
    · rw [lossBeta_eq (by omega), lossBeta_eight]
      linarith [qv_alpha_le_half (k := j + 1) (by omega)]

/-- `β_k ≤ α_k + 1/2` for `k ≤ 8`. -/
theorem lossBeta_le_alpha_add {k : ℕ} (hk : k ≤ 8) : lossBeta k ≤ lossAlpha k + 1 / 2 := by
  by_cases hk7 : k ≤ 7
  · rw [lossBeta_eq hk7]
    linarith [qv_alpha_le_half (k := k + 1) (by omega), lossAlpha_nonneg k]
  · have hk8 : k = 8 := by omega
    subst hk8
    rw [lossBeta_eight, lossAlpha_eight]
    norm_num

/-!
## Monotonicity of the forcing control parameters
-/

section Mono

variable {psiI psiA : ℕ → ℝ} (hpsi : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n) {X X' Y Y' : ℝ}
  (hX' : 0 < X') (hXX : X' ≤ X) (hYY : Y ≤ Y')

include hX' hXX in
theorem rpow_neg_anti {g : ℝ} (hg : 0 ≤ g) : X ^ (-g) ≤ X' ^ (-g) :=
  Real.rpow_le_rpow_of_nonpos hX' hXX (by linarith)

include hX' hXX in
theorem rpow_neg_nonneg_left {g : ℝ} : 0 ≤ X ^ (-g) :=
  Real.rpow_nonneg (hX'.le.trans hXX) _

include hpsi hX' hXX hYY in

/-- **Monotonicity of the averaged forcing parameter.**
`Φ^{av,f}_k(ψ, X, Y) ≤ Φ^{av,f}_k(ψ, X', Y')` for `0 < X' ≤ X`, `Y ≤ Y'`, `ψ ≥ 0`, `k ≤ 8`.
-/
theorem phiAvF_anti {k : ℕ} (hk : k ≤ 8) :
    phiAvF psiI psiA X Y k ≤ phiAvF psiI psiA X' Y' k := by
  have hX0 : 0 < X := hX'.trans_le hXX
  have hI := fun n => (hpsi n).1
  have hA := fun n => (hpsi n).2
  unfold phiAvF
  refine add_le_add (add_le_add ?_ ?_) ?_
  · refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hb : 0 ≤ lossBeta k - lossBeta (2 + i) := by
      linarith [lossBeta_mono (j := 2 + i) (k := k) (by omega) hk]
    have ha : 0 ≤ 1 / 2 - lossAlpha (k + 2 - (2 + i)) := by
      linarith [qv_alpha_le_half (k := k + 2 - (2 + i)) (by omega)]
    have h1 := rpow_neg_anti hX' hXX hb
    have h2 := rpow_neg_anti hX' hXX ha
    have h1' := rpow_neg_nonneg_left hX' hXX (g := lossBeta k - lossBeta (2 + i))
    have h2' := rpow_neg_nonneg_left hX' hXX (g := 1 / 2 - lossAlpha (k + 2 - (2 + i)))
    have hA2 := hA (2 + i)
    have hI2 := hI (k + 2 - (2 + i))
    refine add_le_add (mul_le_mul_of_nonneg_left h1 hA2) ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hA2) hI2) h2
      h2' (mul_nonneg (mul_nonneg hA2 (h1'.trans h1)) hI2)
  · exact mul_le_mul_of_nonneg_left (rpow_neg_anti hX' hXX (by norm_num))
      (mul_nonneg (hI 2) (hA k))
  · split_ifs with h1 h7
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hYY (hA 1)) (hI 2)
    · refine add_le_add ?_ (mul_le_mul_of_nonneg_left
        (rpow_neg_anti hX' hXX (qv_beta_nonneg k)) (hA 1))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hYY (hA 1)) (hI _)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hYY (hA 1)) (hI 4)) (hI 5)

include hpsi hX' hXX hYY in

/-- **Monotonicity of the isotropic forcing parameter.**
`Φ^{iso,f}_k(ψ, X, Y) ≤ Φ^{iso,f}_k(ψ, X', Y')` for `0 < X' ≤ X`, `Y ≤ Y'`, `ψ ≥ 0`, `k ≤ 8`.
-/
theorem phiIsoF_anti {k : ℕ} (hk : k ≤ 8) :
    phiIsoF psiI psiA X Y k ≤ phiIsoF psiI psiA X' Y' k := by
  have hX0 : 0 < X := hX'.trans_le hXX
  have hI := fun n => (hpsi n).1
  have hA := fun n => (hpsi n).2
  have hh : X ^ (-(1 / 2 : ℝ)) ≤ X' ^ (-(1 / 2 : ℝ)) := rpow_neg_anti hX' hXX (by norm_num)
  unfold phiIsoF
  refine add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonneg_left (rpow_neg_anti hX' hXX
      (by linarith [lossAlpha_mono (j := 2 + i) (k := k) (by omega)])) (hI _)
  · refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hYY (hA 1)) (hI _)) (hI _)
  · exact mul_le_mul_of_nonneg_left hh (hA 1)
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left hh
      (mul_nonneg (hI _) (hI _))
  · have hg : 0 ≤ lossAlpha k - lossBeta k + 1 / 2 := by
      linarith [lossBeta_le_alpha_add hk]
    have e : ∀ Z : ℝ, 0 < Z → psiA k * Z ^ (-(lossAlpha k - lossBeta k)) * Z ^ (-(1 / 2 : ℝ)) =
        psiA k * Z ^ (-(lossAlpha k - lossBeta k + 1 / 2)) := fun Z hZ => by
      rw [mul_assoc, ← Real.rpow_add hZ]
      congr 2
      ring
    rw [e X hX0, e X' hX']
    exact mul_le_mul_of_nonneg_left (rpow_neg_anti hX' hXX hg) (hA k)

end Mono

/-!
## Monotonicity of `Y` along the flow
-/

/-- **`Y_s ≤ Y_t`** for `0 ≤ s ≤ t ≤ 1` (`Im z > 0`, `N, W ≥ 1`): from
`ℓ(η_t) ≤ √(η_s/η_t) ℓ(η_s)` (`Kernel.loc_le_sqrt_ratio_mul`, `η_t ≤ η_s`).
-/
theorem yScale_anti {N : ℕ} (P : Psi.PsiData N) (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    {s t : ℝ} (hst : s ≤ t) (ht1 : t ≤ 1) : yScale P s ≤ yScale P t := by
  have hηt := vsHeight_pos hz ht1
  have hηs := vsHeight_pos hz (hst.trans ht1)
  have hηts : vsHeight P.z t ≤ vsHeight P.z s := by
    have h := vsHeight_sub P.z s t
    have hy := (semicircleM_im_pos hz).le
    nlinarith
  have hℓt := Adapters.ErdosRiabov.loc_pos hN hW hηt
  have hℓs := Adapters.ErdosRiabov.loc_pos hN hW hηs
  have hloc := loc_le_sqrt_ratio_mul N P.W hηt hηts
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold yScale Psi.PsiData.lEta
  set ℓt := localizationLength N P.W (vsHeight P.z t)
  set ℓs := localizationLength N P.W (vsHeight P.z s)
  set ηt := vsHeight P.z t
  set ηs := vsHeight P.z s
  rw [div_le_div_iff₀ (mul_pos hℓs hηs) (mul_pos hℓt hηt)]
  have e1 : Real.sqrt (N * ηs) = Real.sqrt N * Real.sqrt ηs := Real.sqrt_mul hN0.le _
  have e2 : Real.sqrt (N * ηt) = Real.sqrt N * Real.sqrt ηt := Real.sqrt_mul hN0.le _
  have e3 : Real.sqrt (ηs / ηt) = Real.sqrt ηs / Real.sqrt ηt := Real.sqrt_div' _ hηt.le
  rw [e3] at hloc
  have hst' : 0 < Real.sqrt ηt := Real.sqrt_pos.mpr hηt
  have hss : 0 < Real.sqrt ηs := Real.sqrt_pos.mpr hηs
  have hsqt : Real.sqrt ηt * Real.sqrt ηt = ηt := Real.mul_self_sqrt hηt.le
  have hsqs : Real.sqrt ηs * Real.sqrt ηs = ηs := Real.mul_self_sqrt hηs.le
  rw [e1, e2]
  have hloc' : ℓt * Real.sqrt ηt ≤ Real.sqrt ηs * ℓs := by
    have h := mul_le_mul_of_nonneg_right hloc hst'.le
    calc ℓt * Real.sqrt ηt ≤ Real.sqrt ηs / Real.sqrt ηt * ℓs * Real.sqrt ηt := h
      _ = Real.sqrt ηs * ℓs := by field_simp
  have hsN := Real.sqrt_nonneg (N : ℝ)
  calc Real.sqrt N * Real.sqrt ηs * (ℓt * ηt)
      = Real.sqrt N * Real.sqrt ηs * Real.sqrt ηt * (ℓt * Real.sqrt ηt) := by
        linear_combination (-(Real.sqrt N * Real.sqrt ηs * ℓt)) * hsqt
    _ ≤ Real.sqrt N * Real.sqrt ηs * Real.sqrt ηt * (Real.sqrt ηs * ℓs) :=
        mul_le_mul_of_nonneg_left hloc' (by positivity)
    _ = Real.sqrt N * Real.sqrt ηt * (ℓs * ηs) := by
        linear_combination (Real.sqrt N * Real.sqrt ηt * ℓs) * hsqs

/-!
## `φ^{qv} ≤ φ` at the thresholds
-/

section Thresholds

/-- A pure `X`-monomial (`a = s = 0`). -/
def PureX (m : Mono) : Prop := m.a = 0 ∧ m.s = 0

theorem pureX_mul {m m' : Mono} (h : PureX m) (h' : PureX m') : PureX (m * m') := by
  unfold PureX at *
  simp [h.1, h.2, h'.1, h'.2]

theorem pureX_div {m m' : Mono} (h : PureX m) (h' : PureX m') : PureX (m / m') := by
  unfold PureX at *
  show m.a - m'.a = 0 ∧ m.s - m'.s = 0
  simp [h.1, h.2, h'.1, h'.2]

theorem pureX_alphaM (k : ℕ) : PureX (alphaM k) := alphaM_as k

theorem pureX_betaM (k : ℕ) : PureX (betaM k) := betaM_as k

theorem pureX_lossC (q : ℚ) : PureX (lossC q) := by
  unfold PureX lossC
  exact ⟨rfl, rfl⟩

theorem gval_lossC (q : ℚ) : gval (lossC q) = q := by
  simp [gval, lossC]

theorem value_pureX' {N ξ X Y : ℝ} {m : Mono} (h : PureX m) :
    m.value N ξ X Y = X ^ (-gval m) := value_pureX h.1 h.2

variable {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y)
include hN hX hY

/-- **`φ^{av,qv}_k ≤ φ^{av}_k`** at the thresholds `thrIso`, `thrAv` (`1 ≤ k ≤ 8`): the QV term of
`Flow.Expo.avTerms` is `QV.qvPhiAv`.
-/
theorem qvPhiAv_le_phiAv {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) :
    qvPhiAv (thrIso N ξ) (thrAv N ξ) k X ≤ phiAv N ξ X Y k := by
  have vb := fun j => value_basic N ξ X Y (k := 0) (by norm_num) j 0
  have hmul := fun m m' => Mono.value_mul (ξ := ξ) hN hX hY m m'
  have hq : Term.value N ξ X Y (if k ≤ 3 then
      Term.sqrtOne (pI (2 * k + 2) * (lossC (1 / 2) / alphaM (2 * k + 2)))
    else if k ≤ 7 then Term.mono (pI (k + 1))
    else Term.monoSqrtOne (pI 5) (pA 8 * (lossC 1 / betaM 8))) =
      qvPhiAv (thrIso N ξ) (thrAv N ξ) k X := by
    unfold qvPhiAv
    split_ifs with h3 h7
    · simp only [Term.value, hmul, (vb _).1, value_half_div_alpha (show 2 * k + 2 ≤ 8 by omega)]
    · simp only [Term.value, (vb _).1]
    · have hk8 : k = 8 := by omega
      subst hk8
      rw [Term.value, hmul, (vb _).1, (vb _).2.1,
        value_pureX' (pureX_div (pureX_lossC 1) (pureX_betaM 8)), gval_div, gval_lossC,
        gval_betaM le_rfl]
      push_cast
      ring_nf
  rw [← hq]
  unfold phiAv avTerms
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  have h1 := sum_value_nonneg (ξ := ξ) hN hX hY [Term.mono Mono.one]
  have h2 := sum_value_nonneg (ξ := ξ) hN hX hY ((List.range' 2 (k - 2)).flatMap (fun j =>
    [Term.mono (pA j * (betaM k / betaM j)),
     Term.mono (pA j * (betaM k / betaM j) * pI (k + 2 - j) *
       (lossC (1 / 2) / alphaM (k + 2 - j)))]))
  have h3 := Term.value_nonneg' (ξ := ξ) hN hX hY (Term.mono (pI 2 * pA k * lossC (1 / 2)))
  have h4 := sum_value_nonneg (ξ := ξ) hN hX hY (if k = 1 then [Term.mono (sqY * pA 1 * pI 2)]
   else if k ≤ 7 then [Term.mono (sqY * pA 1 * pI (k + 1)), Term.mono (pA 1 * betaM k)]
   else [Term.mono (sqY * pA 1 * pI 4 * pI 5)])
  have h5 := sum_value_nonneg (ξ := ξ) hN hX hY (if k % 2 = 0 then
     [Term.mono (pA (k - 1) * (betaM k / betaM (k - 1)))] ++
       (if 4 ≤ k then [Term.mono (pA (k - 2) * (betaM k / betaM (k - 2)))] else [])
   else [])
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
  linarith

/-- **`φ^{iso,qv}_k ≤ φ^{iso}_k`** at the thresholds `thrIso`, `thrAv` (`1 ≤ k ≤ 8`): the three QV
terms of `Flow.Expo.isoTerms` are those of `QV.qvPhiIso`.
-/
theorem qvPhiIso_le_phiIso {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) :
    qvPhiIso (thrIso N ξ) (thrAv N ξ) k X ≤ phiIso N ξ X Y k := by
  have vb := fun j => value_basic N ξ X Y (k := 0) (by norm_num) j 0
  have hmul := fun m m' => Mono.value_mul (ξ := ξ) hN hX hY m m'
  have hQ1 : Term.value N ξ X Y (Term.mono (pI k * (pI 2).half * lossC (1 / 4))) =
      thrIso N ξ k * Real.sqrt (thrIso N ξ 2) * X ^ (-(1 / 4 : ℝ)) := by
    rw [Term.value, hmul, hmul, Mono.value_half hN hX hY, (vb _).1, (vb _).1,
      (value_basic N ξ X Y (k := 0) (by norm_num) 0 (1 / 4)).2.2.2.2.1]
    push_cast
    ring_nf
  have hQ2 : (List.map (Term.value N ξ X Y) ((List.range' 2 ((k + 1) / 2 - 1)).map (fun j =>
      Term.monoSqrtOne (pI (k - j + 1) * (alphaM k / alphaM (k - j + 1)))
        (pI (2 * j) * (lossC (1 / 2) / alphaM (2 * j)))))).sum =
      ∑ j ∈ Finset.Icc 2 ((k + 1) / 2), qvPhiMid (thrIso N ξ) k j X := by
    rw [List.map_map, sum_map_range', ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    have e : (k + 1) / 2 + 1 - 2 = (k + 1) / 2 - 1 := by omega
    rw [e]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have h2 : 2 * (2 + i) ≤ 8 := by omega
    simp only [Function.comp_apply, Term.value, hmul, (vb _).1,
      value_div_alpha hk (show k - (2 + i) + 1 ≤ 8 by omega), value_half_div_alpha h2, qvPhiMid]
  have hQ3 : Term.value N ξ X Y (if k ≤ 4 then
        Term.sqrtOne (pI (2 * k) * (lossC (1 / 2) / alphaM (2 * k)))
      else if k ≤ 7 then
        Term.sqrtMono (pI (k - 1) * pI (k + 1) *
          (alphaM k * alphaM k / alphaM (k - 1) / alphaM (k + 1)))
      else Term.monoSqrtOne (pI 4) (pA 8 * (lossC 1 / betaM 8))) =
      qvPhiTilde (thrIso N ξ) (thrAv N ξ) k X := by
    unfold qvPhiTilde
    split_ifs with h4 h7
    · simp only [Term.value, hmul, (vb _).1, value_half_div_alpha (show 2 * k ≤ 8 by omega)]
    · have hp : PureX (alphaM k * alphaM k / alphaM (k - 1) / alphaM (k + 1)) :=
        pureX_div (pureX_div (pureX_mul (pureX_alphaM k) (pureX_alphaM k)) (pureX_alphaM _))
          (pureX_alphaM _)
      rw [Term.value, hmul, hmul, (vb _).1, (vb _).1, value_pureX' hp, gval_div, gval_div,
        gval_mul, gval_alphaM hk, gval_alphaM (show k - 1 ≤ 8 by omega),
        gval_alphaM (show k + 1 ≤ 8 by omega)]
      congr 2
      ring
    · have hk8 : k = 8 := by omega
      subst hk8
      rw [Term.value, hmul, (vb _).1, (vb _).2.1,
        value_pureX' (pureX_div (pureX_lossC 1) (pureX_betaM 8)), gval_div, gval_lossC,
        gval_betaM le_rfl]
      push_cast
      ring_nf
  unfold qvPhiIso phiIso isoTerms
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [hQ1, hQ2, hQ3]
  have h1 := Term.value_nonneg' (ξ := ξ) hN hX hY (Term.mono Mono.one)
  have h2 := sum_value_nonneg (ξ := ξ) hN hX hY ((List.range' 2 (k - 2)).map
    (fun j => Term.mono (pI j * (alphaM k / alphaM j))))
  have h3 := sum_value_nonneg (ξ := ξ) hN hX hY ((List.range' 1 k).map
    (fun i => Term.mono (sqY * pA 1 * pI i * pI (k - i + 1))))
  have h4 := Term.value_nonneg' (ξ := ξ) hN hX hY (Term.mono (pA 1 * lossC (1 / 2)))
  have h5 := sum_value_nonneg (ξ := ξ) hN hX hY
    (((List.range' 2 (k - 1)).filter (fun j => k - j + 2 ≤ 8)).map
      (fun j => Term.mono (pI j * pI (k - j + 2) * lossC (1 / 2))))
  have h6 := Term.value_nonneg' (ξ := ξ) hN hX hY
    (Term.mono (pA k * (alphaM k / betaM k) * lossC (1 / 2)))
  linarith

end Thresholds

end BlockBand.Native.ErdosRiabov.MI
