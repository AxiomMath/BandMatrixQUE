module

public import BlockBand.Native.ErdosRiabov.Forcing.BoundIso
public import BlockBand.Native.ErdosRiabov.Forcing.BoundAvK
public import BlockBand.Native.ErdosRiabov.Forcing.Cyc
public import BlockBand.Native.ErdosRiabov.Forcing.Phi

/-!
# The forcing bounds

The averaged and isotropic forcing are bounded by explicit constants times the size functions
times the forcing control parameters `Φ`. Deterministic: a fixed time `t ∈ [0,1]` and any matrix
`H`. Hypotheses: the context `FCtx d P t`, the a priori bound `APriori P t H ψ^I ψ^A` with
`ψ ≥ 1`, the isotropic `M`-bounds `IsoBAt P t n (I n)` for `n ∈ kRange` with `I ≥ 0`; for `forcing_av` also the
extra bounds `ExtraBAt P t k e` (`2 ≤ k ≤ 7`) and `Split.CyclicStatement`.

* **`forcing_iso`**: `η |𝓕^{iso}_{[1,k]}(a,x',b)| ≤ isoConst d I k ·
  (ℓη)^{α_k} s^iso_k(a,x',b) · Φ^{iso}_k(ψ, ℓη, Y)`, `1 ≤ k ≤ 8`;
* **`forcing_av`**: `η |𝓕^{av}_{[1,k]}(x)| ≤ avConst d I e k · (ℓη)^{β_k} s^av_k(x) ·
  Φ^{av}_k(ψ, ℓη, Y)`, `1 ≤ k ≤ 8`.
`Φ` is `phiIsoF`/`phiAvF`; at the thresholds `ψ^iso`, `ψ^av` it is `≤` the control parameters of
the exponent inequality (`phiIsoF_le_phiIso`, `phiAvF_le_phiAv`). The constants are explicit in
`VSData`, `k` and the
`M`-bound constants (`ibar I = 1 + Σ_{n ≤ 8} I_n`); they are crude (a factor
`3k² + k + 1` from counting the pairs), which is harmless.
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
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo (lossAlpha lossBeta)

variable {N k : ℕ}

/-!
## Constants
-/

/-- `Ī = 1 + Σ_{n ≤ 8} I_n` (a majorant of every `I_n`, `n ≤ 8`, when `I ≥ 0`). -/
def ibar (I : ℕ → ℝ) : ℝ := 1 + ∑ n ∈ range 9, I n

theorem le_ibar {I : ℕ → ℝ} (hI0 : ∀ n, 0 ≤ I n) {n : ℕ} (hn : n ≤ 8) : I n ≤ ibar I := by
  have := Finset.single_le_sum (f := I) (fun i _ => hI0 i) (Finset.mem_range.mpr
    (show n < 9 by omega))
  unfold ibar
  linarith

theorem one_le_ibar {I : ℕ → ℝ} (hI0 : ∀ n, 0 ≤ I n) : 1 ≤ ibar I := by
  have := Finset.sum_nonneg (s := range 9) fun i _ => hI0 i
  unfold ibar
  linarith

/-- The per-term constant of `forcing_iso`. -/
def cIso (d : VSData) (I : ℕ → ℝ) : ℝ :=
  d.C1pp + (d.C0 + 1) * Real.sqrt d.C1pp * (2 * ibar I + ibar I * ibar I) + d.Cwc * ibar I +
    (d.C0 + 1 + Propagator.vsCK d * d.Cwc)

/-- The constant of `forcing_iso`: `(3k² + k + 1) cIso`. -/
def isoConst (d : VSData) (I : ℕ → ℝ) (k : ℕ) : ℝ := ((3 * k * k + k + 1 : ℕ) : ℝ) * cIso d I

/-- The per-term constant of `forcing_av` (`e` is the extra `M`-bound constant `E_k`). -/
def cAv (d : VSData) (I : ℕ → ℝ) (e : ℝ) : ℝ :=
  d.Cwc * ibar I + d.Cwc + e + constS d * Real.sqrt d.C1pp *
    ((d.C0 + 1) * (ibar I * ibar I + 2 * ibar I) + Real.sqrt d.C1pp)

/-- The constant of `forcing_av`: `(3k² + k + 1) cAv`. -/
def avConst (d : VSData) (I : ℕ → ℝ) (e : ℝ) (k : ℕ) : ℝ :=
  ((3 * k * k + k + 1 : ℕ) : ℝ) * cAv d I e

/-!
## Summation helpers
-/

theorem bound_combine {η T C m Q c Φ : ℝ} (h : η * T ≤ C * m * Q) (hC : 0 ≤ C) (hCc : C ≤ c)
    (hm : 0 ≤ m) (hmΦ : m ≤ Φ) (hQ : 0 ≤ Q) : η * T ≤ c * Q * Φ := by
  refine h.trans ?_
  have h1 : C * m ≤ c * Φ := mul_le_mul hCc hmΦ hm (hC.trans hCc)
  calc C * m * Q ≤ c * Φ * Q := mul_le_mul_of_nonneg_right h1 hQ
    _ = c * Q * Φ := by ring

theorem pair_sum_le (F : Fin k → Fin k → ℂ) {η B : ℝ} (hη : 0 ≤ η) (hB : 0 ≤ B)
    (h : ∀ i j : Fin k, i < j → η * ‖F i j‖ ≤ B) :
    η * ‖∑ j : Fin k, ∑ i with i < j, F i j‖ ≤ ((k * k : ℕ) : ℝ) * B := by
  calc η * ‖∑ j : Fin k, ∑ i with i < j, F i j‖
      ≤ η * ∑ j : Fin k, ∑ i with i < j, ‖F i j‖ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => norm_sum_le _ _)) hη
    _ = ∑ j : Fin k, ∑ i with i < j, η * ‖F i j‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin k, ∑ i with i < j, B := Finset.sum_le_sum fun j _ => Finset.sum_le_sum
        fun i hi => h i j (Finset.mem_filter.mp hi).2
    _ ≤ ∑ _j : Fin k, (k : ℝ) * B := Finset.sum_le_sum fun j _ => by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    _ = _ := by simp; ring

theorem slot_sum_le (F : Fin k → ℂ) {η B : ℝ} (hη : 0 ≤ η) (h : ∀ j, η * ‖F j‖ ≤ B) :
    η * ‖∑ j, F j‖ ≤ (k : ℝ) * B := by
  calc η * ‖∑ j, F j‖ ≤ η * ∑ j, ‖F j‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hη
    _ = ∑ j, η * ‖F j‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _j : Fin k, B := Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp

/-!
## The isotropic forcing bound
-/

section Main

variable {d : VSData} {P : PsiData N} {t : ℝ} (c : FCtx d P t) {H : Matrix (Fin N) (Fin N) ℂ}
  {psiI psiA : ℕ → ℝ} (hAP : APriori P t H psiI psiA)
  (hpsi1 : ∀ n, 1 ≤ psiI n ∧ 1 ≤ psiA n) {I : ℕ → ℝ} (hI : ∀ n ∈ kRange, IsoBAt P t n (I n))
  (hI0 : ∀ n, 0 ≤ I n)
include c hAP hpsi1 hI hI0

/-- **The isotropic forcing bound**: for `1 ≤ k ≤ 8`, every pattern and all sites,
`η |𝓕^{iso}| ≤ isoConst · (ℓη)^{α_k} s^iso_k · Φ^{iso}_k`, under the isotropic `M`-bounds
`IsoBAt`; `Split.CyclicStatement` is not used. -/
theorem forcing_iso (hk1 : 1 ≤ k) (hk : k ≤ 8) (σ : Fin k → Bool) (x : Fin k → Fin N)
    (a b : Fin N) :
    vsHeight P.z t * ‖forcingIso P σ a b x t H‖ ≤
      isoConst d I k * (P.lEta t ^ lossAlpha k * P.sIso a b x t) *
        phiIsoF psiI psiA (P.lEta t) (yScale P t) k := by
  have hη := c.height_pos
  have hpsi : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n := fun n =>
    ⟨by linarith [(hpsi1 n).1], by linarith [(hpsi1 n).2]⟩
  have hX := c.lEta_pos.le
  have hY := (yScale_pos c).le
  have hQ : 0 ≤ P.lEta t ^ lossAlpha k * P.sIso a b x t :=
    mul_nonneg (lEta_rpow_pos c _).le (sIso_pos c a b x).le
  have hΦ := phiIsoF_nonneg (k := k) hpsi hX hY
  have hib := one_le_ibar hI0
  have hC1 : 0 ≤ Real.sqrt d.C1pp := Real.sqrt_nonneg _
  have hC0 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have hCwc : 1 ≤ d.Cwc := d.one_le_Cwc
  have hCK : 0 ≤ Propagator.vsCK d := (Propagator.vsCK_pos d).le
  have hc0 : 0 ≤ cIso d I := by unfold cIso; have := d.one_le_C1pp; positivity
  set B := cIso d I * (P.lEta t ^ lossAlpha k * P.sIso a b x t) *
    phiIsoF psiI psiA (P.lEta t) (yScale P t) k
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hc0 hQ) hΦ
  -- the F1 slots
  have hF1 : ∀ j : Fin k, vsHeight P.z t * ‖f1IsoTerm P σ x t H j a b‖ ≤ B := by
    intro j
    have hj := j.isLt
    have h := slot_isoF1 c hAP hpsi1 σ x hk hI hI0 j a b
    have hi1 := le_ibar hI0 (show (j : ℕ) + 1 ≤ 8 by omega)
    have hi2 := le_ibar hI0 (show k - j ≤ 8 by omega)
    refine bound_combine h (add_nonneg (by linarith [d.one_le_C1pp]) (mul_nonneg
      (mul_nonneg hC0 hC1) (add_nonneg (add_nonneg (hI0 _) (hI0 _))
        (mul_nonneg (hI0 _) (hI0 _))))) ?_
      (mul_nonneg (mul_nonneg (mul_nonneg hY (hpsi 1).2) (hpsi _).1) (hpsi _).1)
      (iso_f1_le_phi hpsi hX hY hj) hQ
    unfold cIso
    have : I ((j : ℕ) + 1) + I (k - j) + I ((j : ℕ) + 1) * I (k - j) ≤
        2 * ibar I + ibar I * ibar I := by
      nlinarith [hI0 ((j : ℕ) + 1), hI0 (k - j)]
    have h2 := mul_le_mul_of_nonneg_left this (mul_nonneg hC0 hC1)
    have h3 : 0 ≤ d.Cwc * ibar I := mul_nonneg (by linarith) (by linarith)
    have h4 : 0 ≤ d.C0 + 1 + Propagator.vsCK d * d.Cwc := add_nonneg hC0 (mul_nonneg hCK
      (by linarith))
    linarith
  have hcw : d.Cwc ≤ cIso d I := by
    unfold cIso
    have h1 : d.Cwc ≤ d.Cwc * ibar I := le_mul_of_one_le_right (by linarith) hib
    have h2 : 0 ≤ (d.C0 + 1) * Real.sqrt d.C1pp * (2 * ibar I + ibar I * ibar I) :=
      mul_nonneg (mul_nonneg hC0 hC1) (by nlinarith)
    have h4 : 0 ≤ d.C0 + 1 + Propagator.vsCK d * d.Cwc := add_nonneg hC0 (mul_nonneg hCK
      (by linarith))
    linarith [d.one_le_C1pp]
  have hcwI : ∀ n, n ≤ 8 → d.Cwc * I n ≤ cIso d I := fun n hn => by
    unfold cIso
    have h1 : d.Cwc * I n ≤ d.Cwc * ibar I :=
      mul_le_mul_of_nonneg_left (le_ibar hI0 hn) (by linarith)
    have h2 : 0 ≤ (d.C0 + 1) * Real.sqrt d.C1pp * (2 * ibar I + ibar I * ibar I) :=
      mul_nonneg (mul_nonneg hC0 hC1) (by nlinarith)
    have h4 : 0 ≤ d.C0 + 1 + Propagator.vsCK d * d.Cwc := add_nonneg hC0 (mul_nonneg hCK
      (by linarith))
    linarith [d.one_le_C1pp]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- k = 1
    obtain rfl : k = 1 := by omega
    have e : forcingIso P σ a b x t H = f1IsoTerm P σ x t H 0 a b := by
      rw [forcingIso_one]
      unfold f1IsoTerm
      simp [gHead, gTail, segProd_self, isoSlots]
    rw [e]
    refine (hF1 0).trans ?_
    have h5 : (1 : ℝ) ≤ ((3 * 1 * 1 + 1 + 1 : ℕ) : ℝ) := by norm_num
    calc B = 1 * B := (one_mul B).symm
      _ ≤ ((3 * 1 * 1 + 1 + 1 : ℕ) : ℝ) * B := mul_le_mul_of_nonneg_right h5 hB
      _ = _ := by simp only [B, isoConst]; ring
  · -- k ≥ 2: the term list
    rw [forcingIso_termList P σ x t H c.stoch c.z_im.ne' ⟨c.t_nonneg, c.t_le_one⟩ hk2 a b]
    have hA : vsHeight P.z t * ‖famF1 P σ t H (isoSlots P.S x) a b‖ ≤ (k : ℝ) * B := by
      rw [famF1_eq, Matrix.sum_apply]
      exact slot_sum_le _ hη.le hF1
    have hQq : vsHeight P.z t * ‖famQ (aG P σ t H (isoSlots P.S x)) (aM P σ x t)
        (bGiso P σ x t H a b) (bMiso P σ x t a b)‖ ≤ ((k * k : ℕ) : ℝ) * B := by
      unfold famQ
      refine pair_sum_le _ hη.le hB fun i j hij => ?_
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      have h := pair_isoFQ c hAP hpsi1 σ x hk hij a b
      have hm := iso_fq_le_phi hpsi hX hY (k := k) (p := (j : ℕ) - i + 1) (by omega) (by omega)
      rw [show k + 2 - ((j : ℕ) - i + 1) = k - ((j : ℕ) - i) + 1 by omega] at hm
      exact bound_combine h (by linarith) hcw (mul_nonneg (mul_nonneg (hpsi _).1 (hpsi _).1)
        (lEta_rpow_pos c _).le) hm hQ
    have hM1 : vsHeight P.z t * ‖famM1 (aG P σ t H (isoSlots P.S x)) (aM P σ x t)
        (bMiso P σ x t a b)‖ ≤ ((k * k : ℕ) : ℝ) * B := by
      unfold famM1
      refine pair_sum_le _ hη.le hB fun i j hij => ?_
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      split_ifs with hc
      · have h := pair_isoFM1 c hAP hpsi1 σ x hk hI hI0 hij a b
        have hm := iso_fm_le_phi hpsi hX hY (k := k) (p := (j : ℕ) - i + 1) (by omega)
          (by omega)
        exact bound_combine h (mul_nonneg (by linarith) (hI0 _)) (hcwI _ (by omega))
          (mul_nonneg (hpsi _).1 (lEta_rpow_pos c _).le) hm hQ
      · rw [norm_zero, mul_zero]
        exact hB
    have hM2 : vsHeight P.z t * ‖famM2 (aM P σ x t) (bGiso P σ x t H a b)
        (bMiso P σ x t a b)‖ ≤ ((k * k : ℕ) : ℝ) * B := by
      unfold famM2
      refine pair_sum_le _ hη.le hB fun i j hij => ?_
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      split_ifs with hc
      · have h := pair_isoFM2 c hAP hpsi1 σ x hk hI hI0 hij a b
        have hm := iso_fm_le_phi hpsi hX hY (k := k) (p := k - ((j : ℕ) - i) + 1) (by omega)
          (by omega)
        exact bound_combine h (mul_nonneg (by linarith) (hI0 _)) (hcwI _ (by omega))
          (mul_nonneg (hpsi _).1 (lEta_rpow_pos c _).le) hm hQ
      · rw [norm_zero, mul_zero]
        exact hB
    have hL : vsHeight P.z t * ‖lastLine P σ x t H a b ⟨k - 1, by omega⟩‖ ≤ B := by
      have h := isoLast c hAP hpsi1 σ x hk hk2 a b
      refine bound_combine h (add_nonneg hC0 (mul_nonneg hCK (by linarith))) ?_
        (mul_nonneg (mul_nonneg (hpsi _).2 (lEta_rpow_pos c _).le) (lEta_rpow_pos c _).le)
        (iso_last_le_phi hpsi hX hY k) hQ
      unfold cIso
      have h1 : 0 ≤ d.Cwc * ibar I := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ (d.C0 + 1) * Real.sqrt d.C1pp * (2 * ibar I + ibar I * ibar I) :=
        mul_nonneg (mul_nonneg hC0 hC1) (by nlinarith)
      linarith [d.one_le_C1pp]
    have htri : vsHeight P.z t * ‖famF1 P σ t H (isoSlots P.S x) a b +
        famQ (aG P σ t H (isoSlots P.S x)) (aM P σ x t) (bGiso P σ x t H a b)
          (bMiso P σ x t a b) +
        famM1 (aG P σ t H (isoSlots P.S x)) (aM P σ x t) (bMiso P σ x t a b) +
        famM2 (aM P σ x t) (bGiso P σ x t H a b) (bMiso P σ x t a b) +
        lastLine P σ x t H a b ⟨k - 1, by omega⟩‖ ≤
        vsHeight P.z t * ‖famF1 P σ t H (isoSlots P.S x) a b‖ +
        vsHeight P.z t * ‖famQ (aG P σ t H (isoSlots P.S x)) (aM P σ x t)
          (bGiso P σ x t H a b) (bMiso P σ x t a b)‖ +
        vsHeight P.z t * ‖famM1 (aG P σ t H (isoSlots P.S x)) (aM P σ x t)
          (bMiso P σ x t a b)‖ +
        vsHeight P.z t * ‖famM2 (aM P σ x t) (bGiso P σ x t H a b) (bMiso P σ x t a b)‖ +
        vsHeight P.z t * ‖lastLine P σ x t H a b ⟨k - 1, by omega⟩‖ := by
      rw [← mul_add, ← mul_add, ← mul_add, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hη.le
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact norm_add_le _ _
    refine htri.trans ?_
    have hsum := add_le_add (add_le_add (add_le_add (add_le_add hA hQq) hM1) hM2) hL
    refine hsum.trans (le_of_eq ?_)
    simp only [B, isoConst]
    push_cast
    ring

/-- **The averaged forcing bound**: for `1 ≤ k ≤ 8`, every pattern and all sites,
`η |𝓕^{av}| ≤ avConst · (ℓη)^{β_k} s^av_k · Φ^{av}_k`. Under the hypothesis
`Split.CyclicStatement` (used for (FM1) only; proved as `MTerms.cyclic_holds`) and the extra
`M`-bound `ExtraBAt` for `2 ≤ k ≤ 7`. -/
theorem forcing_av (hC : Split.CyclicStatement) {e : ℝ} (he0 : 0 ≤ e)
    (hE : 2 ≤ k → k ≤ 7 → ExtraBAt P t k e) (hk1 : 1 ≤ k) (hk : k ≤ 8) (σ : Fin k → Bool)
    (x : Fin k → Fin N) :
    vsHeight P.z t * ‖forcingAv P σ x t H‖ ≤
      avConst d I e k * (P.lEta t ^ lossBeta k * P.sAv x t) *
        phiAvF psiI psiA (P.lEta t) (yScale P t) k := by
  have hη := c.height_pos
  have hpsi : ∀ n, 0 ≤ psiI n ∧ 0 ≤ psiA n := fun n =>
    ⟨by linarith [(hpsi1 n).1], by linarith [(hpsi1 n).2]⟩
  have hX := c.lEta_pos.le
  have hY := (yScale_pos c).le
  have hQ : 0 ≤ P.lEta t ^ lossBeta k * P.sAv x t :=
    mul_nonneg (lEta_rpow_pos c _).le (sAv_pos c x).le
  have hΦ := phiAvF_nonneg (k := k) hpsi hX hY
  have hib := one_le_ibar hI0
  have hC1 : 0 ≤ Real.sqrt d.C1pp := Real.sqrt_nonneg _
  have hC0 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have hCwc : 1 ≤ d.Cwc := d.one_le_Cwc
  have hcS : 0 ≤ constS d := by unfold constS; positivity
  have hK0 : 0 ≤ constS d * Real.sqrt d.C1pp *
      ((d.C0 + 1) * (ibar I * ibar I + 2 * ibar I) + Real.sqrt d.C1pp) :=
    mul_nonneg (mul_nonneg hcS hC1) (add_nonneg (mul_nonneg hC0 (by nlinarith)) hC1)
  have hc0 : 0 ≤ cAv d I e := by
    unfold cAv
    have : 0 ≤ d.Cwc * ibar I := mul_nonneg (by linarith) (by linarith)
    linarith
  set B := cAv d I e * (P.lEta t ^ lossBeta k * P.sAv x t) *
    phiAvF psiI psiA (P.lEta t) (yScale P t) k
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hc0 hQ) hΦ
  have hcw : d.Cwc ≤ cAv d I e := by
    unfold cAv
    have : 0 ≤ d.Cwc * ibar I := mul_nonneg (by linarith) (by linarith)
    linarith
  have hcwI : ∀ n, n ≤ 8 → d.Cwc * I n ≤ cAv d I e := fun n hn => by
    unfold cAv
    have : d.Cwc * I n ≤ d.Cwc * ibar I :=
      mul_le_mul_of_nonneg_left (le_ibar hI0 hn) (by linarith)
    linarith
  have hYh := rpow_neg_half_le_yScale c
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- k = 1
    obtain rfl : k = 1 := by omega
    have h := av_one c hAP hpsi1 σ x
    have hm : psiA 1 * psiI 2 * P.lEta t ^ (-(1 / 2 : ℝ)) ≤
        phiAvF psiI psiA (P.lEta t) (yScale P t) 1 := by
      have h1 := av_last_le_phi hpsi hX hY 1
      rw [ite_eq_left rfl] at h1
      refine le_trans ?_ h1
      calc psiA 1 * psiI 2 * P.lEta t ^ (-(1 / 2 : ℝ)) ≤ psiA 1 * psiI 2 * yScale P t :=
            mul_le_mul_of_nonneg_left hYh (mul_nonneg (hpsi 1).2 (hpsi 2).1)
        _ = _ := by ring
    have hb := bound_combine h (by linarith) hcw (mul_nonneg (mul_nonneg (hpsi 1).2
      (hpsi 2).1) (lEta_rpow_pos c _).le) hm hQ
    refine hb.trans ?_
    have h5 : (1 : ℝ) ≤ ((3 * 1 * 1 + 1 + 1 : ℕ) : ℝ) := by norm_num
    calc B = 1 * B := (one_mul B).symm
      _ ≤ ((3 * 1 * 1 + 1 + 1 : ℕ) : ℝ) * B := mul_le_mul_of_nonneg_right h5 hB
      _ = _ := by simp only [B, avConst]; ring
  · rw [forcingAv_termList P σ x t H c.stoch.symm hk2]
    -- the F1 slots
    have hF1 : ∀ j : Fin k, vsHeight P.z t * ‖f1Term P σ x t H j‖ ≤ B := by
      intro j
      rcases Nat.lt_or_ge k 8 with hk7 | hk8
      · have h := slot_avF1 c hAP hpsi1 σ x (by omega) (hE hk2 (by omega)) j
        have hm := av_last_le_phi hpsi hX hY k
        rw [ite_eq_right (by omega), ite_eq_left (by omega)] at hm
        have hm1 : 0 ≤ psiA 1 * psiI (k + 1) * P.lEta t ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg (mul_nonneg (hpsi 1).2 (hpsi _).1) (lEta_rpow_pos c _).le
        have hm2 : 0 ≤ psiA 1 * P.lEta t ^ (-lossBeta k) :=
          mul_nonneg (hpsi 1).2 (lEta_rpow_pos c _).le
        have hm1' : psiA 1 * psiI (k + 1) * P.lEta t ^ (-(1 / 2 : ℝ)) ≤
            yScale P t * psiA 1 * psiI (k + 1) := by
          calc _ ≤ psiA 1 * psiI (k + 1) * yScale P t :=
                mul_le_mul_of_nonneg_left hYh (mul_nonneg (hpsi 1).2 (hpsi _).1)
            _ = _ := by ring
        have h' : vsHeight P.z t * ‖f1Term P σ x t H j‖ ≤ (d.Cwc + e) *
            (yScale P t * psiA 1 * psiI (k + 1) + psiA 1 * P.lEta t ^ (-lossBeta k)) *
            (P.lEta t ^ lossBeta k * P.sAv x t) := by
          refine h.trans (mul_le_mul_of_nonneg_right ?_ hQ)
          nlinarith
        refine bound_combine h' (by linarith) ?_ (by linarith) hm hQ
        unfold cAv
        have : 0 ≤ d.Cwc * ibar I := mul_nonneg (by linarith) (by linarith)
        linarith
      · obtain rfl : k = 8 := by omega
        have h := slot_avF1_K c hAP hpsi1 σ x hI hI0 j
        have hm := av_last_le_phi hpsi hX hY 8
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hm
        refine bound_combine h (mul_nonneg (mul_nonneg hcS hC1) (add_nonneg (mul_nonneg hC0
          (add_nonneg (add_nonneg (mul_nonneg (hI0 _) (hI0 _)) (hI0 _)) (hI0 _))) hC1)) ?_
          (mul_nonneg (mul_nonneg (mul_nonneg hY (hpsi 1).2) (hpsi _).1) (hpsi _).1) hm hQ
        unfold cAv
        have h4 := le_ibar hI0 (show 4 ≤ 8 by norm_num)
        have h5 := le_ibar hI0 (show 5 ≤ 8 by norm_num)
        have hI4 := hI0 4
        have hI5 := hI0 5
        have hle : I 4 * I 5 + I 4 + I 5 ≤ ibar I * ibar I + 2 * ibar I := by nlinarith
        have hle' : constS d * Real.sqrt d.C1pp * ((d.C0 + 1) * (I 4 * I 5 + I 4 + I 5) +
            Real.sqrt d.C1pp) ≤ constS d * Real.sqrt d.C1pp *
            ((d.C0 + 1) * (ibar I * ibar I + 2 * ibar I) + Real.sqrt d.C1pp) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hle hC0) le_rfl)
            (mul_nonneg hcS hC1)
        have : 0 ≤ d.Cwc * ibar I := mul_nonneg (by linarith) (by linarith)
        linarith
    have hA : vsHeight P.z t * ‖trace (famF1 P σ t H (avSlots P.S x))‖ ≤ (k : ℝ) * B := by
      rw [famF1_eq, Matrix.trace_sum]
      refine slot_sum_le _ hη.le fun j => ?_
      rw [famF1_av_term P σ x t H j]
      exact hF1 j
    have hQq : vsHeight P.z t * ‖famQ (aG P σ t H (avSlots P.S x)) (aM P σ x t)
        (bGav P σ x t H) (bMav P σ x t)‖ ≤ ((k * k : ℕ) : ℝ) * B := by
      unfold famQ
      refine pair_sum_le _ hη.le hB fun i j hij => ?_
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      have h := pair_avFQ c hAP hpsi1 σ x hk hij
      rcases Nat.lt_or_ge ((j : ℕ) - i) 2 with h1 | h2
      · have hr : k - ((j : ℕ) - i) + 1 = k := by omega
        have hp : (j : ℕ) - i + 1 = 2 := by omega
        rw [hr, hp, sub_self, neg_zero, Real.rpow_zero, mul_one, lossAlpha_eq_zero (by norm_num),
          sub_zero] at h
        have hm := av_fq2_le_phi hpsi hX hY k
        exact bound_combine h (by linarith) hcw (by
          have := (hpsi k).2; have := (hpsi 2).1; have := lEta_rpow_pos c (-(1 / 2 : ℝ))
          positivity) (le_trans (le_of_eq (by ring)) hm) hQ
      · have hm := av_fq_le_phi hpsi hX hY (k := k) (r := k - ((j : ℕ) - i) + 1) (by omega)
          (by omega)
        rw [show k + 2 - (k - ((j : ℕ) - i) + 1) = (j : ℕ) - i + 1 by omega] at hm
        exact bound_combine h (by linarith) hcw (mul_nonneg (mul_nonneg (mul_nonneg (hpsi _).2
          (lEta_rpow_pos c _).le) (hpsi _).1) (lEta_rpow_pos c _).le) hm hQ
    have hM1 : vsHeight P.z t * ‖famM1 (aG P σ t H (avSlots P.S x)) (aM P σ x t)
        (bMav P σ x t)‖ ≤ ((k * k : ℕ) : ℝ) * B := by
      unfold famM1
      refine pair_sum_le _ hη.le hB fun i j hij => ?_
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      split_ifs with hc
      · have h := pair_avFM1 c hAP hpsi1 σ x hC hk hI hI0 hij
        have hm := av_fm_le_phi hpsi hX hY (k := k) (r := (j : ℕ) - i + 1) (by omega)
          (by omega)
        exact bound_combine h (mul_nonneg (by linarith) (hI0 _)) (hcwI _ (by omega))
          (mul_nonneg (hpsi _).2 (lEta_rpow_pos c _).le) hm hQ
      · rw [norm_zero, mul_zero]
        exact hB
    have hM2 : vsHeight P.z t * ‖famM2 (aM P σ x t) (bGav P σ x t H)
        (bMav P σ x t)‖ ≤ ((k * k : ℕ) : ℝ) * B := by
      unfold famM2
      refine pair_sum_le _ hη.le hB fun i j hij => ?_
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      split_ifs with hc
      · have h := pair_avFM2 c hAP hpsi1 σ x hk hI hI0 hij
        have hm := av_fm_le_phi hpsi hX hY (k := k) (r := k - ((j : ℕ) - i) + 1) (by omega)
          (by omega)
        exact bound_combine h (mul_nonneg (by linarith) (hI0 _)) (hcwI _ (by omega))
          (mul_nonneg (hpsi _).2 (lEta_rpow_pos c _).le) hm hQ
      · rw [norm_zero, mul_zero]
        exact hB
    have htri : vsHeight P.z t * ‖trace (famF1 P σ t H (avSlots P.S x)) +
        famQ (aG P σ t H (avSlots P.S x)) (aM P σ x t) (bGav P σ x t H) (bMav P σ x t) +
        famM1 (aG P σ t H (avSlots P.S x)) (aM P σ x t) (bMav P σ x t) +
        famM2 (aM P σ x t) (bGav P σ x t H) (bMav P σ x t)‖ ≤
        vsHeight P.z t * ‖trace (famF1 P σ t H (avSlots P.S x))‖ +
        vsHeight P.z t * ‖famQ (aG P σ t H (avSlots P.S x)) (aM P σ x t)
          (bGav P σ x t H) (bMav P σ x t)‖ +
        vsHeight P.z t * ‖famM1 (aG P σ t H (avSlots P.S x)) (aM P σ x t) (bMav P σ x t)‖ +
        vsHeight P.z t * ‖famM2 (aM P σ x t) (bGav P σ x t H) (bMav P σ x t)‖ := by
      rw [← mul_add, ← mul_add, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hη.le
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact norm_add_le _ _
    refine htri.trans ?_
    have hsum := add_le_add (add_le_add (add_le_add hA hQq) hM1) hM2
    refine hsum.trans ?_
    have hle : (k : ℝ) * B + ((k * k : ℕ) : ℝ) * B + ((k * k : ℕ) : ℝ) * B +
        ((k * k : ℕ) : ℝ) * B ≤ ((3 * k * k + k + 1 : ℕ) : ℝ) * B := by
      push_cast
      nlinarith
    refine hle.trans (le_of_eq ?_)
    simp only [B, avConst]
    ring

end Main

end BlockBand.Native.ErdosRiabov.Forcing
