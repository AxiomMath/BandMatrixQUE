module

public import BlockBand.Native.ErdosRiabov.MBound.Iso
public import BlockBand.Native.ErdosRiabov.MBound.Apply

/-!
# The `M`-bound constants and the joint induction

The averaged and isotropic `M`-bounds hold for all lengths, with constants defined by a
recursion in the length.

* `mbStepA`, `mbStepI`: one step of the recursion: `A_1 = I_1 = 1`,
  `A_2 = C_K²`, `I_2 = C_K`; for `k ≥ 3`, `A_k = A^ns_k` (`k` odd), `max(A^ns_k, A^sat_k)`
  (`k` even), `I_k = C_P^{k-1}(B₀_k + Λ F^iso_k)`, all in the table of the shorter lengths;
* `mbTab`: the table of lengths `< k` (structural recursion on `k`); the constants are
  `mbConstA d Λ B₀ k`, `mbConstI d Λ B₀ k` (with the table equations `mbConstA_eq`,
  `mbConstI_eq`, `mbTabA_lt`, and `mbTab_nonneg`);
* **`mbBounds_joint`**: under `MBCtx d P`, `MBAlg` and the initial bounds,
  `AvB(k, A_k) ∧ IsoB(k, I_k)` for every `k ≥ 1` (`Λ = mbLambda d (m W)`), by strong induction:
  the base cases for `k ≤ 2`; for `k ≥ 3`, `mbBounds_nonsat_av` (non-saturated patterns), the
  saturated bound for the saturated patterns (only for even `k`: odd patterns have a
  non-saturated factor, `hasDesatFactor_of_odd`), then `mbBounds_iso` (*av before iso*).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr

/-!
## The constants
-/

/-- One step for `A_k`, from the table `(A, I)` of the shorter lengths. -/
def mbStepA (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) (k : ℕ) (A I : ℕ → ℝ) : ℝ :=
  if k ≤ 1 then 1 else if k = 2 then vsCK d ^ 2 else
    if k % 2 = 1 then mbAns d Λ k A I (B₀ k)
    else max (mbAns d Λ k A I (B₀ k)) (mbAsat d Λ (k - 4) A I (B₀ k))

/-- One step for `I_k`, from `A_k` and the table `I` of the shorter lengths. -/
def mbStepI (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) (k : ℕ) (Ak : ℝ) (I : ℕ → ℝ) : ℝ :=
  if k ≤ 1 then 1 else if k = 2 then vsCK d else mbIsoK d Λ k Ak I (B₀ k)

/-- The table of the constants: `mbTab d Λ B₀ k n = (A_n, I_n)` for `n < k`, `(0, 0)` else. -/
def mbTab (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) : ℕ → ℕ → ℝ × ℝ
  | 0 => fun _ => (0, 0)
  | k + 1 => fun n =>
    if n < k then mbTab d Λ B₀ k n
    else if n = k then
      (mbStepA d Λ B₀ k (fun i => (mbTab d Λ B₀ k i).1) (fun i => (mbTab d Λ B₀ k i).2),
        mbStepI d Λ B₀ k
          (mbStepA d Λ B₀ k (fun i => (mbTab d Λ B₀ k i).1) (fun i => (mbTab d Λ B₀ k i).2))
          (fun i => (mbTab d Λ B₀ k i).2))
    else (0, 0)

/-- The `A`-column of the table of lengths `< k`. -/
def mbTabA (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) (k : ℕ) : ℕ → ℝ := fun i => (mbTab d Λ B₀ k i).1

/-- The `I`-column of the table of lengths `< k`. -/
def mbTabI (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) (k : ℕ) : ℕ → ℝ := fun i => (mbTab d Λ B₀ k i).2

/-- The averaged `M`-bound constant `A_k`. -/
def mbConstA (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) (k : ℕ) : ℝ := (mbTab d Λ B₀ (k + 1) k).1

/-- The isotropic `M`-bound constant `I_k`. -/
def mbConstI (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) (k : ℕ) : ℝ := (mbTab d Λ B₀ (k + 1) k).2

section Table

variable (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ)

theorem mbTab_succ_lt {k n : ℕ} (h : n < k) : mbTab d Λ B₀ (k + 1) n = mbTab d Λ B₀ k n := by
  show (if n < k then _ else _) = _
  rw [ite_eq_left h]

theorem mbTab_succ_self (k : ℕ) :
    mbTab d Λ B₀ (k + 1) k = (mbStepA d Λ B₀ k (mbTabA d Λ B₀ k) (mbTabI d Λ B₀ k),
      mbStepI d Λ B₀ k (mbStepA d Λ B₀ k (mbTabA d Λ B₀ k) (mbTabI d Λ B₀ k))
        (mbTabI d Λ B₀ k)) := by
  show (if k < k then _ else if k = k then _ else _) = _
  rw [ite_eq_right (lt_irrefl k), ite_eq_left rfl]
  rfl

theorem mbTab_succ_gt {k n : ℕ} (h : k < n) : mbTab d Λ B₀ (k + 1) n = (0, 0) := by
  show (if n < k then _ else if n = k then _ else _) = _
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The table is consistent: `mbTab k n = (A_n, I_n)` for `n < k`. -/
theorem mbTab_lt : ∀ k n, n < k → mbTab d Λ B₀ k n = mbTab d Λ B₀ (n + 1) n := by
  intro k
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n hn
    by_cases h : n < k
    · rw [mbTab_succ_lt d Λ B₀ h, ih n h]
    · obtain rfl : n = k := by omega
      rfl

theorem mbTabA_lt {k n : ℕ} (h : n < k) : mbTabA d Λ B₀ k n = mbConstA d Λ B₀ n := by
  unfold mbTabA mbConstA
  rw [mbTab_lt d Λ B₀ k n h]

theorem mbTabI_lt {k n : ℕ} (h : n < k) : mbTabI d Λ B₀ k n = mbConstI d Λ B₀ n := by
  unfold mbTabI mbConstI
  rw [mbTab_lt d Λ B₀ k n h]

/-- `A_k = mbStepA k (table of lengths < k)`. -/
theorem mbConstA_eq (k : ℕ) :
    mbConstA d Λ B₀ k = mbStepA d Λ B₀ k (mbTabA d Λ B₀ k) (mbTabI d Λ B₀ k) := by
  unfold mbConstA
  rw [mbTab_succ_self]

/-- `I_k = mbStepI k A_k (table of lengths < k)`. -/
theorem mbConstI_eq (k : ℕ) :
    mbConstI d Λ B₀ k = mbStepI d Λ B₀ k (mbConstA d Λ B₀ k) (mbTabI d Λ B₀ k) := by
  unfold mbConstI
  rw [mbTab_succ_self, mbConstA_eq]

theorem mbAns_nonneg {Λ' : ℝ} (hΛ : 0 ≤ Λ') (k : ℕ) {A I : ℕ → ℝ} (hA0 : ∀ n, 0 ≤ A n)
    (hI0 : ∀ n, 0 ≤ I n) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ mbAns d Λ' k A I b := by
  unfold mbAns
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  exact mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg hb (mul_nonneg hΛ
    (mul_nonneg (by linarith) (mbFPairSum_nonneg hA0 hI0))))

theorem mbStepA_nonneg (hΛ : 0 ≤ Λ) (hB₀ : ∀ k, 0 ≤ B₀ k) (k : ℕ) {A I : ℕ → ℝ}
    (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n) : 0 ≤ mbStepA d Λ B₀ k A I := by
  unfold mbStepA
  split_ifs
  · exact zero_le_one
  · exact pow_nonneg (vsCK_pos d).le 2
  · exact mbAns_nonneg d hΛ k hA0 hI0 (hB₀ k)
  · exact (mbAns_nonneg d hΛ k hA0 hI0 (hB₀ k)).trans (le_max_left _ _)

theorem mbStepI_nonneg (hΛ : 0 ≤ Λ) (hB₀ : ∀ k, 0 ≤ B₀ k) (k : ℕ) {Ak : ℝ} (hAk : 0 ≤ Ak)
    {I : ℕ → ℝ} (hI0 : ∀ n, 0 ≤ I n) : 0 ≤ mbStepI d Λ B₀ k Ak I := by
  unfold mbStepI
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hCK := (vsCK_pos d).le
  have hC0 := d.C0_ge_one
  split_ifs
  · exact zero_le_one
  · exact hCK
  · unfold mbIsoK mbFIsoC
    exact mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg (hB₀ k) (mul_nonneg hΛ
      (add_nonneg (mul_nonneg (by linarith) (mbFIsoPairSum_nonneg hI0))
        (mul_nonneg (by nlinarith) hAk))))

/-- All entries of the table are nonnegative (for `Λ ≥ 0`, `B₀ ≥ 0`). -/
theorem mbTab_nonneg (hΛ : 0 ≤ Λ) (hB₀ : ∀ k, 0 ≤ B₀ k) :
    ∀ k n, 0 ≤ (mbTab d Λ B₀ k n).1 ∧ 0 ≤ (mbTab d Λ B₀ k n).2 := by
  intro k
  induction k with
  | zero => intro n; exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
    intro n
    have hA0 : ∀ i, 0 ≤ mbTabA d Λ B₀ k i := fun i => (ih i).1
    have hI0 : ∀ i, 0 ≤ mbTabI d Λ B₀ k i := fun i => (ih i).2
    rcases lt_trichotomy n k with h | rfl | h
    · rw [mbTab_succ_lt d Λ B₀ h]
      exact ih n
    · rw [mbTab_succ_self]
      have hs := mbStepA_nonneg d Λ B₀ hΛ hB₀ n hA0 hI0
      exact ⟨hs, mbStepI_nonneg d Λ B₀ hΛ hB₀ n hs hI0⟩
    · rw [mbTab_succ_gt d Λ B₀ h]
      exact ⟨le_rfl, le_rfl⟩

theorem mbConstA_nonneg (hΛ : 0 ≤ Λ) (hB₀ : ∀ k, 0 ≤ B₀ k) (k : ℕ) :
    0 ≤ mbConstA d Λ B₀ k :=
  (mbTab_nonneg d Λ B₀ hΛ hB₀ (k + 1) k).1

theorem mbConstI_nonneg (hΛ : 0 ≤ Λ) (hB₀ : ∀ k, 0 ≤ B₀ k) (k : ℕ) :
    0 ≤ mbConstI d Λ B₀ k :=
  (mbTab_nonneg d Λ B₀ hΛ hB₀ (k + 1) k).2

end Table

/-!
## The joint induction
-/

section Joint

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hA hc in

/-- **The joint `M`-bounds**, under the hypothesis `MBAlg` (proved as
`Discharge.mbAlg_holds`) and the initial bounds `hInitAv`, `hInitIso` with constants
`B₀ k ≥ 0`: under `MBCtx d P`, for every `k ≥ 1`,
`|Tr[M^σ_t(x') S^{x_k}]| ≤ A_k ℓ_tη_t s^av_{k,t}(x)` and
`|(M^σ_t(x'))_{aa}| ≤ I_k √(ℓ_tη_t) s^iso_{k,t}(a,x',a)` for all `t ∈ [0,1]`, patterns and
sites, with `A_k = mbConstA d Λ B₀ k`, `I_k = mbConstI d Λ B₀ k`, `Λ = c_m⁻¹ log((C₀+1)N)`. -/
theorem mbBounds_joint (B₀ : ℕ → ℝ) (hB₀ : ∀ k, 0 ≤ B₀ k)
    (hInitAv : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin (m * W)),
      ‖avM P σ y 0‖ ≤ B₀ k * (P.lEta 0 * P.sAv y 0))
    (hInitIso : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin (m * W)) (y : Fin k → Fin (m * W)),
      ‖P.mChain σ y 0 a‖ ≤ B₀ k * (Real.sqrt (P.lEta 0) * P.sIso a a y 0)) :
    ∀ k, 1 ≤ k → MBAvB P k (mbConstA d (mbLambda d (m * W)) B₀ k) ∧
      MBIsoB P k (mbConstI d (mbLambda d (m * W)) B₀ k) := by
  have hΛ0 : 0 ≤ mbLambda d (m * W) :=
    mbLambda_nonneg d (Nat.mul_pos (by have := hc.hm; omega) hc.hW)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk1
  rw [mbConstI_eq, mbConstA_eq]
  rcases Nat.lt_or_ge k 3 with hk | hk
  · -- base cases
    rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
    · simp only [mbStepA, mbStepI, le_refl, ite_true]
      exact ⟨mbBase_av1 hc, mbBase_iso1 hc⟩
    · have h21 : ¬ (2 ≤ 1) := by omega
      simp only [mbStepA, mbStepI, h21, ite_false, ite_true]
      exact ⟨mbBase_av2 hc, mbBase_iso2 hc⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  -- the table of the shorter lengths
  have hAt0 : ∀ i, 0 ≤ mbTabA d (mbLambda d (m * W)) B₀ (n + 3) i := fun i =>
    (mbTab_nonneg d _ B₀ hΛ0 hB₀ (n + 3) i).1
  have hIt0 : ∀ i, 0 ≤ mbTabI d (mbLambda d (m * W)) B₀ (n + 3) i := fun i =>
    (mbTab_nonneg d _ B₀ hΛ0 hB₀ (n + 3) i).2
  have hAv : ∀ n', 2 ≤ n' → n' + 1 ≤ n + 3 →
      MBAvB P n' (mbTabA d (mbLambda d (m * W)) B₀ (n + 3) n') := fun n' h2 h3 => by
    rw [mbTabA_lt d _ B₀ (by omega)]
    exact (ih n' (by omega) (by omega)).1
  have hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 →
      MBIsoB P n' (mbTabI d (mbLambda d (m * W)) B₀ (n + 3) n') := fun n' h2 h3 => by
    rw [mbTabI_lt d _ B₀ (by omega)]
    exact (ih n' (by omega) (by omega)).2
  have hns : ¬ (n + 3 ≤ 1) := by omega
  have hn2 : ¬ (n + 3 = 2) := by omega
  -- (1)+(2): the averaged bound, av before iso
  have hAvk : MBAvB P (n + 3) (mbStepA d (mbLambda d (m * W)) B₀ (n + 3)
      (mbTabA d (mbLambda d (m * W)) B₀ (n + 3)) (mbTabI d (mbLambda d (m * W)) B₀ (n + 3))) := by
    intro t ht σ x
    have hLx := mb_LsAv_pos_nonneg hc ht x
    by_cases hσ : HasDesatFactor σ
    · -- the non-saturated patterns
      have h := mbBounds_nonsat_av hA hc σ hσ _ _ hAt0 hIt0
        (fun n' h3 h4 => hAv n' (by omega) h4) hIso (hB₀ (n + 3)) (hInitAv (n + 3) σ) ht x
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hLx)
      unfold mbStepA
      rw [ite_eq_right hns, ite_eq_right hn2]
      split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    · -- the saturated patterns: the length is even
      have hev : ¬ Odd (n + 3) := fun hodd => hσ (hasDesatFactor_of_odd hodd σ)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
        rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
        · exact absurd ⟨r + 1, by omega⟩ hev
        · omega⟩
      have h := mbBounds_sat hA hc (n := n') σ hσ _ _ hAt0 hIt0 hAv hIso (hB₀ (n' + 1 + 3))
        (fun τ _ => hInitAv (n' + 1 + 3) τ) ht x
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hLx)
      have hpar : ¬ ((n' + 1 + 3) % 2 = 1) := fun h1 => hev (Nat.odd_iff.mpr h1)
      unfold mbStepA
      rw [ite_eq_right hns, ite_eq_right hn2, ite_eq_right hpar,
        show n' + 1 + 3 - 4 = n' by omega]
      exact le_max_right _ _
  -- (3): the isotropic bound
  have hAk0 : 0 ≤ mbStepA d (mbLambda d (m * W)) B₀ (n + 3)
      (mbTabA d (mbLambda d (m * W)) B₀ (n + 3)) (mbTabI d (mbLambda d (m * W)) B₀ (n + 3)) :=
    mbStepA_nonneg d _ B₀ hΛ0 hB₀ _ hAt0 hIt0
  refine ⟨hAvk, ?_⟩
  intro t ht σ a x
  unfold mbStepI
  rw [ite_eq_right hns, ite_eq_right hn2]
  exact mbBounds_iso hA hc σ hAk0 hAvk _ hIt0 hIso (hB₀ (n + 3)) a (hInitIso (n + 3) σ a) ht x

end Joint

end BlockBand.Native.ErdosRiabov.MBound
