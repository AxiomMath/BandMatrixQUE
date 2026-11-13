module

public import BlockBand.Native.ErdosRiabov.MBound.Joint
public import BlockBand.Native.ErdosRiabov.Split.MTermsStatement

/-!
# The log-power bound on the `M`-bound constants

The `M`-bound constants of length `k` are bounded by `C (log N)^{2^k - 4}`.

* `mb_pow_ns`, `mb_pow_sat`, `mb_pow_iso`, `mb_pow_step`: one step of the recursion. If the
  constants of the lengths `< k` are `≤ M` (`M ≥ 1`), `B₀ k ≤ B` (`B ≥ 1`) and `0 ≤ Λ ≤ L`,
  `L ≥ 1`, then `A_k, I_k ≤ K_k L⁴ M² B` with `K_k = mbPowK d k` explicit in `VSData` and `k`
  (`A^ns ≤ ·L M²B`, `A^sat ≤ ·L³M²B`, `I_k ≤ ·L⁴M²B`);
* **`mbConst_le_pow`**: for every `k` and `j ≤ k`,
  `A_j, I_j ≤ c_k L^{e_k}` with `e_k = 2^k − 4` (`mbPowExp`, truncated: `e_0 = e_1 = e_2 = 0`) and
  `c_k = mbPowC d B k` (`c_k = K_k B c_{k-1}²`, `c_{≤2} = 1 + C_K² + C_K`), where `B ≥ 1` bounds
  `B₀ j` for `j ≤ k`. The `max` in the recursion is handled by bounding both branches
  (`A_k` is not a polynomial in `Λ`, but it is bounded by one);
* `mbConst_le_log_pow` (consumer form): for `N ≥ 2`, `Λ = mbLambda d N = c_m⁻¹ log((C₀+1)N)`:
  `A_k, I_k ≤ c_k (mbLogC d)^{e_k} (log N)^{e_k}`, with `mbLogC d` depending only on `VSData`;
* `mbBounds_joint_log`: `mbBounds_joint` with these constants:
  `AvB(k, C (log N)^{C'})` and `IsoB(k, C (log N)^{C'})`, `N = m W`, `C' = 2^k − 4`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr

/-- The `M`-term algebra `Split.MTermAlgebra` gives the three statements of `MBAlg` used by the
`M`-bounds. -/
theorem MBAlg.of_mTermAlgebra (h : Split.MTermAlgebra) : MBAlg := by
  obtain ⟨-, hcyc, hward, hderiv, -⟩ := h
  exact ⟨hderiv, hcyc, hward⟩

/-!
## Real-number helpers
-/

theorem mb_pow_B {x c Y B : ℝ} (hx : x ≤ c * Y) (h0 : 0 ≤ c * Y) (hB : 1 ≤ B) :
    x ≤ c * (Y * B) := by
  rw [← mul_assoc]
  exact hx.trans (le_mul_of_one_le_right h0 hB)

theorem mb_pow_weak {x p Y Y' B : ℝ} (hx : x ≤ p * (Y * B)) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hYY : Y ≤ Y') : x ≤ p * (Y' * B) :=
  hx.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hYY hB) hp)

theorem mb_pow_lin {Λ L F p Y B : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L) (hp : 0 ≤ p) (hY : 0 ≤ Y)
    (hB : 0 ≤ B) (hF : F ≤ p * (Y * B)) : Λ * F ≤ p * (L * Y * B) := by
  have h1 : Λ * F ≤ Λ * (p * (Y * B)) := mul_le_mul_of_nonneg_left hF hΛ0
  have h2 : Λ * (p * (Y * B)) ≤ L * (p * (Y * B)) :=
    mul_le_mul_of_nonneg_right hΛ (mul_nonneg hp (mul_nonneg hY hB))
  calc Λ * F ≤ L * (p * (Y * B)) := h1.trans h2
    _ = p * (L * Y * B) := by ring

theorem mb_pow_aff {b Λ L F p Y B : ℝ} (hb : b ≤ B) (hB : 1 ≤ B) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L)
    (hL : 1 ≤ L) (hY : 1 ≤ Y) (hp : 0 ≤ p) (hF : F ≤ p * (Y * B)) :
    b + Λ * F ≤ (1 + p) * (L * Y * B) := by
  have h1 := mb_pow_lin hΛ0 hΛ hp (by linarith) (by linarith) hF
  have h2 : B ≤ L * Y * B :=
    le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hL hY)
  linarith

/-!
## The pair sums
-/

theorem mbFPairSum_le {k : ℕ} {A I : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hA0 : ∀ n, 0 ≤ A n)
    (hA : ∀ n, n < k → A n ≤ M) (hI : ∀ n, n < k → I n ≤ M) :
    mbFPairSum k A I ≤ (k : ℝ) ^ 2 * M ^ 2 := by
  unfold mbFPairSum
  calc _ ≤ ∑ j : Fin k, ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), M ^ 2 := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i hi => ?_
        have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
        have hjk := j.isLt
        split_ifs with hc
        · rw [sq]
          exact mul_le_mul (hI _ (by omega)) (hA _ (by omega)) (hA0 _) hM
        · exact sq_nonneg M
    _ ≤ ∑ _j : Fin k, ∑ _i : Fin k, M ^ 2 :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg M
    _ = (k : ℝ) ^ 2 * M ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem mbFIsoPairSum_le {k : ℕ} {I : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hI0 : ∀ n, 0 ≤ I n)
    (hI : ∀ n, n < k → I n ≤ M) : mbFIsoPairSum k I ≤ (k : ℝ) ^ 2 * M ^ 2 := by
  unfold mbFIsoPairSum
  calc _ ≤ ∑ j : Fin k, ∑ i ∈ Finset.univ.filter (fun i : Fin k => i < j), M ^ 2 := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i hi => ?_
        have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
        have hjk := j.isLt
        split_ifs with hc
        · rw [sq]
          exact mul_le_mul (hI _ (by omega)) (hI _ (by omega)) (hI0 _) hM
        · exact sq_nonneg M
    _ ≤ ∑ _j : Fin k, ∑ _i : Fin k, M ^ 2 :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg M
    _ = (k : ℝ) ^ 2 * M ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-!
## The step constants
-/

/-- `C_wc k²`. -/
def mbPowF (d : VSData) (k : ℕ) : ℝ := d.Cwc * (k : ℝ) ^ 2

/-- `4 C_K √C₁''` (the `F̃` coefficient). -/
def mbPowG (d : VSData) : ℝ := 4 * vsCK d * Real.sqrt d.C1pp

/-- `2 C_K² C_wc √C₁'' + C_K² C₁''` (the `R` coefficient). -/
def mbPowR (d : VSData) : ℝ :=
  2 * vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp + vsCK d ^ 2 * d.C1pp

/-- The `Z` coefficient, chain length `n+4`. -/
def mbPowZ (d : VSData) (n : ℕ) : ℝ :=
  onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) * (1 + (mbPowF d (n + 4) + mbPowG d))

/-- The `V` coefficient, chain length `n+4`. -/
def mbPowV (d : VSData) (n : ℕ) : ℝ :=
  vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) * (1 + mbPowF d (n + 4)) +
    kernelActionConst d ^ (n + 5) * (mbPowZ d n + mbPowR d)

/-- The `A^sat` coefficient, chain length `n+4` (`A^sat ≤ · L³ M² B`). -/
def mbPowSat (d : VSData) (n : ℕ) : ℝ :=
  1 + ((n + 4 : ℕ) * mbPowV d n + mbPowF d (n + 4))

/-- The `A^ns` coefficient (`A^ns ≤ · L M² B`). -/
def mbPowNs (d : VSData) (k : ℕ) : ℝ := kernelActionConst d ^ k * (1 + mbPowF d k)

/-- The `A_k` coefficient (`A_k ≤ · L³ M² B`). -/
def mbPowAv (d : VSData) (k : ℕ) : ℝ := mbPowNs d k + mbPowSat d (k - 4)

/-- The `I_k` coefficient given the `A_k` coefficient `a` (`I_k ≤ · L⁴ M² B`). -/
def mbPowIso (d : VSData) (k : ℕ) (a : ℝ) : ℝ :=
  kernelActionConst d ^ (k - 1) * (1 + (mbPowF d k + (d.C0 + 1 + vsCK d * d.Cwc) * a))

/-- The step constant `K_k` (`≥ 1`, also covering the base values `1, C_K, C_K²`). -/
def mbPowK (d : VSData) (k : ℕ) : ℝ :=
  1 + vsCK d ^ 2 + vsCK d + mbPowAv d k + mbPowIso d k (mbPowAv d k)

section Consts

variable (d : VSData)

theorem mbPowF_nonneg (k : ℕ) : 0 ≤ mbPowF d k :=
  mul_nonneg (by linarith [d.one_le_Cwc]) (sq_nonneg _)

theorem mbPowG_nonneg : 0 ≤ mbPowG d :=
  mul_nonneg (mul_nonneg (by norm_num) (vsCK_pos d).le) (Real.sqrt_nonneg _)

theorem mbPowR_nonneg : 0 ≤ mbPowR d := by
  have hCK := (vsCK_pos d).le
  have hCwc := d.one_le_Cwc
  have hC1 := d.one_le_C1pp
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hCK 2))
    (by linarith)) (Real.sqrt_nonneg _)) (mul_nonneg (pow_nonneg hCK 2) (by linarith))

theorem mbPowZ_nonneg (n : ℕ) : 0 ≤ mbPowZ d n := by
  have hCP := kernelActionConst_ge_one d
  have := mbPowF_nonneg d (n + 4)
  have := mbPowG_nonneg d
  exact mul_nonneg (mul_nonneg (pow_nonneg (onestepConst_nonneg d) 2)
    (pow_nonneg (by linarith) _)) (by linarith)

theorem mbPowV_nonneg (n : ℕ) : 0 ≤ mbPowV d n := by
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hCK := (vsCK_pos d).le
  have := mbPowF_nonneg d (n + 4)
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCK (by linarith))
    (pow_nonneg (by linarith) _)) (by linarith)) (mul_nonneg (pow_nonneg (by linarith) _)
      (add_nonneg (mbPowZ_nonneg d n) (mbPowR_nonneg d)))

theorem mbPowSat_nonneg (n : ℕ) : 0 ≤ mbPowSat d n := by
  have h1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) (n + 4)) (mbPowV_nonneg d n)
  have h2 := mbPowF_nonneg d (n + 4)
  unfold mbPowSat
  linarith

theorem mbPowNs_nonneg (k : ℕ) : 0 ≤ mbPowNs d k := by
  have hCP := kernelActionConst_ge_one d
  have := mbPowF_nonneg d k
  exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)

theorem mbPowAv_nonneg (k : ℕ) : 0 ≤ mbPowAv d k :=
  add_nonneg (mbPowNs_nonneg d k) (mbPowSat_nonneg d (k - 4))

theorem mbPowIso_nonneg (k : ℕ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ mbPowIso d k a := by
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hCK := (vsCK_pos d).le
  have hC0 := d.C0_ge_one
  have h3 : 0 ≤ d.C0 + 1 + vsCK d * d.Cwc := by nlinarith
  have := mbPowF_nonneg d k
  have := mul_nonneg h3 ha
  exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)

theorem mbPowK_ge_one (k : ℕ) : 1 ≤ mbPowK d k := by
  have := mbPowAv_nonneg d k
  have := mbPowIso_nonneg d k (mbPowAv_nonneg d k)
  have := (vsCK_pos d).le
  have := sq_nonneg (vsCK d)
  unfold mbPowK
  linarith

end Consts

/-!
## One step of the recursion
-/

section Step

variable (d : VSData) {Λ L M B b : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L) (hL : 1 ≤ L) (hM : 1 ≤ M)
  (hB : 1 ≤ B) (hb : b ≤ B)

include hΛ0 hΛ hL hM hB hb in

/-- `A^ns_k ≤ mbPowNs d k · L³ M² B` if the constants of lengths `< k` are `≤ M`. -/
theorem mb_pow_ns (k : ℕ) {A I : ℕ → ℝ} (hA0 : ∀ j, 0 ≤ A j) (hA : ∀ j, j < k → A j ≤ M)
    (hI : ∀ j, j < k → I j ≤ M) :
    mbAns d Λ k A I b ≤ mbPowNs d k * (L ^ 3 * M ^ 2 * B) := by
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hB0 : 0 ≤ B := by linarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hY1 : M ^ 2 ≤ L * M ^ 2 := le_mul_of_one_le_left (by linarith) hL
  have hY2 : L * M ^ 2 ≤ L * (L * M ^ 2) := le_mul_of_one_le_left (by linarith) hL
  have hY2' : 1 ≤ L * (L * M ^ 2) := (hM2.trans hY1).trans hY2
  have hf0 := mbPowF_nonneg d k
  have hPS := mbFPairSum_le (k := k) (by linarith) hA0 hA hI
  have hF : d.Cwc * mbFPairSum k A I ≤ mbPowF d k * (M ^ 2 * B) := by
    refine mb_pow_B ?_ (mul_nonneg hf0 (by linarith)) hB
    calc d.Cwc * mbFPairSum k A I ≤ d.Cwc * ((k : ℝ) ^ 2 * M ^ 2) :=
          mul_le_mul_of_nonneg_left hPS (by linarith)
      _ = _ := by unfold mbPowF; ring
  have h := mb_pow_aff hb hB hΛ0 hΛ hL hY2' hf0
    (mb_pow_weak (mb_pow_weak hF hf0 hB0 hY1) hf0 hB0 hY2)
  calc mbAns d Λ k A I b = kernelActionConst d ^ k * (b + Λ * (d.Cwc * mbFPairSum k A I)) := rfl
    _ ≤ kernelActionConst d ^ k * ((1 + mbPowF d k) * (L * (L * (L * M ^ 2)) * B)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg (by linarith) _)
    _ = _ := by unfold mbPowNs; ring

include hΛ0 hΛ hL hM hB hb in

/-- `A^sat_{n+4} ≤ mbPowSat d n · L³ M² B` if the constants of lengths `< n+4` are `≤ M`. -/
theorem mb_pow_sat (n : ℕ) {A I : ℕ → ℝ} (hA0 : ∀ j, 0 ≤ A j) (hA : ∀ j, j < n + 4 → A j ≤ M)
    (hI : ∀ j, j < n + 4 → I j ≤ M) :
    mbAsat d Λ n A I b ≤ mbPowSat d n * (L ^ 3 * M ^ 2 * B) := by
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hCK := (vsCK_pos d).le
  have hC1 := d.one_le_C1pp
  have hS := Real.sqrt_nonneg d.C1pp
  have hB0 : 0 ≤ B := by linarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hY1 : M ^ 2 ≤ L * M ^ 2 := le_mul_of_one_le_left (by linarith) hL
  have hY1' : 1 ≤ L * M ^ 2 := hM2.trans hY1
  have hY2 : L * M ^ 2 ≤ L * (L * M ^ 2) := le_mul_of_one_le_left (by linarith) hL
  have hY2' : 1 ≤ L * (L * M ^ 2) := hY1'.trans hY2
  have hf0 := mbPowF_nonneg d (n + 4)
  have hg0 := mbPowG_nonneg d
  have hr0 := mbPowR_nonneg d
  have hz0 := mbPowZ_nonneg d n
  have hv0 := mbPowV_nonneg d n
  have hPS := mbFPairSum_le (k := n + 4) (by linarith) hA0 hA hI
  have hF : mbFc d n A I ≤ mbPowF d (n + 4) * (M ^ 2 * B) := by
    refine mb_pow_B ?_ (mul_nonneg hf0 (by linarith)) hB
    calc mbFc d n A I ≤ d.Cwc * (((n + 4 : ℕ) : ℝ) ^ 2 * M ^ 2) :=
          mul_le_mul_of_nonneg_left hPS (by linarith)
      _ = _ := by unfold mbPowF; ring
  have hFt : mbFtc d n A ≤ mbPowG d * (M ^ 2 * B) := by
    refine mb_pow_B ?_ (mul_nonneg hg0 (by linarith)) hB
    show mbPowG d * A (n + 3) ≤ mbPowG d * M ^ 2
    exact mul_le_mul_of_nonneg_left ((hA _ (by omega)).trans hMM) hg0
  have hR : mbRc d n A ≤ mbPowR d * (M ^ 2 * B) := by
    refine mb_pow_B ?_ (mul_nonneg hr0 (by linarith)) hB
    have c1 : 0 ≤ 2 * vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hCK 2)) (by linarith)) hS
    have c2 : 0 ≤ vsCK d ^ 2 * d.C1pp := mul_nonneg (pow_nonneg hCK 2) (by linarith)
    have a1 := mul_le_mul_of_nonneg_left ((hA (n + 3) (by omega)).trans hMM) c1
    have a2 := mul_le_mul_of_nonneg_left ((hA (n + 2) (by omega)).trans hMM) c2
    show 2 * vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp * A (n + 3) + vsCK d ^ 2 * d.C1pp * A (n + 2)
      ≤ (2 * vsCK d ^ 2 * d.Cwc * Real.sqrt d.C1pp + vsCK d ^ 2 * d.C1pp) * M ^ 2
    linarith
  -- Z
  have hZ : mbZc d Λ n A I b ≤ mbPowZ d n * (L * M ^ 2 * B) := by
    have hin := mb_pow_aff hb hB hΛ0 hΛ hL hM2 (add_nonneg hf0 hg0)
      (F := mbFc d n A I + mbFtc d n A) (by linarith)
    have hc : 0 ≤ onestepConst d ^ 2 * kernelActionConst d ^ (n + 4) :=
      mul_nonneg (pow_nonneg (onestepConst_nonneg d) 2) (pow_nonneg (by linarith) _)
    calc mbZc d Λ n A I b = (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4)) *
          (b + Λ * (mbFc d n A I + mbFtc d n A)) := rfl
      _ ≤ (onestepConst d ^ 2 * kernelActionConst d ^ (n + 4)) *
          ((1 + (mbPowF d (n + 4) + mbPowG d)) * (L * M ^ 2 * B)) :=
          mul_le_mul_of_nonneg_left hin hc
      _ = _ := by unfold mbPowZ; ring
  -- V
  have hV : mbVc d Λ n A I b ≤ mbPowV d n * (L * (L * M ^ 2) * B) := by
    have h1 := mb_pow_aff hb hB hΛ0 hΛ hL hY1' hf0 (mb_pow_weak hF hf0 hB0 hY1)
    have hZR : mbZc d Λ n A I b + mbRc d n A ≤ (mbPowZ d n + mbPowR d) * ((L * M ^ 2) * B) := by
      have := mb_pow_weak hR hr0 hB0 hY1
      linarith
    have h2 := mb_pow_lin hΛ0 hΛ (add_nonneg hz0 hr0) (by linarith) hB0 hZR
    have c1 : 0 ≤ vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) :=
      mul_nonneg (mul_nonneg hCK (by linarith)) (pow_nonneg (by linarith) _)
    have c2 : 0 ≤ kernelActionConst d ^ (n + 5) := pow_nonneg (by linarith) _
    calc mbVc d Λ n A I b = vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) *
          (b + Λ * mbFc d n A I) +
          kernelActionConst d ^ (n + 5) * (Λ * (mbZc d Λ n A I b + mbRc d n A)) := by
          unfold mbVc
          ring
      _ ≤ vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) *
          ((1 + mbPowF d (n + 4)) * (L * (L * M ^ 2) * B)) +
          kernelActionConst d ^ (n + 5) * ((mbPowZ d n + mbPowR d) * (L * (L * M ^ 2) * B)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 c1) (mul_le_mul_of_nonneg_left h2 c2)
      _ = _ := by unfold mbPowV; ring
  -- A^sat
  have hVF : ((n + 4 : ℕ) : ℝ) * mbVc d Λ n A I b + mbFc d n A I ≤
      (((n + 4 : ℕ) : ℝ) * mbPowV d n + mbPowF d (n + 4)) * ((L * (L * M ^ 2)) * B) := by
    have e1 := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg (α := ℝ) (n + 4))
    have e2 := mb_pow_weak (mb_pow_weak hF hf0 hB0 hY1) hf0 hB0 hY2
    linarith
  have h := mb_pow_aff hb hB hΛ0 hΛ hL hY2'
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hv0) hf0) hVF
  calc mbAsat d Λ n A I b =
        b + Λ * (((n + 4 : ℕ) : ℝ) * mbVc d Λ n A I b + mbFc d n A I) := rfl
    _ ≤ _ := h
    _ = _ := by unfold mbPowSat; ring

include hΛ0 hΛ hL hM hB hb in

/-- `I_k ≤ mbPowIso d k a · L⁴ M² B` if `A_k ≤ a L³ M² B` and `I_j ≤ M` for `j < k`. -/
theorem mb_pow_iso (k : ℕ) {Ak a : ℝ} (ha : 0 ≤ a) (hAk : Ak ≤ a * (L ^ 3 * M ^ 2 * B))
    {I : ℕ → ℝ} (hI0 : ∀ j, 0 ≤ I j) (hI : ∀ j, j < k → I j ≤ M) :
    mbIsoK d Λ k Ak I b ≤ mbPowIso d k a * (L ^ 4 * M ^ 2 * B) := by
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hCK := (vsCK_pos d).le
  have hC0 := d.C0_ge_one
  have hB0 : 0 ≤ B := by linarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hY3 : M ^ 2 ≤ L ^ 3 * M ^ 2 := le_mul_of_one_le_left (sq_nonneg M) (one_le_pow₀ hL)
  have hY3' : 1 ≤ L ^ 3 * M ^ 2 := hM2.trans hY3
  have hf0 := mbPowF_nonneg d k
  have hPS := mbFIsoPairSum_le (k := k) (by linarith) hI0 hI
  have hF : d.Cwc * mbFIsoPairSum k I ≤ mbPowF d k * (M ^ 2 * B) := by
    refine mb_pow_B ?_ (mul_nonneg hf0 (by linarith)) hB
    calc d.Cwc * mbFIsoPairSum k I ≤ d.Cwc * ((k : ℝ) ^ 2 * M ^ 2) :=
          mul_le_mul_of_nonneg_left hPS (by linarith)
      _ = _ := by unfold mbPowF; ring
  have hc3 : 0 ≤ d.C0 + 1 + vsCK d * d.Cwc := by nlinarith
  have hFC : mbFIsoC d k Ak I ≤
      (mbPowF d k + (d.C0 + 1 + vsCK d * d.Cwc) * a) * ((L ^ 3 * M ^ 2) * B) := by
    have e1 := mb_pow_weak hF hf0 hB0 hY3
    have e2 := mul_le_mul_of_nonneg_left hAk hc3
    unfold mbFIsoC
    linarith
  have h := mb_pow_aff hb hB hΛ0 hΛ hL hY3' (add_nonneg hf0 (mul_nonneg hc3 ha)) hFC
  calc mbIsoK d Λ k Ak I b = kernelActionConst d ^ (k - 1) * (b + Λ * mbFIsoC d k Ak I) := rfl
    _ ≤ kernelActionConst d ^ (k - 1) * ((1 + (mbPowF d k + (d.C0 + 1 + vsCK d * d.Cwc) * a)) *
          (L * (L ^ 3 * M ^ 2) * B)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg (by linarith) _)
    _ = _ := by unfold mbPowIso; ring

end Step

/-- **One step of the recursion for the `M`-bound constants** (`k ≥ 3`): if `A_j, I_j ≤ M` for
`j < k` (`M ≥ 1`), `B₀ k ≤ B` (`B ≥ 1`), `0 ≤ Λ ≤ L`, `L ≥ 1`, then `A_k, I_k ≤ K_k L⁴ M² B`
(`K_k = mbPowK d k`).
-/
theorem mb_pow_step (d : VSData) {Λ L M B : ℝ} (B₀ : ℕ → ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hB : 1 ≤ B) (hB0 : ∀ j, 0 ≤ B₀ j) {k : ℕ} (hk : 3 ≤ k)
    (hbk : B₀ k ≤ B) (hA : ∀ j, j < k → mbConstA d Λ B₀ j ≤ M)
    (hI : ∀ j, j < k → mbConstI d Λ B₀ j ≤ M) :
    mbConstA d Λ B₀ k ≤ mbPowK d k * (L ^ 4 * M ^ 2 * B) ∧
      mbConstI d Λ B₀ k ≤ mbPowK d k * (L ^ 4 * M ^ 2 * B) := by
  have hAt0 : ∀ i, 0 ≤ mbTabA d Λ B₀ k i := fun i => (mbTab_nonneg d Λ B₀ hΛ0 hB0 k i).1
  have hIt0 : ∀ i, 0 ≤ mbTabI d Λ B₀ k i := fun i => (mbTab_nonneg d Λ B₀ hΛ0 hB0 k i).2
  have hAt : ∀ j, j < k → mbTabA d Λ B₀ k j ≤ M := fun j hj => by
    rw [mbTabA_lt d Λ B₀ hj]
    exact hA j hj
  have hIt : ∀ j, j < k → mbTabI d Λ B₀ k j ≤ M := fun j hj => by
    rw [mbTabI_lt d Λ B₀ hj]
    exact hI j hj
  have hns : ¬ (k ≤ 1) := by omega
  have hk2 : ¬ (k = 2) := by omega
  have hB0' : 0 ≤ B := by linarith
  have hX : 0 ≤ L ^ 3 * M ^ 2 * B :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) 3) (sq_nonneg M)) hB0'
  have hX4 : 0 ≤ L ^ 4 * M ^ 2 * B :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) 4) (sq_nonneg M)) hB0'
  have hav0 := mbPowAv_nonneg d k
  have hAv : mbConstA d Λ B₀ k ≤ mbPowAv d k * (L ^ 3 * M ^ 2 * B) := by
    rw [mbConstA_eq]
    unfold mbStepA
    rw [ite_eq_right hns, ite_eq_right hk2]
    have hN := mb_pow_ns d hΛ0 hΛ hL hM hB hbk k hAt0 hAt hIt
    have hS0 := mbPowSat_nonneg d (k - 4)
    have hN0 := mbPowNs_nonneg d k
    have hN' : mbAns d Λ k (mbTabA d Λ B₀ k) (mbTabI d Λ B₀ k) (B₀ k) ≤
        mbPowAv d k * (L ^ 3 * M ^ 2 * B) :=
      hN.trans (mul_le_mul_of_nonneg_right (by unfold mbPowAv; linarith) hX)
    split_ifs with hodd
    · exact hN'
    · refine max_le hN' ?_
      have hS := mb_pow_sat d hΛ0 hΛ hL hM hB hbk (k - 4) hAt0
        (fun j hj => hAt j (by omega)) (fun j hj => hIt j (by omega))
      exact hS.trans (mul_le_mul_of_nonneg_right (by unfold mbPowAv; linarith) hX)
  have hiso0 := mbPowIso_nonneg d k hav0
  have hCK := (vsCK_pos d).le
  have hCK2 := sq_nonneg (vsCK d)
  have hK1 : mbPowAv d k ≤ mbPowK d k := by unfold mbPowK; linarith
  have hK2 : mbPowIso d k (mbPowAv d k) ≤ mbPowK d k := by unfold mbPowK; linarith
  have hL34 : L ^ 3 * M ^ 2 * B ≤ L ^ 4 * M ^ 2 * B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hL (by norm_num)) (sq_nonneg M)) hB0'
  refine ⟨hAv.trans ((mul_le_mul_of_nonneg_left hL34 hav0).trans
    (mul_le_mul_of_nonneg_right hK1 hX4)), ?_⟩
  rw [mbConstI_eq]
  unfold mbStepI
  rw [ite_eq_right hns, ite_eq_right hk2]
  exact (mb_pow_iso d hΛ0 hΛ hL hM hB hbk k hav0 hAv hIt0 hIt).trans
    (mul_le_mul_of_nonneg_right hK2 hX4)

/-!
## The induction
-/

/-- The exponent `e_k = 2^k − 4` (truncated: `e_0 = e_1 = e_2 = 0`). -/
def mbPowExp (k : ℕ) : ℕ := 2 ^ k - 4

/-- The coefficient `c_k`: `c_0 = c_1 = c_2 = 1 + C_K² + C_K`, `c_k = K_k B c_{k-1}²`. -/
def mbPowC (d : VSData) (B : ℝ) : ℕ → ℝ
  | 0 => 1 + vsCK d ^ 2 + vsCK d
  | 1 => 1 + vsCK d ^ 2 + vsCK d
  | 2 => 1 + vsCK d ^ 2 + vsCK d
  | k + 3 => mbPowK d (k + 3) * B * mbPowC d B (k + 2) ^ 2

theorem mbPowExp_succ {k : ℕ} (hk : 2 ≤ k) : mbPowExp (k + 1) = 2 * mbPowExp k + 4 := by
  unfold mbPowExp
  have h : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [pow_succ]
  omega

theorem mbPowExp_le_two {k : ℕ} (hk : k ≤ 2) : mbPowExp k = 0 := by
  interval_cases k <;> rfl

theorem mbPowC_le_two (d : VSData) (B : ℝ) {k : ℕ} (hk : k ≤ 2) :
    mbPowC d B k = 1 + vsCK d ^ 2 + vsCK d := by
  interval_cases k <;> rfl

theorem mbPowC_ge_one (d : VSData) {B : ℝ} (hB : 1 ≤ B) : ∀ k, 1 ≤ mbPowC d B k
  | 0 => by
    have := (vsCK_pos d).le
    have := sq_nonneg (vsCK d)
    show 1 ≤ 1 + vsCK d ^ 2 + vsCK d
    linarith
  | 1 => by
    have := (vsCK_pos d).le
    have := sq_nonneg (vsCK d)
    show 1 ≤ 1 + vsCK d ^ 2 + vsCK d
    linarith
  | 2 => by
    have := (vsCK_pos d).le
    have := sq_nonneg (vsCK d)
    show 1 ≤ 1 + vsCK d ^ 2 + vsCK d
    linarith
  | k + 3 => by
    have h := mbPowC_ge_one d hB (k + 2)
    show 1 ≤ mbPowK d (k + 3) * B * mbPowC d B (k + 2) ^ 2
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (mbPowK_ge_one d (k + 3)) hB) (one_le_pow₀ h)

/-- The base values `A_j, I_j ∈ {1, C_K, C_K²}` for `j ≤ 2` are `≤ 1 + C_K² + C_K`. -/
theorem mb_pow_base (d : VSData) (Λ : ℝ) (B₀ : ℕ → ℝ) {j : ℕ} (hj : j ≤ 2) :
    mbConstA d Λ B₀ j ≤ 1 + vsCK d ^ 2 + vsCK d ∧
      mbConstI d Λ B₀ j ≤ 1 + vsCK d ^ 2 + vsCK d := by
  have hCK := (vsCK_pos d).le
  have hs := sq_nonneg (vsCK d)
  rw [mbConstI_eq, mbConstA_eq]
  interval_cases j
  · simp only [mbStepA, mbStepI, zero_le_one, ite_true]
    exact ⟨by linarith, by linarith⟩
  · simp only [mbStepA, mbStepI, le_refl, ite_true]
    exact ⟨by linarith, by linarith⟩
  · have h21 : ¬ (2 ≤ 1) := by omega
    simp only [mbStepA, mbStepI, h21, ite_false, ite_true]
    exact ⟨by linarith, by linarith⟩

/-- **The `M`-bound constants are powers of `L`**: for `0 ≤ Λ ≤ L`,
`L ≥ 1`, `B ≥ 1`, `B₀ ≥ 0` and `B₀ j ≤ B` for `j ≤ k`: for every `j ≤ k`,
`A_j ≤ c_k L^{e_k}` and `I_j ≤ c_k L^{e_k}` with `e_k = 2^k − 4` (`mbPowExp`) and
`c_k = mbPowC d B k` (depending only on `VSData`, `k` and `B`).
-/
theorem mbConst_le_pow (d : VSData) {Λ L B : ℝ} (B₀ : ℕ → ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L)
    (hL : 1 ≤ L) (hB : 1 ≤ B) (hB0 : ∀ j, 0 ≤ B₀ j) :
    ∀ k, (∀ j, j ≤ k → B₀ j ≤ B) → ∀ j, j ≤ k →
      mbConstA d Λ B₀ j ≤ mbPowC d B k * L ^ mbPowExp k ∧
        mbConstI d Λ B₀ j ≤ mbPowC d B k * L ^ mbPowExp k := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    rw [mbPowC_le_two d B (k := 0) (by norm_num), mbPowExp_le_two (k := 0) (by norm_num),
      pow_zero, mul_one]
    exact mb_pow_base d Λ B₀ (by omega)
  | succ k ih =>
    intro hBk j hj
    by_cases hk : k + 1 ≤ 2
    · rw [mbPowC_le_two d B hk, mbPowExp_le_two hk, pow_zero, mul_one]
      exact mb_pow_base d Λ B₀ (by omega)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have ih' := ih (fun j hj => hBk j (by omega))
    have hc1 := mbPowC_ge_one d hB (k' + 2)
    have hLe : 1 ≤ L ^ mbPowExp (k' + 2) := one_le_pow₀ hL
    set M := mbPowC d B (k' + 2) * L ^ mbPowExp (k' + 2) with hMdef
    have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hc1 hLe
    have heq : mbPowC d B (k' + 2 + 1) * L ^ mbPowExp (k' + 2 + 1) =
        mbPowK d (k' + 2 + 1) * (L ^ 4 * M ^ 2 * B) := by
      rw [mbPowExp_succ (by omega), hMdef]
      show mbPowK d (k' + 3) * B * mbPowC d B (k' + 2) ^ 2 * L ^ (2 * mbPowExp (k' + 2) + 4) = _
      rw [pow_add, pow_mul']
      ring
    rw [heq]
    rcases Nat.lt_or_ge j (k' + 2 + 1) with hj' | hj'
    · have h := ih' j (by omega)
      have hK := mbPowK_ge_one d (k' + 2 + 1)
      have hB0' : 0 ≤ B := by linarith
      have hX4 : 0 ≤ L ^ 4 * M ^ 2 * B :=
        mul_nonneg (mul_nonneg (pow_nonneg (by linarith) 4) (sq_nonneg M)) hB0'
      have h1 : M ≤ M ^ 2 := by nlinarith
      have h2 : M ^ 2 ≤ L ^ 4 * M ^ 2 * B :=
        (le_mul_of_one_le_left (sq_nonneg M) (one_le_pow₀ hL)).trans
          (le_mul_of_one_le_right (mul_nonneg (pow_nonneg (by linarith) 4) (sq_nonneg M)) hB)
      have h3 : L ^ 4 * M ^ 2 * B ≤ mbPowK d (k' + 2 + 1) * (L ^ 4 * M ^ 2 * B) :=
        le_mul_of_one_le_left hX4 hK
      have hM2 := (h1.trans h2).trans h3
      exact ⟨h.1.trans hM2, h.2.trans hM2⟩
    · obtain rfl : j = k' + 2 + 1 := by omega
      exact mb_pow_step d B₀ hΛ0 hΛ hL hM hB hB0 (by omega) (hBk _ le_rfl)
        (fun j hj => (ih' j (by omega)).1) (fun j hj => (ih' j (by omega)).2)

/-!
## The consumer form: `C (log N)^{C'}`
-/

/-- `C_log = 1/log 2 + c_m⁻¹ (log(C₀+1)/log 2 + 1)`: `max(1, Λ) ≤ C_log log N` for `N ≥ 2`. -/
def mbLogC (d : VSData) : ℝ :=
  1 / Real.log 2 + d.cm⁻¹ * (Real.log (d.C0 + 1) / Real.log 2 + 1)

theorem mbLambda_le_log (d : VSData) {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ mbLambda d N ∧ mbLambda d N ≤ mbLogC d * Real.log N ∧
      1 ≤ mbLogC d * Real.log N := by
  have hN0 : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlN0 : 0 < Real.log N := hl2.trans_le hlN
  have hratio : 1 ≤ Real.log N / Real.log 2 := (one_le_div hl2).mpr hlN
  have hC0 : 0 ≤ Real.log (d.C0 + 1) := Real.log_nonneg (by linarith [d.C0_ge_one])
  have hcm : 0 < d.cm⁻¹ := inv_pos.mpr d.cm_pos
  have h4 : 1 ≤ 1 / Real.log 2 * Real.log N := by
    rw [one_div, inv_mul_eq_div]
    exact hratio
  refine ⟨mbLambda_nonneg d hN0, ?_, ?_⟩
  · unfold mbLambda mbLogC
    rw [Real.log_mul (by linarith [d.C0_ge_one]) (by linarith)]
    have h1 : Real.log (d.C0 + 1) ≤ Real.log (d.C0 + 1) / Real.log 2 * Real.log N := by
      calc Real.log (d.C0 + 1) = Real.log (d.C0 + 1) * 1 := (mul_one _).symm
        _ ≤ Real.log (d.C0 + 1) * (Real.log N / Real.log 2) :=
            mul_le_mul_of_nonneg_left hratio hC0
        _ = _ := by ring
    have h3 := mul_le_mul_of_nonneg_left h1 hcm.le
    have h2 : 0 ≤ 1 / Real.log 2 * Real.log N := by linarith
    nlinarith
  · unfold mbLogC
    have h5 : 0 ≤ d.cm⁻¹ * (Real.log (d.C0 + 1) / Real.log 2 + 1) * Real.log N :=
      mul_nonneg (mul_nonneg hcm.le (add_nonneg (div_nonneg hC0 hl2.le) zero_le_one)) hlN0.le
    nlinarith

/-- **The `M`-bound constants are powers of `log N`**: for `N ≥ 2`,
`Λ = mbLambda d N = c_m⁻¹ log((C₀+1)N)`, `B ≥ 1`, `B₀ ≥ 0` and `B₀ j ≤ B` for `j ≤ k`:
`A_k, I_k ≤ C (log N)^{C'}` with `C = c_k C_log^{e_k}` (`c_k = mbPowC d B k`,
`C_log = mbLogC d`) and `C' = e_k = 2^k − 4`;
`C` depends only on `VSData`, `k` and `B`.
-/
theorem mbConst_le_log_pow (d : VSData) {N : ℕ} (hN : 2 ≤ N) {B : ℝ} (hB : 1 ≤ B)
    (B₀ : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B₀ j) (k : ℕ) (hBk : ∀ j, j ≤ k → B₀ j ≤ B) :
    mbConstA d (mbLambda d N) B₀ k ≤
        mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log N ^ mbPowExp k ∧
      mbConstI d (mbLambda d N) B₀ k ≤
        mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log N ^ mbPowExp k := by
  obtain ⟨h0, h1, h2⟩ := mbLambda_le_log d hN
  have h := mbConst_le_pow d B₀ h0 h1 h2 hB hB0 k hBk k le_rfl
  rw [mul_pow, ← mul_assoc] at h
  exact h

section Joint

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hA hc in

/-- **The joint `M`-bounds with the log-power constants** (under `MBAlg` and the initial
bounds, as `mbBounds_joint`): if `B₀ j ≤ B` (`B ≥ 1`) for `j ≤ k`, then
`AvB(k, C (log N)^{C'})` and `IsoB(k, C (log N)^{C'})`, `N = m W`, `C = c_k C_log^{e_k}`,
`C' = 2^k − 4`.
-/
theorem mbBounds_joint_log (B₀ : ℕ → ℝ) (hB₀ : ∀ k, 0 ≤ B₀ k)
    (hInitAv : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin (m * W)),
      ‖avM P σ y 0‖ ≤ B₀ k * (P.lEta 0 * P.sAv y 0))
    (hInitIso : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin (m * W)) (y : Fin k → Fin (m * W)),
      ‖P.mChain σ y 0 a‖ ≤ B₀ k * (Real.sqrt (P.lEta 0) * P.sIso a a y 0))
    {B : ℝ} (hB : 1 ≤ B) (k : ℕ) (hk : 1 ≤ k) (hBk : ∀ j, j ≤ k → B₀ j ≤ B) :
    MBAvB P k (mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) ∧
      MBIsoB P k
        (mbPowC d B k * mbLogC d ^ mbPowExp k * Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) := by
  have hN : 2 ≤ m * W :=
    calc 2 ≤ 4 := by norm_num
      _ ≤ m := hc.hm
      _ ≤ m * W := Nat.le_mul_of_pos_right m hc.hW
  obtain ⟨hAv, hIso⟩ := mbBounds_joint hA hc B₀ hB₀ hInitAv hInitIso k hk
  obtain ⟨hcA, hcI⟩ := mbConst_le_log_pow d hN hB B₀ hB₀ k hBk
  refine ⟨fun t ht σ x => (hAv t ht σ x).trans
    (mul_le_mul_of_nonneg_right hcA (mb_LsAv_pos_nonneg hc ht x)), fun t ht σ a x =>
      (hIso t ht σ a x).trans (mul_le_mul_of_nonneg_right hcI
        (mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P (hc.inputs ht) _ _ _)))⟩

end Joint

end BlockBand.Native.ErdosRiabov.MBound
