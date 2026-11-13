module

public import BlockBand.Native.ErdosRiabov.Chains.ChainCalc
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.SChainGlobalResolventFunctional
public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ResolventIdentities

/-!
# Resolvent chains: deterministic norm bounds

`‖·‖` is the Euclidean operator norm (`Matrix.Norms.L2Operator`). For a slot product of
`k` resolvents with `‖R_j‖ ≤ c`:

* `norm_slotProd_le`: `‖M₀B₀ ⋯ M_{k-1}B_{k-1}‖ ≤ ∏_j ‖M_j‖ ‖B_j‖`;
* `norm_firstVar_le`: `‖firstVar B R X‖ ≤ k c^{k+1} ‖X‖ ∏ ‖B_j‖`;
* `norm_secondVar_le`: `‖secondVar B R X Y‖ ≤ k (k+1) c^{k+2} ‖X‖ ‖Y‖ ∏ ‖B_j‖`.

For a Hermitian `A(y) = A₀ + L y` and `0 < η ≤ |Im z_j|` for all `j`:
`isUnit_det_res` (invertibility, the hypothesis of all ChainCalc derivative theorems),
`norm_res_le` (`‖R_j‖ ≤ 1/|Im z_j|`), `norm_resChain_le` (`‖C‖ ≤ η^{-k} ∏‖B_j‖`),
`norm_firstVar_resSlots_le` (`‖DC(y)[u]‖ ≤ k η^{-(k+1)} ∏‖B_j‖ ‖L u‖`, the left side being
`D C(y)[u] = -firstVar …` by `fderiv_resChain`), `norm_secondVar_resSlots_le`
(`‖D²C(y)[u, w]‖ ≤ k (k+1) η^{-(k+2)} ∏‖B_j‖ ‖L u‖ ‖L w‖`, `fderiv_fderiv_resChain`).
The norm bounds are stated on the algebraic variations `firstVar`/`secondVar`, which are the
derivatives by ChainCalc; this keeps the `L²` operator norm separate from ChainCalc's
internal `Matrix.linftyOpNormedRing` instance.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Chains
open Matrix Function
open scoped Matrix.Norms.L2Operator

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

theorem norm_one_le : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
  exact ContinuousLinearMap.norm_id_le

theorem norm_list_prod_le (l : List (Matrix ι ι ℂ)) : ‖l.prod‖ ≤ (l.map norm).prod := by
  induction l with
  | nil => simpa using norm_one_le
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact (norm_mul_le a l.prod).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg a))

theorem norm_slotProd_le (B M : Fin k → Matrix ι ι ℂ) :
    ‖slotProd B M‖ ≤ ∏ j, ‖M j‖ * ‖B j‖ := by
  calc ‖slotProd B M‖ ≤ ((slotList B M).map norm).prod := norm_list_prod_le _
    _ = ∏ j, ‖M j * B j‖ := by rw [slotList, List.map_ofFn, List.prod_ofFn]; rfl
    _ ≤ ∏ j, ‖M j‖ * ‖B j‖ :=
      Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => norm_mul_le _ _)

/-- Slot bound with profile: `‖N_l‖ ≤ c d_l` gives `‖slotProd B N‖ ≤ c^k ∏ d ∏ ‖B‖`. -/
theorem norm_slotProd_le_profile (B N : Fin k → Matrix ι ι ℂ) {c : ℝ} (d : Fin k → ℝ)
    (hN : ∀ l, ‖N l‖ ≤ c * d l) :
    ‖slotProd B N‖ ≤ c ^ k * (∏ l, d l) * ∏ l, ‖B l‖ := by
  refine (norm_slotProd_le B N).trans ?_
  calc ∏ l, ‖N l‖ * ‖B l‖ ≤ ∏ l, c * d l * ‖B l‖ :=
        Finset.prod_le_prod₀ (fun l _ => by positivity)
          (fun l _ => mul_le_mul_of_nonneg_right (hN l) (norm_nonneg _))
    _ = c ^ k * (∏ l, d l) * ∏ l, ‖B l‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]

theorem norm_mul3_le (P Q T : Matrix ι ι ℂ) : ‖P * Q * T‖ ≤ ‖P‖ * ‖Q‖ * ‖T‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem norm_sandwich_le {R : Matrix ι ι ℂ} {c : ℝ} (hR : ‖R‖ ≤ c) (X : Matrix ι ι ℂ) :
    ‖R * X * R‖ ≤ c * (c * ‖X‖) := by
  have hc : 0 ≤ c := (norm_nonneg R).trans hR
  calc ‖R * X * R‖ ≤ ‖R‖ * ‖X‖ * ‖R‖ := norm_mul3_le R X R
    _ ≤ c * ‖X‖ * c :=
      mul_le_mul (mul_le_mul_of_nonneg_right hR (norm_nonneg X)) hR (norm_nonneg R)
        (mul_nonneg hc (norm_nonneg X))
    _ = c * (c * ‖X‖) := by ring

theorem norm_double_sandwich_le {R : Matrix ι ι ℂ} {c : ℝ} (hR : ‖R‖ ≤ c) (X Y : Matrix ι ι ℂ) :
    ‖R * X * R * Y * R + R * Y * R * X * R‖ ≤ c * (2 * (c * ‖X‖ * (c * ‖Y‖))) := by
  have hc : 0 ≤ c := (norm_nonneg R).trans hR
  have h1 : ∀ P Q : Matrix ι ι ℂ, ‖R * P * R * Q * R‖ ≤ c * (c * ‖P‖) * ‖Q‖ * c := by
    intro P Q
    calc ‖R * P * R * Q * R‖ ≤ ‖R * P * R‖ * ‖Q‖ * ‖R‖ := norm_mul3_le _ _ _
      _ ≤ c * (c * ‖P‖) * ‖Q‖ * c :=
        mul_le_mul (mul_le_mul_of_nonneg_right (norm_sandwich_le hR P) (norm_nonneg Q)) hR
          (norm_nonneg R) (by positivity)
  calc ‖R * X * R * Y * R + R * Y * R * X * R‖
      ≤ ‖R * X * R * Y * R‖ + ‖R * Y * R * X * R‖ := norm_add_le _ _
    _ ≤ c * (c * ‖X‖) * ‖Y‖ * c + c * (c * ‖Y‖) * ‖X‖ * c := add_le_add (h1 X Y) (h1 Y X)
    _ = c * (2 * (c * ‖X‖ * (c * ‖Y‖))) := by ring

/-- **First-variation bound**: `‖firstVar B R X‖ ≤ k c^{k+1} ‖X‖ ∏ ‖B_l‖` if `‖R_j‖ ≤ c`. -/
theorem norm_firstVar_le (B R : Fin k → Matrix ι ι ℂ) {c : ℝ} (hR : ∀ j, ‖R j‖ ≤ c)
    (X : Matrix ι ι ℂ) :
    ‖firstVar B R X‖ ≤ k * c ^ (k + 1) * ‖X‖ * ∏ l, ‖B l‖ := by
  have hterm : ∀ j, ‖slotProd B (update R j (R j * X * R j))‖ ≤
      c ^ (k + 1) * ‖X‖ * ∏ l, ‖B l‖ := by
    intro j
    have h := norm_slotProd_le_profile B (update R j (R j * X * R j))
      (c := c) (fun l => if l = j then c * ‖X‖ else 1) fun l => by
        by_cases hl : l = j
        · subst hl
          simpa using norm_sandwich_le (hR l) X
        · simpa [hl] using hR l
    refine h.trans (le_of_eq ?_)
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ring
  calc ‖firstVar B R X‖ ≤ ∑ j, ‖slotProd B (update R j (R j * X * R j))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, c ^ (k + 1) * ‖X‖ * ∏ l, ‖B l‖ := Finset.sum_le_sum fun j _ => hterm j
    _ = k * c ^ (k + 1) * ‖X‖ * ∏ l, ‖B l‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- **Second-variation bound**: `‖secondVar B R X Y‖ ≤ k (k+1) c^{k+2} ‖X‖ ‖Y‖ ∏ ‖B_l‖`. -/
theorem norm_secondVar_le (B R : Fin k → Matrix ι ι ℂ) {c : ℝ} (hR : ∀ j, ‖R j‖ ≤ c)
    (X Y : Matrix ι ι ℂ) :
    ‖secondVar B R X Y‖ ≤ k * (k + 1) * c ^ (k + 2) * ‖X‖ * ‖Y‖ * ∏ l, ‖B l‖ := by
  set C := c ^ (k + 2) * ‖X‖ * ‖Y‖ * ∏ l, ‖B l‖ with hC
  have hdiag : ∀ j, ‖slotProd B (update R j
      (R j * X * R j * Y * R j + R j * Y * R j * X * R j))‖ ≤ 2 * C := by
    intro j
    have h := norm_slotProd_le_profile B
      (update R j (R j * X * R j * Y * R j + R j * Y * R j * X * R j)) (c := c)
      (fun l => if l = j then 2 * (c * ‖X‖ * (c * ‖Y‖)) else 1) fun l => by
        by_cases hl : l = j
        · subst hl
          simpa using norm_double_sandwich_le (hR l) X Y
        · simpa [hl] using hR l
    refine h.trans (le_of_eq ?_)
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, hC]
    ring
  have hoff : ∀ i j, i ≠ j →
      ‖slotProd B (update (update R j (R j * Y * R j)) i (R i * X * R i))‖ ≤ C := by
    intro i j hij
    have h := norm_slotProd_le_profile B (update (update R j (R j * Y * R j)) i (R i * X * R i))
      (c := c) (fun l => (if l = i then c * ‖X‖ else 1) * (if l = j then c * ‖Y‖ else 1))
      fun l => by
        by_cases hli : l = i
        · subst hli
          simpa [hij] using norm_sandwich_le (hR l) X
        · by_cases hlj : l = j
          · subst hlj
            simpa [hli] using norm_sandwich_le (hR l) Y
          · simpa [hli, hlj] using hR l
    refine h.trans (le_of_eq ?_)
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true, hC]
    ring
  have hterm : ∀ i j : Fin k, ‖if i = j then
        slotProd B (update R j (R j * X * R j * Y * R j + R j * Y * R j * X * R j))
      else slotProd B (update (update R j (R j * Y * R j)) i (R i * X * R i))‖ ≤
      C + if i = j then C else 0 := by
    intro i j
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij]
      linarith [hdiag j]
    · rw [ite_eq_right hij, ite_eq_right hij, add_zero]
      exact hoff i j hij
  calc ‖secondVar B R X Y‖ ≤ ∑ j : Fin k, ∑ i : Fin k, (C + if i = j then C else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i j)
    _ = k * (k + 1) * c ^ (k + 2) * ‖X‖ * ‖Y‖ * ∏ l, ‖B l‖ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hC]
      ring

end Generic

section Resolvent

variable {N : Type} [Fintype N] [DecidableEq N] {k : ℕ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Hermitian pencils are invertible off the real axis. -/
theorem isUnit_det_res (A₀ : Matrix N N ℂ) (L : V →ₗ[ℝ] Matrix N N ℂ) {z : ℂ} {y : V}
    (hA : (A₀ + L y).IsHermitian) (hz : z.im ≠ 0) :
    IsUnit (A₀ + L y - z • (1 : Matrix N N ℂ)).det := by
  have h := (ERNative.BlockBand.isUnit_resolventPencil (A₀ + L y) hA hz).neg
  rw [neg_sub] at h
  exact (Matrix.isUnit_iff_isUnit_det _).mp h

/-- `‖R(y)‖ ≤ 1/|Im z|` for Hermitian `A(y)`. -/
theorem norm_res_le (A₀ : Matrix N N ℂ) (L : V →ₗ[ℝ] Matrix N N ℂ) {z : ℂ} {y : V}
    (hA : (A₀ + L y).IsHermitian) (hz : z.im ≠ 0) : ‖res A₀ L z y‖ ≤ |z.im|⁻¹ :=
  ERNative.BlockBand.GaussianRing.ERSChainGlobal.norm_sourceInverse_le (A₀ + L y) hA hz

theorem norm_resSlots_le (A₀ : Matrix N N ℂ) (L : V →ₗ[ℝ] Matrix N N ℂ) {z : Fin k → ℂ} {y : V}
    (hA : (A₀ + L y).IsHermitian) {η : ℝ} (hη : 0 < η) (hz : ∀ j, η ≤ |(z j).im|) (j : Fin k) :
    ‖resSlots A₀ L z y j‖ ≤ η⁻¹ := by
  have hz0 : (z j).im ≠ 0 := abs_pos.mp (hη.trans_le (hz j))
  exact (norm_res_le A₀ L hA hz0).trans (inv_anti₀ hη (hz j))

/-- Invertibility of all slots (the hypothesis of the ChainCalc derivative theorems). -/
theorem isUnit_det_resSlots (A₀ : Matrix N N ℂ) (L : V →ₗ[ℝ] Matrix N N ℂ) {z : Fin k → ℂ}
    {y : V} (hA : (A₀ + L y).IsHermitian) {η : ℝ} (hη : 0 < η) (hz : ∀ j, η ≤ |(z j).im|) :
    ∀ j, IsUnit (A₀ + L y - z j • (1 : Matrix N N ℂ)).det :=
  fun j => isUnit_det_res A₀ L hA (abs_pos.mp (hη.trans_le (hz j)))

/-- `‖C(y)‖ ≤ η^{-k} ∏ ‖B_j‖`. -/
theorem norm_resChain_le (A₀ : Matrix N N ℂ) (L : V →ₗ[ℝ] Matrix N N ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix N N ℂ) {y : V} (hA : (A₀ + L y).IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : ∀ j, η ≤ |(z j).im|) :
    ‖resChain A₀ L z B y‖ ≤ η⁻¹ ^ k * ∏ j, ‖B j‖ := by
  have h := norm_slotProd_le_profile B (resSlots A₀ L z y) (c := η⁻¹) (fun _ => 1)
    fun l => by simpa using norm_resSlots_le A₀ L hA hη hz l
  simpa [resChain] using h

/-- `‖D C(y)[u]‖ = ‖firstVar …‖ ≤ k η^{-(k+1)} ∏‖B_j‖ ‖L u‖` (see `fderiv_resChain`). -/
theorem norm_firstVar_resSlots_le (A₀ : Matrix N N ℂ) (L : V →ₗ[ℝ] Matrix N N ℂ)
    (z : Fin k → ℂ) (B : Fin k → Matrix N N ℂ) {y : V} (hA : (A₀ + L y).IsHermitian) {η : ℝ}
    (hη : 0 < η) (hz : ∀ j, η ≤ |(z j).im|) (u : V) :
    ‖firstVar B (resSlots A₀ L z y) (L u)‖ ≤ k * η⁻¹ ^ (k + 1) * (∏ j, ‖B j‖) * ‖L u‖ := by
  exact (norm_firstVar_le B (resSlots A₀ L z y) (norm_resSlots_le A₀ L hA hη hz) (L u)).trans_eq
    (by ring)

/-- `‖D² C(y)[u, w]‖ = ‖secondVar …‖ ≤ k (k+1) η^{-(k+2)} ∏‖B_j‖ ‖L u‖ ‖L w‖`
(see `fderiv_fderiv_resChain`). -/
theorem norm_secondVar_resSlots_le (A₀ : Matrix N N ℂ) (L : V →ₗ[ℝ] Matrix N N ℂ)
    (z : Fin k → ℂ) (B : Fin k → Matrix N N ℂ) {y : V} (hA : (A₀ + L y).IsHermitian) {η : ℝ}
    (hη : 0 < η) (hz : ∀ j, η ≤ |(z j).im|) (u w : V) :
    ‖secondVar B (resSlots A₀ L z y) (L u) (L w)‖ ≤
      k * (k + 1) * η⁻¹ ^ (k + 2) * (∏ j, ‖B j‖) * ‖L u‖ * ‖L w‖ := by
  exact (norm_secondVar_le B (resSlots A₀ L z y) (norm_resSlots_le A₀ L hA hη hz) (L u)
    (L w)).trans_eq (by ring)

end Resolvent

end BlockBand.Native.ErdosRiabov.Chains
