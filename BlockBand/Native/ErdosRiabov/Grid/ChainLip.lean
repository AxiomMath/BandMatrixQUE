module

public import BlockBand.Native.ErdosRiabov.Psi.Cont

set_option autoImplicit false

/-!
# Lipschitz bounds for resolvent chains in `(H, z)`

* `norm_ofFn_prod_sub_le`: telescoping, `‖∏ f_l - ∏ g_l‖ ≤ k c^k ε` if `‖f_l‖, ‖g_l‖ ≤ c`,
  `c ≥ 1`, `‖f_l - g_l‖ ≤ ε`;
* `norm_resolvent_sub_le`: for Hermitian `H, H'` and `|Im w|, |Im w'| ≥ η > 0`,
  `‖(H - w)⁻¹ - (H' - w')⁻¹‖ ≤ η⁻² (‖H - H'‖ + |w - w'|)`;
* `norm_le_card_sq_mul`: `‖X‖ ≤ N² δ` if every entry has `‖X_ab‖ ≤ δ`;
* **`norm_gChain_sub_le`**: for slot observables with `‖B_l‖ ≤ 1`,
  `‖gChain w B H - gChain w' B H'‖ ≤ k c^k η⁻² (‖H - H'‖ + δ_w)`, `c = max 1 η⁻¹`,
  `|w_l - w'_l| ≤ δ_w`; entries (`norm_entry_le_opNorm`) and traces (`norm_trace_le`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open Matrix Set
open BlockBand.Native.ErdosRiabov.Psi
open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-!
### Products
-/

theorem norm_ofFn_prod_le {k : ℕ} (f : Fin k → Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ l, ‖f l‖ ≤ c) : ‖(List.ofFn f).prod‖ ≤ c ^ k := by
  induction k with
  | zero => simpa using Chains.norm_one_le
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hf 0) (ih _ fun l => hf l.succ)
      (norm_nonneg _) hc)

/-- Telescoping bound for products. -/
theorem norm_ofFn_prod_sub_le {k : ℕ} (f g : Fin k → Matrix (Fin N) (Fin N) ℂ) {c ε : ℝ}
    (hc : 1 ≤ c) (hf : ∀ l, ‖f l‖ ≤ c) (hg : ∀ l, ‖g l‖ ≤ c) (hfg : ∀ l, ‖f l - g l‖ ≤ ε) :
    ‖(List.ofFn f).prod - (List.ofFn g).prod‖ ≤ k * c ^ k * ε := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hfg 0)
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    set P := (List.ofFn fun l : Fin k => f l.succ).prod
    set Q := (List.ofFn fun l : Fin k => g l.succ).prod
    have hP := norm_ofFn_prod_le (fun l : Fin k => f l.succ) (by linarith) fun l => hf l.succ
    have hPQ := ih (fun l => f l.succ) (fun l => g l.succ) (fun l => hf l.succ)
      (fun l => hg l.succ) fun l => hfg l.succ
    have e : f 0 * P - g 0 * Q = (f 0 - g 0) * P + g 0 * (P - Q) := by noncomm_ring
    rw [e]
    have hck : c ^ k ≤ c ^ (k + 1) := pow_le_pow_right₀ hc (by omega)
    calc _ ≤ ‖(f 0 - g 0) * P‖ + ‖g 0 * (P - Q)‖ := norm_add_le _ _
      _ ≤ ε * c ^ k + c * (k * c ^ k * ε) :=
          add_le_add ((norm_mul_le _ _).trans (mul_le_mul (hfg 0) hP (norm_nonneg _) hε))
            ((norm_mul_le _ _).trans (mul_le_mul (hg 0) hPQ (norm_nonneg _) (by linarith)))
      _ ≤ ((k + 1 : ℕ) : ℝ) * c ^ (k + 1) * ε := by
          push_cast
          have h1 : ε * c ^ k ≤ ε * c ^ (k + 1) := mul_le_mul_of_nonneg_left hck hε
          have h2 : c * (k * c ^ k * ε) = k * c ^ (k + 1) * ε := by rw [pow_succ]; ring
          nlinarith

/-!
### Resolvents
-/

theorem inv_sub_inv_eq {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUnit A.det) (hB : IsUnit B.det) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB,
    Matrix.mul_one, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

theorem norm_resolvent_le {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {w : ℂ} {η : ℝ}
    (hη : 0 < η) (hw : η ≤ |w.im|) : ‖(H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ ≤ η⁻¹ :=
  (ERNative.BlockBand.GaussianRing.ERSChainGlobal.norm_sourceInverse_le H hH
    (abs_pos.mp (hη.trans_le hw))).trans (inv_anti₀ hη hw)

/-- `‖(H - w)⁻¹ - (H' - w')⁻¹‖ ≤ η⁻² (‖H - H'‖ + |w - w'|)`. -/
theorem norm_resolvent_sub_le {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {w w' : ℂ} {η : ℝ} (hη : 0 < η) (hw : η ≤ |w.im|)
    (hw' : η ≤ |w'.im|) :
    ‖(H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - (H' - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ ≤
      η⁻¹ ^ 2 * (‖H - H'‖ + ‖w - w'‖) := by
  have hw0 : w.im ≠ 0 := abs_pos.mp (hη.trans_le hw)
  have hw0' : w'.im ≠ 0 := abs_pos.mp (hη.trans_le hw')
  rw [inv_sub_inv_eq (isUnit_det_herm_sub hH hw0) (isUnit_det_herm_sub hH' hw0')]
  have e : (H' - w' • (1 : Matrix (Fin N) (Fin N) ℂ)) - (H - w • 1) = (H' - H) + (w - w') • 1 := by
    rw [sub_smul]
    abel
  rw [e]
  have h1 := norm_resolvent_le hH hη hw
  have h2 := norm_resolvent_le hH' hη hw'
  have h3 : ‖(H' - H) + (w - w') • (1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ ‖H - H'‖ + ‖w - w'‖ := by
    refine (norm_add_le _ _).trans (add_le_add (by rw [norm_sub_rev]) ?_)
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) Chains.norm_one_le
  calc _ ≤ ‖(H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ *
        ‖(H' - H) + (w - w') • (1 : Matrix (Fin N) (Fin N) ℂ)‖ *
        ‖(H' - w' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ := Chains.norm_mul3_le _ _ _
    _ ≤ η⁻¹ * (‖H - H'‖ + ‖w - w'‖) * η⁻¹ := by gcongr
    _ = η⁻¹ ^ 2 * (‖H - H'‖ + ‖w - w'‖) := by ring

/-!
### Operator norm and entries
-/

/-- If every entry of `X` has norm `≤ δ`, then `‖X‖ ≤ N² δ`. -/
theorem norm_le_card_sq_mul {X : Matrix (Fin N) (Fin N) ℂ} {δ : ℝ}
    (hX : ∀ a b, ‖X a b‖ ≤ δ) : ‖X‖ ≤ (N : ℝ) ^ 2 * δ := by
  have e := Matrix.matrix_eq_sum_single X
  calc ‖X‖ = ‖∑ a, ∑ b, single a b (X a b)‖ := by rw [← e]
    _ ≤ ∑ a : Fin N, ∑ b : Fin N, δ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        have hs : single a b (X a b) = X a b • single a b (1 : ℂ) := by
          rw [smul_single, smul_eq_mul, mul_one]
        rw [hs, norm_smul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (VS.norm_single_one_le a b)).trans (hX a b)
    _ = (N : ℝ) ^ 2 * δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem norm_entry_le_opNorm (X : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) : ‖X a b‖ ≤ ‖X‖ :=
  ERNative.BlockBand.GaussianRing.ERSChainGlobal.norm_entry_le_l2_opNorm X a b

theorem norm_trace_le (X : Matrix (Fin N) (Fin N) ℂ) : ‖Matrix.trace X‖ ≤ N * ‖X‖ := by
  calc ‖Matrix.trace X‖ ≤ ∑ a, ‖X a a‖ := by
        simp only [Matrix.trace, Matrix.diag]
        exact norm_sum_le _ _
    _ ≤ ∑ _a : Fin N, ‖X‖ := Finset.sum_le_sum fun a _ => norm_entry_le_opNorm X a a
    _ = N * ‖X‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-!
### Chains
-/

/-- **Lipschitz bound for chains** in `(H, w)`. -/
theorem norm_gChain_sub_le {k : ℕ} {w w' : Fin k → ℂ} (B : Fin k → Matrix (Fin N) (Fin N) ℂ)
    (hB : ∀ l, ‖B l‖ ≤ 1) {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {η δw : ℝ} (hη : 0 < η) (hw : ∀ l, η ≤ |(w l).im|)
    (hw' : ∀ l, η ≤ |(w' l).im|) (hδ : ∀ l, ‖w l - w' l‖ ≤ δw) :
    ‖gChain w B H - gChain w' B H'‖ ≤
      k * (max 1 η⁻¹) ^ k * (η⁻¹ ^ 2 * (‖H - H'‖ + δw)) := by
  unfold gChain Chains.slotProd Chains.slotList
  have hc : 1 ≤ max 1 η⁻¹ := le_max_left _ _
  have hslot : ∀ (v : Fin k → ℂ) (G : Matrix (Fin N) (Fin N) ℂ), G.IsHermitian →
      (∀ l, η ≤ |(v l).im|) → ∀ l,
      ‖(G - v l • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * B l‖ ≤ max 1 η⁻¹ := fun v G hG hv l =>
    (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hB l)).trans
      ((norm_resolvent_le hG hη (hv l)).trans (le_max_right _ _)))
  refine norm_ofFn_prod_sub_le _ _ hc (hslot w H hH hw) (hslot w' H' hH' hw') fun l => ?_
  rw [← Matrix.sub_mul]
  refine (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) (hB l)).trans ?_)
  refine (norm_resolvent_sub_le hH hH' hη (hw l) (hw' l)).trans ?_
  gcongr
  exact hδ l

end BlockBand.Native.ErdosRiabov.Grid
