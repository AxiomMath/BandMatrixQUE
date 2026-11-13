module

public import Mathlib
public import BlockBand.Internal.Contracts.Inputs

/-!
# Deterministic bridges for `ShortRingLocalLaw`: profile, sites, control, test vectors

* `Inputs.shortRingProfile b m W` is an ER Definition 2.1 profile: symmetric,
  nonnegative, column-stochastic (`c + 2b = 1`; `m ≥ 3` makes the three blocks distinct) and
  flat (`S ≤ 1/W`); with the bandwidth hypothesis it is an `ErdosRiabov.NativeProfile`.
* For physical parameters `p`, the row-major equivalence `siteFinEquiv p : p.Site ≃ Fin p.N`
  has value `p.siteIndex`; it carries `shortRingProfile p.b p.n p.W` to `p.entryVariance`,
  the native `cyclicDistance` to `Inputs.siteDistance`, and `Inputs.polynomialControl` to
  `Inputs.siteControl`.
* At the coordinate vectors `u = e_i`, `v = e_j`, the native `vectorControl` is `Υ η i j`
  and the pairing `u* R v` is `R i j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External BlockBand.Internal.Contracts.Inputs
open scoped BigOperators

/-!
### The short-ring profile is a profile
-/

/-- `(k+1) mod m` for `k < m`, without division. -/
theorem ringSucc_mod {m k : ℕ} (hk : k < m) :
    (k + 1) % m = if k + 1 = m then 0 else k + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A sum over `Fin m` of an indicator of one value. -/
theorem sum_fin_ite_val {m : ℕ} (t : ℕ) (ht : t < m) (C : ℝ) :
    (∑ k : Fin m, if k.val = t then C else 0) = C := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · simp
  · intro k _ hk
    have : k.val ≠ t := fun h => hk (Fin.ext h)
    simp [this]
  · simp

/-- The block profile `C_kl` summed over the first block index (`m ≥ 3`). -/
theorem blockRow_sum (b : ℝ) {m W : ℕ} (hm : 3 ≤ m) (l : ℕ) (hl : l < m) :
    (∑ k : Fin m, (if k.val = l then (1 - 2 * b) / (W : ℝ)
      else if l = (k.val + 1) % m ∨ k.val = (l + 1) % m then b / (W : ℝ) else 0)) =
      1 / (W : ℝ) := by
  set l1 := if l + 1 = m then 0 else l + 1 with hl1
  set l2 := if l = 0 then m - 1 else l - 1 with hl2
  have hl1m : l1 < m := by rw [hl1]; split_ifs <;> omega
  have hl2m : l2 < m := by rw [hl2]; split_ifs <;> omega
  have hpt : ∀ k : Fin m, (if k.val = l then (1 - 2 * b) / (W : ℝ)
      else if l = (k.val + 1) % m ∨ k.val = (l + 1) % m then b / (W : ℝ) else 0) =
      ((if k.val = l then (1 - 2 * b) / (W : ℝ) else 0) +
        (if k.val = l1 then b / (W : ℝ) else 0)) +
        (if k.val = l2 then b / (W : ℝ) else 0) := by
    intro k
    have hk := k.isLt
    rw [ringSucc_mod hk, ringSucc_mod hl]
    rw [hl1, hl2]
    split_ifs <;> first | omega | ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_fin_ite_val l hl,
    sum_fin_ite_val l1 hl1m, sum_fin_ite_val l2 hl2m]
  ring

/-- Column stochasticity of `S = C ⊗ J_W` on `Fin (mW)` ([ER, (2.3)]), `m ≥ 3`, `W ≥ 1`. -/
theorem shortRingProfile_colSum (b : ℝ) {m W : ℕ} (hm : 3 ≤ m) (hW : 0 < W)
    (j : Fin (m * W)) : (∑ i, shortRingProfile b m W i j) = 1 := by
  have hl : j.val / W < m := (Nat.div_lt_iff_lt_mul hW).mpr (by
    simp)
  rw [← (finProdFinEquiv : Fin m × Fin W ≃ Fin (m * W)).sum_comp, Fintype.sum_prod_type]
  have hdiv : ∀ (k : Fin m) (a : Fin W),
      (finProdFinEquiv (k, a) : Fin (m * W)).val / W = k.val := by
    intro k a
    rw [finProdFinEquiv_apply_val, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt a.isLt,
      zero_add]
  have hterm : ∀ (k : Fin m) (a : Fin W),
      shortRingProfile b m W (finProdFinEquiv (k, a)) j =
        (if k.val = j.val / W then (1 - 2 * b) / (W : ℝ)
          else if j.val / W = (k.val + 1) % m ∨ k.val = (j.val / W + 1) % m then
            b / (W : ℝ) else 0) := by
    intro k a
    simp only [shortRingProfile, hdiv]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, blockRow_sum b hm _ hl]
  have : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  field_simp

theorem shortRingProfile_symm (b : ℝ) (m W : ℕ) (i j : Fin (m * W)) :
    shortRingProfile b m W i j = shortRingProfile b m W j i := by
  unfold shortRingProfile
  by_cases h1 : i.val / W = j.val / W
  · simp [h1]
  · have h1' : ¬j.val / W = i.val / W := fun h => h1 h.symm
    simp only [h1, h1', ite_false, or_comm]

theorem shortRingProfile_nonneg {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (m W : ℕ)
    (i j : Fin (m * W)) : 0 ≤ shortRingProfile b m W i j := by
  unfold shortRingProfile
  split_ifs
  · exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · exact div_nonneg hb0.le (Nat.cast_nonneg _)
  · exact le_rfl

theorem shortRingProfile_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (m W : ℕ)
    (i j : Fin (m * W)) : shortRingProfile b m W i j ≤ 1 / (W : ℝ) := by
  unfold shortRingProfile
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  split_ifs
  · exact div_le_div_of_nonneg_right (by linarith) hW
  · exact div_le_div_of_nonneg_right (by linarith) hW
  · exact div_nonneg zero_le_one hW

/-- [ER, Definition 2.1] for the short ring: `NativeProfile q (mW) W (shortRingProfile b m W)`
for every parameter record with `1 ≤ q.CW`, `m ≥ 3`, `W ≥ 1`, `0 < b < 1/2`, under the
bandwidth hypothesis `(mW)^{1+ζ₀} ≤ W²`. -/
theorem shortRingProfile_nativeProfile (q : ErdosRiabov.ModelParameters) (hCW : 1 ≤ q.CW)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {m W : ℕ} (hm : 3 ≤ m) (hW : 0 < W)
    (hband : ((m * W : ℕ) : ℝ) ^ (1 + q.zeta0) ≤ (W : ℝ) ^ 2) :
    ErdosRiabov.NativeProfile q (m * W) W (shortRingProfile b m W) where
  N_pos := Nat.mul_pos (by omega) hW
  W_pos := hW
  W_le_N := Nat.le_mul_of_pos_left W (by omega)
  bandwidth := hband
  symmetric := shortRingProfile_symm b m W
  nonnegative := shortRingProfile_nonneg hb0 hb m W
  columnStochastic := shortRingProfile_colSum b hm hW
  flat := fun i j => (shortRingProfile_le hb0 hb m W i j).trans
    (div_le_div_of_nonneg_right hCW (Nat.cast_nonneg _))

/-!
### The row-major site equivalence
-/

/-- `ZMod n ≃ Fin n` by the canonical representative. -/
def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun k := ⟨k.val, k.val_lt⟩
  invFun k := (k.val : ZMod n)
  left_inv k := ZMod.natCast_zmod_val k
  right_inv k := by
    apply Fin.ext
    exact ZMod.val_cast_of_lt k.isLt

/-- The row-major equivalence of the physical sites with the cycle `Fin N`. -/
def siteFinEquiv (p : Parameters) : p.Site ≃ Fin p.N :=
  (Equiv.prodCongr (zmodFinEquiv p.n) (Equiv.refl _)).trans finProdFinEquiv

theorem siteFinEquiv_val (p : Parameters) (x : p.Site) :
    (siteFinEquiv p x).val = p.siteIndex x := by
  change x.2.val + p.W * x.1.val = x.1.val * p.W + x.2.val
  ring

theorem siteFinEquiv_div (p : Parameters) (x : p.Site) :
    (siteFinEquiv p x).val / p.W = x.1.val := by
  rw [siteFinEquiv_val]
  unfold Parameters.siteIndex
  rw [Nat.mul_comm, Nat.mul_add_div p.W_pos, Nat.div_eq_of_lt x.2.isLt, add_zero]

theorem zmod_val_succ (p : Parameters) (k : ZMod p.n) :
    (k + 1).val = (k.val + 1) % p.n := by
  have : Fact (1 < p.n) := ⟨by have := p.n_ge_four; omega⟩
  rw [ZMod.val_add, ZMod.val_one]

/-- The contract profile is the physical entry variance under the row-major equivalence. -/
theorem shortRingProfile_siteFinEquiv (p : Parameters) (x y : p.Site) :
    shortRingProfile p.b p.n p.W (siteFinEquiv p x) (siteFinEquiv p y) =
      p.entryVariance x y := by
  unfold shortRingProfile Parameters.entryVariance
  rw [siteFinEquiv_div, siteFinEquiv_div]
  have e1 : y.1 = x.1 ↔ x.1.val = y.1.val := by
    rw [eq_comm]; exact (ZMod.val_injective _).eq_iff.symm
  have e2 : y.1 = x.1 + 1 ↔ y.1.val = (x.1.val + 1) % p.n := by
    rw [← zmod_val_succ]; exact (ZMod.val_injective _).eq_iff.symm
  have e3 : y.1 = x.1 - 1 ↔ x.1.val = (y.1.val + 1) % p.n := by
    rw [← zmod_val_succ, eq_sub_iff_add_eq, eq_comm]; exact (ZMod.val_injective _).eq_iff.symm
  simp only [e1, e2, e3, Parameters.c]

/-- The periodic distance is the contract site distance. -/
theorem cyclicDistance_siteFinEquiv (p : Parameters) (x y : p.Site) :
    ErdosRiabov.cyclicDistance p.N (siteFinEquiv p x) (siteFinEquiv p y) =
      siteDistance p x y := by
  unfold ErdosRiabov.cyclicDistance siteDistance
  rw [siteFinEquiv_val, siteFinEquiv_val]

/-- The polynomial control at the physical sites is the contract `siteControl`. -/
theorem polynomialControl_siteFinEquiv (p : Parameters) (D η : ℝ) (x y : p.Site) :
    polynomialControl p.N p.W D η (siteFinEquiv p x) (siteFinEquiv p y) =
      siteControl p D η x y := by
  unfold polynomialControl siteControl
  rw [cyclicDistance_siteFinEquiv]

/-!
### Coordinate test vectors
-/

/-- The isotropic control (3.9) at `u = e_i`, `v = e_j` is `Υ η i j`. -/
theorem vectorControl_single {N : ℕ} (Upsilon : ℝ → Matrix (Fin N) (Fin N) ℝ) (η : ℝ)
    (i j : Fin N) :
    ErdosRiabov.vectorControl Upsilon η (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single j (1 : ℂ)) = Upsilon η i j := by
  unfold ErdosRiabov.vectorControl
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    simp [hc]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

/-- The pairing `u* R v` at `u = e_i`, `v = e_j` is `R i j`. -/
theorem matrixPairing_single {N : ℕ} (R : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ErdosRiabov.matrixPairing R (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single j (1 : ℂ)) = R i j := by
  unfold ErdosRiabov.matrixPairing
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [hc]
    · simp
  · intro c _ hc
    simp [hc]
  · simp

end BlockBand.Adapters.ErdosRiabov
