module

public import BlockBand.Endpoints.Response.PassDerivativeLimitReversal
public import BlockBand.Endpoints.Response.EdgeClockMoments

/-!
# Path reversal of the far clock; linearity and monotonicity in the source

Part of the remote higher-moment theorem (reverse the path for its far clock) and of the full
remote Schatten theorem (reverse the independent path to treat the far-far block).
Deterministic, at every sample and energy.

* `rh_fullInverse_revPath`, `rh_boundaryToInterior_revPath`, `rh_tagResponse_revPath`: under
  the reversal `revPath n` (blocks and bonds in reverse order, internal bonds
  adjointed, ports swapped; `fullPathMatrix_revPath`), the full inverse, the boundary columns and
  the block responses `Y_{n;k}` are permuted, `Y_{n;k}(rev ω) = Y_{n;n-1-k}(ω)` with the ports
  swapped.
* `rh_farBlock_eq_nearClock_revPath` — **the far clock is a near clock of the reversed path**:
  if `q'((n-k)/W) = q((k+1)/W)` for `k < n` (the reversed grid profile), then
  `portBlock Q(q)(ω) 1 1 = nearClock q' (revPath n ω)`.
* `rh_intervalSource_add`, `rh_intervalSource_sum`, `rh_intervalSource_mono`: `Q(q)` is additive
  in `q` and Loewner-monotone in the grid values (`Y_{n;k} ⪰ 0`).
* `rh_nearClock_sum`: additivity of the near clock; with `rh_portBlock_sub` and
  `rh_portBlock_posSemidef`, Loewner monotonicity passes to port blocks.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory
open scoped ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Endpoints

variable {W n : ℕ}

/-- The position reversal of the path sites. -/
def rhPosRev (W n : ℕ) : Fin n × Fin W ≃ Fin n × Fin W :=
  Equiv.prodCongr Fin.revPerm (Equiv.refl _)

theorem rh_fullInverse_revPath (b E : ℝ) (ω : GrowthPath W) :
    fullInverse b E W n (revPath n ω) =
      (fullInverse b E W n ω).submatrix (fullRev W n) (fullRev W n) := by
  unfold fullInverse
  rw [fullPathMatrix_revPath, inv_submatrix_equiv]

theorem rh_boundaryToInterior_revPath (b E : ℝ) (ω : GrowthPath W) :
    boundaryToInterior b E W n (revPath n ω) =
      (boundaryToInterior b E W n ω).submatrix (rhPosRev W n) (portRev W) := by
  ext x y
  simp only [boundaryToInterior, rh_fullInverse_revPath, toBlocks₁₂, of_apply, submatrix_apply,
    fullRev, rhPosRev, portRev, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]

theorem rh_tagProjection_rev {k : ℕ} (hk : k < n) :
    (tagProjection W n k).submatrix (rhPosRev W n).symm (rhPosRev W n).symm =
      tagProjection W n (n - 1 - k) := by
  unfold tagProjection
  rw [submatrix_diagonal_equiv]
  congr 1
  funext x
  simp only [Function.comp_apply, rhPosRev, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map, Fin.revPerm_symm, Fin.revPerm_apply, Equiv.refl_symm, Equiv.refl_apply,
    Fin.val_rev]
  have hx := x.1.isLt
  have h1 : n - 1 - k < n := by omega
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rh_tagResponse_revPath (b E : ℝ) (ω : GrowthPath W) {k : ℕ} (hk : k < n) :
    tagResponse b E W n k (revPath n ω) =
      (tagResponse b E W n (n - 1 - k) ω).submatrix (portRev W) (portRev W) := by
  unfold tagResponse
  rw [rh_boundaryToInterior_revPath, conjTranspose_submatrix, ← rh_tagProjection_rev hk]
  set U := boundaryToInterior b E W n ω
  set σ := rhPosRev W n
  have hP : tagProjection W n k =
      ((tagProjection W n k).submatrix σ.symm σ.symm).submatrix σ σ := by
    ext x y; simp
  conv_lhs => rw [hP]
  rw [submatrix_mul_equiv, submatrix_mul_equiv]

/-- **The far clock is a near clock of the reversed path.** -/
theorem rh_farBlock_eq_nearClock_revPath (b E : ℝ) (q q' : ℝ → ℝ)
    (hq : ∀ k : ℕ, k < n → q' (((n - k : ℕ) : ℝ) / W) = q (((k + 1 : ℕ) : ℝ) / W))
    (ω : GrowthPath W) :
    portBlock (intervalSource b E W n q ω) 1 1 = nearClock b E W n q' (revPath n ω) := by
  unfold nearClock
  have hsum : intervalSource b E W n q' (revPath n ω) =
      (intervalSource b E W n q ω).submatrix (portRev W) (portRev W) := by
    unfold intervalSource
    rw [Finset.sum_congr rfl fun k hk => by
      rw [rh_tagResponse_revPath b E ω (Finset.mem_range.mp hk)]]
    rw [← Finset.sum_range_reflect]
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, submatrix_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have h1 : n - 1 - k < n := by omega
    have h2 : n - 1 - (n - 1 - k) = k := by omega
    have h3 : n - 1 - k + 1 = n - k := by omega
    rw [h2, h3, hq k hk']
  rw [hsum]
  ext x y
  simp [portBlock, portRev]

/-!
## Linearity and monotonicity in the source
-/

theorem rh_intervalSource_add (b E : ℝ) (q₁ q₂ : ℝ → ℝ) (ω : GrowthPath W) :
    intervalSource b E W n (q₁ + q₂) ω =
      intervalSource b E W n q₁ ω + intervalSource b E W n q₂ ω := by
  unfold intervalSource
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul]
  congr 1
  push_cast [Pi.add_apply]
  ring

theorem rh_intervalSource_zero (b E : ℝ) (ω : GrowthPath W) :
    intervalSource b E W n 0 ω = 0 := by
  unfold intervalSource
  simp

theorem rh_intervalSource_sum {κ : Type*} (b E : ℝ) (s : Finset κ) (q : κ → ℝ → ℝ)
    (ω : GrowthPath W) :
    intervalSource b E W n (∑ i ∈ s, q i) ω = ∑ i ∈ s, intervalSource b E W n (q i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact rh_intervalSource_zero b E ω
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, rh_intervalSource_add, ih]

/-- Loewner monotonicity in the grid values: if `q ≤ q'` at the grid points `(k+1)/W`, `k < n`,
then `Q(q') - Q(q) ⪰ 0`. -/
theorem rh_intervalSource_mono (b E : ℝ) {q q' : ℝ → ℝ}
    (h : ∀ k : ℕ, k < n → q (((k + 1 : ℕ) : ℝ) / W) ≤ q' (((k + 1 : ℕ) : ℝ) / W))
    (ω : GrowthPath W) :
    (intervalSource b E W n q' ω - intervalSource b E W n q ω).PosSemidef := by
  unfold intervalSource
  rw [← Finset.sum_sub_distrib]
  refine posSemidef_sum _ fun k hk => ?_
  rw [← sub_smul]
  have hc : (0 : ℂ) ≤ ((q' (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) -
      ((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub, Complex.zero_le_real, ← sub_div]
    exact div_nonneg (sub_nonneg.mpr (h k (Finset.mem_range.mp hk))) (sq_nonneg _)
  exact (tagResponse_posSemidef b E W n k ω).smul hc

theorem rh_portBlock_sub {Q₁ Q₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (i : Fin 2) :
    portBlock (Q₁ - Q₂) i i = portBlock Q₁ i i - portBlock Q₂ i i := by
  ext x y; rfl

theorem rh_portBlock_posSemidef {Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hQ : Q.PosSemidef) (i : Fin 2) : (portBlock Q i i).PosSemidef := by
  have : portBlock Q i i = Q.submatrix (fun x => (i, x)) (fun x => (i, x)) := by ext; rfl
  rw [this]; exact hQ.submatrix _

theorem rh_nearClock_sum {κ : Type*} (b E : ℝ) (j : ℕ) (s : Finset κ) (q : κ → ℝ → ℝ)
    (ω : GrowthPath W) :
    nearClock b E W j (∑ i ∈ s, q i) ω = ∑ i ∈ s, nearClock b E W j (q i) ω := by
  unfold nearClock
  rw [rh_intervalSource_sum]
  ext x y
  simp [portBlock, Matrix.sum_apply]

end BlockBand.Endpoints
