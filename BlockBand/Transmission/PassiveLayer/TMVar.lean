module

public import BlockBand.Transmission.PassiveLayer.FlucCoord

/-!
# The covariance contraction `𝒱(K)` of the fresh layer in the coordinates `coordMap`

The `traceMatrix` clause of the passive bounds. The entry covariance
`E(d𝓗_{ij}d𝓗_{kℓ}) = W⁻¹σ_{ij}δ_{iℓ}δ_{jk}` contracts these terms to `W⁻²L𝒱(K)N`. For one
physical block and one port, `𝒱(K) = cP₁KP₁ + bP₁KP₂ + bP₂KP₁`. Its operator norm is bounded
independently of `W`. Deterministic, in the coordinates `CoordW W`, variances `coordVar W b` and
directions `layerDir b` (`BilCoord`).

* `tm_dirA0`, `tm_dirA1`, `tm_dirB0`, `tm_dirB1`: every coordinate direction `Nᵢ = ∂ᵢ𝒢⁻¹` is
  an explicit two-entry Hermitian matrix.
* `tmV K = Σᵢ vᵢ Tr(K Nᵢ) Nᵢ` (`vᵢ = coordVar W b i`), `tm_contract_eq`: its block form
  `(t_A/2)(K_{uv}E_{uv} + K_{vu}E_{vu})` on the physical block and `t_B(…)` on the bond, i.e.
  `t_A P₁KP₁ + t_B(P₁KP₂ + P₂KP₁)` (this is `𝒱(K)` with `c/W = t_A`, `b/W = t_B`).
* `tm_contract_le`: **`‖𝒱(K)‖ ≤ (3/W)‖K‖`** in operator norm, for `0 < b < 1/2`, `W ≥ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix
open BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator NNReal

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem tm_pair (K : Matrix n n ℂ) (u v : n) (q : ℝ) :
    (K * ((q : ℂ) • (single u v 1 + single v u 1))).trace •
        ((q : ℂ) • (single u v 1 + single v u 1)) +
      (K * ((q : ℂ) • (Complex.I • single u v 1 - Complex.I • single v u 1))).trace •
        ((q : ℂ) • (Complex.I • single u v 1 - Complex.I • single v u 1)) =
      ((2 * q ^ 2 : ℝ) : ℂ) • (K u v • single u v (1 : ℂ) + K v u • single v u 1) := by
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, trace_add, trace_sub, trace_smul,
    trace_mul_single]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, single_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  push_cast
  split_ifs <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem tm_projector_le {ι : Type*} [Fintype ι] {f : ι → n} (hf : Function.Injective f) :
    ‖∑ i, single (f i) (f i) (1 : ℂ)‖ ≤ 1 := by
  set P := ∑ i, single (f i) (f i) (1 : ℂ) with hPdef
  have hidem : P * P = P := by
    rw [hPdef, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [single_mul_single_same, one_mul]
    · intro j _ hji
      exact single_mul_single_of_ne (h := fun h => hji (hf h).symm) ..
    · intro h; exact absurd (Finset.mem_univ i) h
  have hherm : Pᴴ = P := by
    rw [hPdef, conjTranspose_sum]
    simp [conjTranspose_single]
  have h1 : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hherm, hidem]
  have h0 := norm_nonneg P
  nlinarith

theorem tm_proj_le {ι κ : Type*} [Fintype ι] [Fintype κ] (K : Matrix n n ℂ) {f : ι → n}
    {g : κ → n} (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖∑ i, ∑ j, K (f i) (g j) • single (f i) (g j) (1 : ℂ)‖ ≤ ‖K‖ := by
  have heq : ∑ i, ∑ j, K (f i) (g j) • single (f i) (g j) (1 : ℂ) =
      (∑ i, single (f i) (f i) (1 : ℂ)) * K * ∑ j, single (g j) (g j) (1 : ℂ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [single_mul_mul_single, smul_single, smul_eq_mul, one_mul, mul_one]
  rw [heq]
  set P := ∑ i, single (f i) (f i) (1 : ℂ)
  set Q := ∑ j, single (g j) (g j) (1 : ℂ)
  have h1 : ‖P‖ ≤ 1 := tm_projector_le hf
  have h2 : ‖Q‖ ≤ 1 := tm_projector_le hg
  have h3 : ‖P * K * Q‖ ≤ ‖P‖ * ‖K‖ * ‖Q‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hK := norm_nonneg K
  have hP0 := norm_nonneg P
  have hQ0 := norm_nonneg Q
  calc ‖P * K * Q‖ ≤ ‖P‖ * ‖K‖ * ‖Q‖ := h3
    _ ≤ 1 * ‖K‖ * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right h1 hK) h2 hQ0 (by positivity)
    _ = ‖K‖ := by ring

/-- Norm of one symmetrized block of the contraction. -/
theorem tm_sym_le {m : Type*} [Fintype m] (K : Matrix n n ℂ) {f g : m → n}
    (hf : Function.Injective f) (hg : Function.Injective g) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ α : m, ∑ β : m, (c : ℂ) •
        (K (f α) (g β) • single (f α) (g β) (1 : ℂ) + K (g β) (f α) • single (g β) (f α) 1)‖ ≤
      2 * c * ‖K‖ := by
  have heq : ∑ α : m, ∑ β : m, (c : ℂ) •
      (K (f α) (g β) • single (f α) (g β) (1 : ℂ) + K (g β) (f α) • single (g β) (f α) 1) =
      (c : ℂ) • ((∑ α : m, ∑ β : m, K (f α) (g β) • single (f α) (g β) (1 : ℂ)) +
        ∑ β : m, ∑ α : m, K (g β) (f α) • single (g β) (f α) (1 : ℂ)) := by
    rw [Finset.sum_comm (f := fun β α => K (g β) (f α) • single (g β) (f α) (1 : ℂ))]
    simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib]
  rw [heq, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
  have h1 := tm_proj_le K hf hg
  have h2 := tm_proj_le K hg hf
  have h3 := norm_add_le (∑ α : m, ∑ β : m, K (f α) (g β) • single (f α) (g β) (1 : ℂ))
    (∑ β : m, ∑ α : m, K (g β) (f α) • single (g β) (f α) (1 : ℂ))
  nlinarith

end Generic

variable {W : ℕ}

/-- The `(0, α)` physical site and the `(0, β)` port site. -/
abbrev sP (α : Fin W) : LayerSite W .oneBlockOnePort := Sum.inl ((0 : Fin 1), α)
abbrev sQ (β : Fin W) : LayerSite W .oneBlockOnePort := Sum.inr ((0 : Fin 1), β)

theorem tm_dirA0 (b : ℝ) (α β : Fin W) :
    layerDir (W := W) b (Pi.single (Sum.inl ((α, β), 0)) 1) =
      ((Real.sqrt (tA W b) / 2 : ℝ) : ℂ) • (single (sP α) (sP β) 1 + single (sP β) (sP α) 1) := by
  ext i j
  rcases i with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rcases j with ⟨j0, y⟩ | ⟨j0, y⟩ <;>
    obtain rfl := Subsingleton.elim i0 0 <;> obtain rfl := Subsingleton.elim j0 0 <;>
    simp only [layerDir, liftX, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.of_apply, gueRaw_entry', ginibreRaw, Matrix.conjTranspose_apply,
      Pi.single_apply, Sum.inl.injEq, Prod.mk.injEq, Matrix.smul_apply, Matrix.add_apply,
      Matrix.single_apply, reduceCtorEq, false_and, and_false, Matrix.zero_apply] <;>
    simp
  left
  simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]
  congr 1
  · exact if_congr ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun h => ⟨h.2.symm, h.1.symm⟩, fun h => ⟨h.2.symm, h.1.symm⟩⟩ rfl rfl

theorem tm_dirA1 (b : ℝ) (α β : Fin W) :
    layerDir (W := W) b (Pi.single (Sum.inl ((α, β), 1)) 1) =
      ((Real.sqrt (tA W b) / 2 : ℝ) : ℂ) •
        (Complex.I • single (sP α) (sP β) 1 - Complex.I • single (sP β) (sP α) 1) := by
  ext i j
  rcases i with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rcases j with ⟨j0, y⟩ | ⟨j0, y⟩ <;>
    obtain rfl := Subsingleton.elim i0 0 <;> obtain rfl := Subsingleton.elim j0 0 <;>
    simp only [layerDir, liftX, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.of_apply, gueRaw_entry', ginibreRaw, Matrix.conjTranspose_apply,
      Pi.single_apply, Sum.inl.injEq, Prod.mk.injEq, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.single_apply, reduceCtorEq, false_and, and_false,
      Matrix.zero_apply] <;>
    simp
  left
  have e1 : (if x = α ∧ y = β then (1 : ℂ) else 0) = if α = x ∧ β = y then 1 else 0 :=
    if_congr ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl
  have e2 : (if y = α ∧ x = β then (1 : ℂ) else 0) = if β = x ∧ α = y then 1 else 0 :=
    if_congr ⟨fun h => ⟨h.2.symm, h.1.symm⟩, fun h => ⟨h.2.symm, h.1.symm⟩⟩ rfl rfl
  simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, e1, e2]
  split_ifs <;> ring

theorem tm_dirB0 (b : ℝ) (α β : Fin W) :
    layerDir (W := W) b (Pi.single (Sum.inr (α, β, 0)) 1) =
      single (sP α) (sQ β) 1 + single (sQ β) (sP α) 1 := by
  ext i j
  rcases i with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rcases j with ⟨j0, y⟩ | ⟨j0, y⟩ <;>
    simp [layerDir, liftX, gueRaw_entry', ginibreRaw, Pi.single_apply, Matrix.single_apply,
      Subsingleton.elim i0 0, Subsingleton.elim j0 0, Matrix.conjTranspose_apply]
  all_goals (split_ifs <;> simp_all)

theorem tm_dirB1 (b : ℝ) (α β : Fin W) :
    layerDir (W := W) b (Pi.single (Sum.inr (α, β, 1)) 1) =
      Complex.I • single (sP α) (sQ β) 1 - Complex.I • single (sQ β) (sP α) 1 := by
  ext i j
  rcases i with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rcases j with ⟨j0, y⟩ | ⟨j0, y⟩ <;>
    simp [layerDir, liftX, gueRaw_entry', ginibreRaw, Pi.single_apply, Matrix.single_apply,
      Subsingleton.elim i0 0, Subsingleton.elim j0 0, Matrix.conjTranspose_apply]
  all_goals (split_ifs <;> simp_all)

theorem tm_pairA (b : ℝ) (K : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (α β : Fin W) :
    (((coordVar W b (Sum.inl ((α, β), 0)) : ℝ) : ℂ) *
        (K * layerDir b (Pi.single (Sum.inl ((α, β), 0)) 1)).trace) •
        layerDir b (Pi.single (Sum.inl ((α, β), 0)) 1) +
      (((coordVar W b (Sum.inl ((α, β), 1)) : ℝ) : ℂ) *
        (K * layerDir b (Pi.single (Sum.inl ((α, β), 1)) 1)).trace) •
        layerDir b (Pi.single (Sum.inl ((α, β), 1)) 1) =
      (((tA W b : ℝ) / 2 : ℝ) : ℂ) •
        (K (sP α) (sP β) • single (sP α) (sP β) (1 : ℂ) + K (sP β) (sP α) • single (sP β) (sP α) 1) := by
  rw [tm_dirA0, tm_dirA1]
  simp only [coordVar, Sum.elim_inl, NNReal.coe_one, Complex.ofReal_one, one_mul]
  rw [tm_pair]
  congr 2
  rw [div_pow, Real.sq_sqrt (NNReal.coe_nonneg _)]
  ring

theorem tm_pairB (b : ℝ) (K : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ)
    (α β : Fin W) :
    (((coordVar W b (Sum.inr (α, β, 0)) : ℝ) : ℂ) *
        (K * layerDir b (Pi.single (Sum.inr (α, β, 0)) 1)).trace) •
        layerDir b (Pi.single (Sum.inr (α, β, 0)) 1) +
      (((coordVar W b (Sum.inr (α, β, 1)) : ℝ) : ℂ) *
        (K * layerDir b (Pi.single (Sum.inr (α, β, 1)) 1)).trace) •
        layerDir b (Pi.single (Sum.inr (α, β, 1)) 1) =
      (((Real.toNNReal (b / W) : ℝ≥0) : ℝ) : ℂ) •
        (K (sP α) (sQ β) • single (sP α) (sQ β) (1 : ℂ) + K (sQ β) (sP α) • single (sQ β) (sP α) 1) := by
  have h := tm_pair K (sP α) (sQ β) 1
  simp only [Complex.ofReal_one, one_smul] at h
  rw [tm_dirB0, tm_dirB1]
  simp only [coordVar, Sum.elim_inr, mul_smul]
  rw [← smul_add, h, smul_smul]
  congr 1
  push_cast
  ring

/-- **The covariance contraction** `𝒱(K) = Σᵢ vᵢ Tr(K Nᵢ) Nᵢ`, `Nᵢ = layerDir b eᵢ = ∂ᵢ𝒢⁻¹`. -/
def tmV (b : ℝ) (K : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  ∑ i, (((coordVar W b i : ℝ) : ℂ) * (K * layerDir b (Pi.single i 1)).trace) •
    layerDir b (Pi.single i 1)

/-- Block form of `𝒱(K)`. -/
theorem tm_contract_eq (b : ℝ)
    (K : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    tmV b K = (∑ α : Fin W, ∑ β : Fin W, (((tA W b : ℝ) / 2 : ℝ) : ℂ) •
        (K (sP α) (sP β) • single (sP α) (sP β) (1 : ℂ) + K (sP β) (sP α) • single (sP β) (sP α) 1)) +
      ∑ α : Fin W, ∑ β : Fin W, (((Real.toNNReal (b / W) : ℝ≥0) : ℝ) : ℂ) •
        (K (sP α) (sQ β) • single (sP α) (sQ β) (1 : ℂ) + K (sQ β) (sP α) • single (sQ β) (sP α) 1) := by
  rw [tmV, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1 <;> refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  · exact tm_pairA b K α β
  · exact tm_pairB b K α β

theorem sP_injective : Function.Injective (sP (W := W)) := fun _ _ h => by simpa using h
theorem sQ_injective : Function.Injective (sQ (W := W)) := fun _ _ h => by simpa using h

/-- **The contraction lemma**: `‖𝒱(K)‖ ≤ (3/W)‖K‖`. -/
theorem tm_contract_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (K : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ‖tmV b K‖ ≤ 3 / W * ‖K‖ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have htA : ((tA W b : ℝ≥0) : ℝ) ≤ 1 / W := by
    rw [tA, Real.coe_toNNReal _ (by apply div_nonneg <;> linarith)]
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  have htB : ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) ≤ 1 / W := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  have hK := norm_nonneg K
  have h1 := tm_sym_le K (sP_injective (W := W)) sP_injective ((tA W b : ℝ) / 2) (by positivity)
  have h2 := tm_sym_le K (sP_injective (W := W)) sQ_injective
    ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) (NNReal.coe_nonneg _)
  rw [tm_contract_eq]
  refine (norm_add_le _ _).trans ?_
  have hA : 2 * ((tA W b : ℝ) / 2) * ‖K‖ ≤ 1 / W * ‖K‖ := by nlinarith
  have hB : 2 * ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) * ‖K‖ ≤ 2 * (1 / W * ‖K‖) := by nlinarith
  have e : 3 / (W : ℝ) * ‖K‖ = 1 / W * ‖K‖ + 2 * (1 / W * ‖K‖) := by ring
  linarith

end BlockBand.Transmission.PassiveLayer
