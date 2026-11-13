module

public import BlockBand.SourceProcess.CapLimit.Feasible

/-!
# The cap embedding `SrcCol K π ↪ SrcCol K' π` (`K ≤ K'`)

* `capEmb`: mode columns `(k, σ) ↦ (k, σ)`, probe columns fixed; its range misses exactly the
  mode columns `k ≥ K`.
* `srcSignature K'` does not couple the range with its complement and restricts to
  `srcSignature K`; the birth jumps restrict to the birth jumps.
* `gRestrict_initialGram`: the cap-`K'` initial Gram state restricts to the cap-`K` one, and
  `initialGram_diag_eq_zero`: its mode columns `k` with `t_k ≤ h²` vanish.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open Matrix Function
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws

variable {K K' : ℕ} (hK : K ≤ K') (π : Type*)

/-- The column embedding from cap `K` to cap `K'`. -/
def capEmb : SrcCol K π → SrcCol K' π := Sum.map (Prod.map (Fin.castLE hK) id) id

/-- The row embedding of the canonical blocks. -/
def rowEmb : Fin K × Fin 2 → Fin K' × Fin 2 := Prod.map (Fin.castLE hK) id

theorem rowEmb_injective : Injective (rowEmb hK) :=
  (Fin.castLE_injective hK).prodMap injective_id

theorem capEmb_injective : Injective (capEmb hK π) :=
  (rowEmb_injective hK).sumMap injective_id

variable {hK π}

theorem notMem_range_capEmb {y : SrcCol K' π} (hy : y ∉ Set.range (capEmb hK π)) :
    ∃ k : Fin K', ∃ σ : Fin 2, y = Sum.inl (k, σ) ∧ K ≤ k.val := by
  rcases y with ⟨k, σ⟩ | i
  · by_cases hk : k.val < K
    · exact absurd ⟨Sum.inl (⟨k.val, hk⟩, σ), rfl⟩ hy
    · exact ⟨k, σ, rfl, not_lt.1 hk⟩
  · exact absurd ⟨Sum.inr i, rfl⟩ hy

theorem notMem_range_rowEmb {x : Fin K' × Fin 2} (hx : x ∉ Set.range (rowEmb hK)) :
    K ≤ x.1.val := by
  by_contra h
  exact hx ⟨(⟨x.1.val, not_le.1 h⟩, x.2), rfl⟩

theorem capEmb_inr (i : π) : capEmb hK π (Sum.inr i) = Sum.inr i := rfl

variable [DecidableEq π]

theorem sep_srcSignature : Sep (capEmb hK π) (srcSignature K' π) := by
  intro a z hz
  have hne : capEmb hK π a ≠ z := fun h => hz ⟨a, h⟩
  exact ⟨diagonal_apply_ne _ hne, diagonal_apply_ne _ hne.symm⟩

theorem srcSignature_submatrix :
    (srcSignature K' π).submatrix (capEmb hK π) (capEmb hK π) = srcSignature K π := by
  unfold srcSignature
  rw [submatrix_diagonal _ _ (capEmb_injective hK π)]
  congr 1
  funext c
  rcases c with ⟨k, σ⟩ | i <;> rfl

theorem gRestrict_birthJump [Fintype π] (τ v : π → ℝ) (t : ℝ) :
    gRestrict (capEmb hK π) (birthJump (K := K') τ v t) = birthJump (K := K) τ v t := by
  unfold birthJump gRestrict
  refine Prod.ext ?_ ?_ <;> ext a b <;>
    simp only [Prod.fst_sum, Prod.snd_sum, submatrix_apply, Matrix.sum_apply] <;>
    refine Finset.sum_congr rfl fun i _ => ?_ <;> split_ifs <;>
    rcases a with ⟨k, σ⟩ | j <;> rcases b with ⟨k', σ'⟩ | j' <;>
    simp [capEmb, Matrix.single_apply]

theorem birthJump_inl_diag [Fintype π] (τ v : π → ℝ) (t : ℝ) (x : Fin K × Fin 2) :
    (birthJump (K := K) τ v t).1 (Sum.inl x) (Sum.inl x) = 0 := by
  unfold birthJump
  simp only [Prod.fst_sum, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

theorem re_trace_birthJump_le [Fintype π] (τ v : π → ℝ) (t : ℝ) :
    ((birthJump (K := K) τ v t).1.trace).re ≤ ∑ i, |v i| := by
  unfold birthJump
  rw [Prod.fst_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · simp only [trace_smul, trace_single_eq_same, smul_eq_mul, mul_one, Complex.ofReal_re]
    exact le_abs_self _
  · simp

/-!
### The initial Gram state
-/

/-- Row reindexing of a Gram pair: rows outside the range of an injective `e` are zero. -/
theorem gramPair_rowEmb {ι₁ ι₂ c : Type*} [Fintype ι₁] [Fintype ι₂] {e : ι₁ → ι₂}
    (he : Injective e) {P₁ : Matrix ι₁ ι₁ ℂ} {P₂ : Matrix ι₂ ι₂ ℂ}
    (hP : ∀ y y', P₂ (e y) (e y') = P₁ y y') {V₁ : Matrix ι₁ c ℂ} {V₂ : Matrix ι₂ c ℂ}
    (hV : ∀ y, V₂ (e y) = V₁ y) (h0 : ∀ x, x ∉ Set.range e → V₂ x = 0) :
    gramPair P₂ V₂ = gramPair P₁ V₁ := by
  refine Prod.ext ?_ ?_ <;> ext a b
  · simp only [gramPair, sourceGram, mul_apply, conjTranspose_apply]
    rw [sum_range_of_zero he fun x hx => by simp [h0 x hx]]
    simp only [hV]
  · simp only [gramPair, nearGram, mul_apply, conjTranspose_apply]
    rw [sum_range_of_zero he fun x hx => by simp [h0 x hx]]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [sum_range_of_zero he fun x hx => by simp [h0 x hx]]
    simp only [hV, hP]

omit [DecidableEq π] in
theorem gRestrict_initialGram [Fintype π] (t : ℕ → ℝ) (h : ℝ) :
    gRestrict (capEmb hK π) (initialGram K' π t h) = initialGram K π t h := by
  unfold initialGram
  refine gramPair_rowEmb (rowEmb_injective hK) ?_ ?_ ?_
  · intro y y'
    simp only [modeProjection, diagonal_apply, (rowEmb_injective hK).eq_iff]
    rfl
  · intro y
    funext a
    rcases a with ⟨k, σ⟩ | i
    · simp only [id, initialFrame, capEmb, rowEmb, Sum.map_inl, Prod.map_fst,
        Prod.map_snd, (Fin.castLE_injective hK).eq_iff, Fin.val_castLE]
    · rfl
  · intro x hx
    funext a
    have hxK := notMem_range_rowEmb hx
    rcases a with ⟨k, σ⟩ | i
    · simp only [initialFrame, capEmb, Sum.map_inl, Prod.map_fst,
        Pi.zero_apply]
      split_ifs with hk
      · have := congrArg Fin.val hk.1
        simp only [Fin.val_castLE] at this
        omega
      · rfl
    · rfl

omit [DecidableEq π] in
theorem initialGram_diag_eq_zero [Fintype π] {t : ℕ → ℝ} {h : ℝ} (k : Fin K') (σ : Fin 2)
    (hk : t k.val ≤ h ^ 2) :
    (initialGram K' π t h).1 (Sum.inl (k, σ)) (Sum.inl (k, σ)) = 0 := by
  have h0 : ∀ x, initialFrame K' π t h x (Sum.inl (k, σ)) = 0 := fun x => by
    simp only [initialFrame]
    split_ifs with h'
    · exact absurd h'.2 (not_lt.2 hk)
    · rfl
  simp [initialGram, gramPair, sourceGram, mul_apply, h0]

end BlockBand.SourceProcess.CapLimit
