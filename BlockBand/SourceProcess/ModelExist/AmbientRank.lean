module

public import BlockBand.SourceProcess.ModelExist.AmbientTwo
public import BlockBand.SourceProcess.ModelExist.Rank
public import Mathlib.Analysis.Matrix.PosDef

/-!
# The near rank of the extended initial frame

* `rank_ambP`: `rank P = K + R`;
* `principalMinorSum_extFrame_pos`: `e_{K+R}(B₀) > 0` for `B₀ = V₀ᴴ P V₀`, `V₀ = extFrame`: the
  principal minor on the near ambient columns is `det 1 = 1` and all principal minors of the
  positive semidefinite `B₀` are `≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open scoped ComplexOrder

variable (K R : ℕ)

/-- The near ambient coordinates. -/
def isNear : Amb K R → Prop
  | Sum.inl x => x.2 = 0
  | Sum.inr _ => True

instance : DecidablePred (isNear K R) := fun r => by
  rcases r with x | i
  · exact inferInstanceAs (Decidable (x.2 = 0))
  · exact isTrue trivial

theorem ambP_apply (r r' : Amb K R) :
    ambP K R r r' = if r = r' ∧ isNear K R r then 1 else 0 := by
  rcases r with x | i <;> rcases r' with x' | i' <;> simp [ambP, isNear, diagonal_apply]
  by_cases hx : x = x' <;> simp [hx]

theorem card_isNear : Fintype.card {r // isNear K R r} = K + R := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [isNear, Fin.sum_univ_two]

theorem rank_ambP : (ambP K R).rank = K + R := by
  rw [ambP, rank_diagonal, ← card_isNear K R]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun r => ?_)
  rcases r with x | i <;> simp [isNear]

/-- The near ambient columns of the extended frame. -/
def nearCols : Finset (ExtCol K R) :=
  (univ.filter (isNear K R)).map ⟨Sum.inr, Sum.inr_injective⟩

theorem card_nearCols : (nearCols K R).card = K + R := by
  rw [nearCols, card_map, ← Fintype.card_subtype, card_isNear]

theorem nearGram_extFrame_inr (t : ℕ → ℝ) (h : ℝ) (r r' : Amb K R) :
    nearGram (ambP K R) (extFrame K R t h) (Sum.inr r) (Sum.inr r') = ambP K R r r' := by
  simp only [nearGram, Matrix.mul_apply, conjTranspose_apply, extFrame]
  rw [Finset.sum_eq_single r' (fun b _ hb => by simp [hb]) (by simp)]
  simp only [↓reduceIte, mul_one]
  rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem principalMinorSum_extFrame_pos (t : ℕ → ℝ) (h : ℝ) :
    0 < principalMinorSum (K + R) (nearGram (ambP K R) (extFrame K R t h)) := by
  set B := nearGram (ambP K R) (extFrame K R t h)
  have hPh : (ambP K R)ᴴ = ambP K R := (isNearProjection_ambP K R).1
  have hPP : ambP K R * ambP K R = ambP K R := (isNearProjection_ambP K R).2.1
  have hB : B.PosSemidef := by
    have e : B = (ambP K R * extFrame K R t h)ᴴ * (ambP K R * extFrame K R t h) := by
      simp only [B, nearGram, conjTranspose_mul, hPh, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (ambP K R) (ambP K R), hPP]
    rw [e]; exact posSemidef_conjTranspose_mul_self _
  have hnn : ∀ s ∈ (univ : Finset (ExtCol K R)).powersetCard (K + R),
      0 ≤ (B.submatrix (fun i : s => (i : ExtCol K R)) (fun i : s => (i : ExtCol K R))).det.re :=
    fun s _ => (Complex.le_def.1 ((hB.submatrix _).det_nonneg)).1
  have hone : (B.submatrix (fun i : nearCols K R => (i : ExtCol K R))
      (fun i : nearCols K R => (i : ExtCol K R))) = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [nearCols, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk]
      at hi hj
    obtain ⟨r, hr, rfl⟩ := hi
    obtain ⟨r', hr', rfl⟩ := hj
    simp only [submatrix_apply, B, nearGram_extFrame_inr]
    rw [ambP_apply, Matrix.one_apply]
    by_cases hrr : r = r'
    · subst hrr; simp [hr]
    · simp [hrr]
  have hmem : nearCols K R ∈ (univ : Finset (ExtCol K R)).powersetCard (K + R) :=
    mem_powersetCard.2 ⟨subset_univ _, card_nearCols K R⟩
  have h1 := Finset.single_le_sum hnn hmem
  rw [hone, det_one, Complex.one_re] at h1
  unfold principalMinorSum
  rw [Complex.re_sum]
  linarith

end BlockBand.SourceProcess.ModelExist
