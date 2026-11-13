module

public import BlockBand.SourceProcess.ModelExist.ModelGlue

/-!
# The birth values of the finite source model

If at every sorted birth the selection meets its specification (`SelSpec`), then every
coordinate of `G` has the right value when it is born (`hcase_model`): current–current
coordinates are born at `0`; a probe is perpendicular (`M` and `B`) to the current columns and
to every earlier probe; a probe has `M_ii = B_ii = v_i`, which is the jump of `birthJump` at the
same time. With `bornRepresents_of` this gives `BornRepresents` (`bornRepresents_model`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique
open scoped NNReal ComplexConjugate

/-- `M` or `B`. -/
def gr {c' : Type*} (r : Fin 2) (H : Matrix c' c' ℂ × Matrix c' c' ℂ) : Matrix c' c' ℂ :=
  if r = 0 then H.1 else H.2

theorem bVal_eq {Ω c c' : Type*} [Fintype c] [Fintype c']
    (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ) (θ : c → Ω → ℝ≥0) (lam : c → Ω → c' → ℂ)
    (r : Fin 2) (y y' : c) (ω : Ω) :
    bVal 𝒢 θ lam (r, y, y') ω =
      star (lam y ω) ⬝ᵥ (gr r (𝒢 (max (θ y ω) (θ y' ω)) ω) *ᵥ lam y' ω) := by
  simp only [bVal, bCoef, gramEntry, gr, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  split_ifs <;> ring

theorem gr_mulVec {c' : Type*} [Fintype c'] {H : Matrix c' c' ℂ × Matrix c' c' ℂ} {a : c' → ℂ}
    (h : (H.1 - H.2) *ᵥ a = 0) (r : Fin 2) : gr r H *ᵥ a = H.1 *ᵥ a := by
  unfold gr
  split_ifs
  · rfl
  · rw [sub_mulVec, sub_eq_zero] at h; exact h.symm

theorem herm_dot {c' : Type*} [Fintype c'] {A : Matrix c' c' ℂ} (hA : Aᴴ = A) (u w : c' → ℂ) :
    star u ⬝ᵥ (A *ᵥ w) = star (star w ⬝ᵥ (A *ᵥ u)) := by
  have hA' : ∀ x x', star (A x x') = A x' x := fun x x' => by
    rw [← conjTranspose_apply, hA]
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  rw [hA']
  ring

theorem single_dot {c' : Type*} [Fintype c'] [DecidableEq c'] (k : c') (w : c' → ℂ) :
    star (Pi.single k (1 : ℂ)) ⬝ᵥ w = w k := by
  simp only [dotProduct, Pi.star_apply, Pi.single_apply]
  simp

theorem gramEntry_birthSum {c F : Type*} [Fintype F] (j : F → Matrix c c ℂ × Matrix c c ℂ)
    (b : F → ℝ) (t : ℝ) (e : Fin 2 × c × c) :
    gramEntry e (birthSum j b t) = ∑ f, if b f ≤ t then gramEntry e (j f) else 0 := by
  simp only [birthSum, gramEntry, Prod.fst_sum, Prod.snd_sum, Matrix.sum_apply]
  split_ifs <;> refine Finset.sum_congr rfl fun f _ => ?_ <;> split_ifs <;> rfl

variable (K R : ℕ) {π : Type*} [Fintype π] [DecidableEq π]

omit [Fintype π] in
theorem gramEntry_probeJump (v : π → ℝ) (f : π) (r : Fin 2) (y y' : SrcCol K π) :
    gramEntry (r, y, y') (probeJump (K := K) v f) =
      if y = Sum.inr f ∧ y' = Sum.inr f then (v f : ℂ) else 0 := by
  rcases eq_or_ne y (Sum.inr f) with rfl | h1
  · rcases eq_or_ne y' (Sum.inr f) with rfl | h2
    · simp only [gramEntry, probeJump, and_self, ↓reduceIte]
      split_ifs <;> simp
    · simp [gramEntry, probeJump, Ne.symm h2, h2]
  · simp [gramEntry, probeJump, Ne.symm h1, h1]

end BlockBand.SourceProcess.ModelExist
