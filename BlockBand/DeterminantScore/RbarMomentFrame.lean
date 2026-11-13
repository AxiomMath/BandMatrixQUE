module

public import BlockBand.Angular.DetFactorFrame

/-!
# A global measurable frame of `w^⊥`

`minorFrame_spec`: for `m + 1 = n`, the map `x ↦ U_x ∈ ℂ^{n×m}` given by the Householder
frame (`DetFactor.hhFrame`) at the first nonzero coordinate `j₀` of `x`, with the columns
`e_k`, `k ≠ j₀`, is Borel measurable and, for every unit `x`, an isometry onto `x^⊥`
(`U_x*U_x = 1`, `U_x*x = 0`). This gives the `IsMinorFrame` hypothesis of `cornerMoment_holds`
(the minor `B` is the compression of `M` to `w^⊥`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.RbarMoment

open MeasureTheory Matrix
open BlockBand.Angular.DetFactor
open BlockBand.Internal.Contracts.CoareaPalm

variable {n m : ℕ}

/-- The increasing enumeration of `Fin n \ {j₀}` (`m + 1 = n`). -/
def skipEmb (h : m + 1 = n) (j₀ : Fin n) (k : Fin m) : Fin n :=
  if k.val < j₀.val then ⟨k.val, by omega⟩ else ⟨k.val + 1, by omega⟩

theorem skipEmb_injective (h : m + 1 = n) (j₀ : Fin n) : Function.Injective (skipEmb h j₀) := by
  intro k l hkl
  unfold skipEmb at hkl
  apply Fin.ext
  split_ifs at hkl with h1 h2 h2 <;> simp only [Fin.mk.injEq] at hkl <;> omega

theorem skipEmb_ne (h : m + 1 = n) (j₀ : Fin n) (k : Fin m) : skipEmb h j₀ k ≠ j₀ := by
  unfold skipEmb
  split_ifs with h1
  · intro he; rw [Fin.ext_iff] at he; simp only at he; omega
  · intro he; rw [Fin.ext_iff] at he; simp only at he; omega

/-- `j₀` is the first nonzero coordinate of `x`. -/
def firstRegion (j₀ : Fin n) : Set (Fin n → ℂ) := {x | x j₀ ≠ 0 ∧ ∀ k : Fin n, k < j₀ → x k = 0}

/-- The global frame: the Householder frame at the first nonzero coordinate. -/
def minorFrame (h : m + 1 = n) (x : Fin n → ℂ) : Matrix (Fin n) (Fin m) ℂ := by
  classical
  exact ∑ j₀ : Fin n, if x ∈ firstRegion j₀ then hhFrame j₀ (skipEmb h j₀) x else 0

theorem measurableSet_firstRegion (j₀ : Fin n) : MeasurableSet (firstRegion j₀) := by
  have h1 : MeasurableSet {x : Fin n → ℂ | x j₀ ≠ 0} :=
    (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_pi_apply j₀)
  have h2 : MeasurableSet {x : Fin n → ℂ | ∀ k : Fin n, k < j₀ → x k = 0} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (measurableSet_singleton (0 : ℂ)).preimage (measurable_pi_apply k)
  exact h1.inter h2

theorem measurable_l2Norm : Measurable fun x : Fin n → ℂ => l2Norm x := by
  unfold l2Norm
  exact (Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
    (continuous_apply k).norm.pow 2)).measurable

theorem measurable_hhVec (j₀ : Fin n) : Measurable fun x : Fin n → ℂ => hhVec j₀ x := by
  unfold hhVec
  refine measurable_id.add (measurable_pi_iff.mpr fun y => ?_)
  by_cases hy : y = j₀
  · subst hy
    simp only [Pi.single_eq_same]
    exact (Complex.measurable_ofReal.comp (measurable_l2Norm.div
      (measurable_pi_apply y).norm)).mul (measurable_pi_apply y)
  · simp only [Pi.single_eq_of_ne hy]
    exact measurable_const

theorem measurable_hhFrame_apply (j₀ : Fin n) (e : Fin m → Fin n) (a : Fin n) (b : Fin m) :
    Measurable fun x : Fin n → ℂ => hhFrame j₀ e x a b := by
  have hv := measurable_hhVec j₀
  have hN : Measurable fun x : Fin n → ℂ => hhNorm j₀ x := by
    unfold hhNorm
    exact Finset.measurable_sum _ fun y _ => ((measurable_pi_apply y).comp hv).norm.pow_const 2
  simp only [hhFrame, hhMatrix, submatrix_apply, id, Matrix.sub_apply, Matrix.smul_apply,
    vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  exact measurable_const.sub ((Complex.measurable_ofReal.comp (measurable_const.div hN)).mul
    (((measurable_pi_apply a).comp hv).mul
      (continuous_star.measurable.comp ((measurable_pi_apply (e b)).comp hv))))

theorem measurable_minorFrame (h : m + 1 = n) : Measurable (minorFrame h) := by
  classical
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  have e : (fun x => minorFrame h x a b) = fun x => ∑ j₀ : Fin n,
      if x ∈ firstRegion j₀ then hhFrame j₀ (skipEmb h j₀) x a b else 0 := by
    funext x
    simp only [minorFrame, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j₀ _ => ?_
    split_ifs <;> rfl
  rw [e]
  exact Finset.measurable_sum _ fun j₀ _ =>
    Measurable.ite (measurableSet_firstRegion j₀) (measurable_hhFrame_apply _ _ a b)
      measurable_const

theorem exists_firstRegion {x : Fin n → ℂ} (hx : x ≠ 0) : ∃ j₀, x ∈ firstRegion j₀ := by
  classical
  let S := Finset.univ.filter fun j : Fin n => x j ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
    exact ⟨j, by simpa [S] using hj⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (Finset.min'_mem S hS)).2, fun k hk => ?_⟩
  by_contra hne
  exact (not_le_of_gt hk) (Finset.min'_le S k (by simp [S, hne]))

theorem firstRegion_unique {x : Fin n → ℂ} {j k : Fin n} (hj : x ∈ firstRegion j)
    (hk : x ∈ firstRegion k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim (hj.1 (hk.2 j h))
  · exact h
  · exact False.elim (hk.1 (hj.2 k h))

/-- **A global measurable frame of `x^⊥`.** -/
theorem minorFrame_spec (h : m + 1 = n) {x : Fin n → ℂ} (hx : l2Norm x = 1) :
    (minorFrame h x)ᴴ * minorFrame h x = 1 ∧ (minorFrame h x)ᴴ *ᵥ x = 0 := by
  classical
  have hx0 : x ≠ 0 := by rintro rfl; simp [l2Norm] at hx
  obtain ⟨j₀, hj₀⟩ := exists_firstRegion hx0
  have e : minorFrame h x = hhFrame j₀ (skipEmb h j₀) x := by
    unfold minorFrame
    rw [Finset.sum_eq_single j₀]
    · rw [ite_eq_left hj₀]
    · intro k _ hk
      rw [ite_eq_right]
      exact fun hk' => hk (firstRegion_unique hk' hj₀)
    · simp
  rw [e]
  exact isFrame_hhFrame j₀ (skipEmb h j₀) (skipEmb_injective h j₀) (skipEmb_ne h j₀) hj₀.1

end BlockBand.DeterminantScore.RbarMoment
