module

public import BlockBand.Transmission.Bridge.Transport

/-!
# The far-to-near corner of the boundary resolvent is injective

`corner_injective`: for a path of length `n ≥ 1` with invertible `𝓜` and invertible bonds, the
far-to-near corner `ℝ_{near,far}` of the boundary resolvent is injective. The proof is a chain
argument: if `ℝ_{near,far} v = 0`, the pencil rows force the interior blocks of the solution to
vanish one after another, and then `v = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingAux

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge

variable {W : ℕ}

theorem vec_eq_zero_of_isUnit {B : Matrix (Fin W) (Fin W) ℂ} (hB : IsUnit B) {v : Fin W → ℂ}
    (hv : B *ᵥ v = 0) : v = 0 :=
  eq_zero_of_mulVec_eq_zero ((Matrix.isUnit_iff_isUnit_det B).1 hB).ne_zero hv

theorem vec_eq_zero_of_isUnit_star {B : Matrix (Fin W) (Fin W) ℂ} (hB : IsUnit B)
    {v : Fin W → ℂ} (hv : Bᴴ *ᵥ v = 0) : v = 0 := by
  refine eq_zero_of_mulVec_eq_zero ?_ hv
  rw [det_conjTranspose]
  exact star_ne_zero.2 ((Matrix.isUnit_iff_isUnit_det B).1 hB).ne_zero

/-- The near-port row of `Cᴴ x` only sees the first interior block. -/
theorem conjC_mulVec_near {n : ℕ} (hn : 1 ≤ n) (ω : GrowthPath W) (x : Fin n × Fin W → ℂ)
    (c : Fin W) :
    ((pathPortCoupling (pathAt W n ω))ᴴ *ᵥ x) (0, c) =
      ((ω.2 n)ᴴ *ᵥ fun a => x (⟨0, hn⟩, a)) c := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, conjTranspose_apply]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp [pathPortCoupling, pathAt]
  · intro j _ hj
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [pathPortCoupling, hj']
  · simp

/-- Row `i` of `C y`: the near bond on block `0`, the far bond on block `n-1`. -/
theorem C_mulVec_row {n : ℕ} (ω : GrowthPath W) (y : Fin 2 × Fin W → ℂ) (i : Fin n)
    (a : Fin W) :
    (pathPortCoupling (pathAt W n ω) *ᵥ y) (i, a) =
      (if i.val = 0 then (ω.2 n *ᵥ fun c => y (0, c)) a else 0) +
        (if i.val + 1 = n then (ω.2 0 *ᵥ fun c => y (1, c)) a else 0) := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases h0 : i.val = 0 <;> by_cases h1 : i.val + 1 = n <;>
    simp [pathPortCoupling, pathAt, h0, h1]

theorem pathMatrix_apply_far {r : ℕ} (p : PathSample W r) {i j : Fin r} (h1 : i ≠ j)
    (h2 : i.val + 1 ≠ j.val) (h3 : j.val + 1 ≠ i.val) (a b : Fin W) :
    pathMatrix p (i, a) (j, b) = 0 := by
  simp [pathMatrix, h1, h2, h3]

/-- Row `i` of `(H - E) x` when the blocks `0..i` of `x` vanish (`i + 1 < n`). -/
theorem pencil_mulVec_row {n : ℕ} (E : ℝ) (ω : GrowthPath W) (x : Fin n × Fin W → ℂ)
    (i : Fin n) (hi : i.val + 1 < n) (hx : ∀ j : Fin n, j.val ≤ i.val → ∀ a, x (j, a) = 0)
    (a : Fin W) :
    ((pathMatrix (pathAt W n ω) - (E : ℂ) • 1) *ᵥ x) (i, a) =
      ((ω.2 (n - 1 - i.val))ᴴ *ᵥ fun b => x (⟨i.val + 1, hi⟩, b)) a := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨i.val + 1, hi⟩ : Fin n)]
  · refine Finset.sum_congr rfl fun b _ => ?_
    have hne : (i, a) ≠ ((⟨i.val + 1, hi⟩ : Fin n), b) := fun h => by
      have := congrArg (fun z => z.1.val) h; simp at this
    rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_ne hne]
    have hij : i ≠ ⟨i.val + 1, hi⟩ := fun h => by have := congrArg Fin.val h; simp at this
    simp [pathMatrix, hij, pathAt]
  · intro j _ hj
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hle : j.val ≤ i.val
    · rw [hx j hle b, mul_zero]
    · have hj' : j.val ≠ i.val + 1 := fun h => hj (Fin.ext h)
      have h1 : i ≠ j := fun h => hle (by rw [h])
      have hne : (i, a) ≠ (j, b) := fun h => h1 (congrArg Prod.fst h)
      rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_ne hne,
        pathMatrix_apply_far _ h1 (Ne.symm hj') (by omega)]
      simp
  · simp

/-- **The far-to-near corner `ℝ_{near,far}` is injective** (`n ≥ 1`, `𝓜` and all bonds
invertible). -/
theorem corner_injective (b E : ℝ) {n : ℕ} (hn : 1 ≤ n) (ω : GrowthPath W)
    (hM : IsUnit (fullPathMatrix b E W n ω)) (hB : ∀ k, IsUnit (ω.2 k)) {u : Fin W → ℂ}
    (hu : portBlock (boundaryResolvent b E W n ω) 0 1 *ᵥ u = 0) : u = 0 := by
  obtain ⟨h1, h2⟩ := full_solution b E n ω hM
  set U := boundaryToInterior b E W n ω
  set R := boundaryResolvent b E W n ω
  set C := pathPortCoupling (pathAt W n ω) with hC
  set Mp := pathMatrix (pathAt W n ω) - (E : ℂ) • 1 with hMp
  set w : Fin 2 × Fin W → ℂ := fun y => if y.1 = 1 then u y.2 else 0 with hw
  set x := U *ᵥ w
  set y := R *ᵥ w
  have e1 : Mp *ᵥ x + C *ᵥ y = 0 := by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, h1, zero_mulVec]
  have e2 : Cᴴ *ᵥ x + boundaryZ b E • y = w := by
    rw [mulVec_mulVec, ← smul_mulVec, ← add_mulVec, h2, one_mulVec]
  have hy0 : ∀ c, y (0, c) = 0 := fun c => by
    have := congrFun hu c
    simp only [y, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, hw]
    simpa [portBlock, mulVec, dotProduct] using this
  have hx0 : (fun a => x (⟨0, hn⟩, a)) = 0 := by
    refine vec_eq_zero_of_isUnit_star (hB n) (funext fun c => ?_)
    have := congrFun e2 (0, c)
    rw [Pi.add_apply, conjC_mulVec_near hn, Pi.smul_apply, hy0, smul_zero, add_zero] at this
    simpa [hw] using this
  have hxi : ∀ i : ℕ, i < n → ∀ j : Fin n, j.val ≤ i → ∀ a, x (j, a) = 0 := by
    intro i
    induction i with
    | zero =>
      intro _ j hj a
      have hj0 : j = ⟨0, hn⟩ := Fin.ext (by show j.val = 0; omega)
      rw [hj0]; exact congrFun hx0 a
    | succ i ih =>
      intro hi j hj a
      have ih' := ih (by omega)
      rcases Nat.lt_or_ge j.val (i + 1) with hlt | hge
      · exact ih' j (by omega) a
      have hji : j = ⟨i + 1, hi⟩ := Fin.ext (by show j.val = i + 1; omega)
      have hrow : (fun b => x (⟨i + 1, hi⟩, b)) = 0 := by
        refine vec_eq_zero_of_isUnit_star (hB (n - 1 - i)) (funext fun a' => ?_)
        have := congrFun e1 (⟨i, by omega⟩, a')
        rw [Pi.add_apply, pencil_mulVec_row E ω x ⟨i, by omega⟩ hi ih' a', C_mulVec_row] at this
        have hn1 : i + 1 ≠ n := by omega
        simp only [hn1, ite_false, add_zero] at this
        have hz : (if i = 0 then (ω.2 n *ᵥ fun c => y (0, c)) a' else 0) = 0 := by
          split_ifs
          · have : (fun c => y (0, c)) = 0 := funext hy0
            rw [this, mulVec_zero]; rfl
          · rfl
        rw [hz, add_zero] at this
        exact this
      rw [hji]; exact congrFun hrow a
  have hx : x = 0 := funext fun z => hxi (n - 1) (by omega) z.1 (by omega) z.2
  have hy1 : (fun c => y (1, c)) = 0 := by
    refine vec_eq_zero_of_isUnit (hB 0) (funext fun a => ?_)
    have := congrFun e1 (⟨n - 1, by omega⟩, a)
    rw [Pi.add_apply, hx, mulVec_zero, Pi.zero_apply, zero_add, C_mulVec_row] at this
    have hn1 : n - 1 + 1 = n := by omega
    have hy0' : (fun c => y (0, c)) = 0 := funext hy0
    simp only [hn1, ite_true, hy0', mulVec_zero] at this
    simpa using this
  funext c
  have := congrFun e2 (1, c)
  rw [Pi.add_apply, hx, mulVec_zero, Pi.zero_apply, zero_add, Pi.smul_apply,
    show y (1, c) = 0 from congrFun hy1 c, smul_zero] at this
  simpa [hw] using this.symm

end BlockBand.SourceProcess.ClosingAux
