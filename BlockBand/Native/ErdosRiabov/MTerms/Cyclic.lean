module

public import BlockBand.Native.ErdosRiabov.MTerms.Basic

/-!
# Deterministic `M`-terms: cyclicity

Proves `BlockBand.Native.ErdosRiabov.Split.CyclicStatement` (the cyclicity of `M`-traces,
Erdős–Riabov arXiv 2506.06441v1, at profile `σ S`):
for `k ≥ 2`,
`Tr[M̃(z_1, A_1, …, A_{k-1}, z_k) A_k] = Tr[A_{k-1} M̃(z_k, A_k, z_1, A_1, …, A_{k-2}, z_{k-1})]`,
the trace of diagonal matrices being the bilinear pairing `∑_a u a * v a` of their diagonals.

Setting: `n : ℕ`, profile `S : Matrix (Fin n) (Fin n) ℝ` with `ProfileHyp S`, `σ ∈ [0,1]`,
spectral data `m : ℕ → ℂ` with `‖m i‖ < 1` for all `i`, observables `A : ℕ → Fin n → ℂ`.
These hypotheses are used only through the invertibility of the stability operators
(`chainTilde_recursion2`, `stabOp_mulVec_sub_one`) and the symmetry of `S`
(`dotProduct_stabOp_mulVec`).

Main declarations.
* `cycAtil σ S m A c b`: the auxiliary observables `Ã_b` of Erdős–Riabov, in window form with
  base `c`.
* `chainTilde_expand`: `M̃_{[j,k]} = M̃_{[j,j+1]} M̃_{[j+1,k]} + ∑_{b=j+1}^{k-1} σ m_j m_{b+1}
  S[M̃_{[j,b+1]}] M̃_{[b+1,k]}` for `j < k` (the second form of the recursion with
  `(1 - σ m_j m_k S)` inverted out).
* `sum_cycAtil_mul`, `cyclic_aux` (window form with base `c`):
  `∑_{b ∈ [c+1, J)} M̃(window [b, J], entry b := (m c, Ã_b)) = M̃_{[c,J]}` for `J ≥ c + 2`.
* `window_cyclic`: for `j < k` and any `B`,
  `M̃_{[j+1,k+1]} ⬝ᵥ B = A_k ⬝ᵥ M̃(window [j, k], entry j := (m (k+1), B))`.
* `cyclic_holds : CyclicStatement`.

Proof (the Erdős–Riabov argument, rewritten for windows of arbitrary sequences with
`Function.update` for the replaced first entry, and with a general base index `c` in place of
slot `0`, so no shift is needed in the induction). `cyclic_aux`: strong induction on `J`;
unfold each summand with the plain recursion `chainTilde_of_lt`, remove the update by locality
(`chainTilde_congr`), exchange the double sum (`Finset.sum_comm'`), apply the induction hypothesis
to the inner sums, collapse the `Ã`-terms with `chainTilde_expand` and close with
`chainTilde_recursion2` for `M̃_{[c,J]}`.
`window_cyclic`: strong induction on `k - j`; expand `M̃_{[j+1,k+1]}` by `chainTilde_recursion2`,
move `K_{j+1,k+1}` across the pairing, apply the induction hypothesis to each `M̃_{[i,k+1]}`
and recombine with `cyclic_aux` at base `j`; the base case `k = j + 1`
is the symmetry of `K`. `cyclic_holds`: `window_cyclic` at `j = 0`, and the rotated chain is the
window `[0, k-1]` of the updated sequences shifted by one (`chainTilde_shift`).

Inputs: Mathlib; `BlockBand.Native.ErdosRiabov.Split.MTermsStatement`;
`BlockBand.Native.ErdosRiabov.MTerms.Basic` (`chainTilde_self`, `chainTilde_of_lt`,
`chainTilde_one_step`, `chainTilde_recursion2`, `chainTilde_congr`, `chainTilde_shift`,
`stabOp_mulVec_sub_one`, `dotProduct_stabOp_mulVec`, `norm_mul_lt_one_of_lt_one`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MTerms

open BlockBand.Native.ErdosRiabov.Split Matrix Finset

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} {σ : ℝ} {m : ℕ → ℂ} {A : ℕ → Fin n → ℂ}

/-- Updating one entry by a value of norm `< 1` keeps all entries of norm `< 1`. -/
theorem norm_update_lt_one (hm : ∀ i, ‖m i‖ < 1) (b : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    ∀ i, ‖Function.update m b x i‖ < 1 := by
  intro i
  by_cases h : i = b
  · subst h; simpa using hx
  · rw [Function.update_of_ne h]; exact hm i

/-- Reindexing `∑_{i ∈ (a, k+1)} f i = ∑_{b ∈ [a, k)} f (b + 1)`. -/
theorem sum_Ioo_succ_eq {β : Type*} [AddCommMonoid β] (f : ℕ → β) (a k : ℕ) :
    ∑ i ∈ Finset.Ioo a (k + 1), f i = ∑ b ∈ Finset.Ico a k, f (b + 1) := by
  rw [Finset.sum_Ico_add' f a k 1]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x; simp only [mem_Ioo, mem_Ico]; omega

/-- Full first-index expansion: `M̃_{[j,k]} = M̃_{[j,j+1]} M̃_{[j+1,k]} +
∑_{b=j+1}^{k-1} σ m_j m_{b+1} S[M̃_{[j,b+1]}] M̃_{[b+1,k]}` for `j < k` (the term `b = k-1` is the
`(1 - σ m_j m_k S)` correction of the second form of the recursion). -/
theorem chainTilde_expand (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) {j k : ℕ} (h : j < k) :
    chainTilde σ S m A j k =
      chainTilde σ S m A j (j + 1) * chainTilde σ S m A (j + 1) k +
        ∑ b ∈ Finset.Ico (j + 1) k, ((σ : ℂ) * m j * m (b + 1)) •
          (selfEnergy S (chainTilde σ S m A j (b + 1)) * chainTilde σ S m A (b + 1) k) := by
  rcases Nat.lt_or_ge (j + 1) k with h2 | h2
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : j + 1 ≤ k' := by omega
    rw [Finset.sum_Ico_succ_top hk', ← sum_Ioo_succ_eq (fun i => ((σ : ℂ) * m j * m i) •
      (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i (k' + 1))),
      chainTilde_self, ← add_assoc]
    set v := chainTilde σ S m A j (j + 1) * chainTilde σ S m A (j + 1) (k' + 1) +
      ∑ i ∈ Finset.Ioo (j + 1) (k' + 1), ((σ : ℂ) * m j * m i) •
        (selfEnergy S (chainTilde σ S m A j i) * chainTilde σ S m A i (k' + 1)) with hv
    have hrec : chainTilde σ S m A j (k' + 1) = stabOp σ S (m j * m (k' + 1)) *ᵥ v :=
      chainTilde_recursion2 hS hσ hm (by omega)
    have hsub := stabOp_mulVec_sub_one hS hσ (norm_mul_lt_one_of_lt_one (hm j) (hm (k' + 1))) v
    rw [← hrec] at hsub
    rw [sub_eq_iff_eq_add'] at hsub
    conv_lhs => rw [hsub]
    congr 1
    funext x
    simp [selfEnergy, mul_assoc]
  · have hk : k = j + 1 := by omega
    subst hk
    rw [chainTilde_self, Finset.Ico_self, Finset.sum_empty, add_zero]
    funext x
    simp

/-- The auxiliary observables `Ã_b` in window form with base index `c` (slot `c` holds
`(z_0, A_0)`): `Ã_{c+1} = M̃_{[c,c+1]} M̃_{[c+1,c+2]}` and, for `b ≠ c + 1`,
`Ã_b = σ m_{c+1} m_{b+1} M̃_{[c,c+1]} S[M̃_{[c+1,b+1]}]`. -/
def cycAtil (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ) (c b : ℕ) :
    Fin n → ℂ :=
  if b = c + 1 then chainTilde σ S m A c (c + 1) * chainTilde σ S m A (c + 1) (c + 1 + 1)
  else ((σ : ℂ) * m (c + 1) * m (b + 1)) •
    (chainTilde σ S m A c (c + 1) * selfEnergy S (chainTilde σ S m A (c + 1) (b + 1)))

/-- Collapse of the first `Ã`-terms:
`∑_{b=c+1}^{J-1} Ã_b M̃_{[b+1,J]} = M̃_{[c,c+1]} M̃_{[c+1,J]}`. -/
theorem sum_cycAtil_mul (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) (c J : ℕ) (hJ : c + 2 ≤ J) :
    ∑ b ∈ Finset.Ico (c + 1) J, cycAtil σ S m A c b * chainTilde σ S m A (b + 1) J =
      chainTilde σ S m A c (c + 1) * chainTilde σ S m A (c + 1) J := by
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : c + 1 < J),
    chainTilde_expand hS hσ hm (by omega : c + 1 < J), mul_add, Finset.mul_sum]
  rw [cycAtil, ite_eq_left rfl, mul_assoc]
  congr 1
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hb' := Finset.mem_Ico.mp hb
  rw [cycAtil, ite_eq_right (by omega)]
  funext x
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The auxiliary cyclic identity in window form with base index `c`: for `J ≥ c + 2`,
`∑_{b=c+1}^{J-1} M̃(z_c, Ã_b, z_{b+1}, A_{b+1}, …, z_J) = M̃_{[c,J]}`, where the chain on the left
is the window `[b, J]` of the sequences with entry `b` replaced by `(m c, Ã_b)`. -/
theorem cyclic_aux (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) (c : ℕ) : ∀ J, c + 2 ≤ J →
    ∑ b ∈ Finset.Ico (c + 1) J, chainTilde σ S (Function.update m b (m c))
        (Function.update A b (cycAtil σ S m A c b)) b J = chainTilde σ S m A c J := by
  intro J
  induction J using Nat.strong_induction_on with
  | _ J ih =>
  intro hJ
  have hY : ∀ b ∈ Finset.Ico (c + 1) J,
      chainTilde σ S (Function.update m b (m c)) (Function.update A b (cycAtil σ S m A c b)) b J =
        stabOp σ S (m c * m J) *ᵥ (cycAtil σ S m A c b * chainTilde σ S m A (b + 1) J +
          ∑ p ∈ Finset.Ioo b J, ((σ : ℂ) * m c * m p) •
            (selfEnergy S (chainTilde σ S (Function.update m b (m c))
              (Function.update A b (cycAtil σ S m A c b)) b p) * chainTilde σ S m A p J)) := by
    intro b hb
    have hbJ : b < J := (Finset.mem_Ico.mp hb).2
    rw [chainTilde_of_lt hbJ, Function.update_self, Function.update_self,
      Function.update_of_ne (ne_of_gt hbJ)]
    have h1 : chainTilde σ S (Function.update m b (m c))
        (Function.update A b (cycAtil σ S m A c b)) (b + 1) J = chainTilde σ S m A (b + 1) J := by
      apply chainTilde_congr
      · intro i hi _; exact Function.update_of_ne (by omega) _ _
      · intro i hi _; exact Function.update_of_ne (by omega) _ _
    rw [h1]
    congr 2
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' := Finset.mem_Ioo.mp hp
    rw [Function.update_of_ne (by omega : p ≠ b)]
    congr 2
    apply chainTilde_congr
    · intro i hi _; exact Function.update_of_ne (by omega) _ _
    · intro i hi _; exact Function.update_of_ne (by omega) _ _
  rw [Finset.sum_congr rfl hY, ← Matrix.mulVec_sum, Finset.sum_add_distrib,
    sum_cycAtil_mul hS hσ hm c J hJ, chainTilde_recursion2 hS hσ hm hJ]
  congr 2
  rw [Finset.sum_comm' (t' := Finset.Ioo (c + 1) J) (s' := fun p => Finset.Ico (c + 1) p)
    (f := fun b p => ((σ : ℂ) * m c * m p) • (selfEnergy S (chainTilde σ S
      (Function.update m b (m c)) (Function.update A b (cycAtil σ S m A c b)) b p) *
        chainTilde σ S m A p J))
    (by intro b p; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' := Finset.mem_Ioo.mp hp
  rw [← ih p hp'.2 (by omega), selfEnergy, Matrix.mulVec_sum, Finset.sum_mul, Finset.smul_sum]
  rfl

/-- Pairing identity `(X Y) ⬝ C = Y ⬝ (C X)` for pointwise products. -/
theorem mul_dotProduct_swap (X Y C : Fin n → ℂ) : (X * Y) ⬝ᵥ C = Y ⬝ᵥ (C * X) := by
  simp only [dotProduct, Pi.mul_apply]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Pairing identity `(s • (X Y)) ⬝ C = Y ⬝ (s • (C X))`. -/
theorem smul_mul_dotProduct_swap (s : ℂ) (X Y C : Fin n → ℂ) :
    (s • (X * Y)) ⬝ᵥ C = Y ⬝ᵥ (s • (C * X)) := by
  simp only [dotProduct, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Congruence for a window `[b, k]` whose entry `b` is replaced: only the replaced values and the
entries in `(b, k]` (spectral data) and `(b, k)` (observables) matter. -/
theorem chainTilde_update_congr {b k : ℕ} {m m' : ℕ → ℂ} {A A' : ℕ → Fin n → ℂ} {x x' : ℂ}
    {X X' : Fin n → ℂ} (hx : x = x') (hX : X = X') (hm : ∀ i, b < i → i ≤ k → m i = m' i)
    (hA : ∀ i, b < i → i < k → A i = A' i) :
    chainTilde σ S (Function.update m b x) (Function.update A b X) b k =
      chainTilde σ S (Function.update m' b x') (Function.update A' b X') b k := by
  apply chainTilde_congr
  · intro i hi hik
    by_cases h : i = b
    · subst h; simp only [Function.update_self, hx]
    · rw [Function.update_of_ne h, Function.update_of_ne h]; exact hm i (by omega) hik
  · intro i hi hik
    by_cases h : i = b
    · subst h; simp only [Function.update_self, hX]
    · rw [Function.update_of_ne h, Function.update_of_ne h]; exact hA i (by omega) hik

/-- Window cyclicity (cyclicity for the window `[j+1, k+1]`, traced against `B`):
`Tr[M̃(z_{j+1}, …, z_{k+1}) B] = Tr[A_k M̃(z_{k+1}, B, z_{j+1}, A_{j+1}, …, z_k)]`, the chain on the
right being the window `[j, k]` with entry `j` replaced by `(m (k+1), B)`. Strong induction on
`d = k - j`. -/
theorem window_cyclic (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) : ∀ d j k, k - j = d → j < k → ∀ B : Fin n → ℂ,
    chainTilde σ S m A (j + 1) (k + 1) ⬝ᵥ B =
      A k ⬝ᵥ chainTilde σ S (Function.update m j (m (k + 1))) (Function.update A j B) j k := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro j k hd hjk B
  have hm' := norm_update_lt_one hm j (hm (k + 1)) (x := m (k + 1))
  have hC : chainTilde σ S (Function.update m j (m (k + 1))) (Function.update A j B) j (j + 1) =
      stabOp σ S (m (j + 1) * m (k + 1)) *ᵥ B := by
    rw [chainTilde_one_step, Function.update_self, Function.update_self,
      Function.update_of_ne (by omega : j + 1 ≠ j), mul_comm]
  rcases Nat.lt_or_ge (j + 1) k with h2 | h2
  · rw [chainTilde_recursion2 hS hσ hm (by omega : j + 1 + 2 ≤ k + 1), dotProduct_stabOp_mulVec hS,
      add_dotProduct, sum_dotProduct, sum_Ioo_succ_eq, mul_dotProduct_swap,
      ← cyclic_aux hS hσ hm' j k (by omega), dotProduct_sum,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : j + 1 < k),
      ih (k - (j + 1)) (by omega) (j + 1) k rfl h2]
    congr 1
    · congr 1
      apply chainTilde_update_congr
      · rw [Function.update_self]
      · rw [cycAtil, ite_eq_left rfl, hC]
        congr 1
        apply chainTilde_congr
        · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
        · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
      · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
      · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
    · refine Finset.sum_congr rfl (fun b hb => ?_)
      have hb' := Finset.mem_Ico.mp hb
      rw [smul_mul_dotProduct_swap, ih (k - b) (by omega) b k rfl hb'.2]
      congr 1
      apply chainTilde_update_congr
      · rw [Function.update_self]
      · rw [cycAtil, ite_eq_right (by omega), hC, Function.update_of_ne (by omega : j + 1 ≠ j),
          Function.update_of_ne (by omega : b + 1 ≠ j)]
        congr 3
        apply chainTilde_congr
        · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
        · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
      · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
      · intro i hi _; exact (Function.update_of_ne (by omega) _ _).symm
  · have hk : k = j + 1 := by omega
    subst hk
    rw [hC, chainTilde_one_step, dotProduct_stabOp_mulVec hS]

/-- Cyclicity of `M`-traces at profile `σ S`. -/
theorem cyclic_holds : CyclicStatement := by
  intro n S hS σ hσ m hm A k hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := window_cyclic hS hσ hm (A := A) (k' - 0) 0 k' rfl (by omega) (A (k' + 1))
  have e1 : (fun p => rotateChain (k' + 1) m (p + 1)) = Function.update m 0 (m (k' + 1)) := by
    funext p
    cases p with
    | zero => simp [rotateChain]
    | succ q => simp [rotateChain]
  have e2 : (fun p => rotateChain (k' + 1) A (p + 1)) = Function.update A 0 (A (k' + 1)) := by
    funext p
    cases p with
    | zero => simp [rotateChain]
    | succ q => simp [rotateChain]
  have hrot : chainTilde σ S (rotateChain (k' + 1) m) (rotateChain (k' + 1) A) 1 (k' + 1) =
      chainTilde σ S (Function.update m 0 (m (k' + 1)))
        (Function.update A 0 (A (k' + 1))) 0 k' := by
    rw [← e1, ← e2, chainTilde_shift]
  rw [Nat.add_sub_cancel, hrot]
  exact h

end BlockBand.Native.ErdosRiabov.MTerms
