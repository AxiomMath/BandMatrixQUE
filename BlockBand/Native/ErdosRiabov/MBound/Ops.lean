module

public import BlockBand.Native.ErdosRiabov.Split.MTermsStatement

/-!
# One-slot operators, the observable regularization and its commutator

One-slot kernel actions on functions of `k` sites, their decomposition into regularized parts,
and the commutator of the observable regularization with the generator. All operators act on the
same space (sites `x : Fin k → Fin N`, 0-based slots); a partial trace
is kept as a function of all `k` sites that does not depend on the traced one:
* `mbSlot K j f x = Σ_c K(x_j,c) f(x[j ↦ c])` (`K^{(j)}`);
* `mbTr j f x = Σ_c f(x[j ↦ c])` (`𝒯_j`, as a function of `x` constant in `x_j`);
* `mbGamma K j a f x = K(x_j,x_a) 𝒯_j f(x)` (`Γ^{(j)}` with anchor slot `a`);
* `mbRing K j a f x = Σ_c (K(x_j,c) - K(x_j,x_a)) f(x[j ↦ c])` (`Θ̊^{(j)}`);
* `mbReg j a f x = f x - [x_a = x_j] 𝒯_j f(x)` (the observable regularization `𝒟^{(j)}`);
* `mbG K j a f x = K(x_a,x_j) (𝒯_j f(x[a ↦ x_j]) + 𝒯_j f(x))` (`G^{(j)}`, giving `F̃`).

Main results:
* `mbSlot_eq_ring_add_gamma` (`K^{(j)} = Θ̊^{(j)} + Γ^{(j)}`), `mbRing_eq_slot_reg`
  (`Θ̊^{(j)} = K^{(j)} 𝒟^{(j)}`, `a ≠ j`);
* **`mbRingDecomp`**: for slots `J, J'` with `J' ∉ {J, A}`,
  `K^{(J')} K^{(J)} f = Θ̊^{(J')} Θ̊^{(J)} f + Γ^{(J)} K^{(J')} f + Γ^{(J')} K^{(J)} f
  - Γ^{(J')} Γ^{(J)} f` (`D = Z + R`);
* **`mbRegCommutator`**: for `T` symmetric with constant row and column sums `ρ` and
  `A ≠ J`, `𝒟 (T^{(A)} + T^{(J)}) f = (T^{(A)} + T^{(J)}) 𝒟 f + 𝒟 G f` (single form);
  `mbRegCommutator_double`: the double form with the full generator `Σ_i T^{(i)}` for two
  disjoint pairs `{J, A}`, `{J', A'}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function
open scoped BigOperators

variable {N k : ℕ}

/-!
## The operators
-/

/-- `K^{(j)}`: `(mbSlot K j f) x = Σ_c K(x_j,c) f(x[j ↦ c])`. -/
def mbSlot (K : Matrix (Fin N) (Fin N) ℂ) (j : Fin k) (f : (Fin k → Fin N) → ℂ) :
    (Fin k → Fin N) → ℂ :=
  fun x => ∑ c, K (x j) c * f (update x j c)

/-- The partial trace `𝒯_j f (x) = Σ_c f(x[j ↦ c])` (independent of `x_j`). -/
def mbTr (j : Fin k) (f : (Fin k → Fin N) → ℂ) : (Fin k → Fin N) → ℂ :=
  fun x => ∑ c, f (update x j c)

/-- `Γ^{(j)}` with anchor `a`: `K(x_j,x_a) 𝒯_j f(x)`. -/
def mbGamma (K : Matrix (Fin N) (Fin N) ℂ) (j a : Fin k) (f : (Fin k → Fin N) → ℂ) :
    (Fin k → Fin N) → ℂ :=
  fun x => K (x j) (x a) * mbTr j f x

/-- The regularized operator `Θ̊^{(j)}` with anchor `a`. -/
def mbRing (K : Matrix (Fin N) (Fin N) ℂ) (j a : Fin k) (f : (Fin k → Fin N) → ℂ) :
    (Fin k → Fin N) → ℂ :=
  fun x => ∑ c, (K (x j) c - K (x j) (x a)) * f (update x j c)

/-- The observable regularization `𝒟^{(j)}` with anchor `a`: `f x - [x_a = x_j] 𝒯_j f(x)`. -/
def mbReg (j a : Fin k) (f : (Fin k → Fin N) → ℂ) : (Fin k → Fin N) → ℂ :=
  fun x => f x - if x a = x j then mbTr j f x else 0

/-- The commutator term `G^{(j)}` with anchor `a`:
`K(x_a,x_j) (𝒯_j f(x[a ↦ x_j]) + 𝒯_j f(x))`. -/
def mbG (K : Matrix (Fin N) (Fin N) ℂ) (j a : Fin k) (f : (Fin k → Fin N) → ℂ) :
    (Fin k → Fin N) → ℂ :=
  fun x => K (x a) (x j) * (mbTr j f (update x a (x j)) + mbTr j f x)

/-- The generator `⊕_i K^{(i)}`. -/
def mbOplus (K : Matrix (Fin N) (Fin N) ℂ) (f : (Fin k → Fin N) → ℂ) : (Fin k → Fin N) → ℂ :=
  fun x => ∑ i, mbSlot K i f x

/-!
## Elementary facts
-/

theorem mbTr_update (j : Fin k) (f : (Fin k → Fin N) → ℂ) (x : Fin k → Fin N) (c : Fin N) :
    mbTr j f (update x j c) = mbTr j f x := by
  simp only [mbTr, update_idem]

theorem mbSlot_add (K : Matrix (Fin N) (Fin N) ℂ) (j : Fin k) (f g : (Fin k → Fin N) → ℂ) :
    mbSlot K j (f + g) = mbSlot K j f + mbSlot K j g := by
  funext x
  simp only [mbSlot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem mbSlot_sub (K : Matrix (Fin N) (Fin N) ℂ) (j : Fin k) (f g : (Fin k → Fin N) → ℂ) :
    mbSlot K j (f - g) = mbSlot K j f - mbSlot K j g := by
  funext x
  simp only [mbSlot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem mbTr_add (j : Fin k) (f g : (Fin k → Fin N) → ℂ) :
    mbTr j (f + g) = mbTr j f + mbTr j g := by
  funext x
  simp only [mbTr, Pi.add_apply, Finset.sum_add_distrib]

theorem mbTr_sub (j : Fin k) (f g : (Fin k → Fin N) → ℂ) :
    mbTr j (f - g) = mbTr j f - mbTr j g := by
  funext x
  simp only [mbTr, Pi.sub_apply, Finset.sum_sub_distrib]

theorem mbGamma_sub (K : Matrix (Fin N) (Fin N) ℂ) (j a : Fin k) (f g : (Fin k → Fin N) → ℂ) :
    mbGamma K j a (f - g) = mbGamma K j a f - mbGamma K j a g := by
  funext x
  simp only [mbGamma, mbTr_sub, Pi.sub_apply, mul_sub]

theorem mbReg_add (j a : Fin k) (f g : (Fin k → Fin N) → ℂ) :
    mbReg j a (f + g) = mbReg j a f + mbReg j a g := by
  funext x
  simp only [mbReg, mbTr_add, Pi.add_apply]
  split_ifs <;> ring

/-- `K^{(j)} = Θ̊^{(j)} + Γ^{(j)}` (any anchor). -/
theorem mbSlot_eq_ring_add_gamma (K : Matrix (Fin N) (Fin N) ℂ) (j a : Fin k)
    (f : (Fin k → Fin N) → ℂ) : mbSlot K j f = mbRing K j a f + mbGamma K j a f := by
  funext x
  simp only [mbSlot, mbRing, mbGamma, mbTr, Pi.add_apply, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum]
  ring

/-- `Θ̊^{(j)} = K^{(j)} ∘ 𝒟^{(j)}` for an anchor `a ≠ j`. -/
theorem mbRing_eq_slot_reg (K : Matrix (Fin N) (Fin N) ℂ) {j a : Fin k} (haj : a ≠ j)
    (f : (Fin k → Fin N) → ℂ) : mbRing K j a f = mbSlot K j (mbReg j a f) := by
  funext x
  simp only [mbRing, mbSlot, mbReg, mbTr_update, update_self, update_of_ne haj, mul_sub,
    sub_mul, Finset.sum_sub_distrib, mul_ite, mul_zero]
  congr 1
  rw [Finset.sum_ite_eq]
  simp [mbTr, Finset.mul_sum]

/-- `K^{(i)}` commutes with `Γ^{(j)}` (anchor `a`) when `i ∉ {j, a}`. -/
theorem mbSlot_gamma_comm (K K' : Matrix (Fin N) (Fin N) ℂ) {i j a : Fin k} (hij : i ≠ j)
    (hia : i ≠ a) (f : (Fin k → Fin N) → ℂ) :
    mbSlot K i (mbGamma K' j a f) = mbGamma K' j a (mbSlot K i f) := by
  funext x
  simp only [mbSlot, mbGamma, mbTr, update_of_ne hij.symm, update_of_ne hia.symm,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [update_comm hij, update_of_ne hij]
  ring

/-- **Ring decomposition**: for slots `J, J'` with anchors `A, A'` and `J' ∉ {J, A}`,
`K^{(J')} K^{(J)} f = Θ̊^{(J')} Θ̊^{(J)} f + (Γ^{(J)} K^{(J')} f + Γ^{(J')} K^{(J)} f
- Γ^{(J')} Γ^{(J)} f)`.
-/
theorem mbRingDecomp (K : Matrix (Fin N) (Fin N) ℂ) {J A J' A' : Fin k} (h1 : J' ≠ J)
    (h2 : J' ≠ A) (f : (Fin k → Fin N) → ℂ) :
    mbSlot K J' (mbSlot K J f) = mbRing K J' A' (mbRing K J A f) +
      (mbGamma K J A (mbSlot K J' f) + mbGamma K J' A' (mbSlot K J f) -
        mbGamma K J' A' (mbGamma K J A f)) := by
  have e1 := mbSlot_eq_ring_add_gamma K J A f
  have e2 := mbSlot_eq_ring_add_gamma K J' A' (mbRing K J A f)
  have e3 : mbRing K J A f = mbSlot K J f - mbGamma K J A f := by rw [e1]; abel
  have e4 := mbSlot_gamma_comm K K h1 h2 f
  rw [e1, mbSlot_add, e2, e4]
  nth_rewrite 2 [e3]
  rw [mbGamma_sub, ← e1]
  abel

/-!
## The two-variable commutator
-/

section TwoVar

variable (T : Matrix (Fin N) (Fin N) ℂ)

/-- `𝒟` on functions of two sites. -/
def mbD2 (h : Fin N → Fin N → ℂ) : Fin N → Fin N → ℂ :=
  fun p q => h p q - if p = q then ∑ b, h p b else 0

/-- `𝒞 = T^{(1)} + T^{(2)}` on functions of two sites. -/
def mbC2 (h : Fin N → Fin N → ℂ) : Fin N → Fin N → ℂ :=
  fun p q => ∑ a, T p a * h a q + ∑ b, T q b * h p b

/-- `G` on functions of two sites. -/
def mbG2 (h : Fin N → Fin N → ℂ) : Fin N → Fin N → ℂ :=
  fun p q => T p q * (∑ b, h q b + ∑ b, h p b)

/-- **The commutator identity on two sites**: `𝒟𝒞h = 𝒞𝒟h + 𝒟Gh` for `T` symmetric with constant row
and column sums `ρ`.
-/
theorem mbD2_C2 {ρ : ℂ} (hsym : ∀ a b, T a b = T b a) (hrow : ∀ a, ∑ b, T a b = ρ)
    (hcol : ∀ b, ∑ a, T a b = ρ) (h : Fin N → Fin N → ℂ) (p q : Fin N) :
    mbD2 (mbC2 T h) p q = mbC2 T (mbD2 h) p q + mbD2 (mbG2 T h) p q := by
  simp only [mbD2, mbC2, mbG2, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
  by_cases hpq : p = q
  · subst hpq
    simp only [ite_true, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      Finset.sum_add_distrib]
    have hc : ∑ b, ∑ c, T b c * h p c = ρ * ∑ b, h p b := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol, ← Finset.mul_sum]
    have ha : ∑ b, ∑ a, T p a * h a b = ∑ a, T p a * ∑ b, h a b := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    have hg : ∑ b, T p b * (∑ c, h b c + ∑ c, h p c) =
        ∑ a, T p a * ∑ b, h a b + ρ * ∑ b, h p b := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hrow]
    rw [hc, ha, hg]
    ring
  · simp only [hpq, ite_false, sub_zero]
    have hq : (fun a => if a = q then T p a * ∑ b, h a b else 0) =
        fun a => if q = a then T p q * ∑ b, h q b else 0 := by
      funext a
      by_cases h' : a = q
      · subst h'; simp
      · simp [h', Ne.symm h']
    have hp : (fun b => if p = b then T q b * ∑ c, h p c else 0) =
        fun b => if p = b then T q p * ∑ c, h p c else 0 := by
      funext b
      by_cases h' : p = b
      · subst h'; simp
      · simp [h']
    simp only [hq, hp, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hsym q p]
    ring

end TwoVar

/-!
## Transport to `k` sites
-/

section Transport

variable {J A : Fin k}

/-- The two-site restriction `(p, q) ↦ g(x[A ↦ p][J ↦ q])`. -/
def mbLift (J A : Fin k) (x : Fin k → Fin N) (g : (Fin k → Fin N) → ℂ) :
    Fin N → Fin N → ℂ :=
  fun p q => g (update (update x A p) J q)

theorem mbLift_self (x : Fin k → Fin N) (g : (Fin k → Fin N) → ℂ) :
    mbLift J A x g (x A) (x J) = g x := by
  simp [mbLift]

private theorem mb_upd_A (hAJ : A ≠ J) (x : Fin k → Fin N) (p q c : Fin N) :
    update (update (update x A p) J q) A c = update (update x A c) J q := by
  rw [← update_comm hAJ, update_idem, update_comm hAJ]

private theorem mb_upd_J (x : Fin k → Fin N) (p q c : Fin N) :
    update (update (update x A p) J q) J c = update (update x A p) J c := by
  rw [update_idem]

theorem mbLift_reg (hAJ : A ≠ J) (x : Fin k → Fin N) (g : (Fin k → Fin N) → ℂ) :
    mbLift J A x (mbReg J A g) = mbD2 (mbLift J A x g) := by
  funext p q
  simp only [mbLift, mbReg, mbD2, mbTr, mb_upd_J, update_self, update_of_ne hAJ]

theorem mbLift_C (T : Matrix (Fin N) (Fin N) ℂ) (hAJ : A ≠ J) (x : Fin k → Fin N)
    (g : (Fin k → Fin N) → ℂ) :
    mbLift J A x (mbSlot T A g + mbSlot T J g) = mbC2 T (mbLift J A x g) := by
  funext p q
  simp only [mbLift, mbSlot, mbC2, Pi.add_apply, mb_upd_A hAJ, mb_upd_J, update_self,
    update_of_ne hAJ]

theorem mbLift_G (T : Matrix (Fin N) (Fin N) ℂ) (hAJ : A ≠ J) (x : Fin k → Fin N)
    (g : (Fin k → Fin N) → ℂ) :
    mbLift J A x (mbG T J A g) = mbG2 T (mbLift J A x g) := by
  funext p q
  simp only [mbLift, mbG, mbG2, mbTr, mb_upd_A hAJ, mb_upd_J, update_self, update_of_ne hAJ]

/-- **Commutator with the regularizer**: for `T` symmetric with constant
row and column sums `ρ`, slots `A ≠ J`,
`𝒟^{(J)}(T^{(A)} + T^{(J)}) f = (T^{(A)} + T^{(J)}) 𝒟^{(J)} f + 𝒟^{(J)} G^{(J)} f`.
-/
theorem mbRegCommutator (T : Matrix (Fin N) (Fin N) ℂ) {ρ : ℂ} (hsym : ∀ a b, T a b = T b a)
    (hrow : ∀ a, ∑ b, T a b = ρ) (hcol : ∀ b, ∑ a, T a b = ρ) (hAJ : A ≠ J)
    (f : (Fin k → Fin N) → ℂ) :
    mbReg J A (mbSlot T A f + mbSlot T J f) =
      (mbSlot T A (mbReg J A f) + mbSlot T J (mbReg J A f)) + mbReg J A (mbG T J A f) := by
  funext x
  have h := mbD2_C2 T hsym hrow hcol (mbLift J A x f) (x A) (x J)
  rw [← mbLift_C T hAJ, ← mbLift_reg hAJ, ← mbLift_reg hAJ, ← mbLift_C T hAJ,
    ← mbLift_G T hAJ, ← mbLift_reg hAJ] at h
  simpa only [mbLift_self, Pi.add_apply] using h

end Transport

/-!
## Commutations for disjoint slots and the double commutator
-/

/-- `𝒟^{(j)}` (anchor `a`) commutes with `K^{(i)}` for `i ∉ {j, a}`. -/
theorem mbReg_slot_comm (K : Matrix (Fin N) (Fin N) ℂ) {i j a : Fin k} (hij : i ≠ j)
    (hia : i ≠ a) (f : (Fin k → Fin N) → ℂ) :
    mbReg j a (mbSlot K i f) = mbSlot K i (mbReg j a f) := by
  funext x
  simp only [mbReg, mbSlot, mbTr, mul_sub, Finset.sum_sub_distrib, update_of_ne hij.symm,
    update_of_ne hia.symm, mul_ite, mul_zero]
  congr 1
  split_ifs with h
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [update_comm hij, update_of_ne hij]
  · simp

/-- Two regularizations with disjoint pairs commute. -/
theorem mbReg_reg_comm {j a j' a' : Fin k} (h1 : j ≠ j') (h2 : j ≠ a') (h3 : a ≠ j')
    (f : (Fin k → Fin N) → ℂ) :
    mbReg j a (mbReg j' a' f) = mbReg j' a' (mbReg j a f) := by
  funext x
  simp only [mbReg, mbTr, update_of_ne h2.symm, update_of_ne h1.symm, update_of_ne h3,
    update_of_ne h1]
  have hc : ∑ b, ∑ c, f (update (update x j b) j' c) =
      ∑ c, ∑ b, f (update (update x j' c) j b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    rw [update_comm h1]
  by_cases ha : x a = x j <;> by_cases ha' : x a' = x j'
  · simp only [ha, ha', ite_true, Finset.sum_sub_distrib, hc]
    ring
  · simp only [ha, ha', ite_true, ite_false, sub_zero]
  · simp only [ha, ha', ite_true, ite_false, sub_zero]
  · simp only [ha, ha', ite_false, sub_zero]

/-- `𝒟^{(j)}` is additive over finite sums. -/
theorem mbReg_sum {ι : Type*} (s : Finset ι) (j a : Fin k) (g : ι → (Fin k → Fin N) → ℂ) :
    mbReg j a (fun x => ∑ i ∈ s, g i x) = fun x => ∑ i ∈ s, mbReg j a (g i) x := by
  funext x
  simp only [mbReg, mbTr, Finset.sum_sub_distrib]
  by_cases h : x a = x j
  · simp only [h, ite_true]
    rw [Finset.sum_comm]
  · simp only [h, ite_false, Finset.sum_const_zero]

/-- The generator split along four distinct slots. -/
theorem mbOplus_split (K : Matrix (Fin N) (Fin N) ℂ) {J A J' A' : Fin k} (h1 : A ≠ J)
    (h2 : A ≠ A') (h3 : A ≠ J') (h4 : J ≠ A') (h5 : J ≠ J') (h6 : A' ≠ J')
    (f : (Fin k → Fin N) → ℂ) :
    mbOplus K f = (mbSlot K A f + mbSlot K J f) + (mbSlot K A' f + mbSlot K J' f) +
      fun x => ∑ i ∈ Finset.univ \ {A, J, A', J'}, mbSlot K i f x := by
  funext x
  have hs : ({A, J, A', J'} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
  rw [mbOplus, ← Finset.sum_sdiff hs]
  rw [Finset.sum_insert (by simp [h1, h2, h3]), Finset.sum_insert (by simp [h4, h5]),
    Finset.sum_insert (by simp [h6]), Finset.sum_singleton]
  simp only [Pi.add_apply]
  ring

/-- **Commutator with the regularizer, double form** (used for the `Z`-equation): for `T`
symmetric with
constant row and column sums `ρ` and two disjoint slot pairs `{J, A}`, `{J', A'}` (four distinct
slots), `𝒟'𝒟 (⊕_i T^{(i)}) f = (⊕_i T^{(i)}) 𝒟'𝒟 f + 𝒟'𝒟 (G f + G' f)`.
-/
theorem mbRegCommutator_double (T : Matrix (Fin N) (Fin N) ℂ) {ρ : ℂ}
    (hsym : ∀ a b, T a b = T b a) (hrow : ∀ a, ∑ b, T a b = ρ) (hcol : ∀ b, ∑ a, T a b = ρ)
    {J A J' A' : Fin k} (h1 : A ≠ J) (h2 : A ≠ A') (h3 : A ≠ J') (h4 : J ≠ A') (h5 : J ≠ J')
    (h6 : A' ≠ J') (f : (Fin k → Fin N) → ℂ) :
    mbReg J' A' (mbReg J A (mbOplus T f)) =
      mbOplus T (mbReg J' A' (mbReg J A f)) +
        mbReg J' A' (mbReg J A (mbG T J A f + mbG T J' A' f)) := by
  set R : ((Fin k → Fin N) → ℂ) → (Fin k → Fin N) → ℂ := fun g => mbReg J' A' (mbReg J A g)
  have hRR : ∀ g, mbReg J A (mbReg J' A' g) = R g := fun g =>
    (mbReg_reg_comm h5 h4 h3 g)
  -- the pair `(A, J)`
  have hC : R (mbSlot T A f + mbSlot T J f) =
      (mbSlot T A (R f) + mbSlot T J (R f)) + R (mbG T J A f) := by
    simp only [R]
    rw [mbRegCommutator T hsym hrow hcol h1 f, mbReg_add, mbReg_add,
      mbReg_slot_comm T h3 h2, mbReg_slot_comm T h5 h4]
  -- the pair `(A', J')`
  have hC' : R (mbSlot T A' f + mbSlot T J' f) =
      (mbSlot T A' (R f) + mbSlot T J' (R f)) + R (mbG T J' A' f) := by
    rw [← hRR, mbRegCommutator T hsym hrow hcol h6 f, mbReg_add, mbReg_add,
      mbReg_slot_comm T h4.symm h2.symm, mbReg_slot_comm T h5.symm h3.symm, hRR, hRR]
  -- the other slots
  have hO : R (fun x => ∑ i ∈ Finset.univ \ {A, J, A', J'}, mbSlot T i f x) =
      fun x => ∑ i ∈ Finset.univ \ {A, J, A', J'}, mbSlot T i (R f) x := by
    simp only [R]
    rw [mbReg_sum, mbReg_sum]
    funext x
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
      true_and, not_or] at hi
    obtain ⟨hiA, hiJ, hiA', hiJ'⟩ := hi
    rw [mbReg_slot_comm T hiJ hiA, mbReg_slot_comm T hiJ' hiA']
  have hRadd : ∀ g g', R (g + g') = R g + R g' := fun g g' => by
    simp only [R, mbReg_add]
  rw [mbOplus_split T h1 h2 h3 h4 h5 h6 f, mbOplus_split T h1 h2 h3 h4 h5 h6 (R f)]
  show R _ = _ + R _
  rw [hRadd, hRadd, hC, hC', hO, hRadd]
  abel

end BlockBand.Native.ErdosRiabov.MBound
