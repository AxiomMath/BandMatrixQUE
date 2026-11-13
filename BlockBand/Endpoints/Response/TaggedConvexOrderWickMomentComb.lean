module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The cycle-sum side of the complex Wick formula

Purely combinatorial; no measure. For a permutation `π` of a finite type `α`, weights
`λ : ι → R` in a commutative semiring and `p_r = Σ_i λ_i^r`:

* `wk_sum_fixed_eq_parts`: `Σ_{f : α → ι, f ∘ π = f} Π_a λ_{f a} = Π_{r ∈ parts π} p_r`, where
  `parts π = π.partition.parts` is the multiset of cycle lengths of `π` (fixed points counted as
  cycles of length `1`). A function with `f ∘ π = f` is a colouring constant on the cycles
  (`SameCycle` classes) of `π`.
* `wk_sum_perm_parts_eq`: `Σ_{π ∈ S_α} Π_{r ∈ parts π} p_r = Σ_{f : α → ι} (Π_a λ_{f a}) Π_i k_i(f)!`,
  `k_i(f) = #{a | f a = i}`: exchange the sums and count the stabiliser
  `#{π | f ∘ π = f} = Π_i k_i(f)!` (`DomMulAct.stabilizer_card`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Finset Equiv Equiv.Perm

variable {α ι R : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
  [CommSemiring R]

/-- The `SameCycle` class of `a` under `π`, as a finset. -/
def wk_cls (π : Perm α) (a : α) : Finset α := univ.filter fun b => π.SameCycle a b

theorem wk_mem_cls {π : Perm α} {a b : α} : b ∈ wk_cls π a ↔ π.SameCycle a b := by
  simp [wk_cls]

theorem wk_cls_eq_iff {π : Perm α} {a b : α} : wk_cls π a = wk_cls π b ↔ π.SameCycle a b := by
  constructor
  · intro h
    have hb : b ∈ wk_cls π a := by rw [h]; exact wk_mem_cls.2 (SameCycle.refl _ _)
    exact wk_mem_cls.1 hb
  · intro h
    ext c
    rw [wk_mem_cls, wk_mem_cls]
    exact ⟨fun hc => h.symm.trans hc, fun hc => h.trans hc⟩

theorem wk_cls_of_mem_support {π : Perm α} {a : α} (ha : a ∈ π.support) :
    wk_cls π a = (π.cycleOf a).support := by
  ext b
  rw [wk_mem_cls, mem_support_cycleOf_iff]
  exact ⟨fun h => ⟨h, ha⟩, fun h => h.1⟩

theorem wk_cls_of_not_mem_support {π : Perm α} {a : α} (ha : a ∉ π.support) :
    wk_cls π a = {a} := by
  ext b
  rw [wk_mem_cls, Finset.mem_singleton]
  have hfix : Function.IsFixedPt π a := notMem_support.1 ha
  exact ⟨fun h => (h.eq_of_left hfix).symm, fun h => h ▸ SameCycle.refl _ _⟩

omit [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] in
/-- A function invariant under `π` is constant on the `SameCycle` classes. -/
theorem wk_apply_eq_of_sameCycle {π : Perm α} {f : α → ι} (hf : f ∘ π = f) {a b : α}
    (h : π.SameCycle a b) : f a = f b := by
  have hnat : ∀ (n : ℕ) (x : α), f ((π ^ n) x) = f x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Perm.mul_apply]
      exact (congrFun hf _).trans (ih x)
  obtain ⟨i, rfl⟩ := h
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · rw [zpow_natCast]; exact (hnat n a).symm
  · rw [zpow_neg, zpow_natCast]
    have := hnat n ((π ^ n)⁻¹ a)
    simpa using this

/-- The set of cycle classes of `π`. -/
def wk_classes (π : Perm α) : Finset (Finset α) := univ.image (wk_cls π)

theorem wk_filter_cls_eq {π : Perm α} {S : Finset α} (hS : S ∈ wk_classes π) :
    (univ.filter fun a => wk_cls π a = S) = S := by
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hS
  ext a
  rw [Finset.mem_filter, wk_mem_cls, wk_cls_eq_iff]
  exact ⟨fun h => h.2.symm, fun h => ⟨Finset.mem_univ _, h.symm⟩⟩

/-- A representative of a cycle class. -/
def wk_rep (π : Perm α) (S : wk_classes π) : α := (Finset.mem_image.1 S.2).choose

theorem wk_cls_rep (π : Perm α) (S : wk_classes π) : wk_cls π (wk_rep π S) = S.1 :=
  (Finset.mem_image.1 S.2).choose_spec.2

/-- `Σ_{f ∘ π = f} Π_a λ_{f a} = Π_{S cycle class} Σ_i λ_i^{|S|}`. -/
theorem wk_sum_fixed_eq_prod_classes (π : Perm α) (lam : ι → R) :
    ∑ f ∈ (univ : Finset (α → ι)).filter (fun f => f ∘ π = f), ∏ a, lam (f a) =
      ∏ S ∈ wk_classes π, ∑ i, lam i ^ S.card := by
  classical
  rw [← Finset.prod_coe_sort, Fintype.prod_sum]
  have hmem : ∀ a, wk_cls π a ∈ wk_classes π := fun a =>
    Finset.mem_image_of_mem _ (Finset.mem_univ a)
  refine Finset.sum_bij' (fun f _ => fun S => f (wk_rep π S))
    (fun g _ => fun a => g ⟨wk_cls π a, hmem a⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro g _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    funext a
    simp only [Function.comp_apply]
    congr 2
    exact wk_cls_eq_iff.2 (sameCycle_apply_left.2 (SameCycle.refl _ _))
  · intro f hf
    have hf' := (Finset.mem_filter.1 hf).2
    funext a
    apply wk_apply_eq_of_sameCycle hf'
    have := wk_cls_rep π ⟨wk_cls π a, hmem a⟩
    exact wk_cls_eq_iff.1 this
  · intro g _
    funext S
    exact congrArg g (Subtype.ext (wk_cls_rep π S))
  · intro f hf
    have hf' := (Finset.mem_filter.1 hf).2
    have key : ∀ S : wk_classes π, ∏ a ∈ univ.filter (fun a => wk_cls π a = S.1), lam (f a) =
        lam (f (wk_rep π S)) ^ S.1.card := by
      intro S
      rw [Finset.prod_congr rfl (g := fun _ => lam (f (wk_rep π S))), Finset.prod_const,
        wk_filter_cls_eq S.2]
      intro a ha
      have ha' := (Finset.mem_filter.1 ha).2
      rw [← wk_cls_rep π S] at ha'
      exact congrArg lam (wk_apply_eq_of_sameCycle hf' (wk_cls_eq_iff.1 ha'))
    rw [← Finset.prod_fiberwise_of_maps_to (s := univ) (t := wk_classes π) (g := wk_cls π)
      (fun a _ => hmem a), ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun S _ => key S

/-- `Π_{S cycle class} q(|S|) = Π_{r ∈ parts π} q(r)`. -/
theorem wk_prod_classes_eq_parts (π : Perm α) (q : ℕ → R) :
    ∏ S ∈ wk_classes π, q S.card = (π.partition.parts.map q).prod := by
  classical
  have hC : wk_classes π =
      π.cycleFactorsFinset.image support ∪ π.supportᶜ.image (fun x => ({x} : Finset α)) := by
    ext S
    simp only [wk_classes, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_compl]
    constructor
    · rintro ⟨a, rfl⟩
      by_cases ha : a ∈ π.support
      · exact Or.inl ⟨π.cycleOf a, cycleOf_mem_cycleFactorsFinset_iff.2 ha,
          (wk_cls_of_mem_support ha).symm⟩
      · exact Or.inr ⟨a, ha, (wk_cls_of_not_mem_support ha).symm⟩
    · rintro (⟨c, hc, rfl⟩ | ⟨x, hx, rfl⟩)
      · obtain ⟨x, hx⟩ := (mem_cycleFactorsFinset_iff.1 hc).1.nonempty_support
        have hcx := cycle_is_cycleOf hx hc
        have hxs : x ∈ π.support := by
          rw [← cycleOf_mem_cycleFactorsFinset_iff, ← hcx]; exact hc
        exact ⟨x, by rw [wk_cls_of_mem_support hxs, hcx]⟩
      · exact ⟨x, wk_cls_of_not_mem_support hx⟩
  have hdisj : Disjoint (π.cycleFactorsFinset.image support)
      (π.supportᶜ.image (fun x => ({x} : Finset α))) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hS
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hS'
    have h2 := (mem_cycleFactorsFinset_iff.1 hc).1.two_le_card_support
    rw [← hx, Finset.card_singleton] at h2
    omega
  have hinj : Set.InjOn support (π.cycleFactorsFinset : Set (Perm α)) := by
    intro c hc c' hc' h
    obtain ⟨x, hx⟩ := (mem_cycleFactorsFinset_iff.1 hc).1.nonempty_support
    have hx' : x ∈ c'.support := h ▸ hx
    rw [cycle_is_cycleOf hx hc, cycle_is_cycleOf hx' hc']
  rw [hC, Finset.prod_union hdisj, Finset.prod_image hinj,
    Finset.prod_image (fun x _ y _ h => Finset.singleton_injective h)]
  simp only [Finset.card_singleton, Finset.prod_const, Finset.card_compl]
  rw [parts_partition, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
    Multiset.prod_replicate, cycleType_def, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- **Cycle expansion.** `Σ_{f ∘ π = f} Π_a λ_{f a} = Π_{r ∈ parts π} Σ_i λ_i^r`. -/
theorem wk_sum_fixed_eq_parts (π : Perm α) (lam : ι → R) :
    ∑ f ∈ (univ : Finset (α → ι)).filter (fun f => f ∘ π = f), ∏ a, lam (f a) =
      (π.partition.parts.map fun r => ∑ i, lam i ^ r).prod := by
  rw [wk_sum_fixed_eq_prod_classes, wk_prod_classes_eq_parts π (fun r => ∑ i, lam i ^ r)]

/-- The fibre size `k_i(f) = #{a | f a = i}`. -/
def wk_fib (f : α → ι) (i : ι) : ℕ := (univ.filter fun a => f a = i).card

/-- **The permutation sum as a colouring sum.**
`Σ_{π} Π_{r ∈ parts π} Σ_i λ_i^r = Σ_f (Π_a λ_{f a}) Π_i k_i(f)!`. -/
theorem wk_sum_perm_parts_eq (lam : ι → R) :
    ∑ π : Perm α, (π.partition.parts.map fun r => ∑ i, lam i ^ r).prod =
      ∑ f : α → ι, (∏ a, lam (f a)) * ((∏ i, (wk_fib f i).factorial : ℕ) : R) := by
  classical
  simp_rw [← wk_sum_fixed_eq_parts, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hc := DomMulAct.stabilizer_card f
  rw [Fintype.card_subtype] at hc
  rw [hc]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.card_subtype]
  rfl

end BlockBand.Endpoints
