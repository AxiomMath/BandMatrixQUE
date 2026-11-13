module

public import BlockBand.Critical.MatrixClosing.Clauses

/-!
# Vague coordinates of the collar poles: fiber formula, linearity, measurability

Deterministic; no measure.

* `ofAtoms_residue_apply`: the merged residue of `ofAtoms` at `x` is `Σ_{ℓ : x_ℓ = x} R_ℓ`.
* `atomSum_ofAtoms`: the vague coordinate `Σ_{x ∈ supp} f(x, μ({x}))` of `ofAtoms` equals
  `Σ_ℓ (#fiber ℓ)⁻¹ 1_{S_ℓ ≠ 0} f(x_ℓ, S_ℓ)`, `S_ℓ = Σ_{ℓ' : x_ℓ' = x_ℓ} R_ℓ'` (coincident atoms
  merged, zero residues dropped, exactly as in `AtomicHerglotz.atomSum`).
* `atomSumLinear`: `f ↦ F.atomSum f` is `ℝ`-linear on `C_c(ℝ × Matrix, ℝ)`; `atomSum_nonneg`.
* **`measurable_atomSum_collarFunction`**: `ω ↦ F_W(ω).atomSum f` is measurable for the collar
  function `collarFunction`, every `b, e, X, J` and `f ∈ C_c(ℝ × Matrix, ℝ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Herglotz
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexOrder

/-!
## Linearity
-/

section Linear

variable {r : ℕ}

/-- `f ↦ F.atomSum f` as an `ℝ`-linear map. -/
def atomSumLinear (F : AtomicHerglotz r) :
    CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ →ₗ[ℝ] ℝ where
  toFun f := F.atomSum f
  map_add' f g := by
    simp only [AtomicHerglotz.atomSum, CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
      Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [AtomicHerglotz.atomSum, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem atomSumLinear_apply (F : AtomicHerglotz r)
    (f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    atomSumLinear F f = F.atomSum f := rfl

theorem atomSum_nonneg (F : AtomicHerglotz r)
    {f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ}
    (hf : ∀ p, 0 ≤ f p) : 0 ≤ F.atomSum f :=
  Finset.sum_nonneg fun _ _ => hf _

end Linear

/-!
## The fiber formula for `ofAtoms`
-/

section Fiber

variable {r n : ℕ}

/-- `#{ℓ' : x_ℓ' = x_ℓ}` as a real number. -/
def fiberCard (pts : Fin n → ℝ) (ℓ : Fin n) : ℝ := ∑ ℓ', if pts ℓ' = pts ℓ then 1 else 0

/-- The merged residue `Σ_{ℓ' : x_ℓ' = x_ℓ} R_ℓ'` at the atom `x_ℓ`. -/
def fiberRes (pts : Fin n → ℝ) (res : Fin n → Matrix (Fin r) (Fin r) ℂ) (ℓ : Fin n) :
    Matrix (Fin r) (Fin r) ℂ :=
  ∑ ℓ', if pts ℓ' = pts ℓ then res ℓ' else 0

theorem ofAtoms_residue_apply (C0 : Matrix (Fin r) (Fin r) ℂ) (hC0 : C0.IsHermitian)
    (pts : Fin n → ℝ) (res : Fin n → Matrix (Fin r) (Fin r) ℂ) (hres : ∀ ℓ, (res ℓ).PosSemidef)
    (x : ℝ) :
    (ofAtoms C0 hC0 pts res hres).residue x = ∑ ℓ, if pts ℓ = x then res ℓ else 0 := by
  simp only [ofAtoms, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem fiberCard_eq (pts : Fin n → ℝ) (x : ℝ) :
    (∑ ℓ', if pts ℓ' = x then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun ℓ' => pts ℓ' = x).card : ℝ) := by
  rw [Finset.sum_boole]

/-- **Fiber formula** for the vague coordinate of `ofAtoms`. -/
theorem atomSum_ofAtoms (C0 : Matrix (Fin r) (Fin r) ℂ) (hC0 : C0.IsHermitian)
    (pts : Fin n → ℝ) (res : Fin n → Matrix (Fin r) (Fin r) ℂ) (hres : ∀ ℓ, (res ℓ).PosSemidef)
    (f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    (ofAtoms C0 hC0 pts res hres).atomSum f =
      ∑ ℓ, (fiberCard pts ℓ)⁻¹ *
        (if fiberRes pts res ℓ = 0 then 0 else f (pts ℓ, fiberRes pts res ℓ)) := by
  classical
  set F := ofAtoms C0 hC0 pts res hres
  set h : ℝ → ℝ := fun x => if F.residue x = 0 then 0 else f (x, F.residue x) with hh
  have hR : ∀ ℓ, F.residue (pts ℓ) = fiberRes pts res ℓ := fun ℓ =>
    ofAtoms_residue_apply C0 hC0 pts res hres (pts ℓ)
  have hsupp : F.residue.support ⊆ Finset.univ.image pts := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    rw [Finset.mem_image]
    by_contra hne
    push Not at hne
    apply hx
    rw [ofAtoms_residue_apply]
    exact Finset.sum_eq_zero fun ℓ _ => by simp [hne ℓ (Finset.mem_univ ℓ)]
  have h1 : F.atomSum f = ∑ x ∈ Finset.univ.image pts, h x := by
    rw [AtomicHerglotz.atomSum]
    have h0 : ∑ x ∈ F.residue.support, f (x, F.residue x) = ∑ x ∈ F.residue.support, h x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finsupp.mem_support_iff] at hx
      simp only [h, hx, ite_false]
    rw [h0]
    refine Finset.sum_subset hsupp fun x _ hx => ?_
    rw [Finsupp.notMem_support_iff] at hx
    simp only [h, hx, ite_true]
  rw [h1]
  set c : ℝ → ℝ := fun x => ∑ ℓ', if pts ℓ' = x then (1 : ℝ) else 0
  have h2 : ∑ ℓ, (c (pts ℓ))⁻¹ * h (pts ℓ) =
      ∑ x ∈ Finset.univ.image pts,
        (Finset.univ.filter fun ℓ => pts ℓ = x).card • ((c x)⁻¹ * h x) :=
    Finset.sum_comp (fun x => (c x)⁻¹ * h x) pts
  have h3 : ∑ x ∈ Finset.univ.image pts,
      (Finset.univ.filter fun ℓ => pts ℓ = x).card • ((c x)⁻¹ * h x) =
        ∑ x ∈ Finset.univ.image pts, h x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [nsmul_eq_mul]
    have hc : c x = ((Finset.univ.filter fun ℓ => pts ℓ = x).card : ℝ) := fiberCard_eq pts x
    have hpos : (Finset.univ.filter fun ℓ => pts ℓ = x).card ≠ 0 := by
      obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.card_ne_zero.2 ⟨ℓ, by simp⟩
    rw [← hc, ← mul_assoc, mul_inv_cancel₀ (by rw [hc]; exact_mod_cast hpos), one_mul]
  rw [← h3, ← h2]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [h, c, hR]
  rfl

end Fiber

/-!
## Measurability for the collar function
-/

section Collar

variable {W r : ℕ}

theorem measurable_fiberCard {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {pts : Ω → Fin n → ℝ}
    (hp : ∀ ℓ, Measurable fun ω => pts ω ℓ) (ℓ : Fin n) :
    Measurable fun ω => fiberCard (pts ω) ℓ :=
  Finset.measurable_sum _ fun ℓ' _ =>
    Measurable.ite (measurableSet_eq_fun (hp ℓ') (hp ℓ)) measurable_const measurable_const

theorem measurable_fiberRes {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {pts : Ω → Fin n → ℝ}
    {res : Ω → Fin n → Matrix (Fin r) (Fin r) ℂ} (hp : ∀ ℓ, Measurable fun ω => pts ω ℓ)
    (hr : ∀ ℓ, Measurable fun ω => res ω ℓ) (ℓ : Fin n) :
    Measurable fun ω => fiberRes (pts ω) (res ω) ℓ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [fiberRes, Matrix.sum_apply]
  refine Finset.measurable_sum _ fun ℓ' _ => ?_
  have : (fun ω => (if pts ω ℓ' = pts ω ℓ then res ω ℓ' else 0) i j) =
      fun ω => if pts ω ℓ' = pts ω ℓ then res ω ℓ' i j else 0 := by
    funext ω; split_ifs <;> rfl
  rw [this]
  exact Measurable.ite (measurableSet_eq_fun (hp ℓ') (hp ℓ)) ((hr ℓ').eval_matrix)
    measurable_const

theorem measurableSet_matrix_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {M : Ω → Matrix (Fin r) (Fin r) ℂ} (hM : Measurable M) : MeasurableSet {ω | M ω = 0} := by
  have : {ω | M ω = 0} = ⋂ i, ⋂ j, {ω | M ω i j = 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h i j => by rw [h]; rfl, fun h => Matrix.ext h⟩
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    measurableSet_eq_fun hM.eval_matrix measurable_const

open BlockBand.Coarea.FreshPalm in
/-- **Measurability of the vague coordinates of the collar poles.** -/
theorem measurable_atomSum_collarFunction (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ)
    (f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    Measurable fun ω : CollarSample W => (collarFunction b e X J ω).atomSum f := by
  set pts : CollarSample W → Fin W → ℝ :=
    fun ω ℓ => poleScale W e * freshEigenvalue (portSchurFin e X ω) ℓ
  set res : CollarSample W → Fin W → Matrix (Fin r) (Fin r) ℂ :=
    fun ω ℓ => collarResidue b e X J ω ℓ
  have hp : ∀ ℓ, Measurable fun ω => pts ω ℓ := fun ℓ =>
    measurable_const.mul ((measurable_freshEigenvalue ℓ).comp (measurable_portSchurFin e X))
  have hr : ∀ ℓ, Measurable fun ω => res ω ℓ := fun ℓ => measurable_collarResidue b e X J ℓ
  have heq : (fun ω : CollarSample W => (collarFunction b e X J ω).atomSum f) =
      fun ω => ∑ ℓ, (fiberCard (pts ω) ℓ)⁻¹ *
        (if fiberRes (pts ω) (res ω) ℓ = 0 then 0 else f (pts ω ℓ, fiberRes (pts ω) (res ω) ℓ)) := by
    funext ω
    exact atomSum_ofAtoms _ _ _ _ _ f
  rw [heq]
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  refine (measurable_fiberCard hp ℓ).inv.mul ?_
  exact Measurable.ite (measurableSet_matrix_eq_zero (measurable_fiberRes hp hr ℓ))
    measurable_const (f.continuous.measurable.comp ((hp ℓ).prodMk (measurable_fiberRes hp hr ℓ)))

end Collar

end BlockBand.Critical.MatrixClosing.Poles
