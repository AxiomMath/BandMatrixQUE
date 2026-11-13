module

public import BlockBand.Transmission.Dual.GReindex
public import BlockBand.Transmission.Dual.GProduct
public import BlockBand.Transmission.Dual.GLemma1Mart

/-!
# The pair/rest layout of level `q + 1`

Deterministic. For `j : Fin (q+1)`, `slot j` sends the product layout `Fin ((1+1) + (q+q))`
(pair `(x, y)`, then the rest in `ofFlat` layout) to the `ofFlat` layout of level `q + 1`, with
the pair in the slots `(x₀, y_j)` and the rest in the slots `x ∘ succ`, `y ∘ j.succAbove` (as
`pairOf j`, `restOf j`). It is a bijection; `slotEquiv j` is its inverse. The relabelled
decoupled base coefficients are the base coefficients of level `q + 1`
(`reindexDrift_slot_base`, `reindexDiff_slot_base`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual

variable {q : ℕ}

/-- The slot map: pair to `(x₀, y_j)`, rest to `(x ∘ succ, y ∘ j.succAbove)`. -/
def slot (j : Fin (q + 1)) : Fin ((1 + 1) + (q + q)) → Fin ((q + 1) + (q + 1)) :=
  Fin.addCases (Fin.addCases (fun _ => Fin.castAdd (q + 1) 0) (fun _ => Fin.natAdd (q + 1) j))
    (Fin.addCases (fun i => Fin.castAdd (q + 1) i.succ) (fun k => Fin.natAdd (q + 1) (j.succAbove k)))

section Values

variable (j : Fin (q + 1))

@[simp] theorem slot_px (a : Fin 1) : slot j (Fin.castAdd (q + q) (Fin.castAdd 1 a)) =
    Fin.castAdd (q + 1) 0 := by simp only [slot, Fin.addCases_left]

@[simp] theorem slot_py (a : Fin 1) : slot j (Fin.castAdd (q + q) (Fin.natAdd 1 a)) =
    Fin.natAdd (q + 1) j := by simp only [slot, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem slot_rx (i : Fin q) : slot j (Fin.natAdd (1 + 1) (Fin.castAdd q i)) =
    Fin.castAdd (q + 1) i.succ := by simp only [slot, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem slot_ry (k : Fin q) : slot j (Fin.natAdd (1 + 1) (Fin.natAdd q k)) =
    Fin.natAdd (q + 1) (j.succAbove k) := by
  simp only [slot, Fin.addCases_right]

end Values

theorem castAdd_ne_natAdd' {m n : ℕ} (i : Fin m) (k : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m k := by
  intro h; have := congrArg Fin.val h; simp at this; omega

set_option linter.unusedSimpArgs false in
theorem slot_injective (j : Fin (q + 1)) : Function.Injective (slot j) := by
  intro a b h
  induction a using Fin.addCases with
  | left a => induction a using Fin.addCases with
    | left a => induction b using Fin.addCases with
      | left b => induction b using Fin.addCases with
        | left b => rw [Subsingleton.elim a b]
        | right b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h (castAdd_ne_natAdd' _ _)
      | right b => induction b using Fin.addCases with
        | left b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h.symm (Fin.succ_ne_zero _)
        | right b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h (castAdd_ne_natAdd' _ _)
    | right a => induction b using Fin.addCases with
      | left b => induction b using Fin.addCases with
        | left b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h.symm (castAdd_ne_natAdd' _ _)
        | right b => rw [Subsingleton.elim a b]
      | right b => induction b using Fin.addCases with
        | left b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h.symm (castAdd_ne_natAdd' _ _)
        | right b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h.symm (Fin.succAbove_ne j b)
  | right a => induction a using Fin.addCases with
    | left a => induction b using Fin.addCases with
      | left b => induction b using Fin.addCases with
        | left b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h (Fin.succ_ne_zero _)
        | right b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h (castAdd_ne_natAdd' _ _)
      | right b => induction b using Fin.addCases with
        | left b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; rw [h]
        | right b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h (castAdd_ne_natAdd' _ _)
    | right a => induction b using Fin.addCases with
      | left b => induction b using Fin.addCases with
        | left b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h.symm (castAdd_ne_natAdd' _ _)
        | right b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h (Fin.succAbove_ne j a)
      | right b => induction b using Fin.addCases with
        | left b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; exact absurd h.symm (castAdd_ne_natAdd' _ _)
        | right b => simp only [slot_px, slot_py, slot_rx, slot_ry, Fin.castAdd_inj, Fin.natAdd_inj,
            Fin.succ_inj, Fin.succAbove_right_inj] at h; rw [h]

theorem slot_bijective (j : Fin (q + 1)) : Function.Bijective (slot j) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨slot_injective j, ?_⟩
  simp only [Fintype.card_fin]; omega

/-- The relabelling `e` with `e.symm = slot j`: `y ↦ y ∘ e` reads a level-`q+1` vector in the
product layout. -/
def slotEquiv (j : Fin (q + 1)) : Fin ((q + 1) + (q + 1)) ≃ Fin ((1 + 1) + (q + q)) :=
  (Equiv.ofBijective (slot j) (slot_bijective j)).symm

@[simp] theorem slotEquiv_symm_apply (j : Fin (q + 1)) (s : Fin ((1 + 1) + (q + q))) :
    (slotEquiv j).symm s = slot j s := rfl

@[simp] theorem slotEquiv_slot (j : Fin (q + 1)) (s : Fin ((1 + 1) + (q + q))) :
    slotEquiv j (slot j s) = s :=
  (Equiv.ofBijective (slot j) (slot_bijective j)).symm_apply_apply s

/-- A level-`q+1` statement indexed by `Fin ((q+1)+(q+1))` follows from its values at `slot j s`. -/
theorem forall_slot (j : Fin (q + 1)) {P : Fin ((q + 1) + (q + 1)) → Prop}
    (h : ∀ s, P (slot j s)) (k : Fin ((q + 1) + (q + 1))) : P k := by
  obtain ⟨s, rfl⟩ := (slot_bijective j).2 k
  exact h s

/-!
## Coordinatewise maps and the base coefficients
-/

/-- A coordinatewise map: `f` on the `x`'s, `g` on the `y`'s. -/
def coordMap {α : Type*} (f g : ℝ → α) (q : ℕ) (w : Fin (q + q) → ℝ) : Fin (q + q) → α :=
  Fin.append (fun i => f ((ofFlat q w).1 i)) (fun j => g ((ofFlat q w).2 j))

theorem coordMap_slot {α : Type*} (f g : ℝ → α) (j : Fin (q + 1))
    (y : Fin ((q + 1) + (q + 1)) → ℝ) (s : Fin ((1 + 1) + (q + q))) :
    coordMap f g (q + 1) y (slot j s) =
      Fin.append (coordMap f g 1 (leftPart (y ∘ slot j))) (coordMap f g q (rightPart (y ∘ slot j)))
        s := by
  induction s using Fin.addCases with
  | left s => induction s using Fin.addCases with
    | left a => simp only [slot_px, coordMap, Fin.append_left, ofFlat_apply, leftPart,
        Function.comp_apply]
    | right a => simp only [slot_py, slot_px, coordMap, Fin.append_left, Fin.append_right,
        ofFlat_apply, leftPart, Function.comp_apply]
  | right s => induction s using Fin.addCases with
    | left i => simp only [slot_rx, coordMap, Fin.append_left, Fin.append_right, ofFlat_apply,
        rightPart, Function.comp_apply]
    | right k => simp only [slot_ry, coordMap, Fin.append_right, ofFlat_apply, rightPart,
        Function.comp_apply]

theorem flatBaseDrift_eq_coordMap (D0 : ℝ) (q : ℕ) :
    flatBaseDrift D0 q = coordMap (fun x => D0 / 2 * (1 + 2 * x)) (fun y => D0 / 2 * (1 - 2 * y)) q :=
  rfl

theorem flatDiffDiag_eq_coordMap (D0 : ℝ) (q : ℕ) :
    flatDiffDiag D0 q = coordMap (fun x => D0 * (x * (1 + x))) (fun y => D0 * (y * (1 - y))) q :=
  rfl

theorem reindexDrift_slot_coordMap (f g : ℝ → ℝ) (j : Fin (q + 1)) :
    reindexDrift (slotEquiv j) (prodDrift (coordMap f g 1) (coordMap f g q)) =
      coordMap f g (q + 1) := by
  funext y k
  refine forall_slot j (P := fun k => reindexDrift (slotEquiv j)
    (prodDrift (coordMap f g 1) (coordMap f g q)) y k = coordMap f g (q + 1) y k) (fun s => ?_) k
  simp only [reindexDrift, slotEquiv_slot]
  rw [coordMap_slot]
  rfl

theorem prodDiff_diagonal {d₁ d₂ : ℕ} (v₁ : (Fin d₁ → ℝ) → Fin d₁ → ℝ)
    (v₂ : (Fin d₂ → ℝ) → Fin d₂ → ℝ) :
    prodDiff (fun y => Matrix.diagonal (v₁ y)) (fun y => Matrix.diagonal (v₂ y)) =
      fun y => Matrix.diagonal (prodDrift v₁ v₂ y) := by
  funext y; ext k l
  induction k using Fin.addCases with
  | left i => induction l using Fin.addCases with
    | left l => simp [Matrix.diagonal_apply, prodDrift]
    | right l => simp [castAdd_ne_natAdd']
  | right i => induction l using Fin.addCases with
    | left l => simp [(castAdd_ne_natAdd' _ _).symm]
    | right l => simp [Matrix.diagonal_apply, prodDrift]

theorem reindexDiff_diagonal {d d' : ℕ} (e : Fin d' ≃ Fin d) (v : (Fin d → ℝ) → Fin d → ℝ) :
    reindexDiff e (fun y => Matrix.diagonal (v y)) = fun y => Matrix.diagonal (reindexDrift e v y) := by
  funext y; ext k l
  simp [reindexDiff, reindexDrift, Matrix.diagonal_apply, e.injective.eq_iff]

/-- **The relabelled decoupled base drift is the base drift of level `q + 1`.** -/
theorem reindexDrift_slot_base (D0 : ℝ) (j : Fin (q + 1)) :
    reindexDrift (slotEquiv j) (prodDrift (flatBaseDrift D0 1) (flatBaseDrift D0 q)) =
      flatBaseDrift D0 (q + 1) := by
  simp only [flatBaseDrift_eq_coordMap]
  exact reindexDrift_slot_coordMap _ _ j

/-- **The relabelled decoupled base covariance is the covariance of level `q + 1`.** -/
theorem reindexDiff_slot_base (D0 : ℝ) (j : Fin (q + 1)) :
    reindexDiff (slotEquiv j) (prodDiff (flatDiff D0 1) (flatDiff D0 q)) = flatDiff D0 (q + 1) := by
  have e : ∀ q, flatDiff D0 q = fun y => Matrix.diagonal (flatDiffDiag D0 q y) := fun _ => rfl
  rw [e 1, e q, e (q + 1), prodDiff_diagonal, reindexDiff_diagonal]
  simp only [flatDiffDiag_eq_coordMap]
  rw [reindexDrift_slot_coordMap]

/-!
## The open orthant `O_q = (0,∞)^q × (0,1)^q`
-/

/-- The coordinate sets: `(0, ∞)` for the `x`'s, `(0, 1)` for the `y`'s. -/
def slotSet (q : ℕ) : Fin (q + q) → Set ℝ := coordMap (fun _ => Ioi 0) (fun _ => Ioo 0 1) q 0

/-- The flat orthant `O_q`. -/
def flatO (q : ℕ) : Set (Fin (q + q) → ℝ) := {w | ∀ k, w k ∈ slotSet q k}

theorem slotSet_slot (j : Fin (q + 1)) (s : Fin ((1 + 1) + (q + q))) :
    slotSet (q + 1) (slot j s) = Fin.append (slotSet 1) (slotSet q) s :=
  coordMap_slot _ _ j 0 s

theorem leftPart_mem_flatO {z : Fin ((q + 1) + (q + 1)) → ℝ} (hz : z ∈ flatO (q + 1))
    (j : Fin (q + 1)) : leftPart (z ∘ slot j) ∈ flatO 1 := fun i => by
  have := hz (slot j (Fin.castAdd (q + q) i))
  rwa [slotSet_slot, Fin.append_left] at this

theorem rightPart_mem_flatO {z : Fin ((q + 1) + (q + 1)) → ℝ} (hz : z ∈ flatO (q + 1))
    (j : Fin (q + 1)) : rightPart (z ∘ slot j) ∈ flatO q := fun i => by
  have := hz (slot j (Fin.natAdd (1 + 1) i))
  rwa [slotSet_slot, Fin.append_right] at this

theorem append_comp_mem_flatO {p : Fin (1 + 1) → ℝ} {r : Fin (q + q) → ℝ} (hp : p ∈ flatO 1)
    (hr : r ∈ flatO q) (j : Fin (q + 1)) : Fin.append p r ∘ slotEquiv j ∈ flatO (q + 1) := by
  intro k
  refine forall_slot j (P := fun k => (Fin.append p r ∘ slotEquiv j) k ∈ slotSet (q + 1) k)
    (fun s => ?_) k
  simp only [Function.comp_apply, slotEquiv_slot, slotSet_slot]
  induction s using Fin.addCases with
  | left i => simpa using hp i
  | right i => simpa using hr i

theorem append_slot_comp (j : Fin (q + 1)) (z : Fin ((q + 1) + (q + 1)) → ℝ) :
    Fin.append (leftPart (z ∘ slot j)) (rightPart (z ∘ slot j)) ∘ slotEquiv j = z := by
  rw [show Fin.append (leftPart (z ∘ slot j)) (rightPart (z ∘ slot j)) = z ∘ slot j from
    Fin.append_castAdd_natAdd]
  funext k
  simp only [Function.comp_apply, ← slotEquiv_symm_apply, Equiv.symm_apply_apply]

theorem flatChamber_subset_flatO (q : ℕ) : flatChamber q ⊆ flatO q := by
  intro w hw k
  induction k using Fin.addCases with
  | left i =>
    simp only [slotSet, coordMap, Fin.append_left]
    exact hw.2.2.1 i
  | right j =>
    simp only [slotSet, coordMap, Fin.append_right]
    exact hw.2.2.2 j

end BlockBand.Transmission.Dual.G
