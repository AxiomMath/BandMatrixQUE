module

public import BlockBand.Endpoints.Poisson.SameVolumeStage

/-!
# Same-volume comparison: the empty-stage matrices are `H^ring` and `H^boxes`

Fix box block numbers `nb i ≥ 4` with `Σ nb i = n`. The collar layout is `L i = nb i - 3`
(`svLayout`): unit `i` (collar `i` followed by path `i`) has exactly `nb i` blocks, starting at
`unitOffset`. With base block `0`:

* `sv_stageHerm_cyclic_empty` (proved in the sibling module): the cyclic pairing at the empty stage is the
  ring matrix `H^ring = ringMatrix ω`;
* `sv_directSum_eq`: the box pairing at the empty stage is, after the block relabelling `svSiteEquiv`,
  the direct sum `⊕ᵢ H_i` of the box rings `H_i = ringMatrix (svBoxCoords nb i ω)`, where box `i`
  uses exactly the Gaussian coordinates of unit `i` (its own last bond closes it);
* `sv_hasLaw_boxCoords`: under the original prior `ringCoordLaw n W b`, the box coordinates are
  independent with the box priors `ringCoordLaw (nb i) W b`;
* `sv_card_compl_ringCore_le`, `sv_card_compl_boxCore_le`: the complement of the core `C = InSource`
  (collars and buffers) has at
  most `m (3 + 2 buf)` blocks, on both sides.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.InputsRing (ringParameters toBlockCoords directSumBlockCoords
  siteBlockEquiv)
open BlockBand.Internal.Contracts.Inputs (blockProjector)

section Boxes

variable {m n W : ℕ} (nb : Fin m → ℕ)

/-- The collar layout of the boxes: unit `i` has `nb i` blocks (`3` collar blocks and a path of
`nb i - 3` blocks). -/
def svLayout : Fin m → ℕ := fun i => nb i - 3

variable {nb}

theorem sv_layout_add (hnb : ∀ i, 4 ≤ nb i) (i : Fin m) : svLayout nb i + 3 = nb i := by
  have := hnb i; unfold svLayout; omega

theorem sv_isCollarLayout (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n) :
    IsCollarLayout n (svLayout nb) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [← hsum]; exact Finset.sum_congr rfl fun i _ => sv_layout_add hnb i
  · have := hnb i; unfold svLayout; omega

/-!
### Box coordinates and their law
-/

variable (nb) in
/-- The Gaussian coordinates of box `i`: those of unit `i`, block `q` of the box being block
`unitPos i q` of the ring. -/
def svBoxCoords (i : Fin m) (ω : RingCoords n W) : RingCoords (nb i) W :=
  (fun q => ω.1 (unitPos n (svLayout nb) 0 i q.val),
    fun q => ω.2 (unitPos n (svLayout nb) 0 i q.val))

variable (nb) in
/-- The coordinate index map of all boxes into the ring coordinates. -/
def svBoxIdx : (Σ i : Fin m, ZMod (nb i) ⊕ ZMod (nb i)) → ZMod n ⊕ ZMod n
  | ⟨i, Sum.inl q⟩ => Sum.inl (unitPos n (svLayout nb) 0 i q.val)
  | ⟨i, Sum.inr q⟩ => Sum.inr (unitPos n (svLayout nb) 0 i q.val)

theorem sv_boxIdx_injective (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n) :
    Function.Injective (svBoxIdx (n := n) nb) := by
  have hL := sv_isCollarLayout hnb hsum
  have : ∀ i, NeZero (nb i) := fun i => ⟨by have := hnb i; omega⟩
  have hv : ∀ i (q : ZMod (nb i)), q.val < svLayout nb i + 3 := fun i q => by
    rw [sv_layout_add hnb]; exact ZMod.val_lt q
  rintro ⟨i, q | q⟩ ⟨i', q' | q'⟩ h <;>
    simp only [svBoxIdx, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, hq⟩ := (unitPos_inj hL 0 (hv i q) (hv i' q')).mp h
    rw [ZMod.val_injective _ hq]
  · obtain ⟨rfl, hq⟩ := (unitPos_inj hL 0 (hv i q) (hv i' q')).mp h
    rw [ZMod.val_injective _ hq]

/-- **The box coordinates are independent with the box priors**: the boxes are built from
disjoint sets of the original Gaussian variables. -/
theorem sv_hasLaw_boxCoords [NeZero n] (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n) (b : ℝ) :
    haveI : ∀ i, NeZero (nb i) := fun i => ⟨by have := hnb i; omega⟩
    HasLaw (fun ω : RingCoords n W => fun i => svBoxCoords nb i ω)
      (Measure.pi fun i => ringCoordLaw (nb i) W b) (ringCoordLaw n W b) := by
  have : ∀ i, NeZero (nb i) := fun i => ⟨by have := hnb i; omega⟩
  obtain ⟨hI, hm⟩ := iIndepFun_ringCoord (n := n) (W := W) b
  have hI' := hI.precomp (sv_boxIdx_injective hnb hsum)
  have hv : HasLaw (fun ω p => ringCoord (W := W) (svBoxIdx nb p) ω)
      (Measure.pi fun p => ringCoordMarginal W b (svBoxIdx (n := n) nb p))
      (ringCoordLaw n W b) :=
    hI'.hasLaw_pi fun p => hm _
  have hmarg : (fun p => ringCoordMarginal W b (svBoxIdx (n := n) nb p)) =
      fun p : (Σ i : Fin m, ZMod (nb i) ⊕ ZMod (nb i)) =>
        ringCoordMarginal (n := nb p.1) W b p.2 := by
    funext p; rcases p with ⟨i, q | q⟩ <;> rfl
  rw [hmarg] at hv
  have hcurry : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (i : Fin m) (_ : ZMod (nb i) ⊕ ZMod (nb i)) =>
        Matrix (Fin W) (Fin W) ℂ))
      (Measure.pi fun p : (Σ i : Fin m, ZMod (nb i) ⊕ ZMod (nb i)) =>
        ringCoordMarginal (n := nb p.1) W b p.2)
      (Measure.pi fun i => Measure.pi fun t => ringCoordMarginal (n := nb i) W b t) := by
    refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
    have := Measure.infinitePi_map_piCurry
      (fun (i : Fin m) (t : ZMod (nb i) ⊕ ZMod (nb i)) => ringCoordMarginal (n := nb i) W b t)
    rw [Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi] at this
    simp_rw [Measure.infinitePi_eq_pi] at this
    exact this
  have hbox : MeasurePreserving
      (fun (a : ∀ i, (ZMod (nb i) ⊕ ZMod (nb i)) → Matrix (Fin W) (Fin W) ℂ) i =>
        MeasurableEquiv.sumPiEquivProdPi (fun _ : ZMod (nb i) ⊕ ZMod (nb i) =>
          Matrix (Fin W) (Fin W) ℂ) (a i))
      (Measure.pi fun i => Measure.pi fun t => ringCoordMarginal (n := nb i) W b t)
      (Measure.pi fun i => ringCoordLaw (nb i) W b) :=
    measurePreserving_pi _ _ fun i =>
      measurePreserving_sumPiEquivProdPi (fun t => ringCoordMarginal (n := nb i) W b t)
  exact (hbox.comp hcurry).comp_hasLaw hv

/-!
### The box pairing at the empty stage is the direct sum of the box rings
-/

theorem sv_succ_mod {o N : ℕ} (ho : o < N) :
    ((o + 1) % N = o + 1 ∧ o + 1 < N) ∨ ((o + 1) % N = 0 ∧ o + 1 = N) := by
  rcases Nat.lt_or_ge (o + 1) N with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have h' : o + 1 = N := by omega
    exact Or.inr ⟨by rw [h', Nat.mod_self], h'⟩

/-- In the box pairing, the bond of block `o` of unit `i` goes to block `(o + 1) mod nb i` of the
same unit. -/
theorem sv_bondTarget_box (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n) (i : Fin m) {o : ℕ}
    (ho : o < nb i) :
    bondTarget (svLayout nb) (0 : ZMod n) .box (unitPos n (svLayout nb) 0 i o) =
      unitPos n (svLayout nb) 0 i ((o + 1) % nb i) := by
  have hL := sv_isCollarLayout hnb hsum
  have hLi := sv_layout_add hnb i
  by_cases he : o = svLayout nb i + 2
  · have hpe : unitPos n (svLayout nb) 0 i o = pathEnd (svLayout nb) 0 i := by
      rw [he]; rfl
    rw [hpe, bondTarget_box_pathEnd hL]
    have : (o + 1) % nb i = 0 := by rw [show o + 1 = nb i by omega, Nat.mod_self]
    rw [this]
  · have hne : ∀ k, unitPos n (svLayout nb) 0 i o ≠ pathEnd (svLayout nb) 0 k := by
      intro k h
      have hk := hL.2 k
      have := (unitPos_inj hL 0 (by omega) (by omega)).mp h
      obtain ⟨rfl, h2⟩ := this
      exact he h2
    rw [bondTarget_of_ne .box hne, unitPos_succ]
    rw [Nat.mod_eq_of_lt (by omega)]

/-- The block position of a direct-sum block `a`: block `u.2` of unit `u.1`,
`u = finSigmaFinEquiv.symm a`. -/
def svBlockPos (a : Fin (∑ i, nb i)) : ZMod n :=
  unitPos n (svLayout nb) 0 (finSigmaFinEquiv.symm a).1 (finSigmaFinEquiv.symm a).2.val

theorem sv_blockPos_bijective [NeZero n] (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n) :
    Function.Bijective (svBlockPos (n := n) (nb := nb)) := by
  have hL := sv_isCollarLayout hnb hsum
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a a' h => ?_, by simp [hsum]⟩
  unfold svBlockPos at h
  have hv : ∀ u : (Σ i : Fin m, Fin (nb i)), u.2.val < svLayout nb u.1 + 3 := fun u => by
    rw [sv_layout_add hnb]; exact u.2.isLt
  obtain ⟨h1, h2⟩ := (unitPos_inj hL 0 (hv _) (hv _)).mp h
  apply finSigmaFinEquiv.symm.injective
  rcases hu : finSigmaFinEquiv.symm a with ⟨i, o⟩
  rcases hu' : finSigmaFinEquiv.symm a' with ⟨i', o'⟩
  rw [hu, hu'] at h1 h2
  simp only at h1 h2
  subst h1
  rw [Fin.ext h2]

/-- The site relabelling `Fin (Σ nb) × Fin W ≃ ZMod n × Fin W`. -/
def svSiteEquiv [NeZero n] (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n) :
    Fin (∑ i, nb i) × Fin W ≃ RingSite n W :=
  (Equiv.ofBijective _ (sv_blockPos_bijective (n := n) hnb hsum)).prodCongr (Equiv.refl _)

theorem sv_val_finEquiv {N : ℕ} [NeZero N] (q : Fin N) : (ZMod.finEquiv N q).val = q.val := by
  rcases N with _ | N
  · exact absurd rfl (NeZero.ne 0)
  · rfl

theorem sv_ite_three {α : Type*} [AddMonoid α] {P Q R : Prop} [Decidable P] [Decidable Q]
    [Decidable R] (hPQ : P → ¬ Q) (hPR : P → ¬ R) (hQR : Q → ¬ R) (a b c : α) :
    (if P then a else if Q then b else if R then c else 0) =
      (if P then a else 0) + (if Q then b else 0) + (if R then c else 0) := by
  by_cases hP : P
  · simp [hP, hPQ hP, hPR hP]
  · by_cases hQ : Q
    · simp [hP, hQ, hQR hQ]
    · by_cases hR : R <;> simp [hP, hQ, hR]

/-- Entries of a box ring in block coordinates, as conditions on block indices. -/
theorem sv_box_entry (hnb : ∀ i, 4 ≤ nb i) (b : ℝ) (hW : 0 < W) (hb : 0 < b) (hb' : b < 1 / 2)
    (ω : RingCoords n W) (i : Fin m) (o o' : Fin (nb i)) (α β : Fin W) :
    toBlockCoords (ringParameters (nb i) W b (hnb i) hW hb hb') (ringMatrix (svBoxCoords nb i ω))
        (o, α) (o', β) =
      (if o.val = o'.val then ω.1 (unitPos n (svLayout nb) 0 i o.val) α β else 0) +
      (if o'.val = (o.val + 1) % nb i then ω.2 (unitPos n (svLayout nb) 0 i o.val) α β else 0) +
      (if o.val = (o'.val + 1) % nb i then
        star (ω.2 (unitPos n (svLayout nb) 0 i o'.val) β α) else 0) := by
  have : NeZero (nb i) := ⟨by have := hnb i; omega⟩
  have hN := hnb i
  have hfe : ∀ q : Fin (nb i), ((siteBlockEquiv
      (ringParameters (nb i) W b (hnb i) hW hb hb')).symm (q, α)).1 = ZMod.finEquiv (nb i) q :=
    fun q => rfl
  simp only [toBlockCoords, Matrix.submatrix_apply]
  set q := ZMod.finEquiv (nb i) o with hq
  set q' := ZMod.finEquiv (nb i) o' with hq'
  have hqv : q.val = o.val := sv_val_finEquiv o
  have hqv' : q'.val = o'.val := sv_val_finEquiv o'
  have hsucc : ∀ (r r' : Fin (nb i)), ZMod.finEquiv (nb i) r' = ZMod.finEquiv (nb i) r + 1 ↔
      r'.val = (r.val + 1) % nb i := by
    intro r r'
    rw [← map_one (ZMod.finEquiv (nb i)), ← map_add, (ZMod.finEquiv (nb i)).injective.eq_iff,
      Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (a := 1) (by omega)]
  change (if q = q' then ω.1 (unitPos n (svLayout nb) 0 i q.val) α β
      else if q' = q + 1 then ω.2 (unitPos n (svLayout nb) 0 i q.val) α β
      else if q = q' + 1 then star (ω.2 (unitPos n (svLayout nb) 0 i q'.val) β α) else 0) = _
  have e1 : q = q' ↔ o.val = o'.val := by
    rw [hq, hq', (ZMod.finEquiv (nb i)).injective.eq_iff, Fin.ext_iff]
  have e2 : q' = q + 1 ↔ o'.val = (o.val + 1) % nb i := hsucc o o'
  have e3 : q = q' + 1 ↔ o.val = (o'.val + 1) % nb i := hsucc o' o
  rw [hqv, hqv']
  have ho := o.isLt
  have ho' := o'.isLt
  rw [sv_ite_three (P := q = q') (Q := q' = q + 1) (R := q = q' + 1)]
  · simp only [e1, e2, e3]
  · intro h1 h2; rw [e1] at h1; rw [e2] at h2
    rcases sv_succ_mod ho with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · intro h1 h2; rw [e1] at h1; rw [e3] at h2
    rcases sv_succ_mod ho' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · intro h1 h2; rw [e2] at h1; rw [e3] at h2
    rcases sv_succ_mod ho with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases sv_succ_mod ho' with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> omega

/-- Entries of the box pairing at the empty stage at two unit positions. -/
theorem sv_stageHerm_box_entry (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n)
    (ω : RingCoords n W) (i i' : Fin m) (o : Fin (nb i)) (o' : Fin (nb i')) (α β : Fin W) :
    stageHerm (svLayout nb) (0 : ZMod n) .box ∅ 0 0 ω
        (unitPos n (svLayout nb) 0 i o.val, α) (unitPos n (svLayout nb) 0 i' o'.val, β) =
      (if i = i' ∧ o.val = o'.val then ω.1 (unitPos n (svLayout nb) 0 i o.val) α β else 0) +
      (if i = i' ∧ o'.val = (o.val + 1) % nb i then
        ω.2 (unitPos n (svLayout nb) 0 i o.val) α β else 0) +
      (if i' = i ∧ o.val = (o'.val + 1) % nb i' then
        star (ω.2 (unitPos n (svLayout nb) 0 i' o'.val) β α) else 0) := by
  have hL := sv_isCollarLayout hnb hsum
  have hv : ∀ j (r : ℕ), r < nb j → r < svLayout nb j + 3 := fun j r h => by
    rw [sv_layout_add hnb]; exact h
  have hM := sv_not_isMatched_empty (svLayout nb) (0 : ZMod n)
  simp only [stageHerm, hM, ite_false, Complex.ofReal_zero, ite_self, sub_zero]
  rw [sv_bondTarget_box hnb hsum i o.isLt, sv_bondTarget_box hnb hsum i' o'.isLt]
  have c1 := unitPos_inj hL (0 : ZMod n) (hv i _ o.isLt) (hv i' _ o'.isLt)
  have c2 := unitPos_inj hL (0 : ZMod n)
    (hv i ((o.val + 1) % nb i) (Nat.mod_lt _ (by have := hnb i; omega))) (hv i' _ o'.isLt)
  have c3 := unitPos_inj hL (0 : ZMod n)
    (hv i' ((o'.val + 1) % nb i') (Nat.mod_lt _ (by have := hnb i'; omega))) (hv i _ o.isLt)
  simp only [c1, c2, c3, @eq_comm ℕ ((o.val + 1) % nb i), @eq_comm ℕ ((o'.val + 1) % nb i')]

/-- **The box pairing at the empty stage is the direct sum of the box rings**, after the block
relabelling `svSiteEquiv`. -/
theorem sv_directSum_eq [NeZero n] (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n) (b : ℝ)
    (hW : 0 < W) (hb : 0 < b) (hb' : b < 1 / 2) (ω : RingCoords n W) :
    directSumBlockCoords nb (fun i => toBlockCoords (ringParameters (nb i) W b (hnb i) hW hb hb')
        (ringMatrix (svBoxCoords nb i ω))) =
      (stageHerm (svLayout nb) (0 : ZMod n) .box ∅ 0 0 ω).submatrix (svSiteEquiv hnb hsum)
        (svSiteEquiv hnb hsum) := by
  ext ⟨a, α⟩ ⟨a', β⟩
  simp only [Matrix.submatrix_apply, svSiteEquiv, Equiv.prodCongr_apply, Prod.map,
    Equiv.ofBijective_apply, Equiv.refl_apply, svBlockPos]
  rw [sv_stageHerm_box_entry hnb hsum ω (finSigmaFinEquiv.symm a).1 (finSigmaFinEquiv.symm a').1
    (finSigmaFinEquiv.symm a).2 (finSigmaFinEquiv.symm a').2]
  simp only [directSumBlockCoords]
  by_cases hi : (finSigmaFinEquiv.symm a).1 = (finSigmaFinEquiv.symm a').1
  · simp only [eq_true hi, dite_true]
    refine (sv_box_entry hnb b hW hb hb' ω _ _ _ α β).trans ?_
    have hnbe : nb (finSigmaFinEquiv.symm a').1 = nb (finSigmaFinEquiv.symm a).1 := by rw [hi]
    have hup : ∀ r, unitPos n (svLayout nb) 0 (finSigmaFinEquiv.symm a').1 r =
        unitPos n (svLayout nb) 0 (finSigmaFinEquiv.symm a).1 r := fun r => by rw [hi]
    simp only [eq_true hi.symm, true_and, Fin.val_cast, hnbe, hup]
  · simp only [eq_false hi, dite_false]
    have hi' : ¬ (finSigmaFinEquiv.symm a').1 = (finSigmaFinEquiv.symm a).1 := fun h => hi h.symm
    simp only [eq_false hi', false_and, ite_false, add_zero]

/-!
### The cores
-/

open Classical in
/-- The ring core `C = InSource` (every path block outside the buffers). -/
def svRingCore [NeZero n] (buf : ℕ) : Finset (ZMod n) :=
  Finset.univ.filter fun p => InSource (svLayout nb) (0 : ZMod n) buf p

open Classical in
/-- The box core: the preimage of the ring core under the block relabelling. -/
def svBoxCore (buf : ℕ) : Finset (Fin (∑ i, nb i)) :=
  Finset.univ.filter fun a => InSource (svLayout nb) (0 : ZMod n) buf (svBlockPos a)

theorem sv_physicalBlockProjector_eq (p : Parameters) (buf : ℕ) :
    physicalBlockProjector p (svRingCore (nb := nb) (n := p.n) buf) =
      svSourceProj (n := p.n) (W := p.W) (svLayout nb) 0 buf := by
  unfold physicalBlockProjector svSourceProj svRingCore
  congr 1
  funext x
  by_cases h : InSource (svLayout nb) (0 : ZMod p.n) buf x.1 <;> simp [h]

theorem sv_blockProjector_eq [NeZero n] (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n)
    (buf : ℕ) :
    (blockProjector (W := W) (svBoxCore (nb := nb) (n := n) buf)) =
      (svSourceProj (W := W) (svLayout nb) (0 : ZMod n) buf).submatrix (svSiteEquiv hnb hsum)
        (svSiteEquiv hnb hsum) := by
  unfold blockProjector svSourceProj
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  by_cases h : InSource (svLayout nb) (0 : ZMod n) buf (svBlockPos x.1) <;>
    simp [svBoxCore, h, svSiteEquiv]

/-- Every block outside the core is among the `3 + 2 buf` first or last blocks of its unit. -/
theorem sv_card_compl_ringCore_le [NeZero n] (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n)
    (buf : ℕ) : ((svRingCore (nb := nb) (n := n) buf)ᶜ).card ≤ m * (3 + 2 * buf) := by
  classical
  have hbij := sv_blockPos_bijective (n := n) hnb hsum
  let g : Fin m × Fin (3 + 2 * buf) → ZMod n := fun t =>
    if t.2.val < 3 + buf then unitPos n (svLayout nb) 0 t.1 t.2.val
    else unitPos n (svLayout nb) 0 t.1 (nb t.1 - 1 - (t.2.val - (3 + buf)))
  have hsub : (svRingCore (nb := nb) (n := n) buf)ᶜ ⊆ Finset.univ.image g := by
    intro p hp
    simp only [svRingCore, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨a, rfl⟩ := hbij.2 p
    set i := (finSigmaFinEquiv.symm a).1
    set o := (finSigmaFinEquiv.symm a).2.val
    have ho : o < nb i := (finSigmaFinEquiv.symm a).2.isLt
    have hLi := sv_layout_add hnb i
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_cases h1 : o < 3 + buf
    · exact ⟨(i, ⟨o, by omega⟩), by simp only [g, h1, ite_true]; rfl⟩
    · by_cases h2 : nb i - buf ≤ o
      · refine ⟨(i, ⟨3 + buf + (nb i - 1 - o), by omega⟩), ?_⟩
        have h3 : ¬ (3 + buf + (nb i - 1 - o) < 3 + buf) := by omega
        simp only [g, h3, ite_false]
        have : nb i - 1 - (3 + buf + (nb i - 1 - o) - (3 + buf)) = o := by omega
        rw [this]; rfl
      · exfalso
        apply hp
        refine ⟨i, o - 3, by omega, ?_, ?_⟩
        · unfold svLayout; omega
        · unfold svBlockPos; congr 1; omega
  calc ((svRingCore (nb := nb) (n := n) buf)ᶜ).card ≤ (Finset.univ.image g).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin m × Fin (3 + 2 * buf))).card := Finset.card_image_le
    _ = m * (3 + 2 * buf) := by simp

theorem sv_card_compl_boxCore_le [NeZero n] (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = n)
    (buf : ℕ) : ((svBoxCore (nb := nb) (n := n) buf)ᶜ).card ≤ m * (3 + 2 * buf) := by
  classical
  have hbij := sv_blockPos_bijective (n := n) hnb hsum
  refine le_trans ?_ (sv_card_compl_ringCore_le (n := n) hnb hsum buf)
  refine Finset.card_le_card_of_injOn svBlockPos (fun a ha => ?_) (fun a _ a' _ h => hbij.1 h)
  simp only [svBoxCore, svRingCore, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha

end Boxes

end BlockBand.Endpoints
