module

public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateAlgebra

/-!
# Item (ii): the old response through the incident components

Item (ii) of the sequential collars lemma, Step 3 of its proof: "we remove the selected collar
when we form its old response, and we temporarily expose all the remaining matched ports".
* `outerResolvent_eq`: `(z - X_κ)⁻¹` is the outer block of `(H^after_κ)⁻¹`.
* `runComp_decoupled`, `runComp_block`, `runComp_resolvent`: an incident run whose two ends are
  matched ports in `H^after` is a decoupled component equal to the two-port path with matched
  leads; its port block of `(H^after)⁻¹` is `(z - pathSchur e ps)⁻¹`.
* `pathMatrix_isHermitian`, `pathSchur_isHermitian`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (PathSample pathMatrix pathPortCoupling pathSchur
  pathPortResolvent boundaryZ)

section Outer

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

/-- The two outer coordinates of the selected collar as sites of `H^after`. -/
def outerStageSite (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S)
    (i : Fin 2 × Fin W) : StageSite L s (insert k S) W :=
  (afterEquiv hL hk).symm (Sum.inr i)

theorem outerStageSite_val (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (i : Fin 2 × Fin W) :
    (outerStageSite (s := s) hL hk i).1 = outerSite L s k i := rfl

/-- **The old response from `H^after`**: `(z - X_κ)⁻¹` is the outer block of `(H^after_κ)⁻¹`,
and `H^after_κ` is invertible, whenever `M_κ` and `z - X_κ` are. -/
theorem outerResolvent_eq [NeZero n] (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (π : Pairing) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W)
    (hM : IsUnit (oldInterior L s π S k e z buf κ ω).det)
    (hX : IsUnit (z • 1 - oldSchur (oldInterior L s π S k e z buf κ ω)
      (oldCoupling L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)ᴴ).det) :
    (z • 1 - oldSchur (oldInterior L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)
        (oldCoupling L s π S k e z buf κ ω)ᴴ)⁻¹ =
      ((stageMatrix L s π (insert k S) e z buf κ ω)⁻¹).submatrix (outerStageSite hL hk)
        (outerStageSite hL hk) ∧
    IsUnit (stageMatrix L s π (insert k S) e z buf κ ω).det := by
  set N := stageMatrix L s π (insert k S) e z buf κ ω
  have hre := stageMatrix_after_reindex (s := s) hL hk π e z buf κ ω
  have hdet : IsUnit N.det := by
    rw [← det_submatrix_equiv_self (afterEquiv hL hk).symm, hre, det_collarAfter _ _ _ _ hM]
    exact hM.mul hX
  refine ⟨?_, hdet⟩
  have hinv := congrArg Inv.inv hre
  rw [inv_submatrix_equiv] at hinv
  have h22 := inv_fromBlocks_toBlocks₂₂ (oldInterior L s π S k e z buf κ ω)
    (oldCoupling L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)ᴴ (z • 1) hM hX
  unfold collarAfter at hinv
  rw [← hinv] at h22
  rw [show z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      oldSchur (oldInterior L s π S k e z buf κ ω) (oldCoupling L s π S k e z buf κ ω)
        (oldCoupling L s π S k e z buf κ ω)ᴴ = z • 1 - (oldCoupling L s π S k e z buf κ ω)ᴴ *
          (oldInterior L s π S k e z buf κ ω)⁻¹ * oldCoupling L s π S k e z buf κ ω from rfl,
    ← h22]
  ext i j
  rfl

end Outer

section Component

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

variable (L s) in
/-- Block positions of the component of a run: the run and its two end ports. -/
def InRunComp (π : Pairing) (p₀ : ZMod n) (r : ℕ) (x : RingSite n W) : Prop :=
  (∃ i < r, x.1 = p₀ + (i : ℕ)) ∨ x.1 = p₀ - 1 ∨ x.1 = runRight L s π p₀ r

theorem p₀_eq_of_left {p₀ : ZMod n} {j : Fin m}
    (h : p₀ - 1 = unitPos n L s j 2) : p₀ = unitPos n L s j 3 := by
  rw [← unitPos_succ, ← h]; ring

/-- The component of a run whose two ends are matched ports is decoupled in `H^after` (in fact
in the stage matrix at `insert k S`, for every `κ`). -/
theorem runComp_decoupled (hL : IsCollarLayout n L) {π : Pairing} {S : Finset (Fin m)}
    {k : Fin m} {p₀ : ZMod n} {r : ℕ} (h : IsOldRun L s π S k p₀ r) {j₁ j₂ : Fin m}
    (hj₁ : j₁ ∈ insert k S) (hl : p₀ - 1 = unitPos n L s j₁ 2) (hj₂ : j₂ ∈ insert k S)
    (hr : runRight L s π p₀ r = unitPos n L s j₂ 0) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) (x y : RingSite n W) (hy : ¬ IsDeleted L s (insert k S) y.1)
    (hx : InRunComp L s π p₀ r x) (hny : ¬ InRunComp L s π p₀ r y) :
    stageFull L s π (insert k S) e z buf κ ω x y = 0 ∧
      stageFull L s π (insert k S) e z buf κ ω y x = 0 := by
  have hy1 : ∀ i < r, y.1 ≠ p₀ + (i : ℕ) := fun i hi he => hny (Or.inl ⟨i, hi, he⟩)
  have hy2 : y.1 ≠ p₀ - 1 := fun he => hny (Or.inr (Or.inl he))
  have hy3 : y.1 ≠ runRight L s π p₀ r := fun he => hny (Or.inr (Or.inr he))
  rcases hx with ⟨i, hi, hxi⟩ | hxl | hxr
  · have hd := h.decoupled e z buf κ ω (⟨i, hi⟩, x.2) y hy1 hy2 hy3
    have hxe : runSite p₀ (W := W) (⟨i, hi⟩, x.2) = x := Prod.ext hxi.symm rfl
    rw [hxe] at hd
    have hne : x.1 ≠ y.1 := fun he => hy1 i hi (he ▸ hxi)
    rw [stageFull_insert_eq π S k e z buf κ ω (Or.inl hne),
      stageFull_insert_eq π S k e z buf κ ω (Or.inl (Ne.symm hne))]
    exact hd
  · have hxe : x = outerSite L s j₁ (1, x.2) := Prod.ext (hxl.trans hl) rfl
    rw [hxe]
    refine (matched_port hL π hj₁ e z buf κ ω).2 (1, x.2) y hy ?_ ?_
    · intro he; exact hy2 (he.trans hl.symm)
    · intro he
      apply hy1 0 h.one_le
      rw [Nat.cast_zero, add_zero, p₀_eq_of_left hl]
      exact he
  · have hxe : x = outerSite L s j₂ (0, x.2) := Prod.ext (hxr.trans hr) rfl
    rw [hxe]
    refine (matched_port hL π hj₂ e z buf κ ω).2 (0, x.2) y hy ?_ ?_
    · intro he; exact hy3 (he.trans hr.symm)
    · intro he
      apply hy1 (r - 1) (by have := h.one_le; omega)
      rw [he]
      exact (bondTarget_eq_start hL π (hr ▸ rfl : bondTarget L s π
        (p₀ + ((r - 1 : ℕ) : ZMod n)) = unitPos n L s j₂ 0)).symm

theorem not_deleted_outer (hL : IsCollarLayout n L) (T : Finset (Fin m)) (j : Fin m) {o : ℕ}
    (ho : o = 0 ∨ o = 2) : ¬ IsDeleted L s T (unitPos n L s j o) := by
  rintro ⟨i, -, he⟩
  have := hL.2 j; have := hL.2 i
  have := ((unitPos_inj hL s (by omega) (by omega)).mp he).2
  omega

theorem IsOldRun.not_deleted_insert {π : Pairing} {S : Finset (Fin m)} {k : Fin m} {p₀ : ZMod n}
    {r : ℕ} (h : IsOldRun L s π S k p₀ r) {i : ℕ} (hi : i < r) :
    ¬ IsDeleted L s (insert k S) (p₀ + (i : ℕ)) := by
  rw [isDeleted_insert]
  rintro (he | he)
  · exact h.not_inCollar hi (Or.inr (Or.inl he))
  · exact h.not_deleted hi he

end Component

section PathHermitian

theorem pathMatrix_isHermitian {W r : ℕ} (ω : PathSample W r) (hA : ∀ i, (ω.1 i).IsHermitian) :
    (pathMatrix ω).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨i, a⟩ ⟨j, c⟩
  simp only [pathMatrix]
  by_cases hij : i = j
  · subst hij; simp only [ite_true]; exact (hA i).apply a c
  · have hji : ¬ j = i := fun h => hij h.symm
    simp only [hij, hji, ite_false]
    by_cases h1 : j.val + 1 = i.val
    · have h2 : ¬ i.val + 1 = j.val := by omega
      simp [h1, h2]
    · by_cases h2 : i.val + 1 = j.val
      · simp [h1, h2]
      · simp [h1, h2]

theorem pathSchur_isHermitian {W r : ℕ} (E : ℝ) (ω : PathSample W r)
    (hA : ∀ i, (ω.1 i).IsHermitian) : (pathSchur E ω).IsHermitian := by
  unfold pathSchur
  refine isHermitian_conjTranspose_mul_mul _ ?_
  refine IsHermitian.inv ?_
  refine (pathMatrix_isHermitian ω hA).sub ?_
  simp [IsHermitian, conjTranspose_smul]

end PathHermitian

section CompMap

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n} {π : Pairing} {S : Finset (Fin m)}
  {k : Fin m} {p₀ : ZMod n} {r : ℕ} {j₁ j₂ : Fin m}

/-- The sites of a run component: run sites then the two end ports. -/
def runCompMap (hL : IsCollarLayout n L) (h : IsOldRun L s π S k p₀ r)
    (hl : p₀ - 1 = unitPos n L s j₁ 2) (hr : runRight L s π p₀ r = unitPos n L s j₂ 0) :
    (Fin r × Fin W) ⊕ (Fin 2 × Fin W) →
      {x : StageSite L s (insert k S) W // InRunComp L s π p₀ r x.1}
  | Sum.inl x => ⟨⟨runSite p₀ x, h.not_deleted_insert x.1.isLt⟩,
      Or.inl ⟨x.1, x.1.isLt, rfl⟩⟩
  | Sum.inr y => ⟨⟨runPortSite L s π p₀ r y, by
        change ¬ IsDeleted L s (insert k S) (if y.1 = 0 then p₀ - 1 else runRight L s π p₀ r)
        by_cases hy : y.1 = 0
        · simp only [hy, ite_true]; rw [hl]; exact not_deleted_outer hL _ _ (Or.inr rfl)
        · simp only [hy, ite_false]; rw [hr]; exact not_deleted_outer hL _ _ (Or.inl rfl)⟩, by
        change InRunComp L s π p₀ r (if y.1 = 0 then p₀ - 1 else runRight L s π p₀ r, y.2)
        by_cases hy : y.1 = 0
        · simp only [hy, ite_true]; exact Or.inr (Or.inl rfl)
        · simp only [hy, ite_false]; exact Or.inr (Or.inr rfl)⟩

theorem runCompMap_val_inl (hL : IsCollarLayout n L) (h : IsOldRun L s π S k p₀ r)
    (hl : p₀ - 1 = unitPos n L s j₁ 2) (hr : runRight L s π p₀ r = unitPos n L s j₂ 0)
    (x : Fin r × Fin W) : (runCompMap hL h hl hr (Sum.inl x)).1.1 = runSite p₀ x := rfl

theorem runCompMap_val_inr (hL : IsCollarLayout n L) (h : IsOldRun L s π S k p₀ r)
    (hl : p₀ - 1 = unitPos n L s j₁ 2) (hr : runRight L s π p₀ r = unitPos n L s j₂ 0)
    (y : Fin 2 × Fin W) : (runCompMap hL h hl hr (Sum.inr y)).1.1 = runPortSite L s π p₀ r y :=
  rfl

theorem runCompMap_bijective (hL : IsCollarLayout n L) (h : IsOldRun L s π S k p₀ r)
    (hl : p₀ - 1 = unitPos n L s j₁ 2) (hr : runRight L s π p₀ r = unitPos n L s j₂ 0) :
    Function.Bijective (runCompMap (W := W) hL h hl hr) := by
  constructor
  · rintro (⟨⟨i, hi⟩, a⟩ | ⟨c, a⟩) (⟨⟨i', hi'⟩, a'⟩ | ⟨c', a'⟩) he <;>
      have he' := congrArg (fun t => t.1.1) he <;>
      simp only [runCompMap_val_inl, runCompMap_val_inr, runSite, runPortSite,
        Prod.mk.injEq] at he'
    · obtain ⟨h1, h2⟩ := he'
      have := (h.pos_inj hi.le hi'.le).mp h1
      subst this; subst h2; rfl
    · exfalso
      obtain ⟨h1, -⟩ := he'
      by_cases hc : c' = 0
      · simp only [hc, ite_true] at h1; exact h.sub_one_ne hi h1.symm
      · simp only [hc, ite_false] at h1; exact h.right_ne_run hi h1.symm
    · exfalso
      obtain ⟨h1, -⟩ := he'
      by_cases hc : c = 0
      · simp only [hc, ite_true] at h1; exact h.sub_one_ne hi' h1
      · simp only [hc, ite_false] at h1; exact h.right_ne_run hi' h1
    · obtain ⟨h1, h2⟩ := he'
      subst h2
      fin_cases c <;> fin_cases c' <;> simp at h1 ⊢
      · exact h.ends_ne h1.symm
      · exact h.ends_ne h1
  · rintro ⟨⟨x, hx⟩, hK⟩
    rcases hK with ⟨i, hi, he⟩ | he | he
    · refine ⟨Sum.inl (⟨i, hi⟩, x.2), ?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact Prod.ext he.symm rfl
    · refine ⟨Sum.inr (0, x.2), ?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact Prod.ext (by simp only [runCompMap_val_inr, runPortSite, ite_true]; exact he.symm) rfl
    · refine ⟨Sum.inr (1, x.2), ?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact Prod.ext (by simp only [runCompMap_val_inr, runPortSite]; simpa using he.symm) rfl

/-- At zero source the component of a matched run, in the order (run sites, end ports), is the
two-port path matrix with its two matched leads `[[H_path - e, C], [C*, zI]]`. -/
theorem runComp_block (hL : IsCollarLayout n L) (h : IsOldRun L s π S k p₀ r)
    (hj₁ : j₁ ∈ insert k S) (hl : p₀ - 1 = unitPos n L s j₁ 2) (hj₂ : j₂ ∈ insert k S)
    (hr : runRight L s π p₀ r = unitPos n L s j₂ 0) (e : ℝ) (z : ℂ) (buf : ℕ)
    (ω : RingCoords n W) :
    (stageFull L s π (insert k S) e z buf 0 ω).submatrix
        (fun t => (runCompMap hL h hl hr t).1.1) (fun t => (runCompMap hL h hl hr t).1.1) =
      fromBlocks (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1) (pathPortCoupling (runSample p₀ r ω))
        (pathPortCoupling (runSample p₀ r ω))ᴴ (z • 1) := by
  have hrun : ∀ x : Fin r × Fin W, (runSite p₀ x).1 ≠ unitPos n L s k 0 ∧
      (runSite p₀ x).1 ≠ unitPos n L s k 2 := fun x =>
    ⟨fun he => h.not_inCollar x.1.isLt (Or.inl he),
      fun he => h.not_inCollar x.1.isLt (Or.inr (Or.inr he))⟩
  have hpos : ∀ (x : Fin r × Fin W) (y : Fin 2 × Fin W),
      (runSite p₀ x).1 ≠ (runPortSite L s π p₀ r y).1 := by
    intro x y he
    simp only at he
    by_cases hc : y.1 = 0
    · simp only [hc, ite_true] at he; exact h.sub_one_ne x.1.isLt he.symm
    · simp only [hc, ite_false] at he; exact h.right_ne_run x.1.isLt he.symm
  have hint := h.interior e z buf 0 ω
  have hport := h.ports e z buf 0 ω
  have habs : ∀ x : Fin r × Fin W,
      stageAbsorption L s S buf 0 z.im W (p₀ + ((x.1 : ℕ) : ZMod n)) = 0 := by
    intro x
    simp [stageAbsorption, h.not_matched x.1.isLt]
  have hrr : runRight L s π p₀ r ≠ p₀ - 1 := h.ends_ne
  have hr0 : runRight L s π p₀ r ≠ unitPos n L s j₁ 3 := by
    rw [← p₀_eq_of_left hl]
    have := h.right_ne_run (j := 0) h.one_le
    simpa using this
  have hmp₁ := matched_port (s := s) hL π hj₁ e z buf 0 ω
  have hmp₂ := matched_port (s := s) hL π hj₂ e z buf 0 ω
  ext (x | y) (x' | y')
  · simp only [submatrix_apply, runCompMap_val_inl, fromBlocks_apply₁₁]
    rw [stageFull_insert_eq π S k e z buf 0 ω (Or.inr (hrun x))]
    have := congrFun (congrFun hint x) x'
    simp only [submatrix_apply] at this
    rw [this]
    simp [habs]
  · simp only [submatrix_apply, runCompMap_val_inl, runCompMap_val_inr, fromBlocks_apply₁₂]
    rw [stageFull_insert_eq π S k e z buf 0 ω (Or.inl (hpos x y'))]
    exact congrFun (congrFun hport x) y'
  · simp only [submatrix_apply, runCompMap_val_inl, runCompMap_val_inr, fromBlocks_apply₂₁,
      conjTranspose_apply]
    rw [stageFull_swap π (insert k S) e z buf 0 ω (hpos x' y),
      stageFull_insert_eq π S k e z buf 0 ω (Or.inl (hpos x' y))]
    exact congrArg star (congrFun (congrFun hport x') y)
  · simp only [submatrix_apply, runCompMap_val_inr, fromBlocks_apply₂₂]
    obtain ⟨c, a⟩ := y
    obtain ⟨c', a'⟩ := y'
    have hs1 : ∀ a : Fin W, runPortSite L s π p₀ r (0, a) = outerSite L s j₁ (1, a) := fun a =>
      Prod.ext (by simp [hl]; rfl) rfl
    have hs2 : ∀ a : Fin W, runPortSite L s π p₀ r (1, a) = outerSite L s j₂ (0, a) := fun a =>
      Prod.ext (by simp [hr]; rfl) rfl
    fin_cases c <;> fin_cases c'
    · simp only [Fin.zero_eta, hs1]
      rw [hmp₁.1]
      simp [one_apply]
    · simp only [Fin.zero_eta, Fin.mk_one, hs1]
      rw [(hmp₁.2 (1, a) (runPortSite L s π p₀ r (1, a')) (by
          simp; rw [hr]; exact not_deleted_outer hL _ _ (Or.inl rfl))
        (by simp [outerPos]; rw [← hl]; exact hrr)
        (by simp [portNeighbor]; exact hr0)).1]
      simp [one_apply]
    · simp only [Fin.zero_eta, Fin.mk_one, hs1]
      rw [(hmp₁.2 (1, a') (runPortSite L s π p₀ r (1, a)) (by
          simp; rw [hr]; exact not_deleted_outer hL _ _ (Or.inl rfl))
        (by simp [outerPos]; rw [← hl]; exact hrr)
        (by simp [portNeighbor]; exact hr0)).2]
      simp [one_apply]
    · simp only [Fin.mk_one, hs2]
      rw [hmp₂.1]
      simp [one_apply]

open Classical in

/-- **Old response of a matched run component**: the port block of `(H^after)⁻¹` on the two end
ports of the run is the two-port resolvent `(z - pathSchur e ps)⁻¹` of the run sample, and
`(H^after)⁻¹` couples the component to nothing else. -/
theorem runComp_resolvent [NeZero n] (hL : IsCollarLayout n L) (h : IsOldRun L s π S k p₀ r)
    (hj₁ : j₁ ∈ insert k S) (hl : p₀ - 1 = unitPos n L s j₁ 2) (hj₂ : j₂ ∈ insert k S)
    (hr : runRight L s π p₀ r = unitPos n L s j₂ 0) (e : ℝ) {z : ℂ} (hz : 0 < z.im) (buf : ℕ)
    (ω : RingCoords n W) (hN : IsUnit (stageMatrix L s π (insert k S) e z buf 0 ω).det)
    (hP : IsUnit (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1).det)
    (hA : ∀ i, ((runSample (W := W) p₀ r ω).1 i).IsHermitian) :
    (∀ y y' : Fin 2 × Fin W, (stageMatrix L s π (insert k S) e z buf 0 ω)⁻¹
        (runCompMap hL h hl hr (Sum.inr y)).1 (runCompMap hL h hl hr (Sum.inr y')).1 =
        (z • 1 - pathSchur e (runSample p₀ r ω))⁻¹ y y') ∧
    ∀ x y : StageSite L s (insert k S) W, InRunComp L s π p₀ r x.1 → ¬ InRunComp L s π p₀ r y.1 →
      (stageMatrix L s π (insert k S) e z buf 0 ω)⁻¹ x y = 0 ∧
        (stageMatrix L s π (insert k S) e z buf 0 ω)⁻¹ y x = 0 := by
  set N := stageMatrix L s π (insert k S) e z buf 0 ω
  have hdec : ∀ x y : StageSite L s (insert k S) W, InRunComp L s π p₀ r x.1 →
      ¬ InRunComp L s π p₀ r y.1 → N x y = 0 ∧ N y x = 0 := fun x y hx hy =>
    runComp_decoupled hL h hj₁ hl hj₂ hr e z buf 0 ω x.1 y.1 y.2 hx hy
  obtain ⟨hK, hcross⟩ := inv_block_of_decoupled N (fun x => InRunComp L s π p₀ r x.1) hdec hN
  refine ⟨fun y y' => ?_, hcross⟩
  set φe := Equiv.ofBijective _ (runCompMap_bijective (W := W) hL h hl hr)
  have hblk := runComp_block hL h hj₁ hl hj₂ hr e z buf ω
  have hsub : (N.submatrix (Subtype.val : {x : StageSite L s (insert k S) W //
      InRunComp L s π p₀ r x.1} → StageSite L s (insert k S) W) Subtype.val).submatrix φe φe =
      fromBlocks (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1) (pathPortCoupling (runSample p₀ r ω))
        (pathPortCoupling (runSample p₀ r ω))ᴴ (z • 1) := by
    rw [← hblk]; rfl
  have hinv := congrArg Inv.inv hsub
  rw [inv_submatrix_equiv, ← hK] at hinv
  have h22 := inv_fromBlocks_toBlocks₂₂ (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1)
    (pathPortCoupling (runSample p₀ r ω)) (pathPortCoupling (runSample p₀ r ω))ᴴ (z • 1) hP
    (isUnit_det_sub_hermitian (pathSchur_isHermitian e _ hA) hz)
  rw [← hinv] at h22
  have := congrFun (congrFun h22 y) y'
  exact this

end CompMap

end BlockBand.Endpoints
