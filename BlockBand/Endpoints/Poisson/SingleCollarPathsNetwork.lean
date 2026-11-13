module

public import BlockBand.Endpoints.Poisson.SingleCollarPathsAlgebra
public import BlockBand.Endpoints.Poisson.SingleCollarPathsLaw
public import BlockBand.Endpoints.Poisson.SequentialCollars

/-!
# The components of the old network are two-port Gaussian paths

Stage `T = S ∪ {k}`: the old network with all its input ports is the stage matrix of `T`
(`stageMatrix_after_reindex`), whose ports are the outer blocks of the collars of `T`.

* `scpLen π T i`: the length of component `i ∈ T`, the run starting at `unitPos i 3` (right of
  collar `i`): the complementary path `i` in the box pairing, the path up to the next collar of
  `T` in the cyclic pairing. `scp_comp_run`, `scp_comp_right`: it is an `IsOldRun` whose right
  port is the left outer block of a collar of `T`; its left port is `unitPos i 2`.
* `scpSite`: its path sites and its two port sites; `scp_site_injective`;
  `scp_block`: on these sites the stage matrix is `fullPathMatrix` of the run sample, read as a
  grown path through `scpLift` (`κ = 0`); `scp_dec`: the stage matrix couples them to no other
  surviving site.
* `scp_run_len_unique`, `scp_right_cover`: every left outer block of a collar of `T` is the right
  port of some component (both pairings).
* `scp_window`: the source blocks of a component lie at distance at least `buf` from both ends.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Function
open BlockBand.Internal.Contracts.TransmissionPath (FullSite fullPathMatrix)
open BlockBand.Internal.Contracts.Layers (pathMatrix pathPortCoupling boundaryZ)

section Comp

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

variable (L s) in
/-- Length of component `i` (the run right of collar `i`) at stage `T`. -/
def scpLen (hL : IsCollarLayout n L) : Pairing → Finset (Fin m) → Fin m → ℕ
  | .cyclic, T, i => rightLen L s hL T i
  | .box, _, i => L i

theorem scp_comp_run (hL : IsCollarLayout n L) (π : Pairing) (T : Finset (Fin m)) (i : Fin m) :
    IsOldRun L s π T i (unitPos n L s i 3) (scpLen L s hL π T i) := by
  cases π
  · exact isOldRun_cyclic_right hL T i
  · exact isOldRun_box hL T i

theorem scp_comp_right (hL : IsCollarLayout n L) (π : Pairing) (T : Finset (Fin m)) (i : Fin m) :
    ∃ j ∈ insert i T, runRight L s π (unitPos n L s i 3) (scpLen L s hL π T i) =
      unitPos n L s j 0 := by
  cases π
  · exact runRight_cyclic_right hL T i
  · exact ⟨i, Finset.mem_insert_self _ _, runRight_box hL i⟩

theorem scp_unitPos_three_sub_one (s : ZMod n) (i : Fin m) :
    unitPos n L s i 3 - 1 = unitPos n L s i 2 := by
  rw [← unitPos_succ]; ring

theorem scp_collar_not_deleted (hL : IsCollarLayout n L) (T : Finset (Fin m)) (j : Fin m)
    {o : ℕ} (ho : o ≤ 2) (ho1 : o ≠ 1) : ¬ IsDeleted L s T (unitPos n L s j o) := by
  rintro ⟨j', -, he⟩
  have := hL.2 j; have := hL.2 j'
  exact unitPos_ne hL (by omega) (by omega) ho1 he

/-- Two runs from the same start whose right ports are collar starts of `T` have equal length. -/
theorem scp_run_len_unique {π : Pairing} {T : Finset (Fin m)} {a a' : Fin m} {p₀ : ZMod n}
    {r r' : ℕ} (h : IsOldRun L s π T a p₀ r) (h' : IsOldRun L s π T a' p₀ r')
    (hR : ∃ j ∈ T, runRight L s π p₀ r = unitPos n L s j 0)
    (hR' : ∃ j ∈ T, runRight L s π p₀ r' = unitPos n L s j 0) : r = r' := by
  have key : ∀ {a a' : Fin m} {r r' : ℕ}, IsOldRun L s π T a p₀ r → IsOldRun L s π T a' p₀ r' →
      (∃ j ∈ T, runRight L s π p₀ r = unitPos n L s j 0) → ¬ r < r' := by
    intro a a' r r' h h' hR hlt
    obtain ⟨j, hj, hjR⟩ := hR
    have h1 := h.one_le
    have hs := h'.succ (r - 1) (by omega)
    rw [show r - 1 + 1 = r by omega] at hs
    unfold runRight at hjR
    rw [hs] at hjR
    exact h'.avoid r hlt ⟨j, Finset.mem_insert_of_mem hj, Or.inl hjR⟩
  have h1 := key h h' hR
  have h2 := key h' h hR'
  omega

/-- **Every left outer block of a collar of `T` is the right port of a component.** -/
theorem scp_right_cover (hL : IsCollarLayout n L) (π : Pairing) {T : Finset (Fin m)} {j : Fin m}
    (hj : j ∈ T) : ∃ i ∈ T, runRight L s π (unitPos n L s i 3) (scpLen L s hL π T i) =
      unitPos n L s j 0 := by
  cases π
  · obtain ⟨j₀, hj₀, hl⟩ := left_port_cyclic_left (s := s) hL T j
    rw [Finset.insert_eq_of_mem hj] at hj₀
    have hP : unitPos n L s j 0 - (leftLen L s hL T j : ZMod n) = unitPos n L s j₀ 3 := by
      rw [← unitPos_succ, ← hl]; ring
    have hleft := isOldRun_cyclic_left (s := s) hL T j
    rw [hP] at hleft
    have hrl := runRight_cyclic_left (s := s) hL T j
    rw [hP] at hrl
    have hright := scp_comp_run (s := s) hL .cyclic T j₀
    obtain ⟨j₁, hj₁, hr₁⟩ := scp_comp_right (s := s) hL .cyclic T j₀
    rw [Finset.insert_eq_of_mem hj₀] at hj₁
    have hlen := scp_run_len_unique hleft hright ⟨j, hj, hrl⟩ ⟨j₁, hj₁, hr₁⟩
    refine ⟨j₀, hj₀, ?_⟩
    rw [← hlen]
    exact hrl
  · exact ⟨j, hj, runRight_box hL j⟩

/-- **Source window.** The source blocks of a component lie at offsets `pos` with
`buf ≤ pos` and `pos + buf < r`. -/
theorem scp_window (hL : IsCollarLayout n L) {π : Pairing} {i j : Fin m}
    {r : ℕ} (hR : runRight L s π (unitPos n L s i 3) r = unitPos n L s j 0) {buf pos : ℕ}
    (hpos : pos < r)
    (hsrc : InSource L s buf (unitPos n L s i 3 + (pos : ZMod n))) : buf ≤ pos ∧ pos + buf < r := by
  obtain ⟨k', jj, hb, hjj, he⟩ := hsrc
  have hLi := hL.2 i
  have hLk := hL.2 k'
  have hLj := hL.2 j
  -- lower end
  have hlow : jj ≤ pos := by
    by_contra hlt
    push Not at hlt
    have h2 : unitPos n L s i 2 = unitPos n L s k' (2 + jj - pos) := by
      rw [← scp_unitPos_three_sub_one, unitPos_eq_add (o := 2 + jj - pos)]
      have he' := he
      rw [unitPos_eq_add (o := 3 + jj)] at he'
      rw [Nat.cast_sub (by omega)]
      push_cast at he' ⊢
      linear_combination he'
    have := ((unitPos_inj hL s (by omega) (by omega)).mp h2).2
    omega
  -- upper end
  have hup : pos + (L k' - jj) ≤ r := by
    by_contra hlt
    push Not at hlt
    set d := r - 1 - pos with hd
    have hlast : unitPos n L s i 3 + ((r - 1 : ℕ) : ZMod n) = unitPos n L s k' (3 + jj + d) := by
      rw [show r - 1 = pos + d by omega, Nat.cast_add, ← add_assoc, he, unitPos_add]
    have hnpe : ∀ k'', unitPos n L s i 3 + ((r - 1 : ℕ) : ZMod n) ≠ pathEnd L s k'' := by
      intro k'' hpe
      rw [hlast] at hpe
      have := hL.2 k''
      obtain ⟨rfl, h2⟩ := (unitPos_inj hL s (by omega) (by omega)).mp hpe
      omega
    have hRR := hR
    unfold runRight at hRR
    rw [bondTarget_of_ne π hnpe, hlast, unitPos_succ] at hRR
    have := ((unitPos_inj hL s (by omega) (by omega)).mp hRR).2
    omega
  constructor <;> omega

end Comp

/-!
## The sites of a component and the stage matrix on them
-/

section Sites

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

variable (L s) in
/-- The path sites and the two port sites of the run `p₀, …, p₀ + r - 1`. -/
def scpSite (π : Pairing) (p₀ : ZMod n) (r : ℕ) : FullSite W r → RingSite n W :=
  Sum.elim (runSite p₀) (runPortSite L s π p₀ r)

variable {π : Pairing} {T : Finset (Fin m)} {i j : Fin m} {r : ℕ}

theorem scp_site_not_deleted (hL : IsCollarLayout n L) (h : IsOldRun L s π T i (unitPos n L s i 3) r)
    (hR : runRight L s π (unitPos n L s i 3) r = unitPos n L s j 0) (x : FullSite W r) :
    ¬ IsDeleted L s T (scpSite L s π (unitPos n L s i 3) r x).1 := by
  rcases x with a | ⟨c, w⟩
  · exact h.not_deleted a.1.isLt
  · simp only [scpSite, Sum.elim_inr, runPortSite]
    split_ifs
    · rw [scp_unitPos_three_sub_one]
      exact scp_collar_not_deleted hL T i (by norm_num) (by norm_num)
    · rw [hR]
      exact scp_collar_not_deleted hL T j (by norm_num) (by norm_num)

theorem scp_ports_ne (hL : IsCollarLayout n L) (s : ZMod n) (i j : Fin m) :
    unitPos n L s i 2 ≠ unitPos n L s j 0 := by
  have := hL.2 i; have := hL.2 j
  exact unitPos_ne hL (by omega) (by omega) (by norm_num)

theorem scp_site_injective (hL : IsCollarLayout n L) (h : IsOldRun L s π T i (unitPos n L s i 3) r)
    (hR : runRight L s π (unitPos n L s i 3) r = unitPos n L s j 0) :
    Injective (scpSite (W := W) L s π (unitPos n L s i 3) r) := by
  have hpn := scp_ports_ne (L := L) hL s i j
  rintro (⟨a, w⟩ | ⟨c, w⟩) (⟨a', w'⟩ | ⟨c', w'⟩) he <;>
    simp only [scpSite, Sum.elim_inl, Sum.elim_inr, runSite, runPortSite, Prod.mk.injEq] at he
  · obtain ⟨h1, rfl⟩ := he
    have := (h.pos_inj a.isLt.le a'.isLt.le).mp h1
    rw [Fin.val_inj] at this
    rw [this]
  · exfalso
    split_ifs at he with hc
    · exact h.sub_one_ne a.isLt he.1.symm
    · exact h.right_ne_run a.isLt he.1.symm
  · exfalso
    split_ifs at he with hc
    · exact h.sub_one_ne a'.isLt he.1
    · exact h.right_ne_run a'.isLt he.1
  · obtain ⟨h1, rfl⟩ := he
    rw [scp_unitPos_three_sub_one, hR] at h1
    have hcc : c = c' := by
      split_ifs at h1 with hc hc' hc'
      · rw [hc, hc']
      · exact absurd h1 hpn
      · exact absurd h1.symm hpn
      · exact (Fin.eq_one_of_ne_zero c hc).trans (Fin.eq_one_of_ne_zero c' hc').symm
    rw [hcc]

/-- **On a component the stage matrix (`κ = 0`) is the full path matrix of its run sample.** -/
theorem scp_block (hL : IsCollarLayout n L) (hi : i ∈ T) (hj : j ∈ T)
    (h : IsOldRun L s π T i (unitPos n L s i 3) r)
    (hR : runRight L s π (unitPos n L s i 3) r = unitPos n L s j 0) (b e : ℝ) (buf : ℕ)
    (ω : RingCoords n W) (x y : FullSite W r) :
    stageFull L s π T e (boundaryZ b e) buf 0 ω (scpSite L s π (unitPos n L s i 3) r x)
        (scpSite L s π (unitPos n L s i 3) r y) =
      fullPathMatrix b e W r (scpLift r (runSample (unitPos n L s i 3) r ω)) x y := by
  set p₀ := unitPos n L s i 3 with hp₀
  set z := boundaryZ b e
  have hfp : fullPathMatrix b e W r (scpLift r (runSample p₀ r ω)) =
      fromBlocks (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1) (pathPortCoupling (runSample p₀ r ω))
        (pathPortCoupling (runSample p₀ r ω))ᴴ (z • 1) := by
    simp only [fullPathMatrix, scp_pathAt_lift h.one_le]
    rfl
  rw [hfp]
  have hpn := scp_ports_ne (L := L) hL s i j
  have hl : p₀ - 1 = unitPos n L s i 2 := scp_unitPos_three_sub_one s i
  have hmi := matched_port (s := s) hL π hi e z buf 0 ω
  have hmj := matched_port (s := s) hL π hj e z buf 0 ω
  have hLi := hL.2 i
  have hLj := hL.2 j
  -- the two port sites as outer sites
  have hport0 : ∀ w : Fin W, runPortSite L s π p₀ r ((0 : Fin 2), w) = outerSite L s i (1, w) := by
    intro w; simp only [runPortSite, ite_true, outerSite, outerPos, hl]; rfl
  have hport1 : ∀ w : Fin W, runPortSite L s π p₀ r ((1 : Fin 2), w) = outerSite L s j (0, w) := by
    intro w
    simp only [runPortSite, show ((1 : Fin 2) = 0) = False from by simp, ite_false, outerSite,
      outerPos, hR]
    rfl
  rcases x with a | ⟨c, w⟩ <;> rcases y with a' | ⟨c', w'⟩
  · have hint := congrFun (congrFun (h.interior e z buf 0 ω) a) a'
    have habs : ∀ a : Fin r × Fin W,
        stageAbsorption L s T buf 0 z.im W (p₀ + (a.1.val : ℕ)) = 0 := by
      intro a
      simp [stageAbsorption, h.not_matched a.1.isLt]
    simp only [submatrix_apply, Matrix.add_apply, diagonal_apply, habs, Complex.ofReal_zero,
      zero_mul, ite_self, add_zero] at hint
    simpa only [scpSite, Sum.elim_inl, fromBlocks_apply₁₁] using hint
  · have hp := congrFun (congrFun (h.ports e z buf 0 ω) a) (c', w')
    simpa only [scpSite, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂, submatrix_apply] using hp
  · have hp := congrFun (congrFun (h.ports e z buf 0 ω) a') (c, w)
    simp only [submatrix_apply] at hp
    have hne : (runSite p₀ a').1 ≠ (runPortSite L s π p₀ r (c, w)).1 := by
      show p₀ + ((a'.1.val : ℕ) : ZMod n) ≠ (if c = 0 then p₀ - 1 else runRight L s π p₀ r)
      split_ifs
      · exact (h.sub_one_ne a'.1.isLt).symm
      · exact (h.right_ne_run a'.1.isLt).symm
    simp only [scpSite, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁, conjTranspose_apply]
    rw [stageFull_swap π T e z buf 0 ω hne, hp]
  · simp only [scpSite, Sum.elim_inr, fromBlocks_apply₂₂]
    fin_cases c <;> fin_cases c'
    · simp only [Fin.zero_eta, hport0]
      rw [hmi.1]
      simp [Matrix.smul_apply, one_apply]
    · simp only [Fin.zero_eta, Fin.mk_one, hport0, hport1]
      rw [(hmi.2 (1, w) (outerSite L s j (0, w'))
        (scp_collar_not_deleted hL T j (by norm_num) (by norm_num))
        (fun he => hpn he.symm)
        (by
          simp only [outerPos, portNeighbor]
          exact unitPos_ne hL (by omega) (by omega) (by norm_num))).1]
      simp [Matrix.smul_apply, one_apply]
    · simp only [Fin.zero_eta, Fin.mk_one, hport0, hport1]
      rw [(hmi.2 (1, w') (outerSite L s j (0, w))
        (scp_collar_not_deleted hL T j (by norm_num) (by norm_num))
        (fun he => hpn he.symm)
        (by
          simp only [outerPos, portNeighbor]
          exact unitPos_ne hL (by omega) (by omega) (by norm_num))).2]
      simp [Matrix.smul_apply, one_apply]
    · simp only [Fin.mk_one, hport1]
      rw [hmj.1]
      simp [Matrix.smul_apply, one_apply]

/-- **A component is decoupled** from every other surviving site. -/
theorem scp_dec (hL : IsCollarLayout n L) (hi : i ∈ T) (hj : j ∈ T)
    (h : IsOldRun L s π T i (unitPos n L s i 3) r)
    (hR : runRight L s π (unitPos n L s i 3) r = unitPos n L s j 0) (e : ℝ) (z : ℂ) (buf : ℕ)
    (κ : ℝ) (ω : RingCoords n W) (x : FullSite W r) (y : RingSite n W)
    (hy : ¬ IsDeleted L s T y.1) (hny : y ∉ Set.range (scpSite L s π (unitPos n L s i 3) r)) :
    stageFull L s π T e z buf κ ω (scpSite L s π (unitPos n L s i 3) r x) y = 0 ∧
      stageFull L s π T e z buf κ ω y (scpSite L s π (unitPos n L s i 3) r x) = 0 := by
  set p₀ := unitPos n L s i 3 with hp₀
  have hl : p₀ - 1 = unitPos n L s i 2 := scp_unitPos_three_sub_one s i
  have hLi := hL.2 i
  have hLj := hL.2 j
  have hb1 : ∀ jj < r, y.1 ≠ p₀ + (jj : ℕ) := by
    intro jj hjj he
    exact hny ⟨Sum.inl (⟨jj, hjj⟩, y.2), by simp [scpSite, runSite, ← he]⟩
  have hb2 : y.1 ≠ p₀ - 1 := by
    intro he
    exact hny ⟨Sum.inr (0, y.2), by simp [scpSite, runPortSite, ← he]⟩
  have hb3 : y.1 ≠ runRight L s π p₀ r := by
    intro he
    exact hny ⟨Sum.inr (1, y.2), by simp [scpSite, runPortSite, ← he]⟩
  rcases x with a | ⟨c, w⟩
  · exact h.decoupled e z buf κ ω a y hb1 hb2 hb3
  · fin_cases c
    · have hm := (matched_port (s := s) hL π hi e z buf κ ω).2 (1, w) y hy
        (by show y.1 ≠ unitPos n L s i 2; rw [← hl]; exact hb2)
        (by simp only [portNeighbor]; have := hb1 0 h.one_le; simpa using this)
      have hs : scpSite L s π p₀ r (Sum.inr ((0 : Fin 2), w)) = outerSite L s i (1, w) := by
        simp only [scpSite, Sum.elim_inr, runPortSite, ite_true, outerSite, outerPos, hl]; rfl
      simpa only [Fin.zero_eta, hs] using hm
    · have hpn : p₀ + ((r - 1 : ℕ) : ZMod n) = portNeighbor L s π j 0 := by
        apply bondTarget_eq_start hL π
        have := hR; unfold runRight at this; exact this
      have hm := (matched_port (s := s) hL π hj e z buf κ ω).2 (0, w) y hy
        (by show y.1 ≠ unitPos n L s j 0; rw [← hR]; exact hb3)
        (by rw [← hpn]; exact hb1 (r - 1) (by have := h.one_le; omega))
      have hs : scpSite L s π p₀ r (Sum.inr ((1 : Fin 2), w)) = outerSite L s j (0, w) := by
        simp only [scpSite, Sum.elim_inr, runPortSite,
          show ((1 : Fin 2) = 0) = False from by simp, ite_false, outerSite, outerPos, hR]
        rfl
      simpa only [Fin.mk_one, hs] using hm

end Sites

end BlockBand.Endpoints
