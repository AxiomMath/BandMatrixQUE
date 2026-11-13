module

public import BlockBand.Endpoints.Poisson.SingleCollarMomentSchur
public import BlockBand.Endpoints.Poisson.SingleCollarStage

/-!
# The stage matrix after eliminating the matched blocks (deterministic part)

Sites of the stage matrix split into the matched sites `M` (outer blocks of removed collars,
diagonal `z I`) and the rest `R` (`ScmRest`). With `B = H_{MR}` the endpoint bonds (a function of
the bonds `ω.2` only, `scmBondS`) and `G = B* B`:

* `scm_matched_entry`: the block `H_{MM}` is `z I` (`matched_port`: matched ports never bond to
  each other);
* `scm_RM_eq`, `scm_MR_eq`: the off-diagonal blocks are the bond blocks, and `H_{RM} = B*`;
* `scm_RR_eq`: `H_{RR} = (bonds) + ⊕_p A_p - e + i(κ/W²) P_C` (`P_C = scmQ`);
* `scm_det_stage`: `det H_κ = z^{|M|} det(X - e + i(κ/W²) P_C)` with
  `X = D + ⊕_p A_p + iY`, `D = (bonds) - (Re z/|z|²) G` Hermitian and
  `Y = (Im z/|z|²) G ⪰ 0` (`scmD`, `scmY`, `scmX`).
* `scm_log_ratio_eq`: hence `log(|det H_κ|/|det H_0|) = passiveLog X P_C (κ/W²) e`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix
open BlockBand.Internal.Contracts.Inputs (passiveLog)

section Stage

open Classical

variable {m n W : ℕ} (L : Fin m → ℕ) (s : ZMod n)

/-- Non-matched surviving sites of stage `T`. -/
abbrev ScmRest (T : Finset (Fin m)) (W : ℕ) :=
  {x : StageSite L s T W // ¬ IsMatched L s T x.1.1}

/-- Non-matched surviving blocks of stage `T` (the Gaussian diagonal blocks of `H_eff`). -/
abbrev ScmBlock (T : Finset (Fin m)) :=
  {p : ZMod n // ¬ IsDeleted L s T p ∧ ¬ IsMatched L s T p}

variable {L s}

/-- The block of a non-matched site. -/
def scmBlk {T : Finset (Fin m)} (x : ScmRest L s T W) : ScmBlock L s T :=
  ⟨x.1.1.1, x.1.2, x.2⟩

variable (L s)

/-- The bond part of the stage matrix: `stageHerm` with zero diagonal samples and `e = ξ = 0`,
restricted to the surviving sites; a function of the bonds only. -/
def scmBondS (π : Pairing) (T : Finset (Fin m)) (B : ZMod n → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (StageSite L s T W) (StageSite L s T W) ℂ :=
  (stageHerm L s π T 0 0 ((0 : ZMod n → Matrix (Fin W) (Fin W) ℂ), B)).submatrix
    Subtype.val Subtype.val

/-- The matched predicate on stage sites. -/
abbrev scmIsM (T : Finset (Fin m)) (x : StageSite L s T W) : Prop := IsMatched L s T x.1.1

/-- `G = B* B`, `B = H_{MR}` the endpoint bonds. -/
def scmG [NeZero n] (π : Pairing) (T : Finset (Fin m)) (B : ZMod n → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ :=
  (scmMR (scmIsM L s T) (scmBondS L s π T B))ᴴ * scmMR (scmIsM L s T) (scmBondS L s π T B)

/-- The Hermitian deformation `D = (bonds)_{RR} - (Re z/|z|²) G`. -/
def scmD [NeZero n] (π : Pairing) (T : Finset (Fin m)) (z : ℂ) (B : ZMod n → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ :=
  scmRR (scmIsM L s T) (scmBondS L s π T B) -
    ((z.re / Complex.normSq z : ℝ) : ℂ) • scmG L s π T B

/-- The absorber `Y = (Im z/|z|²) G`. -/
def scmY [NeZero n] (π : Pairing) (T : Finset (Fin m)) (z : ℂ) (B : ZMod n → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ :=
  ((z.im / Complex.normSq z : ℝ) : ℂ) • scmG L s π T B

/-- The block-diagonal part `⊕_p A_p` on the non-matched sites. -/
def scmBlocks (T : Finset (Fin m)) (A : ZMod n → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ :=
  fun x y => if scmBlk x = scmBlk y then A x.1.1.1 x.1.1.2 y.1.1.2 else 0

/-- The source projector `P_C` on the non-matched sites. -/
def scmQ (T : Finset (Fin m)) (buf : ℕ) : Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ :=
  diagonal fun x => if InSource L s buf x.1.1.1 then 1 else 0

/-- `X = D + ⊕_p A_p + iY`. -/
def scmX [NeZero n] (π : Pairing) (T : Finset (Fin m)) (z : ℂ) (ω : RingCoords n W) :
    Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ :=
  scmD L s π T z ω.2 + scmBlocks L s T ω.1 + Complex.I • scmY L s π T z ω.2

variable {L s}

/-!
### Entries
-/

theorem scm_ne_of_matched {T : Finset (Fin m)} {x y : StageSite L s T W}
    (hx : IsMatched L s T x.1.1) (hy : ¬ IsMatched L s T y.1.1) : x.1.1 ≠ y.1.1 :=
  fun h => hy (h ▸ hx)

theorem scm_matched_offset {T : Finset (Fin m)} {p : ZMod n} (hp : IsMatched L s T p) :
    ∃ j ∈ T, ∃ c : Fin 2, p = outerPos L s j c := by
  obtain ⟨j, hj, h | h⟩ := hp
  · exact ⟨j, hj, 0, h⟩
  · exact ⟨j, hj, 1, h⟩

theorem scm_portNeighbor_not_matched (hL : IsCollarLayout n L) (π : Pairing) {T : Finset (Fin m)}
    (j : Fin m) (c : Fin 2) : ¬ IsMatched L s T (portNeighbor L s π j c) := by
  intro h
  obtain ⟨j', -, c', hc'⟩ := scm_matched_offset h
  have hLj := hL.2
  have key : ∀ (i : Fin m) (o : ℕ), 3 ≤ o → o < L i + 3 →
      unitPos n L s i o ≠ outerPos L s j' c' := by
    intro i o ho1 ho2 he
    have hc := c'.isLt
    have := (unitPos_inj hL s ho2 (by have := hLj j'; omega)).mp he
    omega
  fin_cases c
  · cases π
    · exact key _ (L _ + 2) (by have := hLj ((finRotate m).symm j); omega) (by omega) hc'
    · exact key _ (L _ + 2) (by have := hLj j; omega) (by omega) hc'
  · cases π
    · exact key j 3 le_rfl (by have := hLj j; omega) hc'
    · exact key j 3 le_rfl (by have := hLj j; omega) hc'

/-- The matched block of the stage matrix is `z I`. -/
theorem scm_matched_entry (hL : IsCollarLayout n L) (π : Pairing) (T : Finset (Fin m)) (e : ℝ)
    (z : ℂ) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) (x y : StageSite L s T W)
    (hx : IsMatched L s T x.1.1) (hy : IsMatched L s T y.1.1) :
    stageMatrix L s π T e z buf κ ω x y = if x = y then z else 0 := by
  obtain ⟨j, hj, c, hxc⟩ := scm_matched_offset hx
  have hP := matched_port (W := W) (s := s) hL π hj e z buf κ ω
  have hxs : x.1 = outerSite L s j (c, x.1.2) := Prod.ext hxc rfl
  show stageFull L s π T e z buf κ ω x.1 y.1 = _
  by_cases hyc : y.1.1 = outerPos L s j c
  · have hys : y.1 = outerSite L s j (c, y.1.2) := Prod.ext hyc rfl
    rw [hxs, hys, hP.1]
    simp only [Matrix.smul_apply, one_apply, Prod.mk.injEq, true_and, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    congr 1
    apply propext
    constructor
    · intro h; exact Subtype.ext (Prod.ext (hxc.trans hyc.symm) h)
    · intro h; rw [h]
  · have hne : y.1.1 ≠ portNeighbor L s π j c := fun h =>
      scm_portNeighbor_not_matched hL π j c (h ▸ hy)
    rw [hxs, (hP.2 (c, x.1.2) y.1 y.2 hyc hne).1, ite_eq_right_iff.mpr]
    intro h
    exact absurd (by rw [← h, hxc]) hyc

/-- Off the diagonal blocks the stage matrix is its bond part. -/
theorem scm_offdiag_eq (π : Pairing) (T : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) (x y : StageSite L s T W) (h : x.1.1 ≠ y.1.1) :
    stageMatrix L s π T e z buf κ ω x y = scmBondS L s π T ω.2 x y := by
  have hxy : x.1 ≠ y.1 := fun e => h (congrArg Prod.fst e)
  simp only [stageMatrix, scmBondS, submatrix_apply, stageFull, stageHerm, Matrix.add_apply,
    diagonal_apply_ne _ hxy, h, ite_false, add_zero, zero_add]

theorem scm_bondS_isHermitian (π : Pairing) (T : Finset (Fin m))
    (B : ZMod n → Matrix (Fin W) (Fin W) ℂ) : (scmBondS L s π T B).IsHermitian :=
  (stageHerm_isHermitian (L := L) (s := s) π T 0 0 (0, B) fun _ => isHermitian_zero).submatrix _

theorem scm_MR_eq (π : Pairing) (T : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    scmMR (scmIsM L s T) (stageMatrix L s π T e z buf κ ω) =
      scmMR (scmIsM L s T) (scmBondS L s π T ω.2) := by
  ext x y
  exact scm_offdiag_eq π T e z buf κ ω x.1 y.1 (scm_ne_of_matched x.2 y.2)

theorem scm_RM_eq (π : Pairing) (T : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    scmRM (scmIsM L s T) (stageMatrix L s π T e z buf κ ω) =
      (scmMR (scmIsM L s T) (scmBondS L s π T ω.2))ᴴ := by
  ext x y
  simp only [scmRM, scmMR]
  rw [submatrix_apply, scm_offdiag_eq π T e z buf κ ω x.1 y.1
    (fun h => scm_ne_of_matched y.2 x.2 h.symm), conjTranspose_apply, submatrix_apply,
    ← (scm_bondS_isHermitian π T ω.2).apply]

theorem scm_RR_eq (π : Pairing) (T : Finset (Fin m)) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    scmRR (scmIsM L s T) (stageMatrix L s π T e z buf κ ω) =
      scmRR (scmIsM L s T) (scmBondS L s π T ω.2) + scmBlocks L s T ω.1 -
        (e : ℂ) • (1 : Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ) +
        (((κ / (W : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I) • scmQ L s T buf := by
  ext x y
  have hx := x.2
  have hblk : scmBlk x = scmBlk y ↔ x.1.1.1 = y.1.1.1 := by
    simp only [scmBlk, Subtype.mk.injEq]
  have hxy : x = y ↔ x.1.1.1 = y.1.1.1 ∧ x.1.1.2 = y.1.1.2 := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩; exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
  simp only [stageMatrix, scmBondS, scmBlocks, scmQ, submatrix_apply, stageFull, stageHerm,
    stageAbsorption, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply,
    diagonal_apply, hx, ite_false, Pi.zero_apply, Matrix.zero_apply, smul_eq_mul]
  by_cases h1 : x.1.1.1 = y.1.1.1
  · by_cases h2 : x.1.1.2 = y.1.1.2
    · have hxy' : x = y := hxy.2 ⟨h1, h2⟩
      subst hxy'
      by_cases hC : InSource L s buf x.1.1.1 <;> simp [hC] <;> ring
    · have hxy' : ¬ x = y := fun h => h2 (hxy.1 h).2
      have hxy'' : ¬ x.1.1 = y.1.1 := fun h => h2 (congrArg Prod.snd h)
      simp [h1, hblk.2 h1, hxy', hxy'', h2]
      ring
  · have hxy' : ¬ x = y := fun h => h1 (hxy.1 h).1
    have hxy'' : ¬ x.1.1 = y.1.1 := fun h => h1 (congrArg Prod.fst h)
    have hb : ¬ scmBlk x = scmBlk y := fun h => h1 (hblk.1 h)
    simp [h1, hxy', hxy'', hb]

/-!
### Elimination of the matched blocks
-/

/-- **Schur elimination of the matched ports**: `det H_κ = z^{|M|} det(X - e + i(κ/W²) P_C)`. -/
theorem scm_det_stage [NeZero n] (hL : IsCollarLayout n L) (π : Pairing) (T : Finset (Fin m))
    (e : ℝ) {z : ℂ} (hz : z ≠ 0) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    (stageMatrix L s π T e z buf κ ω).det =
      z ^ Fintype.card {x : StageSite L s T W // scmIsM L s T x} *
        (scmX L s π T z ω - (e : ℂ) • (1 : Matrix (ScmRest L s T W) (ScmRest L s T W) ℂ) +
          (((κ / (W : ℝ) ^ 2 : ℝ) : ℂ) * Complex.I) • scmQ L s T buf).det := by
  rw [scm_det_schur (scmIsM L s T) _ z hz (fun i j => by
    rw [scm_matched_entry hL π T e z buf κ ω i.1 j.1 i.2 j.2]
    exact if_congr Subtype.ext_iff.symm rfl rfl)]
  rw [scm_RR_eq, scm_RM_eq, scm_MR_eq]
  congr 2
  unfold scmX scmD scmY scmG
  rw [scm_smul_inv_eq]
  abel

/-- **The stage log ratio is a passive log** of `X = D + ⊕_p A_p + iY` with `Q = P_C` and
`a = κ/W²` (the matched prefactor `z^{|M|}` is `κ`-independent and cancels). -/
theorem scm_log_ratio_eq [NeZero n] (hL : IsCollarLayout n L) (π : Pairing) (T : Finset (Fin m))
    (e : ℝ) {z : ℂ} (hz : z ≠ 0) (buf : ℕ) (κ : ℝ) (ω : RingCoords n W) :
    Real.log (‖(stageMatrix L s π T e z buf κ ω).det‖ /
        ‖(stageMatrix L s π T e z buf 0 ω).det‖) =
      passiveLog (scmX L s π T z ω) (scmQ L s T buf) (κ / (W : ℝ) ^ 2) e := by
  rw [scm_det_stage hL π T e hz buf κ ω, scm_det_stage hL π T e hz buf 0 ω]
  unfold passiveLog
  rw [norm_div, norm_mul, norm_mul,
    mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (pow_ne_zero _ hz))]
  simp only [zero_div, Complex.ofReal_zero, zero_mul, zero_smul, add_zero]

end Stage

end BlockBand.Endpoints
