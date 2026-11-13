module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# Restricting Gram states to a subset of columns

For an injective `r : c₁ → c₂`, `gRestrict r` restricts a Gram state on the columns `c₂` to the
range of `r`. When the state vanishes outside that range (`GSupp`) and the signature does not
couple the range with its complement (`Sep`), traces, Gram scalars, drift and covariance entries
of the restricted state are those of the full state.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open Matrix Function
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {c₁ c₂ : Type*} {r : c₁ → c₂}

/-- `X` does not couple the range of `r` with its complement. -/
def Sep (r : c₁ → c₂) (X : Matrix c₂ c₂ ℂ) : Prop :=
  ∀ a z, z ∉ Set.range r → X (r a) z = 0 ∧ X z (r a) = 0

/-- `X` vanishes on every row and every column outside the range of `r`. -/
def Supp (r : c₁ → c₂) (X : Matrix c₂ c₂ ℂ) : Prop :=
  ∀ y, y ∉ Set.range r → ∀ z, X y z = 0 ∧ X z y = 0

theorem Supp.sep {X : Matrix c₂ c₂ ℂ} (h : Supp r X) : Sep r X :=
  fun _ z hz => ⟨(h z hz _).2, (h z hz _).1⟩

theorem sum_range_of_zero [Fintype c₁] [Fintype c₂] (hr : Injective r) {g : c₂ → ℂ}
    (hg : ∀ z, z ∉ Set.range r → g z = 0) : ∑ z, g z = ∑ a, g (r a) :=
  (Fintype.sum_of_injective r hr _ g hg fun _ => rfl).symm

theorem sum_eq_zero_of_range [Fintype c₂] {g : c₂ → ℂ} (h1 : ∀ z, z ∉ Set.range r → g z = 0)
    (h2 : ∀ a, g (r a) = 0) : ∑ z, g z = 0 := by
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hz : z ∈ Set.range r
  · obtain ⟨a, rfl⟩ := hz
    exact h2 a
  · exact h1 z hz

theorem submatrix_mul_of_sep [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {X : Matrix c₂ c₂ ℂ} (hX : Sep r X)
    (Y : Matrix c₂ c₂ ℂ) : (X * Y).submatrix r r = X.submatrix r r * Y.submatrix r r := by
  ext a b
  simp only [submatrix_apply, mul_apply]
  exact sum_range_of_zero hr fun z hz => by rw [(hX a z hz).1, zero_mul]

theorem Sep.add {X Y : Matrix c₂ c₂ ℂ} (hX : Sep r X) (hY : Sep r Y) : Sep r (X + Y) :=
  fun a z hz => by simp [(hX a z hz).1, (hX a z hz).2, (hY a z hz).1, (hY a z hz).2]

theorem Supp.add {X Y : Matrix c₂ c₂ ℂ} (hX : Supp r X) (hY : Supp r Y) : Supp r (X + Y) :=
  fun y hy z => by simp [(hX y hy z).1, (hX y hy z).2, (hY y hy z).1, (hY y hy z).2]

theorem Supp.mul_left [Fintype c₂] {X Y : Matrix c₂ c₂ ℂ} (hX : Supp r X) (hY : Sep r Y) :
    Supp r (X * Y) := by
  intro y hy z
  simp only [mul_apply]
  refine ⟨Finset.sum_eq_zero fun w _ => by rw [(hX y hy w).1, zero_mul], ?_⟩
  refine sum_eq_zero_of_range (fun w hw => by rw [(hX w hw z).2, zero_mul]) fun b => ?_
  rw [(hY b y hy).1, mul_zero]

theorem Supp.mul_right [Fintype c₂] {X Y : Matrix c₂ c₂ ℂ} (hY : Sep r Y) (hX : Supp r X) :
    Supp r (Y * X) := by
  intro y hy z
  simp only [mul_apply]
  refine ⟨?_, Finset.sum_eq_zero fun w _ => by rw [(hX y hy w).2, mul_zero]⟩
  refine sum_eq_zero_of_range (fun w hw => by rw [(hX w hw z).1, mul_zero]) fun b => ?_
  rw [(hY b y hy).2, zero_mul]

theorem submatrix_add' (X Y : Matrix c₂ c₂ ℂ) :
    (X + Y).submatrix r r = X.submatrix r r + Y.submatrix r r := rfl

theorem trace_submatrix_of_supp [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {X : Matrix c₂ c₂ ℂ} (hX : Supp r X) :
    (X.submatrix r r).trace = X.trace := by
  simp only [trace, diag, submatrix_apply]
  exact (sum_range_of_zero hr fun z hz => (hX z hz z).1).symm

/-!
### Gram states
-/

/-- The restriction of a Gram state to the columns in the range of `r`. -/
def gRestrict (r : c₁ → c₂) (G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ) :
    Matrix c₁ c₁ ℂ × Matrix c₁ c₁ ℂ :=
  (G.1.submatrix r r, G.2.submatrix r r)

/-- Both Gram matrices vanish outside the range of `r`. -/
def GSupp (r : c₁ → c₂) (G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ) : Prop :=
  Supp r G.1 ∧ Supp r G.2

/-- A Gram coordinate of the restricted state, as a coordinate of the full state. -/
def eMap (r : c₁ → c₂) (e : Fin 2 × c₁ × c₁) : Fin 2 × c₂ × c₂ := (e.1, r e.2.1, r e.2.2)

theorem gRestrict_sub (G G' : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ) :
    gRestrict r (G - G') = gRestrict r G - gRestrict r G' := rfl

theorem continuous_gRestrict : Continuous (gRestrict (c₁ := c₁) (c₂ := c₂) r) := by
  unfold gRestrict
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply_apply (r a) (r b)).comp continuous_fst
  · exact continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply_apply (r a) (r b)).comp continuous_snd

theorem gramEntry_gRestrict (e : Fin 2 × c₁ × c₁) (G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ) :
    gramEntry e (gRestrict r G) = gramEntry (eMap r e) G := rfl

theorem trace_gRestrict [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ}
    (hG : Supp r G.1) : (gRestrict r G).1.trace = G.1.trace :=
  trace_submatrix_of_supp hr hG

theorem gramScalar_submatrix [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {D M : Matrix c₂ c₂ ℂ} (hD : Sep r D)
    (hM : Supp r M) : gramScalar (D.submatrix r r) (M.submatrix r r) = gramScalar D M := by
  unfold gramScalar
  have h1 : Supp r (D * M) := Supp.mul_right hD hM
  have h2 : Supp r (D * M * D) := h1.mul_left hD
  have h3 : Supp r (D * M * D * M) := h2.mul_left hM.sep
  rw [← trace_submatrix_of_supp hr h3, submatrix_mul_of_sep hr h2.sep,
    submatrix_mul_of_sep hr h1.sep, submatrix_mul_of_sep hr hD]

theorem gramDriftEntry_gRestrict [Fintype c₁] [Fintype c₂] (hr : Injective r)
    (D0 : ℝ) {D : Matrix c₂ c₂ ℂ}
    (hD : Sep r D) {G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ} (hG : Supp r G.1)
    (e : Fin 2 × c₁ × c₁) :
    gramDriftEntry D0 (D.submatrix r r) e (gRestrict r G) = gramDriftEntry D0 D (eMap r e) G := by
  unfold gramDriftEntry
  simp only [gRestrict, eMap, gramScalar_submatrix hr hD hG, submatrix_apply]
  rfl

theorem gramC0_submatrix [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {M B D : Matrix c₂ c₂ ℂ} (hM : Supp r M)
    (hD : Sep r D) :
    gramC0 (M.submatrix r r) (B.submatrix r r) (D.submatrix r r) =
      (gramC0 M B D).submatrix r r := by
  unfold gramC0
  rw [submatrix_add', submatrix_mul_of_sep hr (hM.mul_left hD).sep, submatrix_mul_of_sep hr hM.sep]

theorem gramC1_submatrix [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {M B D : Matrix c₂ c₂ ℂ} (hM : Supp r M)
    (hD : Sep r D) :
    gramC1 (M.submatrix r r) (B.submatrix r r) (D.submatrix r r) =
      (gramC1 M B D).submatrix r r := by
  unfold gramC1
  rw [submatrix_add', submatrix_mul_of_sep hr (hM.mul_left hD).sep, submatrix_mul_of_sep hr hM.sep]

theorem gramC2_submatrix [Fintype c₁] [Fintype c₂] (hr : Injective r)
    {B D : Matrix c₂ c₂ ℂ} (hB : Supp r B)
    (hD : Sep r D) :
    gramC2 (B.submatrix r r) (D.submatrix r r) = (gramC2 B D).submatrix r r := by
  unfold gramC2
  rw [submatrix_add', submatrix_mul_of_sep hr (hB.mul_left hD).sep, submatrix_mul_of_sep hr hB.sep]

theorem gramCovEntry_gRestrict [Fintype c₁] [Fintype c₂] (hr : Injective r)
    (D0 : ℝ) {D : Matrix c₂ c₂ ℂ}
    (hD : Sep r D) {G : Matrix c₂ c₂ ℂ × Matrix c₂ c₂ ℂ} (hG : GSupp r G)
    (e e' : Fin 2 × c₁ × c₁) :
    gramCovEntry D0 (D.submatrix r r) e e' (gRestrict r G) =
      gramCovEntry D0 D (eMap r e) (eMap r e') G := by
  obtain ⟨i, a, b⟩ := e
  obtain ⟨i', a', b'⟩ := e'
  have h0 := gramC0_submatrix (B := G.2) hr hG.1 hD
  have h1 := gramC1_submatrix (B := G.2) hr hG.1 hD
  have h2 := gramC2_submatrix hr hG.2 hD
  fin_cases i <;> fin_cases i' <;>
    simp only [gramCovEntry, gRestrict, eMap, crossedBracket, h0, h1, h2,
      conjTranspose_submatrix, submatrix_apply]

end BlockBand.SourceProcess.CapLimit
