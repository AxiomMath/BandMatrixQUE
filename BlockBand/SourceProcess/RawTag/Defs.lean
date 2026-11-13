module

public import BlockBand.SourceProcess.ComplexSourceLaw.Interface
public import BlockBand.SourceProcess.FullSourceStops.WordValue
public import BlockBand.Transmission.PathJet.JetPathStep
public import BlockBand.Transmission.PathScalar.AbsorbedStep

/-!
# Raw tag forms along the growing path; the exact update and births

Notation. A unit tag at **birth index** `β` in the path of length `l` sits at position `l-1-β`:
`unitTag W l β g = W^{-1/2}ι g`. The raw form is `rawForm l β₁ β₂ = ξ*G₁₁ξ'`. Its left and right
near frames are `nearL = ι*𝒰*ξ` and `nearR = ι*𝕊𝒰*ξ'`; `stepDelta l = Δ` and `stepR l = R`
are the fresh `Δ = K𝒢₁₁K - K` and `R = (z - X_l)⁻¹` of the step `l → l+1`.

The statements `RawUpdate` (the exact source update on old entries) and `RawBirth` (the entries
with the newest block) are stated here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped Matrix

variable {W : ℕ}

/-- A unit-mass tag at birth index `β` of the length-`l` path (position `l-1-β`). -/
def unitTag (W l β : ℕ) (g : Fin W → ℂ) : Fin l × Fin W → ℂ :=
  fun x => if x.1.val = l - 1 - β ∧ β < l then ((Real.sqrt (1 / W) : ℝ) : ℂ) * g x.2 else 0

/-- `W^{-1/2}g`. -/
def unitVec (W : ℕ) (g : Fin W → ℂ) : Fin W → ℂ := fun a => ((Real.sqrt (1 / W) : ℝ) : ℂ) * g a

/-- The raw form `ξ_{β₁}*G₁₁ξ'_{β₂}` at length `l` (unit masses). -/
def rawForm (b E : ℝ) (W l β₁ β₂ : ℕ) (ω : GrowthPath W) (g h : Fin W → ℂ) : ℂ :=
  star (unitTag W l β₁ g) ⬝ᵥ ((fullInverse b E W l ω).toBlocks₁₁ *ᵥ unitTag W l β₂ h)

/-- The boundary frame `𝒰*ξ` of a unit tag. -/
def frame (b E : ℝ) (W l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) : Fin 2 × Fin W → ℂ :=
  (boundaryToInterior b E W l ω)ᴴ *ᵥ unitTag W l β g

/-- The left near frame `ι*𝒰*ξ`. -/
def nearL (b E : ℝ) (W l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) : Fin W → ℂ :=
  nearSel W *ᵥ frame b E W l β ω g

/-- The right near frame `ι*𝕊𝒰*ξ'`. -/
def nearR (b E : ℝ) (W l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) : Fin W → ℂ :=
  nearSel W *ᵥ (scatteringMatrix b E W l ω *ᵥ frame b E W l β ω g)

/-- `Δ = K𝒢₁₁K - K` of the growth step `l → l+1` (fresh layer at `X_l`). -/
def stepDelta (b E : ℝ) (W l : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  freshDelta b E (pathX b E W l ω) (freshSample W l ω)

/-- `R = (z - X_l)⁻¹`. -/
def stepR (b E : ℝ) (W l : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  passiveResolvent b E (pathX b E W l ω)

/-- **The exact source update** on old entries: a.s., for `l ≥ 1` and old birth indices
`β₁, β₂ < l`, `ξ*G_{l+1}ξ' = ξ*G_lξ' + (ι*𝒰*ξ)*Δ(ι*𝕊𝒰*ξ')`. -/
def RawUpdate : Prop :=
  ∀ b E : ℝ, 0 < b → b < 1 / 2 → -2 < E → E < 2 → ∀ W : ℕ, 1 ≤ W →
    ∀ᵐ ω ∂growthPathLaw W b, ∀ l : ℕ, 1 ≤ l → ∀ β₁ β₂ : ℕ, β₁ < l → β₂ < l →
      ∀ g h : Fin W → ℂ,
        rawForm b E W (l + 1) β₁ β₂ ω g h = rawForm b E W l β₁ β₂ ω g h +
          bilinear (nearL b E W l β₁ ω g) (stepDelta b E W l ω) (nearR b E W l β₂ ω h)

/-- **The births** (at birth this is the uniform fresh inverse estimate): a.s., for `l ≥ 1`,
the entries of `G_{l+1}` with the newest block (birth index `l`) are `G_{old,new} = 𝒰ι(1 + ΔR)`,
`G_{new,old} = (1 + RΔ)ι*𝕊𝒰*`, `G_{new,new} = R + RΔR` (Schur complement of the fresh layer,
`𝒢₁₁ = R + RΔR`). -/
def RawBirth : Prop :=
  ∀ b E : ℝ, 0 < b → b < 1 / 2 → -2 < E → E < 2 → ∀ W : ℕ, 1 ≤ W →
    ∀ᵐ ω ∂growthPathLaw W b, ∀ l : ℕ, 1 ≤ l →
      (∀ β : ℕ, β < l → ∀ g h : Fin W → ℂ, rawForm b E W (l + 1) β l ω g h =
        bilinear (nearL b E W l β ω g) (1 + stepDelta b E W l ω * stepR b E W l ω)
          (unitVec W h)) ∧
      (∀ β : ℕ, β < l → ∀ g h : Fin W → ℂ, rawForm b E W (l + 1) l β ω g h =
        bilinear (unitVec W g) (1 + stepR b E W l ω * stepDelta b E W l ω)
          (nearR b E W l β ω h)) ∧
      ∀ g h : Fin W → ℂ, rawForm b E W (l + 1) l l ω g h =
        bilinear (unitVec W g) (stepR b E W l ω + stepR b E W l ω * stepDelta b E W l ω *
          stepR b E W l ω) (unitVec W h)

/-!
## The tag vector at birth-index coordinates
-/

/-- `ξ = √m · unitTag` at position `j`, birth index `n-1-j`. -/
theorem tagVector_eq_smul_unitTag (n : ℕ) (j : Fin n) {m : ℝ} (hm : 0 ≤ m) (g : Fin W → ℂ) :
    tagVector W n j m g = ((Real.sqrt m : ℝ) : ℂ) • unitTag W n (n - 1 - j.val) g := by
  funext x
  have hj := j.isLt
  have e1 : (x.1 = j) ↔ (x.1.val = n - 1 - (n - 1 - j.val) ∧ n - 1 - j.val < n) := by
    rw [Fin.ext_iff]; constructor
    · intro h; omega
    · intro h; omega
  simp only [tagVector, unitTag, Pi.smul_apply, smul_eq_mul]
  by_cases h : x.1 = j
  · have c1 : (x.1 = j) = True := eq_true h
    have c2 : (x.1.val = n - 1 - (n - 1 - j.val) ∧ n - 1 - j.val < n) = True := eq_true (e1.mp h)
    simp only [c1, c2, ↓reduceIte]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.sqrt_mul hm, mul_one_div]
  · have c1 : (x.1 = j) = False := eq_false h
    have c2 : (x.1.val = n - 1 - (n - 1 - j.val) ∧ n - 1 - j.val < n) = False :=
      eq_false fun h' => h (e1.mpr h')
    simp only [c1, c2, ↓reduceIte, mul_zero]

/-- The tag form with masses is `√(m_jm_k)` times the raw form. -/
theorem tagForm_eq_rawForm (b E : ℝ) (n : ℕ) (j k : Fin n) {mj mk : ℝ} (hj : 0 ≤ mj)
    (hk : 0 ≤ mk) (ω : GrowthPath W) (g h : Fin W → ℂ) :
    star (tagVector W n j mj g) ⬝ᵥ ((fullInverse b E W n ω).toBlocks₁₁ *ᵥ tagVector W n k mk h) =
      ((Real.sqrt mj * Real.sqrt mk : ℝ) : ℂ) *
        rawForm b E W n (n - 1 - j.val) (n - 1 - k.val) ω g h := by
  rw [tagVector_eq_smul_unitTag n j hj, tagVector_eq_smul_unitTag n k hk, rawForm, star_smul,
    mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  push_cast; ring

end BlockBand.SourceProcess.RawTag
