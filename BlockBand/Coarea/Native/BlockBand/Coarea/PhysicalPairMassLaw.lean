module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalEigenvectorMassProfile
public import BlockBand.Coarea.Native.BlockBand.Coarea.ClockReconstruction
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Physical pair-mass tilt and Schur-clock cancellation

The exact probability tilt and algebraic cancellation in the pair-mass step of the eigenpair
coarea argument.  For a fixed ordered physical eigenvector and two exposed blocks, their squared
masses define the pair mass `m`.  The tilt has density `(n / 2) m`.  Once its
normalization `E m = 2 / n` is supplied (the cyclic-invariance step), the
tilted measure is a probability measure.

Independently of any coarea formula, normalized Schur reconstruction gives
`m (vᴴ 𝒟 v) = 1`.  Thus multiplying the crossing density by the pair-mass
tilt replaces `vᴴ 𝒟 v` exactly by `n / 2`.  No conditional density, rank
sector, asymptotic parameter, or global coarea theorem is asserted here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal ComplexOrder

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Mass of the normalized ordered physical eigenvector on two selected
blocks.  In the paper these blocks are the adjacent exposed pair
`S = {i,i+1}`.  Keeping both labels explicit makes the declaration reusable
for the wrap-around pair as well. -/
def Law.physicalOrderedPairMass {p : Params} (M : Law p)
    (ω : M.Ω)
    (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (i j : Fin p.n) : NNReal :=
  physicalBlockMassWeight p
      (orderedNormalizedEigenvector (M.normalizedPhysicalMatrix ω) α) i +
    physicalBlockMassWeight p
      (orderedNormalizedEigenvector (M.normalizedPhysicalMatrix ω) α) j

/-- The pair mass is the sum of the two singleton masses in the existing
ordered eigenvector profile. -/
theorem Law.physicalOrderedPairMass_eq_profile_singletons
    {p : Params} (M : Law p) (ω : M.Ω)
    (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (i j : Fin p.n) :
    M.physicalOrderedPairMass ω α i j =
      M.physicalOrderedBlockMassProfile ω α {i} +
        M.physicalOrderedBlockMassProfile ω α {j} := by
  rw [Law.physicalOrderedBlockMassProfile,
    physicalBlockMassProfile_singleton, physicalBlockMassProfile_singleton]
  rfl

/-- The paper's Radon–Nikodym density `(n/2)m`, represented in `ℝ≥0∞`.
The natural number `n` is first coerced to `ℝ≥0∞`; division is therefore exact
and nonnegative. -/
def Law.physicalPairMassDensity {p : Params} (M : Law p)
    (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (i j : Fin p.n) (ω : M.Ω) : ENNReal :=
  (p.n : ENNReal) / 2 * (M.physicalOrderedPairMass ω α i j : ENNReal)

/-- The unbundled physical pair-mass tilted measure. -/
def Law.physicalPairMassMeasure {p : Params} (M : Law p)
    (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (i j : Fin p.n) : Measure M.Ω :=
  M.P.withDensity (M.physicalPairMassDensity α i j)

/-- The normalization `E m = 2/n` implies that the pair-mass tilted
measure has total mass one.  Cyclic invariance of the physical law supplies `hmean` for each
fixed adjacent pair; it is kept explicit because `GaussianRing.Law` records entry laws but no
block-rotation action. -/
theorem Law.isProbabilityMeasure_physicalPairMassMeasure
    {p : Params} (M : Law p)
    (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (i j : Fin p.n)
    (hmeas : Measurable (fun ω =>
      (M.physicalOrderedPairMass ω α i j : ENNReal)))
    (hmean : ∫⁻ ω, (M.physicalOrderedPairMass ω α i j : ENNReal) ∂M.P =
      2 / (p.n : ENNReal)) :
    IsProbabilityMeasure (M.physicalPairMassMeasure α i j) := by
  constructor
  rw [Law.physicalPairMassMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Law.physicalPairMassDensity]
  rw [lintegral_const_mul _ hmeas]
  simp only [Measure.restrict_univ]
  rw [hmean]
  have hn : (p.n : ENNReal) ≠ 0 := by
    exact_mod_cast p.n_pos.ne'
  have hnTop : (p.n : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top p.n
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (p.n : ENNReal) * 2⁻¹ * (2 * (p.n : ENNReal)⁻¹) =
        ((p.n : ENNReal) * (p.n : ENNReal)⁻¹) * (2⁻¹ * 2) := by
          ac_rfl
    _ = 1 := by
      rw [ENNReal.mul_inv_cancel hn hnTop]
      rw [show (2⁻¹ * 2 : ENNReal) = 2 * 2⁻¹ by ac_rfl]
      have htwo : (2 : ENNReal) * 2⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [htwo]
      simp

/-- The bundled physical pair-mass probability law.  Its only input beyond
physical ordered eigenvector data is the exact cyclic-normalization identity
`E m = 2/n`. -/
def Law.physicalPairMassLaw {p : Params} (M : Law p)
    (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (i j : Fin p.n)
    (hmeas : Measurable (fun ω =>
      (M.physicalOrderedPairMass ω α i j : ENNReal)))
    (hmean : ∫⁻ ω, (M.physicalOrderedPairMass ω α i j : ENNReal) ∂M.P =
      2 / (p.n : ENNReal)) : ProbabilityMeasure M.Ω :=
  ⟨M.physicalPairMassMeasure α i j,
    M.isProbabilityMeasure_physicalPairMassMeasure α i j hmeas hmean⟩

/-- Normalized Schur reconstruction gives the exact mass–crossing identity
`m (vᴴ𝒟v) = 1` over `ℂ` (the clock identity, in the form used for the pair mass). -/
theorem pairMass_mul_schurClock_eq_one
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) (mass : ℝ) (hmass : 0 < mass)
    (hnormalized :
      star ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) ⬝ᵥ
          ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) = 1) :
    (mass : ℂ) * (star v ⬝ᵥ (schurClock T *ᵥ v)) = 1 := by
  rw [schurClock_eq_inv_mass_of_normalized T v mass hmass hnormalized]
  norm_cast
  exact mul_inv_cancel₀ hmass.ne'

/-- Multiplication by the physical pair-mass tilt removes the Schur-clock
crossing factor and leaves exactly the constant `n/2`.  The hypothesis is precisely the
normalized Schur-graph identity; no coarea or density formula is assumed. -/
theorem pairMass_crossing_cancellation
    (blocks : ℕ)
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ) (mass : ℝ) (hmass : 0 < mass)
    (hnormalized :
      star ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) ⬝ᵥ
          ((Real.sqrt mass : ℂ) • (v ⊕ᵥ (-(T *ᵥ v)))) = 1) :
    (((blocks : ℝ) / 2 * mass : ℝ) : ℂ) *
        (star v ⬝ᵥ (schurClock T *ᵥ v)) = ((blocks : ℝ) / 2 : ℝ) := by
  rw [show ((((blocks : ℝ) / 2 * mass : ℝ) : ℂ)) =
      (((blocks : ℝ) / 2 : ℝ) : ℂ) * (mass : ℂ) by push_cast; ring]
  rw [mul_assoc, pairMass_mul_schurClock_eq_one T v mass hmass hnormalized]
  simp

/-- Physical specialization of the cancellation: the mass appearing in the
Schur reconstruction is the mass of the selected ordered eigenvector on the
exposed pair. -/
theorem Law.physicalPairMass_crossing_cancellation
    {p : Params} (M : Law p) (ω : M.Ω)
    (α : Fin (Fintype.card (BlockGUE.Index (physicalBlockSizes p))))
    (i j : Fin p.n)
    {m n : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (T : Matrix n m ℂ) (v : m → ℂ)
    (hmass : 0 < (M.physicalOrderedPairMass ω α i j : ℝ))
    (hnormalized :
      star ((Real.sqrt (M.physicalOrderedPairMass ω α i j : ℝ) : ℂ) •
          (v ⊕ᵥ (-(T *ᵥ v)))) ⬝ᵥ
        ((Real.sqrt (M.physicalOrderedPairMass ω α i j : ℝ) : ℂ) •
          (v ⊕ᵥ (-(T *ᵥ v)))) = 1) :
    (((p.n : ℝ) / 2 * (M.physicalOrderedPairMass ω α i j : ℝ) : ℝ) : ℂ) *
        (star v ⬝ᵥ (schurClock T *ᵥ v)) = ((p.n : ℝ) / 2 : ℝ) :=
  pairMass_crossing_cancellation p.n T v
    (M.physicalOrderedPairMass ω α i j : ℝ) hmass hnormalized

end GaussianRing
end CoareaNative.BlockBand
