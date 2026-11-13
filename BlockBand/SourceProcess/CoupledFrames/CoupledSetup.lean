module

public import BlockBand.SourceProcess.CoupledFrames.JointMeas
public import BlockBand.SourceProcess.CoupledFrames.FrameSolMain
public import BlockBand.SourceProcess.ModelExist.Holds

/-!
# The shared births of the two cutoff frames

Two extended frames `Y₁, Y₂` on one driver space, probe birth times `θ_i = (σ'_i)⁺`, squared norms
`v_i`. Their joint Gram process `jGram = gramPair P [Y₁ | Y₂]` feeds the sorted recursion
(`BirthSort`) with the two-frame selection `jointSel`: `jvec m` is the joint vector of the `m`-th
probe (`c' ⊕ c'`-valued), `pv1`, `pv2` its two halves, and `wv k = Y₁(τ_k) a₁` the shared birth
vector. Measurability: `jvec m`, `pv_j i`, `wv k` are `𝓕_θ`-measurable (`measurable_probeV`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {K R : ℕ} {π : Type*} {n : ℕ} (eπ : π ≃ Fin n) {Ω : Type*}

/-- The joint Gram process of two extended frames. -/
def jGram (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (t : ℝ≥0) (x : Ω) :
    Matrix (ExtCol K R ⊕ ExtCol K R) (ExtCol K R ⊕ ExtCol K R) ℂ ×
      Matrix (ExtCol K R ⊕ ExtCol K R) (ExtCol K R ⊕ ExtCol K R) ℂ :=
  gramPair (ambP K R) (fromCols (Y₁ t x) (Y₂ t x))

/-- The joint vector of the `m`-th sorted-recursion probe. -/
def jvec (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ)
    (m : Fin n) : Ω → ExtCol K R ⊕ ExtCol K R → ℂ :=
  probeV (jointSel n (isCur K R)) (jGram Y₁ Y₂) (mθf eπ σ') (mvf eπ v) m

/-- The probe vectors of the first frame. -/
def pv1 (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ) :
    π → Ω → ExtCol K R → ℂ := fun i x => fstV (jvec eπ Y₁ Y₂ σ' v (eπ i) x)

/-- The probe vectors of the second frame. -/
def pv2 (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ) :
    π → Ω → ExtCol K R → ℂ := fun i x => sndV (jvec eπ Y₁ Y₂ σ' v (eπ i) x)

/-- The shared birth vectors. -/
def wv (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ)
    (k : Fin n) (x : Ω) : Amb K R → ℂ :=
  Y₁ (bτ eπ σ' k x) x *ᵥ fstV (jvec eπ Y₁ Y₂ σ' v k x)

theorem ba_pv1 (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ)
    (k : Fin n) (x : Ω) : ba eπ (pv1 eπ Y₁ Y₂ σ' v) k x = fstV (jvec eπ Y₁ Y₂ σ' v k x) := by
  simp [ba, pv1]

theorem ba_pv2 (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ)
    (k : Fin n) (x : Ω) : ba eπ (pv2 eπ Y₁ Y₂ σ' v) k x = sndV (jvec eπ Y₁ Y₂ σ' v k x) := by
  simp [ba, pv2]

theorem wv_eq (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ)
    (k : Fin n) (x : Ω) :
    Y₁ (bτ eπ σ' k x) x *ᵥ ba eπ (pv1 eπ Y₁ Y₂ σ' v) k x = wv eπ Y₁ Y₂ σ' v k x := by
  rw [ba_pv1]; rfl

end BlockBand.SourceProcess.CoupledFrames
