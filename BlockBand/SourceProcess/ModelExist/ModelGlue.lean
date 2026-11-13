module

public import BlockBand.SourceProcess.ModelExist.BornValue
public import BlockBand.SourceProcess.ModelExist.BirthMeas
public import BlockBand.SourceProcess.ModelExist.SelectSpec
public import BlockBand.SourceProcess.ModelExist.Ambient
public import BlockBand.SourceProcess.BornUnique.Reduce

/-!
# The born columns of the finite source model

Target columns `SrcCol K π`: the current column `(k, σ)` is the extended column `inl (k, σ)`
(born at `0`); probe `i` is born at `θ_i = (τ_i − s)⁺` with the vector `probeV` of the sorted
recursive selection. `mlam`, `mθ` are these data; `bornL_sig`: `L 𝖣 Lᴴ = 𝖣'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique
open scoped NNReal

variable (K R : ℕ) {π : Type*} [Fintype π] [DecidableEq π] {n : ℕ} (eπ : π ≃ Fin n)

/-- The current columns of the extended frame. -/
def isCur : ExtCol K R → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

instance : DecidablePred (isCur K R) := fun c => by
  rcases c with x | i
  · exact isTrue trivial
  · exact isFalse not_false

variable {Ω : Type*}
  (sel : (Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ) ×
    (Fin n → ExtCol K R → ℂ) × ℝ → ExtCol K R → ℂ)
  (𝒢 : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ)
  (σ : π → Ω → ℝ) (v : π → ℝ)

/-- Birth times of the sorted probes. -/
def mθf : Fin n → Ω → ℝ≥0 := fun m ω => (σ (eπ.symm m) ω).toNNReal

/-- Squared norms of the sorted probes. -/
def mvf : Fin n → ℝ := fun m => v (eπ.symm m)

/-- Birth times of the target columns. -/
def mθ : SrcCol K π → Ω → ℝ≥0
  | Sum.inl _ => fun _ => 0
  | Sum.inr i => fun ω => (σ i ω).toNNReal

/-- Vectors of the target columns. -/
def mlam : SrcCol K π → Ω → ExtCol K R → ℂ
  | Sum.inl k => fun _ => Pi.single (Sum.inl k) 1
  | Sum.inr i => probeV sel 𝒢 (mθf eπ σ) (mvf eπ v) (eπ i)

omit [Fintype π] [DecidableEq π] in
theorem mθf_sT (ω : Ω) (i : π) :
    sT (mθf eπ σ) ((srt (mθf eπ σ) ω).symm (eπ i)) ω = (σ i ω).toNNReal := by
  simp [sT, mθf]

omit [Fintype π] [DecidableEq π] in
theorem mvf_srt (ω : Ω) (i : π) :
    mvf eπ v (srt (mθf eπ σ) ω ((srt (mθf eπ σ) ω).symm (eπ i))) = v i := by
  simp [mvf]

/-- **The born columns do not change the signature:** `L_t 𝖣 L_tᴴ = 𝖣'`. -/
theorem bornL_sig (t : ℝ≥0) (ω : Ω) :
    bornL (mθ K σ) (mlam K R eπ sel 𝒢 σ v) t ω * srcSignature K π *
      (bornL (mθ K σ) (mlam K R eπ sel 𝒢 σ v) t ω)ᴴ = extSig K R := by
  ext x x'
  have hD : ∀ (A : Matrix (ExtCol K R) (SrcCol K π) ℂ) r y, (A * srcSignature K π) r y =
      A r y * (match y with | Sum.inl (_, σ) => if σ = 0 then (1 : ℂ) else -1 | Sum.inr _ => 0) :=
    fun A r y => by rw [srcSignature, Matrix.mul_diagonal]; rfl
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hD]
  simp only [conjTranspose_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, bornL, mθ,
    mlam, zero_le, ↓reduceIte]
  rcases x with y | r <;> rcases x' with y' | r'
  · rw [Finset.sum_eq_single y (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    by_cases hy : y = y' <;> simp [extSig, hy]
  · simp [extSig]
  · simp [extSig]
  · simp [extSig, diagonal_apply]

end BlockBand.SourceProcess.ModelExist
