module

public import BlockBand.SourceProcess.PhysApprox.GramMom.B1Abs
public import BlockBand.SourceProcess.PhysApprox.B3ModulAdapt
public import BlockBand.SourceProcess.ClosedSumProof.GramBound

/-!
# Hermitian increments and the bracket bound

* `b3dX_swapE`: the closed Gram state is Hermitian (`nearPortProj` is a real diagonal), so the
  increment of the transposed coordinate `c* = swapE c` is `conj` of that of `c`.
* `norm_cCov_le`, `norm_beta_le`: the Gram bracket coefficient `β = W⁻¹ cCov(G_j)` is bounded on the
  alive set by `W⁻¹ max(covC R, 0)`, uniformly in `W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local.GramMom

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSumProof (l1 swapE)
open scoped ENNReal ComplexConjugate

variable {W np K : ℕ}

theorem nearPortProj_conjTranspose (W : ℕ) : (nearPortProj W)ᴴ = nearPortProj W := by
  unfold nearPortProj
  rw [diagonal_conjTranspose]
  congr 1
  funext z
  simp only [Pi.star_apply]
  split_ifs <;> simp

/-- **Hermitian increments**: `ΔX_{c*} = conj ΔX_c` for the transposed Gram coordinate. -/
theorem b3dX_swapE (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (y : ProbedPath W np × ℝ) :
    b3dX b E s h τ m W j Vs (Sum.inl (swapE c) : CIdx K np) y =
      conj (b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np) y) := by
  simp only [b3dX, b3X, cEntry, b3ClosedGramAt, map_sub, starRingEnd_apply,
    ClosedSumProof.star_gramEntry (nearPortProj W) (nearPortProj_conjTranspose W)]

/-- The entry level `ρ = |SrcCol|² R` of `l1 M, l1 B` below the trace level `R`. -/
def rhoB (K np : ℕ) (R : ℝ) : ℝ := (Fintype.card (SrcCol K (Fin np)) : ℝ) ^ 2 * R

/-- The bound of the Gram bracket coefficients below the trace level `R`. -/
def covC (b E : ℝ) (K np : ℕ) (R : ℝ) : ℝ :=
  |transportD0 b E| * rhoB K np R *
    (rhoB K np R + rhoB K np R * l1 (srcSignature K (Fin np)) * rhoB K np R)

/-- **The bracket coefficient is bounded on the alive set**, uniformly in `W`. -/
theorem norm_cCov_le {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W j : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hj : closeLen s W ≤ j)
    {y : ProbedPath W np × ℝ} (hy : y ∈ b3Alive b E s h τ m R W j Vs)
    (c c' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    ‖cCov b E (Sum.inl c : CIdx K np) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤
      covC b E K np R := by
  set G := b3ClosedGramAt b E s h τ m W j Vs y
  have htr : (G.1.trace).re < R := hy.2 j hj le_rfl
  have hent : ∀ (σ : Fin 2) (a a' : SrcCol K (Fin np)), ‖gramEntry (σ, a, a') G‖ ≤ R :=
    fun σ a a' => (norm_gramEntry_b3ClosedGramAt_le b E s h τ m W j Vs y (σ, a, a')).trans htr.le
  have h1 : l1 G.1 ≤ rhoB K np R :=
    ClosedSumProof.l1_le_of_entry fun a a' => by simpa [gramEntry] using hent 0 a a'
  have h2 : l1 G.2 ≤ rhoB K np R :=
    ClosedSumProof.l1_le_of_entry fun a a' => by simpa [gramEntry] using hent 1 a a'
  exact ClosedSumProof.norm_gramCovEntry_le_rho _ _ c c' G h1 h2

/-- The coefficient `β = W⁻¹ cCov(G_j)` is bounded by `W⁻¹ max(covC R, 0)` on the alive set. -/
theorem norm_beta_le {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W j : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hj : closeLen s W ≤ j)
    (c c' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    ∀ y ∈ b3Alive b E s h τ m R W j Vs,
      ‖(W : ℂ)⁻¹ * cCov b E (Sum.inl c : CIdx K np) (Sum.inl c')
          (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤ (W : ℝ)⁻¹ * max (covC b E K np R) 0 := by
  intro y hy
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_cCov_le hj hy c c').trans (le_max_left _ _))
    (inv_nonneg.2 (Nat.cast_nonneg _))

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local.GramMom
