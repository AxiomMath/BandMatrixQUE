module

public import BlockBand.Transmission.PassiveCovariance.LevelZeroMatch
public import BlockBand.Transmission.PassiveCovariance.LeadAlgebra

/-!
# The Level-1 mean approximations, stated with the Lean words of `srcX1`, `srcX2`

* `jetDelta = δ₀ + δ₁ + q/W`.
* `MeanNear F L` (a `Prop`): for every `b ∈ (0, 1/2)`, `E ∈ (-2, 2)` and stationary jet `s` there are
  `d > 0, C, W₀` such that for `W ≥ W₀`, strictly passive `X` with `δ ≤ d`, every index `i` and all
  `u, v`: `|E[(ι₁u)* F_i (ι₁v)] - u* L_i v| ≤ C(δ + W⁻¹)‖u‖‖v‖` (law `layerLaw W b .oneBlockOnePort`).
  This is the precision the Level-0 sources need (each mean carries `s_{0p} = O(W⁻¹)`).
* `TauNear`: `|τ̄ - 1| ≤ C(δ + W⁻¹)` on the same domain.
* The three word families of `srcX1`/`srcX2`: `gamFam k = γ'_k` (`k = 0`: `𝒢Π(K̂𝒢)ᴴ`,
  `k = 1`: `(K̂𝒢)ᴴ`), `alpFam (k, p) = α'_k P_p 𝒢Π(K̂𝒢)ᴴ`, `alpFamI (k, p) = α'_k P_p 𝒢`
  (`α'_0 = K̂𝒢`, `α'_1 = K̂𝒢Π𝒢ᴴ`), with leading values `leadGam = (R, I)`,
  `leadAlp = (leadM2, leadM4)`, `leadAlpI = (leadM5, leadM6)` (`LeadAlgebra`).
* `meanNear_of_forall`: index-wise statements combine into one (finite index type).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- `δ = δ₀ + δ₁ + q/W`. -/
def jetDelta {W : ℕ} (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W

/-- A family of random layer matrices (a word evaluated at `𝒢`), indexed by `ι`. -/
abbrev WordFam (ι : Type) : Type :=
  ι → ℝ → ℝ → ∀ W : ℕ, Matrix (Fin W) (Fin W) ℂ → LayerSample W .oneBlockOnePort → LayerMat W

/-- A family of deterministic `W × W` leading values, indexed by `ι`. -/
abbrev LeadFam (ι : Type) : Type :=
  ι → ℝ → ℝ → ℂ → ∀ W : ℕ, Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ

/-- **The mean of every word of the family is its leading value up to `C(δ + W⁻¹)`**, on physical
vectors, uniformly in the index, in strictly passive `X` near the jet and in the vectors. -/
def MeanNear {ι : Type} (F : WordFam ι) (L : LeadFam ι) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDelta b E s X ≤ d →
      ∀ (i : ι) (u v : Fin W → ℂ),
        ‖(∫ ω, star (physVec u) ⬝ᵥ (F i b E W X ω *ᵥ physVec v) ∂layerLaw W b .oneBlockOnePort) -
            bilinear u (L i b E s W X) v‖ ≤
          C * (jetDelta b E s X + (W : ℝ)⁻¹) * (vecNorm u * vecNorm v)

/-- `τ̄ = 1 + O(δ + W⁻¹)`. -/
def TauNear : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDelta b E s X ≤ d →
        ‖tauBar b E X - 1‖ ≤ C * (jetDelta b E s X + (W : ℝ)⁻¹)

/-!
## The words of `srcX1`, `srcX2` and their leading values
-/

/-- `γ'_k` of the word `![1,3] ![1,Π,1]` (`k = 0`: `𝒢Π(K̂𝒢)ᴴ`; `k = 1`: `(K̂𝒢)ᴴ`). -/
def gamFam : WordFam (Fin 2) := fun k b E _ X ω =>
  wordGamma (kHat b E X) (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k

/-- `α'_k P_p 𝒢Π(K̂𝒢)ᴴ` (the second factor of `srcX1`). -/
def alpFam : WordFam (Fin 2 × Fin 2) := fun i b E _ X ω =>
  wordAlpha (kHat b E X) (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] i.1 * bProj i.2 *
    (gSide b E X false ω * wordVal (kHat b E X) (gRes b E X ω) ![3] ![portProj, 1])

/-- `α'_k P_p 𝒢` (the second factor of `srcX2`). -/
def alpFamI : WordFam (Fin 2 × Fin 2) := fun i b E _ X ω =>
  wordAlpha (kHat b E X) (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] i.1 * bProj i.2 *
    (gSide b E X false ω * wordVal (kHat b E X) (gRes b E X ω) ![] ![1])

/-- Leading values of `γ'_k`: `R`, `I`. -/
def leadGam : LeadFam (Fin 2) := fun k b E _ _ X => ![passiveResolvent b E X, 1] k

/-- Leading values of `α'_k P_p 𝒢Π(K̂𝒢)ᴴ`: `leadM2 p`, `leadM4 p`. -/
def leadAlp : LeadFam (Fin 2 × Fin 2) := fun i b E s _ X =>
  ![leadM2 b E s X i.2, leadM4 b E s X i.2] i.1

/-- Leading values of `α'_k P_p 𝒢`: `leadM5 p`, `leadM6 p`. -/
def leadAlpI : LeadFam (Fin 2 × Fin 2) := fun i b E s _ X =>
  ![leadM5 b E s X i.2, leadM6 b E s X i.2] i.1

/-!
## Combining index-wise statements
-/

/-- A finite family of positive reals has the positive lower bound `1/(Σ 1/dᵢ + 1)`. -/
theorem exists_pos_le_fintype {ι : Type} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ i, d₀ ≤ d i := by
  have hS : 0 ≤ ∑ i, (d i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hd i)).le
  refine ⟨(∑ i, (d i)⁻¹ + 1)⁻¹, by positivity, fun i => ?_⟩
  have hi : (d i)⁻¹ ≤ ∑ j, (d j)⁻¹ + 1 := by
    have := Finset.single_le_sum (f := fun j => (d j)⁻¹)
      (fun j _ => (inv_pos.mpr (hd j)).le) (Finset.mem_univ i)
    linarith
  calc (∑ j, (d j)⁻¹ + 1)⁻¹ ≤ ((d i)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (hd i)) hi
    _ = d i := inv_inv _

/-- **Index-wise mean approximations combine** (finite index type). -/
theorem meanNear_of_forall {ι : Type} [Fintype ι] {F : WordFam ι} {L : LeadFam ι}
    (h : ∀ i : ι, MeanNear (ι := Unit) (fun _ => F i) (fun _ => L i)) : MeanNear F L := by
  intro b hb0 hb E h1 h2 s hs
  choose d C W₀ hd hC hm using fun i => h i b hb0 hb E h1 h2 s hs
  obtain ⟨d₀, hd₀, hdle⟩ := exists_pos_le_fintype d hd
  refine ⟨d₀, ∑ i, C i, ∑ i, W₀ i, hd₀, Finset.sum_nonneg fun i _ => hC i,
    fun W hW X hX hδ i u v => ?_⟩
  have hWi : W₀ i ≤ W := le_trans (Finset.single_le_sum (f := W₀) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)) hW
  have hCi : C i ≤ ∑ j, C j := Finset.single_le_sum (f := C) (fun j _ => hC j) (Finset.mem_univ i)
  have hδ0 : 0 ≤ jetDelta b E s X := by
    have := passiveMass_nonneg b E hX.posSemidef
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    unfold jetDelta; positivity
  refine (hm i W hWi X hX (hδ.trans (hdle i)) () u v).trans ?_
  have := vecNorm_nonneg u; have := vecNorm_nonneg v
  gcongr

/-!
## Algebra of physical vectors and weights
-/

variable {W : ℕ}

theorem jetDelta_nonneg (b E : ℝ) (s : ℂ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) : 0 ≤ jetDelta b E s X := by
  have := passiveMass_nonneg b E hY
  have : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  unfold jetDelta; positivity

/-- `s_{0p} = w_p/W`. -/
theorem bVar_zero {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (p : Fin 2) :
    bVar W b 0 p = sRow b p / W := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  fin_cases p
  · simp only [bVar, sRow, gueVar]
    rw [Real.coe_toNNReal _ (div_nonneg (by linarith) hW)]
    push_cast; rfl
  · simp only [bVar, sRow, ginVar]
    rw [Real.coe_toNNReal _ (div_nonneg hb0.le hW)]
    push_cast; rfl

/-- `Bᴴ(ι₁v) = ι₁(B₁₁ᴴv)` when `B₁₂ = 0`. -/
theorem conjT_mulVec_physVec {B : LayerMat W} (hB : blkAt B 0 1 = 0) (v : Fin W → ℂ) :
    Bᴴ *ᵥ physVec v = physVec ((blkAt B 0 0)ᴴ *ᵥ v) := by
  have h : ∀ x y, B (phys y) (port x) = 0 := fun x y => by
    have := congrFun (congrFun hB y) x
    simpa [blkAt, siteOf] using this
  have hp : ∀ y : Fin W, physVec v (port y) = 0 := fun _ => rfl
  have hq : ∀ y : Fin W, physVec v (phys y) = v y := fun _ => rfl
  funext α
  rcases α with ⟨i, x⟩ | ⟨i, x⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    show (Bᴴ *ᵥ physVec v) (phys x) = _
    rw [mulVec, dotProduct, sum_layerSite]
    simp only [hp, mul_zero, Finset.sum_const_zero, add_zero, hq, conjTranspose_apply]
    rfl
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    show (Bᴴ *ᵥ physVec v) (port x) = 0
    rw [mulVec, dotProduct, sum_layerSite]
    simp [hp, h, conjTranspose_apply]

theorem bilinear_conjT_left {n : Type*} [Fintype n] (A L : Matrix n n ℂ) (u v : n → ℂ) :
    bilinear (Aᴴ *ᵥ u) L v = bilinear u (A * L) v := by
  rw [bilinear, bilinear, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec,
    mulVec_mulVec]

theorem bilinear_mulVec_right {n : Type*} [Fintype n] (A L : Matrix n n ℂ) (u v : n → ℂ) :
    bilinear u L (A *ᵥ v) = bilinear u (L * A) v := by
  rw [bilinear, bilinear, mulVec_mulVec]

/-- `|m₁m₂ - l₁l₂| ≤ e₁e₂ + e₁|l₂| + |l₁|e₂`. -/
theorem norm_mul_sub_mul_le' {m₁ m₂ l₁ l₂ : ℂ} {e₁ e₂ : ℝ} (h₁ : ‖m₁ - l₁‖ ≤ e₁)
    (h₂ : ‖m₂ - l₂‖ ≤ e₂) : ‖m₁ * m₂ - l₁ * l₂‖ ≤ e₁ * e₂ + e₁ * ‖l₂‖ + ‖l₁‖ * e₂ := by
  have e : m₁ * m₂ - l₁ * l₂ = (m₁ - l₁) * (m₂ - l₂) + (m₁ - l₁) * l₂ + l₁ * (m₂ - l₂) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_mul]; exact mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)

end BlockBand.Transmission.PassiveCovariance
