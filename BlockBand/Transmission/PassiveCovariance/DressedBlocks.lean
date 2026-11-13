module

public import BlockBand.Transmission.PassiveCovariance.WordVariance
public import BlockBand.Transmission.PassiveCovariance.MeanFieldOp

/-!
# Blocks of dressed words are sums of passive words

The `traceMatrix` clause of `PassiveBoundsStatement` is stated for `passiveWord`s (`W × W` letters
`𝒢_{ij}`, `K𝒢₁₁`, `L` and
adjoints). This file shows that every `W × W` block `blkAt w r s` of a dressed word `w`
(`WordCalc`, letters `𝒢, K̂𝒢, 𝒢ᴴ, (K̂𝒢)ᴴ`, `K̂ = kHat`) is the sum over the `4^m` block paths
`π` of the passive words `pathWd w π`, with insertions `pathD D r s π` that are blocks of the
`D_j` (so of norm `≤ K_d`):

* `blkAt_mul`: block multiplication; `blkAt_wLetter`: the blocks of the four letters;
* `blkAt_wordVal`: `blkAt (w(𝒢)) r s = Σ_π passiveWord (pathWd w π) (pathD D r s π)`;
* `norm_pathD_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Block sites: `0 ↦` physical, `1 ↦` port. -/
def siteOf (r : Fin 2) (x : Fin W) : LayerSite W .oneBlockOnePort := if r = 0 then phys x else port x

/-- The `(r, s)` block of a layer matrix. -/
def blkAt (M : LayerMat W) (r s : Fin 2) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => M (siteOf r x) (siteOf s y)

theorem siteOf_injective (r : Fin 2) : Function.Injective (siteOf (W := W) r) := by
  intro x y h
  fin_cases r <;> simpa [siteOf] using h

theorem norm_blkAt_le (M : LayerMat W) (r s : Fin 2) : ‖blkAt M r s‖ ≤ ‖M‖ :=
  norm_submatrix_le M (siteOf_injective r) (siteOf_injective s)

theorem blkAt_mul (M N : LayerMat W) (r s : Fin 2) :
    blkAt (M * N) r s = ∑ t, blkAt M r t * blkAt N t s := by
  ext x y
  simp only [blkAt, Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, Fin.sum_univ_two]
  rw [sum_layerSite]
  rfl

theorem blkAt_add (M N : LayerMat W) (r s : Fin 2) : blkAt (M + N) r s = blkAt M r s + blkAt N r s := by
  ext x y; rfl

theorem blkAt_conjTranspose (M : LayerMat W) (r s : Fin 2) : blkAt Mᴴ r s = (blkAt M s r)ᴴ := by
  ext x y; rfl

/-- The letter convention inside `passiveWord`: letter `l.1`, adjoint when `l.2`. -/
def pLetter (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (l : Fin 6 × Bool) : Matrix (Fin W) (Fin W) ℂ :=
  if l.2 then (passiveLetter E w X ω l.1)ᴴ else passiveLetter E w X ω l.1

theorem passiveWord_zero (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (wd : Fin 0 → Fin 6 × Bool)
    (D : Fin 1 → Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    passiveWord E w X wd D ω = D 0 := by
  simp [passiveWord]

theorem passiveWord_cons (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ} (l : Fin 6 × Bool)
    (wd : Fin ℓ → Fin 6 × Bool) (D₀ : Matrix (Fin W) (Fin W) ℂ) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    passiveWord E w X (Fin.cons l wd) (Fin.cons D₀ D) ω =
      D₀ * pLetter E w X ω l * passiveWord E w X wd D ω := by
  simp only [passiveWord, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ, pLetter,
    Matrix.mul_assoc]

/-- Index of the `(t, u)` block of `𝒢` among the passive letters. -/
def gIdx (t u : Fin 2) : Fin 6 := ![![0, 1], ![2, 3]] t u

/-- The passive letter of the `(t, u)` block of the dressed letter `k`. -/
def letterIdx (k : Fin 4) (t u : Fin 2) : Fin 6 × Bool :=
  ![(gIdx t u, false), (if t = 0 then ![4, 5] u else gIdx t u, false), (gIdx u t, true),
    (if u = 0 then ![4, 5] t else gIdx u t, true)] k

theorem kHat_mul_gRes (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    kHat b E X * gRes b E X ω = fromBlocks (liftX (kG11 E (boundaryZ b E) X ω))
      (liftX (lAt E (boundaryZ b E) X ω)) (liftX (blk21 (gRes b E X ω)))
      (liftX (blk22 (gRes b E X ω))) := by
  conv_lhs => rw [layerMat_eq_fromBlocks (gRes b E X ω)]
  rw [kHat, fromBlocks_multiply]
  simp only [Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, ← liftX_mul]
  rfl

/-- **The blocks of the four dressed letters** are passive letters. -/
theorem blkAt_wLetter (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (k : Fin 4) (t u : Fin 2) :
    blkAt (wLetter (kHat b E X) (gRes b E X ω) k) t u =
      pLetter E (boundaryZ b E) X ω (letterIdx k t u) := by
  have hK := kHat_mul_gRes b E X ω
  have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
  fin_cases k <;> fin_cases t <;> fin_cases u <;> ext x y <;>
    simp [wLetter, letterIdx, gIdx, pLetter, blkAt, siteOf, hK, passiveLetter, g11, g12, g21, g22,
      layerAt, blk21, blk22, liftX, conjTranspose_apply, -conjTranspose_mul]

/-- The passive letters along a block path `π`: `π j = (t_j, u_j)`, letter `j` in block
`t_j u_j`. -/
def pathWd {ℓ : ℕ} (wd : Fin ℓ → Fin 4) (π : Fin ℓ → Fin 2 × Fin 2) : Fin ℓ → Fin 6 × Bool :=
  fun j => letterIdx (wd j) (π j).1 (π j).2

/-- The insertions along a block path: `blkAt D₀ r t₁, blkAt D₁ u₁ t₂, …, blkAt D_m u_m s`. -/
def pathD : (ℓ : ℕ) → (Fin (ℓ + 1) → LayerMat W) → Fin 2 → Fin 2 → (Fin ℓ → Fin 2 × Fin 2) →
    Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ
  | 0, D, r, s, _ => fun _ => blkAt (D 0) r s
  | ℓ + 1, D, r, s, π => Fin.cons (blkAt (D 0) r (π 0).1)
      (pathD ℓ (fun j => D j.succ) (π 0).2 s fun j => π j.succ)

theorem norm_pathD_le {Kd : ℝ} : ∀ (ℓ : ℕ) (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
    ∀ (r s : Fin 2) (π : Fin ℓ → Fin 2 × Fin 2) (j : Fin (ℓ + 1)), ‖pathD ℓ D r s π j‖ ≤ Kd := by
  intro ℓ
  induction ℓ with
  | zero => intro D hD r s π j; exact (norm_blkAt_le _ _ _).trans (hD 0)
  | succ ℓ ih =>
    intro D hD r s π j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [pathD, Fin.cons_zero]; exact (norm_blkAt_le _ _ _).trans (hD 0)
    · simp only [pathD, Fin.cons_succ]; exact ih _ (fun j => hD _) _ _ _ j

/-- **Blocks of a dressed word are sums of passive words**:
`blkAt (w(𝒢)) r s = Σ_π passiveWord (pathWd w π) (pathD D r s π)` over the `4^m` block paths. -/
theorem blkAt_wordVal (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ∀ (ℓ : ℕ) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) (r s : Fin 2),
      blkAt (wordVal (kHat b E X) (gRes b E X ω) wd D) r s =
        ∑ π : Fin ℓ → Fin 2 × Fin 2, passiveWord E (boundaryZ b E) X (pathWd wd π) (pathD ℓ D r s π) ω := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro wd D r s
    rw [wordVal_zero, Fintype.sum_unique, passiveWord_zero]
    rfl
  | succ ℓ ih =>
    intro wd D r s
    rw [wordVal_succ, Matrix.mul_assoc, blkAt_mul]
    have hin : ∀ t, blkAt (wLetter (kHat b E X) (gRes b E X ω) (wd 0) *
        wordVal (kHat b E X) (gRes b E X ω) (fun j => wd j.succ) (fun j => D j.succ)) t s =
        ∑ u, blkAt (wLetter (kHat b E X) (gRes b E X ω) (wd 0)) t u *
          blkAt (wordVal (kHat b E X) (gRes b E X ω) (fun j => wd j.succ) (fun j => D j.succ)) u s :=
      fun t => blkAt_mul _ _ _ _
    simp only [hin, ih, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ : Fin (ℓ + 1) => Fin 2 × Fin 2).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun π _ => ?_
    have e1 : pathWd wd ((Fin.consEquiv fun _ : Fin (ℓ + 1) => Fin 2 × Fin 2) ((t, u), π)) =
        Fin.cons (letterIdx (wd 0) t u) (pathWd (fun j => wd j.succ) π) := by
      funext j; refine Fin.cases rfl (fun j => rfl) j
    have e2 : pathD (ℓ + 1) D r s ((Fin.consEquiv fun _ : Fin (ℓ + 1) => Fin 2 × Fin 2) ((t, u), π)) =
        Fin.cons (blkAt (D 0) r t) (pathD ℓ (fun j => D j.succ) u s π) := rfl
    rw [e1, e2, passiveWord_cons, Matrix.mul_assoc, blkAt_wLetter]

end BlockBand.Transmission.PassiveCovariance
