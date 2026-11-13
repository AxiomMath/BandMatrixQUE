module

public import BlockBand.SourceProcess.ClosedPath.PairGram
public import BlockBand.SourceProcess.ClosedPath.FarPort

/-!
# The physical frame at the closing time `s`

At `n_s = ⌊Ws⌋` (`closeLen s W`) take Mathlib's orthonormal eigenbasis of the Hermitian far
transmission `T_far = farTransmission` in **decreasing** order of eigenvalues (`eigenvalues₀` is
antitone):

* `physTseq k` — the `k`-th largest transmission eigenvalue (`0` for `k ≥ W`);
* `physFarVec k` — its unit far eigenvector; `physFw` — the masked `W × K` frame of retained
  ones (`h² < t_k`, `k < K`); `physF = farInj · physFw` its far-port embedding;
* `physOutProj = 𝕊ᴴP𝕊` at `n_s`; `physCurFrame` — the current frame `Φ V₀` (`curFrame`).

The masked hypotheses of `pairFrame` hold when `𝕊𝕊ᴴ = 1` (`physF_conj_mul_self`,
`one_sub_mul_physOutProj_mul_physF`, …); see `gramPair_physCurFrame` for the resulting Gram state.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedLimit
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws

variable {W : ℕ}

/-- The closing length `n_s = ⌊Ws⌋`. -/
abbrev closeLen (s : ℝ) (W : ℕ) : ℕ := ⌊(W : ℝ) * s⌋₊

/-- The `k`-th index in decreasing eigenvalue order. -/
def sortIdx (W k : ℕ) (hk : k < Fintype.card (Fin W)) : Fin W :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin W))) ⟨k, hk⟩

/-- The sorted transmission eigenvalues of `T_far(n_s)` (`0` beyond `W`). -/
def physTseq (b E s : ℝ) (W : ℕ) (ω : GrowthPath W) (k : ℕ) : ℝ :=
  if hk : k < Fintype.card (Fin W) then
    (isHermitian_farTransmission b E W (closeLen s W) ω).eigenvalues₀ ⟨k, hk⟩ else 0

/-- The unit far eigenvector of `physTseq k`. -/
def physFarVec (b E s : ℝ) (W : ℕ) (ω : GrowthPath W) (k : ℕ) : Fin W → ℂ :=
  if hk : k < Fintype.card (Fin W) then
    ⇑((isHermitian_farTransmission b E W (closeLen s W) ω).eigenvectorBasis (sortIdx W k hk))
  else 0

/-- The masked far frame (retained columns `k < K`, `h² < t_k`). -/
def physFw (b E s h : ℝ) (K W : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin K) ℂ :=
  Matrix.of fun a k => if h ^ 2 < physTseq b E s W ω k.val then physFarVec b E s W ω k.val a else 0

/-- Its far-port embedding `F`. -/
def physF (b E s h : ℝ) (K W : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin K) ℂ :=
  farInj W * physFw b E s h K W ω

/-- `P' = 𝕊ᴴP𝕊` at `n_s`. -/
def physOutProj (b E s : ℝ) (W : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (scatteringMatrix b E W (closeLen s W) ω)ᴴ * nearPortProj W *
    scatteringMatrix b E W (closeLen s W) ω

/-- **The physical current frame at time `s`**: columns `t_k^{1/4}(e_±(t_k)_0 n_k + e_±(t_k)_1 f_k)`
for the retained modes among the first `K` (zero probe columns). -/
def physCurFrame (b E s h : ℝ) (K : ℕ) (π : Type*) (W : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (SrcCol K π) ℂ :=
  curFrame (nearPortProj W) (physOutProj b E s W ω) (physF b E s h K W ω) π (physTseq b E s W ω) h

variable {b E s h : ℝ} {K : ℕ} {ω : GrowthPath W}

theorem farTransmission_mulVec_physFarVec (k : ℕ) :
    farTransmission b E W (closeLen s W) ω *ᵥ physFarVec b E s W ω k =
      ((physTseq b E s W ω k : ℝ) : ℂ) • physFarVec b E s W ω k := by
  unfold physFarVec physTseq
  split_ifs with hk
  · set hT := isHermitian_farTransmission b E W (closeLen s W) ω
    rw [hT.mulVec_eigenvectorBasis, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    congr 2
    exact (congrArg hT.eigenvalues₀ (Equiv.symm_apply_apply _ _))
  · simp

theorem physFarVec_orthonormal {k l : ℕ} (hk : k < Fintype.card (Fin W))
    (hl : l < Fintype.card (Fin W)) :
    star (physFarVec b E s W ω k) ⬝ᵥ physFarVec b E s W ω l = if k = l then 1 else 0 := by
  set hT := isHermitian_farTransmission b E W (closeLen s W) ω
  have ho := orthonormal_iff_ite.mp hT.eigenvectorBasis.orthonormal (sortIdx W k hk)
    (sortIdx W l hl)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at ho
  simp only [physFarVec, hk, hl, ↓reduceDIte]
  rw [ho]
  have : sortIdx W k hk = sortIdx W l hl ↔ k = l := by
    simp [sortIdx, Fin.ext_iff]
  simp only [this]

theorem retained_lt_card {k : ℕ} (hk : h ^ 2 < physTseq b E s W ω k) :
    k < Fintype.card (Fin W) := by
  by_contra hc
  simp only [physTseq, hc, ↓reduceDIte] at hk
  nlinarith [sq_nonneg h]

theorem physFw_conj_mul_self :
    (physFw b E s h K W ω)ᴴ * physFw b E s h K W ω = maskDiag K (physTseq b E s W ω) h := by
  ext k l
  simp only [mul_apply, conjTranspose_apply, physFw, of_apply, maskDiag, diagonal_apply,
    retainMask]
  by_cases hk : h ^ 2 < physTseq b E s W ω k.val <;>
    by_cases hl : h ^ 2 < physTseq b E s W ω l.val
  · have e := physFarVec_orthonormal (b := b) (E := E) (s := s) (ω := ω) (retained_lt_card hk)
      (retained_lt_card hl)
    simp only [hk, hl, ↓reduceIte, dotProduct, Pi.star_apply] at e ⊢
    rw [e]
    by_cases hkl : k = l
    · simp [hkl]
    · have : k.val ≠ l.val := fun h' => hkl (Fin.ext h')
      simp [hkl, this]
  · have hkl : k ≠ l := fun e => hl (e ▸ hk)
    simp [hk, hl, hkl]
  · have hkl : k ≠ l := fun e => hk (e ▸ hl)
    simp [hk, hl, hkl]
  · simp [hk, hl]

theorem physF_conj_mul_self :
    (physF b E s h K W ω)ᴴ * physF b E s h K W ω = maskDiag K (physTseq b E s W ω) h := by
  rw [physF, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (farInj W)ᴴ,
    farInj_conj_mul_self, Matrix.one_mul, physFw_conj_mul_self]

theorem nearPortProj_mul_physF : nearPortProj W * physF b E s h K W ω = 0 := by
  rw [physF, ← Matrix.mul_assoc, nearPortProj_mul_farInj, Matrix.zero_mul]

theorem farTransmission_mul_physFw :
    farTransmission b E W (closeLen s W) ω * physFw b E s h K W ω =
      physFw b E s h K W ω * tDiag K (physTseq b E s W ω) := by
  ext a k
  have e := congrFun (farTransmission_mulVec_physFarVec (b := b) (E := E) (s := s) (ω := ω) k.val) a
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
  rw [mul_apply, mul_apply, Finset.sum_eq_single k (fun j _ hj => by simp [tDiag, hj]) (by simp)]
  simp only [physFw, of_apply, tDiag, diagonal_apply_eq]
  split_ifs with hk
  · exact e.trans (mul_comm _ _)
  · simp

end BlockBand.SourceProcess.ClosedPath
