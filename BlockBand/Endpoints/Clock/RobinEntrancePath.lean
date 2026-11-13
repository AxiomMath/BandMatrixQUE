module

public import BlockBand.Endpoints.Clock.RobinEntranceChain
public import BlockBand.Endpoints.Clock.NegativeClockClosure

/-!
# The Robin entrance lemma: the closed far port is the one-ended chain started at `X₀`

The condition "incoming `= e^{iθ}` outgoing" at the far port replaces the far diagonal by the real
number `λ_θ`; eliminating the far auxiliary coordinate leaves the initial Hermitian cavity `X₀` and
zero initial interior clock. This file proves the corresponding deterministic identity.

## Main result

`closedClock_eq_oneEnded`: for a growth sample `ω` with Hermitian blocks, a path length `n ≥ 1`,
`Im z > 0`, a real `λ ≠ 0` with the closure relation `e^{iθ}(z̄ - λ) = z - λ`
(`z = boundaryZ b E`), an invertible full matrix `𝓜`, an invertible `I - e^{iθ}r'`, and invertible
top blocks `A_j - E - X_j` (`j < n`) of the one-ended chain started at `X₀ = λ⁻¹B₀B₀*`
(`robinInitial`; `B₀ = ω.2 0` couples block `0` to the far port, so in this orientation the far
self-energy is `B₀λ⁻¹B₀*`):

  `closedClock b E W n θ (ω, g) = Re g* Q_n^1 g`,
  `Q_n^1 = oneEndedQ b E 1 X₀ n (robinLayers ω n)`,

for every `g`. So the closed-port clock `W⁻²‖𝒰A_θg‖²` equals the one-ended clock (weight `q ≡ 1`,
`Y₀ = 0`) of the layers `(A_k, B_{k+1})`, `k < n`, started at `X₀`; in particular the normalisation
`d = (1-b)⁻¹` carries over with no extra factor (no `|2η|` or `λ_θ`-dependent factor arises).

## Proof

The candidate `ψ = (a_{n-1-i}; π_n, p_far)` built from the descending chain, with
`p_far = -λ⁻¹B₀*a₀`, solves `𝓜ψ = (0; g, v_far)`, `v_far = (z - λ)p_far` (`robin_system`; rows of
the block-tridiagonal path matrix, `pathAt_row`, and the fresh-layer equations,
`robin_layer_facts`). Hence `(𝒰, ℝ)(g, v_far) = ψ`. The far outgoing amplitude is
`(𝕊(g,v_far))_far = (z̄ - λ)p_far`, so the closure relation gives `v_far = e^{iθ}(tg + r'v_far)`,
i.e. `(g, v_far) = A_θ g`. Finally `‖ψ_int‖² = Σ_{j<n}‖a_j‖² = Re g*Y_n g` (`quadForm_robinY`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
  BlockBand.Internal.Contracts.Clocks

namespace RobinEntrance

variable {W : ℕ}

/-!
## 1. Rows of the path matrix
-/

theorem sum_fin_ite_val (n m : ℕ) {M : Type*} [AddCommMonoid M] (T : M) :
    ∑ k : Fin n, (if m = k.val then T else 0) = if m < n then T else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if m = k then T else 0) n, Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem pathAt_row {n : ℕ} (ω : GrowthPath W) (F : ℕ → Fin W → ℂ) (i : Fin n) (a : Fin W) :
    (pathMatrix (pathAt W n ω) *ᵥ fun x => F (n - 1 - x.1.val) x.2) (i, a) =
      (ω.1 (n - 1 - i.val) *ᵥ F (n - 1 - i.val)) a +
      (if i.val + 1 < n then ((ω.2 (n - 1 - i.val))ᴴ *ᵥ F (n - 1 - i.val - 1)) a else 0) +
      (if 1 ≤ i.val then (ω.2 (n - i.val) *ᵥ F (n - i.val)) a else 0) := by
  set T0 := (ω.1 (n - 1 - i.val) *ᵥ F (n - 1 - i.val)) a
  set T1 := ((ω.2 (n - 1 - i.val))ᴴ *ᵥ F (n - 1 - i.val - 1)) a
  set T2 := (ω.2 (n - i.val) *ᵥ F (n - i.val)) a
  have key : ∀ k : Fin n, ∑ c : Fin W, pathMatrix (pathAt W n ω) (i, a) (k, c) *
      F (n - 1 - k.val) c = (if k = i then T0 else 0) + (if i.val + 1 = k.val then T1 else 0) +
        (if k.val + 1 = i.val then T2 else 0) := by
    intro k
    by_cases h0 : k = i
    · subst h0
      have h1 : ¬ k.val + 1 = k.val := by omega
      simp [pathMatrix, pathAt, T0, mulVec, dotProduct]
    · by_cases h1 : i.val + 1 = k.val
      · have h2 : ¬ k.val + 1 = i.val := by omega
        have h3 : n - 1 - k.val = n - 1 - i.val - 1 := by omega
        have h0' : ¬ i = k := fun h => h0 h.symm
        simp [pathMatrix, pathAt, T1, mulVec, dotProduct, h0, h0', h1, h2, h3]
      · by_cases h2 : i.val = k.val + 1
        · have h3 : n - 1 - k.val = n - i.val := by omega
          have h0' : ¬ i = k := fun h => h0 h.symm
          have h4 : k.val + 1 = i.val := h2.symm
          simp [pathMatrix, pathAt, T2, mulVec, dotProduct, h0, h0', h1, h3, h4]
        · have h0' : ¬ i = k := fun h => h0 h.symm
          have h4 : ¬ k.val + 1 = i.val := fun h => h2 h.symm
          simp [pathMatrix, h0, h0', h1, h4]
  simp only [mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', sum_fin_ite_val]
  simp only [Finset.mem_univ, ite_true]
  congr 1
  rcases Nat.eq_zero_or_pos i.val with h | h
  · have : ∀ k : Fin n, ¬ k.val + 1 = i.val := fun k => by omega
    simp [h]
  · obtain ⟨m, hm⟩ : ∃ m, i.val = m + 1 := ⟨i.val - 1, by omega⟩
    have hmn : m < n := by have := i.isLt; omega
    have : ∀ k : Fin n, (k.val + 1 = i.val) ↔ (m = k.val) := fun k => by omega
    simp only [this, sum_fin_ite_val, hmn, ite_true]
    have : 1 ≤ i.val := by omega
    simp [this]

theorem pathAt_coupling_row {n : ℕ} (ω : GrowthPath W) (ψ₂ : Fin 2 × Fin W → ℂ) (i : Fin n)
    (a : Fin W) :
    (pathPortCoupling (pathAt W n ω) *ᵥ ψ₂) (i, a) =
      (if i.val = 0 then (ω.2 n *ᵥ fun c => ψ₂ (0, c)) a else 0) +
      (if i.val + 1 = n then (ω.2 0 *ᵥ fun c => ψ₂ (1, c)) a else 0) := by
  simp only [mulVec, dotProduct, pathPortCoupling, Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases h0 : i.val = 0 <;> by_cases h1 : i.val + 1 = n <;> simp [h0, h1, pathAt]

theorem pathAt_near_row {n : ℕ} (hn : 0 < n) (ω : GrowthPath W) (F : ℕ → Fin W → ℂ) (c : Fin W) :
    ((pathPortCoupling (pathAt W n ω))ᴴ *ᵥ fun x => F (n - 1 - x.1.val) x.2) (0, c) =
      ((ω.2 n)ᴴ *ᵥ F (n - 1)) c := by
  simp only [mulVec, dotProduct, conjTranspose_apply, pathPortCoupling, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp [pathAt]
  · intro k _ hk
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ¬ (k.val = 0) := fun h => hk (Fin.ext h)
    simp [this]
  · simp

theorem pathAt_far_row {n : ℕ} (hn : 0 < n) (ω : GrowthPath W) (F : ℕ → Fin W → ℂ) (c : Fin W) :
    ((pathPortCoupling (pathAt W n ω))ᴴ *ᵥ fun x => F (n - 1 - x.1.val) x.2) (1, c) =
      ((ω.2 0)ᴴ *ᵥ F 0) c := by
  rw [NegativeClockScattering.far_row _ hn]
  simp [pathAt]

/-!
## 2. The initial cavity and the candidate solution
-/

/-- `X₀ = λ⁻¹ B₀B₀*`, the far self-energy after closing the far port by `λ`. -/
def robinInitial (lam : ℝ) (B : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  ((lam⁻¹ : ℝ) : ℂ) • (B * Bᴴ)

theorem robinInitial_isHermitian (lam : ℝ) (B : Matrix (Fin W) (Fin W) ℂ) :
    (robinInitial lam B).IsHermitian := by
  unfold robinInitial
  rw [IsHermitian, conjTranspose_smul, (isHermitian_mul_conjTranspose_self B).eq,
    Complex.star_def, Complex.conj_ofReal]

theorem robinX_isHermitian {E : ℝ} {D : Matrix (Fin W) (Fin W) ℂ} {ω : GrowthPath W}
    (hH : ∀ k, (ω.1 k).IsHermitian) (hD : D.IsHermitian) :
    ∀ j, (robinX E D ω j).IsHermitian
  | 0 => hD
  | j + 1 => by
    rw [robinX_succ]
    exact ClockMixingAlg.freshSchur_isHermitian E (robinX_isHermitian hH hD j) _
      (fun _ => hH j)

theorem quadForm_ofReal_smul {ι : Type*} [Fintype ι] (c : ℝ) (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm ((c : ℂ) • M) v = c * quadForm M v := by
  unfold quadForm
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- `(G *ᵥ (0, w))` restricted to the first summand is `G₁₂ *ᵥ w`. -/
theorem mulVec_elim_zero_inl {m p : Type*} [Fintype m] [Fintype p]
    (G : Matrix (m ⊕ p) (m ⊕ p) ℂ) (w : p → ℂ) (x : m) :
    (G *ᵥ Sum.elim 0 w) (Sum.inl x) = (G.toBlocks₁₂ *ᵥ w) x := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₂]

theorem mulVec_elim_zero_inr {m p : Type*} [Fintype m] [Fintype p]
    (G : Matrix (m ⊕ p) (m ⊕ p) ℂ) (w : p → ℂ) (x : p) :
    (G *ᵥ Sum.elim 0 w) (Sum.inr x) = (G.toBlocks₂₂ *ᵥ w) x := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₂₂]

section System

variable (b E lam : ℝ) {n : ℕ} (ω : GrowthPath W) (g : Fin W → ℂ)

/-- The far-port amplitude `p_far = -λ⁻¹ B₀* a₀`. -/
def robinFar : Fin W → ℂ :=
  -(((lam⁻¹ : ℝ) : ℂ) • ((ω.2 0)ᴴ *ᵥ robinAmp b E (robinInitial lam (ω.2 0)) ω n g 0))

/-- The port amplitude of layer `j+1`: `π_{j+1} = (𝒢_{j+1})₂₂ v_{j+1}`. -/
def robinPort (j : ℕ) : Fin W → ℂ :=
  freshG22 b E (robinX E (robinInitial lam (ω.2 0)) ω j) (robinLayer ω j) *ᵥ
    robinInput b E (robinInitial lam (ω.2 0)) ω n g (n - (j + 1))

/-- The candidate solution `ψ` of `𝓜ψ = (0, (g, v_far))`. -/
def robinPsi : FullSite W n → ℂ :=
  Sum.elim (fun x => robinAmp b E (robinInitial lam (ω.2 0)) ω n g (n - 1 - x.1.val) x.2)
    (fun q => ![robinPort b E lam (n := n) ω g (n - 1), robinFar b E lam (n := n) ω g] q.1 q.2)

/-- The incoming boundary vector `(g, v_far)`, `v_far = (z - λ) p_far`. -/
def robinIncoming : Fin 2 × Fin W → ℂ :=
  fun q => ![g, (boundaryZ b E - lam) • robinFar b E lam (n := n) ω g] q.1 q.2

variable {b E lam ω}

theorem robin_layer_facts (hn : 0 < n) (hzim : 0 < (boundaryZ b E).im)
    (hH : ∀ k, (ω.1 k).IsHermitian)
    (htop : ∀ j < n, IsUnit (ω.1 j - (E : ℂ) • 1 -
      robinX E (robinInitial lam (ω.2 0)) ω j).det) (hlam : lam ≠ 0) :
    (∀ j < n, ω.1 j *ᵥ robinAmp b E (robinInitial lam (ω.2 0)) ω n g j +
        (if 1 ≤ j then (ω.2 j)ᴴ *ᵥ robinAmp b E (robinInitial lam (ω.2 0)) ω n g (j - 1)
          else ω.2 0 *ᵥ robinFar b E lam (n := n) ω g) +
        ω.2 (j + 1) *ᵥ (if j + 1 < n then robinAmp b E (robinInitial lam (ω.2 0)) ω n g (j + 1)
          else robinPort b E lam (n := n) ω g (n - 1)) -
        (E : ℂ) • robinAmp b E (robinInitial lam (ω.2 0)) ω n g j = 0) ∧
    (ω.2 n)ᴴ *ᵥ robinAmp b E (robinInitial lam (ω.2 0)) ω n g (n - 1) +
        boundaryZ b E • robinPort b E lam (n := n) ω g (n - 1) = g ∧
    (ω.2 0)ᴴ *ᵥ robinAmp b E (robinInitial lam (ω.2 0)) ω n g 0 +
        boundaryZ b E • robinFar b E lam (n := n) ω g =
      (boundaryZ b E - lam) • robinFar b E lam (n := n) ω g := by
  set D := robinInitial lam (ω.2 0) with hDdef
  have hD : D.IsHermitian := robinInitial_isHermitian lam _
  set F := robinAmp b E D ω n g with hFdef
  set π := robinPort b E lam (n := n) ω g with hπdef
  set z := boundaryZ b E with hz
  have hXH := robinX_isHermitian (E := E) hH hD
  have hZ : ∀ j, IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - robinX E D ω j).det := fun j =>
    isUnit_iff_ne_zero.mpr (BlockBand.Layers.resolvent_det_ne_zero _ (hXH j) z hzim)
  have hF : ∀ j < n, IsUnit (freshFull b E (robinX E D ω j) (robinLayer ω j)).det :=
    fun j hj => freshFull_isUnit (htop j hj) (hZ (j + 1))
  -- (Fa)
  have hFa : ∀ j, j + 1 < n → π j = F (j + 1) := by
    intro j hj
    have hv : robinInput b E D ω n g (n - (j + 1)) =
        (z • (1 : Matrix (Fin W) (Fin W) ℂ) - robinX E D ω (j + 1)) *ᵥ F (j + 1) := by
      rw [robinInput_step b E D ω g (m := j + 1) (by omega), freshL_eq, ← mulVec_mulVec]
      rfl
    have hP := fresh_port_rel (htop j (by omega)) (hF j (by omega))
    have hP' : freshG22 b E (robinX E D ω j) (robinLayer ω j) *
        (z • (1 : Matrix (Fin W) (Fin W) ℂ) - robinX E D ω (j + 1)) = 1 :=
      mul_eq_one_comm.mp hP
    rw [hπdef, robinPort, hv, mulVec_mulVec, hP', one_mulVec]
  -- (E1)
  have hE1 : ∀ j < n, (ω.1 j - (E : ℂ) • 1 - robinX E D ω j) *ᵥ F j +
      ω.2 (j + 1) *ᵥ π j = 0 := by
    intro j hj
    have h := congrArg (fun M => M *ᵥ robinInput b E D ω n g (n - (j + 1)))
      (fresh_blocks (hF j hj)).1
    simp only [add_mulVec, zero_mulVec, ← mulVec_mulVec] at h
    exact h
  -- (Fb)
  have hFb : ∀ j, 1 ≤ j → j < n → (ω.2 j)ᴴ *ᵥ F (j - 1) = -(robinX E D ω j *ᵥ F j) := by
    intro j hj1 hjn
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hS := fresh_schur_rel (htop m (by omega)) (hF m (by omega))
    have h := congrArg (fun M => M *ᵥ robinInput b E D ω n g (n - (m + 1))) hS
    simp only [← mulVec_mulVec, neg_mulVec] at h
    rw [Nat.add_sub_cancel, ← hFa m (by omega)]
    exact h
  -- (Fc)
  have hFc : ω.2 0 *ᵥ robinFar b E lam (n := n) ω g = -(robinX E D ω 0 *ᵥ F 0) := by
    rw [robinX_zero, robinFar, hDdef, robinInitial, mulVec_neg, mulVec_smul, mulVec_mulVec,
      smul_mulVec]
    rfl
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · have h1 : (if 1 ≤ j then (ω.2 j)ᴴ *ᵥ F (j - 1) else ω.2 0 *ᵥ robinFar b E lam (n := n) ω g)
        = -(robinX E D ω j *ᵥ F j) := by
      split_ifs with h
      · exact hFb j h hj
      · have : j = 0 := by omega
        subst this; exact hFc
    have h2 : (if j + 1 < n then F (j + 1) else π (n - 1)) = π j := by
      split_ifs with h
      · exact (hFa j h).symm
      · have : j = n - 1 := by omega
        rw [this]
    rw [h1, h2]
    have h := hE1 j hj
    rw [sub_mulVec, sub_mulVec, smul_mulVec, one_mulVec] at h
    rw [← h]
    abel
  · have hn1 : n - 1 + 1 = n := by omega
    have h := congrArg (fun M => M *ᵥ g) (fresh_blocks (hF (n - 1) (by omega))).2
    simp only [add_mulVec, ← mulVec_mulVec, smul_mulVec, one_mulVec] at h
    have hg : robinInput b E D ω n g (n - (n - 1 + 1)) = g := by
      rw [hn1, Nat.sub_self]; rfl
    rw [hFdef, robinAmp, hπdef, robinPort, hg]
    have hb : (robinLayer ω (n - 1)).2 0 0 = ω.2 n := by
      show ω.2 (n - 1 + 1) = ω.2 n
      rw [hn1]
    rw [← hb]
    exact h
  · have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    have h : (ω.2 0)ᴴ *ᵥ F 0 = -((lam : ℂ) • robinFar b E lam (n := n) ω g) := by
      rw [robinFar, smul_neg, neg_neg, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hlam',
        one_smul]
    rw [h, sub_smul]
    abel

end System

section Solve

variable {b E lam : ℝ} {n : ℕ} {ω : GrowthPath W} (g : Fin W → ℂ)

theorem robin_system (hn : 0 < n) (hzim : 0 < (boundaryZ b E).im)
    (hH : ∀ k, (ω.1 k).IsHermitian)
    (htop : ∀ j < n, IsUnit (ω.1 j - (E : ℂ) • 1 -
      robinX E (robinInitial lam (ω.2 0)) ω j).det) (hlam : lam ≠ 0) :
    fullPathMatrix b E W n ω *ᵥ robinPsi b E lam ω g =
      Sum.elim (0 : Fin n × Fin W → ℂ) (robinIncoming b E lam (n := n) ω g) := by
  obtain ⟨hblk, hnear, hfar⟩ := robin_layer_facts g hn hzim hH htop hlam
  set F := robinAmp b E (robinInitial lam (ω.2 0)) ω n g with hFdef
  set π := robinPort b E lam (n := n) ω g with hπdef
  set pF := robinFar b E lam (n := n) ω g with hpF
  funext x
  rcases x with ⟨i, a⟩ | ⟨q, c⟩
  · rw [fullPathMatrix, fromBlocks_mulVec]
    simp only [Sum.elim_inl, Pi.add_apply, Pi.zero_apply]
    have hψ1 : (robinPsi b E lam ω g ∘ Sum.inl) = fun x => F (n - 1 - x.1.val) x.2 := rfl
    rw [hψ1, sub_mulVec, Pi.sub_apply, pathAt_row, pathAt_coupling_row, smul_mulVec,
      one_mulVec]
    have hψ20 : (fun c => (robinPsi b E lam ω g ∘ Sum.inr) (0, c)) = π (n - 1) := rfl
    have hψ21 : (fun c => (robinPsi b E lam ω g ∘ Sum.inr) (1, c)) = pF := rfl
    rw [hψ20, hψ21]
    have hi := i.isLt
    set j := n - 1 - i.val with hj
    have e1 : n - i.val = j + 1 := by omega
    rw [e1]
    have hb := congrFun (hblk j (by omega)) a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
    rcases Nat.eq_zero_or_pos i.val with h0 | h0 <;>
      rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
    · -- i = 0, j = n - 1 ≥ 1
      have hj1 : 1 ≤ j := by omega
      have hj2 : ¬ j + 1 < n := by omega
      have hjn : j + 1 = n := by omega
      rw [ite_eq_left hj1, ite_eq_right hj2, hjn] at hb
      rw [ite_eq_left h1, ite_eq_right (by omega : ¬ 1 ≤ i.val), ite_eq_left h0,
        ite_eq_right (by omega : ¬ i.val + 1 = n)]
      simp only [Pi.smul_apply, smul_eq_mul] at hb ⊢
      linear_combination hb
    · -- i = 0, n = 1, j = 0
      have hj1 : ¬ 1 ≤ j := by omega
      have hj2 : ¬ j + 1 < n := by omega
      have hjn : j + 1 = n := by omega
      rw [ite_eq_right hj1, ite_eq_right hj2, hjn] at hb
      rw [ite_eq_right (by omega : ¬ i.val + 1 < n), ite_eq_right (by omega : ¬ 1 ≤ i.val),
        ite_eq_left h0, ite_eq_left (by omega : i.val + 1 = n)]
      simp only [Pi.smul_apply, smul_eq_mul] at hb ⊢
      linear_combination hb
    · -- 1 ≤ i, i + 1 < n
      have hj1 : 1 ≤ j := by omega
      have hj2 : j + 1 < n := by omega
      rw [ite_eq_left hj1, ite_eq_left hj2] at hb
      rw [ite_eq_left h1, ite_eq_left (by omega : 1 ≤ i.val), ite_eq_right (by omega : ¬ i.val = 0),
        ite_eq_right (by omega : ¬ i.val + 1 = n)]
      simp only [Pi.smul_apply, smul_eq_mul] at hb ⊢
      linear_combination hb
    · -- 1 ≤ i, i + 1 = n, j = 0
      have hj1 : ¬ 1 ≤ j := by omega
      have hj2 : j + 1 < n := by omega
      rw [ite_eq_right hj1, ite_eq_left hj2] at hb
      rw [ite_eq_right (by omega : ¬ i.val + 1 < n), ite_eq_left (by omega : 1 ≤ i.val),
        ite_eq_right (by omega : ¬ i.val = 0), ite_eq_left (by omega : i.val + 1 = n)]
      simp only [Pi.smul_apply, smul_eq_mul] at hb ⊢
      linear_combination hb
  · rw [fullPathMatrix, fromBlocks_mulVec]
    simp only [Sum.elim_inr, Pi.add_apply]
    have hψ1 : (robinPsi b E lam ω g ∘ Sum.inl) = fun x => F (n - 1 - x.1.val) x.2 := rfl
    rw [hψ1, smul_mulVec, one_mulVec]
    obtain rfl | rfl : q = 0 ∨ q = 1 := by fin_cases q <;> simp
    · rw [pathAt_near_row hn]
      have := congrFun hnear c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      simpa [robinIncoming, robinPsi, hπdef, hFdef] using this
    · rw [pathAt_far_row hn]
      have := congrFun hfar c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      simpa [robinIncoming, robinPsi, hpF, hFdef] using this

theorem vecNormSq_reflect {n : ℕ} (F : ℕ → Fin W → ℂ) :
    vecNormSq (fun x : Fin n × Fin W => F (n - 1 - x.1.val) x.2) =
      ∑ j ∈ Finset.range n, vecNormSq (F j) := by
  unfold vecNormSq
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑ y : Fin W, ‖F (n - 1 - k) y‖ ^ 2) n]
  exact Finset.sum_range_reflect (fun j => ∑ y : Fin W, ‖F j y‖ ^ 2) n

/-- **Deterministic closed-port reduction** (proof of the Robin entrance lemma). -/
theorem closedClock_eq_oneEnded (θ : ℝ) (hn : 0 < n) (hzim : 0 < (boundaryZ b E).im)
    (hH : ∀ k, (ω.1 k).IsHermitian)
    (htop : ∀ j < n, IsUnit (ω.1 j - (E : ℂ) • 1 -
      robinX E (robinInitial lam (ω.2 0)) ω j).det) (hlam : lam ≠ 0)
    (hM : IsUnit (fullPathMatrix b E W n ω).det)
    (hR : IsUnit (1 - phase θ • farReflection (scatteringMatrix b E W n ω)).det)
    (hcl : phase θ * (star (boundaryZ b E) - lam) = boundaryZ b E - lam) :
    closedClock b E W n θ (ω, g) =
      quadForm (oneEndedQ b E (fun _ => 1) (robinInitial lam (ω.2 0)) n (robinLayers ω n)) g := by
  set z := boundaryZ b E with hz
  set w₂ := robinIncoming b E lam (n := n) ω g with hw₂
  set ψ := robinPsi b E lam ω g with hψdef
  set pF := robinFar b E lam (n := n) ω g with hpF
  set S := scatteringMatrix b E W n ω with hS
  have hsys := robin_system g hn hzim hH htop hlam
  have hψ : ψ = fullInverse b E W n ω *ᵥ Sum.elim (0 : Fin n × Fin W → ℂ) w₂ := by
    rw [← hsys, fullInverse, mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]
  have hU : boundaryToInterior b E W n ω *ᵥ w₂ = ψ ∘ Sum.inl := by
    funext x
    rw [boundaryToInterior, ← mulVec_elim_zero_inl, ← hψ]
    rfl
  have hRv : boundaryResolvent b E W n ω *ᵥ w₂ = ψ ∘ Sum.inr := by
    funext x
    rw [boundaryResolvent, ← mulVec_elim_zero_inr, ← hψ]
    rfl
  have hκ : (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) = z - star z := by
    rw [Complex.star_def, Complex.sub_conj]; rfl
  -- far component of `S w₂`
  have hfarS : ∀ d, (S *ᵥ w₂) (1, d) = (star z - lam) * pF d := by
    intro d
    have h1 : (S *ᵥ w₂) (1, d) = w₂ (1, d) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) * (ψ ∘ Sum.inr) (1, d) := by
      rw [hS, scatteringMatrix, sub_mulVec, one_mulVec, smul_mulVec, hRv]
      rfl
    rw [h1, hκ]
    simp only [hw₂, robinIncoming, hψdef, robinPsi, Function.comp, Sum.elim_inr,
      Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
    rw [← hpF, ← hz]
    ring
  have hblkS : ∀ d, (S *ᵥ w₂) (1, d) =
      (transmission S *ᵥ g) d + (farReflection S *ᵥ ((z - lam) • pF)) d := by
    intro d
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, transmission,
      farReflection, scatteringBlock, Matrix.of_apply, hw₂, robinIncoming,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hpF]
  have hv : (z - lam) • pF = phaseGamma (farReflection S) (transmission S) θ *ᵥ g := by
    have h1 : (z - lam) • pF = phase θ • (transmission S *ᵥ g +
        farReflection S *ᵥ ((z - lam) • pF)) := by
      funext d
      have := hblkS d
      rw [hfarS d] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      rw [← this, ← mul_assoc, hcl]
    have h2 : (1 - phase θ • farReflection S) *ᵥ ((z - lam) • pF) =
        (phase θ • transmission S) *ᵥ g := by
      rw [sub_mulVec, one_mulVec, smul_mulVec, smul_mulVec]
      nth_rewrite 1 [h1]
      rw [smul_add]
      abel
    rw [phaseGamma, ← mulVec_mulVec, ← h2, mulVec_mulVec, nonsing_inv_mul _ hR, one_mulVec]
  have hA : closurePhaseA b E W n ω θ *ᵥ g = w₂ := by
    funext ⟨q, d⟩
    obtain rfl | rfl : q = 0 ∨ q = 1 := by fin_cases q <;> simp
    · simp [closurePhaseA, scatteringPhaseA, phaseA, mulVec, dotProduct, hw₂, robinIncoming,
        Matrix.one_apply]
    · show (closurePhaseA b E W n ω θ *ᵥ g) (1, d) = ((z - lam) • pF) d
      rw [hv]
      simp [closurePhaseA, scatteringPhaseA, phaseA, mulVec, dotProduct, hS]
  -- the clock
  have hq : quadForm ((closurePhaseA b E W n ω θ)ᴴ * fullClock b E W n ω *
      closurePhaseA b E W n ω θ) g = vecNormSq (ψ ∘ Sum.inl) := by
    have h := clock_after_closure_normSq (boundaryToInterior b E W n ω)
      (closurePhaseA b E W n ω θ) g
    rw [hA, hU] at h
    unfold quadForm
    rw [fullClock, ← h, Complex.ofReal_re]
  rw [closedClock, hq]
  have hψ1 : ψ ∘ Sum.inl = fun x : Fin n × Fin W =>
      robinAmp b E (robinInitial lam (ω.2 0)) ω n g (n - 1 - x.1.val) x.2 := rfl
  rw [hψ1, vecNormSq_reflect]
  have hY := quadForm_robinY b E (robinInitial lam (ω.2 0)) ω g n le_rfl
  rw [Nat.sub_self] at hY
  have e : oneEndedQ b E (fun _ => 1) (robinInitial lam (ω.2 0)) n (robinLayers ω n) =
      ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • robinY b E (robinInitial lam (ω.2 0)) ω n := by
    rw [oneEndedQ]; push_cast; rfl
  rw [e, quadForm_ofReal_smul]
  change _ = _ * quadForm (robinY b E (robinInitial lam (ω.2 0)) ω n)
    (robinInput b E (robinInitial lam (ω.2 0)) ω n g 0)
  rw [hY, div_eq_inv_mul]

end Solve

end RobinEntrance

end BlockBand.Endpoints.Clock
