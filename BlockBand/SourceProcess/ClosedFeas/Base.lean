module

public import BlockBand.SourceProcess.ClosedFeas.TraceSq
public import BlockBand.SourceProcess.ClosedFeas.Conserve
public import BlockBand.SourceProcess.ModelExist.ModeAlg

/-!
# At time `s` the current frame is the whole retained current

* `initialGram_cur`: the current block of `initialGram` is `diag(√t_k 1_{t_k>h²})`.
* `ev_orth`, `modeVector_orth`: for `u ≤ 1` the two vectors `ev u σ` (resp. `modeVector u σ`),
  `σ : Fin 2`, are orthonormal.
* **`base_split`** (deterministic; proved in the sibling module `BaseSplit` from these): let `V` have that Gram matrix, `±√t_k`-eigencolumns of
  `J = 𝕊ᴴP𝕊 - P`, `AV = 0`, and let the retained mass of `V` be the whole retained mass of `T`
  (`Σ_i φ(t_i) = Σ_{k<K} φ(t_k)`, `φ = retW h`; this is the cap event). Then
  `V𝖣Vᴴ = splitCurrent 𝕊 P A Π`. Proof: `X = splitCurrent` and `Z = V𝖣Vᴴ` agree on the columns
  of `V` (`XV = VΛ = ZV`, using `Π𝕊V = 0`), so `Tr (X - Z)² = Tr X² - Tr Z²`, and both traces are
  `2 Σ φ` (`trace_split_sq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedFeas

open Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ModelExist BlockBand.SourceProcess.Stochastic

theorem ev_orth {u : ℝ} (h1 : u ≤ 1) (σ σ' : Fin 2) :
    ∑ a, ev u σ a * ev u σ' a = if σ = σ' then 1 else 0 := by
  have hr : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr h1
  have ha := Real.mul_self_sqrt (show 0 ≤ 1 - Real.sqrt u by linarith)
  have hc := Real.mul_self_sqrt (show 0 ≤ 1 + Real.sqrt u by linarith [Real.sqrt_nonneg u])
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h2p : Real.sqrt 2 ≠ 0 := by positivity
  fin_cases σ <;> fin_cases σ' <;>
    simp only [Fin.sum_univ_two, ev, Fin.zero_eta, Fin.mk_one, Fin.isValue, ↓reduceIte,
      one_ne_zero, zero_ne_one] <;> field_simp <;> nlinarith

theorem modeVector_orth {u : ℝ} (h1 : u ≤ 1) (σ σ' : Fin 2) :
    ∑ a, star (modeVector u σ a) * modeVector u σ' a = if σ = σ' then 1 else 0 := by
  simp only [modeVector_eq, Complex.star_def, Complex.conj_ofReal]
  rw [show (if σ = σ' then (1 : ℂ) else 0) = ((if σ = σ' then (1 : ℝ) else 0 : ℝ) : ℂ) by
    split_ifs <;> simp, ← ev_orth h1]
  push_cast; rfl

variable {K : ℕ}

/-- **The current block of `initialGram`**: `diag(√t_k 1_{t_k > h²})`. -/
theorem initialGram_cur (π : Type*) [DecidableEq π] {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1)
    (h : ℝ) (c c' : Fin K × Fin 2) :
    (initialGram K π t h).1 (Sum.inl c) (Sum.inl c') =
      if c = c' ∧ h ^ 2 < t c.1.val then ((Real.sqrt (t c.1.val) : ℝ) : ℂ) else 0 := by
  obtain ⟨k, σ⟩ := c
  obtain ⟨k', σ'⟩ := c'
  simp only [initialGram, gramPair, sourceGram, mul_apply, conjTranspose_apply, initialFrame,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k (fun k'' _ hk'' => by simp [hk'']) (by simp)]
  by_cases hkk : k = k'
  · subst hkk
    by_cases hr : h ^ 2 < t k.val
    · have h0 := (ht k.val).1
      have e : ∀ a : Fin 2, star (((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (t k.val) σ a) *
          (((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (t k.val) σ' a) =
          ((Real.sqrt (t k.val) : ℝ) : ℂ) * (star (modeVector (t k.val) σ a) *
            modeVector (t k.val) σ' a) := by
        intro a
        rw [← rpow_quarter_mul h0, star_mul', Complex.star_def, Complex.conj_ofReal]
        push_cast; ring
      simp only [hr, and_true, true_and, ↓reduceIte, e, ← Finset.mul_sum,
        modeVector_orth (ht k.val).2, Prod.mk.injEq]
      split_ifs <;> simp
    · simp [hr]
  · simp [hkk, Prod.ext_iff]

end BlockBand.SourceProcess.ClosedFeas
