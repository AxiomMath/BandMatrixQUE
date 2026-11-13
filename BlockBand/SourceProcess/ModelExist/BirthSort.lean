module

public import BlockBand.SourceProcess.ModelExist.TransMain
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Birth vectors chosen in the order of the birth times

The `n` probe births happen at `𝓖₀`-measurable times `θ_m`. Sort them (`Tuple.sort`, ties by
index): `T_l = θ_{srt l}` is nondecreasing. The birth vectors are chosen recursively in this
order: `b_l = sel(𝒢_{T_l}, (b_0, …, b_{l−1}, 0, …), v_{srt l})` (`stateV`, `bV`), and the vector
of probe `m` is `b_{srt⁻¹ m}` (`probeV`). The selection `sel` is a parameter.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Filter Set
open scoped NNReal

variable {Ω : Type*} {c' : Type*} {n : ℕ}
  (sel : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) × ℝ → c' → ℂ)
  (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ) (θf : Fin n → Ω → ℝ≥0) (vf : Fin n → ℝ)

/-- The sorting permutation of the birth times. -/
def srt (ω : Ω) : Equiv.Perm (Fin n) := Tuple.sort fun m => θf m ω

/-- The sorted birth times. -/
def sT (l : Fin n) (ω : Ω) : ℝ≥0 := θf (srt θf ω l) ω

theorem sT_mono (ω : Ω) : Monotone fun l => sT θf l ω :=
  Tuple.monotone_sort (fun m => θf m ω)

/-- The recursive choice: after `m` steps the first `m` sorted births have vectors. -/
def stateV : ℕ → Ω → Fin n → c' → ℂ
  | 0 => fun _ => 0
  | m + 1 => fun ω => if h : m < n then Function.update (stateV m ω) ⟨m, h⟩
      (sel (𝒢 (sT θf ⟨m, h⟩ ω) ω, stateV m ω, vf (srt θf ω ⟨m, h⟩))) else stateV m ω

/-- The vector of the `l`-th sorted birth. -/
def bV (l : Fin n) (ω : Ω) : c' → ℂ := stateV sel 𝒢 θf vf n ω l

/-- The vector of probe `m`. -/
def probeV (m : Fin n) (ω : Ω) : c' → ℂ := bV sel 𝒢 θf vf ((srt θf ω).symm m) ω

theorem stateV_of_le (ω : Ω) : ∀ (m : ℕ) (l : Fin n), m ≤ l.val → stateV sel 𝒢 θf vf m ω l = 0
  | 0, l, _ => rfl
  | m + 1, l, hm => by
    simp only [stateV]
    split_ifs with h
    · rw [Function.update_of_ne (fun e => by rw [e] at hm; simp at hm)]
      exact stateV_of_le ω m l (by omega)
    · exact stateV_of_le ω m l (by omega)

theorem stateV_succ_self (ω : Ω) (l : Fin n) :
    stateV sel 𝒢 θf vf (l.val + 1) ω l =
      sel (𝒢 (sT θf l ω) ω, stateV sel 𝒢 θf vf l.val ω, vf (srt θf ω l)) := by
  simp only [stateV, l.2, ↓reduceDIte, Fin.eta, Function.update_self]

theorem stateV_stable (ω : Ω) (l : Fin n) :
    ∀ k : ℕ, stateV sel 𝒢 θf vf (l.val + 1 + k) ω l = stateV sel 𝒢 θf vf (l.val + 1) ω l
  | 0 => rfl
  | k + 1 => by
    rw [← stateV_stable ω l k, show l.val + 1 + (k + 1) = (l.val + 1 + k) + 1 by ring]
    conv_lhs => simp only [stateV]
    split_ifs with h
    · rw [Function.update_of_ne (fun e => by
        have := congrArg Fin.val e; simp at this; omega)]
    · rfl

theorem bV_eq (ω : Ω) (l : Fin n) :
    bV sel 𝒢 θf vf l ω =
      sel (𝒢 (sT θf l ω) ω, stateV sel 𝒢 θf vf l.val ω, vf (srt θf ω l)) := by
  have h := stateV_stable sel 𝒢 θf vf ω l (n - (l.val + 1))
  rw [show l.val + 1 + (n - (l.val + 1)) = n by omega] at h
  rw [bV, h, stateV_succ_self]

theorem stateV_apply_lt (ω : Ω) (m : ℕ) (l : Fin n) (hl : l.val < m) :
    stateV sel 𝒢 θf vf m ω l = bV sel 𝒢 θf vf l ω := by
  have h := stateV_stable sel 𝒢 θf vf ω l (m - (l.val + 1))
  have h' := stateV_stable sel 𝒢 θf vf ω l (n - (l.val + 1))
  rw [show l.val + 1 + (m - (l.val + 1)) = m by omega] at h
  rw [show l.val + 1 + (n - (l.val + 1)) = n by omega] at h'
  rw [h, bV, h']

end BlockBand.SourceProcess.ModelExist
