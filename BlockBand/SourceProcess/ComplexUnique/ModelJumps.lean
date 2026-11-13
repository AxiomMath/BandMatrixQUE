module

public import BlockBand.SourceProcess.ComplexUnique.Clauses

/-!
# The model's deterministic jumps

For the jumps of `IsFiniteComplexSourceModel` (`birthJump τ' v`, `kBirthJump E τ' m`):
`birthJump_herm` (real diagonal, Hermitian), `exists_bound_jc` (bounded: the joint jump vector
depends on `t` only through the finitely many indicators `τ'_j ≤ t`), `measurable_jc`, and
`birthJump_seg`, `kBirthJump_seg`, `jc_seg` (constant on `[a, t]` when no birth lies in `(a, t]`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

variable {K np : ℕ} (E : ℝ) (τ' v m : Fin np → ℝ)

theorem birthJump_herm (t : ℝ) :
    (birthJump (K := K) τ' v t).1ᴴ = (birthJump (K := K) τ' v t).1 ∧
      (birthJump (K := K) τ' v t).2ᴴ = (birthJump (K := K) τ' v t).2 := by
  constructor <;>
  · simp only [birthJump, Prod.fst_sum, Prod.snd_sum, conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [Complex.conj_ofReal]

/-- The joint jumps as a function of the birth indicators. -/
def jumpOf (x : Fin np → Bool) : JIdx (SrcCol K (Fin np)) (Fin np) → ℂ :=
  jvec (∑ i, if x i then (((v i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
      ((v i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1) else 0)
    (∑ j, if x j then (matchedA E * (m j : ℂ)) • Matrix.single j j 1 else 0)

theorem jc_eq_jumpOf (t : ℝ≥0) :
    jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ)) t =
      jumpOf (K := K) E v m fun j => decide (τ' j ≤ t) := by
  simp only [jc, jumpOf, birthJump, kBirthJump, decide_eq_true_eq]

theorem exists_bound_jc : ∃ C, ∀ t,
    ‖jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ)) t‖ ≤ C :=
  ⟨∑ x, ‖jumpOf (K := K) E v m x‖, fun t => by
    rw [jc_eq_jumpOf]
    exact Finset.single_le_sum (f := fun x => ‖jumpOf (K := K) E v m x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ _)⟩

theorem measurable_jc :
    Measurable (jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ))) := by
  have e : jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ)) =
      (jumpOf (K := K) E v m) ∘ fun t : ℝ≥0 => fun j => decide (τ' j ≤ t) := by
    funext t; exact jc_eq_jumpOf E τ' v m t
  rw [e]
  refine measurable_of_finite _ |>.comp (measurable_pi_iff.2 fun j => ?_)
  have hS : MeasurableSet {x : ℝ≥0 | τ' j ≤ (x : ℝ)} :=
    measurableSet_le measurable_const measurable_coe_nnreal_real
  exact measurable_to_countable' fun b => by
    rcases b with _ | _
    · convert hS.compl using 1; ext x; simp
    · convert hS using 1; ext x; simp

variable {a t : ℝ≥0} (hnb : ∀ j, τ' j ≤ a ∨ (t : ℝ) < τ' j)
include hnb

theorem ite_seg {u : ℝ≥0} (hau : a ≤ u) (hut : u ≤ t) (j : Fin np) :
    (τ' j ≤ (u : ℝ)) ↔ τ' j ≤ (a : ℝ) := by
  rcases hnb j with h | h
  · exact ⟨fun _ => h, fun _ => h.trans (by exact_mod_cast hau)⟩
  · exact ⟨fun h' => absurd (h'.trans (by exact_mod_cast hut)) (not_le.2 h), fun h' =>
      absurd (h'.trans (by exact_mod_cast hau.trans hut)) (not_le.2 h)⟩

theorem birthJump_seg {u : ℝ≥0} (hau : a ≤ u) (hut : u ≤ t) :
    birthJump (K := K) τ' v (u : ℝ) = birthJump (K := K) τ' v (a : ℝ) := by
  unfold birthJump
  exact Finset.sum_congr rfl fun j _ => if_congr (ite_seg τ' hnb hau hut j) rfl rfl

theorem kBirthJump_seg {u : ℝ≥0} (hau : a ≤ u) (hut : u ≤ t) :
    kBirthJump E τ' m (u : ℝ) = kBirthJump E τ' m (a : ℝ) := by
  unfold kBirthJump
  exact Finset.sum_congr rfl fun j _ => if_congr (ite_seg τ' hnb hau hut j) rfl rfl

theorem jc_seg {u : ℝ≥0} (hau : a ≤ u) (hut : u ≤ t) :
    jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ)) u =
      jc (fun t => birthJump (K := K) τ' v (t : ℝ)) (fun t => kBirthJump E τ' m (t : ℝ)) a := by
  simp only [jc, birthJump_seg τ' v hnb hau hut, kBirthJump_seg E τ' m hnb hau hut]

end BlockBand.SourceProcess.ComplexUnique
