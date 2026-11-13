module

public import BlockBand.Palm.RelativeLocalizationDrift

/-!
# Relative localization: gap-truncated generators (continuous coefficients)

The rates `1/(N(λ_k - λ_l)²)` are replaced by `1/(N max((λ_k - λ_l)², g²))`, which are continuous
in the eigenvalues; when all gaps are at least `g` the truncated generators agree with the
reference and short generators (`truncRate_eq`, `truncRefGen_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Finset BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Abstract reference generator (same shape as `referenceGenerator`). -/
def refGen (N : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (b₀ : ℝ) (k l : Fin N) : ℝ :=
  shortGen N lam ℓ k l - if k = l then max (longCoup N lam ℓ k) (b₀ * N / ℓ) else 0

theorem referenceGenerator_eq_refGen (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ) :
    referenceGenerator F a b₀ ω ℓ σ = refGen N (flowEigenvalue F a ω σ) ℓ b₀ := rfl

/-- Truncated rate `1/(N max(x², g²))`. -/
def truncRate (N : ℕ) (g x : ℝ) : ℝ := ((N : ℝ) * max (x ^ 2) (g ^ 2))⁻¹

def truncShortGen (N : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (g : ℝ) (k l : Fin N) : ℝ := by
  classical
  exact if k = l then
      -∑ m ∈ Finset.univ.filter (fun m => m ≠ k ∧ labelDist k m < ℓ), truncRate N g (lam k - lam m)
    else if labelDist k l < ℓ then truncRate N g (lam k - lam l) else 0

def truncLongCoup (N : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (g : ℝ) (k : Fin N) : ℝ := by
  classical
  exact ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist k m), truncRate N g (lam k - lam m)

def truncRefGen (N : ℕ) (lam : Fin N → ℝ) (ℓ : ℕ) (b₀ g : ℝ) (k l : Fin N) : ℝ :=
  truncShortGen N lam ℓ g k l - if k = l then max (truncLongCoup N lam ℓ g k) (b₀ * N / ℓ) else 0

theorem continuous_truncRate (hN : 0 < N) {g : ℝ} (hg : 0 < g) : Continuous (truncRate N g) := by
  unfold truncRate
  refine Continuous.inv₀ (by fun_prop) fun x => ?_
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 < max (x ^ 2) (g ^ 2) := lt_max_of_lt_right (by positivity)
  positivity

theorem continuous_truncRefGen (ℓ : ℕ) (b₀ : ℝ) {g : ℝ} (hg : 0 < g) :
    Continuous fun lam : Fin N → ℝ => truncRefGen N lam ℓ b₀ g := by
  classical
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    exact continuous_pi fun k => k.elim0
  have hr := continuous_truncRate hN hg
  have hd : ∀ k m : Fin N, Continuous fun lam : Fin N → ℝ => truncRate N g (lam k - lam m) :=
    fun k m => hr.comp ((continuous_apply k).sub (continuous_apply m))
  refine continuous_pi fun k => continuous_pi fun l => ?_
  unfold truncRefGen truncShortGen truncLongCoup
  refine Continuous.sub ?_ ?_
  · split_ifs
    · exact (continuous_finsetSum _ fun m _ => hd k m).neg
    · exact hd k l
    · exact continuous_const
  · split_ifs
    · exact (continuous_finsetSum _ fun m _ => hd k m).max continuous_const
    · exact continuous_const

theorem truncRate_eq {g x : ℝ} (hx : g ≤ |x|) (hg : 0 ≤ g) :
    truncRate N g x = ((N : ℝ) * x ^ 2)⁻¹ := by
  unfold truncRate
  congr 2
  refine max_eq_left ?_
  have : g ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ hg hx 2
  rwa [sq_abs] at this

/-- With all gaps `≥ g` and `ℓ ≥ 1` the truncated generator is the reference generator. -/
theorem truncRefGen_eq {lam : Fin N → ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b₀ g : ℝ} (hg : 0 ≤ g)
    (hgap : ∀ k m : Fin N, k ≠ m → g ≤ |lam k - lam m|) :
    truncRefGen N lam ℓ b₀ g = refGen N lam ℓ b₀ := by
  classical
  have hrate : ∀ k m : Fin N, k ≠ m → truncRate N g (lam k - lam m) = pairRate N lam k m :=
    fun k m h => truncRate_eq (hgap k m h) hg
  funext k l
  unfold truncRefGen refGen truncShortGen shortGen truncLongCoup longCoup
  congr 1
  · split_ifs with h1 h2
    · congr 1
      exact Finset.sum_congr rfl fun m hm => by
        simp only [Finset.mem_filter] at hm
        exact hrate k m (fun e => hm.2.1 e.symm)
    · exact hrate k l h1
    · rfl
  · split_ifs
    · congr 1
      exact Finset.sum_congr rfl fun m hm => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        refine hrate k m fun e => ?_
        subst e
        simp [labelDist] at hm
        omega
    · rfl

end BlockBand.Palm.RelativeLocalization
